%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0586+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:38 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :   27 (  42 expanded)
%              Number of leaves         :    6 (  13 expanded)
%              Depth                    :    8
%              Number of atoms          :   68 ( 116 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1018,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f967,f971,f975,f1011])).

fof(f1011,plain,
    ( ~ spl5_1
    | spl5_2
    | ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f1010])).

fof(f1010,plain,
    ( $false
    | ~ spl5_1
    | spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f1009,f974])).

fof(f974,plain,
    ( v1_relat_1(sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f973])).

fof(f973,plain,
    ( spl5_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f1009,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f1005,f966])).

fof(f966,plain,
    ( v3_relat_1(sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f965])).

fof(f965,plain,
    ( spl5_1
  <=> v3_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f1005,plain,
    ( ~ v3_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl5_2 ),
    inference(resolution,[],[f914,f970])).

fof(f970,plain,
    ( ~ v3_relat_1(k7_relat_1(sK1,sK0))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f969])).

fof(f969,plain,
    ( spl5_2
  <=> v3_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f914,plain,(
    ! [X0,X1] :
      ( v3_relat_1(k7_relat_1(X0,X1))
      | ~ v3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f850])).

fof(f850,plain,(
    ! [X0,X1] :
      ( ( v3_relat_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f849])).

fof(f849,plain,(
    ! [X0,X1] :
      ( ( v3_relat_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f680])).

fof(f680,axiom,(
    ! [X0,X1] :
      ( ( v3_relat_1(X0)
        & v1_relat_1(X0) )
     => ( v3_relat_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc19_relat_1)).

fof(f975,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f910,f973])).

fof(f910,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f896])).

fof(f896,plain,
    ( v3_relat_1(sK1)
    & ~ v3_relat_1(k7_relat_1(sK1,sK0))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f848,f895])).

fof(f895,plain,
    ( ? [X0,X1] :
        ( v3_relat_1(X1)
        & ~ v3_relat_1(k7_relat_1(X1,X0))
        & v1_relat_1(X1) )
   => ( v3_relat_1(sK1)
      & ~ v3_relat_1(k7_relat_1(sK1,sK0))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f848,plain,(
    ? [X0,X1] :
      ( v3_relat_1(X1)
      & ~ v3_relat_1(k7_relat_1(X1,X0))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f847])).

fof(f847,plain,(
    ? [X0,X1] :
      ( v3_relat_1(X1)
      & ~ v3_relat_1(k7_relat_1(X1,X0))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f780])).

fof(f780,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ~ ( v3_relat_1(X1)
            & ~ v3_relat_1(k7_relat_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f779])).

fof(f779,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( v3_relat_1(X1)
          & ~ v3_relat_1(k7_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_relat_1)).

fof(f971,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f911,f969])).

fof(f911,plain,(
    ~ v3_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f896])).

fof(f967,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f912,f965])).

fof(f912,plain,(
    v3_relat_1(sK1) ),
    inference(cnf_transformation,[],[f896])).
%------------------------------------------------------------------------------
