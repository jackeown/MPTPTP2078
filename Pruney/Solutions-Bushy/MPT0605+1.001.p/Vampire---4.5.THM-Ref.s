%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0605+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:17 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   36 (  54 expanded)
%              Number of leaves         :    8 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :   86 ( 132 expanded)
%              Number of equality atoms :   13 (  22 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f47,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f20,f25,f30,f35,f41,f46])).

fof(f46,plain,
    ( spl2_1
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_contradiction_clause,[],[f45])).

fof(f45,plain,
    ( $false
    | spl2_1
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f44,f19])).

fof(f19,plain,
    ( sK1 != k7_relat_1(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f17])).

fof(f17,plain,
    ( spl2_1
  <=> sK1 = k7_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f44,plain,
    ( sK1 = k7_relat_1(sK1,sK0)
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f42,f29])).

fof(f29,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl2_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f42,plain,
    ( ~ v1_relat_1(sK1)
    | sK1 = k7_relat_1(sK1,sK0)
    | ~ spl2_5 ),
    inference(resolution,[],[f40,f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f40,plain,
    ( r1_tarski(k1_relat_1(sK1),sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl2_5
  <=> r1_tarski(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f41,plain,
    ( spl2_5
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f36,f33,f22,f38])).

fof(f22,plain,
    ( spl2_2
  <=> v4_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f33,plain,
    ( spl2_4
  <=> ! [X0] :
        ( r1_tarski(k1_relat_1(sK1),X0)
        | ~ v4_relat_1(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f36,plain,
    ( r1_tarski(k1_relat_1(sK1),sK0)
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(resolution,[],[f34,f24])).

fof(f24,plain,
    ( v4_relat_1(sK1,sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f22])).

fof(f34,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK1,X0)
        | r1_tarski(k1_relat_1(sK1),X0) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f33])).

fof(f35,plain,
    ( spl2_4
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f31,f27,f33])).

fof(f31,plain,
    ( ! [X0] :
        ( r1_tarski(k1_relat_1(sK1),X0)
        | ~ v4_relat_1(sK1,X0) )
    | ~ spl2_3 ),
    inference(resolution,[],[f15,f29])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f30,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f10,f27])).

fof(f10,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( k7_relat_1(X1,X0) != X1
      & v4_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( k7_relat_1(X1,X0) != X1
      & v4_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v4_relat_1(X1,X0)
          & v1_relat_1(X1) )
       => k7_relat_1(X1,X0) = X1 ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f25,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f11,f22])).

fof(f11,plain,(
    v4_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f20,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f12,f17])).

fof(f12,plain,(
    sK1 != k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f6])).

%------------------------------------------------------------------------------
