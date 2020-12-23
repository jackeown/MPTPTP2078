%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0944+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:59 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   44 (  64 expanded)
%              Number of leaves         :   12 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :  100 ( 160 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (23191)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_21 on theBenchmark
fof(f1694,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1565,f1569,f1573,f1653,f1687,f1693])).

fof(f1693,plain,
    ( ~ spl15_3
    | spl15_14 ),
    inference(avatar_contradiction_clause,[],[f1692])).

fof(f1692,plain,
    ( $false
    | ~ spl15_3
    | spl15_14 ),
    inference(subsumption_resolution,[],[f1690,f1572])).

fof(f1572,plain,
    ( v3_ordinal1(sK0)
    | ~ spl15_3 ),
    inference(avatar_component_clause,[],[f1571])).

fof(f1571,plain,
    ( spl15_3
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_3])])).

fof(f1690,plain,
    ( ~ v3_ordinal1(sK0)
    | spl15_14 ),
    inference(resolution,[],[f1686,f1527])).

fof(f1527,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f1458])).

fof(f1458,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1434])).

fof(f1434,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v2_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_wellord2)).

fof(f1686,plain,
    ( ~ v2_wellord1(k1_wellord2(sK0))
    | spl15_14 ),
    inference(avatar_component_clause,[],[f1685])).

fof(f1685,plain,
    ( spl15_14
  <=> v2_wellord1(k1_wellord2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_14])])).

fof(f1687,plain,
    ( ~ spl15_14
    | spl15_1
    | ~ spl15_11 ),
    inference(avatar_split_clause,[],[f1683,f1651,f1563,f1685])).

fof(f1563,plain,
    ( spl15_1
  <=> v2_wellord1(k1_wellord2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1])])).

fof(f1651,plain,
    ( spl15_11
  <=> k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_11])])).

fof(f1683,plain,
    ( ~ v2_wellord1(k1_wellord2(sK0))
    | spl15_1
    | ~ spl15_11 ),
    inference(subsumption_resolution,[],[f1682,f1528])).

fof(f1528,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f1423])).

fof(f1423,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f1682,plain,
    ( ~ v2_wellord1(k1_wellord2(sK0))
    | ~ v1_relat_1(k1_wellord2(sK0))
    | spl15_1
    | ~ spl15_11 ),
    inference(subsumption_resolution,[],[f1681,f1564])).

fof(f1564,plain,
    ( ~ v2_wellord1(k1_wellord2(sK1))
    | spl15_1 ),
    inference(avatar_component_clause,[],[f1563])).

fof(f1681,plain,
    ( v2_wellord1(k1_wellord2(sK1))
    | ~ v2_wellord1(k1_wellord2(sK0))
    | ~ v1_relat_1(k1_wellord2(sK0))
    | ~ spl15_11 ),
    inference(superposition,[],[f1511,f1652])).

fof(f1652,plain,
    ( k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)
    | ~ spl15_11 ),
    inference(avatar_component_clause,[],[f1651])).

fof(f1511,plain,(
    ! [X0,X1] :
      ( v2_wellord1(k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1448])).

fof(f1448,plain,(
    ! [X0,X1] :
      ( v2_wellord1(k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1447])).

fof(f1447,plain,(
    ! [X0,X1] :
      ( v2_wellord1(k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1177])).

fof(f1177,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => v2_wellord1(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_wellord1)).

fof(f1653,plain,
    ( spl15_11
    | ~ spl15_2 ),
    inference(avatar_split_clause,[],[f1646,f1567,f1651])).

fof(f1567,plain,
    ( spl15_2
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_2])])).

fof(f1646,plain,
    ( k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)
    | ~ spl15_2 ),
    inference(resolution,[],[f1519,f1568])).

fof(f1568,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl15_2 ),
    inference(avatar_component_clause,[],[f1567])).

fof(f1519,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    inference(cnf_transformation,[],[f1455])).

fof(f1455,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1435])).

fof(f1435,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).

fof(f1573,plain,(
    spl15_3 ),
    inference(avatar_split_clause,[],[f1507,f1571])).

fof(f1507,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f1473])).

fof(f1473,plain,
    ( ~ v2_wellord1(k1_wellord2(sK1))
    & r1_tarski(sK1,sK0)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f1444,f1472,f1471])).

fof(f1471,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_wellord1(k1_wellord2(X1))
            & r1_tarski(X1,X0) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ~ v2_wellord1(k1_wellord2(X1))
          & r1_tarski(X1,sK0) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1472,plain,
    ( ? [X1] :
        ( ~ v2_wellord1(k1_wellord2(X1))
        & r1_tarski(X1,sK0) )
   => ( ~ v2_wellord1(k1_wellord2(sK1))
      & r1_tarski(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1444,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_wellord1(k1_wellord2(X1))
          & r1_tarski(X1,X0) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1437])).

fof(f1437,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( r1_tarski(X1,X0)
           => v2_wellord1(k1_wellord2(X1)) ) ) ),
    inference(negated_conjecture,[],[f1436])).

fof(f1436,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( r1_tarski(X1,X0)
         => v2_wellord1(k1_wellord2(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_wellord2)).

fof(f1569,plain,(
    spl15_2 ),
    inference(avatar_split_clause,[],[f1508,f1567])).

fof(f1508,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f1473])).

fof(f1565,plain,(
    ~ spl15_1 ),
    inference(avatar_split_clause,[],[f1509,f1563])).

fof(f1509,plain,(
    ~ v2_wellord1(k1_wellord2(sK1)) ),
    inference(cnf_transformation,[],[f1473])).
%------------------------------------------------------------------------------
