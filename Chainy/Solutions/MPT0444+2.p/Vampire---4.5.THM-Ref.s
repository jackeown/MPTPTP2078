%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0444+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:30 EST 2020

% Result     : Theorem 1.70s
% Output     : Refutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   54 (  86 expanded)
%              Number of leaves         :   14 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :  134 ( 227 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1405,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f831,f835,f839,f1169,f1361,f1375,f1404])).

fof(f1404,plain,
    ( ~ spl11_21
    | ~ spl11_2
    | spl11_19 ),
    inference(avatar_split_clause,[],[f1403,f1167,f833,f1359])).

fof(f1359,plain,
    ( spl11_21
  <=> v1_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).

fof(f833,plain,
    ( spl11_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f1167,plain,
    ( spl11_19
  <=> r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).

fof(f1403,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ spl11_2
    | spl11_19 ),
    inference(subsumption_resolution,[],[f1402,f834])).

fof(f834,plain,
    ( v1_relat_1(sK1)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f833])).

fof(f1402,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | spl11_19 ),
    inference(subsumption_resolution,[],[f1400,f870])).

fof(f870,plain,(
    ! [X8,X9] : r1_tarski(k3_xboole_0(X9,X8),X8) ),
    inference(superposition,[],[f805,f804])).

fof(f804,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f805,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f1400,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | spl11_19 ),
    inference(resolution,[],[f1168,f756])).

fof(f756,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f682])).

fof(f682,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f681])).

fof(f681,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f661])).

fof(f661,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f1168,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK1))
    | spl11_19 ),
    inference(avatar_component_clause,[],[f1167])).

fof(f1375,plain,
    ( ~ spl11_3
    | spl11_21 ),
    inference(avatar_contradiction_clause,[],[f1374])).

fof(f1374,plain,
    ( $false
    | ~ spl11_3
    | spl11_21 ),
    inference(subsumption_resolution,[],[f1369,f838])).

fof(f838,plain,
    ( v1_relat_1(sK0)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f837])).

fof(f837,plain,
    ( spl11_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f1369,plain,
    ( ~ v1_relat_1(sK0)
    | spl11_21 ),
    inference(resolution,[],[f1360,f811])).

fof(f811,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f708])).

fof(f708,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f645])).

fof(f645,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f1360,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | spl11_21 ),
    inference(avatar_component_clause,[],[f1359])).

fof(f1361,plain,
    ( ~ spl11_21
    | ~ spl11_3
    | spl11_18 ),
    inference(avatar_split_clause,[],[f1357,f1164,f837,f1359])).

fof(f1164,plain,
    ( spl11_18
  <=> r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f1357,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ spl11_3
    | spl11_18 ),
    inference(subsumption_resolution,[],[f1356,f838])).

fof(f1356,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | spl11_18 ),
    inference(subsumption_resolution,[],[f1352,f805])).

fof(f1352,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | spl11_18 ),
    inference(resolution,[],[f756,f1165])).

fof(f1165,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0))
    | spl11_18 ),
    inference(avatar_component_clause,[],[f1164])).

fof(f1169,plain,
    ( ~ spl11_18
    | ~ spl11_19
    | spl11_1 ),
    inference(avatar_split_clause,[],[f1147,f829,f1167,f1164])).

fof(f829,plain,
    ( spl11_1
  <=> r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f1147,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK1))
    | ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0))
    | spl11_1 ),
    inference(resolution,[],[f771,f830])).

fof(f830,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))
    | spl11_1 ),
    inference(avatar_component_clause,[],[f829])).

fof(f771,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f693])).

fof(f693,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f692])).

fof(f692,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f75])).

fof(f75,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f839,plain,(
    spl11_3 ),
    inference(avatar_split_clause,[],[f736,f837])).

fof(f736,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f712])).

fof(f712,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f668,f711,f710])).

fof(f710,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f711,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f668,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f664])).

fof(f664,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f663])).

fof(f663,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_relat_1)).

fof(f835,plain,(
    spl11_2 ),
    inference(avatar_split_clause,[],[f737,f833])).

fof(f737,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f712])).

fof(f831,plain,(
    ~ spl11_1 ),
    inference(avatar_split_clause,[],[f738,f829])).

fof(f738,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f712])).
%------------------------------------------------------------------------------
