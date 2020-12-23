%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0506+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 (  73 expanded)
%              Number of leaves         :   10 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :  105 ( 179 expanded)
%              Number of equality atoms :   13 (  18 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1306,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f839,f843,f847,f1157,f1305])).

fof(f1305,plain,
    ( spl5_1
    | ~ spl5_3
    | ~ spl5_25 ),
    inference(avatar_contradiction_clause,[],[f1304])).

fof(f1304,plain,
    ( $false
    | spl5_1
    | ~ spl5_3
    | ~ spl5_25 ),
    inference(subsumption_resolution,[],[f1299,f838])).

fof(f838,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f837])).

fof(f837,plain,
    ( spl5_1
  <=> r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f1299,plain,
    ( r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))
    | ~ spl5_3
    | ~ spl5_25 ),
    inference(superposition,[],[f1184,f1156])).

fof(f1156,plain,
    ( k7_relat_1(sK2,sK0) = k7_relat_1(sK2,k3_xboole_0(sK1,sK0))
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f1155])).

fof(f1155,plain,
    ( spl5_25
  <=> k7_relat_1(sK2,sK0) = k7_relat_1(sK2,k3_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f1184,plain,
    ( ! [X2,X1] : r1_tarski(k7_relat_1(sK2,k3_xboole_0(X1,X2)),k7_relat_1(sK2,X1))
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f1176,f846])).

fof(f846,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f845])).

fof(f845,plain,
    ( spl5_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f1176,plain,
    ( ! [X2,X1] :
        ( r1_tarski(k7_relat_1(sK2,k3_xboole_0(X1,X2)),k7_relat_1(sK2,X1))
        | ~ v1_relat_1(sK2) )
    | ~ spl5_3 ),
    inference(superposition,[],[f850,f947])).

fof(f947,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1))
    | ~ spl5_3 ),
    inference(resolution,[],[f802,f846])).

fof(f802,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f758])).

fof(f758,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f674])).

fof(f674,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f850,plain,(
    ! [X2,X3,X1] :
      ( r1_tarski(k7_relat_1(k7_relat_1(X1,X2),X3),k7_relat_1(X1,X2))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f817,f818])).

fof(f818,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f775])).

fof(f775,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f656])).

fof(f656,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f817,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    inference(cnf_transformation,[],[f774])).

fof(f774,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f738])).

fof(f738,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f1157,plain,
    ( spl5_25
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f1153,f845,f841,f1155])).

fof(f841,plain,
    ( spl5_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f1153,plain,
    ( k7_relat_1(sK2,sK0) = k7_relat_1(sK2,k3_xboole_0(sK1,sK0))
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(resolution,[],[f1076,f842])).

fof(f842,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f841])).

fof(f1076,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k7_relat_1(sK2,X0) = k7_relat_1(sK2,k3_xboole_0(X1,X0)) )
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f977,f947])).

fof(f977,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X1),X0) )
    | ~ spl5_3 ),
    inference(resolution,[],[f801,f846])).

fof(f801,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ),
    inference(cnf_transformation,[],[f757])).

fof(f757,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f756])).

fof(f756,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f677])).

fof(f677,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).

fof(f847,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f794,f845])).

% (28596)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f794,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f783])).

fof(f783,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f752,f782])).

fof(f782,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f752,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f751])).

fof(f751,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f679])).

% (28598)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_88 on theBenchmark
fof(f679,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f678])).

fof(f678,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_relat_1)).

fof(f843,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f795,f841])).

fof(f795,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f783])).

fof(f839,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f796,f837])).

fof(f796,plain,(
    ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f783])).
%------------------------------------------------------------------------------
