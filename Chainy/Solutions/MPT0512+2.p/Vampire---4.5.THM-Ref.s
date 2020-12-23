%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0512+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:34 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 261 expanded)
%              Number of leaves         :   11 (  71 expanded)
%              Depth                    :   18
%              Number of atoms          :  111 ( 499 expanded)
%              Number of equality atoms :   39 ( 173 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1155,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1154,f838])).

fof(f838,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f813])).

fof(f813,plain,
    ( k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f757,f812])).

fof(f812,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k7_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
   => ( k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f757,plain,(
    ? [X0] :
      ( k1_xboole_0 != k7_relat_1(X0,k1_xboole_0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f686])).

fof(f686,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f685])).

fof(f685,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).

fof(f1154,plain,(
    ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f1153,f868])).

fof(f868,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f790])).

fof(f790,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f656])).

fof(f656,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f1153,plain,(
    ~ v1_relat_1(k7_relat_1(sK0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f1152,f839])).

fof(f839,plain,(
    k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f813])).

fof(f1152,plain,
    ( k1_xboole_0 = k7_relat_1(sK0,k1_xboole_0)
    | ~ v1_relat_1(k7_relat_1(sK0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f1147,f1050])).

fof(f1050,plain,(
    ! [X6] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X6) ),
    inference(forward_demodulation,[],[f1049,f968])).

fof(f968,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f967,f915])).

fof(f915,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f806])).

fof(f806,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f101])).

fof(f101,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f967,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0) ),
    inference(subsumption_resolution,[],[f966,f952])).

fof(f952,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f946,f838])).

fof(f946,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f925,f919])).

fof(f919,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f925,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f809])).

fof(f809,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f665])).

fof(f665,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f966,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f866,f954])).

fof(f954,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f953,f952])).

fof(f953,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_xboole_0)
      | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f867,f915])).

fof(f867,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f789])).

fof(f789,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f745])).

fof(f745,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f866,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f788])).

fof(f788,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f744])).

fof(f744,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f1049,plain,(
    ! [X6] : k1_relat_1(k1_xboole_0) = k3_xboole_0(k1_xboole_0,X6) ),
    inference(forward_demodulation,[],[f1048,f954])).

fof(f1048,plain,(
    ! [X6] : k1_relat_1(k7_relat_1(k1_xboole_0,X6)) = k3_xboole_0(k1_xboole_0,X6) ),
    inference(forward_demodulation,[],[f1044,f968])).

fof(f1044,plain,(
    ! [X6] : k1_relat_1(k7_relat_1(k1_xboole_0,X6)) = k3_xboole_0(k1_relat_1(k1_xboole_0),X6) ),
    inference(resolution,[],[f862,f952])).

fof(f862,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f784])).

fof(f784,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f747])).

fof(f747,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f1147,plain,(
    ! [X3] :
      ( k1_xboole_0 = k7_relat_1(sK0,k3_xboole_0(k1_xboole_0,X3))
      | ~ v1_relat_1(k7_relat_1(sK0,k1_xboole_0)) ) ),
    inference(backward_demodulation,[],[f1123,f1143])).

fof(f1143,plain,(
    ! [X19,X18] : k7_relat_1(k7_relat_1(sK0,X18),X19) = k7_relat_1(sK0,k3_xboole_0(X18,X19)) ),
    inference(resolution,[],[f849,f838])).

fof(f849,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f769])).

fof(f769,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f675])).

fof(f675,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f1123,plain,(
    ! [X3] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(sK0,k1_xboole_0),X3)
      | ~ v1_relat_1(k7_relat_1(sK0,k1_xboole_0)) ) ),
    inference(subsumption_resolution,[],[f1119,f1031])).

fof(f1031,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f1030,f952])).

fof(f1030,plain,(
    ! [X0] :
      ( r1_xboole_0(k1_xboole_0,X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f1029,f954])).

fof(f1029,plain,(
    ! [X0] :
      ( r1_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 != k7_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f857,f968])).

fof(f857,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f816])).

fof(f816,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f778])).

fof(f778,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f752])).

fof(f752,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

% (17501)ott+11_4:1_awrs=converge:awrsf=16:acc=model:add=large:afr=on:afp=4000:afq=1.4:amm=off:br=off:cond=fast:fde=none:gsp=input_only:nm=64:nwc=2:nicw=on:sd=3:ss=axioms:s2a=on:sac=on:sp=frequency:urr=on:updr=off_70 on theBenchmark
fof(f1119,plain,(
    ! [X3] :
      ( ~ r1_xboole_0(k1_xboole_0,X3)
      | k1_xboole_0 = k7_relat_1(k7_relat_1(sK0,k1_xboole_0),X3)
      | ~ v1_relat_1(k7_relat_1(sK0,k1_xboole_0)) ) ),
    inference(superposition,[],[f858,f1108])).

fof(f1108,plain,(
    k1_xboole_0 = k1_relat_1(k7_relat_1(sK0,k1_xboole_0)) ),
    inference(resolution,[],[f965,f838])).

fof(f965,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(k7_relat_1(X0,k1_xboole_0)) ) ),
    inference(resolution,[],[f866,f915])).

fof(f858,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f816])).
%------------------------------------------------------------------------------
