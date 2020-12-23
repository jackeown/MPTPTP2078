%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0551+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:36 EST 2020

% Result     : Theorem 1.96s
% Output     : Refutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   37 (  84 expanded)
%              Number of leaves         :    8 (  23 expanded)
%              Depth                    :   12
%              Number of atoms          :   65 ( 163 expanded)
%              Number of equality atoms :   29 (  73 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2546,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2535,f1478])).

fof(f1478,plain,(
    ! [X1] : ~ r1_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f1325])).

fof(f1325,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f906])).

fof(f906,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f372])).

fof(f372,axiom,(
    ! [X0,X1] :
      ~ ( X0 = X1
        & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

fof(f2535,plain,(
    r1_xboole_0(k1_tarski(k9_relat_1(sK2,k2_xboole_0(sK0,sK1))),k1_tarski(k9_relat_1(sK2,k2_xboole_0(sK0,sK1)))) ),
    inference(backward_demodulation,[],[f2060,f2530])).

fof(f2530,plain,(
    ! [X0,X1] : k2_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k2_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f2529,f1537])).

fof(f1537,plain,(
    ! [X0] : k9_relat_1(sK2,X0) = k2_relat_1(k7_relat_1(sK2,X0)) ),
    inference(unit_resulting_resolution,[],[f1130,f1141])).

fof(f1141,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f817])).

fof(f817,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f729])).

fof(f729,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f1130,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f997])).

fof(f997,plain,
    ( k9_relat_1(sK2,k2_xboole_0(sK0,sK1)) != k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f810,f996])).

fof(f996,plain,
    ( ? [X0,X1,X2] :
        ( k9_relat_1(X2,k2_xboole_0(X0,X1)) != k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & v1_relat_1(X2) )
   => ( k9_relat_1(sK2,k2_xboole_0(sK0,sK1)) != k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f810,plain,(
    ? [X0,X1,X2] :
      ( k9_relat_1(X2,k2_xboole_0(X0,X1)) != k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f736])).

fof(f736,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f735])).

fof(f735,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t153_relat_1)).

fof(f2529,plain,(
    ! [X0,X1] : k2_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k2_relat_1(k7_relat_1(sK2,k2_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f2528,f1659])).

fof(f1659,plain,(
    ! [X0,X1] : k7_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1)) ),
    inference(unit_resulting_resolution,[],[f1130,f1421])).

fof(f1421,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f968])).

fof(f968,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f691])).

fof(f691,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_relat_1)).

fof(f2528,plain,(
    ! [X0,X1] : k2_relat_1(k2_xboole_0(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1))) = k2_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) ),
    inference(forward_demodulation,[],[f2527,f1537])).

fof(f2527,plain,(
    ! [X0,X1] : k2_relat_1(k2_xboole_0(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1))) = k2_xboole_0(k2_relat_1(k7_relat_1(sK2,X0)),k9_relat_1(sK2,X1)) ),
    inference(forward_demodulation,[],[f2147,f1537])).

fof(f2147,plain,(
    ! [X0,X1] : k2_relat_1(k2_xboole_0(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1))) = k2_xboole_0(k2_relat_1(k7_relat_1(sK2,X0)),k2_relat_1(k7_relat_1(sK2,X1))) ),
    inference(unit_resulting_resolution,[],[f1699,f1699,f1405])).

fof(f1405,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f953])).

fof(f953,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f746])).

fof(f746,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_relat_1)).

fof(f1699,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(unit_resulting_resolution,[],[f1130,f1443])).

fof(f1443,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f992])).

fof(f992,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f658])).

fof(f658,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f2060,plain,(
    r1_xboole_0(k1_tarski(k9_relat_1(sK2,k2_xboole_0(sK0,sK1))),k1_tarski(k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) ),
    inference(unit_resulting_resolution,[],[f1131,f1337])).

fof(f1337,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f914])).

fof(f914,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f373])).

fof(f373,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f1131,plain,(
    k9_relat_1(sK2,k2_xboole_0(sK0,sK1)) != k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f997])).
%------------------------------------------------------------------------------
