%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   96 (1820 expanded)
%              Number of leaves         :   15 ( 622 expanded)
%              Depth                    :   34
%              Number of atoms          :  137 (2425 expanded)
%              Number of equality atoms :   76 (1798 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1128,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f539,f1125])).

fof(f1125,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f1122])).

fof(f1122,plain,
    ( $false
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f54,f1119,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f24,f35])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f1119,plain,
    ( r1_xboole_0(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | spl4_2 ),
    inference(forward_demodulation,[],[f1116,f34])).

fof(f34,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f1116,plain,
    ( r1_xboole_0(k3_xboole_0(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | spl4_2 ),
    inference(superposition,[],[f27,f954])).

fof(f954,plain,
    ( k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_xboole_0(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | spl4_2 ),
    inference(forward_demodulation,[],[f895,f34])).

fof(f895,plain,
    ( k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_xboole_0(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k3_xboole_0(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)))
    | spl4_2 ),
    inference(backward_demodulation,[],[f697,f847])).

fof(f847,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f834,f34])).

fof(f834,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X0,X0)) ),
    inference(superposition,[],[f813,f507])).

fof(f507,plain,(
    ! [X8,X9] : k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X8,X9)) = k3_xboole_0(k2_zfmisc_1(k1_xboole_0,X8),k2_zfmisc_1(k1_xboole_0,X9)) ),
    inference(forward_demodulation,[],[f424,f418])).

fof(f418,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(X1,k1_xboole_0) ),
    inference(superposition,[],[f411,f34])).

fof(f411,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X0,k1_xboole_0),k2_zfmisc_1(X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f404,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f404,plain,(
    ! [X1] : r1_xboole_0(k2_zfmisc_1(X1,k1_xboole_0),k2_zfmisc_1(X1,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f401,f34])).

fof(f401,plain,(
    ! [X1] : r1_xboole_0(k3_xboole_0(k2_zfmisc_1(X1,k1_xboole_0),k2_zfmisc_1(X1,k1_xboole_0)),k2_zfmisc_1(X1,k1_xboole_0)) ),
    inference(superposition,[],[f27,f399])).

fof(f399,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k5_xboole_0(k2_zfmisc_1(X0,k1_xboole_0),k2_zfmisc_1(X0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f398,f105])).

fof(f105,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f102,f101])).

fof(f101,plain,(
    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_enumset1(sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f98,f26])).

fof(f98,plain,(
    r1_xboole_0(k1_xboole_0,k1_enumset1(sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f95,f37])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f95,plain,(
    r1_xboole_0(k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_xboole_0),k1_enumset1(sK0,sK0,sK0)) ),
    inference(backward_demodulation,[],[f89,f91])).

fof(f91,plain,(
    k1_xboole_0 = k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f84,f26])).

fof(f84,plain,(
    r1_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f55,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f23,f35])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f55,plain,(
    k1_enumset1(sK0,sK0,sK0) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))) ),
    inference(unit_resulting_resolution,[],[f22,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X0,X0,X0) = k5_xboole_0(k1_enumset1(X0,X0,X0),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f31,f42,f35,f42,f42])).

fof(f42,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f33,f39])).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f33,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f22,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1)))
        | ~ r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3)) )
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( X0 != X1
       => ( r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1)))
          & r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( X0 != X1
     => ( r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1)))
        & r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_zfmisc_1)).

fof(f89,plain,(
    r1_xboole_0(k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))),k1_enumset1(sK0,sK0,sK0)) ),
    inference(superposition,[],[f27,f55])).

% (9928)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (9926)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f102,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_enumset1(sK0,sK0,sK0))) ),
    inference(unit_resulting_resolution,[],[f98,f44])).

fof(f398,plain,(
    ! [X0] : k5_xboole_0(k2_zfmisc_1(X0,k1_xboole_0),k2_zfmisc_1(X0,k1_xboole_0)) = k2_zfmisc_1(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f397,f101])).

fof(f397,plain,(
    ! [X0] : k2_zfmisc_1(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_enumset1(sK0,sK0,sK0)))) = k5_xboole_0(k2_zfmisc_1(X0,k1_xboole_0),k2_zfmisc_1(X0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f390,f34])).

fof(f390,plain,(
    ! [X0] : k2_zfmisc_1(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_enumset1(sK0,sK0,sK0)))) = k5_xboole_0(k2_zfmisc_1(X0,k1_xboole_0),k2_zfmisc_1(k3_xboole_0(X0,X0),k1_xboole_0)) ),
    inference(superposition,[],[f46,f121])).

fof(f121,plain,(
    ! [X0,X1] : k3_xboole_0(k2_zfmisc_1(X0,k1_xboole_0),k2_zfmisc_1(X1,k1_enumset1(sK0,sK0,sK0))) = k2_zfmisc_1(k3_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[],[f28,f101])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f46,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) ),
    inference(definition_unfolding,[],[f30,f35,f35])).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(f424,plain,(
    ! [X8,X7,X9] : k3_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X7,k1_xboole_0),X8),k2_zfmisc_1(k2_zfmisc_1(X7,k1_xboole_0),X9)) = k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X8,X9)) ),
    inference(superposition,[],[f28,f411])).

fof(f813,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(k1_xboole_0,X0),k2_zfmisc_1(k1_xboole_0,X0)) ),
    inference(unit_resulting_resolution,[],[f812,f26])).

fof(f812,plain,(
    ! [X1] : r1_xboole_0(k2_zfmisc_1(k1_xboole_0,X1),k2_zfmisc_1(k1_xboole_0,X1)) ),
    inference(forward_demodulation,[],[f809,f34])).

fof(f809,plain,(
    ! [X1] : r1_xboole_0(k3_xboole_0(k2_zfmisc_1(k1_xboole_0,X1),k2_zfmisc_1(k1_xboole_0,X1)),k2_zfmisc_1(k1_xboole_0,X1)) ),
    inference(superposition,[],[f27,f750])).

fof(f750,plain,(
    ! [X2] : k2_zfmisc_1(k1_xboole_0,X2) = k5_xboole_0(k2_zfmisc_1(k1_xboole_0,X2),k2_zfmisc_1(k1_xboole_0,X2)) ),
    inference(forward_demodulation,[],[f749,f50])).

fof(f50,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f36,f35])).

fof(f36,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f749,plain,(
    ! [X2] : k2_zfmisc_1(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),X2) = k5_xboole_0(k2_zfmisc_1(k1_xboole_0,X2),k2_zfmisc_1(k1_xboole_0,X2)) ),
    inference(forward_demodulation,[],[f739,f34])).

fof(f739,plain,(
    ! [X2] : k2_zfmisc_1(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),X2) = k5_xboole_0(k2_zfmisc_1(k1_xboole_0,X2),k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X2,X2))) ),
    inference(superposition,[],[f47,f507])).

fof(f47,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) ),
    inference(definition_unfolding,[],[f29,f35,f35])).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f697,plain,
    ( k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_xboole_0(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k3_xboole_0(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_enumset1(k2_zfmisc_1(k1_xboole_0,k3_xboole_0(sK2,sK3)),k2_zfmisc_1(k1_xboole_0,k3_xboole_0(sK2,sK3)),k2_zfmisc_1(k1_xboole_0,k3_xboole_0(sK2,sK3)))))
    | spl4_2 ),
    inference(forward_demodulation,[],[f693,f217])).

fof(f217,plain,(
    ! [X2,X3] : k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),X2),k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),X3)) ),
    inference(superposition,[],[f28,f91])).

fof(f693,plain,
    ( k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_xboole_0(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k3_xboole_0(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_enumset1(k3_xboole_0(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK2),k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK3)),k3_xboole_0(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK2),k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK3)),k3_xboole_0(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK2),k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK3)))))
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f606,f49])).

fof(f606,plain,
    ( k1_xboole_0 != k3_xboole_0(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK2),k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK3))
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f64,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f64,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK2),k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK3))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl4_2
  <=> r1_xboole_0(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK2),k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f27,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f54,plain,(
    ! [X1] : k1_enumset1(X1,X1,X1) != k5_xboole_0(k1_enumset1(X1,X1,X1),k3_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1))) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_enumset1(X0,X0,X0) != k5_xboole_0(k1_enumset1(X0,X0,X0),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1))) ) ),
    inference(definition_unfolding,[],[f32,f42,f35,f42,f42])).

fof(f32,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f539,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f536])).

fof(f536,plain,
    ( $false
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f54,f458,f44])).

fof(f458,plain,
    ( r1_xboole_0(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | spl4_1 ),
    inference(backward_demodulation,[],[f405,f418])).

fof(f405,plain,
    ( r1_xboole_0(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_enumset1(k2_zfmisc_1(k3_xboole_0(sK2,sK3),k1_xboole_0),k2_zfmisc_1(k3_xboole_0(sK2,sK3),k1_xboole_0),k2_zfmisc_1(k3_xboole_0(sK2,sK3),k1_xboole_0)))
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f226,f45])).

fof(f226,plain,
    ( k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_xboole_0(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k3_xboole_0(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_enumset1(k2_zfmisc_1(k3_xboole_0(sK2,sK3),k1_xboole_0),k2_zfmisc_1(k3_xboole_0(sK2,sK3),k1_xboole_0),k2_zfmisc_1(k3_xboole_0(sK2,sK3),k1_xboole_0))))
    | spl4_1 ),
    inference(backward_demodulation,[],[f70,f216])).

fof(f216,plain,(
    ! [X0,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k1_xboole_0) = k3_xboole_0(k2_zfmisc_1(X0,k1_enumset1(sK0,sK0,sK0)),k2_zfmisc_1(X1,k1_enumset1(sK1,sK1,sK1))) ),
    inference(superposition,[],[f28,f91])).

fof(f70,plain,
    ( k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_xboole_0(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k3_xboole_0(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_enumset1(k3_xboole_0(k2_zfmisc_1(sK2,k1_enumset1(sK0,sK0,sK0)),k2_zfmisc_1(sK3,k1_enumset1(sK1,sK1,sK1))),k3_xboole_0(k2_zfmisc_1(sK2,k1_enumset1(sK0,sK0,sK0)),k2_zfmisc_1(sK3,k1_enumset1(sK1,sK1,sK1))),k3_xboole_0(k2_zfmisc_1(sK2,k1_enumset1(sK0,sK0,sK0)),k2_zfmisc_1(sK3,k1_enumset1(sK1,sK1,sK1))))))
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f67,f49])).

fof(f67,plain,
    ( k1_xboole_0 != k3_xboole_0(k2_zfmisc_1(sK2,k1_enumset1(sK0,sK0,sK0)),k2_zfmisc_1(sK3,k1_enumset1(sK1,sK1,sK1)))
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f60,f25])).

fof(f60,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(sK2,k1_enumset1(sK0,sK0,sK0)),k2_zfmisc_1(sK3,k1_enumset1(sK1,sK1,sK1)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl4_1
  <=> r1_xboole_0(k2_zfmisc_1(sK2,k1_enumset1(sK0,sK0,sK0)),k2_zfmisc_1(sK3,k1_enumset1(sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f65,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f43,f62,f58])).

fof(f43,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK2),k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK3))
    | ~ r1_xboole_0(k2_zfmisc_1(sK2,k1_enumset1(sK0,sK0,sK0)),k2_zfmisc_1(sK3,k1_enumset1(sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f21,f42,f42,f42,f42])).

fof(f21,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK3))
    | ~ r1_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK3,k1_tarski(sK1))) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:14:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.48  % (9919)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (9935)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.49  % (9911)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (9913)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (9920)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (9909)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (9929)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (9908)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (9909)Refutation not found, incomplete strategy% (9909)------------------------------
% 0.21/0.52  % (9909)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (9909)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (9909)Memory used [KB]: 10746
% 0.21/0.52  % (9909)Time elapsed: 0.113 s
% 0.21/0.52  % (9909)------------------------------
% 0.21/0.52  % (9909)------------------------------
% 0.21/0.52  % (9930)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (9929)Refutation not found, incomplete strategy% (9929)------------------------------
% 0.21/0.52  % (9929)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (9929)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (9929)Memory used [KB]: 10746
% 0.21/0.52  % (9929)Time elapsed: 0.116 s
% 0.21/0.52  % (9929)------------------------------
% 0.21/0.52  % (9929)------------------------------
% 0.21/0.52  % (9922)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (9907)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (9914)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (9907)Refutation not found, incomplete strategy% (9907)------------------------------
% 0.21/0.52  % (9907)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (9910)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (9907)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (9907)Memory used [KB]: 1663
% 0.21/0.52  % (9907)Time elapsed: 0.113 s
% 0.21/0.52  % (9907)------------------------------
% 0.21/0.52  % (9907)------------------------------
% 0.21/0.52  % (9911)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f1128,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f65,f539,f1125])).
% 0.21/0.52  fof(f1125,plain,(
% 0.21/0.52    spl4_2),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f1122])).
% 0.21/0.52  fof(f1122,plain,(
% 0.21/0.52    $false | spl4_2),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f54,f1119,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f24,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.52  fof(f1119,plain,(
% 0.21/0.52    r1_xboole_0(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) | spl4_2),
% 0.21/0.52    inference(forward_demodulation,[],[f1116,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.52    inference(rectify,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.21/0.52  fof(f1116,plain,(
% 0.21/0.52    r1_xboole_0(k3_xboole_0(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) | spl4_2),
% 0.21/0.52    inference(superposition,[],[f27,f954])).
% 0.21/0.52  fof(f954,plain,(
% 0.21/0.52    k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_xboole_0(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) | spl4_2),
% 0.21/0.52    inference(forward_demodulation,[],[f895,f34])).
% 0.21/0.52  fof(f895,plain,(
% 0.21/0.52    k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_xboole_0(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k3_xboole_0(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))) | spl4_2),
% 0.21/0.52    inference(backward_demodulation,[],[f697,f847])).
% 0.21/0.52  fof(f847,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(forward_demodulation,[],[f834,f34])).
% 0.21/0.52  fof(f834,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X0,X0))) )),
% 0.21/0.52    inference(superposition,[],[f813,f507])).
% 0.21/0.52  fof(f507,plain,(
% 0.21/0.52    ( ! [X8,X9] : (k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X8,X9)) = k3_xboole_0(k2_zfmisc_1(k1_xboole_0,X8),k2_zfmisc_1(k1_xboole_0,X9))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f424,f418])).
% 0.21/0.52  fof(f418,plain,(
% 0.21/0.52    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(X1,k1_xboole_0)) )),
% 0.21/0.52    inference(superposition,[],[f411,f34])).
% 0.21/0.52  fof(f411,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X0,k1_xboole_0),k2_zfmisc_1(X0,k1_xboole_0))) )),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f404,f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.52  fof(f404,plain,(
% 0.21/0.52    ( ! [X1] : (r1_xboole_0(k2_zfmisc_1(X1,k1_xboole_0),k2_zfmisc_1(X1,k1_xboole_0))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f401,f34])).
% 0.21/0.52  fof(f401,plain,(
% 0.21/0.52    ( ! [X1] : (r1_xboole_0(k3_xboole_0(k2_zfmisc_1(X1,k1_xboole_0),k2_zfmisc_1(X1,k1_xboole_0)),k2_zfmisc_1(X1,k1_xboole_0))) )),
% 0.21/0.52    inference(superposition,[],[f27,f399])).
% 0.21/0.52  fof(f399,plain,(
% 0.21/0.52    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k5_xboole_0(k2_zfmisc_1(X0,k1_xboole_0),k2_zfmisc_1(X0,k1_xboole_0))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f398,f105])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.52    inference(backward_demodulation,[],[f102,f101])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_enumset1(sK0,sK0,sK0))),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f98,f26])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    r1_xboole_0(k1_xboole_0,k1_enumset1(sK0,sK0,sK0))),
% 0.21/0.52    inference(forward_demodulation,[],[f95,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    r1_xboole_0(k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_xboole_0),k1_enumset1(sK0,sK0,sK0))),
% 0.21/0.52    inference(backward_demodulation,[],[f89,f91])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    k1_xboole_0 = k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f84,f26])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    r1_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f55,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f23,f35])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    k1_enumset1(sK0,sK0,sK0) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)))),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f22,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X0) = k5_xboole_0(k1_enumset1(X0,X0,X0),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1))) | X0 = X1) )),
% 0.21/0.52    inference(definition_unfolding,[],[f31,f42,f35,f42,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f33,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X0,X1] : (X0 = X1 | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,axiom,(
% 0.21/0.52    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    sK0 != sK1),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ? [X0,X1,X2,X3] : ((~r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1))) | ~r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3))) & X0 != X1)),
% 0.21/0.54    inference(ennf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2,X3] : (X0 != X1 => (r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1))) & r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3))))),
% 0.21/0.54    inference(negated_conjecture,[],[f16])).
% 0.21/0.54  fof(f16,conjecture,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (X0 != X1 => (r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1))) & r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_zfmisc_1)).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    r1_xboole_0(k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))),k1_enumset1(sK0,sK0,sK0))),
% 0.21/0.54    inference(superposition,[],[f27,f55])).
% 0.21/0.54  % (9928)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (9926)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  fof(f102,plain,(
% 0.21/0.54    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_enumset1(sK0,sK0,sK0)))),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f98,f44])).
% 0.21/0.54  fof(f398,plain,(
% 0.21/0.54    ( ! [X0] : (k5_xboole_0(k2_zfmisc_1(X0,k1_xboole_0),k2_zfmisc_1(X0,k1_xboole_0)) = k2_zfmisc_1(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f397,f101])).
% 0.21/0.54  fof(f397,plain,(
% 0.21/0.54    ( ! [X0] : (k2_zfmisc_1(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_enumset1(sK0,sK0,sK0)))) = k5_xboole_0(k2_zfmisc_1(X0,k1_xboole_0),k2_zfmisc_1(X0,k1_xboole_0))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f390,f34])).
% 0.21/0.54  fof(f390,plain,(
% 0.21/0.54    ( ! [X0] : (k2_zfmisc_1(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_enumset1(sK0,sK0,sK0)))) = k5_xboole_0(k2_zfmisc_1(X0,k1_xboole_0),k2_zfmisc_1(k3_xboole_0(X0,X0),k1_xboole_0))) )),
% 0.21/0.54    inference(superposition,[],[f46,f121])).
% 0.21/0.54  fof(f121,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k3_xboole_0(k2_zfmisc_1(X0,k1_xboole_0),k2_zfmisc_1(X1,k1_enumset1(sK0,sK0,sK0))) = k2_zfmisc_1(k3_xboole_0(X0,X1),k1_xboole_0)) )),
% 0.21/0.54    inference(superposition,[],[f28,f101])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f30,f35,f35])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).
% 0.21/0.54  fof(f424,plain,(
% 0.21/0.54    ( ! [X8,X7,X9] : (k3_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X7,k1_xboole_0),X8),k2_zfmisc_1(k2_zfmisc_1(X7,k1_xboole_0),X9)) = k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X8,X9))) )),
% 0.21/0.54    inference(superposition,[],[f28,f411])).
% 0.21/0.54  fof(f813,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(k1_xboole_0,X0),k2_zfmisc_1(k1_xboole_0,X0))) )),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f812,f26])).
% 0.21/0.54  fof(f812,plain,(
% 0.21/0.54    ( ! [X1] : (r1_xboole_0(k2_zfmisc_1(k1_xboole_0,X1),k2_zfmisc_1(k1_xboole_0,X1))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f809,f34])).
% 0.21/0.54  fof(f809,plain,(
% 0.21/0.54    ( ! [X1] : (r1_xboole_0(k3_xboole_0(k2_zfmisc_1(k1_xboole_0,X1),k2_zfmisc_1(k1_xboole_0,X1)),k2_zfmisc_1(k1_xboole_0,X1))) )),
% 0.21/0.54    inference(superposition,[],[f27,f750])).
% 0.21/0.54  fof(f750,plain,(
% 0.21/0.54    ( ! [X2] : (k2_zfmisc_1(k1_xboole_0,X2) = k5_xboole_0(k2_zfmisc_1(k1_xboole_0,X2),k2_zfmisc_1(k1_xboole_0,X2))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f749,f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 0.21/0.54    inference(definition_unfolding,[],[f36,f35])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.54  fof(f749,plain,(
% 0.21/0.54    ( ! [X2] : (k2_zfmisc_1(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),X2) = k5_xboole_0(k2_zfmisc_1(k1_xboole_0,X2),k2_zfmisc_1(k1_xboole_0,X2))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f739,f34])).
% 0.21/0.54  fof(f739,plain,(
% 0.21/0.54    ( ! [X2] : (k2_zfmisc_1(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),X2) = k5_xboole_0(k2_zfmisc_1(k1_xboole_0,X2),k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X2,X2)))) )),
% 0.21/0.54    inference(superposition,[],[f47,f507])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f29,f35,f35])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f697,plain,(
% 0.21/0.54    k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_xboole_0(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k3_xboole_0(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_enumset1(k2_zfmisc_1(k1_xboole_0,k3_xboole_0(sK2,sK3)),k2_zfmisc_1(k1_xboole_0,k3_xboole_0(sK2,sK3)),k2_zfmisc_1(k1_xboole_0,k3_xboole_0(sK2,sK3))))) | spl4_2),
% 0.21/0.54    inference(forward_demodulation,[],[f693,f217])).
% 0.21/0.54  fof(f217,plain,(
% 0.21/0.54    ( ! [X2,X3] : (k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),X2),k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),X3))) )),
% 0.21/0.54    inference(superposition,[],[f28,f91])).
% 0.21/0.54  fof(f693,plain,(
% 0.21/0.54    k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_xboole_0(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k3_xboole_0(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_enumset1(k3_xboole_0(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK2),k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK3)),k3_xboole_0(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK2),k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK3)),k3_xboole_0(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK2),k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK3))))) | spl4_2),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f606,f49])).
% 0.21/0.54  fof(f606,plain,(
% 0.21/0.54    k1_xboole_0 != k3_xboole_0(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK2),k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK3)) | spl4_2),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f64,f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    ~r1_xboole_0(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK2),k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK3)) | spl4_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f62])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    spl4_2 <=> r1_xboole_0(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK2),k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK3))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ( ! [X1] : (k1_enumset1(X1,X1,X1) != k5_xboole_0(k1_enumset1(X1,X1,X1),k3_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1)))) )),
% 0.21/0.54    inference(equality_resolution,[],[f48])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X0,X1] : (X0 != X1 | k1_enumset1(X0,X0,X0) != k5_xboole_0(k1_enumset1(X0,X0,X0),k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f32,f42,f35,f42,f42])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f539,plain,(
% 0.21/0.54    spl4_1),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f536])).
% 0.21/0.54  fof(f536,plain,(
% 0.21/0.54    $false | spl4_1),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f54,f458,f44])).
% 0.21/0.54  fof(f458,plain,(
% 0.21/0.54    r1_xboole_0(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) | spl4_1),
% 0.21/0.54    inference(backward_demodulation,[],[f405,f418])).
% 0.21/0.54  fof(f405,plain,(
% 0.21/0.54    r1_xboole_0(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_enumset1(k2_zfmisc_1(k3_xboole_0(sK2,sK3),k1_xboole_0),k2_zfmisc_1(k3_xboole_0(sK2,sK3),k1_xboole_0),k2_zfmisc_1(k3_xboole_0(sK2,sK3),k1_xboole_0))) | spl4_1),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f226,f45])).
% 0.21/0.54  fof(f226,plain,(
% 0.21/0.54    k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_xboole_0(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k3_xboole_0(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_enumset1(k2_zfmisc_1(k3_xboole_0(sK2,sK3),k1_xboole_0),k2_zfmisc_1(k3_xboole_0(sK2,sK3),k1_xboole_0),k2_zfmisc_1(k3_xboole_0(sK2,sK3),k1_xboole_0)))) | spl4_1),
% 0.21/0.54    inference(backward_demodulation,[],[f70,f216])).
% 0.21/0.54  fof(f216,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k1_xboole_0) = k3_xboole_0(k2_zfmisc_1(X0,k1_enumset1(sK0,sK0,sK0)),k2_zfmisc_1(X1,k1_enumset1(sK1,sK1,sK1)))) )),
% 0.21/0.54    inference(superposition,[],[f28,f91])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_xboole_0(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k3_xboole_0(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_enumset1(k3_xboole_0(k2_zfmisc_1(sK2,k1_enumset1(sK0,sK0,sK0)),k2_zfmisc_1(sK3,k1_enumset1(sK1,sK1,sK1))),k3_xboole_0(k2_zfmisc_1(sK2,k1_enumset1(sK0,sK0,sK0)),k2_zfmisc_1(sK3,k1_enumset1(sK1,sK1,sK1))),k3_xboole_0(k2_zfmisc_1(sK2,k1_enumset1(sK0,sK0,sK0)),k2_zfmisc_1(sK3,k1_enumset1(sK1,sK1,sK1)))))) | spl4_1),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f67,f49])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    k1_xboole_0 != k3_xboole_0(k2_zfmisc_1(sK2,k1_enumset1(sK0,sK0,sK0)),k2_zfmisc_1(sK3,k1_enumset1(sK1,sK1,sK1))) | spl4_1),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f60,f25])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ~r1_xboole_0(k2_zfmisc_1(sK2,k1_enumset1(sK0,sK0,sK0)),k2_zfmisc_1(sK3,k1_enumset1(sK1,sK1,sK1))) | spl4_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f58])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    spl4_1 <=> r1_xboole_0(k2_zfmisc_1(sK2,k1_enumset1(sK0,sK0,sK0)),k2_zfmisc_1(sK3,k1_enumset1(sK1,sK1,sK1)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ~spl4_1 | ~spl4_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f43,f62,f58])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ~r1_xboole_0(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK2),k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK3)) | ~r1_xboole_0(k2_zfmisc_1(sK2,k1_enumset1(sK0,sK0,sK0)),k2_zfmisc_1(sK3,k1_enumset1(sK1,sK1,sK1)))),
% 0.21/0.54    inference(definition_unfolding,[],[f21,f42,f42,f42,f42])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ~r1_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK3)) | ~r1_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK3,k1_tarski(sK1)))),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (9911)------------------------------
% 0.21/0.54  % (9911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (9911)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (9911)Memory used [KB]: 6908
% 0.21/0.54  % (9911)Time elapsed: 0.132 s
% 0.21/0.54  % (9911)------------------------------
% 0.21/0.54  % (9911)------------------------------
% 0.21/0.54  % (9912)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (9906)Success in time 0.189 s
% 0.21/0.54  % (9915)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (9924)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (9934)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (9923)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (9918)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (9917)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (9916)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (9927)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (9932)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (9925)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (9921)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (9936)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (9931)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (9933)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
%------------------------------------------------------------------------------
