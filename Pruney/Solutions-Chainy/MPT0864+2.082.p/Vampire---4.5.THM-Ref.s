%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 599 expanded)
%              Number of leaves         :   12 ( 205 expanded)
%              Depth                    :   17
%              Number of atoms          :  118 ( 744 expanded)
%              Number of equality atoms :   93 ( 667 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f91,plain,(
    $false ),
    inference(subsumption_resolution,[],[f90,f84])).

fof(f84,plain,(
    ! [X4,X5] : k4_tarski(X4,X5) != X4 ),
    inference(subsumption_resolution,[],[f80,f48])).

fof(f48,plain,(
    ! [X1] : k1_xboole_0 != k2_enumset1(X1,X1,X1,X1) ),
    inference(forward_demodulation,[],[f47,f18])).

fof(f18,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f47,plain,(
    ! [X1] : k2_enumset1(X1,X1,X1,X1) != k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) ),
    inference(forward_demodulation,[],[f45,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X0) = k1_setfam_1(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f25,f38,f36,f38,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f24,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f24,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f23,f35])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f38,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f19,f35])).

fof(f19,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f25,plain,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

fof(f45,plain,(
    ! [X1] : k2_enumset1(X1,X1,X1,X1) != k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k1_setfam_1(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)))) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k2_enumset1(X0,X0,X0,X0) != k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k1_setfam_1(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)))) ) ),
    inference(definition_unfolding,[],[f30,f38,f37,f38,f38])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f26,f36])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f80,plain,(
    ! [X4,X5] :
      ( k4_tarski(X4,X5) != X4
      | k1_xboole_0 = k2_enumset1(X4,X4,X4,X4) ) ),
    inference(superposition,[],[f58,f77])).

fof(f77,plain,(
    ! [X0] : sK3(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(subsumption_resolution,[],[f76,f66])).

fof(f66,plain,(
    ! [X2] : ~ r2_hidden(X2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f64,f18])).

fof(f64,plain,(
    ! [X2] : ~ r2_hidden(X2,k5_xboole_0(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X2,X2,X2,X2))) ),
    inference(superposition,[],[f46,f39])).

fof(f46,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,k2_enumset1(X2,X2,X2,X2))))) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,k2_enumset1(X2,X2,X2,X2))))) ) ),
    inference(definition_unfolding,[],[f33,f37,f38])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f76,plain,(
    ! [X0] :
      ( r2_hidden(sK3(k2_enumset1(X0,X0,X0,X0)),k1_xboole_0)
      | sK3(k2_enumset1(X0,X0,X0,X0)) = X0 ) ),
    inference(forward_demodulation,[],[f75,f18])).

fof(f75,plain,(
    ! [X0] :
      ( r2_hidden(sK3(k2_enumset1(X0,X0,X0,X0)),k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)))
      | sK3(k2_enumset1(X0,X0,X0,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f74,f48])).

fof(f74,plain,(
    ! [X0] :
      ( r2_hidden(sK3(k2_enumset1(X0,X0,X0,X0)),k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)))
      | sK3(k2_enumset1(X0,X0,X0,X0)) = X0
      | k1_xboole_0 = k2_enumset1(X0,X0,X0,X0) ) ),
    inference(superposition,[],[f62,f39])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0),k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,k2_enumset1(X1,X1,X1,X1)))))
      | sK3(X0) = X1
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f42,f22])).

fof(f22,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | X0 = X2
      | r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,k2_enumset1(X2,X2,X2,X2))))) ) ),
    inference(definition_unfolding,[],[f34,f37,f38])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | X0 = X2
      | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f58,plain,(
    ! [X0,X1] :
      ( sK3(X0) != k4_tarski(sK3(X0),X1)
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | sK3(X0) != k4_tarski(sK3(X0),X1)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f20,f22])).

fof(f20,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0
      | k4_tarski(X2,X3) != sK3(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f90,plain,(
    sK0 = k4_tarski(sK0,sK2) ),
    inference(backward_demodulation,[],[f17,f88])).

fof(f88,plain,(
    sK0 = sK1 ),
    inference(trivial_inequality_removal,[],[f87])).

fof(f87,plain,
    ( sK0 != sK0
    | sK0 = sK1 ),
    inference(superposition,[],[f83,f54])).

fof(f54,plain,
    ( sK0 = k4_tarski(sK1,sK0)
    | sK0 = sK1 ),
    inference(superposition,[],[f17,f52])).

fof(f52,plain,
    ( sK0 = sK2
    | sK0 = sK1 ),
    inference(superposition,[],[f51,f50])).

fof(f50,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = sK1 ),
    inference(backward_demodulation,[],[f16,f49])).

fof(f49,plain,(
    sK1 = k1_mcart_1(sK0) ),
    inference(superposition,[],[f27,f17])).

fof(f27,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f16,plain,
    ( sK0 = k1_mcart_1(sK0)
    | sK0 = k2_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f51,plain,(
    sK2 = k2_mcart_1(sK0) ),
    inference(superposition,[],[f28,f17])).

fof(f28,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f10])).

fof(f83,plain,(
    ! [X2,X3] : k4_tarski(X3,X2) != X2 ),
    inference(subsumption_resolution,[],[f79,f48])).

fof(f79,plain,(
    ! [X2,X3] :
      ( k4_tarski(X3,X2) != X2
      | k1_xboole_0 = k2_enumset1(X2,X2,X2,X2) ) ),
    inference(superposition,[],[f60,f77])).

fof(f60,plain,(
    ! [X0,X1] :
      ( sK3(X0) != k4_tarski(X1,sK3(X0))
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | sK3(X0) != k4_tarski(X1,sK3(X0))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f21,f22])).

fof(f21,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0
      | k4_tarski(X2,X3) != sK3(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f17,plain,(
    sK0 = k4_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:53:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.45  % (8781)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.45  % (8781)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f91,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(subsumption_resolution,[],[f90,f84])).
% 0.20/0.45  fof(f84,plain,(
% 0.20/0.45    ( ! [X4,X5] : (k4_tarski(X4,X5) != X4) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f80,f48])).
% 0.20/0.45  fof(f48,plain,(
% 0.20/0.45    ( ! [X1] : (k1_xboole_0 != k2_enumset1(X1,X1,X1,X1)) )),
% 0.20/0.45    inference(forward_demodulation,[],[f47,f18])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 0.20/0.45    inference(cnf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.20/0.45  fof(f47,plain,(
% 0.20/0.45    ( ! [X1] : (k2_enumset1(X1,X1,X1,X1) != k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))) )),
% 0.20/0.45    inference(forward_demodulation,[],[f45,f39])).
% 0.20/0.45  fof(f39,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = k1_setfam_1(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)))) )),
% 0.20/0.45    inference(definition_unfolding,[],[f25,f38,f36,f38,f35])).
% 0.20/0.45  fof(f35,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.45    inference(definition_unfolding,[],[f24,f31])).
% 0.20/0.45  fof(f31,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f5])).
% 0.20/0.45  fof(f5,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.45  fof(f36,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.20/0.45    inference(definition_unfolding,[],[f23,f35])).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f9])).
% 0.20/0.45  fof(f9,axiom,(
% 0.20/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.45  fof(f38,plain,(
% 0.20/0.45    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.45    inference(definition_unfolding,[],[f19,f35])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f6])).
% 0.20/0.45  fof(f6,axiom,(
% 0.20/0.45    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).
% 0.20/0.45  fof(f45,plain,(
% 0.20/0.45    ( ! [X1] : (k2_enumset1(X1,X1,X1,X1) != k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k1_setfam_1(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))))) )),
% 0.20/0.45    inference(equality_resolution,[],[f40])).
% 0.20/0.45  fof(f40,plain,(
% 0.20/0.45    ( ! [X0,X1] : (X0 != X1 | k2_enumset1(X0,X0,X0,X0) != k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k1_setfam_1(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))))) )),
% 0.20/0.45    inference(definition_unfolding,[],[f30,f38,f37,f38,f38])).
% 0.20/0.45  fof(f37,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 0.20/0.45    inference(definition_unfolding,[],[f26,f36])).
% 0.20/0.45  fof(f26,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.45  fof(f30,plain,(
% 0.20/0.45    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f7])).
% 0.20/0.45  fof(f7,axiom,(
% 0.20/0.45    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.20/0.45  fof(f80,plain,(
% 0.20/0.45    ( ! [X4,X5] : (k4_tarski(X4,X5) != X4 | k1_xboole_0 = k2_enumset1(X4,X4,X4,X4)) )),
% 0.20/0.45    inference(superposition,[],[f58,f77])).
% 0.20/0.45  fof(f77,plain,(
% 0.20/0.45    ( ! [X0] : (sK3(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f76,f66])).
% 0.20/0.45  fof(f66,plain,(
% 0.20/0.45    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) )),
% 0.20/0.45    inference(forward_demodulation,[],[f64,f18])).
% 0.20/0.45  fof(f64,plain,(
% 0.20/0.45    ( ! [X2] : (~r2_hidden(X2,k5_xboole_0(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X2,X2,X2,X2)))) )),
% 0.20/0.45    inference(superposition,[],[f46,f39])).
% 0.20/0.45  fof(f46,plain,(
% 0.20/0.45    ( ! [X2,X1] : (~r2_hidden(X2,k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,k2_enumset1(X2,X2,X2,X2)))))) )),
% 0.20/0.45    inference(equality_resolution,[],[f43])).
% 0.20/0.45  fof(f43,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,k2_enumset1(X2,X2,X2,X2)))))) )),
% 0.20/0.45    inference(definition_unfolding,[],[f33,f37,f38])).
% 0.20/0.45  fof(f33,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f8])).
% 0.20/0.45  fof(f8,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.20/0.45  fof(f76,plain,(
% 0.20/0.45    ( ! [X0] : (r2_hidden(sK3(k2_enumset1(X0,X0,X0,X0)),k1_xboole_0) | sK3(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 0.20/0.45    inference(forward_demodulation,[],[f75,f18])).
% 0.20/0.45  fof(f75,plain,(
% 0.20/0.45    ( ! [X0] : (r2_hidden(sK3(k2_enumset1(X0,X0,X0,X0)),k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0))) | sK3(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f74,f48])).
% 0.20/0.45  fof(f74,plain,(
% 0.20/0.45    ( ! [X0] : (r2_hidden(sK3(k2_enumset1(X0,X0,X0,X0)),k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0))) | sK3(k2_enumset1(X0,X0,X0,X0)) = X0 | k1_xboole_0 = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.45    inference(superposition,[],[f62,f39])).
% 0.20/0.45  fof(f62,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r2_hidden(sK3(X0),k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,k2_enumset1(X1,X1,X1,X1))))) | sK3(X0) = X1 | k1_xboole_0 = X0) )),
% 0.20/0.45    inference(resolution,[],[f42,f22])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.45    inference(cnf_transformation,[],[f15])).
% 0.20/0.45  fof(f15,plain,(
% 0.20/0.45    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.20/0.45    inference(ennf_transformation,[],[f11])).
% 0.20/0.45  fof(f11,axiom,(
% 0.20/0.45    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).
% 0.20/0.45  fof(f42,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | X0 = X2 | r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,k2_enumset1(X2,X2,X2,X2)))))) )),
% 0.20/0.45    inference(definition_unfolding,[],[f34,f37,f38])).
% 0.20/0.45  fof(f34,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | X0 = X2 | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f8])).
% 0.20/0.45  fof(f58,plain,(
% 0.20/0.45    ( ! [X0,X1] : (sK3(X0) != k4_tarski(sK3(X0),X1) | k1_xboole_0 = X0) )),
% 0.20/0.45    inference(duplicate_literal_removal,[],[f57])).
% 0.20/0.45  fof(f57,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k1_xboole_0 = X0 | sK3(X0) != k4_tarski(sK3(X0),X1) | k1_xboole_0 = X0) )),
% 0.20/0.45    inference(resolution,[],[f20,f22])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    ( ! [X2,X0,X3] : (~r2_hidden(X2,X0) | k1_xboole_0 = X0 | k4_tarski(X2,X3) != sK3(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f15])).
% 0.20/0.45  fof(f90,plain,(
% 0.20/0.45    sK0 = k4_tarski(sK0,sK2)),
% 0.20/0.45    inference(backward_demodulation,[],[f17,f88])).
% 0.20/0.45  fof(f88,plain,(
% 0.20/0.45    sK0 = sK1),
% 0.20/0.45    inference(trivial_inequality_removal,[],[f87])).
% 0.20/0.45  fof(f87,plain,(
% 0.20/0.45    sK0 != sK0 | sK0 = sK1),
% 0.20/0.45    inference(superposition,[],[f83,f54])).
% 0.20/0.45  fof(f54,plain,(
% 0.20/0.45    sK0 = k4_tarski(sK1,sK0) | sK0 = sK1),
% 0.20/0.45    inference(superposition,[],[f17,f52])).
% 0.20/0.45  fof(f52,plain,(
% 0.20/0.45    sK0 = sK2 | sK0 = sK1),
% 0.20/0.45    inference(superposition,[],[f51,f50])).
% 0.20/0.45  fof(f50,plain,(
% 0.20/0.45    sK0 = k2_mcart_1(sK0) | sK0 = sK1),
% 0.20/0.45    inference(backward_demodulation,[],[f16,f49])).
% 0.20/0.45  fof(f49,plain,(
% 0.20/0.45    sK1 = k1_mcart_1(sK0)),
% 0.20/0.45    inference(superposition,[],[f27,f17])).
% 0.20/0.45  fof(f27,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.20/0.45    inference(cnf_transformation,[],[f10])).
% 0.20/0.45  fof(f10,axiom,(
% 0.20/0.45    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    sK0 = k1_mcart_1(sK0) | sK0 = k2_mcart_1(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f14])).
% 0.20/0.45  fof(f14,plain,(
% 0.20/0.45    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 0.20/0.45    inference(ennf_transformation,[],[f13])).
% 0.20/0.45  fof(f13,negated_conjecture,(
% 0.20/0.45    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.20/0.45    inference(negated_conjecture,[],[f12])).
% 0.20/0.45  fof(f12,conjecture,(
% 0.20/0.45    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).
% 0.20/0.45  fof(f51,plain,(
% 0.20/0.45    sK2 = k2_mcart_1(sK0)),
% 0.20/0.45    inference(superposition,[],[f28,f17])).
% 0.20/0.45  fof(f28,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.20/0.45    inference(cnf_transformation,[],[f10])).
% 0.20/0.45  fof(f83,plain,(
% 0.20/0.45    ( ! [X2,X3] : (k4_tarski(X3,X2) != X2) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f79,f48])).
% 0.20/0.45  fof(f79,plain,(
% 0.20/0.45    ( ! [X2,X3] : (k4_tarski(X3,X2) != X2 | k1_xboole_0 = k2_enumset1(X2,X2,X2,X2)) )),
% 0.20/0.45    inference(superposition,[],[f60,f77])).
% 0.20/0.45  fof(f60,plain,(
% 0.20/0.45    ( ! [X0,X1] : (sK3(X0) != k4_tarski(X1,sK3(X0)) | k1_xboole_0 = X0) )),
% 0.20/0.45    inference(duplicate_literal_removal,[],[f59])).
% 0.20/0.45  fof(f59,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k1_xboole_0 = X0 | sK3(X0) != k4_tarski(X1,sK3(X0)) | k1_xboole_0 = X0) )),
% 0.20/0.45    inference(resolution,[],[f21,f22])).
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    ( ! [X2,X0,X3] : (~r2_hidden(X3,X0) | k1_xboole_0 = X0 | k4_tarski(X2,X3) != sK3(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f15])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    sK0 = k4_tarski(sK1,sK2)),
% 0.20/0.45    inference(cnf_transformation,[],[f14])).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (8781)------------------------------
% 0.20/0.45  % (8781)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (8781)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (8781)Memory used [KB]: 6268
% 0.20/0.45  % (8781)Time elapsed: 0.009 s
% 0.20/0.45  % (8781)------------------------------
% 0.20/0.45  % (8781)------------------------------
% 0.20/0.46  % (8770)Success in time 0.096 s
%------------------------------------------------------------------------------
