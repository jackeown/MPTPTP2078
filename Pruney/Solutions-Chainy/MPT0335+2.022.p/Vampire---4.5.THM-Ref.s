%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:18 EST 2020

% Result     : Theorem 5.59s
% Output     : Refutation 5.59s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 297 expanded)
%              Number of leaves         :    9 (  86 expanded)
%              Depth                    :   22
%              Number of atoms          :  170 ( 643 expanded)
%              Number of equality atoms :   68 ( 318 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4351,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4349,f17])).

fof(f17,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(f4349,plain,(
    ~ r2_hidden(sK3,sK0) ),
    inference(backward_demodulation,[],[f4339,f4333])).

fof(f4333,plain,(
    sK3 = sK5(sK2,sK0,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(resolution,[],[f4325,f50])).

fof(f50,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_enumset1(X0,X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f25,f36])).

fof(f36,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f19,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f21,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f21,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f19,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f4325,plain,(
    r2_hidden(sK5(sK2,sK0,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(subsumption_resolution,[],[f4303,f37])).

fof(f37,plain,(
    k2_enumset1(sK3,sK3,sK3,sK3) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(definition_unfolding,[],[f18,f36,f22])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f18,plain,(
    k1_tarski(sK3) != k3_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f4303,plain,
    ( r2_hidden(sK5(sK2,sK0,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
    | k2_enumset1(sK3,sK3,sK3,sK3) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(factoring,[],[f3887])).

fof(f3887,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK2,sK0,X0),k2_enumset1(sK3,sK3,sK3,sK3))
      | r2_hidden(sK5(sK2,sK0,X0),X0)
      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = X0 ) ),
    inference(forward_demodulation,[],[f3861,f39])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f20,f22,f22])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f3861,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK2,sK0,X0),k2_enumset1(sK3,sK3,sK3,sK3))
      | r2_hidden(sK5(sK2,sK0,X0),X0)
      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = X0 ) ),
    inference(superposition,[],[f3044,f38])).

fof(f38,plain,(
    k2_enumset1(sK3,sK3,sK3,sK3) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(definition_unfolding,[],[f16,f22,f36])).

fof(f16,plain,(
    k3_xboole_0(sK1,sK2) = k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f3044,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK5(X3,sK0,X4),X4)
      | r2_hidden(sK5(X3,sK0,X4),k4_xboole_0(sK1,k4_xboole_0(sK1,X3)))
      | k4_xboole_0(X3,k4_xboole_0(X3,sK0)) = X4 ) ),
    inference(duplicate_literal_removal,[],[f3037])).

fof(f3037,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK5(X3,sK0,X4),X4)
      | k4_xboole_0(X3,k4_xboole_0(X3,sK0)) = X4
      | k4_xboole_0(X3,k4_xboole_0(X3,sK0)) = X4
      | r2_hidden(sK5(X3,sK0,X4),X4)
      | r2_hidden(sK5(X3,sK0,X4),k4_xboole_0(sK1,k4_xboole_0(sK1,X3))) ) ),
    inference(resolution,[],[f2973,f549])).

fof(f549,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK5(X0,X1,X2),X3)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK5(X0,X1,X2),X2)
      | r2_hidden(sK5(X0,X1,X2),k4_xboole_0(X3,k4_xboole_0(X3,X0))) ) ),
    inference(resolution,[],[f48,f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f34,f22])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f30,f22])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f2973,plain,(
    ! [X19,X20] :
      ( r2_hidden(sK5(X19,sK0,X20),X20)
      | r2_hidden(sK5(X19,sK0,X20),sK1)
      | k4_xboole_0(X19,k4_xboole_0(X19,sK0)) = X20 ) ),
    inference(superposition,[],[f386,f894])).

fof(f894,plain,(
    sK0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) ),
    inference(duplicate_literal_removal,[],[f893])).

fof(f893,plain,
    ( sK0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))
    | sK0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) ),
    inference(resolution,[],[f726,f407])).

fof(f407,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1,X1),X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X1 ) ),
    inference(factoring,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X1)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f31,f22])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X1)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f726,plain,(
    ! [X7] :
      ( ~ r2_hidden(sK5(sK1,X7,X7),sK0)
      | k4_xboole_0(sK1,k4_xboole_0(sK1,X7)) = X7 ) ),
    inference(resolution,[],[f718,f57])).

fof(f57,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f23,f15])).

fof(f15,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f718,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(sK5(X10,X11,X11),X10)
      | k4_xboole_0(X10,k4_xboole_0(X10,X11)) = X11 ) ),
    inference(subsumption_resolution,[],[f715,f47])).

fof(f715,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(sK5(X10,X11,X11),X11)
      | ~ r2_hidden(sK5(X10,X11,X11),X10)
      | k4_xboole_0(X10,k4_xboole_0(X10,X11)) = X11 ) ),
    inference(duplicate_literal_removal,[],[f711])).

fof(f711,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(sK5(X10,X11,X11),X11)
      | ~ r2_hidden(sK5(X10,X11,X11),X10)
      | k4_xboole_0(X10,k4_xboole_0(X10,X11)) = X11
      | k4_xboole_0(X10,k4_xboole_0(X10,X11)) = X11 ) ),
    inference(resolution,[],[f49,f407])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1,X2),X2)
      | ~ r2_hidden(sK5(X0,X1,X2),X1)
      | ~ r2_hidden(sK5(X0,X1,X2),X0)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f29,f22])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1,X2),X0)
      | ~ r2_hidden(sK5(X0,X1,X2),X1)
      | ~ r2_hidden(sK5(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f386,plain,(
    ! [X6,X4,X7,X5] :
      ( r2_hidden(sK5(X4,k4_xboole_0(X5,k4_xboole_0(X5,X6)),X7),X7)
      | r2_hidden(sK5(X4,k4_xboole_0(X5,k4_xboole_0(X5,X6)),X7),X5)
      | k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X5,k4_xboole_0(X5,X6)))) = X7 ) ),
    inference(resolution,[],[f47,f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f32,f22])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f4339,plain,(
    ~ r2_hidden(sK5(sK2,sK0,k2_enumset1(sK3,sK3,sK3,sK3)),sK0) ),
    inference(subsumption_resolution,[],[f4338,f37])).

fof(f4338,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ r2_hidden(sK5(sK2,sK0,k2_enumset1(sK3,sK3,sK3,sK3)),sK0) ),
    inference(forward_demodulation,[],[f4337,f39])).

fof(f4337,plain,
    ( ~ r2_hidden(sK5(sK2,sK0,k2_enumset1(sK3,sK3,sK3,sK3)),sK0)
    | k2_enumset1(sK3,sK3,sK3,sK3) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(subsumption_resolution,[],[f4326,f571])).

fof(f571,plain,(
    ! [X30,X29] :
      ( r2_hidden(sK5(X29,X30,k2_enumset1(sK3,sK3,sK3,sK3)),X29)
      | k2_enumset1(sK3,sK3,sK3,sK3) = k4_xboole_0(X29,k4_xboole_0(X29,X30))
      | r2_hidden(sK5(X29,X30,k2_enumset1(sK3,sK3,sK3,sK3)),sK2) ) ),
    inference(resolution,[],[f48,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3))
      | r2_hidden(X0,sK2) ) ),
    inference(superposition,[],[f54,f38])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f33,f22])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f4326,plain,
    ( ~ r2_hidden(sK5(sK2,sK0,k2_enumset1(sK3,sK3,sK3,sK3)),sK0)
    | ~ r2_hidden(sK5(sK2,sK0,k2_enumset1(sK3,sK3,sK3,sK3)),sK2)
    | k2_enumset1(sK3,sK3,sK3,sK3) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(resolution,[],[f4325,f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:11:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (23513)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (23512)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (23526)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.52  % (23510)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (23508)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (23520)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (23525)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.53  % (23515)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (23534)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.53  % (23532)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % (23536)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  % (23528)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  % (23507)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (23523)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (23511)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.35/0.54  % (23530)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.35/0.54  % (23516)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.35/0.54  % (23533)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.35/0.54  % (23537)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.35/0.54  % (23509)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.35/0.54  % (23524)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.35/0.54  % (23529)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.35/0.54  % (23527)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.35/0.54  % (23519)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.35/0.54  % (23521)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.35/0.55  % (23522)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.35/0.55  % (23535)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.35/0.55  % (23517)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.35/0.55  % (23514)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.52/0.57  % (23531)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 3.59/0.83  % (23512)Time limit reached!
% 3.59/0.83  % (23512)------------------------------
% 3.59/0.83  % (23512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.59/0.83  % (23512)Termination reason: Time limit
% 3.59/0.83  % (23512)Termination phase: Saturation
% 3.59/0.83  
% 3.59/0.83  % (23512)Memory used [KB]: 9466
% 3.59/0.83  % (23512)Time elapsed: 0.400 s
% 3.59/0.83  % (23512)------------------------------
% 3.59/0.83  % (23512)------------------------------
% 3.83/0.91  % (23508)Time limit reached!
% 3.83/0.91  % (23508)------------------------------
% 3.83/0.91  % (23508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.83/0.92  % (23517)Time limit reached!
% 3.83/0.92  % (23517)------------------------------
% 3.83/0.92  % (23517)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.83/0.93  % (23508)Termination reason: Time limit
% 3.83/0.93  
% 3.83/0.93  % (23508)Memory used [KB]: 8187
% 3.83/0.93  % (23508)Time elapsed: 0.510 s
% 3.83/0.93  % (23508)------------------------------
% 3.83/0.93  % (23508)------------------------------
% 4.37/0.93  % (23507)Time limit reached!
% 4.37/0.93  % (23507)------------------------------
% 4.37/0.93  % (23507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.37/0.93  % (23507)Termination reason: Time limit
% 4.37/0.93  % (23507)Termination phase: Saturation
% 4.37/0.93  
% 4.37/0.93  % (23507)Memory used [KB]: 3709
% 4.37/0.93  % (23507)Time elapsed: 0.500 s
% 4.37/0.93  % (23507)------------------------------
% 4.37/0.93  % (23507)------------------------------
% 4.37/0.94  % (23520)Time limit reached!
% 4.37/0.94  % (23520)------------------------------
% 4.37/0.94  % (23520)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.37/0.94  % (23520)Termination reason: Time limit
% 4.37/0.94  % (23520)Termination phase: Saturation
% 4.37/0.94  
% 4.37/0.94  % (23520)Memory used [KB]: 8443
% 4.37/0.94  % (23520)Time elapsed: 0.500 s
% 4.37/0.94  % (23520)------------------------------
% 4.37/0.94  % (23520)------------------------------
% 4.37/0.94  % (23517)Termination reason: Time limit
% 4.37/0.94  % (23517)Termination phase: Saturation
% 4.37/0.94  
% 4.37/0.94  % (23517)Memory used [KB]: 15607
% 4.37/0.94  % (23517)Time elapsed: 0.500 s
% 4.37/0.94  % (23517)------------------------------
% 4.37/0.94  % (23517)------------------------------
% 4.37/0.95  % (23525)Time limit reached!
% 4.37/0.95  % (23525)------------------------------
% 4.37/0.95  % (23525)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.37/0.96  % (23525)Termination reason: Time limit
% 4.37/0.96  
% 4.37/0.96  % (23525)Memory used [KB]: 14583
% 4.37/0.96  % (23525)Time elapsed: 0.503 s
% 4.37/0.96  % (23525)------------------------------
% 4.37/0.96  % (23525)------------------------------
% 4.37/0.97  % (23726)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 4.72/1.01  % (23524)Time limit reached!
% 4.72/1.01  % (23524)------------------------------
% 4.72/1.01  % (23524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.72/1.02  % (23514)Time limit reached!
% 4.72/1.02  % (23514)------------------------------
% 4.72/1.02  % (23514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.72/1.02  % (23524)Termination reason: Time limit
% 4.72/1.02  % (23524)Termination phase: Saturation
% 4.72/1.02  
% 4.72/1.02  % (23524)Memory used [KB]: 15735
% 4.72/1.02  % (23524)Time elapsed: 0.600 s
% 4.72/1.02  % (23524)------------------------------
% 4.72/1.02  % (23524)------------------------------
% 4.72/1.02  % (23514)Termination reason: Time limit
% 4.72/1.02  % (23514)Termination phase: Saturation
% 4.72/1.02  
% 4.72/1.02  % (23514)Memory used [KB]: 9722
% 4.72/1.02  % (23514)Time elapsed: 0.600 s
% 4.72/1.02  % (23514)------------------------------
% 4.72/1.02  % (23514)------------------------------
% 4.72/1.02  % (23536)Time limit reached!
% 4.72/1.02  % (23536)------------------------------
% 4.72/1.02  % (23536)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.72/1.02  % (23536)Termination reason: Time limit
% 4.72/1.02  
% 4.72/1.02  % (23536)Memory used [KB]: 9594
% 4.72/1.02  % (23536)Time elapsed: 0.618 s
% 4.72/1.02  % (23536)------------------------------
% 4.72/1.02  % (23536)------------------------------
% 5.23/1.06  % (23728)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 5.23/1.07  % (23729)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 5.23/1.07  % (23727)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 5.23/1.07  % (23730)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.59/1.09  % (23731)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.59/1.09  % (23513)Refutation found. Thanks to Tanya!
% 5.59/1.09  % SZS status Theorem for theBenchmark
% 5.59/1.11  % SZS output start Proof for theBenchmark
% 5.59/1.11  fof(f4351,plain,(
% 5.59/1.11    $false),
% 5.59/1.11    inference(subsumption_resolution,[],[f4349,f17])).
% 5.59/1.11  fof(f17,plain,(
% 5.59/1.11    r2_hidden(sK3,sK0)),
% 5.59/1.11    inference(cnf_transformation,[],[f13])).
% 5.59/1.11  fof(f13,plain,(
% 5.59/1.11    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 5.59/1.11    inference(flattening,[],[f12])).
% 5.59/1.11  fof(f12,plain,(
% 5.59/1.11    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 5.59/1.11    inference(ennf_transformation,[],[f10])).
% 5.59/1.11  fof(f10,negated_conjecture,(
% 5.59/1.11    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 5.59/1.11    inference(negated_conjecture,[],[f9])).
% 5.59/1.11  fof(f9,conjecture,(
% 5.59/1.11    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 5.59/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).
% 5.59/1.11  fof(f4349,plain,(
% 5.59/1.11    ~r2_hidden(sK3,sK0)),
% 5.59/1.11    inference(backward_demodulation,[],[f4339,f4333])).
% 5.59/1.11  fof(f4333,plain,(
% 5.59/1.11    sK3 = sK5(sK2,sK0,k2_enumset1(sK3,sK3,sK3,sK3))),
% 5.59/1.11    inference(resolution,[],[f4325,f50])).
% 5.59/1.11  fof(f50,plain,(
% 5.59/1.11    ( ! [X2,X0] : (~r2_hidden(X2,k2_enumset1(X0,X0,X0,X0)) | X0 = X2) )),
% 5.59/1.11    inference(equality_resolution,[],[f42])).
% 5.59/1.11  fof(f42,plain,(
% 5.59/1.11    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 5.59/1.11    inference(definition_unfolding,[],[f25,f36])).
% 5.59/1.11  fof(f36,plain,(
% 5.59/1.11    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 5.59/1.11    inference(definition_unfolding,[],[f19,f35])).
% 5.59/1.11  fof(f35,plain,(
% 5.59/1.11    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 5.59/1.11    inference(definition_unfolding,[],[f21,f28])).
% 5.59/1.11  fof(f28,plain,(
% 5.59/1.11    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 5.59/1.11    inference(cnf_transformation,[],[f8])).
% 5.59/1.11  fof(f8,axiom,(
% 5.59/1.11    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 5.59/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 5.59/1.11  fof(f21,plain,(
% 5.59/1.11    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 5.59/1.11    inference(cnf_transformation,[],[f7])).
% 5.59/1.11  fof(f7,axiom,(
% 5.59/1.11    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 5.59/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 5.59/1.11  fof(f19,plain,(
% 5.59/1.11    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 5.59/1.11    inference(cnf_transformation,[],[f6])).
% 5.59/1.11  fof(f6,axiom,(
% 5.59/1.11    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 5.59/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 5.59/1.11  fof(f25,plain,(
% 5.59/1.11    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 5.59/1.11    inference(cnf_transformation,[],[f5])).
% 5.59/1.11  fof(f5,axiom,(
% 5.59/1.11    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 5.59/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 5.59/1.11  fof(f4325,plain,(
% 5.59/1.11    r2_hidden(sK5(sK2,sK0,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))),
% 5.59/1.11    inference(subsumption_resolution,[],[f4303,f37])).
% 5.59/1.11  fof(f37,plain,(
% 5.59/1.11    k2_enumset1(sK3,sK3,sK3,sK3) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 5.59/1.11    inference(definition_unfolding,[],[f18,f36,f22])).
% 5.59/1.11  fof(f22,plain,(
% 5.59/1.11    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 5.59/1.11    inference(cnf_transformation,[],[f4])).
% 5.59/1.11  fof(f4,axiom,(
% 5.59/1.11    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 5.59/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 5.59/1.11  fof(f18,plain,(
% 5.59/1.11    k1_tarski(sK3) != k3_xboole_0(sK0,sK2)),
% 5.59/1.11    inference(cnf_transformation,[],[f13])).
% 5.59/1.11  fof(f4303,plain,(
% 5.59/1.11    r2_hidden(sK5(sK2,sK0,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3)) | k2_enumset1(sK3,sK3,sK3,sK3) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 5.59/1.11    inference(factoring,[],[f3887])).
% 5.59/1.11  fof(f3887,plain,(
% 5.59/1.11    ( ! [X0] : (r2_hidden(sK5(sK2,sK0,X0),k2_enumset1(sK3,sK3,sK3,sK3)) | r2_hidden(sK5(sK2,sK0,X0),X0) | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = X0) )),
% 5.59/1.11    inference(forward_demodulation,[],[f3861,f39])).
% 5.59/1.11  fof(f39,plain,(
% 5.59/1.11    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 5.59/1.11    inference(definition_unfolding,[],[f20,f22,f22])).
% 5.59/1.11  fof(f20,plain,(
% 5.59/1.11    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 5.59/1.11    inference(cnf_transformation,[],[f1])).
% 5.59/1.11  fof(f1,axiom,(
% 5.59/1.11    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 5.59/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 5.59/1.11  fof(f3861,plain,(
% 5.59/1.11    ( ! [X0] : (r2_hidden(sK5(sK2,sK0,X0),k2_enumset1(sK3,sK3,sK3,sK3)) | r2_hidden(sK5(sK2,sK0,X0),X0) | k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = X0) )),
% 5.59/1.11    inference(superposition,[],[f3044,f38])).
% 5.59/1.11  fof(f38,plain,(
% 5.59/1.11    k2_enumset1(sK3,sK3,sK3,sK3) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 5.59/1.11    inference(definition_unfolding,[],[f16,f22,f36])).
% 5.59/1.11  fof(f16,plain,(
% 5.59/1.11    k3_xboole_0(sK1,sK2) = k1_tarski(sK3)),
% 5.59/1.11    inference(cnf_transformation,[],[f13])).
% 5.59/1.11  fof(f3044,plain,(
% 5.59/1.11    ( ! [X4,X3] : (r2_hidden(sK5(X3,sK0,X4),X4) | r2_hidden(sK5(X3,sK0,X4),k4_xboole_0(sK1,k4_xboole_0(sK1,X3))) | k4_xboole_0(X3,k4_xboole_0(X3,sK0)) = X4) )),
% 5.59/1.11    inference(duplicate_literal_removal,[],[f3037])).
% 5.59/1.11  fof(f3037,plain,(
% 5.59/1.11    ( ! [X4,X3] : (r2_hidden(sK5(X3,sK0,X4),X4) | k4_xboole_0(X3,k4_xboole_0(X3,sK0)) = X4 | k4_xboole_0(X3,k4_xboole_0(X3,sK0)) = X4 | r2_hidden(sK5(X3,sK0,X4),X4) | r2_hidden(sK5(X3,sK0,X4),k4_xboole_0(sK1,k4_xboole_0(sK1,X3)))) )),
% 5.59/1.11    inference(resolution,[],[f2973,f549])).
% 5.59/1.11  fof(f549,plain,(
% 5.59/1.11    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK5(X0,X1,X2),X3) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK5(X0,X1,X2),X2) | r2_hidden(sK5(X0,X1,X2),k4_xboole_0(X3,k4_xboole_0(X3,X0)))) )),
% 5.59/1.11    inference(resolution,[],[f48,f53])).
% 5.59/1.11  fof(f53,plain,(
% 5.59/1.11    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 5.59/1.11    inference(equality_resolution,[],[f44])).
% 5.59/1.11  fof(f44,plain,(
% 5.59/1.11    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 5.59/1.11    inference(definition_unfolding,[],[f34,f22])).
% 5.59/1.11  fof(f34,plain,(
% 5.59/1.11    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 5.59/1.11    inference(cnf_transformation,[],[f3])).
% 5.59/1.11  fof(f3,axiom,(
% 5.59/1.11    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 5.59/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 5.59/1.11  fof(f48,plain,(
% 5.59/1.11    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2) )),
% 5.59/1.11    inference(definition_unfolding,[],[f30,f22])).
% 5.59/1.11  fof(f30,plain,(
% 5.59/1.11    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 5.59/1.11    inference(cnf_transformation,[],[f3])).
% 5.59/1.11  fof(f2973,plain,(
% 5.59/1.11    ( ! [X19,X20] : (r2_hidden(sK5(X19,sK0,X20),X20) | r2_hidden(sK5(X19,sK0,X20),sK1) | k4_xboole_0(X19,k4_xboole_0(X19,sK0)) = X20) )),
% 5.59/1.11    inference(superposition,[],[f386,f894])).
% 5.59/1.11  fof(f894,plain,(
% 5.59/1.11    sK0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))),
% 5.59/1.11    inference(duplicate_literal_removal,[],[f893])).
% 5.59/1.11  fof(f893,plain,(
% 5.59/1.11    sK0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) | sK0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))),
% 5.59/1.11    inference(resolution,[],[f726,f407])).
% 5.59/1.11  fof(f407,plain,(
% 5.59/1.11    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1,X1),X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X1) )),
% 5.59/1.11    inference(factoring,[],[f47])).
% 5.59/1.11  fof(f47,plain,(
% 5.59/1.11    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2) )),
% 5.59/1.11    inference(definition_unfolding,[],[f31,f22])).
% 5.59/1.11  fof(f31,plain,(
% 5.59/1.11    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 5.59/1.11    inference(cnf_transformation,[],[f3])).
% 5.59/1.11  fof(f726,plain,(
% 5.59/1.11    ( ! [X7] : (~r2_hidden(sK5(sK1,X7,X7),sK0) | k4_xboole_0(sK1,k4_xboole_0(sK1,X7)) = X7) )),
% 5.59/1.11    inference(resolution,[],[f718,f57])).
% 5.59/1.11  fof(f57,plain,(
% 5.59/1.11    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) )),
% 5.59/1.11    inference(resolution,[],[f23,f15])).
% 5.59/1.11  fof(f15,plain,(
% 5.59/1.11    r1_tarski(sK0,sK1)),
% 5.59/1.11    inference(cnf_transformation,[],[f13])).
% 5.59/1.11  fof(f23,plain,(
% 5.59/1.11    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X2,X0) | r2_hidden(X2,X1)) )),
% 5.59/1.11    inference(cnf_transformation,[],[f14])).
% 5.59/1.11  fof(f14,plain,(
% 5.59/1.11    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 5.59/1.11    inference(ennf_transformation,[],[f11])).
% 5.59/1.11  fof(f11,plain,(
% 5.59/1.11    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 5.59/1.11    inference(unused_predicate_definition_removal,[],[f2])).
% 5.59/1.11  fof(f2,axiom,(
% 5.59/1.11    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 5.59/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 5.59/1.11  fof(f718,plain,(
% 5.59/1.11    ( ! [X10,X11] : (~r2_hidden(sK5(X10,X11,X11),X10) | k4_xboole_0(X10,k4_xboole_0(X10,X11)) = X11) )),
% 5.59/1.11    inference(subsumption_resolution,[],[f715,f47])).
% 5.59/1.11  fof(f715,plain,(
% 5.59/1.11    ( ! [X10,X11] : (~r2_hidden(sK5(X10,X11,X11),X11) | ~r2_hidden(sK5(X10,X11,X11),X10) | k4_xboole_0(X10,k4_xboole_0(X10,X11)) = X11) )),
% 5.59/1.11    inference(duplicate_literal_removal,[],[f711])).
% 5.59/1.11  fof(f711,plain,(
% 5.59/1.11    ( ! [X10,X11] : (~r2_hidden(sK5(X10,X11,X11),X11) | ~r2_hidden(sK5(X10,X11,X11),X10) | k4_xboole_0(X10,k4_xboole_0(X10,X11)) = X11 | k4_xboole_0(X10,k4_xboole_0(X10,X11)) = X11) )),
% 5.59/1.11    inference(resolution,[],[f49,f407])).
% 5.59/1.11  fof(f49,plain,(
% 5.59/1.11    ( ! [X2,X0,X1] : (~r2_hidden(sK5(X0,X1,X2),X2) | ~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2) )),
% 5.59/1.11    inference(definition_unfolding,[],[f29,f22])).
% 5.59/1.11  fof(f29,plain,(
% 5.59/1.11    ( ! [X2,X0,X1] : (~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 5.59/1.11    inference(cnf_transformation,[],[f3])).
% 5.59/1.11  fof(f386,plain,(
% 5.59/1.11    ( ! [X6,X4,X7,X5] : (r2_hidden(sK5(X4,k4_xboole_0(X5,k4_xboole_0(X5,X6)),X7),X7) | r2_hidden(sK5(X4,k4_xboole_0(X5,k4_xboole_0(X5,X6)),X7),X5) | k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X5,k4_xboole_0(X5,X6)))) = X7) )),
% 5.59/1.11    inference(resolution,[],[f47,f55])).
% 5.59/1.11  fof(f55,plain,(
% 5.59/1.11    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r2_hidden(X3,X0)) )),
% 5.59/1.11    inference(equality_resolution,[],[f46])).
% 5.59/1.11  fof(f46,plain,(
% 5.59/1.11    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 5.59/1.11    inference(definition_unfolding,[],[f32,f22])).
% 5.59/1.11  fof(f32,plain,(
% 5.59/1.11    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 5.59/1.11    inference(cnf_transformation,[],[f3])).
% 5.59/1.11  fof(f4339,plain,(
% 5.59/1.11    ~r2_hidden(sK5(sK2,sK0,k2_enumset1(sK3,sK3,sK3,sK3)),sK0)),
% 5.59/1.11    inference(subsumption_resolution,[],[f4338,f37])).
% 5.59/1.11  fof(f4338,plain,(
% 5.59/1.11    k2_enumset1(sK3,sK3,sK3,sK3) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~r2_hidden(sK5(sK2,sK0,k2_enumset1(sK3,sK3,sK3,sK3)),sK0)),
% 5.59/1.11    inference(forward_demodulation,[],[f4337,f39])).
% 5.59/1.11  fof(f4337,plain,(
% 5.59/1.11    ~r2_hidden(sK5(sK2,sK0,k2_enumset1(sK3,sK3,sK3,sK3)),sK0) | k2_enumset1(sK3,sK3,sK3,sK3) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 5.59/1.11    inference(subsumption_resolution,[],[f4326,f571])).
% 5.59/1.11  fof(f571,plain,(
% 5.59/1.11    ( ! [X30,X29] : (r2_hidden(sK5(X29,X30,k2_enumset1(sK3,sK3,sK3,sK3)),X29) | k2_enumset1(sK3,sK3,sK3,sK3) = k4_xboole_0(X29,k4_xboole_0(X29,X30)) | r2_hidden(sK5(X29,X30,k2_enumset1(sK3,sK3,sK3,sK3)),sK2)) )),
% 5.59/1.11    inference(resolution,[],[f48,f60])).
% 5.59/1.11  fof(f60,plain,(
% 5.59/1.11    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) | r2_hidden(X0,sK2)) )),
% 5.59/1.11    inference(superposition,[],[f54,f38])).
% 5.59/1.11  fof(f54,plain,(
% 5.59/1.11    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r2_hidden(X3,X1)) )),
% 5.59/1.11    inference(equality_resolution,[],[f45])).
% 5.59/1.11  fof(f45,plain,(
% 5.59/1.11    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 5.59/1.11    inference(definition_unfolding,[],[f33,f22])).
% 5.59/1.11  fof(f33,plain,(
% 5.59/1.11    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 5.59/1.11    inference(cnf_transformation,[],[f3])).
% 5.59/1.11  fof(f4326,plain,(
% 5.59/1.11    ~r2_hidden(sK5(sK2,sK0,k2_enumset1(sK3,sK3,sK3,sK3)),sK0) | ~r2_hidden(sK5(sK2,sK0,k2_enumset1(sK3,sK3,sK3,sK3)),sK2) | k2_enumset1(sK3,sK3,sK3,sK3) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 5.59/1.11    inference(resolution,[],[f4325,f49])).
% 5.59/1.11  % SZS output end Proof for theBenchmark
% 5.59/1.11  % (23513)------------------------------
% 5.59/1.11  % (23513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.59/1.11  % (23513)Termination reason: Refutation
% 5.59/1.11  
% 5.59/1.11  % (23513)Memory used [KB]: 10874
% 5.59/1.11  % (23513)Time elapsed: 0.692 s
% 5.59/1.11  % (23513)------------------------------
% 5.59/1.11  % (23513)------------------------------
% 5.59/1.12  % (23504)Success in time 0.752 s
%------------------------------------------------------------------------------
