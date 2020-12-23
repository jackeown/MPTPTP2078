%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:49 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   29 (  47 expanded)
%              Number of leaves         :    6 (  11 expanded)
%              Depth                    :   15
%              Number of atoms          :   66 ( 120 expanded)
%              Number of equality atoms :   65 ( 119 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f51,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f45])).

fof(f45,plain,(
    k3_mcart_1(k4_tarski(sK0,sK1),sK2,sK3) != k3_mcart_1(k4_tarski(sK0,sK1),sK2,sK3) ),
    inference(superposition,[],[f21,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k3_mcart_1(k4_tarski(X0,X1),X2,X3) ),
    inference(backward_demodulation,[],[f22,f38])).

fof(f38,plain,(
    ! [X17,X15,X16] : k4_tarski(k4_tarski(X15,X16),X17) = k3_mcart_1(X15,X16,X17) ),
    inference(global_subsumption,[],[f36])).

fof(f36,plain,(
    ! [X6,X7,X5] : k4_tarski(k4_tarski(X5,X6),X7) = k3_mcart_1(X5,X6,X7) ),
    inference(forward_demodulation,[],[f32,f27])).

fof(f27,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X6,X4,X7,X5] :
      ( k4_tarski(X4,X5) != k4_tarski(X6,X7)
      | k1_mcart_1(k4_tarski(X4,X5)) = X4 ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X6,X4,X7,X5,X1] :
      ( X1 = X4
      | k1_mcart_1(k4_tarski(X4,X5)) != X1
      | k4_tarski(X4,X5) != k4_tarski(X6,X7) ) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X6,X4,X0,X7,X5,X1] :
      ( X1 = X4
      | k4_tarski(X4,X5) != X0
      | k1_mcart_1(X0) != X1
      | k4_tarski(X6,X7) != X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_mcart_1(X0) = X1
            | ( sK4(X0,X1) != X1
              & k4_tarski(sK4(X0,X1),sK5(X0,X1)) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X4
                | k4_tarski(X4,X5) != X0 )
            | k1_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f12,f13])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X1 != X2
          & k4_tarski(X2,X3) = X0 )
     => ( sK4(X0,X1) != X1
        & k4_tarski(sK4(X0,X1),sK5(X0,X1)) = X0 ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_mcart_1(X0) = X1
            | ? [X2,X3] :
                ( X1 != X2
                & k4_tarski(X2,X3) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X4
                | k4_tarski(X4,X5) != X0 )
            | k1_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(rectify,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X3] :
          ( ( k1_mcart_1(X0) = X3
            | ? [X4,X5] :
                ( X3 != X4
                & k4_tarski(X4,X5) = X0 ) )
          & ( ! [X4,X5] :
                ( X3 = X4
                | k4_tarski(X4,X5) != X0 )
            | k1_mcart_1(X0) != X3 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X3] :
          ( k1_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( X3 = X4
              | k4_tarski(X4,X5) != X0 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X3] :
          ( k1_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( k4_tarski(X4,X5) = X0
             => X3 = X4 ) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X1] :
          ( k1_mcart_1(X0) = X1
        <=> ! [X2,X3] :
              ( k4_tarski(X2,X3) = X0
             => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_mcart_1)).

fof(f32,plain,(
    ! [X6,X8,X7,X5] : k4_tarski(k4_tarski(X5,X6),X7) = k1_mcart_1(k4_tarski(k3_mcart_1(X5,X6,X7),X8)) ),
    inference(superposition,[],[f27,f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f20,f19])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).

fof(f21,plain,(
    k3_mcart_1(k4_tarski(sK0,sK1),sK2,sK3) != k4_tarski(k3_mcart_1(sK0,sK1,sK2),sK3) ),
    inference(definition_unfolding,[],[f15,f19])).

fof(f15,plain,(
    k4_mcart_1(sK0,sK1,sK2,sK3) != k3_mcart_1(k4_tarski(sK0,sK1),sK2,sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k4_mcart_1(sK0,sK1,sK2,sK3) != k3_mcart_1(k4_tarski(sK0,sK1),sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) != k3_mcart_1(k4_tarski(X0,X1),X2,X3)
   => k4_mcart_1(sK0,sK1,sK2,sK3) != k3_mcart_1(k4_tarski(sK0,sK1),sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) != k3_mcart_1(k4_tarski(X0,X1),X2,X3) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k3_mcart_1(k4_tarski(X0,X1),X2,X3) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k3_mcart_1(k4_tarski(X0,X1),X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:45:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (13237)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (13245)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.50  % (13237)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    k3_mcart_1(k4_tarski(sK0,sK1),sK2,sK3) != k3_mcart_1(k4_tarski(sK0,sK1),sK2,sK3)),
% 0.20/0.50    inference(superposition,[],[f21,f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k3_mcart_1(k4_tarski(X0,X1),X2,X3)) )),
% 0.20/0.50    inference(backward_demodulation,[],[f22,f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ( ! [X17,X15,X16] : (k4_tarski(k4_tarski(X15,X16),X17) = k3_mcart_1(X15,X16,X17)) )),
% 0.20/0.50    inference(global_subsumption,[],[f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ( ! [X6,X7,X5] : (k4_tarski(k4_tarski(X5,X6),X7) = k3_mcart_1(X5,X6,X7)) )),
% 0.20/0.50    inference(forward_demodulation,[],[f32,f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.20/0.50    inference(equality_resolution,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ( ! [X6,X4,X7,X5] : (k4_tarski(X4,X5) != k4_tarski(X6,X7) | k1_mcart_1(k4_tarski(X4,X5)) = X4) )),
% 0.20/0.50    inference(equality_resolution,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ( ! [X6,X4,X7,X5,X1] : (X1 = X4 | k1_mcart_1(k4_tarski(X4,X5)) != X1 | k4_tarski(X4,X5) != k4_tarski(X6,X7)) )),
% 0.20/0.50    inference(equality_resolution,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ( ! [X6,X4,X0,X7,X5,X1] : (X1 = X4 | k4_tarski(X4,X5) != X0 | k1_mcart_1(X0) != X1 | k4_tarski(X6,X7) != X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((k1_mcart_1(X0) = X1 | (sK4(X0,X1) != X1 & k4_tarski(sK4(X0,X1),sK5(X0,X1)) = X0)) & (! [X4,X5] : (X1 = X4 | k4_tarski(X4,X5) != X0) | k1_mcart_1(X0) != X1)) | ! [X6,X7] : k4_tarski(X6,X7) != X0)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f12,f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ! [X1,X0] : (? [X2,X3] : (X1 != X2 & k4_tarski(X2,X3) = X0) => (sK4(X0,X1) != X1 & k4_tarski(sK4(X0,X1),sK5(X0,X1)) = X0))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((k1_mcart_1(X0) = X1 | ? [X2,X3] : (X1 != X2 & k4_tarski(X2,X3) = X0)) & (! [X4,X5] : (X1 = X4 | k4_tarski(X4,X5) != X0) | k1_mcart_1(X0) != X1)) | ! [X6,X7] : k4_tarski(X6,X7) != X0)),
% 0.20/0.50    inference(rectify,[],[f11])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ! [X0] : (! [X3] : ((k1_mcart_1(X0) = X3 | ? [X4,X5] : (X3 != X4 & k4_tarski(X4,X5) = X0)) & (! [X4,X5] : (X3 = X4 | k4_tarski(X4,X5) != X0) | k1_mcart_1(X0) != X3)) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 0.20/0.50    inference(nnf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,plain,(
% 0.20/0.50    ! [X0] : (! [X3] : (k1_mcart_1(X0) = X3 <=> ! [X4,X5] : (X3 = X4 | k4_tarski(X4,X5) != X0)) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,plain,(
% 0.20/0.50    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => ! [X3] : (k1_mcart_1(X0) = X3 <=> ! [X4,X5] : (k4_tarski(X4,X5) = X0 => X3 = X4)))),
% 0.20/0.50    inference(rectify,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => ! [X1] : (k1_mcart_1(X0) = X1 <=> ! [X2,X3] : (k4_tarski(X2,X3) = X0 => X1 = X2)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_mcart_1)).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ( ! [X6,X8,X7,X5] : (k4_tarski(k4_tarski(X5,X6),X7) = k1_mcart_1(k4_tarski(k3_mcart_1(X5,X6,X7),X8))) )),
% 0.20/0.50    inference(superposition,[],[f27,f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f20,f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    k3_mcart_1(k4_tarski(sK0,sK1),sK2,sK3) != k4_tarski(k3_mcart_1(sK0,sK1,sK2),sK3)),
% 0.20/0.50    inference(definition_unfolding,[],[f15,f19])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    k4_mcart_1(sK0,sK1,sK2,sK3) != k3_mcart_1(k4_tarski(sK0,sK1),sK2,sK3)),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,plain,(
% 0.20/0.50    k4_mcart_1(sK0,sK1,sK2,sK3) != k3_mcart_1(k4_tarski(sK0,sK1),sK2,sK3)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f9])).
% 0.20/0.50  fof(f9,plain,(
% 0.20/0.50    ? [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) != k3_mcart_1(k4_tarski(X0,X1),X2,X3) => k4_mcart_1(sK0,sK1,sK2,sK3) != k3_mcart_1(k4_tarski(sK0,sK1),sK2,sK3)),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f7,plain,(
% 0.20/0.50    ? [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) != k3_mcart_1(k4_tarski(X0,X1),X2,X3)),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k3_mcart_1(k4_tarski(X0,X1),X2,X3)),
% 0.20/0.50    inference(negated_conjecture,[],[f4])).
% 0.20/0.50  fof(f4,conjecture,(
% 0.20/0.50    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k3_mcart_1(k4_tarski(X0,X1),X2,X3)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_mcart_1)).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (13237)------------------------------
% 0.20/0.50  % (13237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (13237)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (13237)Memory used [KB]: 10746
% 0.20/0.50  % (13237)Time elapsed: 0.097 s
% 0.20/0.50  % (13237)------------------------------
% 0.20/0.50  % (13237)------------------------------
% 0.20/0.50  % (13228)Success in time 0.142 s
%------------------------------------------------------------------------------
