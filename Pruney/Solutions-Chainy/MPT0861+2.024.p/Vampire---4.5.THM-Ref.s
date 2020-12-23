%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 201 expanded)
%              Number of leaves         :   12 (  65 expanded)
%              Depth                    :   16
%              Number of atoms          :  112 ( 336 expanded)
%              Number of equality atoms :   73 ( 267 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f67,plain,(
    $false ),
    inference(global_subsumption,[],[f21,f20,f53,f65])).

fof(f65,plain,(
    sK3 = k2_mcart_1(sK0) ),
    inference(duplicate_literal_removal,[],[f64])).

fof(f64,plain,
    ( sK3 = k2_mcart_1(sK0)
    | sK3 = k2_mcart_1(sK0) ),
    inference(resolution,[],[f59,f42])).

fof(f42,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) ),
    inference(definition_unfolding,[],[f19,f40,f41])).

fof(f41,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f22,f40])).

fof(f22,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f23,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f26,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f27,f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f33,f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f35,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f34,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f26,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f23,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f19,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( sK3 != k2_mcart_1(sK0)
      | ( sK2 != k1_mcart_1(sK0)
        & sK1 != k1_mcart_1(sK0) ) )
    & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k1_tarski(sK3))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( k2_mcart_1(X0) != X3
          | ( k1_mcart_1(X0) != X2
            & k1_mcart_1(X0) != X1 ) )
        & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))) )
   => ( ( sK3 != k2_mcart_1(sK0)
        | ( sK2 != k1_mcart_1(sK0)
          & sK1 != k1_mcart_1(sK0) ) )
      & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k1_tarski(sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ( k2_mcart_1(X0) != X3
        | ( k1_mcart_1(X0) != X2
          & k1_mcart_1(X0) != X1 ) )
      & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)))
       => ( k2_mcart_1(X0) = X3
          & ( k1_mcart_1(X0) = X2
            | k1_mcart_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)))
     => ( k2_mcart_1(X0) = X3
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_mcart_1)).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))
      | k2_mcart_1(X0) = X2
      | k2_mcart_1(X0) = X1 ) ),
    inference(resolution,[],[f57,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k2_mcart_1(X0),X3)
      | ~ r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),X3)) ) ),
    inference(definition_unfolding,[],[f29,f40])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k2_mcart_1(X0),X3)
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k2_mcart_1(X0),X3)
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) )
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))
     => ( r2_hidden(k2_mcart_1(X0),X3)
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_mcart_1)).

fof(f57,plain,(
    ! [X6,X8,X9] :
      ( ~ r2_hidden(X6,k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X9))
      | X6 = X8
      | X6 = X9 ) ),
    inference(forward_demodulation,[],[f56,f24])).

fof(f24,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f56,plain,(
    ! [X6,X8,X7,X9] :
      ( X6 = X8
      | k1_mcart_1(k4_tarski(X6,X7)) = X9
      | ~ r2_hidden(X6,k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X9)) ) ),
    inference(forward_demodulation,[],[f55,f24])).

fof(f55,plain,(
    ! [X6,X8,X7,X9] :
      ( k1_mcart_1(k4_tarski(X6,X7)) = X8
      | k1_mcart_1(k4_tarski(X6,X7)) = X9
      | ~ r2_hidden(X6,k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X9)) ) ),
    inference(resolution,[],[f44,f48])).

fof(f48,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)))
      | ~ r2_hidden(X0,X2) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)))
      | X1 != X3
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f32,f41])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
      | X1 != X3
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <=> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),X3))
      | k1_mcart_1(X0) = X1
      | k1_mcart_1(X0) = X2 ) ),
    inference(definition_unfolding,[],[f28,f40])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(X0) = X2
      | k1_mcart_1(X0) = X1
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f53,plain,
    ( sK2 = k1_mcart_1(sK0)
    | sK1 = k1_mcart_1(sK0) ),
    inference(resolution,[],[f44,f42])).

fof(f20,plain,
    ( sK3 != k2_mcart_1(sK0)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f21,plain,
    ( sK3 != k2_mcart_1(sK0)
    | sK2 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:15:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (7060)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.50  % (7073)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.50  % (7065)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (7065)Refutation not found, incomplete strategy% (7065)------------------------------
% 0.21/0.51  % (7065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (7065)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (7065)Memory used [KB]: 1663
% 0.21/0.51  % (7065)Time elapsed: 0.057 s
% 0.21/0.51  % (7065)------------------------------
% 0.21/0.51  % (7065)------------------------------
% 0.21/0.51  % (7057)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (7073)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(global_subsumption,[],[f21,f20,f53,f65])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    sK3 = k2_mcart_1(sK0)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f64])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    sK3 = k2_mcart_1(sK0) | sK3 = k2_mcart_1(sK0)),
% 0.21/0.51    inference(resolution,[],[f59,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    r2_hidden(sK0,k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))),
% 0.21/0.51    inference(definition_unfolding,[],[f19,f40,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f22,f40])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f23,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f26,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f27,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f33,f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f34,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k1_tarski(sK3)))),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    (sK3 != k2_mcart_1(sK0) | (sK2 != k1_mcart_1(sK0) & sK1 != k1_mcart_1(sK0))) & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k1_tarski(sK3)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3] : ((k2_mcart_1(X0) != X3 | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)))) => ((sK3 != k2_mcart_1(sK0) | (sK2 != k1_mcart_1(sK0) & sK1 != k1_mcart_1(sK0))) & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k1_tarski(sK3))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3] : ((k2_mcart_1(X0) != X3 | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))) => (k2_mcart_1(X0) = X3 & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 0.21/0.51    inference(negated_conjecture,[],[f11])).
% 0.21/0.51  fof(f11,conjecture,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))) => (k2_mcart_1(X0) = X3 & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_mcart_1)).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) | k2_mcart_1(X0) = X2 | k2_mcart_1(X0) = X1) )),
% 0.21/0.51    inference(resolution,[],[f57,f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(k2_mcart_1(X0),X3) | ~r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),X3))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f29,f40])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(k2_mcart_1(X0),X3) | ~r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((r2_hidden(k2_mcart_1(X0),X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)) | ~r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) => (r2_hidden(k2_mcart_1(X0),X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_mcart_1)).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X6,X8,X9] : (~r2_hidden(X6,k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X9)) | X6 = X8 | X6 = X9) )),
% 0.21/0.51    inference(forward_demodulation,[],[f56,f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X6,X8,X7,X9] : (X6 = X8 | k1_mcart_1(k4_tarski(X6,X7)) = X9 | ~r2_hidden(X6,k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X9))) )),
% 0.21/0.51    inference(forward_demodulation,[],[f55,f24])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X6,X8,X7,X9] : (k1_mcart_1(k4_tarski(X6,X7)) = X8 | k1_mcart_1(k4_tarski(X6,X7)) = X9 | ~r2_hidden(X6,k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X9))) )),
% 0.21/0.51    inference(resolution,[],[f44,f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X2,X0,X3] : (r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) | ~r2_hidden(X0,X2)) )),
% 0.21/0.51    inference(equality_resolution,[],[f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) | X1 != X3 | ~r2_hidden(X0,X2)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f32,f41])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 != X3 | ~r2_hidden(X0,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 != X3 | ~r2_hidden(X0,X2)) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 0.21/0.51    inference(flattening,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | (X1 != X3 | ~r2_hidden(X0,X2))) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 0.21/0.51    inference(nnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),X3)) | k1_mcart_1(X0) = X1 | k1_mcart_1(X0) = X2) )),
% 0.21/0.51    inference(definition_unfolding,[],[f28,f40])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1 | ~r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    sK2 = k1_mcart_1(sK0) | sK1 = k1_mcart_1(sK0)),
% 0.21/0.51    inference(resolution,[],[f44,f42])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    sK3 != k2_mcart_1(sK0) | sK1 != k1_mcart_1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    sK3 != k2_mcart_1(sK0) | sK2 != k1_mcart_1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (7073)------------------------------
% 0.21/0.51  % (7073)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (7073)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (7073)Memory used [KB]: 6268
% 0.21/0.51  % (7073)Time elapsed: 0.062 s
% 0.21/0.51  % (7073)------------------------------
% 0.21/0.51  % (7073)------------------------------
% 0.21/0.51  % (7050)Success in time 0.149 s
%------------------------------------------------------------------------------
