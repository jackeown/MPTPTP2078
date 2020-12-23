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
% DateTime   : Thu Dec  3 12:58:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   27 (  96 expanded)
%              Number of leaves         :    4 (  27 expanded)
%              Depth                    :   12
%              Number of atoms          :   67 ( 278 expanded)
%              Number of equality atoms :   66 ( 277 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f86,plain,(
    $false ),
    inference(global_subsumption,[],[f10,f39,f54,f73,f83])).

fof(f83,plain,(
    sK0 = sK4 ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X4,X5] :
      ( k4_tarski(sK0,sK1) != k4_tarski(X4,X5)
      | sK4 = X4 ) ),
    inference(superposition,[],[f12,f64])).

fof(f64,plain,(
    k4_tarski(sK0,sK1) = k4_tarski(sK4,sK5) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X4,X5] :
      ( k4_tarski(k4_tarski(sK0,sK1),sK2) != k4_tarski(X4,X5)
      | k4_tarski(sK4,sK5) = X4 ) ),
    inference(superposition,[],[f12,f47])).

fof(f47,plain,(
    k4_tarski(k4_tarski(sK0,sK1),sK2) = k4_tarski(k4_tarski(sK4,sK5),sK6) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X4,X5] :
      ( k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3) != k4_tarski(X4,X5)
      | k4_tarski(k4_tarski(sK4,sK5),sK6) = X4 ) ),
    inference(superposition,[],[f12,f14])).

fof(f14,plain,(
    k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3) = k4_tarski(k4_tarski(k4_tarski(sK4,sK5),sK6),sK7) ),
    inference(definition_unfolding,[],[f9,f11,f11])).

fof(f11,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).

fof(f9,plain,(
    k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,
    ( ( sK3 != sK7
      | sK2 != sK6
      | sK1 != sK5
      | sK0 != sK4 )
    & k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f5,f7])).

fof(f7,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( X3 != X7
          | X2 != X6
          | X1 != X5
          | X0 != X4 )
        & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) )
   => ( ( sK3 != sK7
        | sK2 != sK6
        | sK1 != sK5
        | sK0 != sK4 )
      & k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)
       => ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)
     => ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_mcart_1)).

fof(f12,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k4_tarski(X0,X1) != k4_tarski(X2,X3) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( k4_tarski(X0,X1) = k4_tarski(X2,X3)
     => ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_zfmisc_1)).

fof(f73,plain,(
    sK1 = sK5 ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k4_tarski(X0,X1) != k4_tarski(sK0,sK1)
      | sK5 = X1 ) ),
    inference(superposition,[],[f13,f64])).

fof(f13,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f54,plain,(
    sK2 = sK6 ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_tarski(X0,X1) != k4_tarski(k4_tarski(sK0,sK1),sK2)
      | sK6 = X1 ) ),
    inference(superposition,[],[f13,f47])).

fof(f39,plain,(
    sK3 = sK7 ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k4_tarski(X0,X1) != k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)
      | sK7 = X1 ) ),
    inference(superposition,[],[f13,f14])).

fof(f10,plain,
    ( sK3 != sK7
    | sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:03:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (4032)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.50  % (4040)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.50  % (4024)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (4032)Refutation not found, incomplete strategy% (4032)------------------------------
% 0.21/0.50  % (4032)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (4032)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (4032)Memory used [KB]: 1663
% 0.21/0.50  % (4032)Time elapsed: 0.094 s
% 0.21/0.50  % (4032)------------------------------
% 0.21/0.50  % (4032)------------------------------
% 0.21/0.50  % (4024)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(global_subsumption,[],[f10,f39,f54,f73,f83])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    sK0 = sK4),
% 0.21/0.50    inference(equality_resolution,[],[f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X4,X5] : (k4_tarski(sK0,sK1) != k4_tarski(X4,X5) | sK4 = X4) )),
% 0.21/0.50    inference(superposition,[],[f12,f64])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    k4_tarski(sK0,sK1) = k4_tarski(sK4,sK5)),
% 0.21/0.50    inference(equality_resolution,[],[f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X4,X5] : (k4_tarski(k4_tarski(sK0,sK1),sK2) != k4_tarski(X4,X5) | k4_tarski(sK4,sK5) = X4) )),
% 0.21/0.50    inference(superposition,[],[f12,f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    k4_tarski(k4_tarski(sK0,sK1),sK2) = k4_tarski(k4_tarski(sK4,sK5),sK6)),
% 0.21/0.50    inference(equality_resolution,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X4,X5] : (k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3) != k4_tarski(X4,X5) | k4_tarski(k4_tarski(sK4,sK5),sK6) = X4) )),
% 0.21/0.50    inference(superposition,[],[f12,f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3) = k4_tarski(k4_tarski(k4_tarski(sK4,sK5),sK6),sK7)),
% 0.21/0.50    inference(definition_unfolding,[],[f9,f11,f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7)),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,plain,(
% 0.21/0.50    (sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f5,f7])).
% 0.21/0.50  fof(f7,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)) => ((sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f5,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) => (X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4))),
% 0.21/0.50    inference(negated_conjecture,[],[f3])).
% 0.21/0.50  fof(f3,conjecture,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) => (X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_mcart_1)).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k4_tarski(X0,X1) != k4_tarski(X2,X3) | X0 = X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((X1 = X3 & X0 = X2) | k4_tarski(X0,X1) != k4_tarski(X2,X3))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (k4_tarski(X0,X1) = k4_tarski(X2,X3) => (X1 = X3 & X0 = X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_zfmisc_1)).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    sK1 = sK5),
% 0.21/0.50    inference(equality_resolution,[],[f68])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_tarski(X0,X1) != k4_tarski(sK0,sK1) | sK5 = X1) )),
% 0.21/0.50    inference(superposition,[],[f13,f64])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k4_tarski(X0,X1) != k4_tarski(X2,X3) | X1 = X3) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    sK2 = sK6),
% 0.21/0.50    inference(equality_resolution,[],[f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_tarski(X0,X1) != k4_tarski(k4_tarski(sK0,sK1),sK2) | sK6 = X1) )),
% 0.21/0.50    inference(superposition,[],[f13,f47])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    sK3 = sK7),
% 0.21/0.50    inference(equality_resolution,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_tarski(X0,X1) != k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3) | sK7 = X1) )),
% 0.21/0.50    inference(superposition,[],[f13,f14])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (4024)------------------------------
% 0.21/0.50  % (4024)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (4024)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (4024)Memory used [KB]: 10746
% 0.21/0.50  % (4024)Time elapsed: 0.098 s
% 0.21/0.50  % (4024)------------------------------
% 0.21/0.50  % (4024)------------------------------
% 0.21/0.51  % (4017)Success in time 0.148 s
%------------------------------------------------------------------------------
