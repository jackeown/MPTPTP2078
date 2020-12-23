%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   34 ( 149 expanded)
%              Number of leaves         :    6 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :   86 ( 362 expanded)
%              Number of equality atoms :   85 ( 361 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f125,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f111,f108,f16])).

% (20958)Termination reason: Refutation not found, incomplete strategy
fof(f16,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
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

fof(f108,plain,(
    k4_tarski(sK0,sK1) = k4_tarski(sK4,sK1) ),
    inference(backward_demodulation,[],[f30,f96])).

fof(f96,plain,(
    sK1 = sK5 ),
    inference(unit_resulting_resolution,[],[f30,f17])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f30,plain,(
    k4_tarski(sK0,sK1) = k4_tarski(sK4,sK5) ),
    inference(unit_resulting_resolution,[],[f22,f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_tarski(k4_tarski(X0,X1),X2) != k4_tarski(k4_tarski(X3,X4),X5)
      | X0 = X3 ) ),
    inference(definition_unfolding,[],[f18,f14,f14])).

fof(f14,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f18,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X0 = X3
      | k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5)
     => ( X2 = X5
        & X1 = X4
        & X0 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_mcart_1)).

fof(f22,plain,(
    k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3) = k4_tarski(k4_tarski(k4_tarski(sK4,sK5),sK6),sK7) ),
    inference(definition_unfolding,[],[f12,f21,f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f15,f14])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f12,plain,(
    k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ( sK3 != sK7
      | sK2 != sK6
      | sK1 != sK5
      | sK0 != sK4 )
    & k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f7,f10])).

fof(f10,plain,
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

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)
       => ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)
     => ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_mcart_1)).

fof(f111,plain,(
    sK0 != sK4 ),
    inference(subsumption_resolution,[],[f110,f32])).

fof(f32,plain,(
    sK3 = sK7 ),
    inference(unit_resulting_resolution,[],[f22,f17])).

fof(f110,plain,
    ( sK3 != sK7
    | sK0 != sK4 ),
    inference(trivial_inequality_removal,[],[f109])).

fof(f109,plain,
    ( sK1 != sK1
    | sK3 != sK7
    | sK0 != sK4 ),
    inference(backward_demodulation,[],[f52,f96])).

fof(f52,plain,
    ( sK3 != sK7
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(trivial_inequality_removal,[],[f51])).

fof(f51,plain,
    ( sK2 != sK2
    | sK3 != sK7
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(backward_demodulation,[],[f13,f31])).

fof(f31,plain,(
    sK2 = sK6 ),
    inference(unit_resulting_resolution,[],[f22,f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_tarski(k4_tarski(X0,X1),X2) != k4_tarski(k4_tarski(X3,X4),X5)
      | X1 = X4 ) ),
    inference(definition_unfolding,[],[f19,f14,f14])).

fof(f19,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X1 = X4
      | k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f13,plain,
    ( sK3 != sK7
    | sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:58:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (20939)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.51  % (20936)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (20950)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.52  % (20958)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (20943)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.52  % (20958)Refutation not found, incomplete strategy% (20958)------------------------------
% 0.21/0.52  % (20958)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (20950)Refutation not found, incomplete strategy% (20950)------------------------------
% 0.21/0.52  % (20950)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (20950)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (20950)Memory used [KB]: 1663
% 0.21/0.52  % (20950)Time elapsed: 0.114 s
% 0.21/0.52  % (20950)------------------------------
% 0.21/0.52  % (20950)------------------------------
% 0.21/0.52  % (20936)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f111,f108,f16])).
% 0.21/0.53  % (20958)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k4_tarski(X0,X1) != k4_tarski(X2,X3) | X0 = X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((X1 = X3 & X0 = X2) | k4_tarski(X0,X1) != k4_tarski(X2,X3))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (k4_tarski(X0,X1) = k4_tarski(X2,X3) => (X1 = X3 & X0 = X2))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_zfmisc_1)).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    k4_tarski(sK0,sK1) = k4_tarski(sK4,sK1)),
% 0.21/0.53    inference(backward_demodulation,[],[f30,f96])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    sK1 = sK5),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f30,f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k4_tarski(X0,X1) != k4_tarski(X2,X3) | X1 = X3) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    k4_tarski(sK0,sK1) = k4_tarski(sK4,sK5)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f22,f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_tarski(k4_tarski(X0,X1),X2) != k4_tarski(k4_tarski(X3,X4),X5) | X0 = X3) )),
% 0.21/0.53    inference(definition_unfolding,[],[f18,f14,f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (X0 = X3 | k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5] : ((X2 = X5 & X1 = X4 & X0 = X3) | k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5] : (k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5) => (X2 = X5 & X1 = X4 & X0 = X3))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_mcart_1)).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3) = k4_tarski(k4_tarski(k4_tarski(sK4,sK5),sK6),sK7)),
% 0.21/0.53    inference(definition_unfolding,[],[f12,f21,f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f15,f14])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7)),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    (sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f7,f10])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)) => ((sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f7,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) => (X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4))),
% 0.21/0.53    inference(negated_conjecture,[],[f5])).
% 0.21/0.53  fof(f5,conjecture,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) => (X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_mcart_1)).
% 0.21/0.53  fof(f111,plain,(
% 0.21/0.53    sK0 != sK4),
% 0.21/0.53    inference(subsumption_resolution,[],[f110,f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    sK3 = sK7),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f22,f17])).
% 0.21/0.53  fof(f110,plain,(
% 0.21/0.53    sK3 != sK7 | sK0 != sK4),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f109])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    sK1 != sK1 | sK3 != sK7 | sK0 != sK4),
% 0.21/0.53    inference(backward_demodulation,[],[f52,f96])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    sK3 != sK7 | sK1 != sK5 | sK0 != sK4),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    sK2 != sK2 | sK3 != sK7 | sK1 != sK5 | sK0 != sK4),
% 0.21/0.53    inference(backward_demodulation,[],[f13,f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    sK2 = sK6),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f22,f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_tarski(k4_tarski(X0,X1),X2) != k4_tarski(k4_tarski(X3,X4),X5) | X1 = X4) )),
% 0.21/0.53    inference(definition_unfolding,[],[f19,f14,f14])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (X1 = X4 | k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (20936)------------------------------
% 0.21/0.53  % (20936)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (20936)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (20936)Memory used [KB]: 1791
% 0.21/0.53  % (20936)Time elapsed: 0.122 s
% 0.21/0.53  % (20936)------------------------------
% 0.21/0.53  % (20936)------------------------------
% 0.21/0.53  
% 0.21/0.53  % (20958)Memory used [KB]: 6140
% 0.21/0.53  % (20958)Time elapsed: 0.115 s
% 0.21/0.53  % (20958)------------------------------
% 0.21/0.53  % (20958)------------------------------
% 0.21/0.53  % (20931)Success in time 0.169 s
%------------------------------------------------------------------------------
