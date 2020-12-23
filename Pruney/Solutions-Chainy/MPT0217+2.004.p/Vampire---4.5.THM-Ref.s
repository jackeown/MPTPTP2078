%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 120 expanded)
%              Number of leaves         :    6 (  30 expanded)
%              Depth                    :   16
%              Number of atoms          :  136 ( 651 expanded)
%              Number of equality atoms :  104 ( 506 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f75,plain,(
    $false ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X1] : k1_tarski(X1) != k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f64,f62])).

fof(f62,plain,(
    sK0 != sK1 ),
    inference(superposition,[],[f19,f49])).

fof(f49,plain,(
    sK1 = sK3 ),
    inference(subsumption_resolution,[],[f44,f19])).

fof(f44,plain,
    ( sK0 = sK3
    | sK1 = sK3 ),
    inference(resolution,[],[f33,f34])).

fof(f34,plain,(
    r2_hidden(sK3,k2_tarski(sK0,sK1)) ),
    inference(superposition,[],[f30,f17])).

fof(f17,plain,(
    k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( sK0 != sK3
    & sK0 != sK2
    & k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & k2_tarski(X0,X1) = k2_tarski(X2,X3) )
   => ( sK0 != sK3
      & sK0 != sK2
      & k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & k2_tarski(X0,X1) = k2_tarski(X2,X3) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & k2_tarski(X0,X1) = k2_tarski(X2,X3) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & k2_tarski(X0,X1) = k2_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_zfmisc_1)).

fof(f30,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK4(X0,X1,X2) != X1
              & sK4(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X1
            | sK4(X0,X1,X2) = X0
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f15])).

fof(f15,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X1
            & sK4(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X1
          | sK4(X0,X1,X2) = X0
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f33,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f19,plain,(
    sK0 != sK3 ),
    inference(cnf_transformation,[],[f11])).

fof(f64,plain,(
    ! [X1] :
      ( k1_tarski(X1) != k1_tarski(sK1)
      | sK0 = sK1 ) ),
    inference(superposition,[],[f22,f57])).

fof(f57,plain,(
    k2_tarski(sK0,sK1) = k1_tarski(sK1) ),
    inference(forward_demodulation,[],[f54,f20])).

fof(f20,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f54,plain,(
    k2_tarski(sK0,sK1) = k2_tarski(sK1,sK1) ),
    inference(backward_demodulation,[],[f52,f53])).

fof(f53,plain,(
    sK1 = sK2 ),
    inference(subsumption_resolution,[],[f45,f18])).

fof(f18,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f11])).

fof(f45,plain,
    ( sK0 = sK2
    | sK1 = sK2 ),
    inference(resolution,[],[f33,f35])).

fof(f35,plain,(
    r2_hidden(sK2,k2_tarski(sK0,sK1)) ),
    inference(superposition,[],[f32,f17])).

fof(f32,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f52,plain,(
    k2_tarski(sK0,sK1) = k2_tarski(sK2,sK1) ),
    inference(backward_demodulation,[],[f17,f49])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) != k2_tarski(X1,X2)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( X1 = X2
      | k1_tarski(X0) != k2_tarski(X1,X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k2_tarski(X1,X2)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:46:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (24719)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.49  % (24719)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(equality_resolution,[],[f68])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ( ! [X1] : (k1_tarski(X1) != k1_tarski(sK1)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f64,f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    sK0 != sK1),
% 0.21/0.49    inference(superposition,[],[f19,f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    sK1 = sK3),
% 0.21/0.49    inference(subsumption_resolution,[],[f44,f19])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    sK0 = sK3 | sK1 = sK3),
% 0.21/0.49    inference(resolution,[],[f33,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    r2_hidden(sK3,k2_tarski(sK0,sK1))),
% 0.21/0.49    inference(superposition,[],[f30,f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    sK0 != sK3 & sK0 != sK2 & k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & k2_tarski(X0,X1) = k2_tarski(X2,X3)) => (sK0 != sK3 & sK0 != sK2 & k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & k2_tarski(X0,X1) = k2_tarski(X2,X3))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & k2_tarski(X0,X1) = k2_tarski(X2,X3))),
% 0.21/0.49    inference(negated_conjecture,[],[f5])).
% 0.21/0.49  fof(f5,conjecture,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & k2_tarski(X0,X1) = k2_tarski(X2,X3))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_zfmisc_1)).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 0.21/0.49    inference(equality_resolution,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 0.21/0.49    inference(equality_resolution,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.49    inference(rectify,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.49    inference(flattening,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.49    inference(nnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_tarski(X0,X1)) | X0 = X4 | X1 = X4) )),
% 0.21/0.49    inference(equality_resolution,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    sK0 != sK3),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ( ! [X1] : (k1_tarski(X1) != k1_tarski(sK1) | sK0 = sK1) )),
% 0.21/0.49    inference(superposition,[],[f22,f57])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    k2_tarski(sK0,sK1) = k1_tarski(sK1)),
% 0.21/0.49    inference(forward_demodulation,[],[f54,f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    k2_tarski(sK0,sK1) = k2_tarski(sK1,sK1)),
% 0.21/0.49    inference(backward_demodulation,[],[f52,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    sK1 = sK2),
% 0.21/0.49    inference(subsumption_resolution,[],[f45,f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    sK0 != sK2),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    sK0 = sK2 | sK1 = sK2),
% 0.21/0.49    inference(resolution,[],[f33,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    r2_hidden(sK2,k2_tarski(sK0,sK1))),
% 0.21/0.49    inference(superposition,[],[f32,f17])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 0.21/0.49    inference(equality_resolution,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 0.21/0.49    inference(equality_resolution,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    k2_tarski(sK0,sK1) = k2_tarski(sK2,sK1)),
% 0.21/0.49    inference(backward_demodulation,[],[f17,f49])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_tarski(X0) != k2_tarski(X1,X2) | X1 = X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (X1 = X2 | k1_tarski(X0) != k2_tarski(X1,X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X1 = X2)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_zfmisc_1)).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (24719)------------------------------
% 0.21/0.49  % (24719)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (24719)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (24719)Memory used [KB]: 1663
% 0.21/0.49  % (24719)Time elapsed: 0.068 s
% 0.21/0.49  % (24719)------------------------------
% 0.21/0.49  % (24719)------------------------------
% 0.21/0.50  % (24709)Success in time 0.131 s
%------------------------------------------------------------------------------
