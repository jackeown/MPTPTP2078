%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :   38 (  61 expanded)
%              Number of leaves         :    9 (  16 expanded)
%              Depth                    :   10
%              Number of atoms          :  110 ( 170 expanded)
%              Number of equality atoms :   67 ( 119 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f72,plain,(
    $false ),
    inference(subsumption_resolution,[],[f68,f53])).

fof(f53,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f68,plain,(
    ~ r2_hidden(sK0,k1_tarski(sK0)) ),
    inference(backward_demodulation,[],[f60,f67])).

fof(f67,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f66,f59])).

fof(f59,plain,(
    r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(subsumption_resolution,[],[f57,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f57,plain,
    ( r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | sK0 != sK1 ),
    inference(superposition,[],[f55,f29])).

fof(f29,plain,
    ( k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | sK0 != sK1 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( sK0 = sK1
      | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) )
    & ( sK0 != sK1
      | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ( X0 = X1
          | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
        & ( X0 != X1
          | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) )
   => ( ( sK0 = sK1
        | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) )
      & ( sK0 != sK1
        | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ( X0 = X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
      & ( X0 != X1
        | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <~> X0 != X1 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      <=> X0 != X1 ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f55,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(backward_demodulation,[],[f34,f36])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_xboole_1)).

fof(f66,plain,
    ( sK0 = sK1
    | ~ r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(trivial_inequality_removal,[],[f64])).

fof(f64,plain,
    ( k1_tarski(sK0) != k1_tarski(sK0)
    | sK0 = sK1
    | ~ r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(superposition,[],[f30,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f30,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | sK0 = sK1 ),
    inference(cnf_transformation,[],[f20])).

fof(f60,plain,(
    ~ r2_hidden(sK0,k1_tarski(sK1)) ),
    inference(resolution,[],[f49,f59])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:43:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (32653)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.50  % (32669)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.50  % (32653)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 1.28/0.51  % (32661)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.28/0.51  % SZS output start Proof for theBenchmark
% 1.28/0.51  fof(f72,plain,(
% 1.28/0.51    $false),
% 1.28/0.51    inference(subsumption_resolution,[],[f68,f53])).
% 1.28/0.51  fof(f53,plain,(
% 1.28/0.51    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 1.28/0.51    inference(equality_resolution,[],[f52])).
% 1.28/0.51  fof(f52,plain,(
% 1.28/0.51    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 1.28/0.51    inference(equality_resolution,[],[f44])).
% 1.28/0.51  fof(f44,plain,(
% 1.28/0.51    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.28/0.51    inference(cnf_transformation,[],[f27])).
% 1.28/0.51  fof(f27,plain,(
% 1.28/0.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.28/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).
% 1.28/0.51  fof(f26,plain,(
% 1.28/0.51    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 1.28/0.51    introduced(choice_axiom,[])).
% 1.28/0.51  fof(f25,plain,(
% 1.28/0.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.28/0.51    inference(rectify,[],[f24])).
% 1.28/0.51  fof(f24,plain,(
% 1.28/0.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.28/0.51    inference(nnf_transformation,[],[f8])).
% 1.28/0.51  fof(f8,axiom,(
% 1.28/0.51    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.28/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.28/0.51  fof(f68,plain,(
% 1.28/0.51    ~r2_hidden(sK0,k1_tarski(sK0))),
% 1.28/0.51    inference(backward_demodulation,[],[f60,f67])).
% 1.28/0.51  fof(f67,plain,(
% 1.28/0.51    sK0 = sK1),
% 1.28/0.51    inference(subsumption_resolution,[],[f66,f59])).
% 1.28/0.51  fof(f59,plain,(
% 1.28/0.51    r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.28/0.51    inference(subsumption_resolution,[],[f57,f37])).
% 1.28/0.51  fof(f37,plain,(
% 1.28/0.51    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 1.28/0.51    inference(cnf_transformation,[],[f16])).
% 1.28/0.51  fof(f16,plain,(
% 1.28/0.51    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 1.28/0.51    inference(ennf_transformation,[],[f12])).
% 1.28/0.51  fof(f12,axiom,(
% 1.28/0.51    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.28/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).
% 1.28/0.51  fof(f57,plain,(
% 1.28/0.51    r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | sK0 != sK1),
% 1.28/0.51    inference(superposition,[],[f55,f29])).
% 1.28/0.51  fof(f29,plain,(
% 1.28/0.51    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | sK0 != sK1),
% 1.28/0.51    inference(cnf_transformation,[],[f20])).
% 1.28/0.51  fof(f20,plain,(
% 1.28/0.51    (sK0 = sK1 | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) & (sK0 != sK1 | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 1.28/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f19])).
% 1.28/0.51  fof(f19,plain,(
% 1.28/0.51    ? [X0,X1] : ((X0 = X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) & (X0 != X1 | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) => ((sK0 = sK1 | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) & (sK0 != sK1 | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))))),
% 1.28/0.51    introduced(choice_axiom,[])).
% 1.28/0.51  fof(f18,plain,(
% 1.28/0.51    ? [X0,X1] : ((X0 = X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) & (X0 != X1 | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 1.28/0.51    inference(nnf_transformation,[],[f15])).
% 1.28/0.51  fof(f15,plain,(
% 1.28/0.51    ? [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <~> X0 != X1)),
% 1.28/0.51    inference(ennf_transformation,[],[f14])).
% 1.28/0.51  fof(f14,negated_conjecture,(
% 1.28/0.51    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.28/0.51    inference(negated_conjecture,[],[f13])).
% 1.28/0.51  fof(f13,conjecture,(
% 1.28/0.51    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.28/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.28/0.51  fof(f55,plain,(
% 1.28/0.51    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.28/0.51    inference(backward_demodulation,[],[f34,f36])).
% 1.28/0.51  fof(f36,plain,(
% 1.28/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.28/0.51    inference(cnf_transformation,[],[f4])).
% 1.28/0.51  fof(f4,axiom,(
% 1.28/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.28/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.28/0.51  fof(f34,plain,(
% 1.28/0.51    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 1.28/0.51    inference(cnf_transformation,[],[f7])).
% 1.28/0.51  fof(f7,axiom,(
% 1.28/0.51    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)),
% 1.28/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_xboole_1)).
% 1.28/0.51  fof(f66,plain,(
% 1.28/0.51    sK0 = sK1 | ~r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.28/0.51    inference(trivial_inequality_removal,[],[f64])).
% 1.28/0.51  fof(f64,plain,(
% 1.28/0.51    k1_tarski(sK0) != k1_tarski(sK0) | sK0 = sK1 | ~r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.28/0.51    inference(superposition,[],[f30,f41])).
% 1.28/0.51  fof(f41,plain,(
% 1.28/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.28/0.51    inference(cnf_transformation,[],[f23])).
% 1.28/0.51  fof(f23,plain,(
% 1.28/0.51    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.28/0.51    inference(nnf_transformation,[],[f6])).
% 1.28/0.51  fof(f6,axiom,(
% 1.28/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.28/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.28/0.51  fof(f30,plain,(
% 1.28/0.51    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | sK0 = sK1),
% 1.28/0.51    inference(cnf_transformation,[],[f20])).
% 1.28/0.51  fof(f60,plain,(
% 1.28/0.51    ~r2_hidden(sK0,k1_tarski(sK1))),
% 1.28/0.51    inference(resolution,[],[f49,f59])).
% 1.28/0.51  fof(f49,plain,(
% 1.28/0.51    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.28/0.51    inference(cnf_transformation,[],[f17])).
% 1.28/0.51  fof(f17,plain,(
% 1.28/0.51    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 1.28/0.51    inference(ennf_transformation,[],[f11])).
% 1.28/0.51  fof(f11,axiom,(
% 1.28/0.51    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 1.28/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 1.28/0.51  % SZS output end Proof for theBenchmark
% 1.28/0.51  % (32653)------------------------------
% 1.28/0.51  % (32653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.51  % (32653)Termination reason: Refutation
% 1.28/0.51  
% 1.28/0.51  % (32653)Memory used [KB]: 1663
% 1.28/0.51  % (32653)Time elapsed: 0.096 s
% 1.28/0.51  % (32653)------------------------------
% 1.28/0.51  % (32653)------------------------------
% 1.28/0.51  % (32643)Success in time 0.159 s
%------------------------------------------------------------------------------
