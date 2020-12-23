%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   37 (  54 expanded)
%              Number of leaves         :    9 (  16 expanded)
%              Depth                    :   12
%              Number of atoms          :  102 ( 141 expanded)
%              Number of equality atoms :   13 (  22 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f71,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f70])).

fof(f70,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f33,f67])).

fof(f67,plain,(
    k1_xboole_0 = k9_relat_1(sK0,k1_xboole_0) ),
    inference(resolution,[],[f63,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f63,plain,(
    v1_xboole_0(k9_relat_1(sK0,k1_xboole_0)) ),
    inference(resolution,[],[f62,f37])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f62,plain,(
    ! [X0] : ~ r2_hidden(X0,k9_relat_1(sK0,k1_xboole_0)) ),
    inference(resolution,[],[f61,f56])).

fof(f56,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f49,f55])).

fof(f55,plain,(
    k1_xboole_0 = sK3 ),
    inference(resolution,[],[f35,f49])).

fof(f49,plain,(
    v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f3,f30])).

fof(f30,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK3) ),
    introduced(choice_axiom,[])).

fof(f3,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,k9_relat_1(sK0,X1)) ) ),
    inference(resolution,[],[f60,f36])).

fof(f36,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1,sK0),X1)
      | ~ r2_hidden(X0,k9_relat_1(sK0,X1)) ) ),
    inference(resolution,[],[f43,f32])).

fof(f32,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k1_xboole_0 != k9_relat_1(sK0,k1_xboole_0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k9_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
   => ( k1_xboole_0 != k9_relat_1(sK0,k1_xboole_0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( k1_xboole_0 != k9_relat_1(X0,k1_xboole_0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK2(X0,X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2)
            & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2)
        & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f33,plain,(
    k1_xboole_0 != k9_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:11:05 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.41  % (10730)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.43  % (10730)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f71,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(trivial_inequality_removal,[],[f70])).
% 0.22/0.43  fof(f70,plain,(
% 0.22/0.43    k1_xboole_0 != k1_xboole_0),
% 0.22/0.43    inference(superposition,[],[f33,f67])).
% 0.22/0.43  fof(f67,plain,(
% 0.22/0.43    k1_xboole_0 = k9_relat_1(sK0,k1_xboole_0)),
% 0.22/0.43    inference(resolution,[],[f63,f35])).
% 0.22/0.43  fof(f35,plain,(
% 0.22/0.43    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f16])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.43  fof(f63,plain,(
% 0.22/0.43    v1_xboole_0(k9_relat_1(sK0,k1_xboole_0))),
% 0.22/0.43    inference(resolution,[],[f62,f37])).
% 0.22/0.43  fof(f37,plain,(
% 0.22/0.43    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v1_xboole_0(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f25])).
% 0.22/0.43  fof(f25,plain,(
% 0.22/0.43    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f24])).
% 0.22/0.43  fof(f24,plain,(
% 0.22/0.43    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f23,plain,(
% 0.22/0.43    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.43    inference(rectify,[],[f22])).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.43    inference(nnf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.43  fof(f62,plain,(
% 0.22/0.43    ( ! [X0] : (~r2_hidden(X0,k9_relat_1(sK0,k1_xboole_0))) )),
% 0.22/0.43    inference(resolution,[],[f61,f56])).
% 0.22/0.43  fof(f56,plain,(
% 0.22/0.43    v1_xboole_0(k1_xboole_0)),
% 0.22/0.43    inference(backward_demodulation,[],[f49,f55])).
% 0.22/0.43  fof(f55,plain,(
% 0.22/0.43    k1_xboole_0 = sK3),
% 0.22/0.43    inference(resolution,[],[f35,f49])).
% 0.22/0.43  fof(f49,plain,(
% 0.22/0.43    v1_xboole_0(sK3)),
% 0.22/0.43    inference(cnf_transformation,[],[f31])).
% 0.22/0.43  fof(f31,plain,(
% 0.22/0.43    v1_xboole_0(sK3)),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f3,f30])).
% 0.22/0.43  fof(f30,plain,(
% 0.22/0.43    ? [X0] : v1_xboole_0(X0) => v1_xboole_0(sK3)),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ? [X0] : v1_xboole_0(X0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).
% 0.22/0.43  fof(f61,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,k9_relat_1(sK0,X1))) )),
% 0.22/0.43    inference(resolution,[],[f60,f36])).
% 0.22/0.43  fof(f36,plain,(
% 0.22/0.43    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f25])).
% 0.22/0.43  fof(f60,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,sK0),X1) | ~r2_hidden(X0,k9_relat_1(sK0,X1))) )),
% 0.22/0.43    inference(resolution,[],[f43,f32])).
% 0.22/0.43  fof(f32,plain,(
% 0.22/0.43    v1_relat_1(sK0)),
% 0.22/0.43    inference(cnf_transformation,[],[f21])).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    k1_xboole_0 != k9_relat_1(sK0,k1_xboole_0) & v1_relat_1(sK0)),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f20])).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    ? [X0] : (k1_xboole_0 != k9_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => (k1_xboole_0 != k9_relat_1(sK0,k1_xboole_0) & v1_relat_1(sK0))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    ? [X0] : (k1_xboole_0 != k9_relat_1(X0,k1_xboole_0) & v1_relat_1(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f14])).
% 0.22/0.43  fof(f14,negated_conjecture,(
% 0.22/0.43    ~! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0))),
% 0.22/0.43    inference(negated_conjecture,[],[f13])).
% 0.22/0.43  fof(f13,conjecture,(
% 0.22/0.43    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).
% 0.22/0.43  fof(f43,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK2(X0,X1,X2),X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f29])).
% 0.22/0.43  fof(f29,plain,(
% 0.22/0.43    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).
% 0.22/0.43  fof(f28,plain,(
% 0.22/0.43    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2))))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.43    inference(rectify,[],[f26])).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.43    inference(nnf_transformation,[],[f18])).
% 0.22/0.43  fof(f18,plain,(
% 0.22/0.43    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.22/0.43    inference(ennf_transformation,[],[f12])).
% 0.22/0.43  fof(f12,axiom,(
% 0.22/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.22/0.43  fof(f33,plain,(
% 0.22/0.43    k1_xboole_0 != k9_relat_1(sK0,k1_xboole_0)),
% 0.22/0.43    inference(cnf_transformation,[],[f21])).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (10730)------------------------------
% 0.22/0.43  % (10730)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (10730)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (10730)Memory used [KB]: 6140
% 0.22/0.43  % (10730)Time elapsed: 0.039 s
% 0.22/0.43  % (10730)------------------------------
% 0.22/0.43  % (10730)------------------------------
% 0.22/0.43  % (10727)Success in time 0.07 s
%------------------------------------------------------------------------------
