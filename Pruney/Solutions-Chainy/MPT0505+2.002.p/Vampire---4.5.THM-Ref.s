%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:36 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   34 (  63 expanded)
%              Number of leaves         :    6 (  15 expanded)
%              Depth                    :   13
%              Number of atoms          :  105 ( 217 expanded)
%              Number of equality atoms :   33 (  64 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f56,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f55])).

fof(f55,plain,(
    k7_relat_1(sK2,sK0) != k7_relat_1(sK2,sK0) ),
    inference(backward_demodulation,[],[f37,f53])).

fof(f53,plain,(
    sK0 = k3_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f52,f32])).

fof(f32,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f52,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = k3_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f51,f22])).

fof(f22,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).

fof(f51,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ r1_tarski(sK0,sK0)
    | sK0 = k3_xboole_0(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f47])).

fof(f47,plain,
    ( sK0 = k3_xboole_0(sK1,sK0)
    | sK0 = k3_xboole_0(sK1,sK0)
    | ~ r1_tarski(sK0,sK0)
    | ~ r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f42,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(sK3(X0,X1,X2),X0)
      | k3_xboole_0(X1,X2) = X0
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ( ~ r1_tarski(sK3(X0,X1,X2),X0)
        & r1_tarski(sK3(X0,X1,X2),X2)
        & r1_tarski(sK3(X0,X1,X2),X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f17])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
     => ( ~ r1_tarski(sK3(X0,X1,X2),X0)
        & r1_tarski(sK3(X0,X1,X2),X2)
        & r1_tarski(sK3(X0,X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X3,X2)
              & r1_tarski(X3,X1) )
           => r1_tarski(X3,X0) )
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X1,X2) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).

fof(f42,plain,
    ( r1_tarski(sK3(sK0,sK1,sK0),sK0)
    | sK0 = k3_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f36,f32])).

fof(f36,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK0,X1)
      | r1_tarski(sK3(sK0,sK1,X1),X1)
      | sK0 = k3_xboole_0(sK1,X1) ) ),
    inference(resolution,[],[f22,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(sK3(X0,X1,X2),X2)
      | ~ r1_tarski(X0,X2)
      | k3_xboole_0(X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f37,plain,(
    k7_relat_1(sK2,sK0) != k7_relat_1(sK2,k3_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f23,f33])).

fof(f33,plain,(
    ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1)) ),
    inference(resolution,[],[f21,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f21,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f23,plain,(
    k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:51:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.48  % (14682)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.19/0.48  % (14706)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.19/0.48  % (14681)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.19/0.49  % (14681)Refutation found. Thanks to Tanya!
% 0.19/0.49  % SZS status Theorem for theBenchmark
% 0.19/0.49  % SZS output start Proof for theBenchmark
% 0.19/0.49  fof(f56,plain,(
% 0.19/0.49    $false),
% 0.19/0.49    inference(trivial_inequality_removal,[],[f55])).
% 0.19/0.49  fof(f55,plain,(
% 0.19/0.49    k7_relat_1(sK2,sK0) != k7_relat_1(sK2,sK0)),
% 0.19/0.49    inference(backward_demodulation,[],[f37,f53])).
% 0.19/0.49  fof(f53,plain,(
% 0.19/0.49    sK0 = k3_xboole_0(sK1,sK0)),
% 0.19/0.49    inference(resolution,[],[f52,f32])).
% 0.19/0.49  fof(f32,plain,(
% 0.19/0.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.19/0.49    inference(equality_resolution,[],[f28])).
% 0.19/0.49  fof(f28,plain,(
% 0.19/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.19/0.49    inference(cnf_transformation,[],[f20])).
% 0.19/0.49  fof(f20,plain,(
% 0.19/0.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.49    inference(flattening,[],[f19])).
% 0.19/0.49  fof(f19,plain,(
% 0.19/0.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.49    inference(nnf_transformation,[],[f1])).
% 0.19/0.49  fof(f1,axiom,(
% 0.19/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.49  fof(f52,plain,(
% 0.19/0.49    ~r1_tarski(sK0,sK0) | sK0 = k3_xboole_0(sK1,sK0)),
% 0.19/0.49    inference(resolution,[],[f51,f22])).
% 0.19/0.49  fof(f22,plain,(
% 0.19/0.49    r1_tarski(sK0,sK1)),
% 0.19/0.49    inference(cnf_transformation,[],[f16])).
% 0.19/0.49  fof(f16,plain,(
% 0.19/0.49    k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 0.19/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f15])).
% 0.19/0.49  fof(f15,plain,(
% 0.19/0.49    ? [X0,X1,X2] : (k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 0.19/0.49    introduced(choice_axiom,[])).
% 0.19/0.49  fof(f11,plain,(
% 0.19/0.49    ? [X0,X1,X2] : (k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.19/0.49    inference(flattening,[],[f10])).
% 0.19/0.49  fof(f10,plain,(
% 0.19/0.49    ? [X0,X1,X2] : ((k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.19/0.49    inference(ennf_transformation,[],[f9])).
% 0.19/0.49  fof(f9,negated_conjecture,(
% 0.19/0.49    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)))),
% 0.19/0.49    inference(negated_conjecture,[],[f8])).
% 0.19/0.49  fof(f8,conjecture,(
% 0.19/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).
% 0.19/0.49  fof(f51,plain,(
% 0.19/0.49    ~r1_tarski(sK0,sK1) | ~r1_tarski(sK0,sK0) | sK0 = k3_xboole_0(sK1,sK0)),
% 0.19/0.49    inference(duplicate_literal_removal,[],[f47])).
% 0.19/0.49  fof(f47,plain,(
% 0.19/0.49    sK0 = k3_xboole_0(sK1,sK0) | sK0 = k3_xboole_0(sK1,sK0) | ~r1_tarski(sK0,sK0) | ~r1_tarski(sK0,sK1)),
% 0.19/0.49    inference(resolution,[],[f42,f27])).
% 0.19/0.49  fof(f27,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~r1_tarski(sK3(X0,X1,X2),X0) | k3_xboole_0(X1,X2) = X0 | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f18])).
% 0.19/0.49  fof(f18,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | (~r1_tarski(sK3(X0,X1,X2),X0) & r1_tarski(sK3(X0,X1,X2),X2) & r1_tarski(sK3(X0,X1,X2),X1)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.19/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f17])).
% 0.19/0.49  fof(f17,plain,(
% 0.19/0.49    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(X3,X0) & r1_tarski(X3,X2) & r1_tarski(X3,X1)) => (~r1_tarski(sK3(X0,X1,X2),X0) & r1_tarski(sK3(X0,X1,X2),X2) & r1_tarski(sK3(X0,X1,X2),X1)))),
% 0.19/0.49    introduced(choice_axiom,[])).
% 0.19/0.49  fof(f14,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | ? [X3] : (~r1_tarski(X3,X0) & r1_tarski(X3,X2) & r1_tarski(X3,X1)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.19/0.49    inference(flattening,[],[f13])).
% 0.19/0.49  fof(f13,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | (? [X3] : (~r1_tarski(X3,X0) & (r1_tarski(X3,X2) & r1_tarski(X3,X1))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.19/0.49    inference(ennf_transformation,[],[f2])).
% 0.19/0.49  fof(f2,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X3,X2) & r1_tarski(X3,X1)) => r1_tarski(X3,X0)) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k3_xboole_0(X1,X2) = X0)),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).
% 0.19/0.49  fof(f42,plain,(
% 0.19/0.49    r1_tarski(sK3(sK0,sK1,sK0),sK0) | sK0 = k3_xboole_0(sK1,sK0)),
% 0.19/0.49    inference(resolution,[],[f36,f32])).
% 0.19/0.49  fof(f36,plain,(
% 0.19/0.49    ( ! [X1] : (~r1_tarski(sK0,X1) | r1_tarski(sK3(sK0,sK1,X1),X1) | sK0 = k3_xboole_0(sK1,X1)) )),
% 0.19/0.49    inference(resolution,[],[f22,f26])).
% 0.19/0.49  fof(f26,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(sK3(X0,X1,X2),X2) | ~r1_tarski(X0,X2) | k3_xboole_0(X1,X2) = X0) )),
% 0.19/0.49    inference(cnf_transformation,[],[f18])).
% 0.19/0.49  fof(f37,plain,(
% 0.19/0.49    k7_relat_1(sK2,sK0) != k7_relat_1(sK2,k3_xboole_0(sK1,sK0))),
% 0.19/0.49    inference(superposition,[],[f23,f33])).
% 0.19/0.49  fof(f33,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1))) )),
% 0.19/0.49    inference(resolution,[],[f21,f24])).
% 0.19/0.49  fof(f24,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))) )),
% 0.19/0.49    inference(cnf_transformation,[],[f12])).
% 0.19/0.49  fof(f12,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.19/0.49    inference(ennf_transformation,[],[f7])).
% 0.19/0.49  fof(f7,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 0.19/0.49  fof(f21,plain,(
% 0.19/0.49    v1_relat_1(sK2)),
% 0.19/0.49    inference(cnf_transformation,[],[f16])).
% 0.19/0.49  fof(f23,plain,(
% 0.19/0.49    k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0)),
% 0.19/0.49    inference(cnf_transformation,[],[f16])).
% 0.19/0.49  % SZS output end Proof for theBenchmark
% 0.19/0.49  % (14681)------------------------------
% 0.19/0.49  % (14681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (14681)Termination reason: Refutation
% 0.19/0.49  
% 0.19/0.49  % (14681)Memory used [KB]: 1663
% 0.19/0.49  % (14681)Time elapsed: 0.084 s
% 0.19/0.49  % (14681)------------------------------
% 0.19/0.49  % (14681)------------------------------
% 0.19/0.49  % (14679)Success in time 0.138 s
%------------------------------------------------------------------------------
