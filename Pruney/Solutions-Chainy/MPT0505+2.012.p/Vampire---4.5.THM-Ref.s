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
% DateTime   : Thu Dec  3 12:48:37 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   36 (  55 expanded)
%              Number of leaves         :    7 (  14 expanded)
%              Depth                    :   11
%              Number of atoms          :  107 ( 181 expanded)
%              Number of equality atoms :   35 (  55 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f59,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f58])).

fof(f58,plain,(
    k7_relat_1(sK2,sK0) != k7_relat_1(sK2,sK0) ),
    inference(backward_demodulation,[],[f43,f57])).

fof(f57,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f56,f32])).

fof(f32,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f56,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = k3_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f51,f30])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f51,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = k3_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f48,f22])).

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

fof(f48,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X3,X3)
      | ~ r1_tarski(X3,X2)
      | k3_xboole_0(X2,X3) = X3 ) ),
    inference(duplicate_literal_removal,[],[f47])).

fof(f47,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X2,X3) = X3
      | ~ r1_tarski(X3,X3)
      | ~ r1_tarski(X3,X2)
      | k3_xboole_0(X2,X3) = X3
      | ~ r1_tarski(X3,X3)
      | ~ r1_tarski(X3,X2) ) ),
    inference(resolution,[],[f26,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK3(X0,X1,X2),X2)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f17])).

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

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X3,X2)
              & r1_tarski(X3,X1) )
           => r1_tarski(X3,X0) )
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X1,X2) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(sK3(X0,X1,X2),X0)
      | k3_xboole_0(X1,X2) = X0
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f43,plain,(
    k7_relat_1(sK2,sK0) != k7_relat_1(sK2,k3_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f42,f30])).

fof(f42,plain,(
    k7_relat_1(sK2,sK0) != k7_relat_1(sK2,k3_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f23,f39])).

fof(f39,plain,(
    ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1)) ),
    inference(resolution,[],[f31,f21])).

fof(f21,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f23,plain,(
    k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:06:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.23/0.51  % (27825)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.23/0.52  % (27842)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.23/0.52  % (27828)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.23/0.52  % (27826)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.23/0.52  % (27830)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.23/0.52  % (27830)Refutation found. Thanks to Tanya!
% 0.23/0.52  % SZS status Theorem for theBenchmark
% 0.23/0.52  % SZS output start Proof for theBenchmark
% 0.23/0.52  fof(f59,plain,(
% 0.23/0.52    $false),
% 0.23/0.52    inference(trivial_inequality_removal,[],[f58])).
% 0.23/0.52  fof(f58,plain,(
% 0.23/0.52    k7_relat_1(sK2,sK0) != k7_relat_1(sK2,sK0)),
% 0.23/0.52    inference(backward_demodulation,[],[f43,f57])).
% 0.23/0.52  fof(f57,plain,(
% 0.23/0.52    sK0 = k3_xboole_0(sK0,sK1)),
% 0.23/0.52    inference(resolution,[],[f56,f32])).
% 0.23/0.52  fof(f32,plain,(
% 0.23/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.23/0.52    inference(equality_resolution,[],[f28])).
% 0.23/0.52  fof(f28,plain,(
% 0.23/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.23/0.52    inference(cnf_transformation,[],[f20])).
% 0.23/0.52  fof(f20,plain,(
% 0.23/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.23/0.52    inference(flattening,[],[f19])).
% 0.23/0.52  fof(f19,plain,(
% 0.23/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.23/0.52    inference(nnf_transformation,[],[f2])).
% 0.23/0.52  fof(f2,axiom,(
% 0.23/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.23/0.52  fof(f56,plain,(
% 0.23/0.52    ~r1_tarski(sK0,sK0) | sK0 = k3_xboole_0(sK0,sK1)),
% 0.23/0.52    inference(forward_demodulation,[],[f51,f30])).
% 0.23/0.52  fof(f30,plain,(
% 0.23/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f1])).
% 0.23/0.52  fof(f1,axiom,(
% 0.23/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.23/0.52  fof(f51,plain,(
% 0.23/0.52    ~r1_tarski(sK0,sK0) | sK0 = k3_xboole_0(sK1,sK0)),
% 0.23/0.52    inference(resolution,[],[f48,f22])).
% 0.23/0.52  fof(f22,plain,(
% 0.23/0.52    r1_tarski(sK0,sK1)),
% 0.23/0.52    inference(cnf_transformation,[],[f16])).
% 0.23/0.52  fof(f16,plain,(
% 0.23/0.52    k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 0.23/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f15])).
% 0.23/0.52  fof(f15,plain,(
% 0.23/0.52    ? [X0,X1,X2] : (k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 0.23/0.52    introduced(choice_axiom,[])).
% 0.23/0.52  fof(f11,plain,(
% 0.23/0.52    ? [X0,X1,X2] : (k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.23/0.52    inference(flattening,[],[f10])).
% 0.23/0.52  fof(f10,plain,(
% 0.23/0.52    ? [X0,X1,X2] : ((k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.23/0.52    inference(ennf_transformation,[],[f9])).
% 0.23/0.52  fof(f9,negated_conjecture,(
% 0.23/0.52    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)))),
% 0.23/0.52    inference(negated_conjecture,[],[f8])).
% 0.23/0.52  fof(f8,conjecture,(
% 0.23/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).
% 0.23/0.52  fof(f48,plain,(
% 0.23/0.52    ( ! [X2,X3] : (~r1_tarski(X3,X3) | ~r1_tarski(X3,X2) | k3_xboole_0(X2,X3) = X3) )),
% 0.23/0.52    inference(duplicate_literal_removal,[],[f47])).
% 0.23/0.52  fof(f47,plain,(
% 0.23/0.52    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = X3 | ~r1_tarski(X3,X3) | ~r1_tarski(X3,X2) | k3_xboole_0(X2,X3) = X3 | ~r1_tarski(X3,X3) | ~r1_tarski(X3,X2)) )),
% 0.23/0.52    inference(resolution,[],[f26,f25])).
% 0.23/0.52  fof(f25,plain,(
% 0.23/0.52    ( ! [X2,X0,X1] : (r1_tarski(sK3(X0,X1,X2),X2) | k3_xboole_0(X1,X2) = X0 | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f18])).
% 0.23/0.52  fof(f18,plain,(
% 0.23/0.52    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | (~r1_tarski(sK3(X0,X1,X2),X0) & r1_tarski(sK3(X0,X1,X2),X2) & r1_tarski(sK3(X0,X1,X2),X1)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.23/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f17])).
% 0.23/0.52  fof(f17,plain,(
% 0.23/0.52    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(X3,X0) & r1_tarski(X3,X2) & r1_tarski(X3,X1)) => (~r1_tarski(sK3(X0,X1,X2),X0) & r1_tarski(sK3(X0,X1,X2),X2) & r1_tarski(sK3(X0,X1,X2),X1)))),
% 0.23/0.52    introduced(choice_axiom,[])).
% 0.23/0.52  fof(f13,plain,(
% 0.23/0.52    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | ? [X3] : (~r1_tarski(X3,X0) & r1_tarski(X3,X2) & r1_tarski(X3,X1)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.23/0.52    inference(flattening,[],[f12])).
% 0.23/0.52  fof(f12,plain,(
% 0.23/0.52    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | (? [X3] : (~r1_tarski(X3,X0) & (r1_tarski(X3,X2) & r1_tarski(X3,X1))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.23/0.52    inference(ennf_transformation,[],[f3])).
% 0.23/0.52  fof(f3,axiom,(
% 0.23/0.52    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X3,X2) & r1_tarski(X3,X1)) => r1_tarski(X3,X0)) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k3_xboole_0(X1,X2) = X0)),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).
% 0.23/0.52  fof(f26,plain,(
% 0.23/0.52    ( ! [X2,X0,X1] : (~r1_tarski(sK3(X0,X1,X2),X0) | k3_xboole_0(X1,X2) = X0 | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f18])).
% 0.23/0.52  fof(f43,plain,(
% 0.23/0.52    k7_relat_1(sK2,sK0) != k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),
% 0.23/0.52    inference(forward_demodulation,[],[f42,f30])).
% 0.23/0.52  fof(f42,plain,(
% 0.23/0.52    k7_relat_1(sK2,sK0) != k7_relat_1(sK2,k3_xboole_0(sK1,sK0))),
% 0.23/0.52    inference(superposition,[],[f23,f39])).
% 0.23/0.52  fof(f39,plain,(
% 0.23/0.52    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1))) )),
% 0.23/0.52    inference(resolution,[],[f31,f21])).
% 0.23/0.52  fof(f21,plain,(
% 0.23/0.52    v1_relat_1(sK2)),
% 0.23/0.52    inference(cnf_transformation,[],[f16])).
% 0.23/0.52  fof(f31,plain,(
% 0.23/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))) )),
% 0.23/0.52    inference(cnf_transformation,[],[f14])).
% 0.23/0.52  fof(f14,plain,(
% 0.23/0.52    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.23/0.52    inference(ennf_transformation,[],[f7])).
% 0.23/0.52  fof(f7,axiom,(
% 0.23/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 0.23/0.52  fof(f23,plain,(
% 0.23/0.52    k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0)),
% 0.23/0.52    inference(cnf_transformation,[],[f16])).
% 0.23/0.52  % SZS output end Proof for theBenchmark
% 0.23/0.53  % (27836)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.23/0.53  % (27839)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.23/0.53  % (27831)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.53  % (27834)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.23/0.53  % (27833)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.23/0.53  % (27848)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.23/0.54  % (27844)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.23/0.54  % (27851)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.23/0.54  % (27849)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.23/0.54  % (27839)Refutation not found, incomplete strategy% (27839)------------------------------
% 0.23/0.54  % (27839)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (27839)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (27839)Memory used [KB]: 1663
% 0.23/0.54  % (27839)Time elapsed: 0.124 s
% 0.23/0.54  % (27839)------------------------------
% 0.23/0.54  % (27839)------------------------------
% 0.23/0.54  % (27835)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.23/0.54  % (27838)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.23/0.54  % (27830)------------------------------
% 0.23/0.54  % (27830)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (27830)Termination reason: Refutation
% 0.23/0.54  
% 0.23/0.54  % (27830)Memory used [KB]: 1663
% 0.23/0.54  % (27830)Time elapsed: 0.100 s
% 0.23/0.54  % (27830)------------------------------
% 0.23/0.54  % (27830)------------------------------
% 0.23/0.54  % (27824)Success in time 0.174 s
%------------------------------------------------------------------------------
