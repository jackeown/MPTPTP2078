%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:55 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :   38 (  77 expanded)
%              Number of leaves         :    8 (  24 expanded)
%              Depth                    :   14
%              Number of atoms          :  107 ( 329 expanded)
%              Number of equality atoms :    6 (   9 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (14960)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
fof(f596,plain,(
    $false ),
    inference(subsumption_resolution,[],[f595,f26])).

fof(f26,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1))
    & r1_tarski(sK0,sK1)
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f22,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
            & r1_tarski(X0,X1)
            & r1_tarski(X2,X3)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(X3,sK1))
          & r1_tarski(sK0,sK1)
          & r1_tarski(sK2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(X3,sK1))
        & r1_tarski(sK0,sK1)
        & r1_tarski(sK2,X3)
        & v1_relat_1(X3) )
   => ( ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1))
      & r1_tarski(sK0,sK1)
      & r1_tarski(sK2,sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_relat_1)).

fof(f595,plain,(
    ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f594,f27])).

fof(f27,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f594,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f593,f28])).

fof(f28,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f593,plain,
    ( ~ r1_tarski(sK2,sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f591,f29])).

fof(f29,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f591,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ r1_tarski(sK2,sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f559,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_relat_1)).

fof(f559,plain,(
    ! [X1] :
      ( ~ r1_tarski(k9_relat_1(sK2,X1),k9_relat_1(sK3,sK1))
      | ~ r1_tarski(sK0,X1) ) ),
    inference(superposition,[],[f538,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f538,plain,(
    ! [X1] : ~ r1_tarski(k9_relat_1(sK2,k2_xboole_0(sK0,X1)),k9_relat_1(sK3,sK1)) ),
    inference(subsumption_resolution,[],[f524,f26])).

fof(f524,plain,(
    ! [X1] :
      ( ~ r1_tarski(k9_relat_1(sK2,k2_xboole_0(sK0,X1)),k9_relat_1(sK3,sK1))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f188,f170])).

fof(f170,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,k2_xboole_0(X1,X2)))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f31,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t153_relat_1)).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f188,plain,(
    ! [X11] :
      ( ~ r1_tarski(k9_relat_1(sK2,sK0),X11)
      | ~ r1_tarski(X11,k9_relat_1(sK3,sK1)) ) ),
    inference(resolution,[],[f57,f30])).

fof(f30,plain,(
    ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f41,f34])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:20:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (14959)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.46/0.55  % (14967)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.46/0.57  % (14976)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.46/0.57  % (14959)Refutation found. Thanks to Tanya!
% 1.46/0.57  % SZS status Theorem for theBenchmark
% 1.46/0.57  % SZS output start Proof for theBenchmark
% 1.46/0.57  % (14960)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.46/0.57  fof(f596,plain,(
% 1.46/0.57    $false),
% 1.46/0.57    inference(subsumption_resolution,[],[f595,f26])).
% 1.46/0.57  fof(f26,plain,(
% 1.46/0.57    v1_relat_1(sK2)),
% 1.46/0.57    inference(cnf_transformation,[],[f23])).
% 1.46/0.57  fof(f23,plain,(
% 1.46/0.57    (~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 1.46/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f22,f21])).
% 1.46/0.57  fof(f21,plain,(
% 1.46/0.57    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2)) => (? [X3] : (~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(X3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) & v1_relat_1(sK2))),
% 1.46/0.57    introduced(choice_axiom,[])).
% 1.46/0.57  fof(f22,plain,(
% 1.46/0.57    ? [X3] : (~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(X3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) => (~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3))),
% 1.46/0.57    introduced(choice_axiom,[])).
% 1.46/0.57  fof(f13,plain,(
% 1.46/0.57    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 1.46/0.57    inference(flattening,[],[f12])).
% 1.46/0.57  fof(f12,plain,(
% 1.46/0.57    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 1.46/0.57    inference(ennf_transformation,[],[f11])).
% 1.46/0.57  fof(f11,negated_conjecture,(
% 1.46/0.57    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)))))),
% 1.46/0.57    inference(negated_conjecture,[],[f10])).
% 1.46/0.57  fof(f10,conjecture,(
% 1.46/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)))))),
% 1.46/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_relat_1)).
% 1.46/0.57  fof(f595,plain,(
% 1.46/0.57    ~v1_relat_1(sK2)),
% 1.46/0.57    inference(subsumption_resolution,[],[f594,f27])).
% 1.46/0.57  fof(f27,plain,(
% 1.46/0.57    v1_relat_1(sK3)),
% 1.46/0.57    inference(cnf_transformation,[],[f23])).
% 1.46/0.57  fof(f594,plain,(
% 1.46/0.57    ~v1_relat_1(sK3) | ~v1_relat_1(sK2)),
% 1.46/0.57    inference(subsumption_resolution,[],[f593,f28])).
% 1.46/0.57  fof(f28,plain,(
% 1.46/0.57    r1_tarski(sK2,sK3)),
% 1.46/0.57    inference(cnf_transformation,[],[f23])).
% 1.46/0.57  fof(f593,plain,(
% 1.46/0.57    ~r1_tarski(sK2,sK3) | ~v1_relat_1(sK3) | ~v1_relat_1(sK2)),
% 1.46/0.57    inference(subsumption_resolution,[],[f591,f29])).
% 1.46/0.57  fof(f29,plain,(
% 1.46/0.57    r1_tarski(sK0,sK1)),
% 1.46/0.57    inference(cnf_transformation,[],[f23])).
% 1.46/0.57  fof(f591,plain,(
% 1.46/0.57    ~r1_tarski(sK0,sK1) | ~r1_tarski(sK2,sK3) | ~v1_relat_1(sK3) | ~v1_relat_1(sK2)),
% 1.46/0.57    inference(resolution,[],[f559,f33])).
% 1.46/0.57  fof(f33,plain,(
% 1.46/0.57    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f15])).
% 1.46/0.57  fof(f15,plain,(
% 1.46/0.57    ! [X0,X1] : (! [X2] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.46/0.57    inference(flattening,[],[f14])).
% 1.46/0.57  fof(f14,plain,(
% 1.46/0.57    ! [X0,X1] : (! [X2] : ((r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.46/0.57    inference(ennf_transformation,[],[f9])).
% 1.46/0.57  fof(f9,axiom,(
% 1.46/0.57    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)))))),
% 1.46/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_relat_1)).
% 1.46/0.57  fof(f559,plain,(
% 1.46/0.57    ( ! [X1] : (~r1_tarski(k9_relat_1(sK2,X1),k9_relat_1(sK3,sK1)) | ~r1_tarski(sK0,X1)) )),
% 1.46/0.57    inference(superposition,[],[f538,f34])).
% 1.46/0.57  fof(f34,plain,(
% 1.46/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f16])).
% 1.46/0.57  fof(f16,plain,(
% 1.46/0.57    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.46/0.57    inference(ennf_transformation,[],[f4])).
% 1.46/0.57  fof(f4,axiom,(
% 1.46/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.46/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.46/0.57  fof(f538,plain,(
% 1.46/0.57    ( ! [X1] : (~r1_tarski(k9_relat_1(sK2,k2_xboole_0(sK0,X1)),k9_relat_1(sK3,sK1))) )),
% 1.46/0.57    inference(subsumption_resolution,[],[f524,f26])).
% 1.46/0.57  fof(f524,plain,(
% 1.46/0.57    ( ! [X1] : (~r1_tarski(k9_relat_1(sK2,k2_xboole_0(sK0,X1)),k9_relat_1(sK3,sK1)) | ~v1_relat_1(sK2)) )),
% 1.46/0.57    inference(resolution,[],[f188,f170])).
% 1.46/0.57  fof(f170,plain,(
% 1.46/0.57    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,k2_xboole_0(X1,X2))) | ~v1_relat_1(X0)) )),
% 1.46/0.57    inference(superposition,[],[f31,f38])).
% 1.46/0.57  fof(f38,plain,(
% 1.46/0.57    ( ! [X2,X0,X1] : (k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f17])).
% 1.46/0.57  fof(f17,plain,(
% 1.46/0.57    ! [X0,X1,X2] : (k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.46/0.57    inference(ennf_transformation,[],[f8])).
% 1.46/0.57  fof(f8,axiom,(
% 1.46/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))),
% 1.46/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t153_relat_1)).
% 1.46/0.57  fof(f31,plain,(
% 1.46/0.57    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.46/0.57    inference(cnf_transformation,[],[f7])).
% 1.46/0.57  fof(f7,axiom,(
% 1.46/0.57    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.46/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.46/0.57  fof(f188,plain,(
% 1.46/0.57    ( ! [X11] : (~r1_tarski(k9_relat_1(sK2,sK0),X11) | ~r1_tarski(X11,k9_relat_1(sK3,sK1))) )),
% 1.46/0.57    inference(resolution,[],[f57,f30])).
% 1.46/0.57  fof(f30,plain,(
% 1.46/0.57    ~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1))),
% 1.46/0.57    inference(cnf_transformation,[],[f23])).
% 1.46/0.57  fof(f57,plain,(
% 1.46/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.46/0.57    inference(superposition,[],[f41,f34])).
% 1.46/0.57  fof(f41,plain,(
% 1.46/0.57    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f20])).
% 1.46/0.57  fof(f20,plain,(
% 1.46/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.46/0.57    inference(ennf_transformation,[],[f3])).
% 1.46/0.57  fof(f3,axiom,(
% 1.46/0.57    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.46/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.46/0.57  % SZS output end Proof for theBenchmark
% 1.46/0.57  % (14959)------------------------------
% 1.46/0.57  % (14959)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.57  % (14959)Termination reason: Refutation
% 1.46/0.57  
% 1.46/0.57  % (14959)Memory used [KB]: 6396
% 1.46/0.57  % (14959)Time elapsed: 0.129 s
% 1.46/0.57  % (14959)------------------------------
% 1.46/0.57  % (14959)------------------------------
% 1.46/0.57  % (14966)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.46/0.58  % (14954)Success in time 0.209 s
%------------------------------------------------------------------------------
