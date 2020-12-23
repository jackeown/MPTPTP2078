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
% DateTime   : Thu Dec  3 12:54:10 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 199 expanded)
%              Number of leaves         :    8 (  48 expanded)
%              Depth                    :   14
%              Number of atoms          :  158 ( 750 expanded)
%              Number of equality atoms :   33 ( 180 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f168,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f167])).

fof(f167,plain,(
    k10_relat_1(sK1,sK0) != k10_relat_1(sK1,sK0) ),
    inference(superposition,[],[f54,f113])).

fof(f113,plain,(
    ! [X0] : k9_relat_1(k4_relat_1(sK1),X0) = k10_relat_1(sK1,X0) ),
    inference(forward_demodulation,[],[f112,f57])).

fof(f57,plain,(
    sK1 = k2_funct_1(k4_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f56,f52])).

fof(f52,plain,(
    k2_funct_1(sK1) = k4_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f51,f28])).

fof(f28,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k10_relat_1(sK1,sK0) != k9_relat_1(k2_funct_1(sK1),sK0)
    & v2_funct_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( k10_relat_1(X1,X0) != k9_relat_1(k2_funct_1(X1),X0)
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k10_relat_1(sK1,sK0) != k9_relat_1(k2_funct_1(sK1),sK0)
      & v2_funct_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,X0) != k9_relat_1(k2_funct_1(X1),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,X0) != k9_relat_1(k2_funct_1(X1),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

fof(f51,plain,
    ( k2_funct_1(sK1) = k4_relat_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f44,f29])).

fof(f29,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f44,plain,
    ( k2_funct_1(sK1) = k4_relat_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f27,f35])).

fof(f35,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f56,plain,(
    sK1 = k2_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f55,f28])).

fof(f55,plain,
    ( sK1 = k2_funct_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f45,f29])).

fof(f45,plain,
    ( sK1 = k2_funct_1(k2_funct_1(sK1))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f27,f36])).

fof(f36,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(f112,plain,(
    ! [X0] : k9_relat_1(k4_relat_1(sK1),X0) = k10_relat_1(k2_funct_1(k4_relat_1(sK1)),X0) ),
    inference(subsumption_resolution,[],[f111,f48])).

fof(f48,plain,(
    v1_funct_1(k4_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f47,f28])).

fof(f47,plain,
    ( v1_funct_1(k4_relat_1(sK1))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f42,f29])).

fof(f42,plain,
    ( v1_funct_1(k4_relat_1(sK1))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f27,f33])).

fof(f33,plain,(
    ! [X0] :
      ( v1_funct_1(k4_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_funct_1(k4_relat_1(X0))
        & v1_relat_1(k4_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v1_funct_1(k4_relat_1(X0))
        & v1_relat_1(k4_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k4_relat_1(X0))
        & v1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_funct_1)).

fof(f111,plain,(
    ! [X0] :
      ( k9_relat_1(k4_relat_1(sK1),X0) = k10_relat_1(k2_funct_1(k4_relat_1(sK1)),X0)
      | ~ v1_funct_1(k4_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f97,f53])).

fof(f53,plain,(
    v2_funct_1(k4_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f50,f52])).

fof(f50,plain,(
    v2_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f49,f28])).

fof(f49,plain,
    ( v2_funct_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f43,f29])).

fof(f43,plain,
    ( v2_funct_1(k2_funct_1(sK1))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f27,f34])).

fof(f34,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => v2_funct_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).

fof(f97,plain,(
    ! [X0] :
      ( k9_relat_1(k4_relat_1(sK1),X0) = k10_relat_1(k2_funct_1(k4_relat_1(sK1)),X0)
      | ~ v2_funct_1(k4_relat_1(sK1))
      | ~ v1_funct_1(k4_relat_1(sK1)) ) ),
    inference(resolution,[],[f40,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

fof(f40,plain,(
    v1_relat_1(k4_relat_1(sK1)) ),
    inference(resolution,[],[f27,f31])).

fof(f31,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f54,plain,(
    k10_relat_1(sK1,sK0) != k9_relat_1(k4_relat_1(sK1),sK0) ),
    inference(backward_demodulation,[],[f30,f52])).

fof(f30,plain,(
    k10_relat_1(sK1,sK0) != k9_relat_1(k2_funct_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:19:20 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (8932)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.51  % (8924)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (8932)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (8916)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f168,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f167])).
% 0.22/0.52  fof(f167,plain,(
% 0.22/0.52    k10_relat_1(sK1,sK0) != k10_relat_1(sK1,sK0)),
% 0.22/0.52    inference(superposition,[],[f54,f113])).
% 0.22/0.52  fof(f113,plain,(
% 0.22/0.52    ( ! [X0] : (k9_relat_1(k4_relat_1(sK1),X0) = k10_relat_1(sK1,X0)) )),
% 0.22/0.52    inference(forward_demodulation,[],[f112,f57])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    sK1 = k2_funct_1(k4_relat_1(sK1))),
% 0.22/0.52    inference(forward_demodulation,[],[f56,f52])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    k2_funct_1(sK1) = k4_relat_1(sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f51,f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    v1_funct_1(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    k10_relat_1(sK1,sK0) != k9_relat_1(k2_funct_1(sK1),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ? [X0,X1] : (k10_relat_1(X1,X0) != k9_relat_1(k2_funct_1(X1),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k10_relat_1(sK1,sK0) != k9_relat_1(k2_funct_1(sK1),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ? [X0,X1] : (k10_relat_1(X1,X0) != k9_relat_1(k2_funct_1(X1),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.52    inference(flattening,[],[f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ? [X0,X1] : ((k10_relat_1(X1,X0) != k9_relat_1(k2_funct_1(X1),X0) & v2_funct_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 0.22/0.52    inference(negated_conjecture,[],[f9])).
% 0.22/0.52  fof(f9,conjecture,(
% 0.22/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    k2_funct_1(sK1) = k4_relat_1(sK1) | ~v1_funct_1(sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f44,f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    v2_funct_1(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    k2_funct_1(sK1) = k4_relat_1(sK1) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 0.22/0.52    inference(resolution,[],[f27,f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    v1_relat_1(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    sK1 = k2_funct_1(k2_funct_1(sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f55,f28])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    sK1 = k2_funct_1(k2_funct_1(sK1)) | ~v1_funct_1(sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f45,f29])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    sK1 = k2_funct_1(k2_funct_1(sK1)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 0.22/0.52    inference(resolution,[],[f27,f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
% 0.22/0.52  fof(f112,plain,(
% 0.22/0.52    ( ! [X0] : (k9_relat_1(k4_relat_1(sK1),X0) = k10_relat_1(k2_funct_1(k4_relat_1(sK1)),X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f111,f48])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    v1_funct_1(k4_relat_1(sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f47,f28])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    v1_funct_1(k4_relat_1(sK1)) | ~v1_funct_1(sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f42,f29])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    v1_funct_1(k4_relat_1(sK1)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 0.22/0.52    inference(resolution,[],[f27,f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ( ! [X0] : (v1_funct_1(k4_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(k4_relat_1(X0)) & v1_relat_1(k4_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(k4_relat_1(X0)) & v1_relat_1(k4_relat_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k4_relat_1(X0)) & v1_relat_1(k4_relat_1(X0))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_funct_1)).
% 0.22/0.52  fof(f111,plain,(
% 0.22/0.52    ( ! [X0] : (k9_relat_1(k4_relat_1(sK1),X0) = k10_relat_1(k2_funct_1(k4_relat_1(sK1)),X0) | ~v1_funct_1(k4_relat_1(sK1))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f97,f53])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    v2_funct_1(k4_relat_1(sK1))),
% 0.22/0.52    inference(backward_demodulation,[],[f50,f52])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    v2_funct_1(k2_funct_1(sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f49,f28])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    v2_funct_1(k2_funct_1(sK1)) | ~v1_funct_1(sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f43,f29])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    v2_funct_1(k2_funct_1(sK1)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 0.22/0.52    inference(resolution,[],[f27,f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => v2_funct_1(k2_funct_1(X0))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).
% 0.22/0.52  fof(f97,plain,(
% 0.22/0.52    ( ! [X0] : (k9_relat_1(k4_relat_1(sK1),X0) = k10_relat_1(k2_funct_1(k4_relat_1(sK1)),X0) | ~v2_funct_1(k4_relat_1(sK1)) | ~v1_funct_1(k4_relat_1(sK1))) )),
% 0.22/0.52    inference(resolution,[],[f40,f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(flattening,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    v1_relat_1(k4_relat_1(sK1))),
% 0.22/0.52    inference(resolution,[],[f27,f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    k10_relat_1(sK1,sK0) != k9_relat_1(k4_relat_1(sK1),sK0)),
% 0.22/0.52    inference(backward_demodulation,[],[f30,f52])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    k10_relat_1(sK1,sK0) != k9_relat_1(k2_funct_1(sK1),sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (8932)------------------------------
% 0.22/0.52  % (8932)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (8932)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (8932)Memory used [KB]: 1663
% 0.22/0.52  % (8932)Time elapsed: 0.061 s
% 0.22/0.52  % (8932)------------------------------
% 0.22/0.52  % (8932)------------------------------
% 0.22/0.53  % (8908)Success in time 0.159 s
%------------------------------------------------------------------------------
