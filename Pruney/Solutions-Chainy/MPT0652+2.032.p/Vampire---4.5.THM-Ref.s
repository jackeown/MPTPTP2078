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
% DateTime   : Thu Dec  3 12:52:57 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 187 expanded)
%              Number of leaves         :   10 (  35 expanded)
%              Depth                    :   20
%              Number of atoms          :  171 ( 682 expanded)
%              Number of equality atoms :   73 ( 249 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f454,plain,(
    $false ),
    inference(subsumption_resolution,[],[f453,f57])).

fof(f57,plain,(
    v1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f50,f26])).

fof(f26,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
            & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

fof(f50,plain,
    ( ~ v1_funct_1(sK0)
    | v1_relat_1(k2_funct_1(sK0)) ),
    inference(resolution,[],[f25,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f25,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f453,plain,(
    ~ v1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f452,f56])).

fof(f56,plain,(
    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f55,f27])).

fof(f27,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f55,plain,
    ( ~ v2_funct_1(sK0)
    | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f45,f26])).

fof(f45,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v2_funct_1(sK0)
    | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    inference(resolution,[],[f25,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f452,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f449,f54])).

fof(f54,plain,(
    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f53,f27])).

fof(f53,plain,
    ( ~ v2_funct_1(sK0)
    | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f44,f26])).

fof(f44,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v2_funct_1(sK0)
    | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    inference(resolution,[],[f25,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f449,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))
    | k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0)) ),
    inference(superposition,[],[f262,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_relat_1)).

fof(f262,plain,(
    ! [X0] :
      ( k2_relat_1(sK0) != k1_relat_1(k8_relat_1(X0,k2_funct_1(sK0)))
      | k1_relat_1(sK0) != X0 ) ),
    inference(forward_demodulation,[],[f261,f29])).

fof(f29,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f261,plain,(
    ! [X0] :
      ( k2_relat_1(sK0) != k1_relat_1(k8_relat_1(X0,k2_funct_1(sK0)))
      | k1_relat_1(k6_relat_1(X0)) != k1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f255,f39])).

fof(f39,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f255,plain,(
    ! [X0] :
      ( k2_relat_1(sK0) != k1_relat_1(k8_relat_1(X0,k2_funct_1(sK0)))
      | ~ v1_relat_1(k6_relat_1(X0))
      | k1_relat_1(k6_relat_1(X0)) != k1_relat_1(sK0) ) ),
    inference(superposition,[],[f138,f76])).

fof(f76,plain,(
    ! [X6] : k8_relat_1(X6,k2_funct_1(sK0)) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(X6)) ),
    inference(resolution,[],[f57,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f138,plain,(
    ! [X0] :
      ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0))
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) != k1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f137,f57])).

fof(f137,plain,(
    ! [X0] :
      ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k2_funct_1(sK0))
      | k1_relat_1(X0) != k1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f135,f25])).

fof(f135,plain,(
    ! [X0] :
      ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK0)
      | ~ v1_relat_1(k2_funct_1(sK0))
      | k1_relat_1(X0) != k1_relat_1(sK0) ) ),
    inference(superposition,[],[f69,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
              | k1_relat_1(X0) != k1_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
              | k1_relat_1(X0) != k1_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k1_relat_1(X0) = k1_relat_1(X1)
               => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t198_relat_1)).

fof(f69,plain,(
    k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(subsumption_resolution,[],[f68,f46])).

fof(f46,plain,(
    k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) ),
    inference(resolution,[],[f25,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f68,plain,
    ( k2_relat_1(sK0) != k9_relat_1(sK0,k1_relat_1(sK0))
    | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(forward_demodulation,[],[f67,f56])).

fof(f67,plain,
    ( k2_relat_1(sK0) != k9_relat_1(sK0,k2_relat_1(k2_funct_1(sK0)))
    | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(subsumption_resolution,[],[f66,f25])).

fof(f66,plain,
    ( k2_relat_1(sK0) != k9_relat_1(sK0,k2_relat_1(k2_funct_1(sK0)))
    | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f65,f57])).

fof(f65,plain,
    ( k2_relat_1(sK0) != k9_relat_1(sK0,k2_relat_1(k2_funct_1(sK0)))
    | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f24,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(f24,plain,
    ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:07:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.43  % (22899)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.19/0.44  % (22907)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.19/0.45  % (22915)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.19/0.46  % (22915)Refutation found. Thanks to Tanya!
% 0.19/0.46  % SZS status Theorem for theBenchmark
% 0.19/0.46  % (22894)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.19/0.48  % SZS output start Proof for theBenchmark
% 0.19/0.48  fof(f454,plain,(
% 0.19/0.48    $false),
% 0.19/0.48    inference(subsumption_resolution,[],[f453,f57])).
% 0.19/0.48  fof(f57,plain,(
% 0.19/0.48    v1_relat_1(k2_funct_1(sK0))),
% 0.19/0.48    inference(subsumption_resolution,[],[f50,f26])).
% 0.19/0.48  fof(f26,plain,(
% 0.19/0.48    v1_funct_1(sK0)),
% 0.19/0.48    inference(cnf_transformation,[],[f13])).
% 0.19/0.48  fof(f13,plain,(
% 0.19/0.48    ? [X0] : ((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.19/0.48    inference(flattening,[],[f12])).
% 0.19/0.48  fof(f12,plain,(
% 0.19/0.48    ? [X0] : (((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f11])).
% 0.19/0.48  fof(f11,negated_conjecture,(
% 0.19/0.48    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 0.19/0.48    inference(negated_conjecture,[],[f10])).
% 0.19/0.48  fof(f10,conjecture,(
% 0.19/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).
% 0.19/0.48  fof(f50,plain,(
% 0.19/0.48    ~v1_funct_1(sK0) | v1_relat_1(k2_funct_1(sK0))),
% 0.19/0.48    inference(resolution,[],[f25,f36])).
% 0.19/0.48  fof(f36,plain,(
% 0.19/0.48    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 0.19/0.48    inference(cnf_transformation,[],[f22])).
% 0.19/0.48  fof(f22,plain,(
% 0.19/0.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.48    inference(flattening,[],[f21])).
% 0.19/0.48  fof(f21,plain,(
% 0.19/0.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f7])).
% 0.19/0.48  fof(f7,axiom,(
% 0.19/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.19/0.48  fof(f25,plain,(
% 0.19/0.48    v1_relat_1(sK0)),
% 0.19/0.48    inference(cnf_transformation,[],[f13])).
% 0.19/0.48  fof(f453,plain,(
% 0.19/0.48    ~v1_relat_1(k2_funct_1(sK0))),
% 0.19/0.48    inference(subsumption_resolution,[],[f452,f56])).
% 0.19/0.48  fof(f56,plain,(
% 0.19/0.48    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 0.19/0.48    inference(subsumption_resolution,[],[f55,f27])).
% 0.19/0.48  fof(f27,plain,(
% 0.19/0.48    v2_funct_1(sK0)),
% 0.19/0.48    inference(cnf_transformation,[],[f13])).
% 0.19/0.48  fof(f55,plain,(
% 0.19/0.48    ~v2_funct_1(sK0) | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 0.19/0.48    inference(subsumption_resolution,[],[f45,f26])).
% 0.19/0.48  fof(f45,plain,(
% 0.19/0.48    ~v1_funct_1(sK0) | ~v2_funct_1(sK0) | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 0.19/0.48    inference(resolution,[],[f25,f32])).
% 0.19/0.48  fof(f32,plain,(
% 0.19/0.48    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.19/0.48    inference(cnf_transformation,[],[f17])).
% 0.19/0.48  fof(f17,plain,(
% 0.19/0.48    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.48    inference(flattening,[],[f16])).
% 0.19/0.48  fof(f16,plain,(
% 0.19/0.48    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f9])).
% 0.19/0.48  fof(f9,axiom,(
% 0.19/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.19/0.48  fof(f452,plain,(
% 0.19/0.48    k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(k2_funct_1(sK0))),
% 0.19/0.48    inference(subsumption_resolution,[],[f449,f54])).
% 0.19/0.48  fof(f54,plain,(
% 0.19/0.48    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.19/0.48    inference(subsumption_resolution,[],[f53,f27])).
% 0.19/0.48  fof(f53,plain,(
% 0.19/0.48    ~v2_funct_1(sK0) | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.19/0.48    inference(subsumption_resolution,[],[f44,f26])).
% 0.19/0.48  fof(f44,plain,(
% 0.19/0.48    ~v1_funct_1(sK0) | ~v2_funct_1(sK0) | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.19/0.48    inference(resolution,[],[f25,f31])).
% 0.19/0.48  fof(f31,plain,(
% 0.19/0.48    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.19/0.48    inference(cnf_transformation,[],[f17])).
% 0.19/0.48  fof(f449,plain,(
% 0.19/0.48    k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0)) | k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(k2_funct_1(sK0))),
% 0.19/0.48    inference(superposition,[],[f262,f38])).
% 0.19/0.48  fof(f38,plain,(
% 0.19/0.48    ( ! [X0] : (~v1_relat_1(X0) | k8_relat_1(k2_relat_1(X0),X0) = X0) )),
% 0.19/0.48    inference(cnf_transformation,[],[f23])).
% 0.19/0.48  fof(f23,plain,(
% 0.19/0.48    ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0))),
% 0.19/0.48    inference(ennf_transformation,[],[f2])).
% 0.19/0.48  fof(f2,axiom,(
% 0.19/0.48    ! [X0] : (v1_relat_1(X0) => k8_relat_1(k2_relat_1(X0),X0) = X0)),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_relat_1)).
% 0.19/0.48  fof(f262,plain,(
% 0.19/0.48    ( ! [X0] : (k2_relat_1(sK0) != k1_relat_1(k8_relat_1(X0,k2_funct_1(sK0))) | k1_relat_1(sK0) != X0) )),
% 0.19/0.48    inference(forward_demodulation,[],[f261,f29])).
% 0.19/0.48  fof(f29,plain,(
% 0.19/0.48    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.19/0.48    inference(cnf_transformation,[],[f6])).
% 0.19/0.48  fof(f6,axiom,(
% 0.19/0.48    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.19/0.48  fof(f261,plain,(
% 0.19/0.48    ( ! [X0] : (k2_relat_1(sK0) != k1_relat_1(k8_relat_1(X0,k2_funct_1(sK0))) | k1_relat_1(k6_relat_1(X0)) != k1_relat_1(sK0)) )),
% 0.19/0.48    inference(subsumption_resolution,[],[f255,f39])).
% 0.19/0.48  fof(f39,plain,(
% 0.19/0.48    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.19/0.48    inference(cnf_transformation,[],[f8])).
% 0.19/0.48  fof(f8,axiom,(
% 0.19/0.48    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.19/0.48  fof(f255,plain,(
% 0.19/0.48    ( ! [X0] : (k2_relat_1(sK0) != k1_relat_1(k8_relat_1(X0,k2_funct_1(sK0))) | ~v1_relat_1(k6_relat_1(X0)) | k1_relat_1(k6_relat_1(X0)) != k1_relat_1(sK0)) )),
% 0.19/0.48    inference(superposition,[],[f138,f76])).
% 0.19/0.48  fof(f76,plain,(
% 0.19/0.48    ( ! [X6] : (k8_relat_1(X6,k2_funct_1(sK0)) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(X6))) )),
% 0.19/0.48    inference(resolution,[],[f57,f34])).
% 0.19/0.48  fof(f34,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 0.19/0.48    inference(cnf_transformation,[],[f19])).
% 0.19/0.48  fof(f19,plain,(
% 0.19/0.48    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.19/0.48    inference(ennf_transformation,[],[f1])).
% 0.19/0.48  fof(f1,axiom,(
% 0.19/0.48    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 0.19/0.48  fof(f138,plain,(
% 0.19/0.48    ( ! [X0] : (k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) | ~v1_relat_1(X0) | k1_relat_1(X0) != k1_relat_1(sK0)) )),
% 0.19/0.48    inference(subsumption_resolution,[],[f137,f57])).
% 0.19/0.48  fof(f137,plain,(
% 0.19/0.48    ( ! [X0] : (k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k2_funct_1(sK0)) | k1_relat_1(X0) != k1_relat_1(sK0)) )),
% 0.19/0.48    inference(subsumption_resolution,[],[f135,f25])).
% 0.19/0.48  fof(f135,plain,(
% 0.19/0.48    ( ! [X0] : (k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) | ~v1_relat_1(X0) | ~v1_relat_1(sK0) | ~v1_relat_1(k2_funct_1(sK0)) | k1_relat_1(X0) != k1_relat_1(sK0)) )),
% 0.19/0.48    inference(superposition,[],[f69,f28])).
% 0.19/0.48  fof(f28,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | k1_relat_1(X0) != k1_relat_1(X1) | k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))) )),
% 0.19/0.48    inference(cnf_transformation,[],[f15])).
% 0.19/0.48  fof(f15,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (! [X2] : (k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.48    inference(flattening,[],[f14])).
% 0.19/0.48  fof(f14,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (! [X2] : ((k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.48    inference(ennf_transformation,[],[f5])).
% 0.19/0.48  fof(f5,axiom,(
% 0.19/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k1_relat_1(X0) = k1_relat_1(X1) => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))))))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t198_relat_1)).
% 0.19/0.48  fof(f69,plain,(
% 0.19/0.48    k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.19/0.48    inference(subsumption_resolution,[],[f68,f46])).
% 0.19/0.48  fof(f46,plain,(
% 0.19/0.48    k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))),
% 0.19/0.48    inference(resolution,[],[f25,f33])).
% 0.19/0.48  fof(f33,plain,(
% 0.19/0.48    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0))) )),
% 0.19/0.48    inference(cnf_transformation,[],[f18])).
% 0.19/0.48  fof(f18,plain,(
% 0.19/0.48    ! [X0] : (k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.19/0.48    inference(ennf_transformation,[],[f3])).
% 0.19/0.48  fof(f3,axiom,(
% 0.19/0.48    ! [X0] : (v1_relat_1(X0) => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.19/0.48  fof(f68,plain,(
% 0.19/0.48    k2_relat_1(sK0) != k9_relat_1(sK0,k1_relat_1(sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.19/0.48    inference(forward_demodulation,[],[f67,f56])).
% 0.19/0.48  fof(f67,plain,(
% 0.19/0.48    k2_relat_1(sK0) != k9_relat_1(sK0,k2_relat_1(k2_funct_1(sK0))) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.19/0.48    inference(subsumption_resolution,[],[f66,f25])).
% 0.19/0.48  fof(f66,plain,(
% 0.19/0.48    k2_relat_1(sK0) != k9_relat_1(sK0,k2_relat_1(k2_funct_1(sK0))) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | ~v1_relat_1(sK0)),
% 0.19/0.48    inference(subsumption_resolution,[],[f65,f57])).
% 0.19/0.48  fof(f65,plain,(
% 0.19/0.48    k2_relat_1(sK0) != k9_relat_1(sK0,k2_relat_1(k2_funct_1(sK0))) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0)),
% 0.19/0.48    inference(superposition,[],[f24,f35])).
% 0.19/0.48  fof(f35,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))) )),
% 0.19/0.48    inference(cnf_transformation,[],[f20])).
% 0.19/0.48  fof(f20,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.48    inference(ennf_transformation,[],[f4])).
% 0.19/0.48  fof(f4,axiom,(
% 0.19/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).
% 0.19/0.48  fof(f24,plain,(
% 0.19/0.48    k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.19/0.48    inference(cnf_transformation,[],[f13])).
% 0.19/0.48  % SZS output end Proof for theBenchmark
% 0.19/0.48  % (22915)------------------------------
% 0.19/0.48  % (22915)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (22915)Termination reason: Refutation
% 0.19/0.48  
% 0.19/0.48  % (22915)Memory used [KB]: 1918
% 0.19/0.48  % (22915)Time elapsed: 0.087 s
% 0.19/0.48  % (22915)------------------------------
% 0.19/0.48  % (22915)------------------------------
% 0.19/0.48  % (22895)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.19/0.48  % (22893)Success in time 0.131 s
%------------------------------------------------------------------------------
