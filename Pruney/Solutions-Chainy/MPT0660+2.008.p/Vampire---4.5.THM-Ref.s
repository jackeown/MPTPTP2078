%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   41 (  68 expanded)
%              Number of leaves         :    6 (  19 expanded)
%              Depth                    :   22
%              Number of atoms          :  140 ( 182 expanded)
%              Number of equality atoms :   65 (  84 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f41,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f40])).

fof(f40,plain,(
    k6_relat_1(sK0) != k6_relat_1(sK0) ),
    inference(superposition,[],[f14,f39])).

fof(f39,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(trivial_inequality_removal,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( k6_relat_1(X0) != k6_relat_1(X0)
      | k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f37,f23])).

fof(f23,plain,(
    ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) ),
    inference(forward_demodulation,[],[f22,f18])).

fof(f18,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f22,plain,(
    ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0)))) ),
    inference(resolution,[],[f19,f15])).

fof(f15,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) != k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))
      | k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f36,f15])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X1))
      | k6_relat_1(X0) != k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(resolution,[],[f35,f16])).

fof(f16,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(X1)
      | k6_relat_1(X0) != k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(forward_demodulation,[],[f34,f17])).

fof(f17,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k5_relat_1(k6_relat_1(X0),X1) != k6_relat_1(k1_relat_1(k6_relat_1(X0))) ) ),
    inference(subsumption_resolution,[],[f33,f15])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k5_relat_1(k6_relat_1(X0),X1) != k6_relat_1(k1_relat_1(k6_relat_1(X0)))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f32,f16])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k5_relat_1(k6_relat_1(X0),X1) != k6_relat_1(k1_relat_1(k6_relat_1(X0)))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(resolution,[],[f31,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_1)).

fof(f31,plain,(
    ! [X0] :
      ( ~ v2_funct_1(k6_relat_1(X0))
      | k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f30,f17])).

fof(f30,plain,(
    ! [X0] :
      ( k1_relat_1(k6_relat_1(X0)) != X0
      | ~ v2_funct_1(k6_relat_1(X0))
      | k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f29,f18])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v2_funct_1(k6_relat_1(X0))
      | k1_relat_1(k6_relat_1(X0)) != k2_relat_1(k6_relat_1(X0))
      | k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ) ),
    inference(trivial_inequality_removal,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k6_relat_1(X0) != k6_relat_1(X0)
      | ~ v2_funct_1(k6_relat_1(X0))
      | k1_relat_1(k6_relat_1(X0)) != k2_relat_1(k6_relat_1(X0))
      | k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f27,f18])).

fof(f27,plain,(
    ! [X0] :
      ( k6_relat_1(X0) != k6_relat_1(k2_relat_1(k6_relat_1(X0)))
      | ~ v2_funct_1(k6_relat_1(X0))
      | k1_relat_1(k6_relat_1(X0)) != k2_relat_1(k6_relat_1(X0))
      | k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f26,f15])).

fof(f26,plain,(
    ! [X0] :
      ( k6_relat_1(X0) != k6_relat_1(k2_relat_1(k6_relat_1(X0)))
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v2_funct_1(k6_relat_1(X0))
      | k1_relat_1(k6_relat_1(X0)) != k2_relat_1(k6_relat_1(X0))
      | k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f25,f16])).

fof(f25,plain,(
    ! [X0] :
      ( k6_relat_1(X0) != k6_relat_1(k2_relat_1(k6_relat_1(X0)))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v2_funct_1(k6_relat_1(X0))
      | k1_relat_1(k6_relat_1(X0)) != k2_relat_1(k6_relat_1(X0))
      | k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k6_relat_1(X0) != k6_relat_1(k2_relat_1(k6_relat_1(X0)))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v2_funct_1(k6_relat_1(X0))
      | k1_relat_1(k6_relat_1(X0)) != k2_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0))
      | k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f21,f23])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

fof(f14,plain,(
    k6_relat_1(sK0) != k2_funct_1(k6_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] : k6_relat_1(X0) != k2_funct_1(k6_relat_1(X0)) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:30:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.42  % (23524)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.14/0.42  % (23525)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.14/0.42  % (23527)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.22/0.43  % (23518)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.22/0.43  % (23518)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f41,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(trivial_inequality_removal,[],[f40])).
% 0.22/0.43  fof(f40,plain,(
% 0.22/0.43    k6_relat_1(sK0) != k6_relat_1(sK0)),
% 0.22/0.43    inference(superposition,[],[f14,f39])).
% 0.22/0.43  fof(f39,plain,(
% 0.22/0.43    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 0.22/0.43    inference(trivial_inequality_removal,[],[f38])).
% 0.22/0.43  fof(f38,plain,(
% 0.22/0.43    ( ! [X0] : (k6_relat_1(X0) != k6_relat_1(X0) | k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 0.22/0.43    inference(superposition,[],[f37,f23])).
% 0.22/0.43  fof(f23,plain,(
% 0.22/0.43    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))) )),
% 0.22/0.43    inference(forward_demodulation,[],[f22,f18])).
% 0.22/0.43  fof(f18,plain,(
% 0.22/0.43    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0))))) )),
% 0.22/0.43    inference(resolution,[],[f19,f15])).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f9])).
% 0.22/0.43  fof(f9,plain,(
% 0.22/0.43    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 0.22/0.43  fof(f37,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k6_relat_1(X0) != k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) | k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 0.22/0.43    inference(subsumption_resolution,[],[f36,f15])).
% 0.22/0.43  fof(f36,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X1)) | k6_relat_1(X0) != k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) )),
% 0.22/0.43    inference(resolution,[],[f35,f16])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f3])).
% 0.22/0.43  fof(f35,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~v1_funct_1(X1) | k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) | ~v1_relat_1(X1) | k6_relat_1(X0) != k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.22/0.43    inference(forward_demodulation,[],[f34,f17])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f1])).
% 0.22/0.43  fof(f34,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k5_relat_1(k6_relat_1(X0),X1) != k6_relat_1(k1_relat_1(k6_relat_1(X0)))) )),
% 0.22/0.43    inference(subsumption_resolution,[],[f33,f15])).
% 0.22/0.43  fof(f33,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k5_relat_1(k6_relat_1(X0),X1) != k6_relat_1(k1_relat_1(k6_relat_1(X0))) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.43    inference(subsumption_resolution,[],[f32,f16])).
% 0.22/0.43  fof(f32,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k5_relat_1(k6_relat_1(X0),X1) != k6_relat_1(k1_relat_1(k6_relat_1(X0))) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.43    inference(resolution,[],[f31,f20])).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    ( ! [X0,X1] : (v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f11])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ! [X0] : (v2_funct_1(X0) | ! [X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.43    inference(flattening,[],[f10])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    ! [X0] : ((v2_funct_1(X0) | ! [X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.43    inference(ennf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,axiom,(
% 0.22/0.43    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_1)).
% 0.22/0.43  fof(f31,plain,(
% 0.22/0.43    ( ! [X0] : (~v2_funct_1(k6_relat_1(X0)) | k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 0.22/0.43    inference(subsumption_resolution,[],[f30,f17])).
% 0.22/0.43  fof(f30,plain,(
% 0.22/0.43    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) != X0 | ~v2_funct_1(k6_relat_1(X0)) | k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 0.22/0.43    inference(forward_demodulation,[],[f29,f18])).
% 0.22/0.43  fof(f29,plain,(
% 0.22/0.43    ( ! [X0] : (~v2_funct_1(k6_relat_1(X0)) | k1_relat_1(k6_relat_1(X0)) != k2_relat_1(k6_relat_1(X0)) | k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 0.22/0.43    inference(trivial_inequality_removal,[],[f28])).
% 0.22/0.43  fof(f28,plain,(
% 0.22/0.43    ( ! [X0] : (k6_relat_1(X0) != k6_relat_1(X0) | ~v2_funct_1(k6_relat_1(X0)) | k1_relat_1(k6_relat_1(X0)) != k2_relat_1(k6_relat_1(X0)) | k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 0.22/0.43    inference(forward_demodulation,[],[f27,f18])).
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    ( ! [X0] : (k6_relat_1(X0) != k6_relat_1(k2_relat_1(k6_relat_1(X0))) | ~v2_funct_1(k6_relat_1(X0)) | k1_relat_1(k6_relat_1(X0)) != k2_relat_1(k6_relat_1(X0)) | k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 0.22/0.43    inference(subsumption_resolution,[],[f26,f15])).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    ( ! [X0] : (k6_relat_1(X0) != k6_relat_1(k2_relat_1(k6_relat_1(X0))) | ~v1_relat_1(k6_relat_1(X0)) | ~v2_funct_1(k6_relat_1(X0)) | k1_relat_1(k6_relat_1(X0)) != k2_relat_1(k6_relat_1(X0)) | k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 0.22/0.43    inference(subsumption_resolution,[],[f25,f16])).
% 0.22/0.43  fof(f25,plain,(
% 0.22/0.43    ( ! [X0] : (k6_relat_1(X0) != k6_relat_1(k2_relat_1(k6_relat_1(X0))) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0)) | ~v2_funct_1(k6_relat_1(X0)) | k1_relat_1(k6_relat_1(X0)) != k2_relat_1(k6_relat_1(X0)) | k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 0.22/0.43    inference(duplicate_literal_removal,[],[f24])).
% 0.22/0.43  fof(f24,plain,(
% 0.22/0.43    ( ! [X0] : (k6_relat_1(X0) != k6_relat_1(k2_relat_1(k6_relat_1(X0))) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_funct_1(k6_relat_1(X0)) | ~v2_funct_1(k6_relat_1(X0)) | k1_relat_1(k6_relat_1(X0)) != k2_relat_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0)) | k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 0.22/0.43    inference(superposition,[],[f21,f23])).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X0) | k2_funct_1(X0) = X1) )),
% 0.22/0.43    inference(cnf_transformation,[],[f13])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.43    inference(flattening,[],[f12])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.43    inference(ennf_transformation,[],[f5])).
% 0.22/0.43  fof(f5,axiom,(
% 0.22/0.43    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    k6_relat_1(sK0) != k2_funct_1(k6_relat_1(sK0))),
% 0.22/0.43    inference(cnf_transformation,[],[f8])).
% 0.22/0.43  fof(f8,plain,(
% 0.22/0.43    ? [X0] : k6_relat_1(X0) != k2_funct_1(k6_relat_1(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f7])).
% 0.22/0.43  fof(f7,negated_conjecture,(
% 0.22/0.43    ~! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 0.22/0.43    inference(negated_conjecture,[],[f6])).
% 0.22/0.43  fof(f6,conjecture,(
% 0.22/0.43    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (23518)------------------------------
% 0.22/0.43  % (23518)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (23518)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (23518)Memory used [KB]: 10490
% 0.22/0.43  % (23518)Time elapsed: 0.006 s
% 0.22/0.43  % (23518)------------------------------
% 0.22/0.43  % (23518)------------------------------
% 0.22/0.44  % (23517)Success in time 0.073 s
%------------------------------------------------------------------------------
