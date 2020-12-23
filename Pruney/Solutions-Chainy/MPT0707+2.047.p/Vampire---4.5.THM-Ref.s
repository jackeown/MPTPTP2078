%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:32 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   44 (  56 expanded)
%              Number of leaves         :   11 (  17 expanded)
%              Depth                    :   11
%              Number of atoms          :   89 ( 112 expanded)
%              Number of equality atoms :   36 (  45 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f58,plain,(
    $false ),
    inference(global_subsumption,[],[f36,f57])).

fof(f57,plain,(
    sK1 != k3_xboole_0(sK1,sK0) ),
    inference(superposition,[],[f21,f56])).

fof(f56,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X0),X1) = k3_xboole_0(X1,X0) ),
    inference(global_subsumption,[],[f23,f26,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = k3_xboole_0(X1,X0)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f54,f48])).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X1,X0) = k10_relat_1(k6_relat_1(X0),X1) ),
    inference(forward_demodulation,[],[f47,f27])).

fof(f27,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f47,plain,(
    ! [X0,X1] : k10_relat_1(k6_relat_1(X0),X1) = k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0))) ),
    inference(forward_demodulation,[],[f46,f30])).

fof(f30,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f46,plain,(
    ! [X0,X1] : k10_relat_1(k6_relat_1(X0),X1) = k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(resolution,[],[f41,f23])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k1_relat_1(k5_relat_1(X1,k6_relat_1(X0))) ) ),
    inference(forward_demodulation,[],[f38,f27])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X1,k6_relat_1(X0))) = k10_relat_1(X1,k1_relat_1(k6_relat_1(X0))) ) ),
    inference(resolution,[],[f29,f23])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = k10_relat_1(k6_relat_1(X0),X1)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f53,f22])).

fof(f22,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k2_funct_1(k6_relat_1(X0)),X1)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(resolution,[],[f32,f24])).

fof(f24,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

fof(f26,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f23,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f21,plain,(
    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(k6_relat_1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

fof(f36,plain,(
    sK1 = k3_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f35,f20])).

fof(f20,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(resolution,[],[f31,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:34:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.41  % (32625)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.14/0.41  % (32632)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.14/0.41  % (32625)Refutation found. Thanks to Tanya!
% 0.14/0.41  % SZS status Theorem for theBenchmark
% 0.14/0.41  % SZS output start Proof for theBenchmark
% 0.14/0.41  fof(f58,plain,(
% 0.14/0.41    $false),
% 0.14/0.41    inference(global_subsumption,[],[f36,f57])).
% 0.14/0.41  fof(f57,plain,(
% 0.14/0.41    sK1 != k3_xboole_0(sK1,sK0)),
% 0.14/0.41    inference(superposition,[],[f21,f56])).
% 0.14/0.41  fof(f56,plain,(
% 0.14/0.41    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = k3_xboole_0(X1,X0)) )),
% 0.14/0.41    inference(global_subsumption,[],[f23,f26,f55])).
% 0.14/0.41  fof(f55,plain,(
% 0.14/0.41    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = k3_xboole_0(X1,X0) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.14/0.41    inference(forward_demodulation,[],[f54,f48])).
% 0.14/0.41  fof(f48,plain,(
% 0.14/0.41    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k10_relat_1(k6_relat_1(X0),X1)) )),
% 0.14/0.41    inference(forward_demodulation,[],[f47,f27])).
% 0.14/0.41  fof(f27,plain,(
% 0.14/0.41    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.14/0.41    inference(cnf_transformation,[],[f4])).
% 0.14/0.41  fof(f4,axiom,(
% 0.14/0.41    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.14/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.14/0.42  fof(f47,plain,(
% 0.14/0.42    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0)))) )),
% 0.14/0.42    inference(forward_demodulation,[],[f46,f30])).
% 0.14/0.42  fof(f30,plain,(
% 0.14/0.42    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.14/0.42    inference(cnf_transformation,[],[f8])).
% 0.14/0.42  fof(f8,axiom,(
% 0.14/0.42    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 0.14/0.42  fof(f46,plain,(
% 0.14/0.42    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) )),
% 0.14/0.42    inference(resolution,[],[f41,f23])).
% 0.14/0.42  fof(f41,plain,(
% 0.14/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k1_relat_1(k5_relat_1(X1,k6_relat_1(X0)))) )),
% 0.14/0.42    inference(forward_demodulation,[],[f38,f27])).
% 0.14/0.42  fof(f38,plain,(
% 0.14/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X1,k6_relat_1(X0))) = k10_relat_1(X1,k1_relat_1(k6_relat_1(X0)))) )),
% 0.14/0.42    inference(resolution,[],[f29,f23])).
% 0.14/0.42  fof(f29,plain,(
% 0.14/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 0.14/0.42    inference(cnf_transformation,[],[f13])).
% 0.14/0.42  fof(f13,plain,(
% 0.14/0.42    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.14/0.42    inference(ennf_transformation,[],[f3])).
% 0.14/0.42  fof(f3,axiom,(
% 0.14/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 0.14/0.42  fof(f54,plain,(
% 0.14/0.42    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = k10_relat_1(k6_relat_1(X0),X1) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.14/0.42    inference(forward_demodulation,[],[f53,f22])).
% 0.14/0.42  fof(f22,plain,(
% 0.14/0.42    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 0.14/0.42    inference(cnf_transformation,[],[f9])).
% 0.14/0.42  fof(f9,axiom,(
% 0.14/0.42    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).
% 0.14/0.42  fof(f53,plain,(
% 0.14/0.42    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k2_funct_1(k6_relat_1(X0)),X1) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.14/0.42    inference(resolution,[],[f32,f24])).
% 0.14/0.42  fof(f24,plain,(
% 0.14/0.42    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.14/0.42    inference(cnf_transformation,[],[f6])).
% 0.14/0.42  fof(f6,axiom,(
% 0.14/0.42    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.14/0.42  fof(f32,plain,(
% 0.14/0.42    ( ! [X0,X1] : (~v2_funct_1(X1) | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.14/0.42    inference(cnf_transformation,[],[f16])).
% 0.14/0.42  fof(f16,plain,(
% 0.14/0.42    ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.14/0.42    inference(flattening,[],[f15])).
% 0.14/0.42  fof(f15,plain,(
% 0.14/0.42    ! [X0,X1] : ((k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.14/0.42    inference(ennf_transformation,[],[f7])).
% 0.14/0.42  fof(f7,axiom,(
% 0.14/0.42    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).
% 0.14/0.42  fof(f26,plain,(
% 0.14/0.42    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.14/0.42    inference(cnf_transformation,[],[f5])).
% 0.14/0.42  fof(f5,axiom,(
% 0.14/0.42    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.14/0.42  fof(f23,plain,(
% 0.14/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.14/0.42    inference(cnf_transformation,[],[f6])).
% 0.14/0.42  fof(f21,plain,(
% 0.14/0.42    sK1 != k9_relat_1(k6_relat_1(sK0),sK1)),
% 0.14/0.42    inference(cnf_transformation,[],[f18])).
% 0.14/0.42  fof(f18,plain,(
% 0.14/0.42    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.14/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f17])).
% 0.14/0.42  fof(f17,plain,(
% 0.14/0.42    ? [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK1 != k9_relat_1(k6_relat_1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.14/0.42    introduced(choice_axiom,[])).
% 0.14/0.42  fof(f12,plain,(
% 0.14/0.42    ? [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.14/0.42    inference(ennf_transformation,[],[f11])).
% 0.14/0.42  fof(f11,negated_conjecture,(
% 0.14/0.42    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.14/0.42    inference(negated_conjecture,[],[f10])).
% 0.14/0.42  fof(f10,conjecture,(
% 0.14/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).
% 0.14/0.42  fof(f36,plain,(
% 0.14/0.42    sK1 = k3_xboole_0(sK1,sK0)),
% 0.14/0.42    inference(resolution,[],[f35,f20])).
% 0.14/0.42  fof(f20,plain,(
% 0.14/0.42    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.14/0.42    inference(cnf_transformation,[],[f18])).
% 0.14/0.42  fof(f35,plain,(
% 0.14/0.42    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | k3_xboole_0(X0,X1) = X0) )),
% 0.14/0.42    inference(resolution,[],[f31,f33])).
% 0.14/0.42  fof(f33,plain,(
% 0.14/0.42    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.14/0.42    inference(cnf_transformation,[],[f19])).
% 0.14/0.42  fof(f19,plain,(
% 0.14/0.42    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.14/0.42    inference(nnf_transformation,[],[f2])).
% 0.14/0.42  fof(f2,axiom,(
% 0.14/0.42    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.14/0.42  fof(f31,plain,(
% 0.14/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.14/0.42    inference(cnf_transformation,[],[f14])).
% 0.14/0.42  fof(f14,plain,(
% 0.14/0.42    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.14/0.42    inference(ennf_transformation,[],[f1])).
% 0.14/0.42  fof(f1,axiom,(
% 0.14/0.42    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.14/0.42  % SZS output end Proof for theBenchmark
% 0.14/0.42  % (32625)------------------------------
% 0.14/0.42  % (32625)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.14/0.42  % (32625)Termination reason: Refutation
% 0.14/0.42  
% 0.14/0.42  % (32625)Memory used [KB]: 6140
% 0.21/0.42  % (32625)Time elapsed: 0.006 s
% 0.21/0.42  % (32625)------------------------------
% 0.21/0.42  % (32625)------------------------------
% 0.21/0.42  % (32620)Success in time 0.063 s
%------------------------------------------------------------------------------
