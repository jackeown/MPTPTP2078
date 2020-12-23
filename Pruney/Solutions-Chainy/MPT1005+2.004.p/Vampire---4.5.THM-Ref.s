%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   48 (  64 expanded)
%              Number of leaves         :   12 (  18 expanded)
%              Depth                    :   12
%              Number of atoms          :   94 ( 132 expanded)
%              Number of equality atoms :   44 (  57 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (25916)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f79,plain,(
    $false ),
    inference(subsumption_resolution,[],[f71,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k7_relset_1(X0,X1,k1_xboole_0,X2) ),
    inference(forward_demodulation,[],[f75,f35])).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

% (25913)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f75,plain,(
    ! [X2,X0,X1] : k7_relset_1(X0,X1,k1_xboole_0,X2) = k9_relat_1(k1_xboole_0,X2) ),
    inference(resolution,[],[f48,f54])).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f36,f34])).

fof(f34,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f36,plain,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f71,plain,(
    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f32,f67])).

fof(f67,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f64,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f64,plain,(
    v1_xboole_0(sK2) ),
    inference(resolution,[],[f63,f56])).

fof(f56,plain,(
    m1_subset_1(sK2,k1_tarski(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f55,f33])).

fof(f33,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f55,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f31,f53])).

fof(f53,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f25])).

% (25891)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) )
   => ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
       => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f19,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_1(X2) )
       => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_2)).

fof(f63,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_tarski(k1_xboole_0))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f62,f33])).

fof(f62,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f39,f60])).

fof(f60,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f41,f58])).

fof(f58,plain,(
    ! [X0] : k1_xboole_0 = sK3(X0) ),
    inference(resolution,[],[f38,f41])).

fof(f41,plain,(
    ! [X0] : v1_xboole_0(sK3(X0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v1_xboole_0(sK3(X0))
      & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f32,plain,(
    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:17:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (25906)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (25900)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (25892)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (25895)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (25898)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (25898)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  % (25916)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f71,f78])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_xboole_0 = k7_relset_1(X0,X1,k1_xboole_0,X2)) )),
% 0.21/0.52    inference(forward_demodulation,[],[f75,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,axiom,(
% 0.21/0.52    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
% 0.21/0.52  % (25913)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k7_relset_1(X0,X1,k1_xboole_0,X2) = k9_relat_1(k1_xboole_0,X2)) )),
% 0.21/0.52    inference(resolution,[],[f48,f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f36,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)),
% 0.21/0.52    inference(backward_demodulation,[],[f32,f67])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    k1_xboole_0 = sK2),
% 0.21/0.52    inference(resolution,[],[f64,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    v1_xboole_0(sK2)),
% 0.21/0.52    inference(resolution,[],[f63,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_tarski(k1_xboole_0))),
% 0.21/0.52    inference(forward_demodulation,[],[f55,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.52    inference(backward_demodulation,[],[f31,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.52    inference(flattening,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.52    inference(nnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f25])).
% 0.21/0.52  % (25891)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) => (k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))))),
% 0.21/0.52    inference(ennf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f18])).
% 0.21/0.52  fof(f18,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.21/0.52    inference(negated_conjecture,[],[f17])).
% 0.21/0.52  fof(f17,conjecture,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_2)).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_tarski(k1_xboole_0)) | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(forward_demodulation,[],[f62,f33])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(resolution,[],[f39,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    v1_xboole_0(k1_xboole_0)),
% 0.21/0.52    inference(backward_demodulation,[],[f41,f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = sK3(X0)) )),
% 0.21/0.52    inference(resolution,[],[f38,f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X0] : (v1_xboole_0(sK3(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(sK3(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (v1_xboole_0(sK3(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(X0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f13,axiom,(
% 0.21/0.52    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,axiom,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (25898)------------------------------
% 0.21/0.52  % (25898)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (25898)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (25898)Memory used [KB]: 6268
% 0.21/0.52  % (25898)Time elapsed: 0.114 s
% 0.21/0.52  % (25898)------------------------------
% 0.21/0.52  % (25898)------------------------------
% 0.21/0.53  % (25905)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (25890)Success in time 0.169 s
%------------------------------------------------------------------------------
