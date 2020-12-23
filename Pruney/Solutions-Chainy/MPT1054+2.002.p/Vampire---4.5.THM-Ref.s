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
% DateTime   : Thu Dec  3 13:07:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.16s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 133 expanded)
%              Number of leaves         :   22 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :  208 ( 273 expanded)
%              Number of equality atoms :   70 (  99 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f149,plain,(
    $false ),
    inference(subsumption_resolution,[],[f147,f123])).

fof(f123,plain,(
    sK1 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f119,f103])).

fof(f103,plain,(
    sK1 = k9_relat_1(k6_relat_1(sK1),sK0) ),
    inference(forward_demodulation,[],[f102,f56])).

fof(f56,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f102,plain,(
    k9_relat_1(k6_relat_1(sK1),sK0) = k2_relat_1(k6_relat_1(sK1)) ),
    inference(superposition,[],[f89,f100])).

fof(f100,plain,(
    k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK1),sK0) ),
    inference(resolution,[],[f97,f83])).

fof(f83,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f81,f74])).

fof(f74,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f81,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f79,f45])).

fof(f45,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f79,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f64,f43])).

fof(f43,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f37])).

fof(f37,plain,
    ( ? [X0,X1] :
        ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f97,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,X4)
      | k6_relat_1(X3) = k7_relat_1(k6_relat_1(X3),X4) ) ),
    inference(resolution,[],[f95,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(k6_relat_1(X0),X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) ) ),
    inference(resolution,[],[f66,f49])).

fof(f49,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

% (24966)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f95,plain,(
    ! [X0,X1] :
      ( v4_relat_1(k6_relat_1(X0),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f91,f54])).

fof(f54,plain,(
    ! [X0] : v4_relat_1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v5_relat_1(k6_relat_1(X0),X0)
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_relat_1(k6_relat_1(X0),X1)
      | v4_relat_1(k6_relat_1(X0),X2)
      | ~ r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f63,f49])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v4_relat_1(X2,X0)
      | v4_relat_1(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v4_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t217_relat_1)).

fof(f89,plain,(
    ! [X0,X1] : k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(resolution,[],[f62,f49])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f119,plain,(
    ! [X0,X1] : k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(forward_demodulation,[],[f118,f110])).

% (24984)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f110,plain,(
    ! [X0,X1] : k10_relat_1(k6_relat_1(X0),X1) = k3_xboole_0(X1,X0) ),
    inference(forward_demodulation,[],[f109,f55])).

fof(f55,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f109,plain,(
    ! [X0,X1] : k10_relat_1(k6_relat_1(X0),X1) = k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0))) ),
    inference(forward_demodulation,[],[f108,f61])).

fof(f61,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f108,plain,(
    ! [X0,X1] : k10_relat_1(k6_relat_1(X0),X1) = k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(forward_demodulation,[],[f107,f55])).

fof(f107,plain,(
    ! [X0,X1] : k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1))) ),
    inference(resolution,[],[f106,f49])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k10_relat_1(k6_relat_1(X1),k1_relat_1(X0)) ) ),
    inference(resolution,[],[f57,f49])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f118,plain,(
    ! [X0,X1] : k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(forward_demodulation,[],[f117,f47])).

fof(f47,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).

fof(f117,plain,(
    ! [X0,X1] : k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k2_funct_1(k6_relat_1(X0)),X1) ),
    inference(subsumption_resolution,[],[f116,f49])).

fof(f116,plain,(
    ! [X0,X1] :
      ( k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k2_funct_1(k6_relat_1(X0)),X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f115,f50])).

fof(f50,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f115,plain,(
    ! [X0,X1] :
      ( k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k2_funct_1(k6_relat_1(X0)),X1)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(resolution,[],[f65,f52])).

fof(f52,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

% (24975)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f32,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

fof(f147,plain,(
    sK1 != k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f146,f87])).

fof(f87,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    inference(superposition,[],[f77,f60])).

fof(f60,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f77,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f60,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f146,plain,(
    sK1 != k3_xboole_0(sK1,sK0) ),
    inference(superposition,[],[f75,f145])).

fof(f145,plain,(
    ! [X0,X1] : k3_xboole_0(X1,X0) = k8_relset_1(X0,X0,k6_relat_1(X0),X1) ),
    inference(forward_demodulation,[],[f144,f110])).

fof(f144,plain,(
    ! [X0,X1] : k10_relat_1(k6_relat_1(X0),X1) = k8_relset_1(X0,X0,k6_relat_1(X0),X1) ),
    inference(resolution,[],[f72,f48])).

fof(f48,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f75,plain,(
    sK1 != k8_relset_1(sK0,sK0,k6_relat_1(sK0),sK1) ),
    inference(backward_demodulation,[],[f44,f46])).

fof(f46,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f44,plain,(
    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:01:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (24980)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.50  % (24972)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.50  % (24963)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.50  % (24969)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (24969)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (24985)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.16/0.51  % (24972)Refutation not found, incomplete strategy% (24972)------------------------------
% 1.16/0.51  % (24972)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.16/0.51  % (24964)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.16/0.51  % (24965)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.16/0.51  % (24972)Termination reason: Refutation not found, incomplete strategy
% 1.16/0.51  
% 1.16/0.51  % (24972)Memory used [KB]: 10618
% 1.16/0.51  % (24972)Time elapsed: 0.104 s
% 1.16/0.51  % (24972)------------------------------
% 1.16/0.51  % (24972)------------------------------
% 1.16/0.51  % (24964)Refutation not found, incomplete strategy% (24964)------------------------------
% 1.16/0.51  % (24964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.16/0.51  % (24964)Termination reason: Refutation not found, incomplete strategy
% 1.16/0.51  
% 1.16/0.51  % (24964)Memory used [KB]: 10746
% 1.16/0.51  % (24964)Time elapsed: 0.109 s
% 1.16/0.51  % (24964)------------------------------
% 1.16/0.51  % (24964)------------------------------
% 1.16/0.51  % (24977)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.16/0.51  % SZS output start Proof for theBenchmark
% 1.16/0.51  fof(f149,plain,(
% 1.16/0.51    $false),
% 1.16/0.51    inference(subsumption_resolution,[],[f147,f123])).
% 1.16/0.51  fof(f123,plain,(
% 1.16/0.51    sK1 = k3_xboole_0(sK0,sK1)),
% 1.16/0.51    inference(superposition,[],[f119,f103])).
% 1.16/0.51  fof(f103,plain,(
% 1.16/0.51    sK1 = k9_relat_1(k6_relat_1(sK1),sK0)),
% 1.16/0.51    inference(forward_demodulation,[],[f102,f56])).
% 1.16/0.51  fof(f56,plain,(
% 1.16/0.51    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.16/0.51    inference(cnf_transformation,[],[f12])).
% 1.16/0.51  fof(f12,axiom,(
% 1.16/0.51    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.16/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.16/0.51  fof(f102,plain,(
% 1.16/0.51    k9_relat_1(k6_relat_1(sK1),sK0) = k2_relat_1(k6_relat_1(sK1))),
% 1.16/0.51    inference(superposition,[],[f89,f100])).
% 1.16/0.51  fof(f100,plain,(
% 1.16/0.51    k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK1),sK0)),
% 1.16/0.51    inference(resolution,[],[f97,f83])).
% 1.16/0.51  fof(f83,plain,(
% 1.16/0.51    r1_tarski(sK1,sK0)),
% 1.16/0.51    inference(resolution,[],[f81,f74])).
% 1.16/0.51  fof(f74,plain,(
% 1.16/0.51    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 1.16/0.51    inference(equality_resolution,[],[f67])).
% 1.16/0.51  fof(f67,plain,(
% 1.16/0.51    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.16/0.51    inference(cnf_transformation,[],[f42])).
% 1.16/0.51  fof(f42,plain,(
% 1.16/0.51    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.16/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f41])).
% 1.16/0.51  fof(f41,plain,(
% 1.16/0.51    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 1.16/0.51    introduced(choice_axiom,[])).
% 1.16/0.51  fof(f40,plain,(
% 1.16/0.51    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.16/0.51    inference(rectify,[],[f39])).
% 1.16/0.51  fof(f39,plain,(
% 1.16/0.51    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.16/0.51    inference(nnf_transformation,[],[f4])).
% 1.16/0.51  fof(f4,axiom,(
% 1.16/0.51    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.16/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.16/0.51  fof(f81,plain,(
% 1.16/0.51    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.16/0.51    inference(subsumption_resolution,[],[f79,f45])).
% 1.16/0.51  fof(f45,plain,(
% 1.16/0.51    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.16/0.51    inference(cnf_transformation,[],[f5])).
% 1.16/0.51  fof(f5,axiom,(
% 1.16/0.51    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.16/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.16/0.51  fof(f79,plain,(
% 1.16/0.51    v1_xboole_0(k1_zfmisc_1(sK0)) | r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.16/0.51    inference(resolution,[],[f64,f43])).
% 1.16/0.51  fof(f43,plain,(
% 1.16/0.51    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.16/0.51    inference(cnf_transformation,[],[f38])).
% 1.16/0.51  fof(f38,plain,(
% 1.16/0.51    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.16/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f37])).
% 1.16/0.51  fof(f37,plain,(
% 1.16/0.51    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.16/0.51    introduced(choice_axiom,[])).
% 1.16/0.51  fof(f25,plain,(
% 1.16/0.51    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.16/0.51    inference(ennf_transformation,[],[f23])).
% 1.16/0.51  fof(f23,negated_conjecture,(
% 1.16/0.51    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 1.16/0.51    inference(negated_conjecture,[],[f22])).
% 1.16/0.51  fof(f22,conjecture,(
% 1.16/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 1.16/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).
% 1.16/0.51  fof(f64,plain,(
% 1.16/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.16/0.51    inference(cnf_transformation,[],[f31])).
% 1.16/0.51  fof(f31,plain,(
% 1.16/0.51    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.16/0.51    inference(flattening,[],[f30])).
% 1.16/0.51  fof(f30,plain,(
% 1.16/0.51    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.16/0.51    inference(ennf_transformation,[],[f7])).
% 1.16/0.51  fof(f7,axiom,(
% 1.16/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.16/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.16/0.51  fof(f97,plain,(
% 1.16/0.51    ( ! [X4,X3] : (~r1_tarski(X3,X4) | k6_relat_1(X3) = k7_relat_1(k6_relat_1(X3),X4)) )),
% 1.16/0.51    inference(resolution,[],[f95,f90])).
% 1.16/0.51  fof(f90,plain,(
% 1.16/0.51    ( ! [X0,X1] : (~v4_relat_1(k6_relat_1(X0),X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 1.16/0.51    inference(resolution,[],[f66,f49])).
% 1.16/0.51  fof(f49,plain,(
% 1.16/0.51    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.16/0.51    inference(cnf_transformation,[],[f14])).
% 1.16/0.51  fof(f14,axiom,(
% 1.16/0.51    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.16/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.16/0.52  % (24966)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.16/0.52  fof(f66,plain,(
% 1.16/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 1.16/0.52    inference(cnf_transformation,[],[f35])).
% 1.16/0.52  fof(f35,plain,(
% 1.16/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.16/0.52    inference(flattening,[],[f34])).
% 1.16/0.52  fof(f34,plain,(
% 1.16/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.16/0.52    inference(ennf_transformation,[],[f10])).
% 1.16/0.52  fof(f10,axiom,(
% 1.16/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.16/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 1.16/0.52  fof(f95,plain,(
% 1.16/0.52    ( ! [X0,X1] : (v4_relat_1(k6_relat_1(X0),X1) | ~r1_tarski(X0,X1)) )),
% 1.16/0.52    inference(resolution,[],[f91,f54])).
% 1.16/0.52  fof(f54,plain,(
% 1.16/0.52    ( ! [X0] : (v4_relat_1(k6_relat_1(X0),X0)) )),
% 1.16/0.52    inference(cnf_transformation,[],[f24])).
% 1.16/0.52  fof(f24,plain,(
% 1.16/0.52    ! [X0] : (v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 1.16/0.52    inference(pure_predicate_removal,[],[f13])).
% 1.16/0.52  fof(f13,axiom,(
% 1.16/0.52    ! [X0] : (v5_relat_1(k6_relat_1(X0),X0) & v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 1.16/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).
% 1.16/0.52  fof(f91,plain,(
% 1.16/0.52    ( ! [X2,X0,X1] : (~v4_relat_1(k6_relat_1(X0),X1) | v4_relat_1(k6_relat_1(X0),X2) | ~r1_tarski(X1,X2)) )),
% 1.16/0.52    inference(resolution,[],[f63,f49])).
% 1.16/0.52  fof(f63,plain,(
% 1.16/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v4_relat_1(X2,X0) | v4_relat_1(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.16/0.52    inference(cnf_transformation,[],[f29])).
% 1.16/0.52  fof(f29,plain,(
% 1.16/0.52    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~r1_tarski(X0,X1))),
% 1.16/0.52    inference(flattening,[],[f28])).
% 1.16/0.52  fof(f28,plain,(
% 1.16/0.52    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | (~v4_relat_1(X2,X0) | ~v1_relat_1(X2))) | ~r1_tarski(X0,X1))),
% 1.16/0.52    inference(ennf_transformation,[],[f11])).
% 1.16/0.52  fof(f11,axiom,(
% 1.16/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v4_relat_1(X2,X0) & v1_relat_1(X2)) => v4_relat_1(X2,X1)))),
% 1.16/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t217_relat_1)).
% 1.16/0.52  fof(f89,plain,(
% 1.16/0.52    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1)) )),
% 1.16/0.52    inference(resolution,[],[f62,f49])).
% 1.16/0.52  fof(f62,plain,(
% 1.16/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.16/0.52    inference(cnf_transformation,[],[f27])).
% 1.16/0.52  fof(f27,plain,(
% 1.16/0.52    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.16/0.52    inference(ennf_transformation,[],[f8])).
% 1.16/0.52  fof(f8,axiom,(
% 1.16/0.52    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.16/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 1.16/0.52  fof(f119,plain,(
% 1.16/0.52    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X0),X1)) )),
% 1.16/0.52    inference(forward_demodulation,[],[f118,f110])).
% 1.16/0.52  % (24984)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.16/0.52  fof(f110,plain,(
% 1.16/0.52    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k3_xboole_0(X1,X0)) )),
% 1.16/0.52    inference(forward_demodulation,[],[f109,f55])).
% 1.16/0.52  fof(f55,plain,(
% 1.16/0.52    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.16/0.52    inference(cnf_transformation,[],[f12])).
% 1.16/0.52  fof(f109,plain,(
% 1.16/0.52    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0)))) )),
% 1.16/0.52    inference(forward_demodulation,[],[f108,f61])).
% 1.16/0.52  fof(f61,plain,(
% 1.16/0.52    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 1.16/0.52    inference(cnf_transformation,[],[f17])).
% 1.16/0.52  fof(f17,axiom,(
% 1.16/0.52    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.16/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 1.16/0.52  fof(f108,plain,(
% 1.16/0.52    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) )),
% 1.16/0.52    inference(forward_demodulation,[],[f107,f55])).
% 1.16/0.52  fof(f107,plain,(
% 1.16/0.52    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1)))) )),
% 1.16/0.52    inference(resolution,[],[f106,f49])).
% 1.16/0.52  fof(f106,plain,(
% 1.16/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k10_relat_1(k6_relat_1(X1),k1_relat_1(X0))) )),
% 1.16/0.52    inference(resolution,[],[f57,f49])).
% 1.16/0.52  fof(f57,plain,(
% 1.16/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 1.16/0.52    inference(cnf_transformation,[],[f26])).
% 1.16/0.52  fof(f26,plain,(
% 1.16/0.52    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.16/0.52    inference(ennf_transformation,[],[f9])).
% 1.16/0.52  fof(f9,axiom,(
% 1.16/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.16/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 1.16/0.52  fof(f118,plain,(
% 1.16/0.52    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k6_relat_1(X0),X1)) )),
% 1.16/0.52    inference(forward_demodulation,[],[f117,f47])).
% 1.16/0.52  fof(f47,plain,(
% 1.16/0.52    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 1.16/0.52    inference(cnf_transformation,[],[f18])).
% 1.16/0.52  fof(f18,axiom,(
% 1.16/0.52    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 1.16/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).
% 1.16/0.52  fof(f117,plain,(
% 1.16/0.52    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k2_funct_1(k6_relat_1(X0)),X1)) )),
% 1.16/0.52    inference(subsumption_resolution,[],[f116,f49])).
% 1.16/0.52  fof(f116,plain,(
% 1.16/0.52    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k2_funct_1(k6_relat_1(X0)),X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.16/0.52    inference(subsumption_resolution,[],[f115,f50])).
% 1.16/0.52  fof(f50,plain,(
% 1.16/0.52    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.16/0.52    inference(cnf_transformation,[],[f14])).
% 1.16/0.52  fof(f115,plain,(
% 1.16/0.52    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k2_funct_1(k6_relat_1(X0)),X1) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.16/0.52    inference(resolution,[],[f65,f52])).
% 1.16/0.52  fof(f52,plain,(
% 1.16/0.52    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.16/0.52    inference(cnf_transformation,[],[f15])).
% 1.16/0.52  fof(f15,axiom,(
% 1.16/0.52    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.16/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.16/0.52  fof(f65,plain,(
% 1.16/0.52    ( ! [X0,X1] : (~v2_funct_1(X1) | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.16/0.52    inference(cnf_transformation,[],[f33])).
% 1.16/0.52  fof(f33,plain,(
% 1.16/0.52    ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.16/0.52    inference(flattening,[],[f32])).
% 1.16/0.52  % (24975)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.16/0.52  fof(f32,plain,(
% 1.16/0.52    ! [X0,X1] : ((k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.16/0.52    inference(ennf_transformation,[],[f16])).
% 1.16/0.52  fof(f16,axiom,(
% 1.16/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 1.16/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).
% 1.16/0.52  fof(f147,plain,(
% 1.16/0.52    sK1 != k3_xboole_0(sK0,sK1)),
% 1.16/0.52    inference(superposition,[],[f146,f87])).
% 1.16/0.52  fof(f87,plain,(
% 1.16/0.52    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) )),
% 1.16/0.52    inference(superposition,[],[f77,f60])).
% 1.16/0.52  fof(f60,plain,(
% 1.16/0.52    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.16/0.52    inference(cnf_transformation,[],[f6])).
% 1.16/0.52  fof(f6,axiom,(
% 1.16/0.52    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.16/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.16/0.52  fof(f77,plain,(
% 1.16/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 1.16/0.52    inference(superposition,[],[f60,f58])).
% 1.16/0.52  fof(f58,plain,(
% 1.16/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.16/0.52    inference(cnf_transformation,[],[f1])).
% 1.16/0.52  fof(f1,axiom,(
% 1.16/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.16/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.16/0.52  fof(f146,plain,(
% 1.16/0.52    sK1 != k3_xboole_0(sK1,sK0)),
% 1.16/0.52    inference(superposition,[],[f75,f145])).
% 1.16/0.52  fof(f145,plain,(
% 1.16/0.52    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k8_relset_1(X0,X0,k6_relat_1(X0),X1)) )),
% 1.16/0.52    inference(forward_demodulation,[],[f144,f110])).
% 1.16/0.52  fof(f144,plain,(
% 1.16/0.52    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k8_relset_1(X0,X0,k6_relat_1(X0),X1)) )),
% 1.16/0.52    inference(resolution,[],[f72,f48])).
% 1.16/0.52  fof(f48,plain,(
% 1.16/0.52    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.16/0.52    inference(cnf_transformation,[],[f20])).
% 1.16/0.52  fof(f20,axiom,(
% 1.16/0.52    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.16/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 1.16/0.52  fof(f72,plain,(
% 1.16/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 1.16/0.52    inference(cnf_transformation,[],[f36])).
% 1.16/0.52  fof(f36,plain,(
% 1.16/0.52    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.16/0.52    inference(ennf_transformation,[],[f19])).
% 1.16/0.52  fof(f19,axiom,(
% 1.16/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 1.16/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 1.16/0.52  fof(f75,plain,(
% 1.16/0.52    sK1 != k8_relset_1(sK0,sK0,k6_relat_1(sK0),sK1)),
% 1.16/0.52    inference(backward_demodulation,[],[f44,f46])).
% 1.16/0.52  fof(f46,plain,(
% 1.16/0.52    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.16/0.52    inference(cnf_transformation,[],[f21])).
% 1.16/0.52  fof(f21,axiom,(
% 1.16/0.52    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.16/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.16/0.52  fof(f44,plain,(
% 1.16/0.52    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)),
% 1.16/0.52    inference(cnf_transformation,[],[f38])).
% 1.16/0.52  % SZS output end Proof for theBenchmark
% 1.16/0.52  % (24969)------------------------------
% 1.16/0.52  % (24969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.16/0.52  % (24969)Termination reason: Refutation
% 1.16/0.52  
% 1.16/0.52  % (24969)Memory used [KB]: 6268
% 1.16/0.52  % (24969)Time elapsed: 0.102 s
% 1.16/0.52  % (24969)------------------------------
% 1.16/0.52  % (24969)------------------------------
% 1.16/0.52  % (24970)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.16/0.52  % (24984)Refutation not found, incomplete strategy% (24984)------------------------------
% 1.16/0.52  % (24984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.16/0.52  % (24984)Termination reason: Refutation not found, incomplete strategy
% 1.16/0.52  
% 1.16/0.52  % (24984)Memory used [KB]: 10746
% 1.16/0.52  % (24984)Time elapsed: 0.078 s
% 1.16/0.52  % (24984)------------------------------
% 1.16/0.52  % (24984)------------------------------
% 1.16/0.52  % (24970)Refutation not found, incomplete strategy% (24970)------------------------------
% 1.16/0.52  % (24970)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.16/0.52  % (24970)Termination reason: Refutation not found, incomplete strategy
% 1.16/0.52  
% 1.16/0.52  % (24970)Memory used [KB]: 10618
% 1.16/0.52  % (24970)Time elapsed: 0.111 s
% 1.16/0.52  % (24970)------------------------------
% 1.16/0.52  % (24970)------------------------------
% 1.16/0.52  % (24962)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.16/0.52  % (24989)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.16/0.52  % (24976)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.16/0.52  % (24990)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.16/0.52  % (24986)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.16/0.52  % (24991)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.16/0.53  % (24987)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.16/0.53  % (24967)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.16/0.53  % (24978)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.16/0.53  % (24981)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.16/0.53  % (24966)Refutation not found, incomplete strategy% (24966)------------------------------
% 1.16/0.53  % (24966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.16/0.53  % (24966)Termination reason: Refutation not found, incomplete strategy
% 1.16/0.53  
% 1.16/0.53  % (24966)Memory used [KB]: 6140
% 1.16/0.53  % (24966)Time elapsed: 0.121 s
% 1.16/0.53  % (24966)------------------------------
% 1.16/0.53  % (24966)------------------------------
% 1.16/0.53  % (24977)Refutation not found, incomplete strategy% (24977)------------------------------
% 1.16/0.53  % (24977)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.53  % (24979)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.31/0.53  % (24961)Success in time 0.163 s
%------------------------------------------------------------------------------
