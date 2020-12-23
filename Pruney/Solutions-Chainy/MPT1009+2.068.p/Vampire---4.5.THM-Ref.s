%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:35 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 311 expanded)
%              Number of leaves         :   14 (  72 expanded)
%              Depth                    :   19
%              Number of atoms          :  178 ( 957 expanded)
%              Number of equality atoms :   68 ( 240 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f141,plain,(
    $false ),
    inference(subsumption_resolution,[],[f140,f45])).

% (8949)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f45,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f140,plain,(
    ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(k1_xboole_0,sK0))) ),
    inference(forward_demodulation,[],[f139,f79])).

fof(f79,plain,(
    ! [X1] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f78,f44])).

fof(f44,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f78,plain,(
    ! [X1] : k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X1) ),
    inference(backward_demodulation,[],[f74,f77])).

fof(f77,plain,(
    ! [X1] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X1) ),
    inference(subsumption_resolution,[],[f76,f71])).

fof(f71,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f60,f46])).

fof(f46,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

% (8946)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f76,plain,(
    ! [X1] :
      ( ~ v4_relat_1(k1_xboole_0,X1)
      | k1_xboole_0 = k7_relat_1(k1_xboole_0,X1) ) ),
    inference(resolution,[],[f54,f64])).

fof(f64,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f59,f46])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f31])).

% (8938)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f74,plain,(
    ! [X1] : k9_relat_1(k1_xboole_0,X1) = k2_relat_1(k7_relat_1(k1_xboole_0,X1)) ),
    inference(resolution,[],[f52,f64])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f139,plain,(
    ~ r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_tarski(k1_funct_1(k1_xboole_0,sK0))) ),
    inference(forward_demodulation,[],[f106,f108])).

fof(f108,plain,(
    k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f101,f107])).

fof(f107,plain,(
    k1_xboole_0 = k2_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f105,f66])).

fof(f66,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3)) ),
    inference(resolution,[],[f65,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

fof(f65,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f59,f40])).

fof(f40,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f35])).

fof(f35,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

fof(f105,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k1_xboole_0 = k2_relat_1(sK3) ),
    inference(backward_demodulation,[],[f94,f103])).

fof(f103,plain,(
    ! [X3] : k7_relset_1(k1_tarski(sK0),sK1,sK3,X3) = k9_relat_1(sK3,X3) ),
    inference(resolution,[],[f61,f40])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

% (8939)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f94,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k2_relat_1(sK3))
    | k1_xboole_0 = k2_relat_1(sK3) ),
    inference(superposition,[],[f42,f92])).

fof(f92,plain,
    ( k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_xboole_0 = k2_relat_1(sK3) ),
    inference(resolution,[],[f91,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f91,plain,(
    r1_tarski(k2_relat_1(sK3),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(superposition,[],[f89,f83])).

fof(f83,plain,(
    k2_relat_1(sK3) = k9_relat_1(sK3,k1_tarski(sK0)) ),
    inference(superposition,[],[f73,f82])).

fof(f82,plain,(
    sK3 = k7_relat_1(sK3,k1_tarski(sK0)) ),
    inference(resolution,[],[f75,f72])).

fof(f72,plain,(
    v4_relat_1(sK3,k1_tarski(sK0)) ),
    inference(resolution,[],[f60,f40])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v4_relat_1(sK3,X0)
      | sK3 = k7_relat_1(sK3,X0) ) ),
    inference(resolution,[],[f54,f65])).

fof(f73,plain,(
    ! [X0] : k9_relat_1(sK3,X0) = k2_relat_1(k7_relat_1(sK3,X0)) ),
    inference(resolution,[],[f52,f65])).

fof(f89,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK3,k1_tarski(X0)),k1_tarski(k1_funct_1(sK3,X0))) ),
    inference(forward_demodulation,[],[f88,f73])).

fof(f88,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_tarski(X0))),k1_tarski(k1_funct_1(sK3,X0))) ),
    inference(subsumption_resolution,[],[f87,f65])).

fof(f87,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_tarski(X0))),k1_tarski(k1_funct_1(sK3,X0)))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f53,f39])).

fof(f39,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_funct_1)).

fof(f42,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f101,plain,
    ( k1_xboole_0 != k2_relat_1(sK3)
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f100,f83])).

fof(f100,plain,
    ( k1_xboole_0 != k9_relat_1(sK3,k1_tarski(sK0))
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f99,f65])).

fof(f99,plain,
    ( ~ v1_relat_1(sK3)
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k9_relat_1(sK3,k1_tarski(sK0)) ),
    inference(superposition,[],[f81,f82])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k7_relat_1(sK3,X0))
      | k1_xboole_0 = k7_relat_1(sK3,X0)
      | k1_xboole_0 != k9_relat_1(sK3,X0) ) ),
    inference(superposition,[],[f49,f73])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

% (8942)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% (8962)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f106,plain,(
    ~ r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(backward_demodulation,[],[f42,f103])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:12:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.55  % (8937)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.56  % (8948)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.56  % (8952)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.44/0.56  % (8960)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.44/0.57  % (8944)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.44/0.57  % (8940)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.44/0.58  % (8943)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.44/0.58  % (8948)Refutation not found, incomplete strategy% (8948)------------------------------
% 1.44/0.58  % (8948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.58  % (8948)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.58  
% 1.44/0.58  % (8948)Memory used [KB]: 10746
% 1.44/0.58  % (8948)Time elapsed: 0.153 s
% 1.44/0.58  % (8948)------------------------------
% 1.44/0.58  % (8948)------------------------------
% 1.44/0.58  % (8944)Refutation found. Thanks to Tanya!
% 1.44/0.58  % SZS status Theorem for theBenchmark
% 1.44/0.58  % SZS output start Proof for theBenchmark
% 1.44/0.58  fof(f141,plain,(
% 1.44/0.58    $false),
% 1.44/0.58    inference(subsumption_resolution,[],[f140,f45])).
% 1.44/0.58  % (8949)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.44/0.58  fof(f45,plain,(
% 1.44/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.44/0.58    inference(cnf_transformation,[],[f1])).
% 1.44/0.58  fof(f1,axiom,(
% 1.44/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.44/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.44/0.58  fof(f140,plain,(
% 1.44/0.58    ~r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(k1_xboole_0,sK0)))),
% 1.44/0.58    inference(forward_demodulation,[],[f139,f79])).
% 1.44/0.58  fof(f79,plain,(
% 1.44/0.58    ( ! [X1] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X1)) )),
% 1.44/0.58    inference(forward_demodulation,[],[f78,f44])).
% 1.44/0.58  fof(f44,plain,(
% 1.44/0.58    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.44/0.58    inference(cnf_transformation,[],[f11])).
% 1.44/0.58  fof(f11,axiom,(
% 1.44/0.58    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.44/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.44/0.58  fof(f78,plain,(
% 1.44/0.58    ( ! [X1] : (k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X1)) )),
% 1.44/0.58    inference(backward_demodulation,[],[f74,f77])).
% 1.44/0.58  fof(f77,plain,(
% 1.44/0.58    ( ! [X1] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X1)) )),
% 1.44/0.58    inference(subsumption_resolution,[],[f76,f71])).
% 1.44/0.58  fof(f71,plain,(
% 1.44/0.58    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) )),
% 1.44/0.58    inference(resolution,[],[f60,f46])).
% 1.44/0.58  fof(f46,plain,(
% 1.44/0.58    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.44/0.58    inference(cnf_transformation,[],[f6])).
% 1.44/0.58  fof(f6,axiom,(
% 1.44/0.58    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.44/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.44/0.58  fof(f60,plain,(
% 1.44/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.44/0.58    inference(cnf_transformation,[],[f33])).
% 1.44/0.58  fof(f33,plain,(
% 1.44/0.58    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.58    inference(ennf_transformation,[],[f20])).
% 1.44/0.58  % (8946)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.44/0.58  fof(f20,plain,(
% 1.44/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.44/0.58    inference(pure_predicate_removal,[],[f15])).
% 1.44/0.58  fof(f15,axiom,(
% 1.44/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.44/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.44/0.58  fof(f76,plain,(
% 1.44/0.58    ( ! [X1] : (~v4_relat_1(k1_xboole_0,X1) | k1_xboole_0 = k7_relat_1(k1_xboole_0,X1)) )),
% 1.44/0.58    inference(resolution,[],[f54,f64])).
% 1.44/0.58  fof(f64,plain,(
% 1.44/0.58    v1_relat_1(k1_xboole_0)),
% 1.44/0.58    inference(resolution,[],[f59,f46])).
% 1.44/0.58  fof(f59,plain,(
% 1.44/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.44/0.58    inference(cnf_transformation,[],[f32])).
% 1.44/0.58  fof(f32,plain,(
% 1.44/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.58    inference(ennf_transformation,[],[f14])).
% 1.44/0.58  fof(f14,axiom,(
% 1.44/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.44/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.44/0.58  fof(f54,plain,(
% 1.44/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 1.44/0.58    inference(cnf_transformation,[],[f31])).
% 1.64/0.58  % (8938)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.64/0.58  fof(f31,plain,(
% 1.64/0.58    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.64/0.58    inference(flattening,[],[f30])).
% 1.64/0.58  fof(f30,plain,(
% 1.64/0.58    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.64/0.58    inference(ennf_transformation,[],[f10])).
% 1.64/0.58  fof(f10,axiom,(
% 1.64/0.58    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 1.64/0.58  fof(f74,plain,(
% 1.64/0.58    ( ! [X1] : (k9_relat_1(k1_xboole_0,X1) = k2_relat_1(k7_relat_1(k1_xboole_0,X1))) )),
% 1.64/0.58    inference(resolution,[],[f52,f64])).
% 1.64/0.58  fof(f52,plain,(
% 1.64/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))) )),
% 1.64/0.58    inference(cnf_transformation,[],[f27])).
% 1.64/0.58  fof(f27,plain,(
% 1.64/0.58    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.64/0.58    inference(ennf_transformation,[],[f9])).
% 1.64/0.58  fof(f9,axiom,(
% 1.64/0.58    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.64/0.58  fof(f139,plain,(
% 1.64/0.58    ~r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_tarski(k1_funct_1(k1_xboole_0,sK0)))),
% 1.64/0.58    inference(forward_demodulation,[],[f106,f108])).
% 1.64/0.58  fof(f108,plain,(
% 1.64/0.58    k1_xboole_0 = sK3),
% 1.64/0.58    inference(subsumption_resolution,[],[f101,f107])).
% 1.64/0.58  fof(f107,plain,(
% 1.64/0.58    k1_xboole_0 = k2_relat_1(sK3)),
% 1.64/0.58    inference(subsumption_resolution,[],[f105,f66])).
% 1.64/0.58  fof(f66,plain,(
% 1.64/0.58    ( ! [X0] : (r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3))) )),
% 1.64/0.58    inference(resolution,[],[f65,f51])).
% 1.64/0.58  fof(f51,plain,(
% 1.64/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))) )),
% 1.64/0.58    inference(cnf_transformation,[],[f26])).
% 1.64/0.58  fof(f26,plain,(
% 1.64/0.58    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.64/0.58    inference(ennf_transformation,[],[f8])).
% 1.64/0.58  fof(f8,axiom,(
% 1.64/0.58    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).
% 1.64/0.59  fof(f65,plain,(
% 1.64/0.59    v1_relat_1(sK3)),
% 1.64/0.59    inference(resolution,[],[f59,f40])).
% 1.64/0.59  fof(f40,plain,(
% 1.64/0.59    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.64/0.59    inference(cnf_transformation,[],[f36])).
% 1.64/0.59  fof(f36,plain,(
% 1.64/0.59    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 1.64/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f35])).
% 1.64/0.59  fof(f35,plain,(
% 1.64/0.59    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 1.64/0.59    introduced(choice_axiom,[])).
% 1.64/0.59  fof(f23,plain,(
% 1.64/0.59    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 1.64/0.59    inference(flattening,[],[f22])).
% 1.64/0.59  fof(f22,plain,(
% 1.64/0.59    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 1.64/0.59    inference(ennf_transformation,[],[f19])).
% 1.64/0.59  fof(f19,plain,(
% 1.64/0.59    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.64/0.59    inference(pure_predicate_removal,[],[f18])).
% 1.64/0.59  fof(f18,negated_conjecture,(
% 1.64/0.59    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.64/0.59    inference(negated_conjecture,[],[f17])).
% 1.64/0.59  fof(f17,conjecture,(
% 1.64/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.64/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).
% 1.64/0.59  fof(f105,plain,(
% 1.64/0.59    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | k1_xboole_0 = k2_relat_1(sK3)),
% 1.64/0.59    inference(backward_demodulation,[],[f94,f103])).
% 1.64/0.59  fof(f103,plain,(
% 1.64/0.59    ( ! [X3] : (k7_relset_1(k1_tarski(sK0),sK1,sK3,X3) = k9_relat_1(sK3,X3)) )),
% 1.64/0.59    inference(resolution,[],[f61,f40])).
% 1.64/0.59  fof(f61,plain,(
% 1.64/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f34])).
% 1.64/0.59  fof(f34,plain,(
% 1.64/0.59    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.64/0.59    inference(ennf_transformation,[],[f16])).
% 1.64/0.59  % (8939)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.64/0.59  fof(f16,axiom,(
% 1.64/0.59    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.64/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.64/0.59  fof(f94,plain,(
% 1.64/0.59    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k2_relat_1(sK3)) | k1_xboole_0 = k2_relat_1(sK3)),
% 1.64/0.59    inference(superposition,[],[f42,f92])).
% 1.64/0.59  fof(f92,plain,(
% 1.64/0.59    k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | k1_xboole_0 = k2_relat_1(sK3)),
% 1.64/0.59    inference(resolution,[],[f91,f55])).
% 1.64/0.59  fof(f55,plain,(
% 1.64/0.59    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 1.64/0.59    inference(cnf_transformation,[],[f38])).
% 1.64/0.59  fof(f38,plain,(
% 1.64/0.59    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.64/0.59    inference(flattening,[],[f37])).
% 1.64/0.59  fof(f37,plain,(
% 1.64/0.59    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.64/0.59    inference(nnf_transformation,[],[f5])).
% 1.64/0.59  fof(f5,axiom,(
% 1.64/0.59    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.64/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.64/0.59  fof(f91,plain,(
% 1.64/0.59    r1_tarski(k2_relat_1(sK3),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.64/0.59    inference(superposition,[],[f89,f83])).
% 1.64/0.59  fof(f83,plain,(
% 1.64/0.59    k2_relat_1(sK3) = k9_relat_1(sK3,k1_tarski(sK0))),
% 1.64/0.59    inference(superposition,[],[f73,f82])).
% 1.64/0.59  fof(f82,plain,(
% 1.64/0.59    sK3 = k7_relat_1(sK3,k1_tarski(sK0))),
% 1.64/0.59    inference(resolution,[],[f75,f72])).
% 1.64/0.59  fof(f72,plain,(
% 1.64/0.59    v4_relat_1(sK3,k1_tarski(sK0))),
% 1.64/0.59    inference(resolution,[],[f60,f40])).
% 1.64/0.59  fof(f75,plain,(
% 1.64/0.59    ( ! [X0] : (~v4_relat_1(sK3,X0) | sK3 = k7_relat_1(sK3,X0)) )),
% 1.64/0.59    inference(resolution,[],[f54,f65])).
% 1.64/0.59  fof(f73,plain,(
% 1.64/0.59    ( ! [X0] : (k9_relat_1(sK3,X0) = k2_relat_1(k7_relat_1(sK3,X0))) )),
% 1.64/0.59    inference(resolution,[],[f52,f65])).
% 1.64/0.59  fof(f89,plain,(
% 1.64/0.59    ( ! [X0] : (r1_tarski(k9_relat_1(sK3,k1_tarski(X0)),k1_tarski(k1_funct_1(sK3,X0)))) )),
% 1.64/0.59    inference(forward_demodulation,[],[f88,f73])).
% 1.64/0.59  fof(f88,plain,(
% 1.64/0.59    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_tarski(X0))),k1_tarski(k1_funct_1(sK3,X0)))) )),
% 1.64/0.59    inference(subsumption_resolution,[],[f87,f65])).
% 1.64/0.59  fof(f87,plain,(
% 1.64/0.59    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_tarski(X0))),k1_tarski(k1_funct_1(sK3,X0))) | ~v1_relat_1(sK3)) )),
% 1.64/0.59    inference(resolution,[],[f53,f39])).
% 1.64/0.59  fof(f39,plain,(
% 1.64/0.59    v1_funct_1(sK3)),
% 1.64/0.59    inference(cnf_transformation,[],[f36])).
% 1.64/0.59  fof(f53,plain,(
% 1.64/0.59    ( ! [X0,X1] : (~v1_funct_1(X1) | r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) | ~v1_relat_1(X1)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f29])).
% 1.64/0.59  fof(f29,plain,(
% 1.64/0.59    ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.64/0.59    inference(flattening,[],[f28])).
% 1.64/0.59  fof(f28,plain,(
% 1.64/0.59    ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.64/0.59    inference(ennf_transformation,[],[f13])).
% 1.64/0.59  fof(f13,axiom,(
% 1.64/0.59    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 1.64/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_funct_1)).
% 1.64/0.59  fof(f42,plain,(
% 1.64/0.59    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.64/0.59    inference(cnf_transformation,[],[f36])).
% 1.64/0.59  fof(f101,plain,(
% 1.64/0.59    k1_xboole_0 != k2_relat_1(sK3) | k1_xboole_0 = sK3),
% 1.64/0.59    inference(superposition,[],[f100,f83])).
% 1.64/0.59  fof(f100,plain,(
% 1.64/0.59    k1_xboole_0 != k9_relat_1(sK3,k1_tarski(sK0)) | k1_xboole_0 = sK3),
% 1.64/0.59    inference(subsumption_resolution,[],[f99,f65])).
% 1.64/0.59  fof(f99,plain,(
% 1.64/0.59    ~v1_relat_1(sK3) | k1_xboole_0 = sK3 | k1_xboole_0 != k9_relat_1(sK3,k1_tarski(sK0))),
% 1.64/0.59    inference(superposition,[],[f81,f82])).
% 1.64/0.59  fof(f81,plain,(
% 1.64/0.59    ( ! [X0] : (~v1_relat_1(k7_relat_1(sK3,X0)) | k1_xboole_0 = k7_relat_1(sK3,X0) | k1_xboole_0 != k9_relat_1(sK3,X0)) )),
% 1.64/0.59    inference(superposition,[],[f49,f73])).
% 1.64/0.59  fof(f49,plain,(
% 1.64/0.59    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f25])).
% 1.64/0.59  fof(f25,plain,(
% 1.64/0.59    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.64/0.59    inference(flattening,[],[f24])).
% 1.64/0.59  % (8942)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.64/0.59  % (8962)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.64/0.59  fof(f24,plain,(
% 1.64/0.59    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.64/0.59    inference(ennf_transformation,[],[f12])).
% 1.64/0.59  fof(f12,axiom,(
% 1.64/0.59    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.64/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 1.64/0.59  fof(f106,plain,(
% 1.64/0.59    ~r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.64/0.59    inference(backward_demodulation,[],[f42,f103])).
% 1.64/0.59  % SZS output end Proof for theBenchmark
% 1.64/0.59  % (8944)------------------------------
% 1.64/0.59  % (8944)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.59  % (8944)Termination reason: Refutation
% 1.64/0.59  
% 1.64/0.59  % (8944)Memory used [KB]: 6268
% 1.64/0.59  % (8944)Time elapsed: 0.094 s
% 1.64/0.59  % (8944)------------------------------
% 1.64/0.59  % (8944)------------------------------
% 1.64/0.59  % (8936)Success in time 0.228 s
%------------------------------------------------------------------------------
