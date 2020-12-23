%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:12 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 290 expanded)
%              Number of leaves         :   15 (  79 expanded)
%              Depth                    :   13
%              Number of atoms          :  190 ( 582 expanded)
%              Number of equality atoms :   95 ( 320 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f142,plain,(
    $false ),
    inference(subsumption_resolution,[],[f141,f102])).

fof(f102,plain,(
    k3_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f67,f101])).

% (6077)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (6053)Termination reason: Refutation not found, incomplete strategy

% (6053)Memory used [KB]: 1791
% (6053)Time elapsed: 0.136 s
% (6053)------------------------------
% (6053)------------------------------
% (6069)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (6056)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f101,plain,(
    k2_relset_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f46,f68])).

fof(f68,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f35,f66])).

fof(f66,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f38,f65])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f40,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f44,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f44,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f40,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f38,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f67,plain,(
    k2_relset_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,sK2) != k3_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) ),
    inference(definition_unfolding,[],[f37,f66,f66])).

fof(f37,plain,(
    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f141,plain,(
    k3_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f140,f105])).

fof(f105,plain,(
    k2_relat_1(sK2) = k11_relat_1(sK2,sK0) ),
    inference(superposition,[],[f104,f100])).

fof(f100,plain,(
    k9_relat_1(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k2_relat_1(sK2) ),
    inference(superposition,[],[f97,f99])).

fof(f99,plain,(
    sK2 = k7_relat_1(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f98,f96])).

fof(f96,plain,(
    v4_relat_1(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f48,f68])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f98,plain,(
    ! [X0] :
      ( ~ v4_relat_1(sK2,X0)
      | sK2 = k7_relat_1(sK2,X0) ) ),
    inference(resolution,[],[f43,f95])).

fof(f95,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f68,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f97,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(resolution,[],[f41,f95])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f104,plain,(
    ! [X0] : k11_relat_1(sK2,X0) = k9_relat_1(sK2,k3_enumset1(X0,X0,X0,X0,X0)) ),
    inference(resolution,[],[f70,f95])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k3_enumset1(X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f39,f66])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(f140,plain,(
    k3_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k11_relat_1(sK2,sK0) ),
    inference(resolution,[],[f139,f131])).

fof(f131,plain,(
    r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(superposition,[],[f90,f114])).

fof(f114,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f113,f103])).

fof(f103,plain,(
    k1_relset_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f47,f68])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f113,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k1_relset_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,sK2) ),
    inference(subsumption_resolution,[],[f112,f69])).

fof(f69,plain,(
    v1_funct_2(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f34,f66])).

fof(f34,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f112,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k1_relset_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,sK2)
    | ~ v1_funct_2(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(subsumption_resolution,[],[f111,f36])).

fof(f36,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f19])).

fof(f111,plain,
    ( k1_xboole_0 = sK1
    | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k1_relset_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,sK2)
    | ~ v1_funct_2(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(resolution,[],[f54,f68])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f90,plain,(
    ! [X4,X2,X1] : r2_hidden(X4,k3_enumset1(X4,X4,X4,X1,X2)) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(X4,X3)
      | k3_enumset1(X4,X4,X4,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f74])).

% (6055)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f61,f64])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f139,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK2))
      | k11_relat_1(sK2,X0) = k3_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f138,f95])).

fof(f138,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK2)
      | ~ r2_hidden(X0,k1_relat_1(sK2))
      | k11_relat_1(sK2,X0) = k3_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) ) ),
    inference(resolution,[],[f71,f33])).

fof(f33,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k11_relat_1(X1,X0) = k3_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) ) ),
    inference(definition_unfolding,[],[f42,f66])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:29:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.55  % (6053)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.41/0.56  % (6076)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.41/0.56  % (6068)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.41/0.57  % (6068)Refutation not found, incomplete strategy% (6068)------------------------------
% 1.41/0.57  % (6068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.57  % (6068)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.57  
% 1.41/0.57  % (6068)Memory used [KB]: 6268
% 1.41/0.57  % (6068)Time elapsed: 0.080 s
% 1.41/0.57  % (6068)------------------------------
% 1.41/0.57  % (6068)------------------------------
% 1.41/0.57  % (6060)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.41/0.57  % (6059)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.41/0.57  % (6053)Refutation not found, incomplete strategy% (6053)------------------------------
% 1.41/0.57  % (6053)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.58  % (6076)Refutation not found, incomplete strategy% (6076)------------------------------
% 1.41/0.58  % (6076)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.58  % (6076)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.58  
% 1.41/0.58  % (6076)Memory used [KB]: 1791
% 1.41/0.58  % (6076)Time elapsed: 0.075 s
% 1.41/0.58  % (6076)------------------------------
% 1.41/0.58  % (6076)------------------------------
% 1.41/0.58  % (6059)Refutation found. Thanks to Tanya!
% 1.41/0.58  % SZS status Theorem for theBenchmark
% 1.41/0.58  % SZS output start Proof for theBenchmark
% 1.41/0.58  fof(f142,plain,(
% 1.41/0.58    $false),
% 1.41/0.58    inference(subsumption_resolution,[],[f141,f102])).
% 1.41/0.58  fof(f102,plain,(
% 1.41/0.58    k3_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2)),
% 1.41/0.58    inference(backward_demodulation,[],[f67,f101])).
% 1.41/0.58  % (6077)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.41/0.58  % (6053)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.58  
% 1.67/0.58  % (6053)Memory used [KB]: 1791
% 1.67/0.58  % (6053)Time elapsed: 0.136 s
% 1.67/0.58  % (6053)------------------------------
% 1.67/0.58  % (6053)------------------------------
% 1.67/0.58  % (6069)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.67/0.59  % (6056)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.67/0.60  fof(f101,plain,(
% 1.67/0.60    k2_relset_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2)),
% 1.67/0.60    inference(resolution,[],[f46,f68])).
% 1.67/0.60  fof(f68,plain,(
% 1.67/0.60    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)))),
% 1.67/0.60    inference(definition_unfolding,[],[f35,f66])).
% 1.67/0.60  fof(f66,plain,(
% 1.67/0.60    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.67/0.60    inference(definition_unfolding,[],[f38,f65])).
% 1.67/0.60  fof(f65,plain,(
% 1.67/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.67/0.60    inference(definition_unfolding,[],[f40,f64])).
% 1.67/0.60  fof(f64,plain,(
% 1.67/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.67/0.60    inference(definition_unfolding,[],[f44,f55])).
% 1.67/0.60  fof(f55,plain,(
% 1.67/0.60    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f5])).
% 1.67/0.60  fof(f5,axiom,(
% 1.67/0.60    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.67/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.67/0.60  fof(f44,plain,(
% 1.67/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f4])).
% 1.67/0.60  fof(f4,axiom,(
% 1.67/0.60    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.67/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.67/0.60  fof(f40,plain,(
% 1.67/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f3])).
% 1.67/0.60  fof(f3,axiom,(
% 1.67/0.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.67/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.67/0.60  fof(f38,plain,(
% 1.67/0.60    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f2])).
% 1.67/0.60  fof(f2,axiom,(
% 1.67/0.60    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.67/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.67/0.60  fof(f35,plain,(
% 1.67/0.60    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.67/0.60    inference(cnf_transformation,[],[f19])).
% 1.67/0.60  fof(f19,plain,(
% 1.67/0.60    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 1.67/0.60    inference(flattening,[],[f18])).
% 1.67/0.60  fof(f18,plain,(
% 1.67/0.60    ? [X0,X1,X2] : ((k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 1.67/0.60    inference(ennf_transformation,[],[f16])).
% 1.67/0.60  fof(f16,negated_conjecture,(
% 1.67/0.60    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 1.67/0.60    inference(negated_conjecture,[],[f15])).
% 1.67/0.60  fof(f15,conjecture,(
% 1.67/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 1.67/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).
% 1.67/0.60  fof(f46,plain,(
% 1.67/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f27])).
% 1.67/0.60  fof(f27,plain,(
% 1.67/0.60    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.67/0.60    inference(ennf_transformation,[],[f13])).
% 1.67/0.60  fof(f13,axiom,(
% 1.67/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.67/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.67/0.60  fof(f67,plain,(
% 1.67/0.60    k2_relset_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,sK2) != k3_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0))),
% 1.67/0.60    inference(definition_unfolding,[],[f37,f66,f66])).
% 1.67/0.60  fof(f37,plain,(
% 1.67/0.60    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))),
% 1.67/0.60    inference(cnf_transformation,[],[f19])).
% 1.67/0.60  fof(f141,plain,(
% 1.67/0.60    k3_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)),
% 1.67/0.60    inference(forward_demodulation,[],[f140,f105])).
% 1.67/0.60  fof(f105,plain,(
% 1.67/0.60    k2_relat_1(sK2) = k11_relat_1(sK2,sK0)),
% 1.67/0.60    inference(superposition,[],[f104,f100])).
% 1.67/0.60  fof(f100,plain,(
% 1.67/0.60    k9_relat_1(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k2_relat_1(sK2)),
% 1.67/0.60    inference(superposition,[],[f97,f99])).
% 1.67/0.60  fof(f99,plain,(
% 1.67/0.60    sK2 = k7_relat_1(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 1.67/0.60    inference(resolution,[],[f98,f96])).
% 1.67/0.60  fof(f96,plain,(
% 1.67/0.60    v4_relat_1(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 1.67/0.60    inference(resolution,[],[f48,f68])).
% 1.67/0.60  fof(f48,plain,(
% 1.67/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f29])).
% 1.67/0.60  fof(f29,plain,(
% 1.67/0.60    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.67/0.60    inference(ennf_transformation,[],[f17])).
% 1.67/0.60  fof(f17,plain,(
% 1.67/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.67/0.60    inference(pure_predicate_removal,[],[f11])).
% 1.67/0.60  fof(f11,axiom,(
% 1.67/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.67/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.67/0.60  fof(f98,plain,(
% 1.67/0.60    ( ! [X0] : (~v4_relat_1(sK2,X0) | sK2 = k7_relat_1(sK2,X0)) )),
% 1.67/0.60    inference(resolution,[],[f43,f95])).
% 1.67/0.60  fof(f95,plain,(
% 1.67/0.60    v1_relat_1(sK2)),
% 1.67/0.60    inference(resolution,[],[f68,f45])).
% 1.67/0.60  fof(f45,plain,(
% 1.67/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f26])).
% 1.67/0.60  fof(f26,plain,(
% 1.67/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.67/0.60    inference(ennf_transformation,[],[f10])).
% 1.67/0.60  fof(f10,axiom,(
% 1.67/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.67/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.67/0.60  fof(f43,plain,(
% 1.67/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 1.67/0.60    inference(cnf_transformation,[],[f25])).
% 1.67/0.60  fof(f25,plain,(
% 1.67/0.60    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.67/0.60    inference(flattening,[],[f24])).
% 1.67/0.60  fof(f24,plain,(
% 1.67/0.60    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.67/0.60    inference(ennf_transformation,[],[f8])).
% 1.67/0.60  fof(f8,axiom,(
% 1.67/0.60    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.67/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 1.67/0.60  fof(f97,plain,(
% 1.67/0.60    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)) )),
% 1.67/0.60    inference(resolution,[],[f41,f95])).
% 1.67/0.60  fof(f41,plain,(
% 1.67/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f21])).
% 1.67/0.60  fof(f21,plain,(
% 1.67/0.60    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.67/0.60    inference(ennf_transformation,[],[f7])).
% 1.67/0.60  fof(f7,axiom,(
% 1.67/0.60    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.67/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.67/0.60  fof(f104,plain,(
% 1.67/0.60    ( ! [X0] : (k11_relat_1(sK2,X0) = k9_relat_1(sK2,k3_enumset1(X0,X0,X0,X0,X0))) )),
% 1.67/0.60    inference(resolution,[],[f70,f95])).
% 1.67/0.60  fof(f70,plain,(
% 1.67/0.60    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k3_enumset1(X1,X1,X1,X1,X1))) )),
% 1.67/0.60    inference(definition_unfolding,[],[f39,f66])).
% 1.67/0.60  fof(f39,plain,(
% 1.67/0.60    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))) )),
% 1.67/0.60    inference(cnf_transformation,[],[f20])).
% 1.67/0.60  fof(f20,plain,(
% 1.67/0.60    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 1.67/0.60    inference(ennf_transformation,[],[f6])).
% 1.67/0.60  fof(f6,axiom,(
% 1.67/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 1.67/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).
% 1.67/0.60  fof(f140,plain,(
% 1.67/0.60    k3_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k11_relat_1(sK2,sK0)),
% 1.67/0.60    inference(resolution,[],[f139,f131])).
% 1.67/0.60  fof(f131,plain,(
% 1.67/0.60    r2_hidden(sK0,k1_relat_1(sK2))),
% 1.67/0.60    inference(superposition,[],[f90,f114])).
% 1.67/0.60  fof(f114,plain,(
% 1.67/0.60    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK2)),
% 1.67/0.60    inference(forward_demodulation,[],[f113,f103])).
% 1.67/0.60  fof(f103,plain,(
% 1.67/0.60    k1_relset_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,sK2) = k1_relat_1(sK2)),
% 1.67/0.60    inference(resolution,[],[f47,f68])).
% 1.67/0.60  fof(f47,plain,(
% 1.67/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f28])).
% 1.67/0.60  fof(f28,plain,(
% 1.67/0.60    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.67/0.60    inference(ennf_transformation,[],[f12])).
% 1.67/0.60  fof(f12,axiom,(
% 1.67/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.67/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.67/0.60  fof(f113,plain,(
% 1.67/0.60    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k1_relset_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,sK2)),
% 1.67/0.60    inference(subsumption_resolution,[],[f112,f69])).
% 1.67/0.60  fof(f69,plain,(
% 1.67/0.60    v1_funct_2(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)),
% 1.67/0.60    inference(definition_unfolding,[],[f34,f66])).
% 1.67/0.60  fof(f34,plain,(
% 1.67/0.60    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 1.67/0.60    inference(cnf_transformation,[],[f19])).
% 1.67/0.60  fof(f112,plain,(
% 1.67/0.60    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k1_relset_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,sK2) | ~v1_funct_2(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)),
% 1.67/0.60    inference(subsumption_resolution,[],[f111,f36])).
% 1.67/0.60  fof(f36,plain,(
% 1.67/0.60    k1_xboole_0 != sK1),
% 1.67/0.60    inference(cnf_transformation,[],[f19])).
% 1.67/0.60  fof(f111,plain,(
% 1.67/0.60    k1_xboole_0 = sK1 | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k1_relset_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,sK2) | ~v1_funct_2(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)),
% 1.67/0.60    inference(resolution,[],[f54,f68])).
% 1.67/0.60  fof(f54,plain,(
% 1.67/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f31])).
% 1.67/0.60  fof(f31,plain,(
% 1.67/0.60    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.67/0.60    inference(flattening,[],[f30])).
% 1.67/0.60  fof(f30,plain,(
% 1.67/0.60    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.67/0.60    inference(ennf_transformation,[],[f14])).
% 1.67/0.60  fof(f14,axiom,(
% 1.67/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.67/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.67/0.60  fof(f90,plain,(
% 1.67/0.60    ( ! [X4,X2,X1] : (r2_hidden(X4,k3_enumset1(X4,X4,X4,X1,X2))) )),
% 1.67/0.60    inference(equality_resolution,[],[f89])).
% 1.67/0.60  fof(f89,plain,(
% 1.67/0.60    ( ! [X4,X2,X3,X1] : (r2_hidden(X4,X3) | k3_enumset1(X4,X4,X4,X1,X2) != X3) )),
% 1.67/0.60    inference(equality_resolution,[],[f74])).
% 1.67/0.60  % (6055)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.67/0.60  fof(f74,plain,(
% 1.67/0.60    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 1.67/0.60    inference(definition_unfolding,[],[f61,f64])).
% 1.67/0.60  fof(f61,plain,(
% 1.67/0.60    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.67/0.60    inference(cnf_transformation,[],[f32])).
% 1.67/0.60  fof(f32,plain,(
% 1.67/0.60    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.67/0.60    inference(ennf_transformation,[],[f1])).
% 1.67/0.60  fof(f1,axiom,(
% 1.67/0.60    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.67/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.67/0.60  fof(f139,plain,(
% 1.67/0.60    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | k11_relat_1(sK2,X0) = k3_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0))) )),
% 1.67/0.60    inference(subsumption_resolution,[],[f138,f95])).
% 1.67/0.60  fof(f138,plain,(
% 1.67/0.60    ( ! [X0] : (~v1_relat_1(sK2) | ~r2_hidden(X0,k1_relat_1(sK2)) | k11_relat_1(sK2,X0) = k3_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0))) )),
% 1.67/0.60    inference(resolution,[],[f71,f33])).
% 1.67/0.60  fof(f33,plain,(
% 1.67/0.60    v1_funct_1(sK2)),
% 1.67/0.60    inference(cnf_transformation,[],[f19])).
% 1.67/0.60  fof(f71,plain,(
% 1.67/0.60    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | k11_relat_1(X1,X0) = k3_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))) )),
% 1.67/0.60    inference(definition_unfolding,[],[f42,f66])).
% 1.67/0.60  fof(f42,plain,(
% 1.67/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))) )),
% 1.67/0.60    inference(cnf_transformation,[],[f23])).
% 1.67/0.60  fof(f23,plain,(
% 1.67/0.60    ! [X0,X1] : (k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.67/0.60    inference(flattening,[],[f22])).
% 1.67/0.60  fof(f22,plain,(
% 1.67/0.60    ! [X0,X1] : ((k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.67/0.60    inference(ennf_transformation,[],[f9])).
% 1.67/0.60  fof(f9,axiom,(
% 1.67/0.60    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.67/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).
% 1.67/0.60  % SZS output end Proof for theBenchmark
% 1.67/0.60  % (6059)------------------------------
% 1.67/0.60  % (6059)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.60  % (6059)Termination reason: Refutation
% 1.67/0.60  
% 1.67/0.60  % (6059)Memory used [KB]: 6268
% 1.67/0.60  % (6059)Time elapsed: 0.141 s
% 1.67/0.60  % (6059)------------------------------
% 1.67/0.60  % (6059)------------------------------
% 1.67/0.60  % (6052)Success in time 0.237 s
%------------------------------------------------------------------------------
