%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:33 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 447 expanded)
%              Number of leaves         :   18 ( 118 expanded)
%              Depth                    :   23
%              Number of atoms          :  221 ( 886 expanded)
%              Number of equality atoms :   97 ( 369 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f353,plain,(
    $false ),
    inference(subsumption_resolution,[],[f352,f47])).

% (26422)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f47,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f352,plain,(
    ~ r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) ),
    inference(forward_demodulation,[],[f334,f117])).

fof(f117,plain,(
    ! [X2] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X2) ),
    inference(forward_demodulation,[],[f114,f46])).

fof(f46,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f114,plain,(
    ! [X2] : k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X2) ),
    inference(backward_demodulation,[],[f104,f112])).

fof(f112,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f110,f85])).

fof(f85,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f50,f44])).

fof(f44,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f50,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f110,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_xboole_0)
      | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f60,f94])).

fof(f94,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f93,f85])).

fof(f93,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_xboole_0)
      | v4_relat_1(k1_xboole_0,X0) ) ),
    inference(subsumption_resolution,[],[f92,f47])).

fof(f92,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | ~ v1_relat_1(k1_xboole_0)
      | v4_relat_1(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f57,f45])).

fof(f45,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f104,plain,(
    ! [X2] : k9_relat_1(k1_xboole_0,X2) = k2_relat_1(k7_relat_1(k1_xboole_0,X2)) ),
    inference(resolution,[],[f56,f85])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f334,plain,(
    ~ r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) ),
    inference(backward_demodulation,[],[f140,f320])).

fof(f320,plain,(
    k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f317,f89])).

fof(f89,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f62,f73])).

fof(f73,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f41,f71])).

fof(f71,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f49,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f54,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f54,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f49,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f41,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f26])).

% (26447)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f317,plain,
    ( ~ v1_relat_1(sK3)
    | k1_xboole_0 = sK3 ),
    inference(trivial_inequality_removal,[],[f316])).

fof(f316,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(sK3)
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f52,f312])).

fof(f312,plain,(
    k1_xboole_0 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f303,f132])).

fof(f132,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f131,f122])).

fof(f122,plain,(
    k9_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) = k2_relat_1(sK3) ),
    inference(superposition,[],[f105,f120])).

fof(f120,plain,(
    sK3 = k7_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(subsumption_resolution,[],[f111,f89])).

fof(f111,plain,
    ( ~ v1_relat_1(sK3)
    | sK3 = k7_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f60,f99])).

fof(f99,plain,(
    v4_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f63,f73])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f105,plain,(
    ! [X3] : k9_relat_1(sK3,X3) = k2_relat_1(k7_relat_1(sK3,X3)) ),
    inference(resolution,[],[f56,f89])).

fof(f131,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK3,X0),k9_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(subsumption_resolution,[],[f130,f89])).

fof(f130,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK3)
      | r1_tarski(k9_relat_1(sK3,X0),k9_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0))) ) ),
    inference(superposition,[],[f107,f120])).

fof(f107,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(k7_relat_1(sK3,X1))
      | r1_tarski(k9_relat_1(k7_relat_1(sK3,X1),X2),k9_relat_1(sK3,X1)) ) ),
    inference(superposition,[],[f55,f105])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

fof(f303,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(superposition,[],[f140,f246])).

fof(f246,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f245,f89])).

fof(f245,plain,
    ( ~ v1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f244,f40])).

fof(f40,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f244,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(equality_resolution,[],[f165])).

fof(f165,plain,(
    ! [X2] :
      ( k1_relat_1(sK3) != k1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k2_relat_1(X2) = k2_enumset1(k1_funct_1(X2,sK0),k1_funct_1(X2,sK0),k1_funct_1(X2,sK0),k1_funct_1(X2,sK0))
      | k1_xboole_0 = k1_relat_1(sK3) ) ),
    inference(superposition,[],[f74,f153])).

fof(f153,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(duplicate_literal_removal,[],[f152])).

fof(f152,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(resolution,[],[f79,f101])).

fof(f101,plain,(
    r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(subsumption_resolution,[],[f100,f89])).

fof(f100,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f99,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
      | k2_enumset1(X1,X1,X1,X1) = X0
      | k2_enumset1(X2,X2,X2,X2) = X0
      | k2_enumset1(X1,X1,X1,X2) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f64,f71,f71,f70,f70])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | k1_tarski(X2) = X0
      | k2_tarski(X1,X2) = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) ) ),
    inference(definition_unfolding,[],[f59,f71,f71])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f52,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f140,plain,(
    ~ r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(backward_demodulation,[],[f72,f138])).

fof(f138,plain,(
    ! [X3] : k9_relat_1(sK3,X3) = k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X3) ),
    inference(resolution,[],[f69,f73])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f72,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f43,f71,f71])).

fof(f43,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:59:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.50  % (26442)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.50  % (26434)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.50  % (26431)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.50  % (26426)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (26442)Refutation not found, incomplete strategy% (26442)------------------------------
% 0.22/0.51  % (26442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (26442)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (26442)Memory used [KB]: 10746
% 0.22/0.51  % (26442)Time elapsed: 0.049 s
% 0.22/0.51  % (26442)------------------------------
% 0.22/0.51  % (26442)------------------------------
% 0.22/0.51  % (26446)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.51  % (26424)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (26431)Refutation not found, incomplete strategy% (26431)------------------------------
% 0.22/0.51  % (26431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (26438)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.52  % (26431)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (26431)Memory used [KB]: 10618
% 0.22/0.52  % (26431)Time elapsed: 0.094 s
% 0.22/0.52  % (26431)------------------------------
% 0.22/0.52  % (26431)------------------------------
% 0.22/0.52  % (26429)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (26425)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.31/0.53  % (26420)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.31/0.53  % (26421)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.31/0.53  % (26420)Refutation not found, incomplete strategy% (26420)------------------------------
% 1.31/0.53  % (26420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.53  % (26420)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.53  
% 1.31/0.53  % (26420)Memory used [KB]: 1791
% 1.31/0.53  % (26420)Time elapsed: 0.115 s
% 1.31/0.53  % (26420)------------------------------
% 1.31/0.53  % (26420)------------------------------
% 1.31/0.53  % (26432)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.31/0.53  % (26424)Refutation not found, incomplete strategy% (26424)------------------------------
% 1.31/0.53  % (26424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.53  % (26424)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.53  
% 1.31/0.53  % (26424)Memory used [KB]: 6268
% 1.31/0.53  % (26424)Time elapsed: 0.099 s
% 1.31/0.53  % (26424)------------------------------
% 1.31/0.53  % (26424)------------------------------
% 1.31/0.53  % (26426)Refutation found. Thanks to Tanya!
% 1.31/0.53  % SZS status Theorem for theBenchmark
% 1.31/0.53  % SZS output start Proof for theBenchmark
% 1.31/0.53  fof(f353,plain,(
% 1.31/0.53    $false),
% 1.31/0.53    inference(subsumption_resolution,[],[f352,f47])).
% 1.31/0.53  % (26422)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.31/0.53  fof(f47,plain,(
% 1.31/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f1])).
% 1.31/0.53  fof(f1,axiom,(
% 1.31/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.31/0.53  fof(f352,plain,(
% 1.31/0.53    ~r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)))),
% 1.31/0.53    inference(forward_demodulation,[],[f334,f117])).
% 1.31/0.53  fof(f117,plain,(
% 1.31/0.53    ( ! [X2] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X2)) )),
% 1.31/0.53    inference(forward_demodulation,[],[f114,f46])).
% 1.31/0.53  fof(f46,plain,(
% 1.31/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.31/0.53    inference(cnf_transformation,[],[f12])).
% 1.31/0.53  fof(f12,axiom,(
% 1.31/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.31/0.53  fof(f114,plain,(
% 1.31/0.53    ( ! [X2] : (k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X2)) )),
% 1.31/0.53    inference(backward_demodulation,[],[f104,f112])).
% 1.31/0.53  fof(f112,plain,(
% 1.31/0.53    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 1.31/0.53    inference(subsumption_resolution,[],[f110,f85])).
% 1.31/0.53  fof(f85,plain,(
% 1.31/0.53    v1_relat_1(k1_xboole_0)),
% 1.31/0.53    inference(superposition,[],[f50,f44])).
% 1.31/0.53  fof(f44,plain,(
% 1.31/0.53    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.31/0.53    inference(cnf_transformation,[],[f14])).
% 1.31/0.53  fof(f14,axiom,(
% 1.31/0.53    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 1.31/0.53  fof(f50,plain,(
% 1.31/0.53    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.31/0.53    inference(cnf_transformation,[],[f15])).
% 1.31/0.53  fof(f15,axiom,(
% 1.31/0.53    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.31/0.53  fof(f110,plain,(
% 1.31/0.53    ( ! [X0] : (~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 1.31/0.53    inference(resolution,[],[f60,f94])).
% 1.31/0.53  fof(f94,plain,(
% 1.31/0.53    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) )),
% 1.31/0.53    inference(subsumption_resolution,[],[f93,f85])).
% 1.31/0.53  fof(f93,plain,(
% 1.31/0.53    ( ! [X0] : (~v1_relat_1(k1_xboole_0) | v4_relat_1(k1_xboole_0,X0)) )),
% 1.31/0.53    inference(subsumption_resolution,[],[f92,f47])).
% 1.31/0.53  fof(f92,plain,(
% 1.31/0.53    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0) | v4_relat_1(k1_xboole_0,X0)) )),
% 1.31/0.53    inference(superposition,[],[f57,f45])).
% 1.31/0.53  fof(f45,plain,(
% 1.31/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.31/0.53    inference(cnf_transformation,[],[f12])).
% 1.31/0.53  fof(f57,plain,(
% 1.31/0.53    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | v4_relat_1(X1,X0)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f31])).
% 1.31/0.53  fof(f31,plain,(
% 1.31/0.53    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.31/0.53    inference(ennf_transformation,[],[f8])).
% 1.31/0.53  fof(f8,axiom,(
% 1.31/0.53    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.31/0.53  fof(f60,plain,(
% 1.31/0.53    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1) )),
% 1.31/0.53    inference(cnf_transformation,[],[f35])).
% 1.31/0.53  fof(f35,plain,(
% 1.31/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.31/0.53    inference(flattening,[],[f34])).
% 1.31/0.53  fof(f34,plain,(
% 1.31/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.31/0.53    inference(ennf_transformation,[],[f11])).
% 1.31/0.53  fof(f11,axiom,(
% 1.31/0.53    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 1.31/0.53  fof(f104,plain,(
% 1.31/0.53    ( ! [X2] : (k9_relat_1(k1_xboole_0,X2) = k2_relat_1(k7_relat_1(k1_xboole_0,X2))) )),
% 1.31/0.53    inference(resolution,[],[f56,f85])).
% 1.31/0.53  fof(f56,plain,(
% 1.31/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))) )),
% 1.31/0.53    inference(cnf_transformation,[],[f30])).
% 1.31/0.53  fof(f30,plain,(
% 1.31/0.53    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.31/0.53    inference(ennf_transformation,[],[f10])).
% 1.31/0.53  fof(f10,axiom,(
% 1.31/0.53    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.31/0.53  fof(f334,plain,(
% 1.31/0.53    ~r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)))),
% 1.31/0.53    inference(backward_demodulation,[],[f140,f320])).
% 1.31/0.53  fof(f320,plain,(
% 1.31/0.53    k1_xboole_0 = sK3),
% 1.31/0.53    inference(subsumption_resolution,[],[f317,f89])).
% 1.31/0.53  fof(f89,plain,(
% 1.31/0.53    v1_relat_1(sK3)),
% 1.31/0.53    inference(resolution,[],[f62,f73])).
% 1.31/0.53  fof(f73,plain,(
% 1.31/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.31/0.53    inference(definition_unfolding,[],[f41,f71])).
% 1.31/0.53  fof(f71,plain,(
% 1.31/0.53    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.31/0.53    inference(definition_unfolding,[],[f49,f70])).
% 1.31/0.53  fof(f70,plain,(
% 1.31/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.31/0.53    inference(definition_unfolding,[],[f54,f61])).
% 1.31/0.53  fof(f61,plain,(
% 1.31/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f4])).
% 1.31/0.53  fof(f4,axiom,(
% 1.31/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.31/0.53  fof(f54,plain,(
% 1.31/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f3])).
% 1.31/0.53  fof(f3,axiom,(
% 1.31/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.31/0.53  fof(f49,plain,(
% 1.31/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f2])).
% 1.31/0.53  fof(f2,axiom,(
% 1.31/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.31/0.53  fof(f41,plain,(
% 1.31/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.31/0.53    inference(cnf_transformation,[],[f26])).
% 1.31/0.53  % (26447)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.31/0.53  fof(f26,plain,(
% 1.31/0.53    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 1.31/0.53    inference(flattening,[],[f25])).
% 1.31/0.53  fof(f25,plain,(
% 1.31/0.53    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 1.31/0.53    inference(ennf_transformation,[],[f22])).
% 1.31/0.53  fof(f22,plain,(
% 1.31/0.53    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.31/0.53    inference(pure_predicate_removal,[],[f21])).
% 1.31/0.53  fof(f21,negated_conjecture,(
% 1.31/0.53    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.31/0.53    inference(negated_conjecture,[],[f20])).
% 1.31/0.53  fof(f20,conjecture,(
% 1.31/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).
% 1.31/0.53  fof(f62,plain,(
% 1.31/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f36])).
% 1.31/0.53  fof(f36,plain,(
% 1.31/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.31/0.53    inference(ennf_transformation,[],[f17])).
% 1.31/0.53  fof(f17,axiom,(
% 1.31/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.31/0.53  fof(f317,plain,(
% 1.31/0.53    ~v1_relat_1(sK3) | k1_xboole_0 = sK3),
% 1.31/0.53    inference(trivial_inequality_removal,[],[f316])).
% 1.31/0.53  fof(f316,plain,(
% 1.31/0.53    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(sK3) | k1_xboole_0 = sK3),
% 1.31/0.53    inference(superposition,[],[f52,f312])).
% 1.31/0.53  fof(f312,plain,(
% 1.31/0.53    k1_xboole_0 = k1_relat_1(sK3)),
% 1.31/0.53    inference(subsumption_resolution,[],[f303,f132])).
% 1.31/0.53  fof(f132,plain,(
% 1.31/0.53    ( ! [X0] : (r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3))) )),
% 1.31/0.53    inference(forward_demodulation,[],[f131,f122])).
% 1.31/0.53  fof(f122,plain,(
% 1.31/0.53    k9_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) = k2_relat_1(sK3)),
% 1.31/0.53    inference(superposition,[],[f105,f120])).
% 1.31/0.53  fof(f120,plain,(
% 1.31/0.53    sK3 = k7_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.31/0.53    inference(subsumption_resolution,[],[f111,f89])).
% 1.31/0.53  fof(f111,plain,(
% 1.31/0.53    ~v1_relat_1(sK3) | sK3 = k7_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.31/0.53    inference(resolution,[],[f60,f99])).
% 1.31/0.53  fof(f99,plain,(
% 1.31/0.53    v4_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.31/0.53    inference(resolution,[],[f63,f73])).
% 1.31/0.53  fof(f63,plain,(
% 1.31/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f37])).
% 1.31/0.53  fof(f37,plain,(
% 1.31/0.53    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.31/0.53    inference(ennf_transformation,[],[f23])).
% 1.31/0.53  fof(f23,plain,(
% 1.31/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.31/0.53    inference(pure_predicate_removal,[],[f18])).
% 1.31/0.53  fof(f18,axiom,(
% 1.31/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.31/0.53  fof(f105,plain,(
% 1.31/0.53    ( ! [X3] : (k9_relat_1(sK3,X3) = k2_relat_1(k7_relat_1(sK3,X3))) )),
% 1.31/0.53    inference(resolution,[],[f56,f89])).
% 1.31/0.53  fof(f131,plain,(
% 1.31/0.53    ( ! [X0] : (r1_tarski(k9_relat_1(sK3,X0),k9_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)))) )),
% 1.31/0.53    inference(subsumption_resolution,[],[f130,f89])).
% 1.31/0.53  fof(f130,plain,(
% 1.31/0.53    ( ! [X0] : (~v1_relat_1(sK3) | r1_tarski(k9_relat_1(sK3,X0),k9_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)))) )),
% 1.31/0.53    inference(superposition,[],[f107,f120])).
% 1.31/0.53  fof(f107,plain,(
% 1.31/0.53    ( ! [X2,X1] : (~v1_relat_1(k7_relat_1(sK3,X1)) | r1_tarski(k9_relat_1(k7_relat_1(sK3,X1),X2),k9_relat_1(sK3,X1))) )),
% 1.31/0.53    inference(superposition,[],[f55,f105])).
% 1.31/0.53  fof(f55,plain,(
% 1.31/0.53    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f29])).
% 1.31/0.53  fof(f29,plain,(
% 1.31/0.53    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.31/0.53    inference(ennf_transformation,[],[f9])).
% 1.31/0.53  fof(f9,axiom,(
% 1.31/0.53    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).
% 1.31/0.53  fof(f303,plain,(
% 1.31/0.53    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | k1_xboole_0 = k1_relat_1(sK3)),
% 1.31/0.53    inference(superposition,[],[f140,f246])).
% 1.31/0.53  fof(f246,plain,(
% 1.31/0.53    k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3)),
% 1.31/0.53    inference(subsumption_resolution,[],[f245,f89])).
% 1.31/0.53  fof(f245,plain,(
% 1.31/0.53    ~v1_relat_1(sK3) | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3)),
% 1.31/0.53    inference(subsumption_resolution,[],[f244,f40])).
% 1.31/0.53  fof(f40,plain,(
% 1.31/0.53    v1_funct_1(sK3)),
% 1.31/0.53    inference(cnf_transformation,[],[f26])).
% 1.31/0.53  fof(f244,plain,(
% 1.31/0.53    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3)),
% 1.31/0.53    inference(equality_resolution,[],[f165])).
% 1.31/0.53  fof(f165,plain,(
% 1.31/0.53    ( ! [X2] : (k1_relat_1(sK3) != k1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | k2_relat_1(X2) = k2_enumset1(k1_funct_1(X2,sK0),k1_funct_1(X2,sK0),k1_funct_1(X2,sK0),k1_funct_1(X2,sK0)) | k1_xboole_0 = k1_relat_1(sK3)) )),
% 1.31/0.53    inference(superposition,[],[f74,f153])).
% 1.31/0.53  fof(f153,plain,(
% 1.31/0.53    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3)),
% 1.31/0.53    inference(duplicate_literal_removal,[],[f152])).
% 1.31/0.53  fof(f152,plain,(
% 1.31/0.53    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3)),
% 1.31/0.53    inference(resolution,[],[f79,f101])).
% 1.31/0.53  fof(f101,plain,(
% 1.31/0.53    r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.31/0.53    inference(subsumption_resolution,[],[f100,f89])).
% 1.31/0.53  fof(f100,plain,(
% 1.31/0.53    r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) | ~v1_relat_1(sK3)),
% 1.31/0.53    inference(resolution,[],[f99,f58])).
% 1.31/0.53  fof(f58,plain,(
% 1.31/0.53    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f31])).
% 1.31/0.53  fof(f79,plain,(
% 1.31/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X2)) | k2_enumset1(X1,X1,X1,X1) = X0 | k2_enumset1(X2,X2,X2,X2) = X0 | k2_enumset1(X1,X1,X1,X2) = X0 | k1_xboole_0 = X0) )),
% 1.31/0.53    inference(definition_unfolding,[],[f64,f71,f71,f70,f70])).
% 1.31/0.53  fof(f64,plain,(
% 1.31/0.53    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | k1_tarski(X2) = X0 | k2_tarski(X1,X2) = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 1.31/0.53    inference(cnf_transformation,[],[f38])).
% 1.31/0.53  fof(f38,plain,(
% 1.31/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.31/0.53    inference(ennf_transformation,[],[f5])).
% 1.31/0.53  fof(f5,axiom,(
% 1.31/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 1.31/0.53  fof(f74,plain,(
% 1.31/0.53    ( ! [X0,X1] : (k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))) )),
% 1.31/0.53    inference(definition_unfolding,[],[f59,f71,f71])).
% 1.31/0.53  fof(f59,plain,(
% 1.31/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))) )),
% 1.31/0.53    inference(cnf_transformation,[],[f33])).
% 1.31/0.53  fof(f33,plain,(
% 1.31/0.53    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.31/0.53    inference(flattening,[],[f32])).
% 1.31/0.53  fof(f32,plain,(
% 1.31/0.53    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.31/0.53    inference(ennf_transformation,[],[f16])).
% 1.31/0.53  fof(f16,axiom,(
% 1.31/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 1.31/0.53  fof(f52,plain,(
% 1.31/0.53    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 1.31/0.53    inference(cnf_transformation,[],[f28])).
% 1.31/0.53  fof(f28,plain,(
% 1.31/0.53    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.31/0.53    inference(flattening,[],[f27])).
% 1.31/0.53  fof(f27,plain,(
% 1.31/0.53    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.31/0.53    inference(ennf_transformation,[],[f13])).
% 1.31/0.53  fof(f13,axiom,(
% 1.31/0.53    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 1.31/0.53  fof(f140,plain,(
% 1.31/0.53    ~r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 1.31/0.53    inference(backward_demodulation,[],[f72,f138])).
% 1.31/0.53  fof(f138,plain,(
% 1.31/0.53    ( ! [X3] : (k9_relat_1(sK3,X3) = k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X3)) )),
% 1.31/0.53    inference(resolution,[],[f69,f73])).
% 1.31/0.53  fof(f69,plain,(
% 1.31/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f39])).
% 1.31/0.53  fof(f39,plain,(
% 1.31/0.53    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.31/0.53    inference(ennf_transformation,[],[f19])).
% 1.31/0.53  fof(f19,axiom,(
% 1.31/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.31/0.53  fof(f72,plain,(
% 1.31/0.53    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 1.31/0.53    inference(definition_unfolding,[],[f43,f71,f71])).
% 1.31/0.53  fof(f43,plain,(
% 1.31/0.53    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.31/0.53    inference(cnf_transformation,[],[f26])).
% 1.31/0.53  % SZS output end Proof for theBenchmark
% 1.31/0.53  % (26426)------------------------------
% 1.31/0.53  % (26426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.53  % (26426)Termination reason: Refutation
% 1.31/0.53  
% 1.31/0.53  % (26426)Memory used [KB]: 6396
% 1.31/0.53  % (26426)Time elapsed: 0.066 s
% 1.31/0.53  % (26426)------------------------------
% 1.31/0.53  % (26426)------------------------------
% 1.31/0.54  % (26419)Success in time 0.169 s
%------------------------------------------------------------------------------
