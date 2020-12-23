%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:09 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 182 expanded)
%              Number of leaves         :   16 (  42 expanded)
%              Depth                    :   14
%              Number of atoms          :  154 ( 376 expanded)
%              Number of equality atoms :   49 ( 153 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f205,plain,(
    $false ),
    inference(subsumption_resolution,[],[f204,f181])).

fof(f181,plain,(
    k1_relat_1(sK2) != k10_relat_1(sK2,sK1) ),
    inference(trivial_inequality_removal,[],[f173])).

fof(f173,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | k1_relat_1(sK2) != k10_relat_1(sK2,sK1) ),
    inference(backward_demodulation,[],[f81,f172])).

fof(f172,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f170,f86])).

fof(f86,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f83,f82])).

fof(f82,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(resolution,[],[f73,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f73,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f43,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1)
        | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
          & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f83,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,k1_relat_1(sK2))) ),
    inference(resolution,[],[f73,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_relat_1)).

fof(f170,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK0),k2_relat_1(sK2))
    | k2_relat_1(sK2) = k9_relat_1(sK2,sK0) ),
    inference(resolution,[],[f163,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f163,plain,(
    r1_tarski(k2_relat_1(sK2),k9_relat_1(sK2,sK0)) ),
    inference(forward_demodulation,[],[f162,f82])).

fof(f162,plain,(
    r1_tarski(k9_relat_1(sK2,k1_relat_1(sK2)),k9_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f89,f73])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(k9_relat_1(X0,k1_relat_1(sK2)),k9_relat_1(X0,sK0)) ) ),
    inference(resolution,[],[f88,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

fof(f88,plain,(
    r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(resolution,[],[f77,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f77,plain,(
    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) ),
    inference(backward_demodulation,[],[f68,f69])).

fof(f69,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f43,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f68,plain,(
    m1_subset_1(k1_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f43,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f81,plain,
    ( k1_relat_1(sK2) != k10_relat_1(sK2,sK1)
    | k2_relat_1(sK2) != k9_relat_1(sK2,sK0) ),
    inference(backward_demodulation,[],[f79,f72])).

fof(f72,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f43,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f79,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k9_relat_1(sK2,sK0)
    | k1_relat_1(sK2) != k10_relat_1(sK2,sK1) ),
    inference(backward_demodulation,[],[f78,f70])).

fof(f70,plain,(
    ! [X1] : k7_relset_1(sK0,sK1,sK2,X1) = k9_relat_1(sK2,X1) ),
    inference(resolution,[],[f43,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f78,plain,
    ( k1_relat_1(sK2) != k10_relat_1(sK2,sK1)
    | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) ),
    inference(backward_demodulation,[],[f76,f69])).

fof(f76,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k10_relat_1(sK2,sK1)
    | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) ),
    inference(backward_demodulation,[],[f42,f67])).

fof(f67,plain,(
    ! [X0] : k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(resolution,[],[f43,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f42,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)
    | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f204,plain,(
    k1_relat_1(sK2) = k10_relat_1(sK2,sK1) ),
    inference(subsumption_resolution,[],[f202,f85])).

fof(f85,plain,(
    ! [X1] : r1_tarski(k10_relat_1(sK2,X1),k1_relat_1(sK2)) ),
    inference(resolution,[],[f73,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f202,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK1),k1_relat_1(sK2))
    | k1_relat_1(sK2) = k10_relat_1(sK2,sK1) ),
    inference(resolution,[],[f195,f49])).

fof(f195,plain,(
    r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,sK1)) ),
    inference(forward_demodulation,[],[f194,f84])).

fof(f84,plain,(
    k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    inference(resolution,[],[f73,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f194,plain,(
    r1_tarski(k10_relat_1(sK2,k2_relat_1(sK2)),k10_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f101,f73])).

fof(f101,plain,(
    ! [X3] :
      ( ~ v1_relat_1(X3)
      | r1_tarski(k10_relat_1(X3,k2_relat_1(sK2)),k10_relat_1(X3,sK1)) ) ),
    inference(resolution,[],[f97,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

fof(f97,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(resolution,[],[f80,f55])).

fof(f80,plain,(
    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(backward_demodulation,[],[f71,f72])).

fof(f71,plain,(
    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f43,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : run_vampire %s %d
% 0.16/0.36  % Computer   : n010.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % WCLimit    : 600
% 0.16/0.37  % DateTime   : Tue Dec  1 11:21:44 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.24/0.51  % (32390)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.24/0.51  % (32389)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.24/0.51  % (32387)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.24/0.51  % (32378)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.24/0.52  % (32399)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.24/0.52  % (32374)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.24/0.52  % (32379)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.24/0.53  % (32397)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.24/0.53  % (32379)Refutation found. Thanks to Tanya!
% 0.24/0.53  % SZS status Theorem for theBenchmark
% 0.24/0.53  % SZS output start Proof for theBenchmark
% 0.24/0.53  fof(f205,plain,(
% 0.24/0.53    $false),
% 0.24/0.53    inference(subsumption_resolution,[],[f204,f181])).
% 0.24/0.53  fof(f181,plain,(
% 0.24/0.53    k1_relat_1(sK2) != k10_relat_1(sK2,sK1)),
% 0.24/0.53    inference(trivial_inequality_removal,[],[f173])).
% 0.24/0.53  fof(f173,plain,(
% 0.24/0.53    k2_relat_1(sK2) != k2_relat_1(sK2) | k1_relat_1(sK2) != k10_relat_1(sK2,sK1)),
% 0.24/0.53    inference(backward_demodulation,[],[f81,f172])).
% 0.24/0.53  fof(f172,plain,(
% 0.24/0.53    k2_relat_1(sK2) = k9_relat_1(sK2,sK0)),
% 0.24/0.53    inference(subsumption_resolution,[],[f170,f86])).
% 0.24/0.53  fof(f86,plain,(
% 0.24/0.53    ( ! [X0] : (r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(sK2))) )),
% 0.24/0.53    inference(forward_demodulation,[],[f83,f82])).
% 0.24/0.53  fof(f82,plain,(
% 0.24/0.53    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))),
% 0.24/0.53    inference(resolution,[],[f73,f62])).
% 0.24/0.53  fof(f62,plain,(
% 0.24/0.53    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 0.24/0.53    inference(cnf_transformation,[],[f37])).
% 0.24/0.53  fof(f37,plain,(
% 0.24/0.53    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.24/0.53    inference(ennf_transformation,[],[f5])).
% 0.24/0.53  fof(f5,axiom,(
% 0.24/0.53    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.24/0.53  fof(f73,plain,(
% 0.24/0.53    v1_relat_1(sK2)),
% 0.24/0.53    inference(resolution,[],[f43,f53])).
% 0.24/0.53  fof(f53,plain,(
% 0.24/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.24/0.53    inference(cnf_transformation,[],[f28])).
% 0.24/0.53  fof(f28,plain,(
% 0.24/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.24/0.53    inference(ennf_transformation,[],[f12])).
% 0.24/0.53  fof(f12,axiom,(
% 0.24/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.24/0.53  fof(f43,plain,(
% 0.24/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.24/0.53    inference(cnf_transformation,[],[f21])).
% 0.24/0.53  fof(f21,plain,(
% 0.24/0.53    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1) | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.24/0.53    inference(ennf_transformation,[],[f20])).
% 0.24/0.53  fof(f20,negated_conjecture,(
% 0.24/0.53    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.24/0.53    inference(negated_conjecture,[],[f19])).
% 0.24/0.53  fof(f19,conjecture,(
% 0.24/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 0.24/0.53  fof(f83,plain,(
% 0.24/0.53    ( ! [X0] : (r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,k1_relat_1(sK2)))) )),
% 0.24/0.53    inference(resolution,[],[f73,f61])).
% 0.24/0.53  fof(f61,plain,(
% 0.24/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1)))) )),
% 0.24/0.53    inference(cnf_transformation,[],[f36])).
% 0.24/0.53  fof(f36,plain,(
% 0.24/0.53    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.24/0.53    inference(ennf_transformation,[],[f6])).
% 0.24/0.53  fof(f6,axiom,(
% 0.24/0.53    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))))),
% 0.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_relat_1)).
% 0.24/0.53  fof(f170,plain,(
% 0.24/0.53    ~r1_tarski(k9_relat_1(sK2,sK0),k2_relat_1(sK2)) | k2_relat_1(sK2) = k9_relat_1(sK2,sK0)),
% 0.24/0.53    inference(resolution,[],[f163,f49])).
% 0.24/0.53  fof(f49,plain,(
% 0.24/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.24/0.53    inference(cnf_transformation,[],[f1])).
% 0.24/0.53  fof(f1,axiom,(
% 0.24/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.24/0.53  fof(f163,plain,(
% 0.24/0.53    r1_tarski(k2_relat_1(sK2),k9_relat_1(sK2,sK0))),
% 0.24/0.53    inference(forward_demodulation,[],[f162,f82])).
% 0.24/0.53  fof(f162,plain,(
% 0.24/0.53    r1_tarski(k9_relat_1(sK2,k1_relat_1(sK2)),k9_relat_1(sK2,sK0))),
% 0.24/0.53    inference(resolution,[],[f89,f73])).
% 0.24/0.53  fof(f89,plain,(
% 0.24/0.53    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(k9_relat_1(X0,k1_relat_1(sK2)),k9_relat_1(X0,sK0))) )),
% 0.24/0.53    inference(resolution,[],[f88,f64])).
% 0.24/0.53  fof(f64,plain,(
% 0.24/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X2) | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) )),
% 0.24/0.53    inference(cnf_transformation,[],[f41])).
% 0.24/0.53  fof(f41,plain,(
% 0.24/0.53    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.24/0.53    inference(flattening,[],[f40])).
% 0.24/0.53  fof(f40,plain,(
% 0.24/0.53    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.24/0.53    inference(ennf_transformation,[],[f7])).
% 0.24/0.53  fof(f7,axiom,(
% 0.24/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).
% 0.24/0.53  fof(f88,plain,(
% 0.24/0.53    r1_tarski(k1_relat_1(sK2),sK0)),
% 0.24/0.53    inference(resolution,[],[f77,f55])).
% 0.24/0.53  fof(f55,plain,(
% 0.24/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.24/0.53    inference(cnf_transformation,[],[f3])).
% 0.24/0.53  fof(f3,axiom,(
% 0.24/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.24/0.53  fof(f77,plain,(
% 0.24/0.53    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))),
% 0.24/0.53    inference(backward_demodulation,[],[f68,f69])).
% 0.24/0.53  fof(f69,plain,(
% 0.24/0.53    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.24/0.53    inference(resolution,[],[f43,f46])).
% 0.24/0.53  fof(f46,plain,(
% 0.24/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.24/0.53    inference(cnf_transformation,[],[f24])).
% 0.24/0.53  fof(f24,plain,(
% 0.24/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.24/0.53    inference(ennf_transformation,[],[f15])).
% 0.24/0.53  fof(f15,axiom,(
% 0.24/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.24/0.53  fof(f68,plain,(
% 0.24/0.53    m1_subset_1(k1_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))),
% 0.24/0.53    inference(resolution,[],[f43,f45])).
% 0.24/0.53  fof(f45,plain,(
% 0.24/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 0.24/0.53    inference(cnf_transformation,[],[f23])).
% 0.24/0.53  fof(f23,plain,(
% 0.24/0.53    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.24/0.53    inference(ennf_transformation,[],[f13])).
% 0.24/0.53  fof(f13,axiom,(
% 0.24/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 0.24/0.53  fof(f81,plain,(
% 0.24/0.53    k1_relat_1(sK2) != k10_relat_1(sK2,sK1) | k2_relat_1(sK2) != k9_relat_1(sK2,sK0)),
% 0.24/0.53    inference(backward_demodulation,[],[f79,f72])).
% 0.24/0.53  fof(f72,plain,(
% 0.24/0.53    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.24/0.53    inference(resolution,[],[f43,f52])).
% 0.24/0.53  fof(f52,plain,(
% 0.24/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.24/0.53    inference(cnf_transformation,[],[f27])).
% 0.24/0.53  fof(f27,plain,(
% 0.24/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.24/0.53    inference(ennf_transformation,[],[f16])).
% 0.24/0.53  fof(f16,axiom,(
% 0.24/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.24/0.53  fof(f79,plain,(
% 0.24/0.53    k2_relset_1(sK0,sK1,sK2) != k9_relat_1(sK2,sK0) | k1_relat_1(sK2) != k10_relat_1(sK2,sK1)),
% 0.24/0.53    inference(backward_demodulation,[],[f78,f70])).
% 0.24/0.53  fof(f70,plain,(
% 0.24/0.53    ( ! [X1] : (k7_relset_1(sK0,sK1,sK2,X1) = k9_relat_1(sK2,X1)) )),
% 0.24/0.53    inference(resolution,[],[f43,f50])).
% 0.24/0.53  fof(f50,plain,(
% 0.24/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.24/0.53    inference(cnf_transformation,[],[f25])).
% 0.24/0.53  fof(f25,plain,(
% 0.24/0.53    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.24/0.53    inference(ennf_transformation,[],[f17])).
% 0.24/0.53  fof(f17,axiom,(
% 0.24/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.24/0.53  fof(f78,plain,(
% 0.24/0.53    k1_relat_1(sK2) != k10_relat_1(sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)),
% 0.24/0.53    inference(backward_demodulation,[],[f76,f69])).
% 0.24/0.53  fof(f76,plain,(
% 0.24/0.53    k1_relset_1(sK0,sK1,sK2) != k10_relat_1(sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)),
% 0.24/0.53    inference(backward_demodulation,[],[f42,f67])).
% 0.24/0.53  fof(f67,plain,(
% 0.24/0.53    ( ! [X0] : (k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0)) )),
% 0.24/0.53    inference(resolution,[],[f43,f44])).
% 0.24/0.53  fof(f44,plain,(
% 0.24/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.24/0.53    inference(cnf_transformation,[],[f22])).
% 0.24/0.53  fof(f22,plain,(
% 0.24/0.53    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.24/0.53    inference(ennf_transformation,[],[f18])).
% 0.24/0.53  fof(f18,axiom,(
% 0.24/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.24/0.53  fof(f42,plain,(
% 0.24/0.53    k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)),
% 0.24/0.53    inference(cnf_transformation,[],[f21])).
% 0.24/0.53  fof(f204,plain,(
% 0.24/0.53    k1_relat_1(sK2) = k10_relat_1(sK2,sK1)),
% 0.24/0.53    inference(subsumption_resolution,[],[f202,f85])).
% 0.24/0.53  fof(f85,plain,(
% 0.24/0.53    ( ! [X1] : (r1_tarski(k10_relat_1(sK2,X1),k1_relat_1(sK2))) )),
% 0.24/0.53    inference(resolution,[],[f73,f59])).
% 0.24/0.53  fof(f59,plain,(
% 0.24/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))) )),
% 0.24/0.53    inference(cnf_transformation,[],[f34])).
% 0.24/0.53  fof(f34,plain,(
% 0.24/0.53    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.24/0.53    inference(ennf_transformation,[],[f8])).
% 0.24/0.53  fof(f8,axiom,(
% 0.24/0.53    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 0.24/0.53  fof(f202,plain,(
% 0.24/0.53    ~r1_tarski(k10_relat_1(sK2,sK1),k1_relat_1(sK2)) | k1_relat_1(sK2) = k10_relat_1(sK2,sK1)),
% 0.24/0.53    inference(resolution,[],[f195,f49])).
% 0.24/0.53  fof(f195,plain,(
% 0.24/0.53    r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,sK1))),
% 0.24/0.53    inference(forward_demodulation,[],[f194,f84])).
% 0.24/0.53  fof(f84,plain,(
% 0.24/0.53    k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2))),
% 0.24/0.53    inference(resolution,[],[f73,f60])).
% 0.24/0.53  fof(f60,plain,(
% 0.24/0.53    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))) )),
% 0.24/0.53    inference(cnf_transformation,[],[f35])).
% 0.24/0.53  fof(f35,plain,(
% 0.24/0.53    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.24/0.53    inference(ennf_transformation,[],[f9])).
% 0.24/0.53  fof(f9,axiom,(
% 0.24/0.53    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 0.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.24/0.53  fof(f194,plain,(
% 0.24/0.53    r1_tarski(k10_relat_1(sK2,k2_relat_1(sK2)),k10_relat_1(sK2,sK1))),
% 0.24/0.53    inference(resolution,[],[f101,f73])).
% 0.24/0.53  fof(f101,plain,(
% 0.24/0.53    ( ! [X3] : (~v1_relat_1(X3) | r1_tarski(k10_relat_1(X3,k2_relat_1(sK2)),k10_relat_1(X3,sK1))) )),
% 0.24/0.53    inference(resolution,[],[f97,f57])).
% 0.24/0.53  fof(f57,plain,(
% 0.24/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X2) | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) )),
% 0.24/0.53    inference(cnf_transformation,[],[f31])).
% 0.24/0.53  fof(f31,plain,(
% 0.24/0.53    ! [X0,X1,X2] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.24/0.53    inference(flattening,[],[f30])).
% 0.24/0.53  fof(f30,plain,(
% 0.24/0.53    ! [X0,X1,X2] : ((r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.24/0.53    inference(ennf_transformation,[],[f10])).
% 0.24/0.53  fof(f10,axiom,(
% 0.24/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 0.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).
% 0.24/0.53  fof(f97,plain,(
% 0.24/0.53    r1_tarski(k2_relat_1(sK2),sK1)),
% 0.24/0.53    inference(resolution,[],[f80,f55])).
% 0.24/0.53  fof(f80,plain,(
% 0.24/0.53    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.24/0.53    inference(backward_demodulation,[],[f71,f72])).
% 0.24/0.53  fof(f71,plain,(
% 0.24/0.53    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))),
% 0.24/0.53    inference(resolution,[],[f43,f51])).
% 0.24/0.53  fof(f51,plain,(
% 0.24/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))) )),
% 0.24/0.53    inference(cnf_transformation,[],[f26])).
% 0.24/0.53  fof(f26,plain,(
% 0.24/0.53    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.24/0.53    inference(ennf_transformation,[],[f14])).
% 0.24/0.53  fof(f14,axiom,(
% 0.24/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.24/0.53  % SZS output end Proof for theBenchmark
% 0.24/0.53  % (32379)------------------------------
% 0.24/0.53  % (32379)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.24/0.53  % (32379)Termination reason: Refutation
% 0.24/0.53  
% 0.24/0.53  % (32379)Memory used [KB]: 6268
% 0.24/0.53  % (32379)Time elapsed: 0.077 s
% 0.24/0.53  % (32379)------------------------------
% 0.24/0.53  % (32379)------------------------------
% 0.24/0.53  % (32370)Success in time 0.15 s
%------------------------------------------------------------------------------
