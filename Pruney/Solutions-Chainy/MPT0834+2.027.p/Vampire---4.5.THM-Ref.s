%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:13 EST 2020

% Result     : Theorem 3.47s
% Output     : Refutation 3.83s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 301 expanded)
%              Number of leaves         :   22 (  81 expanded)
%              Depth                    :   17
%              Number of atoms          :  258 ( 749 expanded)
%              Number of equality atoms :   85 ( 297 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1867,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1866,f101])).

fof(f101,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f93,f55])).

fof(f55,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
      | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f49])).

fof(f49,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1)
          | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
        | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1)
        | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
          & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f93,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | v1_relat_1(X2) ) ),
    inference(resolution,[],[f63,f64])).

fof(f64,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f1866,plain,(
    ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f1865,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f1865,plain,(
    ~ r1_tarski(k10_relat_1(sK2,sK1),k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f1863,f1216])).

fof(f1216,plain,(
    k1_relat_1(sK2) != k10_relat_1(sK2,sK1) ),
    inference(superposition,[],[f1027,f1214])).

fof(f1214,plain,(
    ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(sK0,sK1,sK2,X0) ),
    inference(resolution,[],[f86,f55])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f1027,plain,(
    k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f1026,f276])).

fof(f276,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,sK0) ),
    inference(superposition,[],[f265,f275])).

fof(f275,plain,(
    sK2 = k7_relat_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f270,f101])).

fof(f270,plain,
    ( sK2 = k7_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f74,f124])).

fof(f124,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f82,f55])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f265,plain,(
    ! [X80] : k2_relat_1(k7_relat_1(sK2,X80)) = k9_relat_1(sK2,X80) ),
    inference(resolution,[],[f68,f101])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f1026,plain,
    ( k2_relat_1(sK2) != k9_relat_1(sK2,sK0)
    | k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f918,f1024])).

fof(f1024,plain,(
    ! [X0] : k9_relat_1(sK2,X0) = k7_relset_1(sK0,sK1,sK2,X0) ),
    inference(resolution,[],[f85,f55])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f918,plain,
    ( k7_relset_1(sK0,sK1,sK2,sK0) != k2_relat_1(sK2)
    | k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f799,f916])).

fof(f916,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f81,f55])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f799,plain,
    ( k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) ),
    inference(backward_demodulation,[],[f56,f797])).

fof(f797,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f80,f55])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f56,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
    | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f1863,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK1),k1_relat_1(sK2))
    | k1_relat_1(sK2) = k10_relat_1(sK2,sK1) ),
    inference(resolution,[],[f1713,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1713,plain,(
    r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,sK1)) ),
    inference(forward_demodulation,[],[f1712,f1588])).

fof(f1588,plain,(
    k10_relat_1(sK2,sK1) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    inference(superposition,[],[f424,f1581])).

fof(f1581,plain,(
    k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),sK1) ),
    inference(superposition,[],[f1573,f523])).

fof(f523,plain,(
    k2_relat_1(sK2) = k9_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1) ),
    inference(forward_demodulation,[],[f521,f61])).

fof(f61,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f521,plain,(
    k9_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1) = k2_relat_1(k6_relat_1(k2_relat_1(sK2))) ),
    inference(superposition,[],[f264,f507])).

fof(f507,plain,(
    k6_relat_1(k2_relat_1(sK2)) = k7_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1) ),
    inference(resolution,[],[f308,f133])).

fof(f133,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(subsumption_resolution,[],[f132,f101])).

fof(f132,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f130,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f130,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f83,f55])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f308,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,X4)
      | k6_relat_1(X3) = k7_relat_1(k6_relat_1(X3),X4) ) ),
    inference(subsumption_resolution,[],[f306,f57])).

fof(f57,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v5_relat_1(k6_relat_1(X0),X0)
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).

fof(f306,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,X4)
      | k6_relat_1(X3) = k7_relat_1(k6_relat_1(X3),X4)
      | ~ v1_relat_1(k6_relat_1(X3)) ) ),
    inference(resolution,[],[f302,f74])).

fof(f302,plain,(
    ! [X12,X11] :
      ( v4_relat_1(k6_relat_1(X11),X12)
      | ~ r1_tarski(X11,X12) ) ),
    inference(subsumption_resolution,[],[f297,f57])).

fof(f297,plain,(
    ! [X12,X11] :
      ( v4_relat_1(k6_relat_1(X11),X12)
      | ~ v1_relat_1(k6_relat_1(X11))
      | ~ r1_tarski(X11,X12) ) ),
    inference(resolution,[],[f73,f58])).

fof(f58,plain,(
    ! [X0] : v4_relat_1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_relat_1(X2,X0)
      | v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v4_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t217_relat_1)).

fof(f264,plain,(
    ! [X78,X79] : k2_relat_1(k7_relat_1(k6_relat_1(X78),X79)) = k9_relat_1(k6_relat_1(X78),X79) ),
    inference(resolution,[],[f68,f57])).

fof(f1573,plain,(
    ! [X290,X291] : k9_relat_1(k6_relat_1(X291),X290) = k3_xboole_0(X291,X290) ),
    inference(forward_demodulation,[],[f1572,f61])).

fof(f1572,plain,(
    ! [X290,X291] : k9_relat_1(k6_relat_1(X291),X290) = k2_relat_1(k6_relat_1(k3_xboole_0(X291,X290))) ),
    inference(forward_demodulation,[],[f1570,f65])).

fof(f65,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f1570,plain,(
    ! [X290,X291] : k2_relat_1(k5_relat_1(k6_relat_1(X290),k6_relat_1(X291))) = k9_relat_1(k6_relat_1(X291),X290) ),
    inference(resolution,[],[f569,f57])).

fof(f569,plain,(
    ! [X136,X135] :
      ( ~ v1_relat_1(X135)
      | k2_relat_1(k5_relat_1(k6_relat_1(X136),X135)) = k9_relat_1(X135,X136) ) ),
    inference(forward_demodulation,[],[f567,f61])).

fof(f567,plain,(
    ! [X136,X135] :
      ( ~ v1_relat_1(X135)
      | k2_relat_1(k5_relat_1(k6_relat_1(X136),X135)) = k9_relat_1(X135,k2_relat_1(k6_relat_1(X136))) ) ),
    inference(resolution,[],[f62,f57])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f424,plain,(
    ! [X109] : k10_relat_1(sK2,X109) = k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X109)) ),
    inference(resolution,[],[f69,f101])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

fof(f1712,plain,(
    r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2))) ),
    inference(subsumption_resolution,[],[f1694,f101])).

fof(f1694,plain,
    ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2)))
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f674,f1385])).

fof(f1385,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(superposition,[],[f265,f1372])).

fof(f1372,plain,(
    sK2 = k7_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f1370,f101])).

fof(f1370,plain,
    ( sK2 = k7_relat_1(sK2,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f1362,f74])).

fof(f1362,plain,(
    v4_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(resolution,[],[f1359,f82])).

fof(f1359,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
    inference(resolution,[],[f1356,f88])).

fof(f88,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f1356,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),X0)
      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) ) ),
    inference(resolution,[],[f87,f55])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

fof(f674,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(X0),k10_relat_1(X0,k9_relat_1(X0,k1_relat_1(X0))))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f70,f88])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:05:09 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.30/0.56  % (15523)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.50/0.56  % (15520)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.50/0.56  % (15521)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.50/0.56  % (15522)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.50/0.56  % (15531)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.50/0.57  % (15536)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.50/0.57  % (15534)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.50/0.57  % (15518)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.50/0.57  % (15528)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.50/0.57  % (15539)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.50/0.57  % (15537)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.50/0.58  % (15538)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.50/0.58  % (15529)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.50/0.58  % (15530)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.50/0.58  % (15526)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.50/0.58  % (15519)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.50/0.59  % (15527)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.50/0.60  % (15535)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.50/0.61  % (15517)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.50/0.62  % (15515)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.50/0.63  % (15532)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.50/0.63  % (15524)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.50/0.63  % (15540)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.50/0.64  % (15533)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.50/0.64  % (15516)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.50/0.64  % (15525)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 3.47/0.85  % (15518)Refutation found. Thanks to Tanya!
% 3.47/0.85  % SZS status Theorem for theBenchmark
% 3.83/0.86  % SZS output start Proof for theBenchmark
% 3.83/0.87  fof(f1867,plain,(
% 3.83/0.87    $false),
% 3.83/0.87    inference(subsumption_resolution,[],[f1866,f101])).
% 3.83/0.87  fof(f101,plain,(
% 3.83/0.87    v1_relat_1(sK2)),
% 3.83/0.87    inference(resolution,[],[f93,f55])).
% 3.83/0.87  fof(f55,plain,(
% 3.83/0.87    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.83/0.87    inference(cnf_transformation,[],[f50])).
% 3.83/0.87  fof(f50,plain,(
% 3.83/0.87    (k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.83/0.87    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f49])).
% 3.83/0.87  fof(f49,plain,(
% 3.83/0.87    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1) | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 3.83/0.87    introduced(choice_axiom,[])).
% 3.83/0.87  fof(f26,plain,(
% 3.83/0.87    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1) | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.83/0.87    inference(ennf_transformation,[],[f25])).
% 3.83/0.87  fof(f25,negated_conjecture,(
% 3.83/0.87    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 3.83/0.87    inference(negated_conjecture,[],[f24])).
% 3.83/0.87  fof(f24,conjecture,(
% 3.83/0.87    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 3.83/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 3.83/0.87  fof(f93,plain,(
% 3.83/0.87    ( ! [X4,X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | v1_relat_1(X2)) )),
% 3.83/0.87    inference(resolution,[],[f63,f64])).
% 3.83/0.87  fof(f64,plain,(
% 3.83/0.87    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.83/0.87    inference(cnf_transformation,[],[f6])).
% 3.83/0.87  fof(f6,axiom,(
% 3.83/0.87    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.83/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 3.83/0.87  fof(f63,plain,(
% 3.83/0.87    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 3.83/0.87    inference(cnf_transformation,[],[f28])).
% 3.83/0.87  fof(f28,plain,(
% 3.83/0.87    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.83/0.87    inference(ennf_transformation,[],[f4])).
% 3.83/0.87  fof(f4,axiom,(
% 3.83/0.87    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.83/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 3.83/0.87  fof(f1866,plain,(
% 3.83/0.87    ~v1_relat_1(sK2)),
% 3.83/0.87    inference(resolution,[],[f1865,f66])).
% 3.83/0.87  fof(f66,plain,(
% 3.83/0.87    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.83/0.87    inference(cnf_transformation,[],[f29])).
% 3.83/0.87  fof(f29,plain,(
% 3.83/0.87    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.83/0.87    inference(ennf_transformation,[],[f9])).
% 3.83/0.87  fof(f9,axiom,(
% 3.83/0.87    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 3.83/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 3.83/0.87  fof(f1865,plain,(
% 3.83/0.87    ~r1_tarski(k10_relat_1(sK2,sK1),k1_relat_1(sK2))),
% 3.83/0.87    inference(subsumption_resolution,[],[f1863,f1216])).
% 3.83/0.87  fof(f1216,plain,(
% 3.83/0.87    k1_relat_1(sK2) != k10_relat_1(sK2,sK1)),
% 3.83/0.87    inference(superposition,[],[f1027,f1214])).
% 3.83/0.87  fof(f1214,plain,(
% 3.83/0.87    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(sK0,sK1,sK2,X0)) )),
% 3.83/0.87    inference(resolution,[],[f86,f55])).
% 3.83/0.87  fof(f86,plain,(
% 3.83/0.87    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 3.83/0.87    inference(cnf_transformation,[],[f46])).
% 3.83/0.87  fof(f46,plain,(
% 3.83/0.87    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.83/0.87    inference(ennf_transformation,[],[f22])).
% 3.83/0.87  fof(f22,axiom,(
% 3.83/0.87    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 3.83/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 3.83/0.87  fof(f1027,plain,(
% 3.83/0.87    k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2)),
% 3.83/0.87    inference(subsumption_resolution,[],[f1026,f276])).
% 3.83/0.87  fof(f276,plain,(
% 3.83/0.87    k2_relat_1(sK2) = k9_relat_1(sK2,sK0)),
% 3.83/0.87    inference(superposition,[],[f265,f275])).
% 3.83/0.87  fof(f275,plain,(
% 3.83/0.87    sK2 = k7_relat_1(sK2,sK0)),
% 3.83/0.87    inference(subsumption_resolution,[],[f270,f101])).
% 3.83/0.87  fof(f270,plain,(
% 3.83/0.87    sK2 = k7_relat_1(sK2,sK0) | ~v1_relat_1(sK2)),
% 3.83/0.87    inference(resolution,[],[f74,f124])).
% 3.83/0.87  fof(f124,plain,(
% 3.83/0.87    v4_relat_1(sK2,sK0)),
% 3.83/0.87    inference(resolution,[],[f82,f55])).
% 3.83/0.87  fof(f82,plain,(
% 3.83/0.87    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 3.83/0.87    inference(cnf_transformation,[],[f42])).
% 3.83/0.87  fof(f42,plain,(
% 3.83/0.87    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.83/0.87    inference(ennf_transformation,[],[f18])).
% 3.83/0.87  fof(f18,axiom,(
% 3.83/0.87    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.83/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 3.83/0.87  fof(f74,plain,(
% 3.83/0.87    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 3.83/0.87    inference(cnf_transformation,[],[f39])).
% 3.83/0.87  fof(f39,plain,(
% 3.83/0.87    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.83/0.87    inference(flattening,[],[f38])).
% 3.83/0.87  fof(f38,plain,(
% 3.83/0.87    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.83/0.87    inference(ennf_transformation,[],[f11])).
% 3.83/0.87  fof(f11,axiom,(
% 3.83/0.87    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.83/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 3.83/0.87  fof(f265,plain,(
% 3.83/0.87    ( ! [X80] : (k2_relat_1(k7_relat_1(sK2,X80)) = k9_relat_1(sK2,X80)) )),
% 3.83/0.87    inference(resolution,[],[f68,f101])).
% 3.83/0.87  fof(f68,plain,(
% 3.83/0.87    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 3.83/0.87    inference(cnf_transformation,[],[f31])).
% 3.83/0.87  fof(f31,plain,(
% 3.83/0.87    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.83/0.87    inference(ennf_transformation,[],[f7])).
% 3.83/0.87  fof(f7,axiom,(
% 3.83/0.87    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.83/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 3.83/0.87  fof(f1026,plain,(
% 3.83/0.87    k2_relat_1(sK2) != k9_relat_1(sK2,sK0) | k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2)),
% 3.83/0.87    inference(backward_demodulation,[],[f918,f1024])).
% 3.83/0.87  fof(f1024,plain,(
% 3.83/0.87    ( ! [X0] : (k9_relat_1(sK2,X0) = k7_relset_1(sK0,sK1,sK2,X0)) )),
% 3.83/0.87    inference(resolution,[],[f85,f55])).
% 3.83/0.87  fof(f85,plain,(
% 3.83/0.87    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 3.83/0.87    inference(cnf_transformation,[],[f45])).
% 3.83/0.87  fof(f45,plain,(
% 3.83/0.87    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.83/0.87    inference(ennf_transformation,[],[f21])).
% 3.83/0.87  fof(f21,axiom,(
% 3.83/0.87    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 3.83/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 3.83/0.87  fof(f918,plain,(
% 3.83/0.87    k7_relset_1(sK0,sK1,sK2,sK0) != k2_relat_1(sK2) | k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2)),
% 3.83/0.87    inference(backward_demodulation,[],[f799,f916])).
% 3.83/0.87  fof(f916,plain,(
% 3.83/0.87    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 3.83/0.87    inference(resolution,[],[f81,f55])).
% 3.83/0.87  fof(f81,plain,(
% 3.83/0.87    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 3.83/0.87    inference(cnf_transformation,[],[f41])).
% 3.83/0.87  fof(f41,plain,(
% 3.83/0.87    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.83/0.87    inference(ennf_transformation,[],[f20])).
% 3.83/0.87  fof(f20,axiom,(
% 3.83/0.87    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 3.83/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 3.83/0.87  fof(f799,plain,(
% 3.83/0.87    k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)),
% 3.83/0.87    inference(backward_demodulation,[],[f56,f797])).
% 3.83/0.87  fof(f797,plain,(
% 3.83/0.87    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 3.83/0.87    inference(resolution,[],[f80,f55])).
% 3.83/0.87  fof(f80,plain,(
% 3.83/0.87    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 3.83/0.87    inference(cnf_transformation,[],[f40])).
% 3.83/0.87  fof(f40,plain,(
% 3.83/0.87    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.83/0.87    inference(ennf_transformation,[],[f19])).
% 3.83/0.87  fof(f19,axiom,(
% 3.83/0.87    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 3.83/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 3.83/0.87  fof(f56,plain,(
% 3.83/0.87    k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)),
% 3.83/0.87    inference(cnf_transformation,[],[f50])).
% 3.83/0.87  fof(f1863,plain,(
% 3.83/0.87    ~r1_tarski(k10_relat_1(sK2,sK1),k1_relat_1(sK2)) | k1_relat_1(sK2) = k10_relat_1(sK2,sK1)),
% 3.83/0.87    inference(resolution,[],[f1713,f77])).
% 3.83/0.87  fof(f77,plain,(
% 3.83/0.87    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 3.83/0.87    inference(cnf_transformation,[],[f53])).
% 3.83/0.87  fof(f53,plain,(
% 3.83/0.87    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.83/0.87    inference(flattening,[],[f52])).
% 3.83/0.87  fof(f52,plain,(
% 3.83/0.87    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.83/0.87    inference(nnf_transformation,[],[f1])).
% 3.83/0.87  fof(f1,axiom,(
% 3.83/0.87    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.83/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.83/0.87  fof(f1713,plain,(
% 3.83/0.87    r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,sK1))),
% 3.83/0.87    inference(forward_demodulation,[],[f1712,f1588])).
% 3.83/0.87  fof(f1588,plain,(
% 3.83/0.87    k10_relat_1(sK2,sK1) = k10_relat_1(sK2,k2_relat_1(sK2))),
% 3.83/0.87    inference(superposition,[],[f424,f1581])).
% 3.83/0.87  fof(f1581,plain,(
% 3.83/0.87    k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),sK1)),
% 3.83/0.87    inference(superposition,[],[f1573,f523])).
% 3.83/0.87  fof(f523,plain,(
% 3.83/0.87    k2_relat_1(sK2) = k9_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1)),
% 3.83/0.87    inference(forward_demodulation,[],[f521,f61])).
% 3.83/0.87  fof(f61,plain,(
% 3.83/0.87    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.83/0.87    inference(cnf_transformation,[],[f13])).
% 3.83/0.87  fof(f13,axiom,(
% 3.83/0.87    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.83/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 3.83/0.87  fof(f521,plain,(
% 3.83/0.87    k9_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1) = k2_relat_1(k6_relat_1(k2_relat_1(sK2)))),
% 3.83/0.87    inference(superposition,[],[f264,f507])).
% 3.83/0.87  fof(f507,plain,(
% 3.83/0.87    k6_relat_1(k2_relat_1(sK2)) = k7_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1)),
% 3.83/0.87    inference(resolution,[],[f308,f133])).
% 3.83/0.87  fof(f133,plain,(
% 3.83/0.87    r1_tarski(k2_relat_1(sK2),sK1)),
% 3.83/0.87    inference(subsumption_resolution,[],[f132,f101])).
% 3.83/0.87  fof(f132,plain,(
% 3.83/0.87    r1_tarski(k2_relat_1(sK2),sK1) | ~v1_relat_1(sK2)),
% 3.83/0.87    inference(resolution,[],[f130,f71])).
% 3.83/0.87  fof(f71,plain,(
% 3.83/0.87    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.83/0.87    inference(cnf_transformation,[],[f51])).
% 3.83/0.87  fof(f51,plain,(
% 3.83/0.87    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.83/0.87    inference(nnf_transformation,[],[f35])).
% 3.83/0.87  fof(f35,plain,(
% 3.83/0.87    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.83/0.87    inference(ennf_transformation,[],[f5])).
% 3.83/0.87  fof(f5,axiom,(
% 3.83/0.87    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.83/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 3.83/0.87  fof(f130,plain,(
% 3.83/0.87    v5_relat_1(sK2,sK1)),
% 3.83/0.87    inference(resolution,[],[f83,f55])).
% 3.83/0.87  fof(f83,plain,(
% 3.83/0.87    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 3.83/0.87    inference(cnf_transformation,[],[f42])).
% 3.83/0.87  fof(f308,plain,(
% 3.83/0.87    ( ! [X4,X3] : (~r1_tarski(X3,X4) | k6_relat_1(X3) = k7_relat_1(k6_relat_1(X3),X4)) )),
% 3.83/0.87    inference(subsumption_resolution,[],[f306,f57])).
% 3.83/0.87  fof(f57,plain,(
% 3.83/0.87    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.83/0.87    inference(cnf_transformation,[],[f15])).
% 3.83/0.87  fof(f15,axiom,(
% 3.83/0.87    ! [X0] : (v5_relat_1(k6_relat_1(X0),X0) & v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 3.83/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).
% 3.83/0.87  fof(f306,plain,(
% 3.83/0.87    ( ! [X4,X3] : (~r1_tarski(X3,X4) | k6_relat_1(X3) = k7_relat_1(k6_relat_1(X3),X4) | ~v1_relat_1(k6_relat_1(X3))) )),
% 3.83/0.87    inference(resolution,[],[f302,f74])).
% 3.83/0.87  fof(f302,plain,(
% 3.83/0.87    ( ! [X12,X11] : (v4_relat_1(k6_relat_1(X11),X12) | ~r1_tarski(X11,X12)) )),
% 3.83/0.87    inference(subsumption_resolution,[],[f297,f57])).
% 3.83/0.87  fof(f297,plain,(
% 3.83/0.87    ( ! [X12,X11] : (v4_relat_1(k6_relat_1(X11),X12) | ~v1_relat_1(k6_relat_1(X11)) | ~r1_tarski(X11,X12)) )),
% 3.83/0.87    inference(resolution,[],[f73,f58])).
% 3.83/0.87  fof(f58,plain,(
% 3.83/0.87    ( ! [X0] : (v4_relat_1(k6_relat_1(X0),X0)) )),
% 3.83/0.87    inference(cnf_transformation,[],[f15])).
% 3.83/0.87  fof(f73,plain,(
% 3.83/0.87    ( ! [X2,X0,X1] : (~v4_relat_1(X2,X0) | v4_relat_1(X2,X1) | ~v1_relat_1(X2) | ~r1_tarski(X0,X1)) )),
% 3.83/0.87    inference(cnf_transformation,[],[f37])).
% 3.83/0.87  fof(f37,plain,(
% 3.83/0.87    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~r1_tarski(X0,X1))),
% 3.83/0.87    inference(flattening,[],[f36])).
% 3.83/0.87  fof(f36,plain,(
% 3.83/0.87    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | (~v4_relat_1(X2,X0) | ~v1_relat_1(X2))) | ~r1_tarski(X0,X1))),
% 3.83/0.87    inference(ennf_transformation,[],[f12])).
% 3.83/0.87  fof(f12,axiom,(
% 3.83/0.87    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v4_relat_1(X2,X0) & v1_relat_1(X2)) => v4_relat_1(X2,X1)))),
% 3.83/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t217_relat_1)).
% 3.83/0.87  fof(f264,plain,(
% 3.83/0.87    ( ! [X78,X79] : (k2_relat_1(k7_relat_1(k6_relat_1(X78),X79)) = k9_relat_1(k6_relat_1(X78),X79)) )),
% 3.83/0.87    inference(resolution,[],[f68,f57])).
% 3.83/0.87  fof(f1573,plain,(
% 3.83/0.87    ( ! [X290,X291] : (k9_relat_1(k6_relat_1(X291),X290) = k3_xboole_0(X291,X290)) )),
% 3.83/0.87    inference(forward_demodulation,[],[f1572,f61])).
% 3.83/0.87  fof(f1572,plain,(
% 3.83/0.87    ( ! [X290,X291] : (k9_relat_1(k6_relat_1(X291),X290) = k2_relat_1(k6_relat_1(k3_xboole_0(X291,X290)))) )),
% 3.83/0.87    inference(forward_demodulation,[],[f1570,f65])).
% 3.83/0.87  fof(f65,plain,(
% 3.83/0.87    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 3.83/0.87    inference(cnf_transformation,[],[f17])).
% 3.83/0.87  fof(f17,axiom,(
% 3.83/0.87    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 3.83/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 3.83/0.87  fof(f1570,plain,(
% 3.83/0.87    ( ! [X290,X291] : (k2_relat_1(k5_relat_1(k6_relat_1(X290),k6_relat_1(X291))) = k9_relat_1(k6_relat_1(X291),X290)) )),
% 3.83/0.87    inference(resolution,[],[f569,f57])).
% 3.83/0.87  fof(f569,plain,(
% 3.83/0.87    ( ! [X136,X135] : (~v1_relat_1(X135) | k2_relat_1(k5_relat_1(k6_relat_1(X136),X135)) = k9_relat_1(X135,X136)) )),
% 3.83/0.87    inference(forward_demodulation,[],[f567,f61])).
% 3.83/0.87  fof(f567,plain,(
% 3.83/0.87    ( ! [X136,X135] : (~v1_relat_1(X135) | k2_relat_1(k5_relat_1(k6_relat_1(X136),X135)) = k9_relat_1(X135,k2_relat_1(k6_relat_1(X136)))) )),
% 3.83/0.87    inference(resolution,[],[f62,f57])).
% 3.83/0.87  fof(f62,plain,(
% 3.83/0.87    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))) )),
% 3.83/0.87    inference(cnf_transformation,[],[f27])).
% 3.83/0.87  fof(f27,plain,(
% 3.83/0.87    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.83/0.87    inference(ennf_transformation,[],[f8])).
% 3.83/0.87  fof(f8,axiom,(
% 3.83/0.87    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 3.83/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).
% 3.83/0.87  fof(f424,plain,(
% 3.83/0.87    ( ! [X109] : (k10_relat_1(sK2,X109) = k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X109))) )),
% 3.83/0.87    inference(resolution,[],[f69,f101])).
% 3.83/0.87  fof(f69,plain,(
% 3.83/0.87    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))) )),
% 3.83/0.87    inference(cnf_transformation,[],[f32])).
% 3.83/0.87  fof(f32,plain,(
% 3.83/0.87    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.83/0.87    inference(ennf_transformation,[],[f10])).
% 3.83/0.87  fof(f10,axiom,(
% 3.83/0.87    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 3.83/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).
% 3.83/0.87  fof(f1712,plain,(
% 3.83/0.87    r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2)))),
% 3.83/0.87    inference(subsumption_resolution,[],[f1694,f101])).
% 3.83/0.87  fof(f1694,plain,(
% 3.83/0.87    r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2))) | ~v1_relat_1(sK2)),
% 3.83/0.87    inference(superposition,[],[f674,f1385])).
% 3.83/0.87  fof(f1385,plain,(
% 3.83/0.87    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))),
% 3.83/0.87    inference(superposition,[],[f265,f1372])).
% 3.83/0.87  fof(f1372,plain,(
% 3.83/0.87    sK2 = k7_relat_1(sK2,k1_relat_1(sK2))),
% 3.83/0.87    inference(subsumption_resolution,[],[f1370,f101])).
% 3.83/0.87  fof(f1370,plain,(
% 3.83/0.87    sK2 = k7_relat_1(sK2,k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 3.83/0.87    inference(resolution,[],[f1362,f74])).
% 3.83/0.87  fof(f1362,plain,(
% 3.83/0.87    v4_relat_1(sK2,k1_relat_1(sK2))),
% 3.83/0.87    inference(resolution,[],[f1359,f82])).
% 3.83/0.87  fof(f1359,plain,(
% 3.83/0.87    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))),
% 3.83/0.87    inference(resolution,[],[f1356,f88])).
% 3.83/0.87  fof(f88,plain,(
% 3.83/0.87    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.83/0.87    inference(equality_resolution,[],[f76])).
% 3.83/0.87  fof(f76,plain,(
% 3.83/0.87    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.83/0.87    inference(cnf_transformation,[],[f53])).
% 3.83/0.87  fof(f1356,plain,(
% 3.83/0.87    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) )),
% 3.83/0.87    inference(resolution,[],[f87,f55])).
% 3.83/0.87  fof(f87,plain,(
% 3.83/0.87    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 3.83/0.87    inference(cnf_transformation,[],[f48])).
% 3.83/0.87  fof(f48,plain,(
% 3.83/0.87    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 3.83/0.87    inference(flattening,[],[f47])).
% 3.83/0.87  fof(f47,plain,(
% 3.83/0.87    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 3.83/0.87    inference(ennf_transformation,[],[f23])).
% 3.83/0.87  fof(f23,axiom,(
% 3.83/0.87    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 3.83/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).
% 3.83/0.87  fof(f674,plain,(
% 3.83/0.87    ( ! [X0] : (r1_tarski(k1_relat_1(X0),k10_relat_1(X0,k9_relat_1(X0,k1_relat_1(X0)))) | ~v1_relat_1(X0)) )),
% 3.83/0.87    inference(resolution,[],[f70,f88])).
% 3.83/0.87  fof(f70,plain,(
% 3.83/0.87    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~v1_relat_1(X1)) )),
% 3.83/0.87    inference(cnf_transformation,[],[f34])).
% 3.83/0.87  fof(f34,plain,(
% 3.83/0.87    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.83/0.87    inference(flattening,[],[f33])).
% 3.83/0.87  fof(f33,plain,(
% 3.83/0.87    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.83/0.87    inference(ennf_transformation,[],[f16])).
% 3.83/0.87  fof(f16,axiom,(
% 3.83/0.87    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 3.83/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 3.83/0.87  % SZS output end Proof for theBenchmark
% 3.83/0.87  % (15518)------------------------------
% 3.83/0.87  % (15518)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.83/0.87  % (15518)Termination reason: Refutation
% 3.83/0.87  
% 3.83/0.87  % (15518)Memory used [KB]: 9466
% 3.83/0.87  % (15518)Time elapsed: 0.411 s
% 3.83/0.87  % (15518)------------------------------
% 3.83/0.87  % (15518)------------------------------
% 3.83/0.87  % (15514)Success in time 0.505 s
%------------------------------------------------------------------------------
