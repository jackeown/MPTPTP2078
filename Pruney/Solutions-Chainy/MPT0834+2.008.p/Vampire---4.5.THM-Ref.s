%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:10 EST 2020

% Result     : Theorem 2.41s
% Output     : Refutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 264 expanded)
%              Number of leaves         :   21 (  69 expanded)
%              Depth                    :   18
%              Number of atoms          :  243 ( 668 expanded)
%              Number of equality atoms :   81 ( 287 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1361,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1360,f92])).

fof(f92,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f77,f54])).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
      | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f48])).

fof(f48,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1)
          | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
        | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1)
        | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
          & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f1360,plain,(
    ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f1355,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f1355,plain,(
    ~ r1_tarski(k10_relat_1(sK2,sK1),k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f1354,f1154])).

fof(f1154,plain,(
    k1_relat_1(sK2) != k10_relat_1(sK2,sK1) ),
    inference(superposition,[],[f1056,f1152])).

fof(f1152,plain,(
    ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(sK0,sK1,sK2,X0) ),
    inference(resolution,[],[f84,f54])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f1056,plain,(
    k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f1055,f260])).

fof(f260,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,sK0) ),
    inference(superposition,[],[f236,f259])).

fof(f259,plain,(
    sK2 = k7_relat_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f252,f92])).

fof(f252,plain,
    ( sK2 = k7_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f71,f106])).

fof(f106,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f80,f54])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f236,plain,(
    ! [X40] : k2_relat_1(k7_relat_1(sK2,X40)) = k9_relat_1(sK2,X40) ),
    inference(resolution,[],[f65,f92])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f1055,plain,
    ( k2_relat_1(sK2) != k9_relat_1(sK2,sK0)
    | k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f939,f1053])).

fof(f1053,plain,(
    ! [X0] : k9_relat_1(sK2,X0) = k7_relset_1(sK0,sK1,sK2,X0) ),
    inference(resolution,[],[f83,f54])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f939,plain,
    ( k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2)
    | k7_relset_1(sK0,sK1,sK2,sK0) != k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f803,f937])).

fof(f937,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f79,f54])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f803,plain,
    ( k7_relset_1(sK0,sK1,sK2,sK0) != k2_relat_1(sK2)
    | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) ),
    inference(backward_demodulation,[],[f55,f801])).

fof(f801,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f78,f54])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f55,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
    | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f1354,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK1),k1_relat_1(sK2))
    | k1_relat_1(sK2) = k10_relat_1(sK2,sK1) ),
    inference(resolution,[],[f1348,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
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

fof(f1348,plain,(
    r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,sK1)) ),
    inference(forward_demodulation,[],[f1347,f557])).

fof(f557,plain,(
    k10_relat_1(sK2,k2_relat_1(sK2)) = k10_relat_1(sK2,sK1) ),
    inference(superposition,[],[f488,f548])).

fof(f548,plain,(
    k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),sK1) ),
    inference(forward_demodulation,[],[f538,f59])).

fof(f59,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f538,plain,(
    k3_xboole_0(k2_relat_1(sK2),sK1) = k1_relat_1(k6_relat_1(k2_relat_1(sK2))) ),
    inference(superposition,[],[f170,f515])).

fof(f515,plain,(
    k6_relat_1(k2_relat_1(sK2)) = k7_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1) ),
    inference(resolution,[],[f347,f111])).

fof(f111,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(subsumption_resolution,[],[f110,f92])).

fof(f110,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f108,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f108,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f81,f54])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f347,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,X4)
      | k6_relat_1(X3) = k7_relat_1(k6_relat_1(X3),X4) ) ),
    inference(subsumption_resolution,[],[f344,f56])).

fof(f56,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v5_relat_1(k6_relat_1(X0),X0)
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).

fof(f344,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,X4)
      | k6_relat_1(X3) = k7_relat_1(k6_relat_1(X3),X4)
      | ~ v1_relat_1(k6_relat_1(X3)) ) ),
    inference(resolution,[],[f339,f71])).

fof(f339,plain,(
    ! [X19,X20] :
      ( v4_relat_1(k6_relat_1(X19),X20)
      | ~ r1_tarski(X19,X20) ) ),
    inference(subsumption_resolution,[],[f331,f56])).

fof(f331,plain,(
    ! [X19,X20] :
      ( v4_relat_1(k6_relat_1(X19),X20)
      | ~ v1_relat_1(k6_relat_1(X19))
      | ~ r1_tarski(X19,X20) ) ),
    inference(resolution,[],[f70,f57])).

fof(f57,plain,(
    ! [X0] : v4_relat_1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_relat_1(X2,X0)
      | v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v4_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t217_relat_1)).

fof(f170,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k1_relat_1(k7_relat_1(k6_relat_1(X6),X7)) ),
    inference(superposition,[],[f59,f166])).

fof(f166,plain,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(backward_demodulation,[],[f61,f163])).

fof(f163,plain,(
    ! [X12,X13] : k7_relat_1(k6_relat_1(X12),X13) = k5_relat_1(k6_relat_1(X13),k6_relat_1(X12)) ),
    inference(resolution,[],[f64,f56])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f61,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f488,plain,(
    ! [X64] : k10_relat_1(sK2,X64) = k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X64)) ),
    inference(resolution,[],[f66,f92])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

fof(f1347,plain,(
    r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2))) ),
    inference(subsumption_resolution,[],[f1346,f92])).

fof(f1346,plain,
    ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2)))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f1345,f86])).

fof(f86,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f1345,plain,
    ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2)))
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f67,f1329])).

fof(f1329,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(superposition,[],[f236,f1315])).

fof(f1315,plain,(
    sK2 = k7_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f1313,f92])).

fof(f1313,plain,
    ( sK2 = k7_relat_1(sK2,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f1306,f71])).

fof(f1306,plain,(
    v4_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(resolution,[],[f1300,f80])).

fof(f1300,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
    inference(resolution,[],[f1271,f86])).

fof(f1271,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),X0)
      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) ) ),
    inference(resolution,[],[f85,f54])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:47:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (13947)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.49  % (13955)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.52  % (13942)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.52  % (13937)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.54  % (13940)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.54  % (13936)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (13939)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.54  % (13950)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.55  % (13959)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.41/0.55  % (13954)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.41/0.55  % (13951)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.41/0.55  % (13949)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.41/0.55  % (13935)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.41/0.56  % (13941)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.41/0.56  % (13941)Refutation not found, incomplete strategy% (13941)------------------------------
% 1.41/0.56  % (13941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (13941)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.56  
% 1.41/0.56  % (13941)Memory used [KB]: 10618
% 1.41/0.56  % (13941)Time elapsed: 0.145 s
% 1.41/0.56  % (13941)------------------------------
% 1.41/0.56  % (13941)------------------------------
% 1.41/0.56  % (13938)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.41/0.56  % (13958)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.41/0.56  % (13957)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.61/0.57  % (13946)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.61/0.57  % (13952)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.61/0.57  % (13953)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.61/0.57  % (13943)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.61/0.57  % (13944)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.61/0.58  % (13956)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.61/0.58  % (13945)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.61/0.58  % (13960)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.61/0.58  % (13948)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 2.41/0.70  % (13938)Refutation found. Thanks to Tanya!
% 2.41/0.70  % SZS status Theorem for theBenchmark
% 2.41/0.70  % SZS output start Proof for theBenchmark
% 2.41/0.70  fof(f1361,plain,(
% 2.41/0.70    $false),
% 2.41/0.70    inference(subsumption_resolution,[],[f1360,f92])).
% 2.41/0.70  fof(f92,plain,(
% 2.41/0.70    v1_relat_1(sK2)),
% 2.41/0.70    inference(resolution,[],[f77,f54])).
% 2.41/0.70  fof(f54,plain,(
% 2.41/0.70    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.41/0.70    inference(cnf_transformation,[],[f49])).
% 2.41/0.70  fof(f49,plain,(
% 2.41/0.70    (k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.41/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f48])).
% 2.41/0.70  fof(f48,plain,(
% 2.41/0.70    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1) | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 2.41/0.70    introduced(choice_axiom,[])).
% 2.41/0.70  fof(f25,plain,(
% 2.41/0.70    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1) | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.41/0.70    inference(ennf_transformation,[],[f24])).
% 2.41/0.70  fof(f24,negated_conjecture,(
% 2.41/0.70    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 2.41/0.70    inference(negated_conjecture,[],[f23])).
% 2.41/0.70  fof(f23,conjecture,(
% 2.41/0.70    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 2.41/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 2.41/0.70  fof(f77,plain,(
% 2.41/0.70    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 2.41/0.70    inference(cnf_transformation,[],[f38])).
% 2.41/0.70  fof(f38,plain,(
% 2.41/0.70    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.41/0.70    inference(ennf_transformation,[],[f16])).
% 2.41/0.70  fof(f16,axiom,(
% 2.41/0.70    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.41/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.41/0.70  fof(f1360,plain,(
% 2.41/0.70    ~v1_relat_1(sK2)),
% 2.41/0.70    inference(resolution,[],[f1355,f62])).
% 2.41/0.70  fof(f62,plain,(
% 2.41/0.70    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.41/0.70    inference(cnf_transformation,[],[f26])).
% 2.41/0.70  fof(f26,plain,(
% 2.41/0.70    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.41/0.70    inference(ennf_transformation,[],[f6])).
% 2.41/0.70  fof(f6,axiom,(
% 2.41/0.70    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 2.41/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 2.41/0.70  fof(f1355,plain,(
% 2.41/0.70    ~r1_tarski(k10_relat_1(sK2,sK1),k1_relat_1(sK2))),
% 2.41/0.70    inference(subsumption_resolution,[],[f1354,f1154])).
% 2.41/0.70  fof(f1154,plain,(
% 2.41/0.70    k1_relat_1(sK2) != k10_relat_1(sK2,sK1)),
% 2.41/0.70    inference(superposition,[],[f1056,f1152])).
% 2.41/0.70  fof(f1152,plain,(
% 2.41/0.70    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(sK0,sK1,sK2,X0)) )),
% 2.41/0.70    inference(resolution,[],[f84,f54])).
% 2.41/0.70  fof(f84,plain,(
% 2.41/0.70    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 2.41/0.70    inference(cnf_transformation,[],[f45])).
% 2.41/0.70  fof(f45,plain,(
% 2.41/0.70    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.41/0.70    inference(ennf_transformation,[],[f21])).
% 2.41/0.70  fof(f21,axiom,(
% 2.41/0.70    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 2.41/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 2.41/0.70  fof(f1056,plain,(
% 2.41/0.70    k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2)),
% 2.41/0.70    inference(subsumption_resolution,[],[f1055,f260])).
% 2.41/0.70  fof(f260,plain,(
% 2.41/0.70    k2_relat_1(sK2) = k9_relat_1(sK2,sK0)),
% 2.41/0.70    inference(superposition,[],[f236,f259])).
% 2.41/0.70  fof(f259,plain,(
% 2.41/0.70    sK2 = k7_relat_1(sK2,sK0)),
% 2.41/0.70    inference(subsumption_resolution,[],[f252,f92])).
% 2.41/0.70  fof(f252,plain,(
% 2.41/0.70    sK2 = k7_relat_1(sK2,sK0) | ~v1_relat_1(sK2)),
% 2.41/0.70    inference(resolution,[],[f71,f106])).
% 2.41/0.70  fof(f106,plain,(
% 2.41/0.70    v4_relat_1(sK2,sK0)),
% 2.41/0.70    inference(resolution,[],[f80,f54])).
% 2.41/0.70  fof(f80,plain,(
% 2.41/0.70    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.41/0.70    inference(cnf_transformation,[],[f41])).
% 2.41/0.70  fof(f41,plain,(
% 2.41/0.70    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.41/0.70    inference(ennf_transformation,[],[f17])).
% 2.41/0.70  fof(f17,axiom,(
% 2.41/0.70    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.41/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.41/0.70  fof(f71,plain,(
% 2.41/0.70    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 2.41/0.70    inference(cnf_transformation,[],[f37])).
% 2.41/0.70  fof(f37,plain,(
% 2.41/0.70    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.41/0.70    inference(flattening,[],[f36])).
% 2.41/0.70  fof(f36,plain,(
% 2.41/0.70    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.41/0.70    inference(ennf_transformation,[],[f8])).
% 2.41/0.70  fof(f8,axiom,(
% 2.41/0.70    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.41/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 2.41/0.70  fof(f236,plain,(
% 2.41/0.70    ( ! [X40] : (k2_relat_1(k7_relat_1(sK2,X40)) = k9_relat_1(sK2,X40)) )),
% 2.41/0.70    inference(resolution,[],[f65,f92])).
% 2.41/0.70  fof(f65,plain,(
% 2.41/0.70    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 2.41/0.70    inference(cnf_transformation,[],[f29])).
% 2.41/0.70  fof(f29,plain,(
% 2.41/0.70    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.41/0.70    inference(ennf_transformation,[],[f5])).
% 2.41/0.70  fof(f5,axiom,(
% 2.41/0.70    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.41/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 2.41/0.70  fof(f1055,plain,(
% 2.41/0.70    k2_relat_1(sK2) != k9_relat_1(sK2,sK0) | k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2)),
% 2.41/0.70    inference(backward_demodulation,[],[f939,f1053])).
% 2.41/0.70  fof(f1053,plain,(
% 2.41/0.70    ( ! [X0] : (k9_relat_1(sK2,X0) = k7_relset_1(sK0,sK1,sK2,X0)) )),
% 2.41/0.70    inference(resolution,[],[f83,f54])).
% 2.41/0.70  fof(f83,plain,(
% 2.41/0.70    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 2.41/0.70    inference(cnf_transformation,[],[f44])).
% 2.41/0.70  fof(f44,plain,(
% 2.41/0.70    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.41/0.70    inference(ennf_transformation,[],[f20])).
% 2.41/0.70  fof(f20,axiom,(
% 2.41/0.70    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 2.41/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 2.41/0.70  fof(f939,plain,(
% 2.41/0.70    k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2) | k7_relset_1(sK0,sK1,sK2,sK0) != k2_relat_1(sK2)),
% 2.41/0.70    inference(backward_demodulation,[],[f803,f937])).
% 2.41/0.70  fof(f937,plain,(
% 2.41/0.70    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 2.41/0.70    inference(resolution,[],[f79,f54])).
% 2.41/0.70  fof(f79,plain,(
% 2.41/0.70    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 2.41/0.70    inference(cnf_transformation,[],[f40])).
% 2.41/0.70  fof(f40,plain,(
% 2.41/0.70    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.41/0.70    inference(ennf_transformation,[],[f18])).
% 2.41/0.70  fof(f18,axiom,(
% 2.41/0.70    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.41/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.41/0.70  fof(f803,plain,(
% 2.41/0.70    k7_relset_1(sK0,sK1,sK2,sK0) != k2_relat_1(sK2) | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)),
% 2.41/0.70    inference(backward_demodulation,[],[f55,f801])).
% 2.41/0.70  fof(f801,plain,(
% 2.41/0.70    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 2.41/0.70    inference(resolution,[],[f78,f54])).
% 2.41/0.70  fof(f78,plain,(
% 2.41/0.70    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 2.41/0.70    inference(cnf_transformation,[],[f39])).
% 2.41/0.70  fof(f39,plain,(
% 2.41/0.70    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.41/0.70    inference(ennf_transformation,[],[f19])).
% 2.41/0.70  fof(f19,axiom,(
% 2.41/0.70    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.41/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.41/0.70  fof(f55,plain,(
% 2.41/0.70    k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)),
% 2.41/0.70    inference(cnf_transformation,[],[f49])).
% 2.41/0.70  fof(f1354,plain,(
% 2.41/0.70    ~r1_tarski(k10_relat_1(sK2,sK1),k1_relat_1(sK2)) | k1_relat_1(sK2) = k10_relat_1(sK2,sK1)),
% 2.41/0.70    inference(resolution,[],[f1348,f74])).
% 2.41/0.70  fof(f74,plain,(
% 2.41/0.70    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 2.41/0.70    inference(cnf_transformation,[],[f52])).
% 2.41/0.70  fof(f52,plain,(
% 2.41/0.70    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.41/0.70    inference(flattening,[],[f51])).
% 2.41/0.70  fof(f51,plain,(
% 2.41/0.70    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.41/0.70    inference(nnf_transformation,[],[f1])).
% 2.41/0.70  fof(f1,axiom,(
% 2.41/0.70    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.41/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.41/0.70  fof(f1348,plain,(
% 2.41/0.70    r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,sK1))),
% 2.41/0.70    inference(forward_demodulation,[],[f1347,f557])).
% 2.41/0.70  fof(f557,plain,(
% 2.41/0.70    k10_relat_1(sK2,k2_relat_1(sK2)) = k10_relat_1(sK2,sK1)),
% 2.41/0.70    inference(superposition,[],[f488,f548])).
% 2.41/0.70  fof(f548,plain,(
% 2.41/0.70    k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),sK1)),
% 2.41/0.70    inference(forward_demodulation,[],[f538,f59])).
% 2.41/0.70  fof(f59,plain,(
% 2.41/0.70    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.41/0.70    inference(cnf_transformation,[],[f10])).
% 2.41/0.70  fof(f10,axiom,(
% 2.41/0.70    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.41/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 2.41/0.70  fof(f538,plain,(
% 2.41/0.70    k3_xboole_0(k2_relat_1(sK2),sK1) = k1_relat_1(k6_relat_1(k2_relat_1(sK2)))),
% 2.41/0.70    inference(superposition,[],[f170,f515])).
% 2.41/0.70  fof(f515,plain,(
% 2.41/0.70    k6_relat_1(k2_relat_1(sK2)) = k7_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1)),
% 2.41/0.70    inference(resolution,[],[f347,f111])).
% 2.41/0.70  fof(f111,plain,(
% 2.41/0.70    r1_tarski(k2_relat_1(sK2),sK1)),
% 2.41/0.70    inference(subsumption_resolution,[],[f110,f92])).
% 2.41/0.70  fof(f110,plain,(
% 2.41/0.70    r1_tarski(k2_relat_1(sK2),sK1) | ~v1_relat_1(sK2)),
% 2.41/0.70    inference(resolution,[],[f108,f68])).
% 2.41/0.70  fof(f68,plain,(
% 2.41/0.70    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.41/0.70    inference(cnf_transformation,[],[f50])).
% 2.41/0.70  fof(f50,plain,(
% 2.41/0.70    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.41/0.70    inference(nnf_transformation,[],[f33])).
% 2.41/0.70  fof(f33,plain,(
% 2.41/0.70    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.41/0.70    inference(ennf_transformation,[],[f4])).
% 2.41/0.70  fof(f4,axiom,(
% 2.41/0.70    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.41/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 2.41/0.70  fof(f108,plain,(
% 2.41/0.70    v5_relat_1(sK2,sK1)),
% 2.41/0.70    inference(resolution,[],[f81,f54])).
% 2.41/0.70  fof(f81,plain,(
% 2.41/0.70    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 2.41/0.70    inference(cnf_transformation,[],[f41])).
% 2.41/0.70  fof(f347,plain,(
% 2.41/0.70    ( ! [X4,X3] : (~r1_tarski(X3,X4) | k6_relat_1(X3) = k7_relat_1(k6_relat_1(X3),X4)) )),
% 2.41/0.70    inference(subsumption_resolution,[],[f344,f56])).
% 2.41/0.70  fof(f56,plain,(
% 2.41/0.70    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.41/0.70    inference(cnf_transformation,[],[f13])).
% 2.41/0.70  fof(f13,axiom,(
% 2.41/0.70    ! [X0] : (v5_relat_1(k6_relat_1(X0),X0) & v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 2.41/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).
% 2.41/0.70  fof(f344,plain,(
% 2.41/0.70    ( ! [X4,X3] : (~r1_tarski(X3,X4) | k6_relat_1(X3) = k7_relat_1(k6_relat_1(X3),X4) | ~v1_relat_1(k6_relat_1(X3))) )),
% 2.41/0.70    inference(resolution,[],[f339,f71])).
% 2.41/0.70  fof(f339,plain,(
% 2.41/0.70    ( ! [X19,X20] : (v4_relat_1(k6_relat_1(X19),X20) | ~r1_tarski(X19,X20)) )),
% 2.41/0.70    inference(subsumption_resolution,[],[f331,f56])).
% 2.41/0.70  fof(f331,plain,(
% 2.41/0.70    ( ! [X19,X20] : (v4_relat_1(k6_relat_1(X19),X20) | ~v1_relat_1(k6_relat_1(X19)) | ~r1_tarski(X19,X20)) )),
% 2.41/0.70    inference(resolution,[],[f70,f57])).
% 2.41/0.70  fof(f57,plain,(
% 2.41/0.70    ( ! [X0] : (v4_relat_1(k6_relat_1(X0),X0)) )),
% 2.41/0.70    inference(cnf_transformation,[],[f13])).
% 2.41/0.70  fof(f70,plain,(
% 2.41/0.70    ( ! [X2,X0,X1] : (~v4_relat_1(X2,X0) | v4_relat_1(X2,X1) | ~v1_relat_1(X2) | ~r1_tarski(X0,X1)) )),
% 2.41/0.70    inference(cnf_transformation,[],[f35])).
% 2.41/0.70  fof(f35,plain,(
% 2.41/0.70    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~r1_tarski(X0,X1))),
% 2.41/0.70    inference(flattening,[],[f34])).
% 2.41/0.70  fof(f34,plain,(
% 2.41/0.70    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | (~v4_relat_1(X2,X0) | ~v1_relat_1(X2))) | ~r1_tarski(X0,X1))),
% 2.41/0.70    inference(ennf_transformation,[],[f9])).
% 2.41/0.70  fof(f9,axiom,(
% 2.41/0.70    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v4_relat_1(X2,X0) & v1_relat_1(X2)) => v4_relat_1(X2,X1)))),
% 2.41/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t217_relat_1)).
% 2.41/0.70  fof(f170,plain,(
% 2.41/0.70    ( ! [X6,X7] : (k3_xboole_0(X6,X7) = k1_relat_1(k7_relat_1(k6_relat_1(X6),X7))) )),
% 2.41/0.70    inference(superposition,[],[f59,f166])).
% 2.41/0.70  fof(f166,plain,(
% 2.41/0.70    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 2.41/0.70    inference(backward_demodulation,[],[f61,f163])).
% 2.41/0.70  fof(f163,plain,(
% 2.41/0.70    ( ! [X12,X13] : (k7_relat_1(k6_relat_1(X12),X13) = k5_relat_1(k6_relat_1(X13),k6_relat_1(X12))) )),
% 2.41/0.70    inference(resolution,[],[f64,f56])).
% 2.41/0.70  fof(f64,plain,(
% 2.41/0.70    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 2.41/0.70    inference(cnf_transformation,[],[f28])).
% 2.41/0.70  fof(f28,plain,(
% 2.41/0.70    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 2.41/0.70    inference(ennf_transformation,[],[f12])).
% 2.41/0.70  fof(f12,axiom,(
% 2.41/0.70    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 2.41/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 2.41/0.70  fof(f61,plain,(
% 2.41/0.70    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 2.41/0.70    inference(cnf_transformation,[],[f15])).
% 2.41/0.70  fof(f15,axiom,(
% 2.41/0.70    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 2.41/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 2.41/0.70  fof(f488,plain,(
% 2.41/0.70    ( ! [X64] : (k10_relat_1(sK2,X64) = k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X64))) )),
% 2.41/0.70    inference(resolution,[],[f66,f92])).
% 2.41/0.70  fof(f66,plain,(
% 2.41/0.70    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))) )),
% 2.41/0.70    inference(cnf_transformation,[],[f30])).
% 2.41/0.70  fof(f30,plain,(
% 2.41/0.70    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.41/0.70    inference(ennf_transformation,[],[f7])).
% 2.41/0.70  fof(f7,axiom,(
% 2.41/0.70    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 2.41/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).
% 2.41/0.70  fof(f1347,plain,(
% 2.41/0.70    r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2)))),
% 2.41/0.70    inference(subsumption_resolution,[],[f1346,f92])).
% 2.41/0.70  fof(f1346,plain,(
% 2.41/0.70    r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2))) | ~v1_relat_1(sK2)),
% 2.41/0.70    inference(subsumption_resolution,[],[f1345,f86])).
% 2.41/0.70  fof(f86,plain,(
% 2.41/0.70    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.41/0.70    inference(equality_resolution,[],[f73])).
% 2.41/0.70  fof(f73,plain,(
% 2.41/0.70    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.41/0.70    inference(cnf_transformation,[],[f52])).
% 2.41/0.70  fof(f1345,plain,(
% 2.41/0.70    r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2))) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 2.41/0.70    inference(superposition,[],[f67,f1329])).
% 2.41/0.70  fof(f1329,plain,(
% 2.41/0.70    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))),
% 2.41/0.70    inference(superposition,[],[f236,f1315])).
% 2.41/0.70  fof(f1315,plain,(
% 2.41/0.70    sK2 = k7_relat_1(sK2,k1_relat_1(sK2))),
% 2.41/0.70    inference(subsumption_resolution,[],[f1313,f92])).
% 2.41/0.70  fof(f1313,plain,(
% 2.41/0.70    sK2 = k7_relat_1(sK2,k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 2.41/0.70    inference(resolution,[],[f1306,f71])).
% 2.41/0.70  fof(f1306,plain,(
% 2.41/0.70    v4_relat_1(sK2,k1_relat_1(sK2))),
% 2.41/0.70    inference(resolution,[],[f1300,f80])).
% 2.41/0.70  fof(f1300,plain,(
% 2.41/0.70    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))),
% 2.41/0.70    inference(resolution,[],[f1271,f86])).
% 2.41/0.70  fof(f1271,plain,(
% 2.41/0.70    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) )),
% 2.41/0.70    inference(resolution,[],[f85,f54])).
% 2.41/0.70  fof(f85,plain,(
% 2.41/0.70    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 2.41/0.70    inference(cnf_transformation,[],[f47])).
% 2.41/0.70  fof(f47,plain,(
% 2.41/0.70    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 2.41/0.70    inference(flattening,[],[f46])).
% 2.41/0.70  fof(f46,plain,(
% 2.41/0.70    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 2.41/0.70    inference(ennf_transformation,[],[f22])).
% 2.41/0.70  fof(f22,axiom,(
% 2.41/0.70    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 2.41/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).
% 2.41/0.70  fof(f67,plain,(
% 2.41/0.70    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.41/0.70    inference(cnf_transformation,[],[f32])).
% 2.41/0.70  fof(f32,plain,(
% 2.41/0.70    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.41/0.70    inference(flattening,[],[f31])).
% 2.41/0.70  fof(f31,plain,(
% 2.41/0.70    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.41/0.70    inference(ennf_transformation,[],[f14])).
% 2.41/0.70  fof(f14,axiom,(
% 2.41/0.70    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 2.41/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 2.41/0.70  % SZS output end Proof for theBenchmark
% 2.41/0.70  % (13938)------------------------------
% 2.41/0.70  % (13938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.41/0.70  % (13938)Termination reason: Refutation
% 2.41/0.70  
% 2.41/0.70  % (13938)Memory used [KB]: 7931
% 2.41/0.70  % (13938)Time elapsed: 0.268 s
% 2.41/0.70  % (13938)------------------------------
% 2.41/0.70  % (13938)------------------------------
% 2.41/0.70  % (13934)Success in time 0.328 s
%------------------------------------------------------------------------------
