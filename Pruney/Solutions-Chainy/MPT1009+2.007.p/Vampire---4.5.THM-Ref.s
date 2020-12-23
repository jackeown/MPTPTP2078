%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:26 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 334 expanded)
%              Number of leaves         :   18 (  74 expanded)
%              Depth                    :   24
%              Number of atoms          :  261 (1096 expanded)
%              Number of equality atoms :   78 ( 261 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f592,plain,(
    $false ),
    inference(subsumption_resolution,[],[f591,f251])).

fof(f251,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3)) ),
    inference(resolution,[],[f250,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f250,plain,(
    ! [X0] : m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(k2_relat_1(sK3))) ),
    inference(subsumption_resolution,[],[f247,f106])).

fof(f106,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f247,plain,(
    ! [X0] :
      ( m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(k2_relat_1(sK3)))
      | ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3)) ) ),
    inference(resolution,[],[f212,f113])).

fof(f113,plain,(
    ! [X1] :
      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),X1)))
      | ~ r1_tarski(k2_relat_1(sK3),X1) ) ),
    inference(resolution,[],[f69,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

fof(f69,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f34,f56])).

fof(f56,plain,
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

fof(f34,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f30])).

fof(f30,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f29])).

fof(f29,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

fof(f212,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_relat_1(sK3))))
      | m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(k2_relat_1(sK3))) ) ),
    inference(superposition,[],[f88,f204])).

fof(f204,plain,(
    ! [X0] : k9_relat_1(sK3,X0) = k7_relset_1(k1_tarski(sK0),k2_relat_1(sK3),sK3,X0) ),
    inference(resolution,[],[f147,f106])).

fof(f147,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(k2_relat_1(sK3),X3)
      | k9_relat_1(sK3,X4) = k7_relset_1(k1_tarski(sK0),X3,sK3,X4) ) ),
    inference(resolution,[],[f113,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f591,plain,(
    ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f116,f590])).

fof(f590,plain,(
    k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) ),
    inference(equality_resolution,[],[f528])).

fof(f528,plain,(
    ! [X0] :
      ( k1_tarski(X0) != k1_tarski(sK0)
      | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f527,f110])).

fof(f110,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f69,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f527,plain,(
    ! [X0] :
      ( k1_tarski(X0) != k1_tarski(sK0)
      | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0))
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f524,f68])).

fof(f68,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f524,plain,(
    ! [X0] :
      ( k1_tarski(X0) != k1_tarski(sK0)
      | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0))
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(superposition,[],[f86,f460])).

fof(f460,plain,(
    k1_tarski(sK0) = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f457,f85])).

fof(f85,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f457,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(sK3,sK0)))
    | k1_tarski(sK0) = k1_relat_1(sK3) ),
    inference(superposition,[],[f116,f416])).

fof(f416,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(sK3,X0)
      | k1_tarski(sK0) = k1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f412,f85])).

fof(f412,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k9_relat_1(sK3,X0))
      | k1_xboole_0 = k9_relat_1(sK3,X0)
      | k1_tarski(sK0) = k1_relat_1(sK3) ) ),
    inference(superposition,[],[f260,f278])).

fof(f278,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | k1_tarski(sK0) = k1_relat_1(sK3) ),
    inference(superposition,[],[f272,f168])).

fof(f168,plain,(
    k2_relat_1(sK3) = k11_relat_1(sK3,sK0) ),
    inference(superposition,[],[f161,f118])).

fof(f118,plain,(
    ! [X1] : k11_relat_1(sK3,X1) = k9_relat_1(sK3,k1_tarski(X1)) ),
    inference(resolution,[],[f110,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(f161,plain,(
    k2_relat_1(sK3) = k9_relat_1(sK3,k1_tarski(sK0)) ),
    inference(superposition,[],[f117,f123])).

fof(f123,plain,(
    sK3 = k7_relat_1(sK3,k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f120,f110])).

fof(f120,plain,
    ( sK3 = k7_relat_1(sK3,k1_tarski(sK0))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f109,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f109,plain,(
    v4_relat_1(sK3,k1_tarski(sK0)) ),
    inference(resolution,[],[f69,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f117,plain,(
    ! [X0] : k9_relat_1(sK3,X0) = k2_relat_1(k7_relat_1(sK3,X0)) ),
    inference(resolution,[],[f110,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f272,plain,
    ( k1_xboole_0 = k11_relat_1(sK3,sK0)
    | k1_tarski(sK0) = k1_relat_1(sK3) ),
    inference(resolution,[],[f259,f127])).

fof(f127,plain,
    ( ~ r1_tarski(k1_tarski(sK0),k1_relat_1(sK3))
    | k1_tarski(sK0) = k1_relat_1(sK3) ),
    inference(resolution,[],[f124,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f124,plain,(
    r1_tarski(k1_relat_1(sK3),k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f121,f110])).

fof(f121,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_tarski(sK0))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f109,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f259,plain,(
    ! [X0] :
      ( r1_tarski(k1_tarski(X0),k1_relat_1(sK3))
      | k1_xboole_0 = k11_relat_1(sK3,X0) ) ),
    inference(duplicate_literal_removal,[],[f258])).

fof(f258,plain,(
    ! [X0] :
      ( r1_tarski(k1_tarski(X0),k1_relat_1(sK3))
      | k1_xboole_0 = k11_relat_1(sK3,X0)
      | k1_xboole_0 = k11_relat_1(sK3,X0) ) ),
    inference(superposition,[],[f231,f100])).

fof(f100,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f231,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),k1_relat_1(sK3))
      | k1_xboole_0 = k11_relat_1(sK3,X1)
      | k1_xboole_0 = k11_relat_1(sK3,X0) ) ),
    inference(resolution,[],[f172,f119])).

fof(f119,plain,(
    ! [X2] :
      ( r2_hidden(X2,k1_relat_1(sK3))
      | k1_xboole_0 = k11_relat_1(sK3,X2) ) ),
    inference(resolution,[],[f110,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_xboole_0 = k11_relat_1(X1,X0)
      | r2_hidden(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k1_xboole_0 = k11_relat_1(X1,X0) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(f172,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(sK3))
      | r1_tarski(k2_tarski(X1,X0),k1_relat_1(sK3))
      | k1_xboole_0 = k11_relat_1(sK3,X0) ) ),
    inference(resolution,[],[f119,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f260,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK3),k9_relat_1(sK3,X0))
      | k9_relat_1(sK3,X0) = k2_relat_1(sK3) ) ),
    inference(resolution,[],[f251,f81])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) != k1_relat_1(X1)
      | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f116,plain,(
    ~ r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(backward_demodulation,[],[f71,f112])).

fof(f112,plain,(
    ! [X0] : k7_relset_1(k1_tarski(sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(resolution,[],[f69,f87])).

fof(f71,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f57])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:43:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (5495)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (5494)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (5497)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.52  % (5502)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (5513)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.52  % (5504)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.52  % (5508)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.52  % (5492)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.52  % (5508)Refutation not found, incomplete strategy% (5508)------------------------------
% 0.20/0.52  % (5508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (5508)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (5508)Memory used [KB]: 1791
% 0.20/0.52  % (5508)Time elapsed: 0.109 s
% 0.20/0.52  % (5508)------------------------------
% 0.20/0.52  % (5508)------------------------------
% 0.20/0.52  % (5496)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (5501)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.52  % (5516)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (5512)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  % (5491)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (5505)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.53  % (5491)Refutation not found, incomplete strategy% (5491)------------------------------
% 0.20/0.53  % (5491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (5491)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (5491)Memory used [KB]: 1663
% 0.20/0.53  % (5491)Time elapsed: 0.106 s
% 0.20/0.53  % (5491)------------------------------
% 0.20/0.53  % (5491)------------------------------
% 0.20/0.53  % (5509)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.53  % (5506)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.53  % (5507)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.54  % (5516)Refutation not found, incomplete strategy% (5516)------------------------------
% 0.20/0.54  % (5516)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (5516)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (5516)Memory used [KB]: 6396
% 0.20/0.54  % (5516)Time elapsed: 0.117 s
% 0.20/0.54  % (5516)------------------------------
% 0.20/0.54  % (5516)------------------------------
% 0.20/0.54  % (5519)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (5519)Refutation not found, incomplete strategy% (5519)------------------------------
% 0.20/0.54  % (5519)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (5519)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (5519)Memory used [KB]: 1663
% 0.20/0.54  % (5519)Time elapsed: 0.093 s
% 0.20/0.54  % (5519)------------------------------
% 0.20/0.54  % (5519)------------------------------
% 0.20/0.54  % (5500)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.54  % (5510)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.54  % (5500)Refutation not found, incomplete strategy% (5500)------------------------------
% 0.20/0.54  % (5500)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (5500)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (5500)Memory used [KB]: 10874
% 0.20/0.54  % (5500)Time elapsed: 0.131 s
% 0.20/0.54  % (5500)------------------------------
% 0.20/0.54  % (5500)------------------------------
% 0.20/0.54  % (5514)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (5493)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.30/0.54  % (5503)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.30/0.54  % (5490)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.30/0.54  % (5499)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.30/0.55  % (5517)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.30/0.55  % (5502)Refutation not found, incomplete strategy% (5502)------------------------------
% 1.30/0.55  % (5502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  % (5502)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.55  
% 1.30/0.55  % (5502)Memory used [KB]: 10874
% 1.30/0.55  % (5502)Time elapsed: 0.135 s
% 1.30/0.55  % (5502)------------------------------
% 1.30/0.55  % (5502)------------------------------
% 1.30/0.55  % (5507)Refutation not found, incomplete strategy% (5507)------------------------------
% 1.30/0.55  % (5507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  % (5507)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.55  
% 1.30/0.55  % (5507)Memory used [KB]: 1791
% 1.30/0.55  % (5507)Time elapsed: 0.121 s
% 1.30/0.55  % (5507)------------------------------
% 1.30/0.55  % (5507)------------------------------
% 1.30/0.55  % (5504)Refutation found. Thanks to Tanya!
% 1.30/0.55  % SZS status Theorem for theBenchmark
% 1.30/0.55  % SZS output start Proof for theBenchmark
% 1.30/0.55  fof(f592,plain,(
% 1.30/0.55    $false),
% 1.30/0.55    inference(subsumption_resolution,[],[f591,f251])).
% 1.30/0.55  fof(f251,plain,(
% 1.30/0.55    ( ! [X0] : (r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3))) )),
% 1.30/0.55    inference(resolution,[],[f250,f77])).
% 1.30/0.55  fof(f77,plain,(
% 1.30/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.30/0.55    inference(cnf_transformation,[],[f60])).
% 1.30/0.55  fof(f60,plain,(
% 1.30/0.55    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.30/0.55    inference(nnf_transformation,[],[f12])).
% 1.30/0.55  fof(f12,axiom,(
% 1.30/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.30/0.55  fof(f250,plain,(
% 1.30/0.55    ( ! [X0] : (m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(k2_relat_1(sK3)))) )),
% 1.30/0.55    inference(subsumption_resolution,[],[f247,f106])).
% 1.30/0.55  fof(f106,plain,(
% 1.30/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.30/0.55    inference(equality_resolution,[],[f79])).
% 1.30/0.55  fof(f79,plain,(
% 1.30/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.30/0.55    inference(cnf_transformation,[],[f62])).
% 1.30/0.55  fof(f62,plain,(
% 1.30/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.30/0.55    inference(flattening,[],[f61])).
% 1.30/0.55  fof(f61,plain,(
% 1.30/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.30/0.55    inference(nnf_transformation,[],[f1])).
% 1.30/0.55  fof(f1,axiom,(
% 1.30/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.30/0.55  fof(f247,plain,(
% 1.30/0.55    ( ! [X0] : (m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(k2_relat_1(sK3))) | ~r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3))) )),
% 1.30/0.55    inference(resolution,[],[f212,f113])).
% 1.30/0.55  fof(f113,plain,(
% 1.30/0.55    ( ! [X1] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),X1))) | ~r1_tarski(k2_relat_1(sK3),X1)) )),
% 1.30/0.55    inference(resolution,[],[f69,f73])).
% 1.30/0.55  fof(f73,plain,(
% 1.30/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~r1_tarski(k2_relat_1(X3),X1) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))) )),
% 1.30/0.55    inference(cnf_transformation,[],[f38])).
% 1.30/0.55  fof(f38,plain,(
% 1.30/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 1.30/0.55    inference(flattening,[],[f37])).
% 1.30/0.55  fof(f37,plain,(
% 1.30/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 1.30/0.55    inference(ennf_transformation,[],[f28])).
% 1.30/0.55  fof(f28,axiom,(
% 1.30/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).
% 1.30/0.55  fof(f69,plain,(
% 1.30/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.30/0.55    inference(cnf_transformation,[],[f57])).
% 1.30/0.55  fof(f57,plain,(
% 1.30/0.55    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 1.30/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f34,f56])).
% 1.30/0.55  fof(f56,plain,(
% 1.30/0.55    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 1.30/0.55    introduced(choice_axiom,[])).
% 1.30/0.55  fof(f34,plain,(
% 1.30/0.55    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 1.30/0.55    inference(flattening,[],[f33])).
% 1.30/0.55  fof(f33,plain,(
% 1.30/0.55    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 1.30/0.55    inference(ennf_transformation,[],[f31])).
% 1.30/0.55  fof(f31,plain,(
% 1.30/0.55    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.30/0.55    inference(pure_predicate_removal,[],[f30])).
% 1.30/0.55  fof(f30,negated_conjecture,(
% 1.30/0.55    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.30/0.55    inference(negated_conjecture,[],[f29])).
% 1.30/0.55  fof(f29,conjecture,(
% 1.30/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).
% 1.30/0.55  fof(f212,plain,(
% 1.30/0.55    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_relat_1(sK3)))) | m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(k2_relat_1(sK3)))) )),
% 1.30/0.55    inference(superposition,[],[f88,f204])).
% 1.30/0.55  fof(f204,plain,(
% 1.30/0.55    ( ! [X0] : (k9_relat_1(sK3,X0) = k7_relset_1(k1_tarski(sK0),k2_relat_1(sK3),sK3,X0)) )),
% 1.30/0.55    inference(resolution,[],[f147,f106])).
% 1.30/0.55  fof(f147,plain,(
% 1.30/0.55    ( ! [X4,X3] : (~r1_tarski(k2_relat_1(sK3),X3) | k9_relat_1(sK3,X4) = k7_relset_1(k1_tarski(sK0),X3,sK3,X4)) )),
% 1.30/0.55    inference(resolution,[],[f113,f87])).
% 1.30/0.55  fof(f87,plain,(
% 1.30/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.30/0.55    inference(cnf_transformation,[],[f44])).
% 1.30/0.55  fof(f44,plain,(
% 1.30/0.55    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/0.55    inference(ennf_transformation,[],[f26])).
% 1.30/0.55  fof(f26,axiom,(
% 1.30/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.30/0.55  fof(f88,plain,(
% 1.30/0.55    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.30/0.55    inference(cnf_transformation,[],[f45])).
% 1.30/0.55  fof(f45,plain,(
% 1.30/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/0.55    inference(ennf_transformation,[],[f24])).
% 1.30/0.55  fof(f24,axiom,(
% 1.30/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).
% 1.30/0.55  fof(f591,plain,(
% 1.30/0.55    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))),
% 1.30/0.55    inference(backward_demodulation,[],[f116,f590])).
% 1.30/0.55  fof(f590,plain,(
% 1.30/0.55    k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)),
% 1.30/0.55    inference(equality_resolution,[],[f528])).
% 1.30/0.55  fof(f528,plain,(
% 1.30/0.55    ( ! [X0] : (k1_tarski(X0) != k1_tarski(sK0) | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0))) )),
% 1.30/0.55    inference(subsumption_resolution,[],[f527,f110])).
% 1.30/0.55  fof(f110,plain,(
% 1.30/0.55    v1_relat_1(sK3)),
% 1.30/0.55    inference(resolution,[],[f69,f98])).
% 1.30/0.55  fof(f98,plain,(
% 1.30/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.30/0.55    inference(cnf_transformation,[],[f50])).
% 1.30/0.55  fof(f50,plain,(
% 1.30/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/0.55    inference(ennf_transformation,[],[f21])).
% 1.30/0.55  fof(f21,axiom,(
% 1.30/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.30/0.55  fof(f527,plain,(
% 1.30/0.55    ( ! [X0] : (k1_tarski(X0) != k1_tarski(sK0) | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0)) | ~v1_relat_1(sK3)) )),
% 1.30/0.55    inference(subsumption_resolution,[],[f524,f68])).
% 1.30/0.55  fof(f68,plain,(
% 1.30/0.55    v1_funct_1(sK3)),
% 1.30/0.55    inference(cnf_transformation,[],[f57])).
% 1.30/0.55  fof(f524,plain,(
% 1.30/0.55    ( ! [X0] : (k1_tarski(X0) != k1_tarski(sK0) | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 1.30/0.55    inference(superposition,[],[f86,f460])).
% 1.30/0.55  fof(f460,plain,(
% 1.30/0.55    k1_tarski(sK0) = k1_relat_1(sK3)),
% 1.30/0.55    inference(subsumption_resolution,[],[f457,f85])).
% 1.30/0.55  fof(f85,plain,(
% 1.30/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.30/0.55    inference(cnf_transformation,[],[f2])).
% 1.30/0.55  fof(f2,axiom,(
% 1.30/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.30/0.55  fof(f457,plain,(
% 1.30/0.55    ~r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(sK3,sK0))) | k1_tarski(sK0) = k1_relat_1(sK3)),
% 1.30/0.55    inference(superposition,[],[f116,f416])).
% 1.30/0.55  fof(f416,plain,(
% 1.30/0.55    ( ! [X0] : (k1_xboole_0 = k9_relat_1(sK3,X0) | k1_tarski(sK0) = k1_relat_1(sK3)) )),
% 1.30/0.55    inference(subsumption_resolution,[],[f412,f85])).
% 1.30/0.55  fof(f412,plain,(
% 1.30/0.55    ( ! [X0] : (~r1_tarski(k1_xboole_0,k9_relat_1(sK3,X0)) | k1_xboole_0 = k9_relat_1(sK3,X0) | k1_tarski(sK0) = k1_relat_1(sK3)) )),
% 1.30/0.55    inference(superposition,[],[f260,f278])).
% 1.30/0.55  fof(f278,plain,(
% 1.30/0.55    k1_xboole_0 = k2_relat_1(sK3) | k1_tarski(sK0) = k1_relat_1(sK3)),
% 1.30/0.55    inference(superposition,[],[f272,f168])).
% 1.30/0.55  fof(f168,plain,(
% 1.30/0.55    k2_relat_1(sK3) = k11_relat_1(sK3,sK0)),
% 1.30/0.55    inference(superposition,[],[f161,f118])).
% 1.30/0.55  fof(f118,plain,(
% 1.30/0.55    ( ! [X1] : (k11_relat_1(sK3,X1) = k9_relat_1(sK3,k1_tarski(X1))) )),
% 1.30/0.55    inference(resolution,[],[f110,f99])).
% 1.30/0.55  fof(f99,plain,(
% 1.30/0.55    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))) )),
% 1.30/0.55    inference(cnf_transformation,[],[f51])).
% 1.30/0.55  fof(f51,plain,(
% 1.30/0.55    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 1.30/0.55    inference(ennf_transformation,[],[f13])).
% 1.30/0.55  fof(f13,axiom,(
% 1.30/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).
% 1.30/0.55  fof(f161,plain,(
% 1.30/0.55    k2_relat_1(sK3) = k9_relat_1(sK3,k1_tarski(sK0))),
% 1.30/0.55    inference(superposition,[],[f117,f123])).
% 1.30/0.55  fof(f123,plain,(
% 1.30/0.55    sK3 = k7_relat_1(sK3,k1_tarski(sK0))),
% 1.30/0.55    inference(subsumption_resolution,[],[f120,f110])).
% 1.30/0.55  fof(f120,plain,(
% 1.30/0.55    sK3 = k7_relat_1(sK3,k1_tarski(sK0)) | ~v1_relat_1(sK3)),
% 1.30/0.55    inference(resolution,[],[f109,f104])).
% 1.30/0.55  fof(f104,plain,(
% 1.30/0.55    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 1.30/0.55    inference(cnf_transformation,[],[f55])).
% 1.30/0.55  fof(f55,plain,(
% 1.30/0.55    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.30/0.55    inference(flattening,[],[f54])).
% 1.30/0.55  fof(f54,plain,(
% 1.30/0.55    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.30/0.55    inference(ennf_transformation,[],[f17])).
% 1.30/0.55  fof(f17,axiom,(
% 1.30/0.55    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 1.30/0.55  fof(f109,plain,(
% 1.30/0.55    v4_relat_1(sK3,k1_tarski(sK0))),
% 1.30/0.55    inference(resolution,[],[f69,f103])).
% 1.30/0.55  fof(f103,plain,(
% 1.30/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.30/0.55    inference(cnf_transformation,[],[f53])).
% 1.30/0.55  fof(f53,plain,(
% 1.30/0.55    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/0.55    inference(ennf_transformation,[],[f32])).
% 1.30/0.55  fof(f32,plain,(
% 1.30/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.30/0.55    inference(pure_predicate_removal,[],[f22])).
% 1.30/0.55  fof(f22,axiom,(
% 1.30/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.30/0.55  fof(f117,plain,(
% 1.30/0.55    ( ! [X0] : (k9_relat_1(sK3,X0) = k2_relat_1(k7_relat_1(sK3,X0))) )),
% 1.30/0.55    inference(resolution,[],[f110,f101])).
% 1.30/0.55  fof(f101,plain,(
% 1.30/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.30/0.55    inference(cnf_transformation,[],[f52])).
% 1.30/0.55  fof(f52,plain,(
% 1.30/0.55    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.30/0.55    inference(ennf_transformation,[],[f15])).
% 1.30/0.55  fof(f15,axiom,(
% 1.30/0.55    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.30/0.55  fof(f272,plain,(
% 1.30/0.55    k1_xboole_0 = k11_relat_1(sK3,sK0) | k1_tarski(sK0) = k1_relat_1(sK3)),
% 1.30/0.55    inference(resolution,[],[f259,f127])).
% 1.30/0.55  fof(f127,plain,(
% 1.30/0.55    ~r1_tarski(k1_tarski(sK0),k1_relat_1(sK3)) | k1_tarski(sK0) = k1_relat_1(sK3)),
% 1.30/0.55    inference(resolution,[],[f124,f81])).
% 1.30/0.55  fof(f81,plain,(
% 1.30/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.30/0.55    inference(cnf_transformation,[],[f62])).
% 1.30/0.55  fof(f124,plain,(
% 1.30/0.55    r1_tarski(k1_relat_1(sK3),k1_tarski(sK0))),
% 1.30/0.55    inference(subsumption_resolution,[],[f121,f110])).
% 1.30/0.55  fof(f121,plain,(
% 1.30/0.55    r1_tarski(k1_relat_1(sK3),k1_tarski(sK0)) | ~v1_relat_1(sK3)),
% 1.30/0.55    inference(resolution,[],[f109,f83])).
% 1.30/0.55  fof(f83,plain,(
% 1.30/0.55    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.30/0.55    inference(cnf_transformation,[],[f63])).
% 1.30/0.55  fof(f63,plain,(
% 1.30/0.55    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.30/0.55    inference(nnf_transformation,[],[f41])).
% 1.30/0.55  fof(f41,plain,(
% 1.30/0.55    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.30/0.55    inference(ennf_transformation,[],[f14])).
% 1.30/0.55  fof(f14,axiom,(
% 1.30/0.55    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.30/0.55  fof(f259,plain,(
% 1.30/0.55    ( ! [X0] : (r1_tarski(k1_tarski(X0),k1_relat_1(sK3)) | k1_xboole_0 = k11_relat_1(sK3,X0)) )),
% 1.30/0.55    inference(duplicate_literal_removal,[],[f258])).
% 1.30/0.55  fof(f258,plain,(
% 1.30/0.55    ( ! [X0] : (r1_tarski(k1_tarski(X0),k1_relat_1(sK3)) | k1_xboole_0 = k11_relat_1(sK3,X0) | k1_xboole_0 = k11_relat_1(sK3,X0)) )),
% 1.30/0.55    inference(superposition,[],[f231,f100])).
% 1.30/0.55  fof(f100,plain,(
% 1.30/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.30/0.55    inference(cnf_transformation,[],[f3])).
% 1.30/0.55  fof(f3,axiom,(
% 1.30/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.30/0.55  fof(f231,plain,(
% 1.30/0.55    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X1),k1_relat_1(sK3)) | k1_xboole_0 = k11_relat_1(sK3,X1) | k1_xboole_0 = k11_relat_1(sK3,X0)) )),
% 1.30/0.55    inference(resolution,[],[f172,f119])).
% 1.30/0.55  fof(f119,plain,(
% 1.30/0.55    ( ! [X2] : (r2_hidden(X2,k1_relat_1(sK3)) | k1_xboole_0 = k11_relat_1(sK3,X2)) )),
% 1.30/0.55    inference(resolution,[],[f110,f95])).
% 1.30/0.55  fof(f95,plain,(
% 1.30/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_xboole_0 = k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) )),
% 1.30/0.55    inference(cnf_transformation,[],[f67])).
% 1.30/0.55  fof(f67,plain,(
% 1.30/0.55    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 1.30/0.55    inference(nnf_transformation,[],[f47])).
% 1.30/0.55  fof(f47,plain,(
% 1.30/0.55    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.30/0.55    inference(ennf_transformation,[],[f16])).
% 1.30/0.55  fof(f16,axiom,(
% 1.30/0.55    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).
% 1.30/0.55  fof(f172,plain,(
% 1.30/0.55    ( ! [X0,X1] : (~r2_hidden(X1,k1_relat_1(sK3)) | r1_tarski(k2_tarski(X1,X0),k1_relat_1(sK3)) | k1_xboole_0 = k11_relat_1(sK3,X0)) )),
% 1.30/0.55    inference(resolution,[],[f119,f76])).
% 1.30/0.55  fof(f76,plain,(
% 1.30/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 1.30/0.55    inference(cnf_transformation,[],[f59])).
% 1.30/0.55  fof(f59,plain,(
% 1.30/0.55    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.30/0.55    inference(flattening,[],[f58])).
% 1.30/0.55  fof(f58,plain,(
% 1.30/0.55    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.30/0.55    inference(nnf_transformation,[],[f11])).
% 1.30/0.55  fof(f11,axiom,(
% 1.30/0.55    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.30/0.55  fof(f260,plain,(
% 1.30/0.55    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),k9_relat_1(sK3,X0)) | k9_relat_1(sK3,X0) = k2_relat_1(sK3)) )),
% 1.30/0.55    inference(resolution,[],[f251,f81])).
% 1.30/0.55  fof(f86,plain,(
% 1.30/0.55    ( ! [X0,X1] : (k1_tarski(X0) != k1_relat_1(X1) | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.30/0.55    inference(cnf_transformation,[],[f43])).
% 1.30/0.55  fof(f43,plain,(
% 1.30/0.55    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.30/0.55    inference(flattening,[],[f42])).
% 1.30/0.55  fof(f42,plain,(
% 1.30/0.55    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.30/0.55    inference(ennf_transformation,[],[f20])).
% 1.30/0.55  fof(f20,axiom,(
% 1.30/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 1.30/0.55  fof(f116,plain,(
% 1.30/0.55    ~r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.30/0.55    inference(backward_demodulation,[],[f71,f112])).
% 1.30/0.55  fof(f112,plain,(
% 1.30/0.55    ( ! [X0] : (k7_relset_1(k1_tarski(sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0)) )),
% 1.30/0.55    inference(resolution,[],[f69,f87])).
% 1.30/0.55  fof(f71,plain,(
% 1.30/0.55    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.30/0.55    inference(cnf_transformation,[],[f57])).
% 1.30/0.55  % SZS output end Proof for theBenchmark
% 1.30/0.55  % (5504)------------------------------
% 1.30/0.55  % (5504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  % (5504)Termination reason: Refutation
% 1.30/0.55  
% 1.30/0.55  % (5504)Memory used [KB]: 1918
% 1.30/0.55  % (5504)Time elapsed: 0.109 s
% 1.30/0.55  % (5504)------------------------------
% 1.30/0.55  % (5504)------------------------------
% 1.30/0.55  % (5489)Success in time 0.182 s
%------------------------------------------------------------------------------
