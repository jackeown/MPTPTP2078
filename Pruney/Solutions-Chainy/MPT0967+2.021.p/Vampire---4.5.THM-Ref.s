%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:45 EST 2020

% Result     : Theorem 1.77s
% Output     : Refutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :  116 (1099 expanded)
%              Number of leaves         :   17 ( 246 expanded)
%              Depth                    :   31
%              Number of atoms          :  287 (4437 expanded)
%              Number of equality atoms :   86 (1072 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1636,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1635,f159])).

fof(f159,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f146,f157])).

fof(f157,plain,(
    ! [X6] : k1_xboole_0 = sK7(X6,k1_xboole_0) ),
    inference(resolution,[],[f149,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f149,plain,(
    ! [X0] : v1_xboole_0(sK7(X0,k1_xboole_0)) ),
    inference(resolution,[],[f146,f124])).

fof(f124,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f61,f54])).

fof(f54,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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

fof(f146,plain,(
    ! [X0] : m1_subset_1(sK7(X0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f82,f98])).

fof(f98,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f82,plain,(
    ! [X0,X1] : m1_subset_1(sK7(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).

fof(f1635,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f1634,f99])).

fof(f99,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f1634,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) ),
    inference(forward_demodulation,[],[f1633,f1630])).

fof(f1630,plain,(
    k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f1629])).

fof(f1629,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f49,f1539])).

fof(f1539,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f1512,f233])).

fof(f233,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,k1_xboole_0)
      | k1_xboole_0 = X3 ) ),
    inference(resolution,[],[f72,f56])).

fof(f56,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1512,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f53,f1511])).

fof(f1511,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f1509,f952])).

fof(f952,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) ),
    inference(resolution,[],[f947,f334])).

fof(f334,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X4))
      | r1_tarski(X3,X4) ) ),
    inference(resolution,[],[f323,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f323,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f311,f96])).

fof(f96,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f311,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f94,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f947,plain,(
    r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(resolution,[],[f942,f53])).

fof(f942,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK1,X1)
      | r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) ) ),
    inference(resolution,[],[f933,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f933,plain,(
    ! [X6] :
      ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),X6)
      | r2_hidden(sK3,k1_zfmisc_1(X6)) ) ),
    inference(resolution,[],[f248,f135])).

fof(f135,plain,(
    r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f133,f55])).

fof(f55,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f133,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f68,f52])).

fof(f52,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X1,X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X1,X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f248,plain,(
    ! [X8,X7,X9] :
      ( ~ r2_hidden(X7,k1_zfmisc_1(X9))
      | r2_hidden(X7,k1_zfmisc_1(X8))
      | ~ r1_tarski(X9,X8) ) ),
    inference(resolution,[],[f73,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f1509,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) ),
    inference(resolution,[],[f1507,f76])).

fof(f1507,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f1506])).

fof(f1506,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f1490,f1180])).

fof(f1180,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f1178,f697])).

fof(f697,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f87,f52])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f1178,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f1174,f52])).

fof(f1174,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f93,f51])).

fof(f51,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
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

fof(f1490,plain,
    ( sK0 != k1_relat_1(sK3)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f1489,f105])).

fof(f105,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f48,f50])).

fof(f50,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f48,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f30])).

fof(f1489,plain,
    ( sK0 != k1_relat_1(sK3)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | v1_funct_2(sK3,sK0,sK2) ),
    inference(superposition,[],[f92,f1476])).

fof(f1476,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3) ),
    inference(resolution,[],[f696,f952])).

fof(f696,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X5,k2_zfmisc_1(X3,X4))
      | k1_relat_1(X5) = k1_relset_1(X3,X4,X5) ) ),
    inference(resolution,[],[f87,f76])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f53,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f49,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f30])).

fof(f1633,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f1631,f194])).

fof(f194,plain,(
    ! [X1] : v1_funct_2(k1_xboole_0,k1_xboole_0,X1) ),
    inference(superposition,[],[f84,f183])).

fof(f183,plain,(
    ! [X6] : k1_xboole_0 = sK7(k1_xboole_0,X6) ),
    inference(resolution,[],[f174,f59])).

fof(f174,plain,(
    ! [X0] : v1_xboole_0(sK7(k1_xboole_0,X0)) ),
    inference(resolution,[],[f147,f124])).

fof(f147,plain,(
    ! [X1] : m1_subset_1(sK7(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f82,f99])).

fof(f84,plain,(
    ! [X0,X1] : v1_funct_2(sK7(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f28])).

fof(f1631,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK2)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(backward_demodulation,[],[f1597,f1630])).

fof(f1597,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(k1_xboole_0,sK0,sK2) ),
    inference(forward_demodulation,[],[f1576,f1574])).

fof(f1574,plain,(
    k1_xboole_0 = sK3 ),
    inference(forward_demodulation,[],[f1573,f98])).

fof(f1573,plain,(
    sK3 = k2_zfmisc_1(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1572,f1539])).

fof(f1572,plain,(
    sK3 = k2_zfmisc_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f1571,f56])).

fof(f1571,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | sK3 = k2_zfmisc_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f1546,f98])).

fof(f1546,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK3)
    | sK3 = k2_zfmisc_1(sK0,sK1) ),
    inference(backward_demodulation,[],[f236,f1539])).

fof(f236,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK3)
    | sK3 = k2_zfmisc_1(sK0,sK1) ),
    inference(resolution,[],[f72,f117])).

fof(f117,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f77,f52])).

fof(f1576,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(backward_demodulation,[],[f105,f1574])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:59:06 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.53  % (23228)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.23/0.53  % (23215)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.53  % (23236)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.23/0.53  % (23219)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.23/0.53  % (23214)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.23/0.53  % (23217)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.23/0.53  % (23216)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.23/0.54  % (23218)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.23/0.54  % (23213)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.23/0.54  % (23241)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.23/0.54  % (23223)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.23/0.54  % (23230)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.23/0.54  % (23220)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.23/0.54  % (23232)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.23/0.55  % (23226)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.55  % (23227)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.23/0.55  % (23222)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.23/0.55  % (23236)Refutation not found, incomplete strategy% (23236)------------------------------
% 0.23/0.55  % (23236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (23236)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (23236)Memory used [KB]: 10874
% 0.23/0.55  % (23236)Time elapsed: 0.072 s
% 0.23/0.55  % (23236)------------------------------
% 0.23/0.55  % (23236)------------------------------
% 0.23/0.55  % (23234)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.23/0.55  % (23238)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.23/0.55  % (23233)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.23/0.55  % (23243)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.23/0.55  % (23221)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.23/0.55  % (23224)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.23/0.55  % (23229)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.23/0.55  % (23215)Refutation not found, incomplete strategy% (23215)------------------------------
% 0.23/0.55  % (23215)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (23215)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (23215)Memory used [KB]: 10746
% 0.23/0.55  % (23215)Time elapsed: 0.116 s
% 0.23/0.55  % (23215)------------------------------
% 0.23/0.55  % (23215)------------------------------
% 0.23/0.56  % (23242)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.23/0.56  % (23221)Refutation not found, incomplete strategy% (23221)------------------------------
% 0.23/0.56  % (23221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (23221)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (23221)Memory used [KB]: 10746
% 0.23/0.56  % (23221)Time elapsed: 0.140 s
% 0.23/0.56  % (23221)------------------------------
% 0.23/0.56  % (23221)------------------------------
% 0.23/0.56  % (23237)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.23/0.56  % (23239)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.23/0.56  % (23235)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.23/0.56  % (23231)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.23/0.57  % (23240)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.77/0.62  % (23219)Refutation found. Thanks to Tanya!
% 1.77/0.62  % SZS status Theorem for theBenchmark
% 1.77/0.62  % SZS output start Proof for theBenchmark
% 1.77/0.62  fof(f1636,plain,(
% 1.77/0.62    $false),
% 1.77/0.62    inference(subsumption_resolution,[],[f1635,f159])).
% 1.77/0.62  fof(f159,plain,(
% 1.77/0.62    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 1.77/0.62    inference(backward_demodulation,[],[f146,f157])).
% 1.77/0.62  fof(f157,plain,(
% 1.77/0.62    ( ! [X6] : (k1_xboole_0 = sK7(X6,k1_xboole_0)) )),
% 1.77/0.62    inference(resolution,[],[f149,f59])).
% 1.77/0.62  fof(f59,plain,(
% 1.77/0.62    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.77/0.62    inference(cnf_transformation,[],[f32])).
% 1.77/0.62  fof(f32,plain,(
% 1.77/0.62    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.77/0.62    inference(ennf_transformation,[],[f4])).
% 1.77/0.62  fof(f4,axiom,(
% 1.77/0.62    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.77/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.77/0.62  fof(f149,plain,(
% 1.77/0.62    ( ! [X0] : (v1_xboole_0(sK7(X0,k1_xboole_0))) )),
% 1.77/0.62    inference(resolution,[],[f146,f124])).
% 1.77/0.62  fof(f124,plain,(
% 1.77/0.62    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0)) )),
% 1.77/0.62    inference(resolution,[],[f61,f54])).
% 1.77/0.62  fof(f54,plain,(
% 1.77/0.62    v1_xboole_0(k1_xboole_0)),
% 1.77/0.62    inference(cnf_transformation,[],[f3])).
% 1.77/0.62  fof(f3,axiom,(
% 1.77/0.62    v1_xboole_0(k1_xboole_0)),
% 1.77/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.77/0.62  fof(f61,plain,(
% 1.77/0.62    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 1.77/0.62    inference(cnf_transformation,[],[f34])).
% 1.77/0.62  fof(f34,plain,(
% 1.77/0.62    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.77/0.62    inference(ennf_transformation,[],[f14])).
% 1.77/0.62  fof(f14,axiom,(
% 1.77/0.62    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.77/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 1.77/0.62  fof(f146,plain,(
% 1.77/0.62    ( ! [X0] : (m1_subset_1(sK7(X0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))) )),
% 1.77/0.62    inference(superposition,[],[f82,f98])).
% 1.77/0.62  fof(f98,plain,(
% 1.77/0.62    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.77/0.62    inference(equality_resolution,[],[f80])).
% 1.77/0.62  fof(f80,plain,(
% 1.77/0.62    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.77/0.62    inference(cnf_transformation,[],[f10])).
% 1.77/0.62  fof(f10,axiom,(
% 1.77/0.62    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.77/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.77/0.62  fof(f82,plain,(
% 1.77/0.62    ( ! [X0,X1] : (m1_subset_1(sK7(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.77/0.62    inference(cnf_transformation,[],[f28])).
% 1.77/0.62  fof(f28,plain,(
% 1.77/0.62    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.77/0.62    inference(pure_predicate_removal,[],[f27])).
% 1.77/0.62  fof(f27,plain,(
% 1.77/0.62    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.77/0.62    inference(pure_predicate_removal,[],[f26])).
% 1.77/0.62  fof(f26,plain,(
% 1.77/0.62    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.77/0.62    inference(pure_predicate_removal,[],[f22])).
% 1.77/0.62  fof(f22,axiom,(
% 1.77/0.62    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.77/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).
% 1.77/0.62  fof(f1635,plain,(
% 1.77/0.62    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 1.77/0.62    inference(forward_demodulation,[],[f1634,f99])).
% 1.77/0.62  fof(f99,plain,(
% 1.77/0.62    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.77/0.62    inference(equality_resolution,[],[f79])).
% 1.77/0.62  fof(f79,plain,(
% 1.77/0.62    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.77/0.62    inference(cnf_transformation,[],[f10])).
% 1.77/0.62  fof(f1634,plain,(
% 1.77/0.62    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))),
% 1.77/0.62    inference(forward_demodulation,[],[f1633,f1630])).
% 1.77/0.62  fof(f1630,plain,(
% 1.77/0.62    k1_xboole_0 = sK0),
% 1.77/0.62    inference(trivial_inequality_removal,[],[f1629])).
% 1.77/0.62  fof(f1629,plain,(
% 1.77/0.62    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0),
% 1.77/0.62    inference(superposition,[],[f49,f1539])).
% 1.77/0.62  fof(f1539,plain,(
% 1.77/0.62    k1_xboole_0 = sK1),
% 1.77/0.62    inference(subsumption_resolution,[],[f1512,f233])).
% 1.77/0.62  fof(f233,plain,(
% 1.77/0.62    ( ! [X3] : (~r1_tarski(X3,k1_xboole_0) | k1_xboole_0 = X3) )),
% 1.77/0.62    inference(resolution,[],[f72,f56])).
% 1.77/0.62  fof(f56,plain,(
% 1.77/0.62    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.77/0.62    inference(cnf_transformation,[],[f7])).
% 1.77/0.62  fof(f7,axiom,(
% 1.77/0.62    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.77/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.77/0.62  fof(f72,plain,(
% 1.77/0.62    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.77/0.62    inference(cnf_transformation,[],[f6])).
% 1.77/0.62  fof(f6,axiom,(
% 1.77/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.77/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.77/0.62  fof(f1512,plain,(
% 1.77/0.62    r1_tarski(sK1,k1_xboole_0) | k1_xboole_0 = sK1),
% 1.77/0.62    inference(superposition,[],[f53,f1511])).
% 1.77/0.62  fof(f1511,plain,(
% 1.77/0.62    k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.77/0.62    inference(subsumption_resolution,[],[f1509,f952])).
% 1.77/0.62  fof(f952,plain,(
% 1.77/0.62    r1_tarski(sK3,k2_zfmisc_1(sK0,sK2))),
% 1.77/0.62    inference(resolution,[],[f947,f334])).
% 1.77/0.62  fof(f334,plain,(
% 1.77/0.62    ( ! [X4,X3] : (~r2_hidden(X3,k1_zfmisc_1(X4)) | r1_tarski(X3,X4)) )),
% 1.77/0.62    inference(resolution,[],[f323,f77])).
% 1.77/0.62  fof(f77,plain,(
% 1.77/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.77/0.62    inference(cnf_transformation,[],[f16])).
% 1.77/0.62  fof(f16,axiom,(
% 1.77/0.62    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.77/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.77/0.62  fof(f323,plain,(
% 1.77/0.62    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.77/0.62    inference(resolution,[],[f311,f96])).
% 1.77/0.62  fof(f96,plain,(
% 1.77/0.62    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.77/0.62    inference(equality_resolution,[],[f71])).
% 1.77/0.62  fof(f71,plain,(
% 1.77/0.62    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.77/0.62    inference(cnf_transformation,[],[f6])).
% 1.77/0.62  fof(f311,plain,(
% 1.77/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.77/0.62    inference(resolution,[],[f94,f76])).
% 1.77/0.62  fof(f76,plain,(
% 1.77/0.62    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.77/0.62    inference(cnf_transformation,[],[f16])).
% 1.77/0.62  fof(f94,plain,(
% 1.77/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 1.77/0.62    inference(cnf_transformation,[],[f47])).
% 1.77/0.62  fof(f47,plain,(
% 1.77/0.62    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.77/0.62    inference(flattening,[],[f46])).
% 1.77/0.62  fof(f46,plain,(
% 1.77/0.62    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.77/0.62    inference(ennf_transformation,[],[f17])).
% 1.77/0.62  fof(f17,axiom,(
% 1.77/0.62    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.77/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 1.77/0.62  fof(f947,plain,(
% 1.77/0.62    r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.77/0.62    inference(resolution,[],[f942,f53])).
% 1.77/0.62  fof(f942,plain,(
% 1.77/0.62    ( ! [X1] : (~r1_tarski(sK1,X1) | r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))) )),
% 1.77/0.62    inference(resolution,[],[f933,f86])).
% 1.77/0.62  fof(f86,plain,(
% 1.77/0.62    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.77/0.62    inference(cnf_transformation,[],[f42])).
% 1.77/0.62  fof(f42,plain,(
% 1.77/0.62    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 1.77/0.62    inference(ennf_transformation,[],[f11])).
% 1.77/0.62  fof(f11,axiom,(
% 1.77/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 1.77/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 1.77/0.62  fof(f933,plain,(
% 1.77/0.62    ( ! [X6] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),X6) | r2_hidden(sK3,k1_zfmisc_1(X6))) )),
% 1.77/0.62    inference(resolution,[],[f248,f135])).
% 1.77/0.62  fof(f135,plain,(
% 1.77/0.62    r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.77/0.62    inference(subsumption_resolution,[],[f133,f55])).
% 1.77/0.62  fof(f55,plain,(
% 1.77/0.62    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.77/0.62    inference(cnf_transformation,[],[f13])).
% 1.77/0.62  fof(f13,axiom,(
% 1.77/0.62    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.77/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.77/0.62  fof(f133,plain,(
% 1.77/0.62    v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.77/0.62    inference(resolution,[],[f68,f52])).
% 1.77/0.62  fof(f52,plain,(
% 1.77/0.62    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.77/0.62    inference(cnf_transformation,[],[f30])).
% 1.77/0.62  fof(f30,plain,(
% 1.77/0.62    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.77/0.62    inference(flattening,[],[f29])).
% 1.77/0.62  fof(f29,plain,(
% 1.77/0.62    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X1,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.77/0.62    inference(ennf_transformation,[],[f24])).
% 1.77/0.62  fof(f24,negated_conjecture,(
% 1.77/0.62    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.77/0.62    inference(negated_conjecture,[],[f23])).
% 1.77/0.62  fof(f23,conjecture,(
% 1.77/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.77/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).
% 1.77/0.62  fof(f68,plain,(
% 1.77/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.77/0.62    inference(cnf_transformation,[],[f38])).
% 1.77/0.62  fof(f38,plain,(
% 1.77/0.62    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.77/0.62    inference(flattening,[],[f37])).
% 1.77/0.62  fof(f37,plain,(
% 1.77/0.62    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.77/0.62    inference(ennf_transformation,[],[f15])).
% 1.77/0.62  fof(f15,axiom,(
% 1.77/0.62    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.77/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.77/0.62  fof(f248,plain,(
% 1.77/0.62    ( ! [X8,X7,X9] : (~r2_hidden(X7,k1_zfmisc_1(X9)) | r2_hidden(X7,k1_zfmisc_1(X8)) | ~r1_tarski(X9,X8)) )),
% 1.77/0.62    inference(resolution,[],[f73,f69])).
% 1.77/0.62  fof(f69,plain,(
% 1.77/0.62    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.77/0.62    inference(cnf_transformation,[],[f39])).
% 1.77/0.62  fof(f39,plain,(
% 1.77/0.62    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 1.77/0.62    inference(ennf_transformation,[],[f12])).
% 1.77/0.62  fof(f12,axiom,(
% 1.77/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 1.77/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).
% 1.77/0.62  fof(f73,plain,(
% 1.77/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.77/0.62    inference(cnf_transformation,[],[f40])).
% 1.77/0.62  fof(f40,plain,(
% 1.77/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.77/0.62    inference(ennf_transformation,[],[f2])).
% 1.77/0.62  fof(f2,axiom,(
% 1.77/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.77/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.77/0.62  fof(f1509,plain,(
% 1.77/0.62    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | ~r1_tarski(sK3,k2_zfmisc_1(sK0,sK2))),
% 1.77/0.62    inference(resolution,[],[f1507,f76])).
% 1.77/0.62  fof(f1507,plain,(
% 1.77/0.62    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.77/0.62    inference(trivial_inequality_removal,[],[f1506])).
% 1.77/0.62  fof(f1506,plain,(
% 1.77/0.62    sK0 != sK0 | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | k1_xboole_0 = sK1),
% 1.77/0.62    inference(superposition,[],[f1490,f1180])).
% 1.77/0.62  fof(f1180,plain,(
% 1.77/0.62    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1),
% 1.77/0.62    inference(superposition,[],[f1178,f697])).
% 1.77/0.62  fof(f697,plain,(
% 1.77/0.62    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 1.77/0.62    inference(resolution,[],[f87,f52])).
% 1.77/0.62  fof(f87,plain,(
% 1.77/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.77/0.62    inference(cnf_transformation,[],[f43])).
% 1.77/0.62  fof(f43,plain,(
% 1.77/0.62    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.77/0.62    inference(ennf_transformation,[],[f20])).
% 1.77/0.62  fof(f20,axiom,(
% 1.77/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.77/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.77/0.62  fof(f1178,plain,(
% 1.77/0.62    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1),
% 1.77/0.62    inference(subsumption_resolution,[],[f1174,f52])).
% 1.77/0.62  fof(f1174,plain,(
% 1.77/0.62    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.77/0.62    inference(resolution,[],[f93,f51])).
% 1.77/0.62  fof(f51,plain,(
% 1.77/0.62    v1_funct_2(sK3,sK0,sK1)),
% 1.77/0.62    inference(cnf_transformation,[],[f30])).
% 1.77/0.62  fof(f93,plain,(
% 1.77/0.62    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.77/0.62    inference(cnf_transformation,[],[f45])).
% 1.77/0.62  fof(f45,plain,(
% 1.77/0.62    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.77/0.62    inference(flattening,[],[f44])).
% 1.77/0.62  fof(f44,plain,(
% 1.77/0.62    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.77/0.62    inference(ennf_transformation,[],[f21])).
% 1.77/0.62  fof(f21,axiom,(
% 1.77/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.77/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.77/0.62  fof(f1490,plain,(
% 1.77/0.62    sK0 != k1_relat_1(sK3) | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.77/0.62    inference(subsumption_resolution,[],[f1489,f105])).
% 1.77/0.62  fof(f105,plain,(
% 1.77/0.62    ~v1_funct_2(sK3,sK0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.77/0.62    inference(subsumption_resolution,[],[f48,f50])).
% 1.77/0.62  fof(f50,plain,(
% 1.77/0.62    v1_funct_1(sK3)),
% 1.77/0.62    inference(cnf_transformation,[],[f30])).
% 1.77/0.62  fof(f48,plain,(
% 1.77/0.62    ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.77/0.62    inference(cnf_transformation,[],[f30])).
% 1.77/0.62  fof(f1489,plain,(
% 1.77/0.62    sK0 != k1_relat_1(sK3) | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | v1_funct_2(sK3,sK0,sK2)),
% 1.77/0.62    inference(superposition,[],[f92,f1476])).
% 1.77/0.62  fof(f1476,plain,(
% 1.77/0.62    k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3)),
% 1.77/0.62    inference(resolution,[],[f696,f952])).
% 1.77/0.62  fof(f696,plain,(
% 1.77/0.62    ( ! [X4,X5,X3] : (~r1_tarski(X5,k2_zfmisc_1(X3,X4)) | k1_relat_1(X5) = k1_relset_1(X3,X4,X5)) )),
% 1.77/0.62    inference(resolution,[],[f87,f76])).
% 1.77/0.62  fof(f92,plain,(
% 1.77/0.62    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(X2,X0,X1)) )),
% 1.77/0.62    inference(cnf_transformation,[],[f45])).
% 1.77/0.62  fof(f53,plain,(
% 1.77/0.62    r1_tarski(sK1,sK2)),
% 1.77/0.62    inference(cnf_transformation,[],[f30])).
% 1.77/0.62  fof(f49,plain,(
% 1.77/0.62    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 1.77/0.62    inference(cnf_transformation,[],[f30])).
% 1.77/0.62  fof(f1633,plain,(
% 1.77/0.62    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.77/0.62    inference(subsumption_resolution,[],[f1631,f194])).
% 1.77/0.62  fof(f194,plain,(
% 1.77/0.62    ( ! [X1] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)) )),
% 1.77/0.62    inference(superposition,[],[f84,f183])).
% 1.77/0.62  fof(f183,plain,(
% 1.77/0.62    ( ! [X6] : (k1_xboole_0 = sK7(k1_xboole_0,X6)) )),
% 1.77/0.62    inference(resolution,[],[f174,f59])).
% 1.77/0.62  fof(f174,plain,(
% 1.77/0.62    ( ! [X0] : (v1_xboole_0(sK7(k1_xboole_0,X0))) )),
% 1.77/0.62    inference(resolution,[],[f147,f124])).
% 1.77/0.62  fof(f147,plain,(
% 1.77/0.62    ( ! [X1] : (m1_subset_1(sK7(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0))) )),
% 1.77/0.62    inference(superposition,[],[f82,f99])).
% 1.77/0.62  fof(f84,plain,(
% 1.77/0.62    ( ! [X0,X1] : (v1_funct_2(sK7(X0,X1),X0,X1)) )),
% 1.77/0.62    inference(cnf_transformation,[],[f28])).
% 1.77/0.62  fof(f1631,plain,(
% 1.77/0.62    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK2) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.77/0.62    inference(backward_demodulation,[],[f1597,f1630])).
% 1.77/0.62  fof(f1597,plain,(
% 1.77/0.62    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(k1_xboole_0,sK0,sK2)),
% 1.77/0.62    inference(forward_demodulation,[],[f1576,f1574])).
% 1.77/0.62  fof(f1574,plain,(
% 1.77/0.62    k1_xboole_0 = sK3),
% 1.77/0.62    inference(forward_demodulation,[],[f1573,f98])).
% 1.77/0.62  fof(f1573,plain,(
% 1.77/0.62    sK3 = k2_zfmisc_1(sK0,k1_xboole_0)),
% 1.77/0.62    inference(forward_demodulation,[],[f1572,f1539])).
% 1.77/0.62  fof(f1572,plain,(
% 1.77/0.62    sK3 = k2_zfmisc_1(sK0,sK1)),
% 1.77/0.62    inference(subsumption_resolution,[],[f1571,f56])).
% 1.77/0.62  fof(f1571,plain,(
% 1.77/0.62    ~r1_tarski(k1_xboole_0,sK3) | sK3 = k2_zfmisc_1(sK0,sK1)),
% 1.77/0.62    inference(forward_demodulation,[],[f1546,f98])).
% 1.77/0.62  fof(f1546,plain,(
% 1.77/0.62    ~r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK3) | sK3 = k2_zfmisc_1(sK0,sK1)),
% 1.77/0.62    inference(backward_demodulation,[],[f236,f1539])).
% 1.77/0.62  fof(f236,plain,(
% 1.77/0.62    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) | sK3 = k2_zfmisc_1(sK0,sK1)),
% 1.77/0.62    inference(resolution,[],[f72,f117])).
% 1.77/0.62  fof(f117,plain,(
% 1.77/0.62    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 1.77/0.62    inference(resolution,[],[f77,f52])).
% 1.77/0.62  fof(f1576,plain,(
% 1.77/0.62    ~v1_funct_2(k1_xboole_0,sK0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.77/0.62    inference(backward_demodulation,[],[f105,f1574])).
% 1.77/0.62  % SZS output end Proof for theBenchmark
% 1.77/0.62  % (23219)------------------------------
% 1.77/0.62  % (23219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.77/0.62  % (23219)Termination reason: Refutation
% 1.77/0.62  
% 1.77/0.62  % (23219)Memory used [KB]: 7419
% 1.77/0.62  % (23219)Time elapsed: 0.149 s
% 1.77/0.62  % (23219)------------------------------
% 1.77/0.62  % (23219)------------------------------
% 1.77/0.62  % (23209)Success in time 0.251 s
%------------------------------------------------------------------------------
