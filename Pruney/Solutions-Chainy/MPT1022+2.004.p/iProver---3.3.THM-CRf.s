%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:36 EST 2020

% Result     : Theorem 1.51s
% Output     : CNFRefutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :  153 (1741 expanded)
%              Number of clauses        :  100 ( 612 expanded)
%              Number of leaves         :   13 ( 324 expanded)
%              Depth                    :   29
%              Number of atoms          :  490 (8636 expanded)
%              Number of equality atoms :  251 (2865 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X2,X0,X0)
        & v1_funct_2(X2,X0,X0)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,X0)
       => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
          & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
       => ( r1_tarski(X1,X0)
         => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
            & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f33,plain,
    ( ? [X0,X1,X2] :
        ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
          | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
        & r1_tarski(X1,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X2,X0,X0)
        & v1_funct_2(X2,X0,X0)
        & v1_funct_1(X2) )
   => ( ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
        | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 )
      & r1_tarski(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK2,sK0,sK0)
      & v1_funct_2(sK2,sK0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
      | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 )
    & r1_tarski(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK2,sK0,sK0)
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f33])).

fof(f54,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f57,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f23])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f55,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f53,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f58,plain,
    ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
    | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
    inference(cnf_transformation,[],[f34])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f63,plain,(
    ! [X2,X1] :
      ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f46])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_461,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_462,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | k1_relset_1(X0,X1,sK2) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_461])).

cnf(c_681,plain,
    ( k1_relset_1(X0,X1,sK2) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | sK2 != sK2
    | sK0 != X1
    | sK0 != X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_462])).

cnf(c_682,plain,
    ( k1_relset_1(sK0,sK0,sK2) = sK0
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_681])).

cnf(c_735,plain,
    ( k1_relset_1(sK0,sK0,sK2) = sK0
    | k1_xboole_0 = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_682])).

cnf(c_756,plain,
    ( k1_relset_1(sK0,sK0,sK2) = sK0
    | k1_xboole_0 = sK0 ),
    inference(subtyping,[status(esa)],[c_735])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_515,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_20])).

cnf(c_516,plain,
    ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(unflattening,[status(thm)],[c_515])).

cnf(c_759,plain,
    ( k1_relset_1(X0_52,X1_52,sK2) = k1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(subtyping,[status(esa)],[c_516])).

cnf(c_916,plain,
    ( k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_759])).

cnf(c_1054,plain,
    ( k1_relat_1(sK2) = sK0
    | sK0 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_756,c_916])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_8,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v2_funct_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_21,negated_conjecture,
    ( v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_259,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | sK2 != X0
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_21])).

cnf(c_260,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v2_funct_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_259])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_262,plain,
    ( v2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_260,c_23,c_20])).

cnf(c_285,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_262])).

cnf(c_286,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_285])).

cnf(c_290,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r1_tarski(X0,k1_relat_1(sK2))
    | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_286,c_23])).

cnf(c_291,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_290])).

cnf(c_329,plain,
    ( ~ v1_relat_1(sK2)
    | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
    | k1_relat_1(sK2) != sK0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_291])).

cnf(c_330,plain,
    ( ~ v1_relat_1(sK2)
    | k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = sK1
    | k1_relat_1(sK2) != sK0 ),
    inference(unflattening,[status(thm)],[c_329])).

cnf(c_438,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = sK1
    | k1_relat_1(sK2) != sK0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_330])).

cnf(c_439,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = sK1
    | k1_relat_1(sK2) != sK0 ),
    inference(unflattening,[status(thm)],[c_438])).

cnf(c_600,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = sK1
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | k1_relat_1(sK2) != sK0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_439])).

cnf(c_738,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = sK1
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | k1_relat_1(sK2) != sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_600])).

cnf(c_754,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = sK1
    | k1_relat_1(sK2) != sK0
    | k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(subtyping,[status(esa)],[c_738])).

cnf(c_765,plain,
    ( sP0_iProver_split
    | k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = sK1
    | k1_relat_1(sK2) != sK0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_754])).

cnf(c_850,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = sK1
    | k1_relat_1(sK2) != sK0
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_765])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_310,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_23])).

cnf(c_311,plain,
    ( ~ r1_tarski(X0,k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_310])).

cnf(c_342,plain,
    ( ~ v1_relat_1(sK2)
    | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
    | k2_relat_1(sK2) != sK0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_311])).

cnf(c_343,plain,
    ( ~ v1_relat_1(sK2)
    | k9_relat_1(sK2,k10_relat_1(sK2,sK1)) = sK1
    | k2_relat_1(sK2) != sK0 ),
    inference(unflattening,[status(thm)],[c_342])).

cnf(c_423,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k9_relat_1(sK2,k10_relat_1(sK2,sK1)) = sK1
    | k2_relat_1(sK2) != sK0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_343])).

cnf(c_424,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k9_relat_1(sK2,k10_relat_1(sK2,sK1)) = sK1
    | k2_relat_1(sK2) != sK0 ),
    inference(unflattening,[status(thm)],[c_423])).

cnf(c_614,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK1)) = sK1
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | k2_relat_1(sK2) != sK0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_424])).

cnf(c_736,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK1)) = sK1
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | k2_relat_1(sK2) != sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_614])).

cnf(c_755,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK1)) = sK1
    | k2_relat_1(sK2) != sK0
    | k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(subtyping,[status(esa)],[c_736])).

cnf(c_764,plain,
    ( sP0_iProver_split
    | k9_relat_1(sK2,k10_relat_1(sK2,sK1)) = sK1
    | k2_relat_1(sK2) != sK0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_755])).

cnf(c_798,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK1)) = sK1
    | k2_relat_1(sK2) != sK0
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_764])).

cnf(c_802,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = sK1
    | k1_relat_1(sK2) != sK0
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_765])).

cnf(c_766,plain,
    ( X0_50 = X0_50 ),
    theory(equality)).

cnf(c_917,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_766])).

cnf(c_3,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_17,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_363,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_3,c_17])).

cnf(c_375,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_363,c_2])).

cnf(c_7,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_270,plain,
    ( v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | sK2 != X0
    | sK0 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_21])).

cnf(c_271,plain,
    ( v2_funct_2(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_270])).

cnf(c_273,plain,
    ( v2_funct_2(sK2,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_271,c_23,c_20])).

cnf(c_408,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relat_1(X0) = X2
    | sK2 != X0
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_375,c_273])).

cnf(c_409,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | k2_relat_1(sK2) = sK0 ),
    inference(unflattening,[status(thm)],[c_408])).

cnf(c_589,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | k2_relat_1(sK2) = sK0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_409])).

cnf(c_740,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | k2_relat_1(sK2) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_589])).

cnf(c_753,plain,
    ( k2_relat_1(sK2) = sK0
    | k1_zfmisc_1(k2_zfmisc_1(X0_52,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(subtyping,[status(esa)],[c_740])).

cnf(c_918,plain,
    ( k2_relat_1(sK2) = sK0
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_753])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_497,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_20])).

cnf(c_498,plain,
    ( k8_relset_1(X0,X1,sK2,X2) = k10_relat_1(sK2,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(unflattening,[status(thm)],[c_497])).

cnf(c_761,plain,
    ( k8_relset_1(X0_52,X1_52,sK2,X0_53) = k10_relat_1(sK2,X0_53)
    | k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(subtyping,[status(esa)],[c_498])).

cnf(c_939,plain,
    ( k8_relset_1(sK0,sK0,sK2,X0_53) = k10_relat_1(sK2,X0_53) ),
    inference(equality_resolution,[status(thm)],[c_761])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_506,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_20])).

cnf(c_507,plain,
    ( k7_relset_1(X0,X1,sK2,X2) = k9_relat_1(sK2,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(unflattening,[status(thm)],[c_506])).

cnf(c_760,plain,
    ( k7_relset_1(X0_52,X1_52,sK2,X0_53) = k9_relat_1(sK2,X0_53)
    | k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(subtyping,[status(esa)],[c_507])).

cnf(c_935,plain,
    ( k7_relset_1(sK0,sK0,sK2,X0_53) = k9_relat_1(sK2,X0_53) ),
    inference(equality_resolution,[status(thm)],[c_760])).

cnf(c_18,negated_conjecture,
    ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
    | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_762,negated_conjecture,
    ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
    | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_987,plain,
    ( k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1)) != sK1
    | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
    inference(demodulation,[status(thm)],[c_935,c_762])).

cnf(c_988,plain,
    ( k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1)) != sK1
    | k9_relat_1(sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
    inference(demodulation,[status(thm)],[c_987,c_935])).

cnf(c_1052,plain,
    ( k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1)) != sK1
    | k9_relat_1(sK2,k10_relat_1(sK2,sK1)) != sK1 ),
    inference(demodulation,[status(thm)],[c_939,c_988])).

cnf(c_1053,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK1)) != sK1
    | k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != sK1 ),
    inference(demodulation,[status(thm)],[c_1052,c_939])).

cnf(c_763,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_755])).

cnf(c_849,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_763])).

cnf(c_1099,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_849])).

cnf(c_1158,plain,
    ( k1_relat_1(sK2) != sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_850,c_798,c_802,c_917,c_918,c_1053,c_1099])).

cnf(c_1161,plain,
    ( sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1054,c_1158])).

cnf(c_1191,plain,
    ( k1_relat_1(sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1161,c_1158])).

cnf(c_1197,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1161,c_916])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_559,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_20])).

cnf(c_560,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,X0)
    | k1_relset_1(k1_xboole_0,X0,sK2) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(unflattening,[status(thm)],[c_559])).

cnf(c_706,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK2) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | sK2 != sK2
    | sK0 != X0
    | sK0 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_560])).

cnf(c_707,plain,
    ( k1_relset_1(k1_xboole_0,sK0,sK2) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | sK0 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_706])).

cnf(c_757,plain,
    ( k1_relset_1(k1_xboole_0,sK0,sK2) = k1_xboole_0
    | sK0 != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(subtyping,[status(esa)],[c_707])).

cnf(c_1199,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_1161,c_757])).

cnf(c_1215,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_1199])).

cnf(c_1218,plain,
    ( k1_relat_1(sK2) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1197,c_1215])).

cnf(c_1232,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1191,c_1218])).

cnf(c_1233,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_1232])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:10:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.51/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.51/0.98  
% 1.51/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.51/0.98  
% 1.51/0.98  ------  iProver source info
% 1.51/0.98  
% 1.51/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.51/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.51/0.98  git: non_committed_changes: false
% 1.51/0.98  git: last_make_outside_of_git: false
% 1.51/0.98  
% 1.51/0.98  ------ 
% 1.51/0.98  
% 1.51/0.98  ------ Input Options
% 1.51/0.98  
% 1.51/0.98  --out_options                           all
% 1.51/0.98  --tptp_safe_out                         true
% 1.51/0.98  --problem_path                          ""
% 1.51/0.98  --include_path                          ""
% 1.51/0.98  --clausifier                            res/vclausify_rel
% 1.51/0.98  --clausifier_options                    --mode clausify
% 1.51/0.98  --stdin                                 false
% 1.51/0.98  --stats_out                             all
% 1.51/0.98  
% 1.51/0.98  ------ General Options
% 1.51/0.98  
% 1.51/0.98  --fof                                   false
% 1.51/0.98  --time_out_real                         305.
% 1.51/0.98  --time_out_virtual                      -1.
% 1.51/0.98  --symbol_type_check                     false
% 1.51/0.98  --clausify_out                          false
% 1.51/0.98  --sig_cnt_out                           false
% 1.51/0.98  --trig_cnt_out                          false
% 1.51/0.98  --trig_cnt_out_tolerance                1.
% 1.51/0.98  --trig_cnt_out_sk_spl                   false
% 1.51/0.98  --abstr_cl_out                          false
% 1.51/0.98  
% 1.51/0.98  ------ Global Options
% 1.51/0.98  
% 1.51/0.98  --schedule                              default
% 1.51/0.98  --add_important_lit                     false
% 1.51/0.98  --prop_solver_per_cl                    1000
% 1.51/0.98  --min_unsat_core                        false
% 1.51/0.98  --soft_assumptions                      false
% 1.51/0.98  --soft_lemma_size                       3
% 1.51/0.98  --prop_impl_unit_size                   0
% 1.51/0.98  --prop_impl_unit                        []
% 1.51/0.98  --share_sel_clauses                     true
% 1.51/0.98  --reset_solvers                         false
% 1.51/0.98  --bc_imp_inh                            [conj_cone]
% 1.51/0.98  --conj_cone_tolerance                   3.
% 1.51/0.98  --extra_neg_conj                        none
% 1.51/0.98  --large_theory_mode                     true
% 1.51/0.98  --prolific_symb_bound                   200
% 1.51/0.98  --lt_threshold                          2000
% 1.51/0.98  --clause_weak_htbl                      true
% 1.51/0.98  --gc_record_bc_elim                     false
% 1.51/0.98  
% 1.51/0.98  ------ Preprocessing Options
% 1.51/0.98  
% 1.51/0.98  --preprocessing_flag                    true
% 1.51/0.98  --time_out_prep_mult                    0.1
% 1.51/0.98  --splitting_mode                        input
% 1.51/0.98  --splitting_grd                         true
% 1.51/0.98  --splitting_cvd                         false
% 1.51/0.98  --splitting_cvd_svl                     false
% 1.51/0.98  --splitting_nvd                         32
% 1.51/0.98  --sub_typing                            true
% 1.51/0.98  --prep_gs_sim                           true
% 1.51/0.98  --prep_unflatten                        true
% 1.51/0.98  --prep_res_sim                          true
% 1.51/0.98  --prep_upred                            true
% 1.51/0.98  --prep_sem_filter                       exhaustive
% 1.51/0.98  --prep_sem_filter_out                   false
% 1.51/0.98  --pred_elim                             true
% 1.51/0.98  --res_sim_input                         true
% 1.51/0.98  --eq_ax_congr_red                       true
% 1.51/0.98  --pure_diseq_elim                       true
% 1.51/0.98  --brand_transform                       false
% 1.51/0.98  --non_eq_to_eq                          false
% 1.51/0.98  --prep_def_merge                        true
% 1.51/0.98  --prep_def_merge_prop_impl              false
% 1.51/0.98  --prep_def_merge_mbd                    true
% 1.51/0.98  --prep_def_merge_tr_red                 false
% 1.51/0.98  --prep_def_merge_tr_cl                  false
% 1.51/0.98  --smt_preprocessing                     true
% 1.51/0.98  --smt_ac_axioms                         fast
% 1.51/0.98  --preprocessed_out                      false
% 1.51/0.98  --preprocessed_stats                    false
% 1.51/0.98  
% 1.51/0.98  ------ Abstraction refinement Options
% 1.51/0.98  
% 1.51/0.98  --abstr_ref                             []
% 1.51/0.98  --abstr_ref_prep                        false
% 1.51/0.98  --abstr_ref_until_sat                   false
% 1.51/0.98  --abstr_ref_sig_restrict                funpre
% 1.51/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.51/0.98  --abstr_ref_under                       []
% 1.51/0.98  
% 1.51/0.98  ------ SAT Options
% 1.51/0.98  
% 1.51/0.98  --sat_mode                              false
% 1.51/0.98  --sat_fm_restart_options                ""
% 1.51/0.98  --sat_gr_def                            false
% 1.51/0.98  --sat_epr_types                         true
% 1.51/0.98  --sat_non_cyclic_types                  false
% 1.51/0.98  --sat_finite_models                     false
% 1.51/0.98  --sat_fm_lemmas                         false
% 1.51/0.98  --sat_fm_prep                           false
% 1.51/0.98  --sat_fm_uc_incr                        true
% 1.51/0.98  --sat_out_model                         small
% 1.51/0.98  --sat_out_clauses                       false
% 1.51/0.98  
% 1.51/0.98  ------ QBF Options
% 1.51/0.98  
% 1.51/0.98  --qbf_mode                              false
% 1.51/0.98  --qbf_elim_univ                         false
% 1.51/0.98  --qbf_dom_inst                          none
% 1.51/0.98  --qbf_dom_pre_inst                      false
% 1.51/0.98  --qbf_sk_in                             false
% 1.51/0.98  --qbf_pred_elim                         true
% 1.51/0.98  --qbf_split                             512
% 1.51/0.98  
% 1.51/0.98  ------ BMC1 Options
% 1.51/0.98  
% 1.51/0.98  --bmc1_incremental                      false
% 1.51/0.98  --bmc1_axioms                           reachable_all
% 1.51/0.98  --bmc1_min_bound                        0
% 1.51/0.98  --bmc1_max_bound                        -1
% 1.51/0.98  --bmc1_max_bound_default                -1
% 1.51/0.98  --bmc1_symbol_reachability              true
% 1.51/0.98  --bmc1_property_lemmas                  false
% 1.51/0.98  --bmc1_k_induction                      false
% 1.51/0.98  --bmc1_non_equiv_states                 false
% 1.51/0.98  --bmc1_deadlock                         false
% 1.51/0.98  --bmc1_ucm                              false
% 1.51/0.98  --bmc1_add_unsat_core                   none
% 1.51/0.98  --bmc1_unsat_core_children              false
% 1.51/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.51/0.98  --bmc1_out_stat                         full
% 1.51/0.98  --bmc1_ground_init                      false
% 1.51/0.98  --bmc1_pre_inst_next_state              false
% 1.51/0.98  --bmc1_pre_inst_state                   false
% 1.51/0.98  --bmc1_pre_inst_reach_state             false
% 1.51/0.98  --bmc1_out_unsat_core                   false
% 1.51/0.98  --bmc1_aig_witness_out                  false
% 1.51/0.98  --bmc1_verbose                          false
% 1.51/0.98  --bmc1_dump_clauses_tptp                false
% 1.51/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.51/0.98  --bmc1_dump_file                        -
% 1.51/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.51/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.51/0.98  --bmc1_ucm_extend_mode                  1
% 1.51/0.98  --bmc1_ucm_init_mode                    2
% 1.51/0.98  --bmc1_ucm_cone_mode                    none
% 1.51/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.51/0.98  --bmc1_ucm_relax_model                  4
% 1.51/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.51/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.51/0.98  --bmc1_ucm_layered_model                none
% 1.51/0.98  --bmc1_ucm_max_lemma_size               10
% 1.51/0.98  
% 1.51/0.98  ------ AIG Options
% 1.51/0.98  
% 1.51/0.98  --aig_mode                              false
% 1.51/0.98  
% 1.51/0.98  ------ Instantiation Options
% 1.51/0.98  
% 1.51/0.98  --instantiation_flag                    true
% 1.51/0.98  --inst_sos_flag                         false
% 1.51/0.98  --inst_sos_phase                        true
% 1.51/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.51/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.51/0.98  --inst_lit_sel_side                     num_symb
% 1.51/0.98  --inst_solver_per_active                1400
% 1.51/0.98  --inst_solver_calls_frac                1.
% 1.51/0.98  --inst_passive_queue_type               priority_queues
% 1.51/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.51/0.98  --inst_passive_queues_freq              [25;2]
% 1.51/0.98  --inst_dismatching                      true
% 1.51/0.98  --inst_eager_unprocessed_to_passive     true
% 1.51/0.98  --inst_prop_sim_given                   true
% 1.51/0.98  --inst_prop_sim_new                     false
% 1.51/0.98  --inst_subs_new                         false
% 1.51/0.98  --inst_eq_res_simp                      false
% 1.51/0.98  --inst_subs_given                       false
% 1.51/0.98  --inst_orphan_elimination               true
% 1.51/0.98  --inst_learning_loop_flag               true
% 1.51/0.98  --inst_learning_start                   3000
% 1.51/0.98  --inst_learning_factor                  2
% 1.51/0.98  --inst_start_prop_sim_after_learn       3
% 1.51/0.98  --inst_sel_renew                        solver
% 1.51/0.98  --inst_lit_activity_flag                true
% 1.51/0.98  --inst_restr_to_given                   false
% 1.51/0.98  --inst_activity_threshold               500
% 1.51/0.98  --inst_out_proof                        true
% 1.51/0.98  
% 1.51/0.98  ------ Resolution Options
% 1.51/0.98  
% 1.51/0.98  --resolution_flag                       true
% 1.51/0.98  --res_lit_sel                           adaptive
% 1.51/0.98  --res_lit_sel_side                      none
% 1.51/0.98  --res_ordering                          kbo
% 1.51/0.98  --res_to_prop_solver                    active
% 1.51/0.98  --res_prop_simpl_new                    false
% 1.51/0.98  --res_prop_simpl_given                  true
% 1.51/0.98  --res_passive_queue_type                priority_queues
% 1.51/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.51/0.98  --res_passive_queues_freq               [15;5]
% 1.51/0.98  --res_forward_subs                      full
% 1.51/0.98  --res_backward_subs                     full
% 1.51/0.98  --res_forward_subs_resolution           true
% 1.51/0.98  --res_backward_subs_resolution          true
% 1.51/0.98  --res_orphan_elimination                true
% 1.51/0.98  --res_time_limit                        2.
% 1.51/0.98  --res_out_proof                         true
% 1.51/0.98  
% 1.51/0.98  ------ Superposition Options
% 1.51/0.98  
% 1.51/0.98  --superposition_flag                    true
% 1.51/0.98  --sup_passive_queue_type                priority_queues
% 1.51/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.51/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.51/0.98  --demod_completeness_check              fast
% 1.51/0.98  --demod_use_ground                      true
% 1.51/0.98  --sup_to_prop_solver                    passive
% 1.51/0.98  --sup_prop_simpl_new                    true
% 1.51/0.98  --sup_prop_simpl_given                  true
% 1.51/0.98  --sup_fun_splitting                     false
% 1.51/0.98  --sup_smt_interval                      50000
% 1.51/0.98  
% 1.51/0.98  ------ Superposition Simplification Setup
% 1.51/0.98  
% 1.51/0.98  --sup_indices_passive                   []
% 1.51/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.51/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.51/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.51/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.51/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.51/0.98  --sup_full_bw                           [BwDemod]
% 1.51/0.98  --sup_immed_triv                        [TrivRules]
% 1.51/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.51/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.51/0.98  --sup_immed_bw_main                     []
% 1.51/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.51/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.51/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.51/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.51/0.98  
% 1.51/0.98  ------ Combination Options
% 1.51/0.98  
% 1.51/0.98  --comb_res_mult                         3
% 1.51/0.98  --comb_sup_mult                         2
% 1.51/0.98  --comb_inst_mult                        10
% 1.51/0.98  
% 1.51/0.98  ------ Debug Options
% 1.51/0.98  
% 1.51/0.98  --dbg_backtrace                         false
% 1.51/0.98  --dbg_dump_prop_clauses                 false
% 1.51/0.98  --dbg_dump_prop_clauses_file            -
% 1.51/0.98  --dbg_out_stat                          false
% 1.51/0.98  ------ Parsing...
% 1.51/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.51/0.98  
% 1.51/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 1.51/0.98  
% 1.51/0.98  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.51/0.98  
% 1.51/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.51/0.98  ------ Proving...
% 1.51/0.98  ------ Problem Properties 
% 1.51/0.98  
% 1.51/0.98  
% 1.51/0.98  clauses                                 12
% 1.51/0.98  conjectures                             1
% 1.51/0.98  EPR                                     0
% 1.51/0.98  Horn                                    8
% 1.51/0.98  unary                                   0
% 1.51/0.98  binary                                  8
% 1.51/0.98  lits                                    29
% 1.51/0.98  lits eq                                 25
% 1.51/0.98  fd_pure                                 0
% 1.51/0.98  fd_pseudo                               0
% 1.51/0.98  fd_cond                                 0
% 1.51/0.98  fd_pseudo_cond                          0
% 1.51/0.98  AC symbols                              0
% 1.51/0.98  
% 1.51/0.98  ------ Schedule dynamic 5 is on 
% 1.51/0.98  
% 1.51/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.51/0.98  
% 1.51/0.98  
% 1.51/0.98  ------ 
% 1.51/0.98  Current options:
% 1.51/0.98  ------ 
% 1.51/0.98  
% 1.51/0.98  ------ Input Options
% 1.51/0.98  
% 1.51/0.98  --out_options                           all
% 1.51/0.98  --tptp_safe_out                         true
% 1.51/0.98  --problem_path                          ""
% 1.51/0.98  --include_path                          ""
% 1.51/0.98  --clausifier                            res/vclausify_rel
% 1.51/0.98  --clausifier_options                    --mode clausify
% 1.51/0.98  --stdin                                 false
% 1.51/0.98  --stats_out                             all
% 1.51/0.98  
% 1.51/0.98  ------ General Options
% 1.51/0.98  
% 1.51/0.98  --fof                                   false
% 1.51/0.98  --time_out_real                         305.
% 1.51/0.98  --time_out_virtual                      -1.
% 1.51/0.98  --symbol_type_check                     false
% 1.51/0.98  --clausify_out                          false
% 1.51/0.98  --sig_cnt_out                           false
% 1.51/0.98  --trig_cnt_out                          false
% 1.51/0.98  --trig_cnt_out_tolerance                1.
% 1.51/0.98  --trig_cnt_out_sk_spl                   false
% 1.51/0.98  --abstr_cl_out                          false
% 1.51/0.98  
% 1.51/0.98  ------ Global Options
% 1.51/0.98  
% 1.51/0.98  --schedule                              default
% 1.51/0.98  --add_important_lit                     false
% 1.51/0.98  --prop_solver_per_cl                    1000
% 1.51/0.98  --min_unsat_core                        false
% 1.51/0.98  --soft_assumptions                      false
% 1.51/0.98  --soft_lemma_size                       3
% 1.51/0.98  --prop_impl_unit_size                   0
% 1.51/0.98  --prop_impl_unit                        []
% 1.51/0.98  --share_sel_clauses                     true
% 1.51/0.98  --reset_solvers                         false
% 1.51/0.98  --bc_imp_inh                            [conj_cone]
% 1.51/0.98  --conj_cone_tolerance                   3.
% 1.51/0.98  --extra_neg_conj                        none
% 1.51/0.98  --large_theory_mode                     true
% 1.51/0.98  --prolific_symb_bound                   200
% 1.51/0.98  --lt_threshold                          2000
% 1.51/0.98  --clause_weak_htbl                      true
% 1.51/0.98  --gc_record_bc_elim                     false
% 1.51/0.98  
% 1.51/0.98  ------ Preprocessing Options
% 1.51/0.98  
% 1.51/0.98  --preprocessing_flag                    true
% 1.51/0.98  --time_out_prep_mult                    0.1
% 1.51/0.98  --splitting_mode                        input
% 1.51/0.98  --splitting_grd                         true
% 1.51/0.98  --splitting_cvd                         false
% 1.51/0.98  --splitting_cvd_svl                     false
% 1.51/0.98  --splitting_nvd                         32
% 1.51/0.98  --sub_typing                            true
% 1.51/0.98  --prep_gs_sim                           true
% 1.51/0.98  --prep_unflatten                        true
% 1.51/0.98  --prep_res_sim                          true
% 1.51/0.98  --prep_upred                            true
% 1.51/0.98  --prep_sem_filter                       exhaustive
% 1.51/0.98  --prep_sem_filter_out                   false
% 1.51/0.98  --pred_elim                             true
% 1.51/0.98  --res_sim_input                         true
% 1.51/0.98  --eq_ax_congr_red                       true
% 1.51/0.98  --pure_diseq_elim                       true
% 1.51/0.98  --brand_transform                       false
% 1.51/0.98  --non_eq_to_eq                          false
% 1.51/0.98  --prep_def_merge                        true
% 1.51/0.98  --prep_def_merge_prop_impl              false
% 1.51/0.98  --prep_def_merge_mbd                    true
% 1.51/0.98  --prep_def_merge_tr_red                 false
% 1.51/0.98  --prep_def_merge_tr_cl                  false
% 1.51/0.98  --smt_preprocessing                     true
% 1.51/0.98  --smt_ac_axioms                         fast
% 1.51/0.98  --preprocessed_out                      false
% 1.51/0.98  --preprocessed_stats                    false
% 1.51/0.98  
% 1.51/0.98  ------ Abstraction refinement Options
% 1.51/0.98  
% 1.51/0.98  --abstr_ref                             []
% 1.51/0.98  --abstr_ref_prep                        false
% 1.51/0.98  --abstr_ref_until_sat                   false
% 1.51/0.98  --abstr_ref_sig_restrict                funpre
% 1.51/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.51/0.98  --abstr_ref_under                       []
% 1.51/0.98  
% 1.51/0.98  ------ SAT Options
% 1.51/0.98  
% 1.51/0.98  --sat_mode                              false
% 1.51/0.98  --sat_fm_restart_options                ""
% 1.51/0.98  --sat_gr_def                            false
% 1.51/0.98  --sat_epr_types                         true
% 1.51/0.98  --sat_non_cyclic_types                  false
% 1.51/0.98  --sat_finite_models                     false
% 1.51/0.98  --sat_fm_lemmas                         false
% 1.51/0.98  --sat_fm_prep                           false
% 1.51/0.98  --sat_fm_uc_incr                        true
% 1.51/0.98  --sat_out_model                         small
% 1.51/0.98  --sat_out_clauses                       false
% 1.51/0.98  
% 1.51/0.98  ------ QBF Options
% 1.51/0.98  
% 1.51/0.98  --qbf_mode                              false
% 1.51/0.98  --qbf_elim_univ                         false
% 1.51/0.98  --qbf_dom_inst                          none
% 1.51/0.98  --qbf_dom_pre_inst                      false
% 1.51/0.98  --qbf_sk_in                             false
% 1.51/0.98  --qbf_pred_elim                         true
% 1.51/0.98  --qbf_split                             512
% 1.51/0.98  
% 1.51/0.98  ------ BMC1 Options
% 1.51/0.98  
% 1.51/0.98  --bmc1_incremental                      false
% 1.51/0.98  --bmc1_axioms                           reachable_all
% 1.51/0.98  --bmc1_min_bound                        0
% 1.51/0.98  --bmc1_max_bound                        -1
% 1.51/0.98  --bmc1_max_bound_default                -1
% 1.51/0.98  --bmc1_symbol_reachability              true
% 1.51/0.98  --bmc1_property_lemmas                  false
% 1.51/0.98  --bmc1_k_induction                      false
% 1.51/0.98  --bmc1_non_equiv_states                 false
% 1.51/0.98  --bmc1_deadlock                         false
% 1.51/0.98  --bmc1_ucm                              false
% 1.51/0.98  --bmc1_add_unsat_core                   none
% 1.51/0.98  --bmc1_unsat_core_children              false
% 1.51/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.51/0.98  --bmc1_out_stat                         full
% 1.51/0.98  --bmc1_ground_init                      false
% 1.51/0.98  --bmc1_pre_inst_next_state              false
% 1.51/0.98  --bmc1_pre_inst_state                   false
% 1.51/0.98  --bmc1_pre_inst_reach_state             false
% 1.51/0.98  --bmc1_out_unsat_core                   false
% 1.51/0.98  --bmc1_aig_witness_out                  false
% 1.51/0.98  --bmc1_verbose                          false
% 1.51/0.98  --bmc1_dump_clauses_tptp                false
% 1.51/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.51/0.98  --bmc1_dump_file                        -
% 1.51/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.51/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.51/0.98  --bmc1_ucm_extend_mode                  1
% 1.51/0.98  --bmc1_ucm_init_mode                    2
% 1.51/0.98  --bmc1_ucm_cone_mode                    none
% 1.51/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.51/0.98  --bmc1_ucm_relax_model                  4
% 1.51/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.51/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.51/0.98  --bmc1_ucm_layered_model                none
% 1.51/0.98  --bmc1_ucm_max_lemma_size               10
% 1.51/0.98  
% 1.51/0.98  ------ AIG Options
% 1.51/0.98  
% 1.51/0.98  --aig_mode                              false
% 1.51/0.98  
% 1.51/0.98  ------ Instantiation Options
% 1.51/0.98  
% 1.51/0.98  --instantiation_flag                    true
% 1.51/0.98  --inst_sos_flag                         false
% 1.51/0.98  --inst_sos_phase                        true
% 1.51/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.51/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.51/0.98  --inst_lit_sel_side                     none
% 1.51/0.98  --inst_solver_per_active                1400
% 1.51/0.98  --inst_solver_calls_frac                1.
% 1.51/0.98  --inst_passive_queue_type               priority_queues
% 1.51/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.51/0.98  --inst_passive_queues_freq              [25;2]
% 1.51/0.98  --inst_dismatching                      true
% 1.51/0.98  --inst_eager_unprocessed_to_passive     true
% 1.51/0.98  --inst_prop_sim_given                   true
% 1.51/0.98  --inst_prop_sim_new                     false
% 1.51/0.98  --inst_subs_new                         false
% 1.51/0.98  --inst_eq_res_simp                      false
% 1.51/0.98  --inst_subs_given                       false
% 1.51/0.98  --inst_orphan_elimination               true
% 1.51/0.98  --inst_learning_loop_flag               true
% 1.51/0.98  --inst_learning_start                   3000
% 1.51/0.98  --inst_learning_factor                  2
% 1.51/0.98  --inst_start_prop_sim_after_learn       3
% 1.51/0.98  --inst_sel_renew                        solver
% 1.51/0.98  --inst_lit_activity_flag                true
% 1.51/0.98  --inst_restr_to_given                   false
% 1.51/0.98  --inst_activity_threshold               500
% 1.51/0.98  --inst_out_proof                        true
% 1.51/0.98  
% 1.51/0.98  ------ Resolution Options
% 1.51/0.98  
% 1.51/0.98  --resolution_flag                       false
% 1.51/0.98  --res_lit_sel                           adaptive
% 1.51/0.98  --res_lit_sel_side                      none
% 1.51/0.98  --res_ordering                          kbo
% 1.51/0.98  --res_to_prop_solver                    active
% 1.51/0.98  --res_prop_simpl_new                    false
% 1.51/0.98  --res_prop_simpl_given                  true
% 1.51/0.98  --res_passive_queue_type                priority_queues
% 1.51/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.51/0.98  --res_passive_queues_freq               [15;5]
% 1.51/0.98  --res_forward_subs                      full
% 1.51/0.98  --res_backward_subs                     full
% 1.51/0.98  --res_forward_subs_resolution           true
% 1.51/0.98  --res_backward_subs_resolution          true
% 1.51/0.98  --res_orphan_elimination                true
% 1.51/0.98  --res_time_limit                        2.
% 1.51/0.98  --res_out_proof                         true
% 1.51/0.98  
% 1.51/0.98  ------ Superposition Options
% 1.51/0.98  
% 1.51/0.98  --superposition_flag                    true
% 1.51/0.98  --sup_passive_queue_type                priority_queues
% 1.51/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.51/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.51/0.98  --demod_completeness_check              fast
% 1.51/0.98  --demod_use_ground                      true
% 1.51/0.98  --sup_to_prop_solver                    passive
% 1.51/0.98  --sup_prop_simpl_new                    true
% 1.51/0.98  --sup_prop_simpl_given                  true
% 1.51/0.98  --sup_fun_splitting                     false
% 1.51/0.98  --sup_smt_interval                      50000
% 1.51/0.98  
% 1.51/0.98  ------ Superposition Simplification Setup
% 1.51/0.98  
% 1.51/0.98  --sup_indices_passive                   []
% 1.51/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.51/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.51/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.51/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.51/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.51/0.98  --sup_full_bw                           [BwDemod]
% 1.51/0.98  --sup_immed_triv                        [TrivRules]
% 1.51/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.51/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.51/0.98  --sup_immed_bw_main                     []
% 1.51/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.51/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.51/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.51/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.51/0.98  
% 1.51/0.98  ------ Combination Options
% 1.51/0.98  
% 1.51/0.98  --comb_res_mult                         3
% 1.51/0.98  --comb_sup_mult                         2
% 1.51/0.98  --comb_inst_mult                        10
% 1.51/0.98  
% 1.51/0.98  ------ Debug Options
% 1.51/0.98  
% 1.51/0.98  --dbg_backtrace                         false
% 1.51/0.98  --dbg_dump_prop_clauses                 false
% 1.51/0.98  --dbg_dump_prop_clauses_file            -
% 1.51/0.98  --dbg_out_stat                          false
% 1.51/0.98  
% 1.51/0.98  
% 1.51/0.98  
% 1.51/0.98  
% 1.51/0.98  ------ Proving...
% 1.51/0.98  
% 1.51/0.98  
% 1.51/0.98  % SZS status Theorem for theBenchmark.p
% 1.51/0.98  
% 1.51/0.98   Resolution empty clause
% 1.51/0.98  
% 1.51/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.51/0.98  
% 1.51/0.98  fof(f11,conjecture,(
% 1.51/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 1.51/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/0.98  
% 1.51/0.98  fof(f12,negated_conjecture,(
% 1.51/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 1.51/0.98    inference(negated_conjecture,[],[f11])).
% 1.51/0.98  
% 1.51/0.98  fof(f29,plain,(
% 1.51/0.98    ? [X0,X1,X2] : (((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)))),
% 1.51/0.98    inference(ennf_transformation,[],[f12])).
% 1.51/0.98  
% 1.51/0.98  fof(f30,plain,(
% 1.51/0.98    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))),
% 1.51/0.98    inference(flattening,[],[f29])).
% 1.51/0.98  
% 1.51/0.98  fof(f33,plain,(
% 1.51/0.98    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1) & r1_tarski(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 1.51/0.98    introduced(choice_axiom,[])).
% 1.51/0.98  
% 1.51/0.98  fof(f34,plain,(
% 1.51/0.98    (k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1) & r1_tarski(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)),
% 1.51/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f33])).
% 1.51/0.98  
% 1.51/0.98  fof(f54,plain,(
% 1.51/0.98    v1_funct_2(sK2,sK0,sK0)),
% 1.51/0.98    inference(cnf_transformation,[],[f34])).
% 1.51/0.98  
% 1.51/0.98  fof(f9,axiom,(
% 1.51/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.51/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/0.98  
% 1.51/0.98  fof(f25,plain,(
% 1.51/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.98    inference(ennf_transformation,[],[f9])).
% 1.51/0.98  
% 1.51/0.98  fof(f26,plain,(
% 1.51/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.98    inference(flattening,[],[f25])).
% 1.51/0.98  
% 1.51/0.98  fof(f31,plain,(
% 1.51/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.98    inference(nnf_transformation,[],[f26])).
% 1.51/0.98  
% 1.51/0.98  fof(f45,plain,(
% 1.51/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.51/0.98    inference(cnf_transformation,[],[f31])).
% 1.51/0.98  
% 1.51/0.98  fof(f56,plain,(
% 1.51/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.51/0.98    inference(cnf_transformation,[],[f34])).
% 1.51/0.98  
% 1.51/0.98  fof(f5,axiom,(
% 1.51/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.51/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/0.98  
% 1.51/0.98  fof(f20,plain,(
% 1.51/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.98    inference(ennf_transformation,[],[f5])).
% 1.51/0.98  
% 1.51/0.98  fof(f39,plain,(
% 1.51/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.51/0.98    inference(cnf_transformation,[],[f20])).
% 1.51/0.98  
% 1.51/0.98  fof(f3,axiom,(
% 1.51/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.51/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/0.98  
% 1.51/0.98  fof(f18,plain,(
% 1.51/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.98    inference(ennf_transformation,[],[f3])).
% 1.51/0.98  
% 1.51/0.98  fof(f37,plain,(
% 1.51/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.51/0.98    inference(cnf_transformation,[],[f18])).
% 1.51/0.98  
% 1.51/0.98  fof(f57,plain,(
% 1.51/0.98    r1_tarski(sK1,sK0)),
% 1.51/0.98    inference(cnf_transformation,[],[f34])).
% 1.51/0.98  
% 1.51/0.98  fof(f2,axiom,(
% 1.51/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 1.51/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/0.98  
% 1.51/0.98  fof(f16,plain,(
% 1.51/0.98    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.51/0.98    inference(ennf_transformation,[],[f2])).
% 1.51/0.98  
% 1.51/0.98  fof(f17,plain,(
% 1.51/0.98    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.51/0.98    inference(flattening,[],[f16])).
% 1.51/0.98  
% 1.51/0.98  fof(f36,plain,(
% 1.51/0.98    ( ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.51/0.98    inference(cnf_transformation,[],[f17])).
% 1.51/0.98  
% 1.51/0.98  fof(f8,axiom,(
% 1.51/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 1.51/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/0.98  
% 1.51/0.98  fof(f23,plain,(
% 1.51/0.98    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.98    inference(ennf_transformation,[],[f8])).
% 1.51/0.98  
% 1.51/0.98  fof(f24,plain,(
% 1.51/0.98    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.98    inference(flattening,[],[f23])).
% 1.51/0.98  
% 1.51/0.98  fof(f43,plain,(
% 1.51/0.98    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.51/0.98    inference(cnf_transformation,[],[f24])).
% 1.51/0.98  
% 1.51/0.98  fof(f55,plain,(
% 1.51/0.98    v3_funct_2(sK2,sK0,sK0)),
% 1.51/0.98    inference(cnf_transformation,[],[f34])).
% 1.51/0.98  
% 1.51/0.98  fof(f53,plain,(
% 1.51/0.98    v1_funct_1(sK2)),
% 1.51/0.98    inference(cnf_transformation,[],[f34])).
% 1.51/0.98  
% 1.51/0.98  fof(f1,axiom,(
% 1.51/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 1.51/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/0.98  
% 1.51/0.98  fof(f14,plain,(
% 1.51/0.98    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.51/0.98    inference(ennf_transformation,[],[f1])).
% 1.51/0.98  
% 1.51/0.98  fof(f15,plain,(
% 1.51/0.98    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.51/0.98    inference(flattening,[],[f14])).
% 1.51/0.98  
% 1.51/0.98  fof(f35,plain,(
% 1.51/0.98    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.51/0.98    inference(cnf_transformation,[],[f15])).
% 1.51/0.98  
% 1.51/0.98  fof(f4,axiom,(
% 1.51/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.51/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/0.98  
% 1.51/0.98  fof(f13,plain,(
% 1.51/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.51/0.98    inference(pure_predicate_removal,[],[f4])).
% 1.51/0.98  
% 1.51/0.98  fof(f19,plain,(
% 1.51/0.98    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.98    inference(ennf_transformation,[],[f13])).
% 1.51/0.98  
% 1.51/0.98  fof(f38,plain,(
% 1.51/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.51/0.98    inference(cnf_transformation,[],[f19])).
% 1.51/0.98  
% 1.51/0.98  fof(f10,axiom,(
% 1.51/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.51/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/0.98  
% 1.51/0.98  fof(f27,plain,(
% 1.51/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.51/0.98    inference(ennf_transformation,[],[f10])).
% 1.51/0.98  
% 1.51/0.98  fof(f28,plain,(
% 1.51/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.51/0.98    inference(flattening,[],[f27])).
% 1.51/0.98  
% 1.51/0.98  fof(f32,plain,(
% 1.51/0.98    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.51/0.98    inference(nnf_transformation,[],[f28])).
% 1.51/0.98  
% 1.51/0.98  fof(f51,plain,(
% 1.51/0.98    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.51/0.98    inference(cnf_transformation,[],[f32])).
% 1.51/0.98  
% 1.51/0.98  fof(f44,plain,(
% 1.51/0.98    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.51/0.98    inference(cnf_transformation,[],[f24])).
% 1.51/0.98  
% 1.51/0.98  fof(f7,axiom,(
% 1.51/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 1.51/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/0.98  
% 1.51/0.98  fof(f22,plain,(
% 1.51/0.98    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.98    inference(ennf_transformation,[],[f7])).
% 1.51/0.98  
% 1.51/0.98  fof(f41,plain,(
% 1.51/0.98    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.51/0.98    inference(cnf_transformation,[],[f22])).
% 1.51/0.98  
% 1.51/0.98  fof(f6,axiom,(
% 1.51/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 1.51/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/0.98  
% 1.51/0.98  fof(f21,plain,(
% 1.51/0.98    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.98    inference(ennf_transformation,[],[f6])).
% 1.51/0.98  
% 1.51/0.98  fof(f40,plain,(
% 1.51/0.98    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.51/0.98    inference(cnf_transformation,[],[f21])).
% 1.51/0.98  
% 1.51/0.98  fof(f58,plain,(
% 1.51/0.98    k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1),
% 1.51/0.98    inference(cnf_transformation,[],[f34])).
% 1.51/0.98  
% 1.51/0.98  fof(f46,plain,(
% 1.51/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.51/0.98    inference(cnf_transformation,[],[f31])).
% 1.51/0.98  
% 1.51/0.98  fof(f63,plain,(
% 1.51/0.98    ( ! [X2,X1] : (k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0 | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.51/0.98    inference(equality_resolution,[],[f46])).
% 1.51/0.98  
% 1.51/0.98  cnf(c_22,negated_conjecture,
% 1.51/0.98      ( v1_funct_2(sK2,sK0,sK0) ),
% 1.51/0.98      inference(cnf_transformation,[],[f54]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_15,plain,
% 1.51/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 1.51/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.51/0.98      | k1_relset_1(X1,X2,X0) = X1
% 1.51/0.98      | k1_xboole_0 = X2 ),
% 1.51/0.98      inference(cnf_transformation,[],[f45]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_20,negated_conjecture,
% 1.51/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 1.51/0.98      inference(cnf_transformation,[],[f56]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_461,plain,
% 1.51/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 1.51/0.98      | k1_relset_1(X1,X2,X0) = X1
% 1.51/0.98      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 1.51/0.98      | sK2 != X0
% 1.51/0.98      | k1_xboole_0 = X2 ),
% 1.51/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_20]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_462,plain,
% 1.51/0.98      ( ~ v1_funct_2(sK2,X0,X1)
% 1.51/0.98      | k1_relset_1(X0,X1,sK2) = X0
% 1.51/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 1.51/0.98      | k1_xboole_0 = X1 ),
% 1.51/0.98      inference(unflattening,[status(thm)],[c_461]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_681,plain,
% 1.51/0.98      ( k1_relset_1(X0,X1,sK2) = X0
% 1.51/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 1.51/0.98      | sK2 != sK2
% 1.51/0.98      | sK0 != X1
% 1.51/0.98      | sK0 != X0
% 1.51/0.98      | k1_xboole_0 = X1 ),
% 1.51/0.98      inference(resolution_lifted,[status(thm)],[c_22,c_462]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_682,plain,
% 1.51/0.98      ( k1_relset_1(sK0,sK0,sK2) = sK0
% 1.51/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 1.51/0.98      | k1_xboole_0 = sK0 ),
% 1.51/0.98      inference(unflattening,[status(thm)],[c_681]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_735,plain,
% 1.51/0.98      ( k1_relset_1(sK0,sK0,sK2) = sK0 | k1_xboole_0 = sK0 ),
% 1.51/0.98      inference(equality_resolution_simp,[status(thm)],[c_682]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_756,plain,
% 1.51/0.98      ( k1_relset_1(sK0,sK0,sK2) = sK0 | k1_xboole_0 = sK0 ),
% 1.51/0.98      inference(subtyping,[status(esa)],[c_735]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_4,plain,
% 1.51/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.51/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.51/0.98      inference(cnf_transformation,[],[f39]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_515,plain,
% 1.51/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.51/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 1.51/0.98      | sK2 != X2 ),
% 1.51/0.98      inference(resolution_lifted,[status(thm)],[c_4,c_20]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_516,plain,
% 1.51/0.98      ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
% 1.51/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 1.51/0.98      inference(unflattening,[status(thm)],[c_515]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_759,plain,
% 1.51/0.98      ( k1_relset_1(X0_52,X1_52,sK2) = k1_relat_1(sK2)
% 1.51/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 1.51/0.98      inference(subtyping,[status(esa)],[c_516]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_916,plain,
% 1.51/0.98      ( k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2) ),
% 1.51/0.98      inference(equality_resolution,[status(thm)],[c_759]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_1054,plain,
% 1.51/0.98      ( k1_relat_1(sK2) = sK0 | sK0 = k1_xboole_0 ),
% 1.51/0.98      inference(demodulation,[status(thm)],[c_756,c_916]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_2,plain,
% 1.51/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 1.51/0.98      inference(cnf_transformation,[],[f37]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_19,negated_conjecture,
% 1.51/0.98      ( r1_tarski(sK1,sK0) ),
% 1.51/0.98      inference(cnf_transformation,[],[f57]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_1,plain,
% 1.51/0.98      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 1.51/0.98      | ~ v2_funct_1(X1)
% 1.51/0.98      | ~ v1_relat_1(X1)
% 1.51/0.98      | ~ v1_funct_1(X1)
% 1.51/0.98      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
% 1.51/0.98      inference(cnf_transformation,[],[f36]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_8,plain,
% 1.51/0.98      ( ~ v3_funct_2(X0,X1,X2)
% 1.51/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.51/0.98      | v2_funct_1(X0)
% 1.51/0.98      | ~ v1_funct_1(X0) ),
% 1.51/0.98      inference(cnf_transformation,[],[f43]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_21,negated_conjecture,
% 1.51/0.98      ( v3_funct_2(sK2,sK0,sK0) ),
% 1.51/0.98      inference(cnf_transformation,[],[f55]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_259,plain,
% 1.51/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.51/0.98      | v2_funct_1(X0)
% 1.51/0.98      | ~ v1_funct_1(X0)
% 1.51/0.98      | sK2 != X0
% 1.51/0.98      | sK0 != X2
% 1.51/0.98      | sK0 != X1 ),
% 1.51/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_21]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_260,plain,
% 1.51/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.51/0.98      | v2_funct_1(sK2)
% 1.51/0.98      | ~ v1_funct_1(sK2) ),
% 1.51/0.98      inference(unflattening,[status(thm)],[c_259]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_23,negated_conjecture,
% 1.51/0.98      ( v1_funct_1(sK2) ),
% 1.51/0.98      inference(cnf_transformation,[],[f53]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_262,plain,
% 1.51/0.98      ( v2_funct_1(sK2) ),
% 1.51/0.98      inference(global_propositional_subsumption,
% 1.51/0.98                [status(thm)],
% 1.51/0.98                [c_260,c_23,c_20]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_285,plain,
% 1.51/0.98      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 1.51/0.98      | ~ v1_relat_1(X1)
% 1.51/0.98      | ~ v1_funct_1(X1)
% 1.51/0.98      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
% 1.51/0.98      | sK2 != X1 ),
% 1.51/0.98      inference(resolution_lifted,[status(thm)],[c_1,c_262]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_286,plain,
% 1.51/0.98      ( ~ r1_tarski(X0,k1_relat_1(sK2))
% 1.51/0.98      | ~ v1_relat_1(sK2)
% 1.51/0.98      | ~ v1_funct_1(sK2)
% 1.51/0.98      | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
% 1.51/0.98      inference(unflattening,[status(thm)],[c_285]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_290,plain,
% 1.51/0.98      ( ~ v1_relat_1(sK2)
% 1.51/0.98      | ~ r1_tarski(X0,k1_relat_1(sK2))
% 1.51/0.98      | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
% 1.51/0.98      inference(global_propositional_subsumption,[status(thm)],[c_286,c_23]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_291,plain,
% 1.51/0.98      ( ~ r1_tarski(X0,k1_relat_1(sK2))
% 1.51/0.98      | ~ v1_relat_1(sK2)
% 1.51/0.98      | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
% 1.51/0.98      inference(renaming,[status(thm)],[c_290]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_329,plain,
% 1.51/0.98      ( ~ v1_relat_1(sK2)
% 1.51/0.98      | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
% 1.51/0.98      | k1_relat_1(sK2) != sK0
% 1.51/0.98      | sK1 != X0 ),
% 1.51/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_291]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_330,plain,
% 1.51/0.98      ( ~ v1_relat_1(sK2)
% 1.51/0.98      | k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = sK1
% 1.51/0.98      | k1_relat_1(sK2) != sK0 ),
% 1.51/0.98      inference(unflattening,[status(thm)],[c_329]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_438,plain,
% 1.51/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.51/0.98      | k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = sK1
% 1.51/0.98      | k1_relat_1(sK2) != sK0
% 1.51/0.98      | sK2 != X0 ),
% 1.51/0.98      inference(resolution_lifted,[status(thm)],[c_2,c_330]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_439,plain,
% 1.51/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.51/0.98      | k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = sK1
% 1.51/0.98      | k1_relat_1(sK2) != sK0 ),
% 1.51/0.98      inference(unflattening,[status(thm)],[c_438]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_600,plain,
% 1.51/0.98      ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = sK1
% 1.51/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 1.51/0.98      | k1_relat_1(sK2) != sK0
% 1.51/0.98      | sK2 != sK2 ),
% 1.51/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_439]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_738,plain,
% 1.51/0.98      ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = sK1
% 1.51/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 1.51/0.98      | k1_relat_1(sK2) != sK0 ),
% 1.51/0.98      inference(equality_resolution_simp,[status(thm)],[c_600]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_754,plain,
% 1.51/0.98      ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = sK1
% 1.51/0.98      | k1_relat_1(sK2) != sK0
% 1.51/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 1.51/0.98      inference(subtyping,[status(esa)],[c_738]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_765,plain,
% 1.51/0.98      ( sP0_iProver_split
% 1.51/0.98      | k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = sK1
% 1.51/0.98      | k1_relat_1(sK2) != sK0 ),
% 1.51/0.98      inference(splitting,
% 1.51/0.98                [splitting(split),new_symbols(definition,[])],
% 1.51/0.98                [c_754]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_850,plain,
% 1.51/0.98      ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = sK1
% 1.51/0.98      | k1_relat_1(sK2) != sK0
% 1.51/0.98      | sP0_iProver_split = iProver_top ),
% 1.51/0.98      inference(predicate_to_equality,[status(thm)],[c_765]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_0,plain,
% 1.51/0.98      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 1.51/0.98      | ~ v1_relat_1(X1)
% 1.51/0.98      | ~ v1_funct_1(X1)
% 1.51/0.98      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 1.51/0.98      inference(cnf_transformation,[],[f35]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_310,plain,
% 1.51/0.98      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 1.51/0.98      | ~ v1_relat_1(X1)
% 1.51/0.98      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
% 1.51/0.98      | sK2 != X1 ),
% 1.51/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_23]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_311,plain,
% 1.51/0.98      ( ~ r1_tarski(X0,k2_relat_1(sK2))
% 1.51/0.98      | ~ v1_relat_1(sK2)
% 1.51/0.98      | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ),
% 1.51/0.98      inference(unflattening,[status(thm)],[c_310]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_342,plain,
% 1.51/0.98      ( ~ v1_relat_1(sK2)
% 1.51/0.98      | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
% 1.51/0.98      | k2_relat_1(sK2) != sK0
% 1.51/0.98      | sK1 != X0 ),
% 1.51/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_311]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_343,plain,
% 1.51/0.98      ( ~ v1_relat_1(sK2)
% 1.51/0.98      | k9_relat_1(sK2,k10_relat_1(sK2,sK1)) = sK1
% 1.51/0.98      | k2_relat_1(sK2) != sK0 ),
% 1.51/0.98      inference(unflattening,[status(thm)],[c_342]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_423,plain,
% 1.51/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.51/0.98      | k9_relat_1(sK2,k10_relat_1(sK2,sK1)) = sK1
% 1.51/0.98      | k2_relat_1(sK2) != sK0
% 1.51/0.98      | sK2 != X0 ),
% 1.51/0.98      inference(resolution_lifted,[status(thm)],[c_2,c_343]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_424,plain,
% 1.51/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.51/0.98      | k9_relat_1(sK2,k10_relat_1(sK2,sK1)) = sK1
% 1.51/0.98      | k2_relat_1(sK2) != sK0 ),
% 1.51/0.98      inference(unflattening,[status(thm)],[c_423]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_614,plain,
% 1.51/0.98      ( k9_relat_1(sK2,k10_relat_1(sK2,sK1)) = sK1
% 1.51/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 1.51/0.98      | k2_relat_1(sK2) != sK0
% 1.51/0.98      | sK2 != sK2 ),
% 1.51/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_424]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_736,plain,
% 1.51/0.98      ( k9_relat_1(sK2,k10_relat_1(sK2,sK1)) = sK1
% 1.51/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 1.51/0.98      | k2_relat_1(sK2) != sK0 ),
% 1.51/0.98      inference(equality_resolution_simp,[status(thm)],[c_614]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_755,plain,
% 1.51/0.98      ( k9_relat_1(sK2,k10_relat_1(sK2,sK1)) = sK1
% 1.51/0.98      | k2_relat_1(sK2) != sK0
% 1.51/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 1.51/0.98      inference(subtyping,[status(esa)],[c_736]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_764,plain,
% 1.51/0.98      ( sP0_iProver_split
% 1.51/0.98      | k9_relat_1(sK2,k10_relat_1(sK2,sK1)) = sK1
% 1.51/0.98      | k2_relat_1(sK2) != sK0 ),
% 1.51/0.98      inference(splitting,
% 1.51/0.98                [splitting(split),new_symbols(definition,[])],
% 1.51/0.98                [c_755]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_798,plain,
% 1.51/0.98      ( k9_relat_1(sK2,k10_relat_1(sK2,sK1)) = sK1
% 1.51/0.98      | k2_relat_1(sK2) != sK0
% 1.51/0.98      | sP0_iProver_split = iProver_top ),
% 1.51/0.98      inference(predicate_to_equality,[status(thm)],[c_764]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_802,plain,
% 1.51/0.98      ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = sK1
% 1.51/0.98      | k1_relat_1(sK2) != sK0
% 1.51/0.98      | sP0_iProver_split = iProver_top ),
% 1.51/0.98      inference(predicate_to_equality,[status(thm)],[c_765]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_766,plain,( X0_50 = X0_50 ),theory(equality) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_917,plain,
% 1.51/0.98      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 1.51/0.98      inference(instantiation,[status(thm)],[c_766]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_3,plain,
% 1.51/0.98      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 1.51/0.98      inference(cnf_transformation,[],[f38]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_17,plain,
% 1.51/0.98      ( ~ v2_funct_2(X0,X1)
% 1.51/0.98      | ~ v5_relat_1(X0,X1)
% 1.51/0.98      | ~ v1_relat_1(X0)
% 1.51/0.98      | k2_relat_1(X0) = X1 ),
% 1.51/0.98      inference(cnf_transformation,[],[f51]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_363,plain,
% 1.51/0.98      ( ~ v2_funct_2(X0,X1)
% 1.51/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 1.51/0.98      | ~ v1_relat_1(X0)
% 1.51/0.98      | k2_relat_1(X0) = X1 ),
% 1.51/0.98      inference(resolution,[status(thm)],[c_3,c_17]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_375,plain,
% 1.51/0.98      ( ~ v2_funct_2(X0,X1)
% 1.51/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 1.51/0.98      | k2_relat_1(X0) = X1 ),
% 1.51/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_363,c_2]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_7,plain,
% 1.51/0.98      ( ~ v3_funct_2(X0,X1,X2)
% 1.51/0.98      | v2_funct_2(X0,X2)
% 1.51/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.51/0.98      | ~ v1_funct_1(X0) ),
% 1.51/0.98      inference(cnf_transformation,[],[f44]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_270,plain,
% 1.51/0.98      ( v2_funct_2(X0,X1)
% 1.51/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 1.51/0.98      | ~ v1_funct_1(X0)
% 1.51/0.98      | sK2 != X0
% 1.51/0.98      | sK0 != X1
% 1.51/0.98      | sK0 != X2 ),
% 1.51/0.98      inference(resolution_lifted,[status(thm)],[c_7,c_21]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_271,plain,
% 1.51/0.98      ( v2_funct_2(sK2,sK0)
% 1.51/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.51/0.98      | ~ v1_funct_1(sK2) ),
% 1.51/0.98      inference(unflattening,[status(thm)],[c_270]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_273,plain,
% 1.51/0.98      ( v2_funct_2(sK2,sK0) ),
% 1.51/0.98      inference(global_propositional_subsumption,
% 1.51/0.98                [status(thm)],
% 1.51/0.98                [c_271,c_23,c_20]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_408,plain,
% 1.51/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.51/0.98      | k2_relat_1(X0) = X2
% 1.51/0.98      | sK2 != X0
% 1.51/0.98      | sK0 != X2 ),
% 1.51/0.98      inference(resolution_lifted,[status(thm)],[c_375,c_273]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_409,plain,
% 1.51/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
% 1.51/0.98      | k2_relat_1(sK2) = sK0 ),
% 1.51/0.98      inference(unflattening,[status(thm)],[c_408]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_589,plain,
% 1.51/0.98      ( k1_zfmisc_1(k2_zfmisc_1(X0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 1.51/0.98      | k2_relat_1(sK2) = sK0
% 1.51/0.98      | sK2 != sK2 ),
% 1.51/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_409]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_740,plain,
% 1.51/0.98      ( k1_zfmisc_1(k2_zfmisc_1(X0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 1.51/0.98      | k2_relat_1(sK2) = sK0 ),
% 1.51/0.98      inference(equality_resolution_simp,[status(thm)],[c_589]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_753,plain,
% 1.51/0.98      ( k2_relat_1(sK2) = sK0
% 1.51/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0_52,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 1.51/0.98      inference(subtyping,[status(esa)],[c_740]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_918,plain,
% 1.51/0.98      ( k2_relat_1(sK2) = sK0
% 1.51/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 1.51/0.98      inference(instantiation,[status(thm)],[c_753]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_6,plain,
% 1.51/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.51/0.98      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 1.51/0.98      inference(cnf_transformation,[],[f41]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_497,plain,
% 1.51/0.98      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 1.51/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 1.51/0.98      | sK2 != X2 ),
% 1.51/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_20]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_498,plain,
% 1.51/0.98      ( k8_relset_1(X0,X1,sK2,X2) = k10_relat_1(sK2,X2)
% 1.51/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 1.51/0.98      inference(unflattening,[status(thm)],[c_497]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_761,plain,
% 1.51/0.98      ( k8_relset_1(X0_52,X1_52,sK2,X0_53) = k10_relat_1(sK2,X0_53)
% 1.51/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 1.51/0.98      inference(subtyping,[status(esa)],[c_498]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_939,plain,
% 1.51/0.98      ( k8_relset_1(sK0,sK0,sK2,X0_53) = k10_relat_1(sK2,X0_53) ),
% 1.51/0.98      inference(equality_resolution,[status(thm)],[c_761]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_5,plain,
% 1.51/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.51/0.98      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 1.51/0.98      inference(cnf_transformation,[],[f40]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_506,plain,
% 1.51/0.98      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 1.51/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 1.51/0.98      | sK2 != X2 ),
% 1.51/0.98      inference(resolution_lifted,[status(thm)],[c_5,c_20]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_507,plain,
% 1.51/0.98      ( k7_relset_1(X0,X1,sK2,X2) = k9_relat_1(sK2,X2)
% 1.51/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 1.51/0.98      inference(unflattening,[status(thm)],[c_506]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_760,plain,
% 1.51/0.98      ( k7_relset_1(X0_52,X1_52,sK2,X0_53) = k9_relat_1(sK2,X0_53)
% 1.51/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 1.51/0.98      inference(subtyping,[status(esa)],[c_507]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_935,plain,
% 1.51/0.98      ( k7_relset_1(sK0,sK0,sK2,X0_53) = k9_relat_1(sK2,X0_53) ),
% 1.51/0.98      inference(equality_resolution,[status(thm)],[c_760]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_18,negated_conjecture,
% 1.51/0.98      ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
% 1.51/0.98      | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
% 1.51/0.98      inference(cnf_transformation,[],[f58]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_762,negated_conjecture,
% 1.51/0.98      ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
% 1.51/0.98      | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
% 1.51/0.98      inference(subtyping,[status(esa)],[c_18]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_987,plain,
% 1.51/0.98      ( k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1)) != sK1
% 1.51/0.98      | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
% 1.51/0.98      inference(demodulation,[status(thm)],[c_935,c_762]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_988,plain,
% 1.51/0.98      ( k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1)) != sK1
% 1.51/0.98      | k9_relat_1(sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
% 1.51/0.98      inference(demodulation,[status(thm)],[c_987,c_935]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_1052,plain,
% 1.51/0.98      ( k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1)) != sK1
% 1.51/0.98      | k9_relat_1(sK2,k10_relat_1(sK2,sK1)) != sK1 ),
% 1.51/0.98      inference(demodulation,[status(thm)],[c_939,c_988]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_1053,plain,
% 1.51/0.98      ( k9_relat_1(sK2,k10_relat_1(sK2,sK1)) != sK1
% 1.51/0.98      | k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != sK1 ),
% 1.51/0.98      inference(demodulation,[status(thm)],[c_1052,c_939]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_763,plain,
% 1.51/0.98      ( k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 1.51/0.98      | ~ sP0_iProver_split ),
% 1.51/0.98      inference(splitting,
% 1.51/0.98                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.51/0.98                [c_755]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_849,plain,
% 1.51/0.98      ( k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 1.51/0.98      | sP0_iProver_split != iProver_top ),
% 1.51/0.98      inference(predicate_to_equality,[status(thm)],[c_763]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_1099,plain,
% 1.51/0.98      ( sP0_iProver_split != iProver_top ),
% 1.51/0.98      inference(equality_resolution,[status(thm)],[c_849]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_1158,plain,
% 1.51/0.98      ( k1_relat_1(sK2) != sK0 ),
% 1.51/0.98      inference(global_propositional_subsumption,
% 1.51/0.98                [status(thm)],
% 1.51/0.98                [c_850,c_798,c_802,c_917,c_918,c_1053,c_1099]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_1161,plain,
% 1.51/0.98      ( sK0 = k1_xboole_0 ),
% 1.51/0.98      inference(superposition,[status(thm)],[c_1054,c_1158]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_1191,plain,
% 1.51/0.98      ( k1_relat_1(sK2) != k1_xboole_0 ),
% 1.51/0.98      inference(demodulation,[status(thm)],[c_1161,c_1158]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_1197,plain,
% 1.51/0.98      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k1_relat_1(sK2) ),
% 1.51/0.98      inference(demodulation,[status(thm)],[c_1161,c_916]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_14,plain,
% 1.51/0.98      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 1.51/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.51/0.98      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 1.51/0.98      inference(cnf_transformation,[],[f63]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_559,plain,
% 1.51/0.98      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 1.51/0.98      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 1.51/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 1.51/0.98      | sK2 != X0 ),
% 1.51/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_20]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_560,plain,
% 1.51/0.98      ( ~ v1_funct_2(sK2,k1_xboole_0,X0)
% 1.51/0.98      | k1_relset_1(k1_xboole_0,X0,sK2) = k1_xboole_0
% 1.51/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 1.51/0.98      inference(unflattening,[status(thm)],[c_559]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_706,plain,
% 1.51/0.98      ( k1_relset_1(k1_xboole_0,X0,sK2) = k1_xboole_0
% 1.51/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 1.51/0.98      | sK2 != sK2
% 1.51/0.98      | sK0 != X0
% 1.51/0.98      | sK0 != k1_xboole_0 ),
% 1.51/0.98      inference(resolution_lifted,[status(thm)],[c_22,c_560]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_707,plain,
% 1.51/0.98      ( k1_relset_1(k1_xboole_0,sK0,sK2) = k1_xboole_0
% 1.51/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 1.51/0.98      | sK0 != k1_xboole_0 ),
% 1.51/0.98      inference(unflattening,[status(thm)],[c_706]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_757,plain,
% 1.51/0.98      ( k1_relset_1(k1_xboole_0,sK0,sK2) = k1_xboole_0
% 1.51/0.98      | sK0 != k1_xboole_0
% 1.51/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 1.51/0.98      inference(subtyping,[status(esa)],[c_707]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_1199,plain,
% 1.51/0.98      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k1_xboole_0
% 1.51/0.98      | k1_xboole_0 != k1_xboole_0
% 1.51/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
% 1.51/0.98      inference(demodulation,[status(thm)],[c_1161,c_757]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_1215,plain,
% 1.51/0.98      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k1_xboole_0 ),
% 1.51/0.98      inference(equality_resolution_simp,[status(thm)],[c_1199]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_1218,plain,
% 1.51/0.98      ( k1_relat_1(sK2) = k1_xboole_0 ),
% 1.51/0.98      inference(light_normalisation,[status(thm)],[c_1197,c_1215]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_1232,plain,
% 1.51/0.98      ( k1_xboole_0 != k1_xboole_0 ),
% 1.51/0.98      inference(light_normalisation,[status(thm)],[c_1191,c_1218]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_1233,plain,
% 1.51/0.98      ( $false ),
% 1.51/0.98      inference(equality_resolution_simp,[status(thm)],[c_1232]) ).
% 1.51/0.98  
% 1.51/0.98  
% 1.51/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 1.51/0.98  
% 1.51/0.98  ------                               Statistics
% 1.51/0.98  
% 1.51/0.98  ------ General
% 1.51/0.98  
% 1.51/0.98  abstr_ref_over_cycles:                  0
% 1.51/0.98  abstr_ref_under_cycles:                 0
% 1.51/0.98  gc_basic_clause_elim:                   0
% 1.51/0.98  forced_gc_time:                         0
% 1.51/0.98  parsing_time:                           0.01
% 1.51/0.98  unif_index_cands_time:                  0.
% 1.51/0.98  unif_index_add_time:                    0.
% 1.51/0.98  orderings_time:                         0.
% 1.51/0.98  out_proof_time:                         0.01
% 1.51/0.98  total_time:                             0.074
% 1.51/0.98  num_of_symbols:                         55
% 1.51/0.98  num_of_terms:                           1451
% 1.51/0.98  
% 1.51/0.98  ------ Preprocessing
% 1.51/0.98  
% 1.51/0.98  num_of_splits:                          2
% 1.51/0.98  num_of_split_atoms:                     1
% 1.51/0.98  num_of_reused_defs:                     1
% 1.51/0.98  num_eq_ax_congr_red:                    10
% 1.51/0.98  num_of_sem_filtered_clauses:            0
% 1.51/0.98  num_of_subtypes:                        4
% 1.51/0.98  monotx_restored_types:                  0
% 1.51/0.98  sat_num_of_epr_types:                   0
% 1.51/0.98  sat_num_of_non_cyclic_types:            0
% 1.51/0.98  sat_guarded_non_collapsed_types:        0
% 1.51/0.98  num_pure_diseq_elim:                    0
% 1.51/0.98  simp_replaced_by:                       0
% 1.51/0.98  res_preprocessed:                       87
% 1.51/0.98  prep_upred:                             0
% 1.51/0.98  prep_unflattend:                        43
% 1.51/0.98  smt_new_axioms:                         0
% 1.51/0.98  pred_elim_cands:                        0
% 1.51/0.98  pred_elim:                              9
% 1.51/0.98  pred_elim_cl:                           13
% 1.51/0.98  pred_elim_cycles:                       10
% 1.51/0.98  merged_defs:                            0
% 1.51/0.98  merged_defs_ncl:                        0
% 1.51/0.98  bin_hyper_res:                          0
% 1.51/0.98  prep_cycles:                            4
% 1.51/0.98  pred_elim_time:                         0.008
% 1.51/0.98  splitting_time:                         0.
% 1.51/0.98  sem_filter_time:                        0.
% 1.51/0.98  monotx_time:                            0.
% 1.51/0.98  subtype_inf_time:                       0.
% 1.51/0.98  
% 1.51/0.98  ------ Problem properties
% 1.51/0.98  
% 1.51/0.98  clauses:                                12
% 1.51/0.98  conjectures:                            1
% 1.51/0.98  epr:                                    0
% 1.51/0.98  horn:                                   8
% 1.51/0.98  ground:                                 6
% 1.51/0.98  unary:                                  0
% 1.51/0.98  binary:                                 8
% 1.51/0.98  lits:                                   29
% 1.51/0.98  lits_eq:                                25
% 1.51/0.98  fd_pure:                                0
% 1.51/0.98  fd_pseudo:                              0
% 1.51/0.98  fd_cond:                                0
% 1.51/0.98  fd_pseudo_cond:                         0
% 1.51/0.98  ac_symbols:                             0
% 1.51/0.98  
% 1.51/0.98  ------ Propositional Solver
% 1.51/0.98  
% 1.51/0.98  prop_solver_calls:                      25
% 1.51/0.98  prop_fast_solver_calls:                 581
% 1.51/0.98  smt_solver_calls:                       0
% 1.51/0.98  smt_fast_solver_calls:                  0
% 1.51/0.98  prop_num_of_clauses:                    360
% 1.51/0.98  prop_preprocess_simplified:             1858
% 1.51/0.98  prop_fo_subsumed:                       11
% 1.51/0.98  prop_solver_time:                       0.
% 1.51/0.98  smt_solver_time:                        0.
% 1.51/0.98  smt_fast_solver_time:                   0.
% 1.51/0.98  prop_fast_solver_time:                  0.
% 1.51/0.98  prop_unsat_core_time:                   0.
% 1.51/0.98  
% 1.51/0.98  ------ QBF
% 1.51/0.98  
% 1.51/0.98  qbf_q_res:                              0
% 1.51/0.98  qbf_num_tautologies:                    0
% 1.51/0.98  qbf_prep_cycles:                        0
% 1.51/0.98  
% 1.51/0.98  ------ BMC1
% 1.51/0.98  
% 1.51/0.98  bmc1_current_bound:                     -1
% 1.51/0.98  bmc1_last_solved_bound:                 -1
% 1.51/0.98  bmc1_unsat_core_size:                   -1
% 1.51/0.98  bmc1_unsat_core_parents_size:           -1
% 1.51/0.98  bmc1_merge_next_fun:                    0
% 1.51/0.98  bmc1_unsat_core_clauses_time:           0.
% 1.51/0.98  
% 1.51/0.98  ------ Instantiation
% 1.51/0.98  
% 1.51/0.98  inst_num_of_clauses:                    109
% 1.51/0.98  inst_num_in_passive:                    27
% 1.51/0.98  inst_num_in_active:                     79
% 1.51/0.98  inst_num_in_unprocessed:                3
% 1.51/0.98  inst_num_of_loops:                      90
% 1.51/0.98  inst_num_of_learning_restarts:          0
% 1.51/0.98  inst_num_moves_active_passive:          8
% 1.51/0.98  inst_lit_activity:                      0
% 1.51/0.98  inst_lit_activity_moves:                0
% 1.51/0.98  inst_num_tautologies:                   0
% 1.51/0.98  inst_num_prop_implied:                  0
% 1.51/0.98  inst_num_existing_simplified:           0
% 1.51/0.98  inst_num_eq_res_simplified:             0
% 1.51/0.98  inst_num_child_elim:                    0
% 1.51/0.98  inst_num_of_dismatching_blockings:      9
% 1.51/0.98  inst_num_of_non_proper_insts:           90
% 1.51/0.98  inst_num_of_duplicates:                 0
% 1.51/0.98  inst_inst_num_from_inst_to_res:         0
% 1.51/0.98  inst_dismatching_checking_time:         0.
% 1.51/0.98  
% 1.51/0.98  ------ Resolution
% 1.51/0.98  
% 1.51/0.98  res_num_of_clauses:                     0
% 1.51/0.98  res_num_in_passive:                     0
% 1.51/0.98  res_num_in_active:                      0
% 1.51/0.98  res_num_of_loops:                       91
% 1.51/0.98  res_forward_subset_subsumed:            13
% 1.51/0.98  res_backward_subset_subsumed:           0
% 1.51/0.98  res_forward_subsumed:                   0
% 1.51/0.98  res_backward_subsumed:                  0
% 1.51/0.98  res_forward_subsumption_resolution:     2
% 1.51/0.98  res_backward_subsumption_resolution:    0
% 1.51/0.98  res_clause_to_clause_subsumption:       22
% 1.51/0.98  res_orphan_elimination:                 0
% 1.51/0.98  res_tautology_del:                      23
% 1.51/0.98  res_num_eq_res_simplified:              4
% 1.51/0.98  res_num_sel_changes:                    0
% 1.51/0.98  res_moves_from_active_to_pass:          0
% 1.51/0.98  
% 1.51/0.98  ------ Superposition
% 1.51/0.98  
% 1.51/0.98  sup_time_total:                         0.
% 1.51/0.98  sup_time_generating:                    0.
% 1.51/0.98  sup_time_sim_full:                      0.
% 1.51/0.98  sup_time_sim_immed:                     0.
% 1.51/0.98  
% 1.51/0.98  sup_num_of_clauses:                     4
% 1.51/0.98  sup_num_in_active:                      2
% 1.51/0.98  sup_num_in_passive:                     2
% 1.51/0.98  sup_num_of_loops:                       16
% 1.51/0.98  sup_fw_superposition:                   1
% 1.51/0.98  sup_bw_superposition:                   0
% 1.51/0.98  sup_immediate_simplified:               2
% 1.51/0.98  sup_given_eliminated:                   0
% 1.51/0.98  comparisons_done:                       0
% 1.51/0.98  comparisons_avoided:                    0
% 1.51/0.98  
% 1.51/0.98  ------ Simplifications
% 1.51/0.98  
% 1.51/0.98  
% 1.51/0.98  sim_fw_subset_subsumed:                 1
% 1.51/0.98  sim_bw_subset_subsumed:                 0
% 1.51/0.98  sim_fw_subsumed:                        0
% 1.51/0.98  sim_bw_subsumed:                        0
% 1.51/0.98  sim_fw_subsumption_res:                 0
% 1.51/0.98  sim_bw_subsumption_res:                 0
% 1.51/0.98  sim_tautology_del:                      1
% 1.51/0.98  sim_eq_tautology_del:                   1
% 1.51/0.98  sim_eq_res_simp:                        1
% 1.51/0.98  sim_fw_demodulated:                     3
% 1.51/0.98  sim_bw_demodulated:                     15
% 1.51/0.98  sim_light_normalised:                   2
% 1.51/0.98  sim_joinable_taut:                      0
% 1.51/0.98  sim_joinable_simp:                      0
% 1.51/0.98  sim_ac_normalised:                      0
% 1.51/0.98  sim_smt_subsumption:                    0
% 1.51/0.98  
%------------------------------------------------------------------------------
