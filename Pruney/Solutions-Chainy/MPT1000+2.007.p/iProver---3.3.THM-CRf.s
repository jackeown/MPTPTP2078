%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:19 EST 2020

% Result     : Theorem 7.53s
% Output     : CNFRefutation 7.53s
% Verified   : 
% Statistics : Number of formulae       :  169 (1845 expanded)
%              Number of clauses        :  106 ( 716 expanded)
%              Number of leaves         :   20 ( 326 expanded)
%              Depth                    :   26
%              Number of atoms          :  432 (6192 expanded)
%              Number of equality atoms :  257 (3104 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,axiom,(
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

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f23,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f38,plain,(
    ? [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) != X0
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f39,plain,(
    ? [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) != X0
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f51,plain,
    ( ? [X0,X1,X2] :
        ( k8_relset_1(X0,X1,X2,X1) != X0
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1) )
   => ( k8_relset_1(sK2,sK3,sK4,sK3) != sK2
      & ( k1_xboole_0 = sK2
        | k1_xboole_0 != sK3 )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK4,sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( k8_relset_1(sK2,sK3,sK4,sK3) != sK2
    & ( k1_xboole_0 = sK2
      | k1_xboole_0 != sK3 )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f39,f51])).

fof(f82,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f83,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f52])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f72,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f85,plain,(
    k8_relset_1(sK2,sK3,sK4,sK3) != sK2 ),
    inference(cnf_transformation,[],[f52])).

fof(f84,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f52])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f90,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f77])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f59,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f88,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f80])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1106,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK3 != X2
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_32])).

cnf(c_1107,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_1106])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1109,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1107,c_31])).

cnf(c_2522,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2524,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3664,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2522,c_2524])).

cnf(c_3837,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1109,c_3664])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2530,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3282,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2522,c_2530])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_240,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_241,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_240])).

cnf(c_298,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_241])).

cnf(c_2521,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_298])).

cnf(c_17834,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3282,c_2521])).

cnf(c_14,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2528,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_18101,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_17834,c_2528])).

cnf(c_20,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_12,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_403,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_20,c_12])).

cnf(c_2520,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_403])).

cnf(c_2854,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2522,c_2520])).

cnf(c_18,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2526,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3820,plain,
    ( k5_relat_1(sK4,k6_relat_1(sK3)) = sK4
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2854,c_2526])).

cnf(c_18123,plain,
    ( k5_relat_1(sK4,k6_relat_1(sK3)) = sK4 ),
    inference(superposition,[status(thm)],[c_18101,c_3820])).

cnf(c_19,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2525,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2527,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_18105,plain,
    ( k10_relat_1(sK4,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK4,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_18101,c_2527])).

cnf(c_19346,plain,
    ( k10_relat_1(sK4,k1_relat_1(k6_relat_1(X0))) = k1_relat_1(k5_relat_1(sK4,k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_2525,c_18105])).

cnf(c_17,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_19360,plain,
    ( k1_relat_1(k5_relat_1(sK4,k6_relat_1(X0))) = k10_relat_1(sK4,X0) ),
    inference(light_normalisation,[status(thm)],[c_19346,c_17])).

cnf(c_19597,plain,
    ( k10_relat_1(sK4,sK3) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_18123,c_19360])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2523,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3212,plain,
    ( k8_relset_1(sK2,sK3,sK4,X0) = k10_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_2522,c_2523])).

cnf(c_29,negated_conjecture,
    ( k8_relset_1(sK2,sK3,sK4,sK3) != sK2 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_3471,plain,
    ( k10_relat_1(sK4,sK3) != sK2 ),
    inference(demodulation,[status(thm)],[c_3212,c_29])).

cnf(c_19703,plain,
    ( k1_relat_1(sK4) != sK2 ),
    inference(demodulation,[status(thm)],[c_19597,c_3471])).

cnf(c_19705,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3837,c_19703])).

cnf(c_19791,plain,
    ( k10_relat_1(sK4,k1_xboole_0) = k1_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_19705,c_19597])).

cnf(c_19949,plain,
    ( k1_relset_1(sK2,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_19705,c_3664])).

cnf(c_30,negated_conjecture,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_19957,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_19705,c_30])).

cnf(c_19958,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_19957])).

cnf(c_19984,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_19949,c_19958])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1093,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK4 != X0
    | sK3 != X1
    | sK2 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_32])).

cnf(c_1094,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
    | k1_relset_1(k1_xboole_0,sK3,sK4) = k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_1093])).

cnf(c_2518,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) = k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1094])).

cnf(c_19954,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19705,c_2518])).

cnf(c_19965,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19954,c_19958])).

cnf(c_19966,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_19965])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2534,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2532,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2533,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3144,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2532,c_2533])).

cnf(c_3502,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2534,c_3144])).

cnf(c_19969,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19966,c_3502])).

cnf(c_19986,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19984,c_19969])).

cnf(c_19956,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_19705,c_2522])).

cnf(c_19961,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19956,c_19958])).

cnf(c_19963,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_19961,c_3502])).

cnf(c_19990,plain,
    ( k1_relat_1(sK4) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_19986,c_19963])).

cnf(c_20825,plain,
    ( k10_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_19791,c_19990])).

cnf(c_1949,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2792,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_1949])).

cnf(c_7664,plain,
    ( k10_relat_1(sK4,X0) != X1
    | sK2 != X1
    | sK2 = k10_relat_1(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_2792])).

cnf(c_7665,plain,
    ( k10_relat_1(sK4,k1_xboole_0) != k1_xboole_0
    | sK2 = k10_relat_1(sK4,k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7664])).

cnf(c_1960,plain,
    ( X0 != X1
    | k10_relat_1(X2,X0) = k10_relat_1(X2,X1) ),
    theory(equality)).

cnf(c_4103,plain,
    ( k10_relat_1(sK4,sK3) = k10_relat_1(sK4,X0)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1960])).

cnf(c_4105,plain,
    ( k10_relat_1(sK4,sK3) = k10_relat_1(sK4,k1_xboole_0)
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4103])).

cnf(c_3171,plain,
    ( k10_relat_1(sK4,sK3) != X0
    | sK2 != X0
    | sK2 = k10_relat_1(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_2792])).

cnf(c_4102,plain,
    ( k10_relat_1(sK4,sK3) != k10_relat_1(sK4,X0)
    | sK2 != k10_relat_1(sK4,X0)
    | sK2 = k10_relat_1(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_3171])).

cnf(c_4104,plain,
    ( k10_relat_1(sK4,sK3) != k10_relat_1(sK4,k1_xboole_0)
    | sK2 = k10_relat_1(sK4,sK3)
    | sK2 != k10_relat_1(sK4,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4102])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1073,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK4 != X0
    | sK3 != k1_xboole_0
    | sK2 != X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_32])).

cnf(c_1074,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | sK3 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_1073])).

cnf(c_2519,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK2
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1074])).

cnf(c_3523,plain,
    ( sK4 = k1_xboole_0
    | sK3 != k1_xboole_0
    | sK2 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3502,c_2519])).

cnf(c_96,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2728,plain,
    ( sK2 != X0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1949])).

cnf(c_2793,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_2728])).

cnf(c_1948,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2794,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1948])).

cnf(c_3496,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_1949])).

cnf(c_3497,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3496])).

cnf(c_3615,plain,
    ( sK2 = k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3523,c_30,c_96,c_5,c_2793,c_2794,c_3497])).

cnf(c_3616,plain,
    ( sK3 != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3615])).

cnf(c_2773,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k8_relset_1(sK2,sK3,sK4,X0) = k10_relat_1(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2979,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k8_relset_1(sK2,sK3,sK4,sK3) = k10_relat_1(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_2773])).

cnf(c_2726,plain,
    ( k8_relset_1(sK2,sK3,sK4,sK3) != X0
    | k8_relset_1(sK2,sK3,sK4,sK3) = sK2
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_1949])).

cnf(c_2978,plain,
    ( k8_relset_1(sK2,sK3,sK4,sK3) != k10_relat_1(sK4,sK3)
    | k8_relset_1(sK2,sK3,sK4,sK3) = sK2
    | sK2 != k10_relat_1(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_2726])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_20825,c_19703,c_7665,c_4105,c_4104,c_3837,c_3616,c_2979,c_2978,c_29,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:52:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.53/1.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.53/1.51  
% 7.53/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.53/1.51  
% 7.53/1.51  ------  iProver source info
% 7.53/1.51  
% 7.53/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.53/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.53/1.51  git: non_committed_changes: false
% 7.53/1.51  git: last_make_outside_of_git: false
% 7.53/1.51  
% 7.53/1.51  ------ 
% 7.53/1.51  
% 7.53/1.51  ------ Input Options
% 7.53/1.51  
% 7.53/1.51  --out_options                           all
% 7.53/1.51  --tptp_safe_out                         true
% 7.53/1.51  --problem_path                          ""
% 7.53/1.51  --include_path                          ""
% 7.53/1.51  --clausifier                            res/vclausify_rel
% 7.53/1.51  --clausifier_options                    --mode clausify
% 7.53/1.51  --stdin                                 false
% 7.53/1.51  --stats_out                             all
% 7.53/1.51  
% 7.53/1.51  ------ General Options
% 7.53/1.51  
% 7.53/1.51  --fof                                   false
% 7.53/1.51  --time_out_real                         305.
% 7.53/1.51  --time_out_virtual                      -1.
% 7.53/1.51  --symbol_type_check                     false
% 7.53/1.51  --clausify_out                          false
% 7.53/1.51  --sig_cnt_out                           false
% 7.53/1.51  --trig_cnt_out                          false
% 7.53/1.51  --trig_cnt_out_tolerance                1.
% 7.53/1.51  --trig_cnt_out_sk_spl                   false
% 7.53/1.51  --abstr_cl_out                          false
% 7.53/1.51  
% 7.53/1.51  ------ Global Options
% 7.53/1.51  
% 7.53/1.51  --schedule                              default
% 7.53/1.51  --add_important_lit                     false
% 7.53/1.51  --prop_solver_per_cl                    1000
% 7.53/1.51  --min_unsat_core                        false
% 7.53/1.51  --soft_assumptions                      false
% 7.53/1.51  --soft_lemma_size                       3
% 7.53/1.51  --prop_impl_unit_size                   0
% 7.53/1.51  --prop_impl_unit                        []
% 7.53/1.51  --share_sel_clauses                     true
% 7.53/1.51  --reset_solvers                         false
% 7.53/1.51  --bc_imp_inh                            [conj_cone]
% 7.53/1.51  --conj_cone_tolerance                   3.
% 7.53/1.51  --extra_neg_conj                        none
% 7.53/1.51  --large_theory_mode                     true
% 7.53/1.51  --prolific_symb_bound                   200
% 7.53/1.51  --lt_threshold                          2000
% 7.53/1.51  --clause_weak_htbl                      true
% 7.53/1.51  --gc_record_bc_elim                     false
% 7.53/1.51  
% 7.53/1.51  ------ Preprocessing Options
% 7.53/1.51  
% 7.53/1.51  --preprocessing_flag                    true
% 7.53/1.51  --time_out_prep_mult                    0.1
% 7.53/1.51  --splitting_mode                        input
% 7.53/1.51  --splitting_grd                         true
% 7.53/1.51  --splitting_cvd                         false
% 7.53/1.51  --splitting_cvd_svl                     false
% 7.53/1.51  --splitting_nvd                         32
% 7.53/1.51  --sub_typing                            true
% 7.53/1.51  --prep_gs_sim                           true
% 7.53/1.51  --prep_unflatten                        true
% 7.53/1.51  --prep_res_sim                          true
% 7.53/1.51  --prep_upred                            true
% 7.53/1.51  --prep_sem_filter                       exhaustive
% 7.53/1.51  --prep_sem_filter_out                   false
% 7.53/1.51  --pred_elim                             true
% 7.53/1.51  --res_sim_input                         true
% 7.53/1.51  --eq_ax_congr_red                       true
% 7.53/1.51  --pure_diseq_elim                       true
% 7.53/1.51  --brand_transform                       false
% 7.53/1.51  --non_eq_to_eq                          false
% 7.53/1.51  --prep_def_merge                        true
% 7.53/1.51  --prep_def_merge_prop_impl              false
% 7.53/1.51  --prep_def_merge_mbd                    true
% 7.53/1.51  --prep_def_merge_tr_red                 false
% 7.53/1.51  --prep_def_merge_tr_cl                  false
% 7.53/1.51  --smt_preprocessing                     true
% 7.53/1.51  --smt_ac_axioms                         fast
% 7.53/1.51  --preprocessed_out                      false
% 7.53/1.51  --preprocessed_stats                    false
% 7.53/1.51  
% 7.53/1.51  ------ Abstraction refinement Options
% 7.53/1.51  
% 7.53/1.51  --abstr_ref                             []
% 7.53/1.51  --abstr_ref_prep                        false
% 7.53/1.51  --abstr_ref_until_sat                   false
% 7.53/1.51  --abstr_ref_sig_restrict                funpre
% 7.53/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.53/1.51  --abstr_ref_under                       []
% 7.53/1.51  
% 7.53/1.51  ------ SAT Options
% 7.53/1.51  
% 7.53/1.51  --sat_mode                              false
% 7.53/1.51  --sat_fm_restart_options                ""
% 7.53/1.51  --sat_gr_def                            false
% 7.53/1.51  --sat_epr_types                         true
% 7.53/1.51  --sat_non_cyclic_types                  false
% 7.53/1.51  --sat_finite_models                     false
% 7.53/1.51  --sat_fm_lemmas                         false
% 7.53/1.51  --sat_fm_prep                           false
% 7.53/1.51  --sat_fm_uc_incr                        true
% 7.53/1.51  --sat_out_model                         small
% 7.53/1.51  --sat_out_clauses                       false
% 7.53/1.51  
% 7.53/1.51  ------ QBF Options
% 7.53/1.51  
% 7.53/1.51  --qbf_mode                              false
% 7.53/1.51  --qbf_elim_univ                         false
% 7.53/1.51  --qbf_dom_inst                          none
% 7.53/1.51  --qbf_dom_pre_inst                      false
% 7.53/1.51  --qbf_sk_in                             false
% 7.53/1.51  --qbf_pred_elim                         true
% 7.53/1.51  --qbf_split                             512
% 7.53/1.51  
% 7.53/1.51  ------ BMC1 Options
% 7.53/1.51  
% 7.53/1.51  --bmc1_incremental                      false
% 7.53/1.51  --bmc1_axioms                           reachable_all
% 7.53/1.51  --bmc1_min_bound                        0
% 7.53/1.51  --bmc1_max_bound                        -1
% 7.53/1.51  --bmc1_max_bound_default                -1
% 7.53/1.51  --bmc1_symbol_reachability              true
% 7.53/1.51  --bmc1_property_lemmas                  false
% 7.53/1.51  --bmc1_k_induction                      false
% 7.53/1.51  --bmc1_non_equiv_states                 false
% 7.53/1.51  --bmc1_deadlock                         false
% 7.53/1.51  --bmc1_ucm                              false
% 7.53/1.51  --bmc1_add_unsat_core                   none
% 7.53/1.51  --bmc1_unsat_core_children              false
% 7.53/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.53/1.51  --bmc1_out_stat                         full
% 7.53/1.51  --bmc1_ground_init                      false
% 7.53/1.51  --bmc1_pre_inst_next_state              false
% 7.53/1.51  --bmc1_pre_inst_state                   false
% 7.53/1.51  --bmc1_pre_inst_reach_state             false
% 7.53/1.51  --bmc1_out_unsat_core                   false
% 7.53/1.51  --bmc1_aig_witness_out                  false
% 7.53/1.51  --bmc1_verbose                          false
% 7.53/1.51  --bmc1_dump_clauses_tptp                false
% 7.53/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.53/1.51  --bmc1_dump_file                        -
% 7.53/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.53/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.53/1.51  --bmc1_ucm_extend_mode                  1
% 7.53/1.51  --bmc1_ucm_init_mode                    2
% 7.53/1.51  --bmc1_ucm_cone_mode                    none
% 7.53/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.53/1.51  --bmc1_ucm_relax_model                  4
% 7.53/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.53/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.53/1.51  --bmc1_ucm_layered_model                none
% 7.53/1.51  --bmc1_ucm_max_lemma_size               10
% 7.53/1.51  
% 7.53/1.51  ------ AIG Options
% 7.53/1.51  
% 7.53/1.51  --aig_mode                              false
% 7.53/1.51  
% 7.53/1.51  ------ Instantiation Options
% 7.53/1.51  
% 7.53/1.51  --instantiation_flag                    true
% 7.53/1.51  --inst_sos_flag                         false
% 7.53/1.51  --inst_sos_phase                        true
% 7.53/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.53/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.53/1.51  --inst_lit_sel_side                     num_symb
% 7.53/1.51  --inst_solver_per_active                1400
% 7.53/1.51  --inst_solver_calls_frac                1.
% 7.53/1.51  --inst_passive_queue_type               priority_queues
% 7.53/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.53/1.51  --inst_passive_queues_freq              [25;2]
% 7.53/1.51  --inst_dismatching                      true
% 7.53/1.51  --inst_eager_unprocessed_to_passive     true
% 7.53/1.51  --inst_prop_sim_given                   true
% 7.53/1.51  --inst_prop_sim_new                     false
% 7.53/1.51  --inst_subs_new                         false
% 7.53/1.51  --inst_eq_res_simp                      false
% 7.53/1.51  --inst_subs_given                       false
% 7.53/1.51  --inst_orphan_elimination               true
% 7.53/1.51  --inst_learning_loop_flag               true
% 7.53/1.51  --inst_learning_start                   3000
% 7.53/1.51  --inst_learning_factor                  2
% 7.53/1.51  --inst_start_prop_sim_after_learn       3
% 7.53/1.51  --inst_sel_renew                        solver
% 7.53/1.51  --inst_lit_activity_flag                true
% 7.53/1.51  --inst_restr_to_given                   false
% 7.53/1.51  --inst_activity_threshold               500
% 7.53/1.51  --inst_out_proof                        true
% 7.53/1.51  
% 7.53/1.51  ------ Resolution Options
% 7.53/1.51  
% 7.53/1.51  --resolution_flag                       true
% 7.53/1.51  --res_lit_sel                           adaptive
% 7.53/1.51  --res_lit_sel_side                      none
% 7.53/1.51  --res_ordering                          kbo
% 7.53/1.51  --res_to_prop_solver                    active
% 7.53/1.51  --res_prop_simpl_new                    false
% 7.53/1.51  --res_prop_simpl_given                  true
% 7.53/1.51  --res_passive_queue_type                priority_queues
% 7.53/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.53/1.51  --res_passive_queues_freq               [15;5]
% 7.53/1.51  --res_forward_subs                      full
% 7.53/1.51  --res_backward_subs                     full
% 7.53/1.51  --res_forward_subs_resolution           true
% 7.53/1.51  --res_backward_subs_resolution          true
% 7.53/1.51  --res_orphan_elimination                true
% 7.53/1.51  --res_time_limit                        2.
% 7.53/1.51  --res_out_proof                         true
% 7.53/1.51  
% 7.53/1.51  ------ Superposition Options
% 7.53/1.51  
% 7.53/1.51  --superposition_flag                    true
% 7.53/1.51  --sup_passive_queue_type                priority_queues
% 7.53/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.53/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.53/1.51  --demod_completeness_check              fast
% 7.53/1.51  --demod_use_ground                      true
% 7.53/1.51  --sup_to_prop_solver                    passive
% 7.53/1.51  --sup_prop_simpl_new                    true
% 7.53/1.51  --sup_prop_simpl_given                  true
% 7.53/1.51  --sup_fun_splitting                     false
% 7.53/1.51  --sup_smt_interval                      50000
% 7.53/1.51  
% 7.53/1.51  ------ Superposition Simplification Setup
% 7.53/1.51  
% 7.53/1.51  --sup_indices_passive                   []
% 7.53/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.53/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.53/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.53/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.53/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.53/1.51  --sup_full_bw                           [BwDemod]
% 7.53/1.51  --sup_immed_triv                        [TrivRules]
% 7.53/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.53/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.53/1.51  --sup_immed_bw_main                     []
% 7.53/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.53/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.53/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.53/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.53/1.51  
% 7.53/1.51  ------ Combination Options
% 7.53/1.51  
% 7.53/1.51  --comb_res_mult                         3
% 7.53/1.51  --comb_sup_mult                         2
% 7.53/1.51  --comb_inst_mult                        10
% 7.53/1.51  
% 7.53/1.51  ------ Debug Options
% 7.53/1.51  
% 7.53/1.51  --dbg_backtrace                         false
% 7.53/1.51  --dbg_dump_prop_clauses                 false
% 7.53/1.51  --dbg_dump_prop_clauses_file            -
% 7.53/1.51  --dbg_out_stat                          false
% 7.53/1.51  ------ Parsing...
% 7.53/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.53/1.51  
% 7.53/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.53/1.51  
% 7.53/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.53/1.51  
% 7.53/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.53/1.51  ------ Proving...
% 7.53/1.51  ------ Problem Properties 
% 7.53/1.51  
% 7.53/1.51  
% 7.53/1.51  clauses                                 27
% 7.53/1.51  conjectures                             3
% 7.53/1.51  EPR                                     6
% 7.53/1.51  Horn                                    23
% 7.53/1.51  unary                                   7
% 7.53/1.51  binary                                  13
% 7.53/1.51  lits                                    55
% 7.53/1.51  lits eq                                 17
% 7.53/1.51  fd_pure                                 0
% 7.53/1.51  fd_pseudo                               0
% 7.53/1.51  fd_cond                                 1
% 7.53/1.51  fd_pseudo_cond                          0
% 7.53/1.51  AC symbols                              0
% 7.53/1.51  
% 7.53/1.51  ------ Schedule dynamic 5 is on 
% 7.53/1.51  
% 7.53/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.53/1.51  
% 7.53/1.51  
% 7.53/1.51  ------ 
% 7.53/1.51  Current options:
% 7.53/1.51  ------ 
% 7.53/1.51  
% 7.53/1.51  ------ Input Options
% 7.53/1.51  
% 7.53/1.51  --out_options                           all
% 7.53/1.51  --tptp_safe_out                         true
% 7.53/1.51  --problem_path                          ""
% 7.53/1.51  --include_path                          ""
% 7.53/1.51  --clausifier                            res/vclausify_rel
% 7.53/1.51  --clausifier_options                    --mode clausify
% 7.53/1.51  --stdin                                 false
% 7.53/1.51  --stats_out                             all
% 7.53/1.51  
% 7.53/1.51  ------ General Options
% 7.53/1.51  
% 7.53/1.51  --fof                                   false
% 7.53/1.51  --time_out_real                         305.
% 7.53/1.51  --time_out_virtual                      -1.
% 7.53/1.51  --symbol_type_check                     false
% 7.53/1.51  --clausify_out                          false
% 7.53/1.51  --sig_cnt_out                           false
% 7.53/1.51  --trig_cnt_out                          false
% 7.53/1.51  --trig_cnt_out_tolerance                1.
% 7.53/1.51  --trig_cnt_out_sk_spl                   false
% 7.53/1.51  --abstr_cl_out                          false
% 7.53/1.51  
% 7.53/1.51  ------ Global Options
% 7.53/1.51  
% 7.53/1.51  --schedule                              default
% 7.53/1.51  --add_important_lit                     false
% 7.53/1.51  --prop_solver_per_cl                    1000
% 7.53/1.51  --min_unsat_core                        false
% 7.53/1.51  --soft_assumptions                      false
% 7.53/1.51  --soft_lemma_size                       3
% 7.53/1.51  --prop_impl_unit_size                   0
% 7.53/1.51  --prop_impl_unit                        []
% 7.53/1.51  --share_sel_clauses                     true
% 7.53/1.51  --reset_solvers                         false
% 7.53/1.51  --bc_imp_inh                            [conj_cone]
% 7.53/1.51  --conj_cone_tolerance                   3.
% 7.53/1.51  --extra_neg_conj                        none
% 7.53/1.51  --large_theory_mode                     true
% 7.53/1.51  --prolific_symb_bound                   200
% 7.53/1.51  --lt_threshold                          2000
% 7.53/1.51  --clause_weak_htbl                      true
% 7.53/1.51  --gc_record_bc_elim                     false
% 7.53/1.51  
% 7.53/1.51  ------ Preprocessing Options
% 7.53/1.51  
% 7.53/1.51  --preprocessing_flag                    true
% 7.53/1.51  --time_out_prep_mult                    0.1
% 7.53/1.51  --splitting_mode                        input
% 7.53/1.51  --splitting_grd                         true
% 7.53/1.51  --splitting_cvd                         false
% 7.53/1.51  --splitting_cvd_svl                     false
% 7.53/1.51  --splitting_nvd                         32
% 7.53/1.51  --sub_typing                            true
% 7.53/1.51  --prep_gs_sim                           true
% 7.53/1.51  --prep_unflatten                        true
% 7.53/1.51  --prep_res_sim                          true
% 7.53/1.51  --prep_upred                            true
% 7.53/1.51  --prep_sem_filter                       exhaustive
% 7.53/1.51  --prep_sem_filter_out                   false
% 7.53/1.51  --pred_elim                             true
% 7.53/1.51  --res_sim_input                         true
% 7.53/1.51  --eq_ax_congr_red                       true
% 7.53/1.51  --pure_diseq_elim                       true
% 7.53/1.51  --brand_transform                       false
% 7.53/1.51  --non_eq_to_eq                          false
% 7.53/1.51  --prep_def_merge                        true
% 7.53/1.51  --prep_def_merge_prop_impl              false
% 7.53/1.51  --prep_def_merge_mbd                    true
% 7.53/1.51  --prep_def_merge_tr_red                 false
% 7.53/1.51  --prep_def_merge_tr_cl                  false
% 7.53/1.51  --smt_preprocessing                     true
% 7.53/1.51  --smt_ac_axioms                         fast
% 7.53/1.51  --preprocessed_out                      false
% 7.53/1.51  --preprocessed_stats                    false
% 7.53/1.51  
% 7.53/1.51  ------ Abstraction refinement Options
% 7.53/1.51  
% 7.53/1.51  --abstr_ref                             []
% 7.53/1.51  --abstr_ref_prep                        false
% 7.53/1.51  --abstr_ref_until_sat                   false
% 7.53/1.51  --abstr_ref_sig_restrict                funpre
% 7.53/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.53/1.51  --abstr_ref_under                       []
% 7.53/1.51  
% 7.53/1.51  ------ SAT Options
% 7.53/1.51  
% 7.53/1.51  --sat_mode                              false
% 7.53/1.51  --sat_fm_restart_options                ""
% 7.53/1.51  --sat_gr_def                            false
% 7.53/1.51  --sat_epr_types                         true
% 7.53/1.51  --sat_non_cyclic_types                  false
% 7.53/1.51  --sat_finite_models                     false
% 7.53/1.51  --sat_fm_lemmas                         false
% 7.53/1.51  --sat_fm_prep                           false
% 7.53/1.51  --sat_fm_uc_incr                        true
% 7.53/1.51  --sat_out_model                         small
% 7.53/1.51  --sat_out_clauses                       false
% 7.53/1.51  
% 7.53/1.51  ------ QBF Options
% 7.53/1.51  
% 7.53/1.51  --qbf_mode                              false
% 7.53/1.51  --qbf_elim_univ                         false
% 7.53/1.51  --qbf_dom_inst                          none
% 7.53/1.51  --qbf_dom_pre_inst                      false
% 7.53/1.51  --qbf_sk_in                             false
% 7.53/1.51  --qbf_pred_elim                         true
% 7.53/1.51  --qbf_split                             512
% 7.53/1.51  
% 7.53/1.51  ------ BMC1 Options
% 7.53/1.51  
% 7.53/1.51  --bmc1_incremental                      false
% 7.53/1.51  --bmc1_axioms                           reachable_all
% 7.53/1.51  --bmc1_min_bound                        0
% 7.53/1.51  --bmc1_max_bound                        -1
% 7.53/1.51  --bmc1_max_bound_default                -1
% 7.53/1.51  --bmc1_symbol_reachability              true
% 7.53/1.51  --bmc1_property_lemmas                  false
% 7.53/1.51  --bmc1_k_induction                      false
% 7.53/1.51  --bmc1_non_equiv_states                 false
% 7.53/1.51  --bmc1_deadlock                         false
% 7.53/1.51  --bmc1_ucm                              false
% 7.53/1.51  --bmc1_add_unsat_core                   none
% 7.53/1.51  --bmc1_unsat_core_children              false
% 7.53/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.53/1.51  --bmc1_out_stat                         full
% 7.53/1.51  --bmc1_ground_init                      false
% 7.53/1.51  --bmc1_pre_inst_next_state              false
% 7.53/1.51  --bmc1_pre_inst_state                   false
% 7.53/1.51  --bmc1_pre_inst_reach_state             false
% 7.53/1.51  --bmc1_out_unsat_core                   false
% 7.53/1.51  --bmc1_aig_witness_out                  false
% 7.53/1.51  --bmc1_verbose                          false
% 7.53/1.51  --bmc1_dump_clauses_tptp                false
% 7.53/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.53/1.51  --bmc1_dump_file                        -
% 7.53/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.53/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.53/1.51  --bmc1_ucm_extend_mode                  1
% 7.53/1.51  --bmc1_ucm_init_mode                    2
% 7.53/1.51  --bmc1_ucm_cone_mode                    none
% 7.53/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.53/1.51  --bmc1_ucm_relax_model                  4
% 7.53/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.53/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.53/1.51  --bmc1_ucm_layered_model                none
% 7.53/1.51  --bmc1_ucm_max_lemma_size               10
% 7.53/1.51  
% 7.53/1.51  ------ AIG Options
% 7.53/1.51  
% 7.53/1.51  --aig_mode                              false
% 7.53/1.51  
% 7.53/1.51  ------ Instantiation Options
% 7.53/1.51  
% 7.53/1.51  --instantiation_flag                    true
% 7.53/1.51  --inst_sos_flag                         false
% 7.53/1.51  --inst_sos_phase                        true
% 7.53/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.53/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.53/1.51  --inst_lit_sel_side                     none
% 7.53/1.51  --inst_solver_per_active                1400
% 7.53/1.51  --inst_solver_calls_frac                1.
% 7.53/1.51  --inst_passive_queue_type               priority_queues
% 7.53/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.53/1.51  --inst_passive_queues_freq              [25;2]
% 7.53/1.51  --inst_dismatching                      true
% 7.53/1.51  --inst_eager_unprocessed_to_passive     true
% 7.53/1.51  --inst_prop_sim_given                   true
% 7.53/1.51  --inst_prop_sim_new                     false
% 7.53/1.51  --inst_subs_new                         false
% 7.53/1.51  --inst_eq_res_simp                      false
% 7.53/1.51  --inst_subs_given                       false
% 7.53/1.51  --inst_orphan_elimination               true
% 7.53/1.51  --inst_learning_loop_flag               true
% 7.53/1.51  --inst_learning_start                   3000
% 7.53/1.51  --inst_learning_factor                  2
% 7.53/1.51  --inst_start_prop_sim_after_learn       3
% 7.53/1.51  --inst_sel_renew                        solver
% 7.53/1.51  --inst_lit_activity_flag                true
% 7.53/1.51  --inst_restr_to_given                   false
% 7.53/1.51  --inst_activity_threshold               500
% 7.53/1.51  --inst_out_proof                        true
% 7.53/1.51  
% 7.53/1.51  ------ Resolution Options
% 7.53/1.51  
% 7.53/1.51  --resolution_flag                       false
% 7.53/1.51  --res_lit_sel                           adaptive
% 7.53/1.51  --res_lit_sel_side                      none
% 7.53/1.51  --res_ordering                          kbo
% 7.53/1.51  --res_to_prop_solver                    active
% 7.53/1.51  --res_prop_simpl_new                    false
% 7.53/1.51  --res_prop_simpl_given                  true
% 7.53/1.51  --res_passive_queue_type                priority_queues
% 7.53/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.53/1.51  --res_passive_queues_freq               [15;5]
% 7.53/1.51  --res_forward_subs                      full
% 7.53/1.51  --res_backward_subs                     full
% 7.53/1.51  --res_forward_subs_resolution           true
% 7.53/1.51  --res_backward_subs_resolution          true
% 7.53/1.51  --res_orphan_elimination                true
% 7.53/1.51  --res_time_limit                        2.
% 7.53/1.51  --res_out_proof                         true
% 7.53/1.51  
% 7.53/1.51  ------ Superposition Options
% 7.53/1.51  
% 7.53/1.51  --superposition_flag                    true
% 7.53/1.51  --sup_passive_queue_type                priority_queues
% 7.53/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.53/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.53/1.51  --demod_completeness_check              fast
% 7.53/1.51  --demod_use_ground                      true
% 7.53/1.51  --sup_to_prop_solver                    passive
% 7.53/1.51  --sup_prop_simpl_new                    true
% 7.53/1.51  --sup_prop_simpl_given                  true
% 7.53/1.51  --sup_fun_splitting                     false
% 7.53/1.51  --sup_smt_interval                      50000
% 7.53/1.51  
% 7.53/1.51  ------ Superposition Simplification Setup
% 7.53/1.51  
% 7.53/1.51  --sup_indices_passive                   []
% 7.53/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.53/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.53/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.53/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.53/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.53/1.51  --sup_full_bw                           [BwDemod]
% 7.53/1.51  --sup_immed_triv                        [TrivRules]
% 7.53/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.53/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.53/1.51  --sup_immed_bw_main                     []
% 7.53/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.53/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.53/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.53/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.53/1.51  
% 7.53/1.51  ------ Combination Options
% 7.53/1.51  
% 7.53/1.51  --comb_res_mult                         3
% 7.53/1.51  --comb_sup_mult                         2
% 7.53/1.51  --comb_inst_mult                        10
% 7.53/1.51  
% 7.53/1.51  ------ Debug Options
% 7.53/1.51  
% 7.53/1.51  --dbg_backtrace                         false
% 7.53/1.51  --dbg_dump_prop_clauses                 false
% 7.53/1.51  --dbg_dump_prop_clauses_file            -
% 7.53/1.51  --dbg_out_stat                          false
% 7.53/1.51  
% 7.53/1.51  
% 7.53/1.51  
% 7.53/1.51  
% 7.53/1.51  ------ Proving...
% 7.53/1.51  
% 7.53/1.51  
% 7.53/1.51  % SZS status Theorem for theBenchmark.p
% 7.53/1.51  
% 7.53/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.53/1.51  
% 7.53/1.51  fof(f18,axiom,(
% 7.53/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.53/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.51  
% 7.53/1.51  fof(f36,plain,(
% 7.53/1.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.53/1.51    inference(ennf_transformation,[],[f18])).
% 7.53/1.51  
% 7.53/1.51  fof(f37,plain,(
% 7.53/1.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.53/1.51    inference(flattening,[],[f36])).
% 7.53/1.51  
% 7.53/1.51  fof(f50,plain,(
% 7.53/1.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.53/1.51    inference(nnf_transformation,[],[f37])).
% 7.53/1.51  
% 7.53/1.51  fof(f76,plain,(
% 7.53/1.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.53/1.51    inference(cnf_transformation,[],[f50])).
% 7.53/1.51  
% 7.53/1.51  fof(f19,conjecture,(
% 7.53/1.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 7.53/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.51  
% 7.53/1.51  fof(f20,negated_conjecture,(
% 7.53/1.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 7.53/1.51    inference(negated_conjecture,[],[f19])).
% 7.53/1.51  
% 7.53/1.51  fof(f23,plain,(
% 7.53/1.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 7.53/1.51    inference(pure_predicate_removal,[],[f20])).
% 7.53/1.51  
% 7.53/1.51  fof(f38,plain,(
% 7.53/1.51    ? [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) != X0 & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1)))),
% 7.53/1.51    inference(ennf_transformation,[],[f23])).
% 7.53/1.51  
% 7.53/1.51  fof(f39,plain,(
% 7.53/1.51    ? [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) != X0 & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1))),
% 7.53/1.51    inference(flattening,[],[f38])).
% 7.53/1.51  
% 7.53/1.51  fof(f51,plain,(
% 7.53/1.51    ? [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) != X0 & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1)) => (k8_relset_1(sK2,sK3,sK4,sK3) != sK2 & (k1_xboole_0 = sK2 | k1_xboole_0 != sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3))),
% 7.53/1.51    introduced(choice_axiom,[])).
% 7.53/1.51  
% 7.53/1.51  fof(f52,plain,(
% 7.53/1.51    k8_relset_1(sK2,sK3,sK4,sK3) != sK2 & (k1_xboole_0 = sK2 | k1_xboole_0 != sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3)),
% 7.53/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f39,f51])).
% 7.53/1.51  
% 7.53/1.51  fof(f82,plain,(
% 7.53/1.51    v1_funct_2(sK4,sK2,sK3)),
% 7.53/1.51    inference(cnf_transformation,[],[f52])).
% 7.53/1.51  
% 7.53/1.51  fof(f83,plain,(
% 7.53/1.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 7.53/1.51    inference(cnf_transformation,[],[f52])).
% 7.53/1.51  
% 7.53/1.51  fof(f16,axiom,(
% 7.53/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.53/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.51  
% 7.53/1.51  fof(f34,plain,(
% 7.53/1.51    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.53/1.51    inference(ennf_transformation,[],[f16])).
% 7.53/1.51  
% 7.53/1.51  fof(f74,plain,(
% 7.53/1.51    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.53/1.51    inference(cnf_transformation,[],[f34])).
% 7.53/1.51  
% 7.53/1.51  fof(f6,axiom,(
% 7.53/1.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.53/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.51  
% 7.53/1.51  fof(f48,plain,(
% 7.53/1.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.53/1.51    inference(nnf_transformation,[],[f6])).
% 7.53/1.51  
% 7.53/1.51  fof(f61,plain,(
% 7.53/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.53/1.51    inference(cnf_transformation,[],[f48])).
% 7.53/1.51  
% 7.53/1.51  fof(f7,axiom,(
% 7.53/1.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.53/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.51  
% 7.53/1.51  fof(f27,plain,(
% 7.53/1.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.53/1.51    inference(ennf_transformation,[],[f7])).
% 7.53/1.51  
% 7.53/1.51  fof(f63,plain,(
% 7.53/1.51    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.53/1.51    inference(cnf_transformation,[],[f27])).
% 7.53/1.51  
% 7.53/1.51  fof(f62,plain,(
% 7.53/1.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.53/1.51    inference(cnf_transformation,[],[f48])).
% 7.53/1.51  
% 7.53/1.51  fof(f10,axiom,(
% 7.53/1.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.53/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.51  
% 7.53/1.51  fof(f67,plain,(
% 7.53/1.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.53/1.51    inference(cnf_transformation,[],[f10])).
% 7.53/1.51  
% 7.53/1.51  fof(f15,axiom,(
% 7.53/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.53/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.51  
% 7.53/1.51  fof(f21,plain,(
% 7.53/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 7.53/1.51    inference(pure_predicate_removal,[],[f15])).
% 7.53/1.51  
% 7.53/1.51  fof(f33,plain,(
% 7.53/1.51    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.53/1.51    inference(ennf_transformation,[],[f21])).
% 7.53/1.51  
% 7.53/1.51  fof(f73,plain,(
% 7.53/1.51    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.53/1.51    inference(cnf_transformation,[],[f33])).
% 7.53/1.51  
% 7.53/1.51  fof(f8,axiom,(
% 7.53/1.51    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 7.53/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.51  
% 7.53/1.51  fof(f28,plain,(
% 7.53/1.51    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.53/1.51    inference(ennf_transformation,[],[f8])).
% 7.53/1.51  
% 7.53/1.51  fof(f49,plain,(
% 7.53/1.51    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.53/1.51    inference(nnf_transformation,[],[f28])).
% 7.53/1.51  
% 7.53/1.51  fof(f64,plain,(
% 7.53/1.51    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.53/1.51    inference(cnf_transformation,[],[f49])).
% 7.53/1.51  
% 7.53/1.51  fof(f13,axiom,(
% 7.53/1.51    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 7.53/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.51  
% 7.53/1.51  fof(f31,plain,(
% 7.53/1.51    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.53/1.51    inference(ennf_transformation,[],[f13])).
% 7.53/1.51  
% 7.53/1.51  fof(f32,plain,(
% 7.53/1.51    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 7.53/1.51    inference(flattening,[],[f31])).
% 7.53/1.51  
% 7.53/1.51  fof(f71,plain,(
% 7.53/1.51    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.53/1.51    inference(cnf_transformation,[],[f32])).
% 7.53/1.51  
% 7.53/1.51  fof(f14,axiom,(
% 7.53/1.51    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 7.53/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.51  
% 7.53/1.51  fof(f22,plain,(
% 7.53/1.51    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 7.53/1.51    inference(pure_predicate_removal,[],[f14])).
% 7.53/1.51  
% 7.53/1.51  fof(f72,plain,(
% 7.53/1.51    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 7.53/1.51    inference(cnf_transformation,[],[f22])).
% 7.53/1.51  
% 7.53/1.51  fof(f11,axiom,(
% 7.53/1.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 7.53/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.51  
% 7.53/1.51  fof(f30,plain,(
% 7.53/1.51    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.53/1.51    inference(ennf_transformation,[],[f11])).
% 7.53/1.51  
% 7.53/1.51  fof(f68,plain,(
% 7.53/1.51    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.53/1.51    inference(cnf_transformation,[],[f30])).
% 7.53/1.51  
% 7.53/1.51  fof(f12,axiom,(
% 7.53/1.51    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 7.53/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.51  
% 7.53/1.51  fof(f69,plain,(
% 7.53/1.51    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 7.53/1.51    inference(cnf_transformation,[],[f12])).
% 7.53/1.51  
% 7.53/1.51  fof(f17,axiom,(
% 7.53/1.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 7.53/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.51  
% 7.53/1.51  fof(f35,plain,(
% 7.53/1.51    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.53/1.51    inference(ennf_transformation,[],[f17])).
% 7.53/1.51  
% 7.53/1.51  fof(f75,plain,(
% 7.53/1.51    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.53/1.51    inference(cnf_transformation,[],[f35])).
% 7.53/1.51  
% 7.53/1.51  fof(f85,plain,(
% 7.53/1.51    k8_relset_1(sK2,sK3,sK4,sK3) != sK2),
% 7.53/1.51    inference(cnf_transformation,[],[f52])).
% 7.53/1.51  
% 7.53/1.51  fof(f84,plain,(
% 7.53/1.51    k1_xboole_0 = sK2 | k1_xboole_0 != sK3),
% 7.53/1.51    inference(cnf_transformation,[],[f52])).
% 7.53/1.51  
% 7.53/1.51  fof(f77,plain,(
% 7.53/1.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.53/1.51    inference(cnf_transformation,[],[f50])).
% 7.53/1.51  
% 7.53/1.51  fof(f90,plain,(
% 7.53/1.51    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 7.53/1.51    inference(equality_resolution,[],[f77])).
% 7.53/1.51  
% 7.53/1.51  fof(f3,axiom,(
% 7.53/1.51    v1_xboole_0(k1_xboole_0)),
% 7.53/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.51  
% 7.53/1.51  fof(f58,plain,(
% 7.53/1.51    v1_xboole_0(k1_xboole_0)),
% 7.53/1.51    inference(cnf_transformation,[],[f3])).
% 7.53/1.51  
% 7.53/1.51  fof(f5,axiom,(
% 7.53/1.51    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 7.53/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.51  
% 7.53/1.51  fof(f26,plain,(
% 7.53/1.51    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 7.53/1.51    inference(ennf_transformation,[],[f5])).
% 7.53/1.51  
% 7.53/1.51  fof(f60,plain,(
% 7.53/1.51    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 7.53/1.51    inference(cnf_transformation,[],[f26])).
% 7.53/1.51  
% 7.53/1.51  fof(f4,axiom,(
% 7.53/1.51    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 7.53/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.51  
% 7.53/1.51  fof(f25,plain,(
% 7.53/1.51    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 7.53/1.51    inference(ennf_transformation,[],[f4])).
% 7.53/1.51  
% 7.53/1.51  fof(f59,plain,(
% 7.53/1.51    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 7.53/1.51    inference(cnf_transformation,[],[f25])).
% 7.53/1.51  
% 7.53/1.51  fof(f80,plain,(
% 7.53/1.51    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.53/1.51    inference(cnf_transformation,[],[f50])).
% 7.53/1.51  
% 7.53/1.51  fof(f88,plain,(
% 7.53/1.51    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 7.53/1.51    inference(equality_resolution,[],[f80])).
% 7.53/1.51  
% 7.53/1.51  cnf(c_28,plain,
% 7.53/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.53/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.53/1.51      | k1_relset_1(X1,X2,X0) = X1
% 7.53/1.51      | k1_xboole_0 = X2 ),
% 7.53/1.51      inference(cnf_transformation,[],[f76]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_32,negated_conjecture,
% 7.53/1.51      ( v1_funct_2(sK4,sK2,sK3) ),
% 7.53/1.51      inference(cnf_transformation,[],[f82]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_1106,plain,
% 7.53/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.53/1.51      | k1_relset_1(X1,X2,X0) = X1
% 7.53/1.51      | sK4 != X0
% 7.53/1.51      | sK3 != X2
% 7.53/1.51      | sK2 != X1
% 7.53/1.51      | k1_xboole_0 = X2 ),
% 7.53/1.51      inference(resolution_lifted,[status(thm)],[c_28,c_32]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_1107,plain,
% 7.53/1.51      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 7.53/1.51      | k1_relset_1(sK2,sK3,sK4) = sK2
% 7.53/1.51      | k1_xboole_0 = sK3 ),
% 7.53/1.51      inference(unflattening,[status(thm)],[c_1106]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_31,negated_conjecture,
% 7.53/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 7.53/1.51      inference(cnf_transformation,[],[f83]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_1109,plain,
% 7.53/1.51      ( k1_relset_1(sK2,sK3,sK4) = sK2 | k1_xboole_0 = sK3 ),
% 7.53/1.51      inference(global_propositional_subsumption,
% 7.53/1.51                [status(thm)],
% 7.53/1.51                [c_1107,c_31]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_2522,plain,
% 7.53/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 7.53/1.51      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_21,plain,
% 7.53/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.53/1.51      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.53/1.51      inference(cnf_transformation,[],[f74]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_2524,plain,
% 7.53/1.51      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.53/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.53/1.51      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_3664,plain,
% 7.53/1.51      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 7.53/1.51      inference(superposition,[status(thm)],[c_2522,c_2524]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_3837,plain,
% 7.53/1.51      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 7.53/1.51      inference(superposition,[status(thm)],[c_1109,c_3664]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_9,plain,
% 7.53/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.53/1.51      inference(cnf_transformation,[],[f61]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_2530,plain,
% 7.53/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.53/1.51      | r1_tarski(X0,X1) = iProver_top ),
% 7.53/1.51      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_3282,plain,
% 7.53/1.51      ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 7.53/1.51      inference(superposition,[status(thm)],[c_2522,c_2530]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_10,plain,
% 7.53/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.53/1.51      | ~ v1_relat_1(X1)
% 7.53/1.51      | v1_relat_1(X0) ),
% 7.53/1.51      inference(cnf_transformation,[],[f63]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_8,plain,
% 7.53/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.53/1.51      inference(cnf_transformation,[],[f62]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_240,plain,
% 7.53/1.51      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.53/1.51      inference(prop_impl,[status(thm)],[c_8]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_241,plain,
% 7.53/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.53/1.51      inference(renaming,[status(thm)],[c_240]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_298,plain,
% 7.53/1.51      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 7.53/1.51      inference(bin_hyper_res,[status(thm)],[c_10,c_241]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_2521,plain,
% 7.53/1.51      ( r1_tarski(X0,X1) != iProver_top
% 7.53/1.51      | v1_relat_1(X1) != iProver_top
% 7.53/1.51      | v1_relat_1(X0) = iProver_top ),
% 7.53/1.51      inference(predicate_to_equality,[status(thm)],[c_298]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_17834,plain,
% 7.53/1.51      ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
% 7.53/1.51      | v1_relat_1(sK4) = iProver_top ),
% 7.53/1.51      inference(superposition,[status(thm)],[c_3282,c_2521]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_14,plain,
% 7.53/1.51      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.53/1.51      inference(cnf_transformation,[],[f67]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_2528,plain,
% 7.53/1.51      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.53/1.51      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_18101,plain,
% 7.53/1.51      ( v1_relat_1(sK4) = iProver_top ),
% 7.53/1.51      inference(forward_subsumption_resolution,
% 7.53/1.51                [status(thm)],
% 7.53/1.51                [c_17834,c_2528]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_20,plain,
% 7.53/1.51      ( v5_relat_1(X0,X1)
% 7.53/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 7.53/1.51      inference(cnf_transformation,[],[f73]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_12,plain,
% 7.53/1.51      ( ~ v5_relat_1(X0,X1)
% 7.53/1.51      | r1_tarski(k2_relat_1(X0),X1)
% 7.53/1.51      | ~ v1_relat_1(X0) ),
% 7.53/1.51      inference(cnf_transformation,[],[f64]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_403,plain,
% 7.53/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.53/1.51      | r1_tarski(k2_relat_1(X0),X2)
% 7.53/1.51      | ~ v1_relat_1(X0) ),
% 7.53/1.51      inference(resolution,[status(thm)],[c_20,c_12]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_2520,plain,
% 7.53/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.53/1.51      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 7.53/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.53/1.51      inference(predicate_to_equality,[status(thm)],[c_403]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_2854,plain,
% 7.53/1.51      ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top
% 7.53/1.51      | v1_relat_1(sK4) != iProver_top ),
% 7.53/1.51      inference(superposition,[status(thm)],[c_2522,c_2520]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_18,plain,
% 7.53/1.51      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 7.53/1.51      | ~ v1_relat_1(X0)
% 7.53/1.51      | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
% 7.53/1.51      inference(cnf_transformation,[],[f71]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_2526,plain,
% 7.53/1.51      ( k5_relat_1(X0,k6_relat_1(X1)) = X0
% 7.53/1.51      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 7.53/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.53/1.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_3820,plain,
% 7.53/1.51      ( k5_relat_1(sK4,k6_relat_1(sK3)) = sK4
% 7.53/1.51      | v1_relat_1(sK4) != iProver_top ),
% 7.53/1.51      inference(superposition,[status(thm)],[c_2854,c_2526]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_18123,plain,
% 7.53/1.51      ( k5_relat_1(sK4,k6_relat_1(sK3)) = sK4 ),
% 7.53/1.51      inference(superposition,[status(thm)],[c_18101,c_3820]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_19,plain,
% 7.53/1.51      ( v1_relat_1(k6_relat_1(X0)) ),
% 7.53/1.51      inference(cnf_transformation,[],[f72]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_2525,plain,
% 7.53/1.51      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 7.53/1.51      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_15,plain,
% 7.53/1.51      ( ~ v1_relat_1(X0)
% 7.53/1.51      | ~ v1_relat_1(X1)
% 7.53/1.51      | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
% 7.53/1.51      inference(cnf_transformation,[],[f68]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_2527,plain,
% 7.53/1.51      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 7.53/1.51      | v1_relat_1(X0) != iProver_top
% 7.53/1.51      | v1_relat_1(X1) != iProver_top ),
% 7.53/1.51      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_18105,plain,
% 7.53/1.51      ( k10_relat_1(sK4,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK4,X0))
% 7.53/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.53/1.51      inference(superposition,[status(thm)],[c_18101,c_2527]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_19346,plain,
% 7.53/1.51      ( k10_relat_1(sK4,k1_relat_1(k6_relat_1(X0))) = k1_relat_1(k5_relat_1(sK4,k6_relat_1(X0))) ),
% 7.53/1.51      inference(superposition,[status(thm)],[c_2525,c_18105]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_17,plain,
% 7.53/1.51      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 7.53/1.51      inference(cnf_transformation,[],[f69]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_19360,plain,
% 7.53/1.51      ( k1_relat_1(k5_relat_1(sK4,k6_relat_1(X0))) = k10_relat_1(sK4,X0) ),
% 7.53/1.51      inference(light_normalisation,[status(thm)],[c_19346,c_17]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_19597,plain,
% 7.53/1.51      ( k10_relat_1(sK4,sK3) = k1_relat_1(sK4) ),
% 7.53/1.51      inference(superposition,[status(thm)],[c_18123,c_19360]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_22,plain,
% 7.53/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.53/1.51      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 7.53/1.51      inference(cnf_transformation,[],[f75]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_2523,plain,
% 7.53/1.51      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 7.53/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.53/1.51      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_3212,plain,
% 7.53/1.51      ( k8_relset_1(sK2,sK3,sK4,X0) = k10_relat_1(sK4,X0) ),
% 7.53/1.51      inference(superposition,[status(thm)],[c_2522,c_2523]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_29,negated_conjecture,
% 7.53/1.51      ( k8_relset_1(sK2,sK3,sK4,sK3) != sK2 ),
% 7.53/1.51      inference(cnf_transformation,[],[f85]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_3471,plain,
% 7.53/1.51      ( k10_relat_1(sK4,sK3) != sK2 ),
% 7.53/1.51      inference(demodulation,[status(thm)],[c_3212,c_29]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_19703,plain,
% 7.53/1.51      ( k1_relat_1(sK4) != sK2 ),
% 7.53/1.51      inference(demodulation,[status(thm)],[c_19597,c_3471]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_19705,plain,
% 7.53/1.51      ( sK3 = k1_xboole_0 ),
% 7.53/1.51      inference(superposition,[status(thm)],[c_3837,c_19703]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_19791,plain,
% 7.53/1.51      ( k10_relat_1(sK4,k1_xboole_0) = k1_relat_1(sK4) ),
% 7.53/1.51      inference(demodulation,[status(thm)],[c_19705,c_19597]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_19949,plain,
% 7.53/1.51      ( k1_relset_1(sK2,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
% 7.53/1.51      inference(demodulation,[status(thm)],[c_19705,c_3664]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_30,negated_conjecture,
% 7.53/1.51      ( k1_xboole_0 != sK3 | k1_xboole_0 = sK2 ),
% 7.53/1.51      inference(cnf_transformation,[],[f84]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_19957,plain,
% 7.53/1.51      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 7.53/1.51      inference(demodulation,[status(thm)],[c_19705,c_30]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_19958,plain,
% 7.53/1.51      ( sK2 = k1_xboole_0 ),
% 7.53/1.51      inference(equality_resolution_simp,[status(thm)],[c_19957]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_19984,plain,
% 7.53/1.51      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
% 7.53/1.51      inference(light_normalisation,[status(thm)],[c_19949,c_19958]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_27,plain,
% 7.53/1.51      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 7.53/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.53/1.51      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 7.53/1.51      inference(cnf_transformation,[],[f90]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_1093,plain,
% 7.53/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.53/1.51      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 7.53/1.51      | sK4 != X0
% 7.53/1.51      | sK3 != X1
% 7.53/1.51      | sK2 != k1_xboole_0 ),
% 7.53/1.51      inference(resolution_lifted,[status(thm)],[c_27,c_32]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_1094,plain,
% 7.53/1.51      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
% 7.53/1.51      | k1_relset_1(k1_xboole_0,sK3,sK4) = k1_xboole_0
% 7.53/1.51      | sK2 != k1_xboole_0 ),
% 7.53/1.51      inference(unflattening,[status(thm)],[c_1093]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_2518,plain,
% 7.53/1.51      ( k1_relset_1(k1_xboole_0,sK3,sK4) = k1_xboole_0
% 7.53/1.51      | sK2 != k1_xboole_0
% 7.53/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
% 7.53/1.51      inference(predicate_to_equality,[status(thm)],[c_1094]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_19954,plain,
% 7.53/1.51      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 7.53/1.51      | sK2 != k1_xboole_0
% 7.53/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 7.53/1.51      inference(demodulation,[status(thm)],[c_19705,c_2518]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_19965,plain,
% 7.53/1.51      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 7.53/1.51      | k1_xboole_0 != k1_xboole_0
% 7.53/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 7.53/1.51      inference(light_normalisation,[status(thm)],[c_19954,c_19958]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_19966,plain,
% 7.53/1.51      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 7.53/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 7.53/1.51      inference(equality_resolution_simp,[status(thm)],[c_19965]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_5,plain,
% 7.53/1.51      ( v1_xboole_0(k1_xboole_0) ),
% 7.53/1.51      inference(cnf_transformation,[],[f58]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_2534,plain,
% 7.53/1.51      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.53/1.51      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_7,plain,
% 7.53/1.51      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
% 7.53/1.51      inference(cnf_transformation,[],[f60]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_2532,plain,
% 7.53/1.51      ( v1_xboole_0(X0) != iProver_top
% 7.53/1.51      | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
% 7.53/1.51      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_6,plain,
% 7.53/1.51      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 7.53/1.51      inference(cnf_transformation,[],[f59]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_2533,plain,
% 7.53/1.51      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 7.53/1.51      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_3144,plain,
% 7.53/1.51      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
% 7.53/1.51      | v1_xboole_0(X1) != iProver_top ),
% 7.53/1.51      inference(superposition,[status(thm)],[c_2532,c_2533]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_3502,plain,
% 7.53/1.51      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.53/1.51      inference(superposition,[status(thm)],[c_2534,c_3144]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_19969,plain,
% 7.53/1.51      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 7.53/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.53/1.51      inference(demodulation,[status(thm)],[c_19966,c_3502]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_19986,plain,
% 7.53/1.51      ( k1_relat_1(sK4) = k1_xboole_0
% 7.53/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.53/1.51      inference(demodulation,[status(thm)],[c_19984,c_19969]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_19956,plain,
% 7.53/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
% 7.53/1.51      inference(demodulation,[status(thm)],[c_19705,c_2522]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_19961,plain,
% 7.53/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 7.53/1.51      inference(light_normalisation,[status(thm)],[c_19956,c_19958]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_19963,plain,
% 7.53/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.53/1.51      inference(demodulation,[status(thm)],[c_19961,c_3502]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_19990,plain,
% 7.53/1.51      ( k1_relat_1(sK4) = k1_xboole_0 ),
% 7.53/1.51      inference(forward_subsumption_resolution,
% 7.53/1.51                [status(thm)],
% 7.53/1.51                [c_19986,c_19963]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_20825,plain,
% 7.53/1.51      ( k10_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 7.53/1.51      inference(light_normalisation,[status(thm)],[c_19791,c_19990]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_1949,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_2792,plain,
% 7.53/1.51      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 7.53/1.51      inference(instantiation,[status(thm)],[c_1949]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_7664,plain,
% 7.53/1.51      ( k10_relat_1(sK4,X0) != X1
% 7.53/1.51      | sK2 != X1
% 7.53/1.51      | sK2 = k10_relat_1(sK4,X0) ),
% 7.53/1.51      inference(instantiation,[status(thm)],[c_2792]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_7665,plain,
% 7.53/1.51      ( k10_relat_1(sK4,k1_xboole_0) != k1_xboole_0
% 7.53/1.51      | sK2 = k10_relat_1(sK4,k1_xboole_0)
% 7.53/1.51      | sK2 != k1_xboole_0 ),
% 7.53/1.51      inference(instantiation,[status(thm)],[c_7664]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_1960,plain,
% 7.53/1.51      ( X0 != X1 | k10_relat_1(X2,X0) = k10_relat_1(X2,X1) ),
% 7.53/1.51      theory(equality) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_4103,plain,
% 7.53/1.51      ( k10_relat_1(sK4,sK3) = k10_relat_1(sK4,X0) | sK3 != X0 ),
% 7.53/1.51      inference(instantiation,[status(thm)],[c_1960]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_4105,plain,
% 7.53/1.51      ( k10_relat_1(sK4,sK3) = k10_relat_1(sK4,k1_xboole_0)
% 7.53/1.51      | sK3 != k1_xboole_0 ),
% 7.53/1.51      inference(instantiation,[status(thm)],[c_4103]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_3171,plain,
% 7.53/1.51      ( k10_relat_1(sK4,sK3) != X0
% 7.53/1.51      | sK2 != X0
% 7.53/1.51      | sK2 = k10_relat_1(sK4,sK3) ),
% 7.53/1.51      inference(instantiation,[status(thm)],[c_2792]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_4102,plain,
% 7.53/1.51      ( k10_relat_1(sK4,sK3) != k10_relat_1(sK4,X0)
% 7.53/1.51      | sK2 != k10_relat_1(sK4,X0)
% 7.53/1.51      | sK2 = k10_relat_1(sK4,sK3) ),
% 7.53/1.51      inference(instantiation,[status(thm)],[c_3171]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_4104,plain,
% 7.53/1.51      ( k10_relat_1(sK4,sK3) != k10_relat_1(sK4,k1_xboole_0)
% 7.53/1.51      | sK2 = k10_relat_1(sK4,sK3)
% 7.53/1.51      | sK2 != k10_relat_1(sK4,k1_xboole_0) ),
% 7.53/1.51      inference(instantiation,[status(thm)],[c_4102]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_24,plain,
% 7.53/1.51      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 7.53/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 7.53/1.51      | k1_xboole_0 = X1
% 7.53/1.51      | k1_xboole_0 = X0 ),
% 7.53/1.51      inference(cnf_transformation,[],[f88]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_1073,plain,
% 7.53/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 7.53/1.51      | sK4 != X0
% 7.53/1.51      | sK3 != k1_xboole_0
% 7.53/1.51      | sK2 != X1
% 7.53/1.51      | k1_xboole_0 = X0
% 7.53/1.51      | k1_xboole_0 = X1 ),
% 7.53/1.51      inference(resolution_lifted,[status(thm)],[c_24,c_32]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_1074,plain,
% 7.53/1.51      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 7.53/1.51      | sK3 != k1_xboole_0
% 7.53/1.51      | k1_xboole_0 = sK4
% 7.53/1.51      | k1_xboole_0 = sK2 ),
% 7.53/1.51      inference(unflattening,[status(thm)],[c_1073]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_2519,plain,
% 7.53/1.51      ( sK3 != k1_xboole_0
% 7.53/1.51      | k1_xboole_0 = sK4
% 7.53/1.51      | k1_xboole_0 = sK2
% 7.53/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 7.53/1.51      inference(predicate_to_equality,[status(thm)],[c_1074]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_3523,plain,
% 7.53/1.51      ( sK4 = k1_xboole_0
% 7.53/1.51      | sK3 != k1_xboole_0
% 7.53/1.51      | sK2 = k1_xboole_0
% 7.53/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.53/1.51      inference(demodulation,[status(thm)],[c_3502,c_2519]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_96,plain,
% 7.53/1.51      ( ~ v1_xboole_0(k1_xboole_0) | k1_xboole_0 = k1_xboole_0 ),
% 7.53/1.51      inference(instantiation,[status(thm)],[c_6]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_2728,plain,
% 7.53/1.51      ( sK2 != X0 | sK2 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 7.53/1.51      inference(instantiation,[status(thm)],[c_1949]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_2793,plain,
% 7.53/1.51      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 7.53/1.51      inference(instantiation,[status(thm)],[c_2728]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_1948,plain,( X0 = X0 ),theory(equality) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_2794,plain,
% 7.53/1.51      ( sK2 = sK2 ),
% 7.53/1.51      inference(instantiation,[status(thm)],[c_1948]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_3496,plain,
% 7.53/1.51      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 7.53/1.51      inference(instantiation,[status(thm)],[c_1949]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_3497,plain,
% 7.53/1.51      ( sK3 != k1_xboole_0
% 7.53/1.51      | k1_xboole_0 = sK3
% 7.53/1.51      | k1_xboole_0 != k1_xboole_0 ),
% 7.53/1.51      inference(instantiation,[status(thm)],[c_3496]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_3615,plain,
% 7.53/1.51      ( sK2 = k1_xboole_0 | sK3 != k1_xboole_0 ),
% 7.53/1.51      inference(global_propositional_subsumption,
% 7.53/1.51                [status(thm)],
% 7.53/1.51                [c_3523,c_30,c_96,c_5,c_2793,c_2794,c_3497]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_3616,plain,
% 7.53/1.51      ( sK3 != k1_xboole_0 | sK2 = k1_xboole_0 ),
% 7.53/1.51      inference(renaming,[status(thm)],[c_3615]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_2773,plain,
% 7.53/1.51      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 7.53/1.51      | k8_relset_1(sK2,sK3,sK4,X0) = k10_relat_1(sK4,X0) ),
% 7.53/1.51      inference(instantiation,[status(thm)],[c_22]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_2979,plain,
% 7.53/1.51      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 7.53/1.51      | k8_relset_1(sK2,sK3,sK4,sK3) = k10_relat_1(sK4,sK3) ),
% 7.53/1.51      inference(instantiation,[status(thm)],[c_2773]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_2726,plain,
% 7.53/1.51      ( k8_relset_1(sK2,sK3,sK4,sK3) != X0
% 7.53/1.51      | k8_relset_1(sK2,sK3,sK4,sK3) = sK2
% 7.53/1.51      | sK2 != X0 ),
% 7.53/1.51      inference(instantiation,[status(thm)],[c_1949]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(c_2978,plain,
% 7.53/1.51      ( k8_relset_1(sK2,sK3,sK4,sK3) != k10_relat_1(sK4,sK3)
% 7.53/1.51      | k8_relset_1(sK2,sK3,sK4,sK3) = sK2
% 7.53/1.51      | sK2 != k10_relat_1(sK4,sK3) ),
% 7.53/1.51      inference(instantiation,[status(thm)],[c_2726]) ).
% 7.53/1.51  
% 7.53/1.51  cnf(contradiction,plain,
% 7.53/1.51      ( $false ),
% 7.53/1.51      inference(minisat,
% 7.53/1.51                [status(thm)],
% 7.53/1.51                [c_20825,c_19703,c_7665,c_4105,c_4104,c_3837,c_3616,
% 7.53/1.51                 c_2979,c_2978,c_29,c_31]) ).
% 7.53/1.51  
% 7.53/1.51  
% 7.53/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.53/1.51  
% 7.53/1.51  ------                               Statistics
% 7.53/1.51  
% 7.53/1.51  ------ General
% 7.53/1.51  
% 7.53/1.51  abstr_ref_over_cycles:                  0
% 7.53/1.51  abstr_ref_under_cycles:                 0
% 7.53/1.51  gc_basic_clause_elim:                   0
% 7.53/1.51  forced_gc_time:                         0
% 7.53/1.51  parsing_time:                           0.009
% 7.53/1.51  unif_index_cands_time:                  0.
% 7.53/1.51  unif_index_add_time:                    0.
% 7.53/1.51  orderings_time:                         0.
% 7.53/1.51  out_proof_time:                         0.014
% 7.53/1.51  total_time:                             0.768
% 7.53/1.51  num_of_symbols:                         53
% 7.53/1.51  num_of_terms:                           13423
% 7.53/1.51  
% 7.53/1.51  ------ Preprocessing
% 7.53/1.51  
% 7.53/1.51  num_of_splits:                          0
% 7.53/1.51  num_of_split_atoms:                     0
% 7.53/1.51  num_of_reused_defs:                     0
% 7.53/1.51  num_eq_ax_congr_red:                    28
% 7.53/1.51  num_of_sem_filtered_clauses:            1
% 7.53/1.51  num_of_subtypes:                        0
% 7.53/1.51  monotx_restored_types:                  0
% 7.53/1.51  sat_num_of_epr_types:                   0
% 7.53/1.51  sat_num_of_non_cyclic_types:            0
% 7.53/1.51  sat_guarded_non_collapsed_types:        0
% 7.53/1.51  num_pure_diseq_elim:                    0
% 7.53/1.51  simp_replaced_by:                       0
% 7.53/1.51  res_preprocessed:                       145
% 7.53/1.51  prep_upred:                             0
% 7.53/1.51  prep_unflattend:                        89
% 7.53/1.51  smt_new_axioms:                         0
% 7.53/1.51  pred_elim_cands:                        5
% 7.53/1.51  pred_elim:                              2
% 7.53/1.51  pred_elim_cl:                           6
% 7.53/1.51  pred_elim_cycles:                       7
% 7.53/1.51  merged_defs:                            8
% 7.53/1.51  merged_defs_ncl:                        0
% 7.53/1.51  bin_hyper_res:                          9
% 7.53/1.51  prep_cycles:                            4
% 7.53/1.51  pred_elim_time:                         0.023
% 7.53/1.51  splitting_time:                         0.
% 7.53/1.51  sem_filter_time:                        0.
% 7.53/1.51  monotx_time:                            0.
% 7.53/1.51  subtype_inf_time:                       0.
% 7.53/1.51  
% 7.53/1.51  ------ Problem properties
% 7.53/1.51  
% 7.53/1.51  clauses:                                27
% 7.53/1.51  conjectures:                            3
% 7.53/1.51  epr:                                    6
% 7.53/1.51  horn:                                   23
% 7.53/1.51  ground:                                 7
% 7.53/1.51  unary:                                  7
% 7.53/1.51  binary:                                 13
% 7.53/1.51  lits:                                   55
% 7.53/1.51  lits_eq:                                17
% 7.53/1.51  fd_pure:                                0
% 7.53/1.51  fd_pseudo:                              0
% 7.53/1.51  fd_cond:                                1
% 7.53/1.51  fd_pseudo_cond:                         0
% 7.53/1.51  ac_symbols:                             0
% 7.53/1.51  
% 7.53/1.51  ------ Propositional Solver
% 7.53/1.51  
% 7.53/1.51  prop_solver_calls:                      31
% 7.53/1.51  prop_fast_solver_calls:                 1650
% 7.53/1.51  smt_solver_calls:                       0
% 7.53/1.51  smt_fast_solver_calls:                  0
% 7.53/1.51  prop_num_of_clauses:                    7362
% 7.53/1.51  prop_preprocess_simplified:             12634
% 7.53/1.51  prop_fo_subsumed:                       28
% 7.53/1.51  prop_solver_time:                       0.
% 7.53/1.51  smt_solver_time:                        0.
% 7.53/1.51  smt_fast_solver_time:                   0.
% 7.53/1.51  prop_fast_solver_time:                  0.
% 7.53/1.51  prop_unsat_core_time:                   0.001
% 7.53/1.51  
% 7.53/1.51  ------ QBF
% 7.53/1.51  
% 7.53/1.51  qbf_q_res:                              0
% 7.53/1.51  qbf_num_tautologies:                    0
% 7.53/1.51  qbf_prep_cycles:                        0
% 7.53/1.51  
% 7.53/1.51  ------ BMC1
% 7.53/1.51  
% 7.53/1.51  bmc1_current_bound:                     -1
% 7.53/1.51  bmc1_last_solved_bound:                 -1
% 7.53/1.51  bmc1_unsat_core_size:                   -1
% 7.53/1.51  bmc1_unsat_core_parents_size:           -1
% 7.53/1.51  bmc1_merge_next_fun:                    0
% 7.53/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.53/1.51  
% 7.53/1.51  ------ Instantiation
% 7.53/1.51  
% 7.53/1.51  inst_num_of_clauses:                    2248
% 7.53/1.51  inst_num_in_passive:                    390
% 7.53/1.51  inst_num_in_active:                     1111
% 7.53/1.51  inst_num_in_unprocessed:                747
% 7.53/1.51  inst_num_of_loops:                      1490
% 7.53/1.51  inst_num_of_learning_restarts:          0
% 7.53/1.51  inst_num_moves_active_passive:          375
% 7.53/1.51  inst_lit_activity:                      0
% 7.53/1.51  inst_lit_activity_moves:                0
% 7.53/1.51  inst_num_tautologies:                   0
% 7.53/1.51  inst_num_prop_implied:                  0
% 7.53/1.51  inst_num_existing_simplified:           0
% 7.53/1.51  inst_num_eq_res_simplified:             0
% 7.53/1.51  inst_num_child_elim:                    0
% 7.53/1.51  inst_num_of_dismatching_blockings:      667
% 7.53/1.51  inst_num_of_non_proper_insts:           2427
% 7.53/1.51  inst_num_of_duplicates:                 0
% 7.53/1.51  inst_inst_num_from_inst_to_res:         0
% 7.53/1.51  inst_dismatching_checking_time:         0.
% 7.53/1.51  
% 7.53/1.51  ------ Resolution
% 7.53/1.51  
% 7.53/1.51  res_num_of_clauses:                     0
% 7.53/1.51  res_num_in_passive:                     0
% 7.53/1.51  res_num_in_active:                      0
% 7.53/1.51  res_num_of_loops:                       149
% 7.53/1.51  res_forward_subset_subsumed:            178
% 7.53/1.51  res_backward_subset_subsumed:           2
% 7.53/1.51  res_forward_subsumed:                   0
% 7.53/1.51  res_backward_subsumed:                  0
% 7.53/1.51  res_forward_subsumption_resolution:     0
% 7.53/1.51  res_backward_subsumption_resolution:    0
% 7.53/1.51  res_clause_to_clause_subsumption:       4845
% 7.53/1.51  res_orphan_elimination:                 0
% 7.53/1.51  res_tautology_del:                      297
% 7.53/1.51  res_num_eq_res_simplified:              0
% 7.53/1.51  res_num_sel_changes:                    0
% 7.53/1.51  res_moves_from_active_to_pass:          0
% 7.53/1.51  
% 7.53/1.51  ------ Superposition
% 7.53/1.51  
% 7.53/1.51  sup_time_total:                         0.
% 7.53/1.51  sup_time_generating:                    0.
% 7.53/1.51  sup_time_sim_full:                      0.
% 7.53/1.51  sup_time_sim_immed:                     0.
% 7.53/1.51  
% 7.53/1.51  sup_num_of_clauses:                     454
% 7.53/1.51  sup_num_in_active:                      123
% 7.53/1.51  sup_num_in_passive:                     331
% 7.53/1.51  sup_num_of_loops:                       297
% 7.53/1.51  sup_fw_superposition:                   414
% 7.53/1.51  sup_bw_superposition:                   217
% 7.53/1.51  sup_immediate_simplified:               192
% 7.53/1.51  sup_given_eliminated:                   1
% 7.53/1.51  comparisons_done:                       0
% 7.53/1.51  comparisons_avoided:                    3
% 7.53/1.51  
% 7.53/1.51  ------ Simplifications
% 7.53/1.51  
% 7.53/1.51  
% 7.53/1.51  sim_fw_subset_subsumed:                 4
% 7.53/1.51  sim_bw_subset_subsumed:                 3
% 7.53/1.51  sim_fw_subsumed:                        15
% 7.53/1.51  sim_bw_subsumed:                        69
% 7.53/1.51  sim_fw_subsumption_res:                 3
% 7.53/1.51  sim_bw_subsumption_res:                 6
% 7.53/1.51  sim_tautology_del:                      4
% 7.53/1.51  sim_eq_tautology_del:                   29
% 7.53/1.51  sim_eq_res_simp:                        3
% 7.53/1.51  sim_fw_demodulated:                     31
% 7.53/1.51  sim_bw_demodulated:                     172
% 7.53/1.51  sim_light_normalised:                   70
% 7.53/1.51  sim_joinable_taut:                      0
% 7.53/1.51  sim_joinable_simp:                      0
% 7.53/1.51  sim_ac_normalised:                      0
% 7.53/1.51  sim_smt_subsumption:                    0
% 7.53/1.51  
%------------------------------------------------------------------------------
