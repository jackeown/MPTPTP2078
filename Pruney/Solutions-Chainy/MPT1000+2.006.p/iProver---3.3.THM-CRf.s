%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:19 EST 2020

% Result     : Theorem 6.74s
% Output     : CNFRefutation 6.74s
% Verified   : 
% Statistics : Number of formulae       :  168 (1836 expanded)
%              Number of clauses        :  106 ( 716 expanded)
%              Number of leaves         :   20 ( 326 expanded)
%              Depth                    :   26
%              Number of atoms          :  430 (6174 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
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
    inference(flattening,[],[f35])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f21,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f37,plain,(
    ? [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) != X0
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f38,plain,(
    ? [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) != X0
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f50,plain,
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

fof(f51,plain,
    ( k8_relset_1(sK2,sK3,sK4,sK3) != sK2
    & ( k1_xboole_0 = sK2
      | k1_xboole_0 != sK3 )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f38,f50])).

fof(f81,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f82,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f51])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f13,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f84,plain,(
    k8_relset_1(sK2,sK3,sK4,sK3) != sK2 ),
    inference(cnf_transformation,[],[f51])).

fof(f83,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f51])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f89,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f76])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f58,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f87,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f79])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f81])).

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
    inference(cnf_transformation,[],[f82])).

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
    inference(cnf_transformation,[],[f73])).

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
    inference(cnf_transformation,[],[f60])).

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
    inference(cnf_transformation,[],[f62])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

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

cnf(c_17836,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3282,c_2521])).

cnf(c_15,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2527,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_18103,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_17836,c_2527])).

cnf(c_20,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_12,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

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

cnf(c_19,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2525,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3820,plain,
    ( k5_relat_1(sK4,k6_relat_1(sK3)) = sK4
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2854,c_2525])).

cnf(c_18125,plain,
    ( k5_relat_1(sK4,k6_relat_1(sK3)) = sK4 ),
    inference(superposition,[status(thm)],[c_18103,c_3820])).

cnf(c_13,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2529,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2526,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_18107,plain,
    ( k10_relat_1(sK4,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK4,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_18103,c_2526])).

cnf(c_19347,plain,
    ( k10_relat_1(sK4,k1_relat_1(k6_relat_1(X0))) = k1_relat_1(k5_relat_1(sK4,k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_2529,c_18107])).

cnf(c_18,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_19364,plain,
    ( k1_relat_1(k5_relat_1(sK4,k6_relat_1(X0))) = k10_relat_1(sK4,X0) ),
    inference(light_normalisation,[status(thm)],[c_19347,c_18])).

cnf(c_19599,plain,
    ( k10_relat_1(sK4,sK3) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_18125,c_19364])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2523,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3212,plain,
    ( k8_relset_1(sK2,sK3,sK4,X0) = k10_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_2522,c_2523])).

cnf(c_29,negated_conjecture,
    ( k8_relset_1(sK2,sK3,sK4,sK3) != sK2 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_3471,plain,
    ( k10_relat_1(sK4,sK3) != sK2 ),
    inference(demodulation,[status(thm)],[c_3212,c_29])).

cnf(c_19705,plain,
    ( k1_relat_1(sK4) != sK2 ),
    inference(demodulation,[status(thm)],[c_19599,c_3471])).

cnf(c_19707,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3837,c_19705])).

cnf(c_19793,plain,
    ( k10_relat_1(sK4,k1_xboole_0) = k1_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_19707,c_19599])).

cnf(c_19951,plain,
    ( k1_relset_1(sK2,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_19707,c_3664])).

cnf(c_30,negated_conjecture,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_19959,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_19707,c_30])).

cnf(c_19960,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_19959])).

cnf(c_19986,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_19951,c_19960])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f89])).

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

cnf(c_19956,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19707,c_2518])).

cnf(c_19967,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19956,c_19960])).

cnf(c_19968,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_19967])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2534,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2532,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f58])).

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

cnf(c_19971,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19968,c_3502])).

cnf(c_19988,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19986,c_19971])).

cnf(c_19958,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_19707,c_2522])).

cnf(c_19963,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19958,c_19960])).

cnf(c_19965,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_19963,c_3502])).

cnf(c_19992,plain,
    ( k1_relat_1(sK4) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_19988,c_19965])).

cnf(c_20827,plain,
    ( k10_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_19793,c_19992])).

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
    inference(cnf_transformation,[],[f87])).

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
    inference(minisat,[status(thm)],[c_20827,c_19705,c_7665,c_4105,c_4104,c_3837,c_3616,c_2979,c_2978,c_29,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n003.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 15:53:12 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 6.74/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.74/1.48  
% 6.74/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.74/1.48  
% 6.74/1.48  ------  iProver source info
% 6.74/1.48  
% 6.74/1.48  git: date: 2020-06-30 10:37:57 +0100
% 6.74/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.74/1.48  git: non_committed_changes: false
% 6.74/1.48  git: last_make_outside_of_git: false
% 6.74/1.48  
% 6.74/1.48  ------ 
% 6.74/1.48  
% 6.74/1.48  ------ Input Options
% 6.74/1.48  
% 6.74/1.48  --out_options                           all
% 6.74/1.48  --tptp_safe_out                         true
% 6.74/1.48  --problem_path                          ""
% 6.74/1.48  --include_path                          ""
% 6.74/1.48  --clausifier                            res/vclausify_rel
% 6.74/1.48  --clausifier_options                    --mode clausify
% 6.74/1.48  --stdin                                 false
% 6.74/1.48  --stats_out                             all
% 6.74/1.48  
% 6.74/1.48  ------ General Options
% 6.74/1.48  
% 6.74/1.48  --fof                                   false
% 6.74/1.48  --time_out_real                         305.
% 6.74/1.48  --time_out_virtual                      -1.
% 6.74/1.48  --symbol_type_check                     false
% 6.74/1.48  --clausify_out                          false
% 6.74/1.48  --sig_cnt_out                           false
% 6.74/1.48  --trig_cnt_out                          false
% 6.74/1.48  --trig_cnt_out_tolerance                1.
% 6.74/1.48  --trig_cnt_out_sk_spl                   false
% 6.74/1.48  --abstr_cl_out                          false
% 6.74/1.48  
% 6.74/1.48  ------ Global Options
% 6.74/1.48  
% 6.74/1.48  --schedule                              default
% 6.74/1.48  --add_important_lit                     false
% 6.74/1.48  --prop_solver_per_cl                    1000
% 6.74/1.48  --min_unsat_core                        false
% 6.74/1.48  --soft_assumptions                      false
% 6.74/1.48  --soft_lemma_size                       3
% 6.74/1.48  --prop_impl_unit_size                   0
% 6.74/1.48  --prop_impl_unit                        []
% 6.74/1.48  --share_sel_clauses                     true
% 6.74/1.48  --reset_solvers                         false
% 6.74/1.48  --bc_imp_inh                            [conj_cone]
% 6.74/1.48  --conj_cone_tolerance                   3.
% 6.74/1.48  --extra_neg_conj                        none
% 6.74/1.48  --large_theory_mode                     true
% 6.74/1.48  --prolific_symb_bound                   200
% 6.74/1.48  --lt_threshold                          2000
% 6.74/1.48  --clause_weak_htbl                      true
% 6.74/1.48  --gc_record_bc_elim                     false
% 6.74/1.48  
% 6.74/1.48  ------ Preprocessing Options
% 6.74/1.48  
% 6.74/1.48  --preprocessing_flag                    true
% 6.74/1.48  --time_out_prep_mult                    0.1
% 6.74/1.48  --splitting_mode                        input
% 6.74/1.48  --splitting_grd                         true
% 6.74/1.48  --splitting_cvd                         false
% 6.74/1.48  --splitting_cvd_svl                     false
% 6.74/1.48  --splitting_nvd                         32
% 6.74/1.48  --sub_typing                            true
% 6.74/1.48  --prep_gs_sim                           true
% 6.74/1.48  --prep_unflatten                        true
% 6.74/1.48  --prep_res_sim                          true
% 6.74/1.48  --prep_upred                            true
% 6.74/1.48  --prep_sem_filter                       exhaustive
% 6.74/1.48  --prep_sem_filter_out                   false
% 6.74/1.48  --pred_elim                             true
% 6.74/1.48  --res_sim_input                         true
% 6.74/1.48  --eq_ax_congr_red                       true
% 6.74/1.48  --pure_diseq_elim                       true
% 6.74/1.48  --brand_transform                       false
% 6.74/1.48  --non_eq_to_eq                          false
% 6.74/1.48  --prep_def_merge                        true
% 6.74/1.48  --prep_def_merge_prop_impl              false
% 6.74/1.48  --prep_def_merge_mbd                    true
% 6.74/1.48  --prep_def_merge_tr_red                 false
% 6.74/1.48  --prep_def_merge_tr_cl                  false
% 6.74/1.48  --smt_preprocessing                     true
% 6.74/1.48  --smt_ac_axioms                         fast
% 6.74/1.48  --preprocessed_out                      false
% 6.74/1.48  --preprocessed_stats                    false
% 6.74/1.48  
% 6.74/1.48  ------ Abstraction refinement Options
% 6.74/1.48  
% 6.74/1.48  --abstr_ref                             []
% 6.74/1.48  --abstr_ref_prep                        false
% 6.74/1.48  --abstr_ref_until_sat                   false
% 6.74/1.48  --abstr_ref_sig_restrict                funpre
% 6.74/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 6.74/1.48  --abstr_ref_under                       []
% 6.74/1.48  
% 6.74/1.48  ------ SAT Options
% 6.74/1.48  
% 6.74/1.48  --sat_mode                              false
% 6.74/1.48  --sat_fm_restart_options                ""
% 6.74/1.48  --sat_gr_def                            false
% 6.74/1.48  --sat_epr_types                         true
% 6.74/1.48  --sat_non_cyclic_types                  false
% 6.74/1.48  --sat_finite_models                     false
% 6.74/1.48  --sat_fm_lemmas                         false
% 6.74/1.48  --sat_fm_prep                           false
% 6.74/1.48  --sat_fm_uc_incr                        true
% 6.74/1.48  --sat_out_model                         small
% 6.74/1.48  --sat_out_clauses                       false
% 6.74/1.48  
% 6.74/1.48  ------ QBF Options
% 6.74/1.48  
% 6.74/1.48  --qbf_mode                              false
% 6.74/1.48  --qbf_elim_univ                         false
% 6.74/1.48  --qbf_dom_inst                          none
% 6.74/1.48  --qbf_dom_pre_inst                      false
% 6.74/1.48  --qbf_sk_in                             false
% 6.74/1.48  --qbf_pred_elim                         true
% 6.74/1.48  --qbf_split                             512
% 6.74/1.48  
% 6.74/1.48  ------ BMC1 Options
% 6.74/1.48  
% 6.74/1.48  --bmc1_incremental                      false
% 6.74/1.48  --bmc1_axioms                           reachable_all
% 6.74/1.48  --bmc1_min_bound                        0
% 6.74/1.48  --bmc1_max_bound                        -1
% 6.74/1.48  --bmc1_max_bound_default                -1
% 6.74/1.48  --bmc1_symbol_reachability              true
% 6.74/1.48  --bmc1_property_lemmas                  false
% 6.74/1.48  --bmc1_k_induction                      false
% 6.74/1.48  --bmc1_non_equiv_states                 false
% 6.74/1.48  --bmc1_deadlock                         false
% 6.74/1.48  --bmc1_ucm                              false
% 6.74/1.48  --bmc1_add_unsat_core                   none
% 6.74/1.48  --bmc1_unsat_core_children              false
% 6.74/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 6.74/1.48  --bmc1_out_stat                         full
% 6.74/1.48  --bmc1_ground_init                      false
% 6.74/1.48  --bmc1_pre_inst_next_state              false
% 6.74/1.48  --bmc1_pre_inst_state                   false
% 6.74/1.48  --bmc1_pre_inst_reach_state             false
% 6.74/1.48  --bmc1_out_unsat_core                   false
% 6.74/1.48  --bmc1_aig_witness_out                  false
% 6.74/1.48  --bmc1_verbose                          false
% 6.74/1.48  --bmc1_dump_clauses_tptp                false
% 6.74/1.48  --bmc1_dump_unsat_core_tptp             false
% 6.74/1.48  --bmc1_dump_file                        -
% 6.74/1.48  --bmc1_ucm_expand_uc_limit              128
% 6.74/1.48  --bmc1_ucm_n_expand_iterations          6
% 6.74/1.48  --bmc1_ucm_extend_mode                  1
% 6.74/1.48  --bmc1_ucm_init_mode                    2
% 6.74/1.48  --bmc1_ucm_cone_mode                    none
% 6.74/1.48  --bmc1_ucm_reduced_relation_type        0
% 6.74/1.48  --bmc1_ucm_relax_model                  4
% 6.74/1.48  --bmc1_ucm_full_tr_after_sat            true
% 6.74/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 6.74/1.48  --bmc1_ucm_layered_model                none
% 6.74/1.48  --bmc1_ucm_max_lemma_size               10
% 6.74/1.48  
% 6.74/1.48  ------ AIG Options
% 6.74/1.48  
% 6.74/1.48  --aig_mode                              false
% 6.74/1.48  
% 6.74/1.48  ------ Instantiation Options
% 6.74/1.48  
% 6.74/1.48  --instantiation_flag                    true
% 6.74/1.48  --inst_sos_flag                         false
% 6.74/1.48  --inst_sos_phase                        true
% 6.74/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.74/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.74/1.48  --inst_lit_sel_side                     num_symb
% 6.74/1.48  --inst_solver_per_active                1400
% 6.74/1.48  --inst_solver_calls_frac                1.
% 6.74/1.48  --inst_passive_queue_type               priority_queues
% 6.74/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.74/1.48  --inst_passive_queues_freq              [25;2]
% 6.74/1.48  --inst_dismatching                      true
% 6.74/1.48  --inst_eager_unprocessed_to_passive     true
% 6.74/1.48  --inst_prop_sim_given                   true
% 6.74/1.48  --inst_prop_sim_new                     false
% 6.74/1.48  --inst_subs_new                         false
% 6.74/1.48  --inst_eq_res_simp                      false
% 6.74/1.48  --inst_subs_given                       false
% 6.74/1.48  --inst_orphan_elimination               true
% 6.74/1.48  --inst_learning_loop_flag               true
% 6.74/1.48  --inst_learning_start                   3000
% 6.74/1.48  --inst_learning_factor                  2
% 6.74/1.48  --inst_start_prop_sim_after_learn       3
% 6.74/1.48  --inst_sel_renew                        solver
% 6.74/1.48  --inst_lit_activity_flag                true
% 6.74/1.48  --inst_restr_to_given                   false
% 6.74/1.48  --inst_activity_threshold               500
% 6.74/1.48  --inst_out_proof                        true
% 6.74/1.48  
% 6.74/1.48  ------ Resolution Options
% 6.74/1.48  
% 6.74/1.48  --resolution_flag                       true
% 6.74/1.48  --res_lit_sel                           adaptive
% 6.74/1.48  --res_lit_sel_side                      none
% 6.74/1.48  --res_ordering                          kbo
% 6.74/1.48  --res_to_prop_solver                    active
% 6.74/1.48  --res_prop_simpl_new                    false
% 6.74/1.48  --res_prop_simpl_given                  true
% 6.74/1.48  --res_passive_queue_type                priority_queues
% 6.74/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.74/1.48  --res_passive_queues_freq               [15;5]
% 6.74/1.48  --res_forward_subs                      full
% 6.74/1.48  --res_backward_subs                     full
% 6.74/1.48  --res_forward_subs_resolution           true
% 6.74/1.48  --res_backward_subs_resolution          true
% 6.74/1.48  --res_orphan_elimination                true
% 6.74/1.48  --res_time_limit                        2.
% 6.74/1.48  --res_out_proof                         true
% 6.74/1.48  
% 6.74/1.48  ------ Superposition Options
% 6.74/1.48  
% 6.74/1.48  --superposition_flag                    true
% 6.74/1.48  --sup_passive_queue_type                priority_queues
% 6.74/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.74/1.48  --sup_passive_queues_freq               [8;1;4]
% 6.74/1.48  --demod_completeness_check              fast
% 6.74/1.48  --demod_use_ground                      true
% 6.74/1.48  --sup_to_prop_solver                    passive
% 6.74/1.48  --sup_prop_simpl_new                    true
% 6.74/1.48  --sup_prop_simpl_given                  true
% 6.74/1.48  --sup_fun_splitting                     false
% 6.74/1.48  --sup_smt_interval                      50000
% 6.74/1.48  
% 6.74/1.48  ------ Superposition Simplification Setup
% 6.74/1.48  
% 6.74/1.48  --sup_indices_passive                   []
% 6.74/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.74/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.74/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.74/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 6.74/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.74/1.48  --sup_full_bw                           [BwDemod]
% 6.74/1.48  --sup_immed_triv                        [TrivRules]
% 6.74/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.74/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.74/1.48  --sup_immed_bw_main                     []
% 6.74/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.74/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 6.74/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.74/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.74/1.48  
% 6.74/1.48  ------ Combination Options
% 6.74/1.48  
% 6.74/1.48  --comb_res_mult                         3
% 6.74/1.48  --comb_sup_mult                         2
% 6.74/1.48  --comb_inst_mult                        10
% 6.74/1.48  
% 6.74/1.48  ------ Debug Options
% 6.74/1.48  
% 6.74/1.48  --dbg_backtrace                         false
% 6.74/1.48  --dbg_dump_prop_clauses                 false
% 6.74/1.48  --dbg_dump_prop_clauses_file            -
% 6.74/1.48  --dbg_out_stat                          false
% 6.74/1.48  ------ Parsing...
% 6.74/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.74/1.48  
% 6.74/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 6.74/1.48  
% 6.74/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.74/1.48  
% 6.74/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.74/1.48  ------ Proving...
% 6.74/1.48  ------ Problem Properties 
% 6.74/1.48  
% 6.74/1.48  
% 6.74/1.48  clauses                                 27
% 6.74/1.48  conjectures                             3
% 6.74/1.48  EPR                                     6
% 6.74/1.48  Horn                                    23
% 6.74/1.48  unary                                   7
% 6.74/1.48  binary                                  13
% 6.74/1.48  lits                                    55
% 6.74/1.48  lits eq                                 17
% 6.74/1.48  fd_pure                                 0
% 6.74/1.48  fd_pseudo                               0
% 6.74/1.48  fd_cond                                 1
% 6.74/1.48  fd_pseudo_cond                          0
% 6.74/1.48  AC symbols                              0
% 6.74/1.48  
% 6.74/1.48  ------ Schedule dynamic 5 is on 
% 6.74/1.48  
% 6.74/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.74/1.48  
% 6.74/1.48  
% 6.74/1.48  ------ 
% 6.74/1.48  Current options:
% 6.74/1.48  ------ 
% 6.74/1.48  
% 6.74/1.48  ------ Input Options
% 6.74/1.48  
% 6.74/1.48  --out_options                           all
% 6.74/1.48  --tptp_safe_out                         true
% 6.74/1.48  --problem_path                          ""
% 6.74/1.48  --include_path                          ""
% 6.74/1.48  --clausifier                            res/vclausify_rel
% 6.74/1.48  --clausifier_options                    --mode clausify
% 6.74/1.48  --stdin                                 false
% 6.74/1.48  --stats_out                             all
% 6.74/1.48  
% 6.74/1.48  ------ General Options
% 6.74/1.48  
% 6.74/1.48  --fof                                   false
% 6.74/1.48  --time_out_real                         305.
% 6.74/1.48  --time_out_virtual                      -1.
% 6.74/1.48  --symbol_type_check                     false
% 6.74/1.48  --clausify_out                          false
% 6.74/1.48  --sig_cnt_out                           false
% 6.74/1.48  --trig_cnt_out                          false
% 6.74/1.48  --trig_cnt_out_tolerance                1.
% 6.74/1.48  --trig_cnt_out_sk_spl                   false
% 6.74/1.48  --abstr_cl_out                          false
% 6.74/1.48  
% 6.74/1.48  ------ Global Options
% 6.74/1.48  
% 6.74/1.48  --schedule                              default
% 6.74/1.48  --add_important_lit                     false
% 6.74/1.48  --prop_solver_per_cl                    1000
% 6.74/1.48  --min_unsat_core                        false
% 6.74/1.48  --soft_assumptions                      false
% 6.74/1.48  --soft_lemma_size                       3
% 6.74/1.48  --prop_impl_unit_size                   0
% 6.74/1.48  --prop_impl_unit                        []
% 6.74/1.48  --share_sel_clauses                     true
% 6.74/1.48  --reset_solvers                         false
% 6.74/1.48  --bc_imp_inh                            [conj_cone]
% 6.74/1.48  --conj_cone_tolerance                   3.
% 6.74/1.48  --extra_neg_conj                        none
% 6.74/1.48  --large_theory_mode                     true
% 6.74/1.48  --prolific_symb_bound                   200
% 6.74/1.48  --lt_threshold                          2000
% 6.74/1.48  --clause_weak_htbl                      true
% 6.74/1.48  --gc_record_bc_elim                     false
% 6.74/1.48  
% 6.74/1.48  ------ Preprocessing Options
% 6.74/1.48  
% 6.74/1.48  --preprocessing_flag                    true
% 6.74/1.48  --time_out_prep_mult                    0.1
% 6.74/1.48  --splitting_mode                        input
% 6.74/1.48  --splitting_grd                         true
% 6.74/1.48  --splitting_cvd                         false
% 6.74/1.48  --splitting_cvd_svl                     false
% 6.74/1.48  --splitting_nvd                         32
% 6.74/1.48  --sub_typing                            true
% 6.74/1.48  --prep_gs_sim                           true
% 6.74/1.48  --prep_unflatten                        true
% 6.74/1.48  --prep_res_sim                          true
% 6.74/1.48  --prep_upred                            true
% 6.74/1.48  --prep_sem_filter                       exhaustive
% 6.74/1.48  --prep_sem_filter_out                   false
% 6.74/1.48  --pred_elim                             true
% 6.74/1.48  --res_sim_input                         true
% 6.74/1.48  --eq_ax_congr_red                       true
% 6.74/1.48  --pure_diseq_elim                       true
% 6.74/1.48  --brand_transform                       false
% 6.74/1.48  --non_eq_to_eq                          false
% 6.74/1.48  --prep_def_merge                        true
% 6.74/1.48  --prep_def_merge_prop_impl              false
% 6.74/1.48  --prep_def_merge_mbd                    true
% 6.74/1.48  --prep_def_merge_tr_red                 false
% 6.74/1.48  --prep_def_merge_tr_cl                  false
% 6.74/1.48  --smt_preprocessing                     true
% 6.74/1.48  --smt_ac_axioms                         fast
% 6.74/1.48  --preprocessed_out                      false
% 6.74/1.48  --preprocessed_stats                    false
% 6.74/1.48  
% 6.74/1.48  ------ Abstraction refinement Options
% 6.74/1.48  
% 6.74/1.48  --abstr_ref                             []
% 6.74/1.48  --abstr_ref_prep                        false
% 6.74/1.48  --abstr_ref_until_sat                   false
% 6.74/1.48  --abstr_ref_sig_restrict                funpre
% 6.74/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 6.74/1.48  --abstr_ref_under                       []
% 6.74/1.48  
% 6.74/1.48  ------ SAT Options
% 6.74/1.48  
% 6.74/1.48  --sat_mode                              false
% 6.74/1.48  --sat_fm_restart_options                ""
% 6.74/1.48  --sat_gr_def                            false
% 6.74/1.48  --sat_epr_types                         true
% 6.74/1.48  --sat_non_cyclic_types                  false
% 6.74/1.48  --sat_finite_models                     false
% 6.74/1.48  --sat_fm_lemmas                         false
% 6.74/1.48  --sat_fm_prep                           false
% 6.74/1.48  --sat_fm_uc_incr                        true
% 6.74/1.48  --sat_out_model                         small
% 6.74/1.48  --sat_out_clauses                       false
% 6.74/1.48  
% 6.74/1.48  ------ QBF Options
% 6.74/1.48  
% 6.74/1.48  --qbf_mode                              false
% 6.74/1.48  --qbf_elim_univ                         false
% 6.74/1.48  --qbf_dom_inst                          none
% 6.74/1.48  --qbf_dom_pre_inst                      false
% 6.74/1.48  --qbf_sk_in                             false
% 6.74/1.48  --qbf_pred_elim                         true
% 6.74/1.48  --qbf_split                             512
% 6.74/1.48  
% 6.74/1.48  ------ BMC1 Options
% 6.74/1.48  
% 6.74/1.48  --bmc1_incremental                      false
% 6.74/1.48  --bmc1_axioms                           reachable_all
% 6.74/1.48  --bmc1_min_bound                        0
% 6.74/1.48  --bmc1_max_bound                        -1
% 6.74/1.48  --bmc1_max_bound_default                -1
% 6.74/1.48  --bmc1_symbol_reachability              true
% 6.74/1.48  --bmc1_property_lemmas                  false
% 6.74/1.48  --bmc1_k_induction                      false
% 6.74/1.48  --bmc1_non_equiv_states                 false
% 6.74/1.48  --bmc1_deadlock                         false
% 6.74/1.48  --bmc1_ucm                              false
% 6.74/1.48  --bmc1_add_unsat_core                   none
% 6.74/1.48  --bmc1_unsat_core_children              false
% 6.74/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 6.74/1.48  --bmc1_out_stat                         full
% 6.74/1.48  --bmc1_ground_init                      false
% 6.74/1.48  --bmc1_pre_inst_next_state              false
% 6.74/1.48  --bmc1_pre_inst_state                   false
% 6.74/1.48  --bmc1_pre_inst_reach_state             false
% 6.74/1.48  --bmc1_out_unsat_core                   false
% 6.74/1.48  --bmc1_aig_witness_out                  false
% 6.74/1.48  --bmc1_verbose                          false
% 6.74/1.48  --bmc1_dump_clauses_tptp                false
% 6.74/1.48  --bmc1_dump_unsat_core_tptp             false
% 6.74/1.48  --bmc1_dump_file                        -
% 6.74/1.48  --bmc1_ucm_expand_uc_limit              128
% 6.74/1.48  --bmc1_ucm_n_expand_iterations          6
% 6.74/1.48  --bmc1_ucm_extend_mode                  1
% 6.74/1.48  --bmc1_ucm_init_mode                    2
% 6.74/1.48  --bmc1_ucm_cone_mode                    none
% 6.74/1.48  --bmc1_ucm_reduced_relation_type        0
% 6.74/1.48  --bmc1_ucm_relax_model                  4
% 6.74/1.48  --bmc1_ucm_full_tr_after_sat            true
% 6.74/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 6.74/1.48  --bmc1_ucm_layered_model                none
% 6.74/1.48  --bmc1_ucm_max_lemma_size               10
% 6.74/1.48  
% 6.74/1.48  ------ AIG Options
% 6.74/1.48  
% 6.74/1.48  --aig_mode                              false
% 6.74/1.48  
% 6.74/1.48  ------ Instantiation Options
% 6.74/1.48  
% 6.74/1.48  --instantiation_flag                    true
% 6.74/1.48  --inst_sos_flag                         false
% 6.74/1.48  --inst_sos_phase                        true
% 6.74/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.74/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.74/1.48  --inst_lit_sel_side                     none
% 6.74/1.48  --inst_solver_per_active                1400
% 6.74/1.48  --inst_solver_calls_frac                1.
% 6.74/1.48  --inst_passive_queue_type               priority_queues
% 6.74/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.74/1.48  --inst_passive_queues_freq              [25;2]
% 6.74/1.48  --inst_dismatching                      true
% 6.74/1.48  --inst_eager_unprocessed_to_passive     true
% 6.74/1.48  --inst_prop_sim_given                   true
% 6.74/1.48  --inst_prop_sim_new                     false
% 6.74/1.48  --inst_subs_new                         false
% 6.74/1.48  --inst_eq_res_simp                      false
% 6.74/1.48  --inst_subs_given                       false
% 6.74/1.48  --inst_orphan_elimination               true
% 6.74/1.48  --inst_learning_loop_flag               true
% 6.74/1.48  --inst_learning_start                   3000
% 6.74/1.48  --inst_learning_factor                  2
% 6.74/1.48  --inst_start_prop_sim_after_learn       3
% 6.74/1.48  --inst_sel_renew                        solver
% 6.74/1.48  --inst_lit_activity_flag                true
% 6.74/1.48  --inst_restr_to_given                   false
% 6.74/1.48  --inst_activity_threshold               500
% 6.74/1.48  --inst_out_proof                        true
% 6.74/1.48  
% 6.74/1.48  ------ Resolution Options
% 6.74/1.48  
% 6.74/1.48  --resolution_flag                       false
% 6.74/1.48  --res_lit_sel                           adaptive
% 6.74/1.48  --res_lit_sel_side                      none
% 6.74/1.48  --res_ordering                          kbo
% 6.74/1.48  --res_to_prop_solver                    active
% 6.74/1.48  --res_prop_simpl_new                    false
% 6.74/1.48  --res_prop_simpl_given                  true
% 6.74/1.48  --res_passive_queue_type                priority_queues
% 6.74/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.74/1.48  --res_passive_queues_freq               [15;5]
% 6.74/1.48  --res_forward_subs                      full
% 6.74/1.48  --res_backward_subs                     full
% 6.74/1.48  --res_forward_subs_resolution           true
% 6.74/1.48  --res_backward_subs_resolution          true
% 6.74/1.48  --res_orphan_elimination                true
% 6.74/1.48  --res_time_limit                        2.
% 6.74/1.48  --res_out_proof                         true
% 6.74/1.48  
% 6.74/1.48  ------ Superposition Options
% 6.74/1.48  
% 6.74/1.48  --superposition_flag                    true
% 6.74/1.48  --sup_passive_queue_type                priority_queues
% 6.74/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.74/1.48  --sup_passive_queues_freq               [8;1;4]
% 6.74/1.48  --demod_completeness_check              fast
% 6.74/1.48  --demod_use_ground                      true
% 6.74/1.48  --sup_to_prop_solver                    passive
% 6.74/1.48  --sup_prop_simpl_new                    true
% 6.74/1.48  --sup_prop_simpl_given                  true
% 6.74/1.48  --sup_fun_splitting                     false
% 6.74/1.48  --sup_smt_interval                      50000
% 6.74/1.48  
% 6.74/1.48  ------ Superposition Simplification Setup
% 6.74/1.48  
% 6.74/1.48  --sup_indices_passive                   []
% 6.74/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.74/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.74/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.74/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 6.74/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.74/1.48  --sup_full_bw                           [BwDemod]
% 6.74/1.48  --sup_immed_triv                        [TrivRules]
% 6.74/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.74/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.74/1.48  --sup_immed_bw_main                     []
% 6.74/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.74/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 6.74/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.74/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.74/1.48  
% 6.74/1.48  ------ Combination Options
% 6.74/1.48  
% 6.74/1.48  --comb_res_mult                         3
% 6.74/1.48  --comb_sup_mult                         2
% 6.74/1.48  --comb_inst_mult                        10
% 6.74/1.48  
% 6.74/1.48  ------ Debug Options
% 6.74/1.48  
% 6.74/1.48  --dbg_backtrace                         false
% 6.74/1.48  --dbg_dump_prop_clauses                 false
% 6.74/1.48  --dbg_dump_prop_clauses_file            -
% 6.74/1.48  --dbg_out_stat                          false
% 6.74/1.48  
% 6.74/1.48  
% 6.74/1.48  
% 6.74/1.48  
% 6.74/1.48  ------ Proving...
% 6.74/1.48  
% 6.74/1.48  
% 6.74/1.48  % SZS status Theorem for theBenchmark.p
% 6.74/1.48  
% 6.74/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 6.74/1.48  
% 6.74/1.48  fof(f18,axiom,(
% 6.74/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 6.74/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.48  
% 6.74/1.48  fof(f35,plain,(
% 6.74/1.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.74/1.48    inference(ennf_transformation,[],[f18])).
% 6.74/1.48  
% 6.74/1.48  fof(f36,plain,(
% 6.74/1.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.74/1.48    inference(flattening,[],[f35])).
% 6.74/1.48  
% 6.74/1.48  fof(f49,plain,(
% 6.74/1.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.74/1.48    inference(nnf_transformation,[],[f36])).
% 6.74/1.48  
% 6.74/1.48  fof(f75,plain,(
% 6.74/1.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.74/1.48    inference(cnf_transformation,[],[f49])).
% 6.74/1.48  
% 6.74/1.48  fof(f19,conjecture,(
% 6.74/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 6.74/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.48  
% 6.74/1.48  fof(f20,negated_conjecture,(
% 6.74/1.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 6.74/1.48    inference(negated_conjecture,[],[f19])).
% 6.74/1.48  
% 6.74/1.48  fof(f21,plain,(
% 6.74/1.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 6.74/1.48    inference(pure_predicate_removal,[],[f20])).
% 6.74/1.48  
% 6.74/1.48  fof(f37,plain,(
% 6.74/1.48    ? [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) != X0 & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1)))),
% 6.74/1.48    inference(ennf_transformation,[],[f21])).
% 6.74/1.48  
% 6.74/1.48  fof(f38,plain,(
% 6.74/1.48    ? [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) != X0 & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1))),
% 6.74/1.48    inference(flattening,[],[f37])).
% 6.74/1.48  
% 6.74/1.48  fof(f50,plain,(
% 6.74/1.48    ? [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) != X0 & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1)) => (k8_relset_1(sK2,sK3,sK4,sK3) != sK2 & (k1_xboole_0 = sK2 | k1_xboole_0 != sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3))),
% 6.74/1.48    introduced(choice_axiom,[])).
% 6.74/1.48  
% 6.74/1.48  fof(f51,plain,(
% 6.74/1.48    k8_relset_1(sK2,sK3,sK4,sK3) != sK2 & (k1_xboole_0 = sK2 | k1_xboole_0 != sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3)),
% 6.74/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f38,f50])).
% 6.74/1.48  
% 6.74/1.48  fof(f81,plain,(
% 6.74/1.48    v1_funct_2(sK4,sK2,sK3)),
% 6.74/1.48    inference(cnf_transformation,[],[f51])).
% 6.74/1.48  
% 6.74/1.48  fof(f82,plain,(
% 6.74/1.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 6.74/1.48    inference(cnf_transformation,[],[f51])).
% 6.74/1.48  
% 6.74/1.48  fof(f16,axiom,(
% 6.74/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 6.74/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.48  
% 6.74/1.48  fof(f33,plain,(
% 6.74/1.48    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.74/1.48    inference(ennf_transformation,[],[f16])).
% 6.74/1.48  
% 6.74/1.48  fof(f73,plain,(
% 6.74/1.48    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.74/1.48    inference(cnf_transformation,[],[f33])).
% 6.74/1.48  
% 6.74/1.48  fof(f6,axiom,(
% 6.74/1.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 6.74/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.48  
% 6.74/1.48  fof(f47,plain,(
% 6.74/1.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 6.74/1.48    inference(nnf_transformation,[],[f6])).
% 6.74/1.48  
% 6.74/1.48  fof(f60,plain,(
% 6.74/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 6.74/1.48    inference(cnf_transformation,[],[f47])).
% 6.74/1.48  
% 6.74/1.48  fof(f7,axiom,(
% 6.74/1.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 6.74/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.48  
% 6.74/1.48  fof(f26,plain,(
% 6.74/1.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 6.74/1.48    inference(ennf_transformation,[],[f7])).
% 6.74/1.48  
% 6.74/1.48  fof(f62,plain,(
% 6.74/1.48    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 6.74/1.48    inference(cnf_transformation,[],[f26])).
% 6.74/1.48  
% 6.74/1.48  fof(f61,plain,(
% 6.74/1.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 6.74/1.48    inference(cnf_transformation,[],[f47])).
% 6.74/1.48  
% 6.74/1.48  fof(f11,axiom,(
% 6.74/1.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 6.74/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.48  
% 6.74/1.48  fof(f67,plain,(
% 6.74/1.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 6.74/1.48    inference(cnf_transformation,[],[f11])).
% 6.74/1.48  
% 6.74/1.48  fof(f15,axiom,(
% 6.74/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 6.74/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.48  
% 6.74/1.48  fof(f22,plain,(
% 6.74/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 6.74/1.48    inference(pure_predicate_removal,[],[f15])).
% 6.74/1.48  
% 6.74/1.48  fof(f32,plain,(
% 6.74/1.48    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.74/1.48    inference(ennf_transformation,[],[f22])).
% 6.74/1.48  
% 6.74/1.48  fof(f72,plain,(
% 6.74/1.48    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.74/1.48    inference(cnf_transformation,[],[f32])).
% 6.74/1.48  
% 6.74/1.48  fof(f8,axiom,(
% 6.74/1.48    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 6.74/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.48  
% 6.74/1.48  fof(f27,plain,(
% 6.74/1.48    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 6.74/1.48    inference(ennf_transformation,[],[f8])).
% 6.74/1.48  
% 6.74/1.48  fof(f48,plain,(
% 6.74/1.48    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 6.74/1.48    inference(nnf_transformation,[],[f27])).
% 6.74/1.48  
% 6.74/1.48  fof(f63,plain,(
% 6.74/1.48    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 6.74/1.48    inference(cnf_transformation,[],[f48])).
% 6.74/1.48  
% 6.74/1.48  fof(f14,axiom,(
% 6.74/1.48    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 6.74/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.48  
% 6.74/1.48  fof(f30,plain,(
% 6.74/1.48    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 6.74/1.48    inference(ennf_transformation,[],[f14])).
% 6.74/1.48  
% 6.74/1.48  fof(f31,plain,(
% 6.74/1.48    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 6.74/1.48    inference(flattening,[],[f30])).
% 6.74/1.48  
% 6.74/1.48  fof(f71,plain,(
% 6.74/1.48    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 6.74/1.48    inference(cnf_transformation,[],[f31])).
% 6.74/1.48  
% 6.74/1.48  fof(f9,axiom,(
% 6.74/1.48    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 6.74/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.48  
% 6.74/1.48  fof(f65,plain,(
% 6.74/1.48    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 6.74/1.48    inference(cnf_transformation,[],[f9])).
% 6.74/1.48  
% 6.74/1.48  fof(f12,axiom,(
% 6.74/1.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 6.74/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.48  
% 6.74/1.48  fof(f29,plain,(
% 6.74/1.48    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 6.74/1.48    inference(ennf_transformation,[],[f12])).
% 6.74/1.48  
% 6.74/1.48  fof(f68,plain,(
% 6.74/1.48    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 6.74/1.48    inference(cnf_transformation,[],[f29])).
% 6.74/1.48  
% 6.74/1.48  fof(f13,axiom,(
% 6.74/1.48    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 6.74/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.48  
% 6.74/1.48  fof(f69,plain,(
% 6.74/1.48    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 6.74/1.48    inference(cnf_transformation,[],[f13])).
% 6.74/1.48  
% 6.74/1.48  fof(f17,axiom,(
% 6.74/1.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 6.74/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.48  
% 6.74/1.48  fof(f34,plain,(
% 6.74/1.48    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.74/1.48    inference(ennf_transformation,[],[f17])).
% 6.74/1.48  
% 6.74/1.48  fof(f74,plain,(
% 6.74/1.48    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.74/1.48    inference(cnf_transformation,[],[f34])).
% 6.74/1.48  
% 6.74/1.48  fof(f84,plain,(
% 6.74/1.48    k8_relset_1(sK2,sK3,sK4,sK3) != sK2),
% 6.74/1.48    inference(cnf_transformation,[],[f51])).
% 6.74/1.48  
% 6.74/1.48  fof(f83,plain,(
% 6.74/1.48    k1_xboole_0 = sK2 | k1_xboole_0 != sK3),
% 6.74/1.48    inference(cnf_transformation,[],[f51])).
% 6.74/1.48  
% 6.74/1.48  fof(f76,plain,(
% 6.74/1.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.74/1.48    inference(cnf_transformation,[],[f49])).
% 6.74/1.48  
% 6.74/1.48  fof(f89,plain,(
% 6.74/1.48    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 6.74/1.48    inference(equality_resolution,[],[f76])).
% 6.74/1.48  
% 6.74/1.48  fof(f3,axiom,(
% 6.74/1.48    v1_xboole_0(k1_xboole_0)),
% 6.74/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.48  
% 6.74/1.48  fof(f57,plain,(
% 6.74/1.48    v1_xboole_0(k1_xboole_0)),
% 6.74/1.48    inference(cnf_transformation,[],[f3])).
% 6.74/1.48  
% 6.74/1.48  fof(f5,axiom,(
% 6.74/1.48    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 6.74/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.48  
% 6.74/1.48  fof(f25,plain,(
% 6.74/1.48    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 6.74/1.48    inference(ennf_transformation,[],[f5])).
% 6.74/1.48  
% 6.74/1.48  fof(f59,plain,(
% 6.74/1.48    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 6.74/1.48    inference(cnf_transformation,[],[f25])).
% 6.74/1.48  
% 6.74/1.48  fof(f4,axiom,(
% 6.74/1.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 6.74/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.48  
% 6.74/1.48  fof(f24,plain,(
% 6.74/1.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 6.74/1.48    inference(ennf_transformation,[],[f4])).
% 6.74/1.48  
% 6.74/1.48  fof(f58,plain,(
% 6.74/1.48    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 6.74/1.48    inference(cnf_transformation,[],[f24])).
% 6.74/1.48  
% 6.74/1.48  fof(f79,plain,(
% 6.74/1.48    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.74/1.48    inference(cnf_transformation,[],[f49])).
% 6.74/1.48  
% 6.74/1.48  fof(f87,plain,(
% 6.74/1.48    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 6.74/1.48    inference(equality_resolution,[],[f79])).
% 6.74/1.48  
% 6.74/1.48  cnf(c_28,plain,
% 6.74/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 6.74/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.74/1.48      | k1_relset_1(X1,X2,X0) = X1
% 6.74/1.48      | k1_xboole_0 = X2 ),
% 6.74/1.48      inference(cnf_transformation,[],[f75]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_32,negated_conjecture,
% 6.74/1.48      ( v1_funct_2(sK4,sK2,sK3) ),
% 6.74/1.48      inference(cnf_transformation,[],[f81]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_1106,plain,
% 6.74/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.74/1.48      | k1_relset_1(X1,X2,X0) = X1
% 6.74/1.48      | sK4 != X0
% 6.74/1.48      | sK3 != X2
% 6.74/1.48      | sK2 != X1
% 6.74/1.48      | k1_xboole_0 = X2 ),
% 6.74/1.48      inference(resolution_lifted,[status(thm)],[c_28,c_32]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_1107,plain,
% 6.74/1.48      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 6.74/1.48      | k1_relset_1(sK2,sK3,sK4) = sK2
% 6.74/1.48      | k1_xboole_0 = sK3 ),
% 6.74/1.48      inference(unflattening,[status(thm)],[c_1106]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_31,negated_conjecture,
% 6.74/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 6.74/1.48      inference(cnf_transformation,[],[f82]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_1109,plain,
% 6.74/1.48      ( k1_relset_1(sK2,sK3,sK4) = sK2 | k1_xboole_0 = sK3 ),
% 6.74/1.48      inference(global_propositional_subsumption,
% 6.74/1.48                [status(thm)],
% 6.74/1.48                [c_1107,c_31]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_2522,plain,
% 6.74/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 6.74/1.48      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_21,plain,
% 6.74/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.74/1.48      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 6.74/1.48      inference(cnf_transformation,[],[f73]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_2524,plain,
% 6.74/1.48      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 6.74/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 6.74/1.48      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_3664,plain,
% 6.74/1.48      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 6.74/1.48      inference(superposition,[status(thm)],[c_2522,c_2524]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_3837,plain,
% 6.74/1.48      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 6.74/1.48      inference(superposition,[status(thm)],[c_1109,c_3664]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_9,plain,
% 6.74/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 6.74/1.48      inference(cnf_transformation,[],[f60]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_2530,plain,
% 6.74/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 6.74/1.48      | r1_tarski(X0,X1) = iProver_top ),
% 6.74/1.48      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_3282,plain,
% 6.74/1.48      ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 6.74/1.48      inference(superposition,[status(thm)],[c_2522,c_2530]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_10,plain,
% 6.74/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.74/1.48      | ~ v1_relat_1(X1)
% 6.74/1.48      | v1_relat_1(X0) ),
% 6.74/1.48      inference(cnf_transformation,[],[f62]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_8,plain,
% 6.74/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 6.74/1.48      inference(cnf_transformation,[],[f61]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_240,plain,
% 6.74/1.48      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 6.74/1.48      inference(prop_impl,[status(thm)],[c_8]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_241,plain,
% 6.74/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 6.74/1.48      inference(renaming,[status(thm)],[c_240]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_298,plain,
% 6.74/1.48      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 6.74/1.48      inference(bin_hyper_res,[status(thm)],[c_10,c_241]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_2521,plain,
% 6.74/1.48      ( r1_tarski(X0,X1) != iProver_top
% 6.74/1.48      | v1_relat_1(X1) != iProver_top
% 6.74/1.48      | v1_relat_1(X0) = iProver_top ),
% 6.74/1.48      inference(predicate_to_equality,[status(thm)],[c_298]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_17836,plain,
% 6.74/1.48      ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
% 6.74/1.48      | v1_relat_1(sK4) = iProver_top ),
% 6.74/1.48      inference(superposition,[status(thm)],[c_3282,c_2521]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_15,plain,
% 6.74/1.48      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 6.74/1.48      inference(cnf_transformation,[],[f67]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_2527,plain,
% 6.74/1.48      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 6.74/1.48      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_18103,plain,
% 6.74/1.48      ( v1_relat_1(sK4) = iProver_top ),
% 6.74/1.48      inference(forward_subsumption_resolution,
% 6.74/1.48                [status(thm)],
% 6.74/1.48                [c_17836,c_2527]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_20,plain,
% 6.74/1.48      ( v5_relat_1(X0,X1)
% 6.74/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 6.74/1.48      inference(cnf_transformation,[],[f72]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_12,plain,
% 6.74/1.48      ( ~ v5_relat_1(X0,X1)
% 6.74/1.48      | r1_tarski(k2_relat_1(X0),X1)
% 6.74/1.48      | ~ v1_relat_1(X0) ),
% 6.74/1.48      inference(cnf_transformation,[],[f63]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_403,plain,
% 6.74/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.74/1.48      | r1_tarski(k2_relat_1(X0),X2)
% 6.74/1.48      | ~ v1_relat_1(X0) ),
% 6.74/1.48      inference(resolution,[status(thm)],[c_20,c_12]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_2520,plain,
% 6.74/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 6.74/1.48      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 6.74/1.48      | v1_relat_1(X0) != iProver_top ),
% 6.74/1.48      inference(predicate_to_equality,[status(thm)],[c_403]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_2854,plain,
% 6.74/1.48      ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top
% 6.74/1.48      | v1_relat_1(sK4) != iProver_top ),
% 6.74/1.48      inference(superposition,[status(thm)],[c_2522,c_2520]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_19,plain,
% 6.74/1.48      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 6.74/1.48      | ~ v1_relat_1(X0)
% 6.74/1.48      | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
% 6.74/1.48      inference(cnf_transformation,[],[f71]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_2525,plain,
% 6.74/1.48      ( k5_relat_1(X0,k6_relat_1(X1)) = X0
% 6.74/1.48      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 6.74/1.48      | v1_relat_1(X0) != iProver_top ),
% 6.74/1.48      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_3820,plain,
% 6.74/1.48      ( k5_relat_1(sK4,k6_relat_1(sK3)) = sK4
% 6.74/1.48      | v1_relat_1(sK4) != iProver_top ),
% 6.74/1.48      inference(superposition,[status(thm)],[c_2854,c_2525]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_18125,plain,
% 6.74/1.48      ( k5_relat_1(sK4,k6_relat_1(sK3)) = sK4 ),
% 6.74/1.48      inference(superposition,[status(thm)],[c_18103,c_3820]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_13,plain,
% 6.74/1.48      ( v1_relat_1(k6_relat_1(X0)) ),
% 6.74/1.48      inference(cnf_transformation,[],[f65]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_2529,plain,
% 6.74/1.48      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 6.74/1.48      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_16,plain,
% 6.74/1.48      ( ~ v1_relat_1(X0)
% 6.74/1.48      | ~ v1_relat_1(X1)
% 6.74/1.48      | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
% 6.74/1.48      inference(cnf_transformation,[],[f68]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_2526,plain,
% 6.74/1.48      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 6.74/1.48      | v1_relat_1(X0) != iProver_top
% 6.74/1.48      | v1_relat_1(X1) != iProver_top ),
% 6.74/1.48      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_18107,plain,
% 6.74/1.48      ( k10_relat_1(sK4,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK4,X0))
% 6.74/1.48      | v1_relat_1(X0) != iProver_top ),
% 6.74/1.48      inference(superposition,[status(thm)],[c_18103,c_2526]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_19347,plain,
% 6.74/1.48      ( k10_relat_1(sK4,k1_relat_1(k6_relat_1(X0))) = k1_relat_1(k5_relat_1(sK4,k6_relat_1(X0))) ),
% 6.74/1.48      inference(superposition,[status(thm)],[c_2529,c_18107]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_18,plain,
% 6.74/1.48      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 6.74/1.48      inference(cnf_transformation,[],[f69]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_19364,plain,
% 6.74/1.48      ( k1_relat_1(k5_relat_1(sK4,k6_relat_1(X0))) = k10_relat_1(sK4,X0) ),
% 6.74/1.48      inference(light_normalisation,[status(thm)],[c_19347,c_18]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_19599,plain,
% 6.74/1.48      ( k10_relat_1(sK4,sK3) = k1_relat_1(sK4) ),
% 6.74/1.48      inference(superposition,[status(thm)],[c_18125,c_19364]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_22,plain,
% 6.74/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.74/1.48      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 6.74/1.48      inference(cnf_transformation,[],[f74]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_2523,plain,
% 6.74/1.48      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 6.74/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 6.74/1.48      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_3212,plain,
% 6.74/1.48      ( k8_relset_1(sK2,sK3,sK4,X0) = k10_relat_1(sK4,X0) ),
% 6.74/1.48      inference(superposition,[status(thm)],[c_2522,c_2523]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_29,negated_conjecture,
% 6.74/1.48      ( k8_relset_1(sK2,sK3,sK4,sK3) != sK2 ),
% 6.74/1.48      inference(cnf_transformation,[],[f84]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_3471,plain,
% 6.74/1.48      ( k10_relat_1(sK4,sK3) != sK2 ),
% 6.74/1.48      inference(demodulation,[status(thm)],[c_3212,c_29]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_19705,plain,
% 6.74/1.48      ( k1_relat_1(sK4) != sK2 ),
% 6.74/1.48      inference(demodulation,[status(thm)],[c_19599,c_3471]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_19707,plain,
% 6.74/1.48      ( sK3 = k1_xboole_0 ),
% 6.74/1.48      inference(superposition,[status(thm)],[c_3837,c_19705]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_19793,plain,
% 6.74/1.48      ( k10_relat_1(sK4,k1_xboole_0) = k1_relat_1(sK4) ),
% 6.74/1.48      inference(demodulation,[status(thm)],[c_19707,c_19599]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_19951,plain,
% 6.74/1.48      ( k1_relset_1(sK2,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
% 6.74/1.48      inference(demodulation,[status(thm)],[c_19707,c_3664]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_30,negated_conjecture,
% 6.74/1.48      ( k1_xboole_0 != sK3 | k1_xboole_0 = sK2 ),
% 6.74/1.48      inference(cnf_transformation,[],[f83]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_19959,plain,
% 6.74/1.48      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 6.74/1.48      inference(demodulation,[status(thm)],[c_19707,c_30]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_19960,plain,
% 6.74/1.48      ( sK2 = k1_xboole_0 ),
% 6.74/1.48      inference(equality_resolution_simp,[status(thm)],[c_19959]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_19986,plain,
% 6.74/1.48      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
% 6.74/1.48      inference(light_normalisation,[status(thm)],[c_19951,c_19960]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_27,plain,
% 6.74/1.48      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 6.74/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 6.74/1.48      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 6.74/1.48      inference(cnf_transformation,[],[f89]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_1093,plain,
% 6.74/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 6.74/1.48      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 6.74/1.48      | sK4 != X0
% 6.74/1.48      | sK3 != X1
% 6.74/1.48      | sK2 != k1_xboole_0 ),
% 6.74/1.48      inference(resolution_lifted,[status(thm)],[c_27,c_32]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_1094,plain,
% 6.74/1.48      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
% 6.74/1.48      | k1_relset_1(k1_xboole_0,sK3,sK4) = k1_xboole_0
% 6.74/1.48      | sK2 != k1_xboole_0 ),
% 6.74/1.48      inference(unflattening,[status(thm)],[c_1093]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_2518,plain,
% 6.74/1.48      ( k1_relset_1(k1_xboole_0,sK3,sK4) = k1_xboole_0
% 6.74/1.48      | sK2 != k1_xboole_0
% 6.74/1.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
% 6.74/1.48      inference(predicate_to_equality,[status(thm)],[c_1094]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_19956,plain,
% 6.74/1.48      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 6.74/1.48      | sK2 != k1_xboole_0
% 6.74/1.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 6.74/1.48      inference(demodulation,[status(thm)],[c_19707,c_2518]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_19967,plain,
% 6.74/1.48      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 6.74/1.48      | k1_xboole_0 != k1_xboole_0
% 6.74/1.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 6.74/1.48      inference(light_normalisation,[status(thm)],[c_19956,c_19960]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_19968,plain,
% 6.74/1.48      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 6.74/1.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 6.74/1.48      inference(equality_resolution_simp,[status(thm)],[c_19967]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_5,plain,
% 6.74/1.48      ( v1_xboole_0(k1_xboole_0) ),
% 6.74/1.48      inference(cnf_transformation,[],[f57]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_2534,plain,
% 6.74/1.48      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 6.74/1.48      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_7,plain,
% 6.74/1.48      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
% 6.74/1.48      inference(cnf_transformation,[],[f59]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_2532,plain,
% 6.74/1.48      ( v1_xboole_0(X0) != iProver_top
% 6.74/1.48      | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
% 6.74/1.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_6,plain,
% 6.74/1.48      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 6.74/1.48      inference(cnf_transformation,[],[f58]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_2533,plain,
% 6.74/1.48      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 6.74/1.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_3144,plain,
% 6.74/1.48      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
% 6.74/1.48      | v1_xboole_0(X1) != iProver_top ),
% 6.74/1.48      inference(superposition,[status(thm)],[c_2532,c_2533]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_3502,plain,
% 6.74/1.48      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 6.74/1.48      inference(superposition,[status(thm)],[c_2534,c_3144]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_19971,plain,
% 6.74/1.48      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 6.74/1.48      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 6.74/1.48      inference(demodulation,[status(thm)],[c_19968,c_3502]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_19988,plain,
% 6.74/1.48      ( k1_relat_1(sK4) = k1_xboole_0
% 6.74/1.48      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 6.74/1.48      inference(demodulation,[status(thm)],[c_19986,c_19971]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_19958,plain,
% 6.74/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
% 6.74/1.48      inference(demodulation,[status(thm)],[c_19707,c_2522]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_19963,plain,
% 6.74/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 6.74/1.48      inference(light_normalisation,[status(thm)],[c_19958,c_19960]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_19965,plain,
% 6.74/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 6.74/1.48      inference(demodulation,[status(thm)],[c_19963,c_3502]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_19992,plain,
% 6.74/1.48      ( k1_relat_1(sK4) = k1_xboole_0 ),
% 6.74/1.48      inference(forward_subsumption_resolution,
% 6.74/1.48                [status(thm)],
% 6.74/1.48                [c_19988,c_19965]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_20827,plain,
% 6.74/1.48      ( k10_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 6.74/1.48      inference(light_normalisation,[status(thm)],[c_19793,c_19992]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_1949,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_2792,plain,
% 6.74/1.48      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 6.74/1.48      inference(instantiation,[status(thm)],[c_1949]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_7664,plain,
% 6.74/1.48      ( k10_relat_1(sK4,X0) != X1
% 6.74/1.48      | sK2 != X1
% 6.74/1.48      | sK2 = k10_relat_1(sK4,X0) ),
% 6.74/1.48      inference(instantiation,[status(thm)],[c_2792]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_7665,plain,
% 6.74/1.48      ( k10_relat_1(sK4,k1_xboole_0) != k1_xboole_0
% 6.74/1.48      | sK2 = k10_relat_1(sK4,k1_xboole_0)
% 6.74/1.48      | sK2 != k1_xboole_0 ),
% 6.74/1.48      inference(instantiation,[status(thm)],[c_7664]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_1960,plain,
% 6.74/1.48      ( X0 != X1 | k10_relat_1(X2,X0) = k10_relat_1(X2,X1) ),
% 6.74/1.48      theory(equality) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_4103,plain,
% 6.74/1.48      ( k10_relat_1(sK4,sK3) = k10_relat_1(sK4,X0) | sK3 != X0 ),
% 6.74/1.48      inference(instantiation,[status(thm)],[c_1960]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_4105,plain,
% 6.74/1.48      ( k10_relat_1(sK4,sK3) = k10_relat_1(sK4,k1_xboole_0)
% 6.74/1.48      | sK3 != k1_xboole_0 ),
% 6.74/1.48      inference(instantiation,[status(thm)],[c_4103]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_3171,plain,
% 6.74/1.48      ( k10_relat_1(sK4,sK3) != X0
% 6.74/1.48      | sK2 != X0
% 6.74/1.48      | sK2 = k10_relat_1(sK4,sK3) ),
% 6.74/1.48      inference(instantiation,[status(thm)],[c_2792]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_4102,plain,
% 6.74/1.48      ( k10_relat_1(sK4,sK3) != k10_relat_1(sK4,X0)
% 6.74/1.48      | sK2 != k10_relat_1(sK4,X0)
% 6.74/1.48      | sK2 = k10_relat_1(sK4,sK3) ),
% 6.74/1.48      inference(instantiation,[status(thm)],[c_3171]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_4104,plain,
% 6.74/1.48      ( k10_relat_1(sK4,sK3) != k10_relat_1(sK4,k1_xboole_0)
% 6.74/1.48      | sK2 = k10_relat_1(sK4,sK3)
% 6.74/1.48      | sK2 != k10_relat_1(sK4,k1_xboole_0) ),
% 6.74/1.48      inference(instantiation,[status(thm)],[c_4102]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_24,plain,
% 6.74/1.48      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 6.74/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 6.74/1.48      | k1_xboole_0 = X1
% 6.74/1.48      | k1_xboole_0 = X0 ),
% 6.74/1.48      inference(cnf_transformation,[],[f87]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_1073,plain,
% 6.74/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 6.74/1.48      | sK4 != X0
% 6.74/1.48      | sK3 != k1_xboole_0
% 6.74/1.48      | sK2 != X1
% 6.74/1.48      | k1_xboole_0 = X0
% 6.74/1.48      | k1_xboole_0 = X1 ),
% 6.74/1.48      inference(resolution_lifted,[status(thm)],[c_24,c_32]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_1074,plain,
% 6.74/1.48      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 6.74/1.48      | sK3 != k1_xboole_0
% 6.74/1.48      | k1_xboole_0 = sK4
% 6.74/1.48      | k1_xboole_0 = sK2 ),
% 6.74/1.48      inference(unflattening,[status(thm)],[c_1073]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_2519,plain,
% 6.74/1.48      ( sK3 != k1_xboole_0
% 6.74/1.48      | k1_xboole_0 = sK4
% 6.74/1.48      | k1_xboole_0 = sK2
% 6.74/1.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 6.74/1.48      inference(predicate_to_equality,[status(thm)],[c_1074]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_3523,plain,
% 6.74/1.48      ( sK4 = k1_xboole_0
% 6.74/1.48      | sK3 != k1_xboole_0
% 6.74/1.48      | sK2 = k1_xboole_0
% 6.74/1.48      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 6.74/1.48      inference(demodulation,[status(thm)],[c_3502,c_2519]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_96,plain,
% 6.74/1.48      ( ~ v1_xboole_0(k1_xboole_0) | k1_xboole_0 = k1_xboole_0 ),
% 6.74/1.48      inference(instantiation,[status(thm)],[c_6]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_2728,plain,
% 6.74/1.48      ( sK2 != X0 | sK2 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 6.74/1.48      inference(instantiation,[status(thm)],[c_1949]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_2793,plain,
% 6.74/1.48      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 6.74/1.48      inference(instantiation,[status(thm)],[c_2728]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_1948,plain,( X0 = X0 ),theory(equality) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_2794,plain,
% 6.74/1.48      ( sK2 = sK2 ),
% 6.74/1.48      inference(instantiation,[status(thm)],[c_1948]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_3496,plain,
% 6.74/1.48      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 6.74/1.48      inference(instantiation,[status(thm)],[c_1949]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_3497,plain,
% 6.74/1.48      ( sK3 != k1_xboole_0
% 6.74/1.48      | k1_xboole_0 = sK3
% 6.74/1.48      | k1_xboole_0 != k1_xboole_0 ),
% 6.74/1.48      inference(instantiation,[status(thm)],[c_3496]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_3615,plain,
% 6.74/1.48      ( sK2 = k1_xboole_0 | sK3 != k1_xboole_0 ),
% 6.74/1.48      inference(global_propositional_subsumption,
% 6.74/1.48                [status(thm)],
% 6.74/1.48                [c_3523,c_30,c_96,c_5,c_2793,c_2794,c_3497]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_3616,plain,
% 6.74/1.48      ( sK3 != k1_xboole_0 | sK2 = k1_xboole_0 ),
% 6.74/1.48      inference(renaming,[status(thm)],[c_3615]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_2773,plain,
% 6.74/1.48      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 6.74/1.48      | k8_relset_1(sK2,sK3,sK4,X0) = k10_relat_1(sK4,X0) ),
% 6.74/1.48      inference(instantiation,[status(thm)],[c_22]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_2979,plain,
% 6.74/1.48      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 6.74/1.48      | k8_relset_1(sK2,sK3,sK4,sK3) = k10_relat_1(sK4,sK3) ),
% 6.74/1.48      inference(instantiation,[status(thm)],[c_2773]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_2726,plain,
% 6.74/1.48      ( k8_relset_1(sK2,sK3,sK4,sK3) != X0
% 6.74/1.48      | k8_relset_1(sK2,sK3,sK4,sK3) = sK2
% 6.74/1.48      | sK2 != X0 ),
% 6.74/1.48      inference(instantiation,[status(thm)],[c_1949]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(c_2978,plain,
% 6.74/1.48      ( k8_relset_1(sK2,sK3,sK4,sK3) != k10_relat_1(sK4,sK3)
% 6.74/1.48      | k8_relset_1(sK2,sK3,sK4,sK3) = sK2
% 6.74/1.48      | sK2 != k10_relat_1(sK4,sK3) ),
% 6.74/1.48      inference(instantiation,[status(thm)],[c_2726]) ).
% 6.74/1.48  
% 6.74/1.48  cnf(contradiction,plain,
% 6.74/1.48      ( $false ),
% 6.74/1.48      inference(minisat,
% 6.74/1.48                [status(thm)],
% 6.74/1.48                [c_20827,c_19705,c_7665,c_4105,c_4104,c_3837,c_3616,
% 6.74/1.48                 c_2979,c_2978,c_29,c_31]) ).
% 6.74/1.48  
% 6.74/1.48  
% 6.74/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 6.74/1.48  
% 6.74/1.48  ------                               Statistics
% 6.74/1.48  
% 6.74/1.48  ------ General
% 6.74/1.48  
% 6.74/1.48  abstr_ref_over_cycles:                  0
% 6.74/1.48  abstr_ref_under_cycles:                 0
% 6.74/1.48  gc_basic_clause_elim:                   0
% 6.74/1.48  forced_gc_time:                         0
% 6.74/1.48  parsing_time:                           0.009
% 6.74/1.48  unif_index_cands_time:                  0.
% 6.74/1.48  unif_index_add_time:                    0.
% 6.74/1.48  orderings_time:                         0.
% 6.74/1.48  out_proof_time:                         0.008
% 6.74/1.48  total_time:                             0.527
% 6.74/1.48  num_of_symbols:                         53
% 6.74/1.48  num_of_terms:                           13393
% 6.74/1.48  
% 6.74/1.48  ------ Preprocessing
% 6.74/1.48  
% 6.74/1.48  num_of_splits:                          0
% 6.74/1.48  num_of_split_atoms:                     0
% 6.74/1.48  num_of_reused_defs:                     0
% 6.74/1.48  num_eq_ax_congr_red:                    28
% 6.74/1.48  num_of_sem_filtered_clauses:            1
% 6.74/1.48  num_of_subtypes:                        0
% 6.74/1.48  monotx_restored_types:                  0
% 6.74/1.48  sat_num_of_epr_types:                   0
% 6.74/1.48  sat_num_of_non_cyclic_types:            0
% 6.74/1.48  sat_guarded_non_collapsed_types:        0
% 6.74/1.48  num_pure_diseq_elim:                    0
% 6.74/1.48  simp_replaced_by:                       0
% 6.74/1.48  res_preprocessed:                       145
% 6.74/1.48  prep_upred:                             0
% 6.74/1.48  prep_unflattend:                        89
% 6.74/1.48  smt_new_axioms:                         0
% 6.74/1.48  pred_elim_cands:                        5
% 6.74/1.48  pred_elim:                              2
% 6.74/1.48  pred_elim_cl:                           6
% 6.74/1.48  pred_elim_cycles:                       7
% 6.74/1.48  merged_defs:                            8
% 6.74/1.48  merged_defs_ncl:                        0
% 6.74/1.48  bin_hyper_res:                          9
% 6.74/1.48  prep_cycles:                            4
% 6.74/1.48  pred_elim_time:                         0.023
% 6.74/1.48  splitting_time:                         0.
% 6.74/1.48  sem_filter_time:                        0.
% 6.74/1.48  monotx_time:                            0.
% 6.74/1.48  subtype_inf_time:                       0.
% 6.74/1.48  
% 6.74/1.48  ------ Problem properties
% 6.74/1.48  
% 6.74/1.48  clauses:                                27
% 6.74/1.48  conjectures:                            3
% 6.74/1.48  epr:                                    6
% 6.74/1.48  horn:                                   23
% 6.74/1.48  ground:                                 7
% 6.74/1.48  unary:                                  7
% 6.74/1.48  binary:                                 13
% 6.74/1.48  lits:                                   55
% 6.74/1.48  lits_eq:                                17
% 6.74/1.48  fd_pure:                                0
% 6.74/1.48  fd_pseudo:                              0
% 6.74/1.48  fd_cond:                                1
% 6.74/1.48  fd_pseudo_cond:                         0
% 6.74/1.48  ac_symbols:                             0
% 6.74/1.48  
% 6.74/1.48  ------ Propositional Solver
% 6.74/1.48  
% 6.74/1.48  prop_solver_calls:                      31
% 6.74/1.48  prop_fast_solver_calls:                 1650
% 6.74/1.48  smt_solver_calls:                       0
% 6.74/1.48  smt_fast_solver_calls:                  0
% 6.74/1.48  prop_num_of_clauses:                    7362
% 6.74/1.48  prop_preprocess_simplified:             12634
% 6.74/1.48  prop_fo_subsumed:                       28
% 6.74/1.48  prop_solver_time:                       0.
% 6.74/1.48  smt_solver_time:                        0.
% 6.74/1.48  smt_fast_solver_time:                   0.
% 6.74/1.48  prop_fast_solver_time:                  0.
% 6.74/1.48  prop_unsat_core_time:                   0.
% 6.74/1.48  
% 6.74/1.48  ------ QBF
% 6.74/1.48  
% 6.74/1.48  qbf_q_res:                              0
% 6.74/1.48  qbf_num_tautologies:                    0
% 6.74/1.48  qbf_prep_cycles:                        0
% 6.74/1.48  
% 6.74/1.48  ------ BMC1
% 6.74/1.48  
% 6.74/1.48  bmc1_current_bound:                     -1
% 6.74/1.48  bmc1_last_solved_bound:                 -1
% 6.74/1.48  bmc1_unsat_core_size:                   -1
% 6.74/1.48  bmc1_unsat_core_parents_size:           -1
% 6.74/1.48  bmc1_merge_next_fun:                    0
% 6.74/1.48  bmc1_unsat_core_clauses_time:           0.
% 6.74/1.48  
% 6.74/1.48  ------ Instantiation
% 6.74/1.48  
% 6.74/1.48  inst_num_of_clauses:                    2247
% 6.74/1.48  inst_num_in_passive:                    390
% 6.74/1.48  inst_num_in_active:                     1111
% 6.74/1.48  inst_num_in_unprocessed:                747
% 6.74/1.48  inst_num_of_loops:                      1490
% 6.74/1.48  inst_num_of_learning_restarts:          0
% 6.74/1.48  inst_num_moves_active_passive:          375
% 6.74/1.48  inst_lit_activity:                      0
% 6.74/1.48  inst_lit_activity_moves:                0
% 6.74/1.48  inst_num_tautologies:                   0
% 6.74/1.48  inst_num_prop_implied:                  0
% 6.74/1.48  inst_num_existing_simplified:           0
% 6.74/1.48  inst_num_eq_res_simplified:             0
% 6.74/1.48  inst_num_child_elim:                    0
% 6.74/1.48  inst_num_of_dismatching_blockings:      667
% 6.74/1.48  inst_num_of_non_proper_insts:           2427
% 6.74/1.48  inst_num_of_duplicates:                 0
% 6.74/1.48  inst_inst_num_from_inst_to_res:         0
% 6.74/1.48  inst_dismatching_checking_time:         0.
% 6.74/1.48  
% 6.74/1.48  ------ Resolution
% 6.74/1.48  
% 6.74/1.48  res_num_of_clauses:                     0
% 6.74/1.48  res_num_in_passive:                     0
% 6.74/1.48  res_num_in_active:                      0
% 6.74/1.48  res_num_of_loops:                       149
% 6.74/1.48  res_forward_subset_subsumed:            178
% 6.74/1.48  res_backward_subset_subsumed:           4
% 6.74/1.48  res_forward_subsumed:                   0
% 6.74/1.48  res_backward_subsumed:                  0
% 6.74/1.48  res_forward_subsumption_resolution:     0
% 6.74/1.48  res_backward_subsumption_resolution:    0
% 6.74/1.48  res_clause_to_clause_subsumption:       4845
% 6.74/1.48  res_orphan_elimination:                 0
% 6.74/1.48  res_tautology_del:                      297
% 6.74/1.48  res_num_eq_res_simplified:              0
% 6.74/1.48  res_num_sel_changes:                    0
% 6.74/1.48  res_moves_from_active_to_pass:          0
% 6.74/1.48  
% 6.74/1.48  ------ Superposition
% 6.74/1.48  
% 6.74/1.48  sup_time_total:                         0.
% 6.74/1.48  sup_time_generating:                    0.
% 6.74/1.48  sup_time_sim_full:                      0.
% 6.74/1.48  sup_time_sim_immed:                     0.
% 6.74/1.48  
% 6.74/1.48  sup_num_of_clauses:                     454
% 6.74/1.48  sup_num_in_active:                      123
% 6.74/1.48  sup_num_in_passive:                     331
% 6.74/1.48  sup_num_of_loops:                       297
% 6.74/1.48  sup_fw_superposition:                   414
% 6.74/1.48  sup_bw_superposition:                   217
% 6.74/1.48  sup_immediate_simplified:               192
% 6.74/1.48  sup_given_eliminated:                   1
% 6.74/1.48  comparisons_done:                       0
% 6.74/1.48  comparisons_avoided:                    3
% 6.74/1.48  
% 6.74/1.48  ------ Simplifications
% 6.74/1.48  
% 6.74/1.48  
% 6.74/1.48  sim_fw_subset_subsumed:                 4
% 6.74/1.48  sim_bw_subset_subsumed:                 3
% 6.74/1.48  sim_fw_subsumed:                        15
% 6.74/1.48  sim_bw_subsumed:                        69
% 6.74/1.48  sim_fw_subsumption_res:                 3
% 6.74/1.48  sim_bw_subsumption_res:                 6
% 6.74/1.48  sim_tautology_del:                      4
% 6.74/1.48  sim_eq_tautology_del:                   29
% 6.74/1.48  sim_eq_res_simp:                        3
% 6.74/1.48  sim_fw_demodulated:                     31
% 6.74/1.48  sim_bw_demodulated:                     172
% 6.74/1.48  sim_light_normalised:                   70
% 6.74/1.48  sim_joinable_taut:                      0
% 6.74/1.48  sim_joinable_simp:                      0
% 6.74/1.48  sim_ac_normalised:                      0
% 6.74/1.48  sim_smt_subsumption:                    0
% 6.74/1.48  
%------------------------------------------------------------------------------
