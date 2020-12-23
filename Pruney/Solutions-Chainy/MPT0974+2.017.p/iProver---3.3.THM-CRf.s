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
% DateTime   : Thu Dec  3 12:01:20 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 480 expanded)
%              Number of clauses        :   82 ( 166 expanded)
%              Number of leaves         :   12 ( 103 expanded)
%              Depth                    :   17
%              Number of atoms          :  356 (2740 expanded)
%              Number of equality atoms :  171 (1292 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( k2_relset_1(X1,X2,X4) = X2
              & k2_relset_1(X0,X1,X3) = X1 )
           => ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
              | k1_xboole_0 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X4,X1,X2)
              & v1_funct_1(X4) )
           => ( ( k2_relset_1(X1,X2,X4) = X2
                & k2_relset_1(X0,X1,X3) = X1 )
             => ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
                | k1_xboole_0 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f12,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_1(X4) )
           => ( ( k2_relset_1(X1,X2,X4) = X2
                & k2_relset_1(X0,X1,X3) = X1 )
             => ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
                | k1_xboole_0 = X2 ) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2
          & k1_xboole_0 != X2
          & k2_relset_1(X1,X2,X4) = X2
          & k2_relset_1(X0,X1,X3) = X1
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2
          & k1_xboole_0 != X2
          & k2_relset_1(X1,X2,X4) = X2
          & k2_relset_1(X0,X1,X3) = X1
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f25])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2
          & k1_xboole_0 != X2
          & k2_relset_1(X1,X2,X4) = X2
          & k2_relset_1(X0,X1,X3) = X1
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X4) )
     => ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,sK4)) != X2
        & k1_xboole_0 != X2
        & k2_relset_1(X1,X2,sK4) = X2
        & k2_relset_1(X0,X1,X3) = X1
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2
            & k1_xboole_0 != X2
            & k2_relset_1(X1,X2,X4) = X2
            & k2_relset_1(X0,X1,X3) = X1
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) != sK2
          & k1_xboole_0 != sK2
          & k2_relset_1(sK1,sK2,X4) = sK2
          & k2_relset_1(sK0,sK1,sK3) = sK1
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) != sK2
    & k1_xboole_0 != sK2
    & k2_relset_1(sK1,sK2,sK4) = sK2
    & k2_relset_1(sK0,sK1,sK3) = sK1
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f26,f28,f27])).

fof(f41,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f43,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f21])).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f42,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f23])).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f40,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f44,plain,(
    k2_relset_1(sK0,sK1,sK3) = sK1 ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f45,plain,(
    k2_relset_1(sK1,sK2,sK4) = sK2 ),
    inference(cnf_transformation,[],[f29])).

fof(f47,plain,(
    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) != sK2 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_275,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_567,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_275])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_277,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_565,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_277])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_284,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
    | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X2_48,X3_48)))
    | m1_subset_1(k1_partfun1(X2_48,X3_48,X0_48,X1_48,X1_46,X0_46),k1_zfmisc_1(k2_zfmisc_1(X2_48,X1_48)))
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(X1_46) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_562,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
    | m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X2_48,X3_48))) != iProver_top
    | m1_subset_1(k1_partfun1(X2_48,X3_48,X0_48,X1_48,X1_46,X0_46),k1_zfmisc_1(k2_zfmisc_1(X2_48,X1_48))) = iProver_top
    | v1_funct_1(X0_46) != iProver_top
    | v1_funct_1(X1_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_284])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_285,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
    | k2_relset_1(X0_48,X1_48,X0_46) = k2_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_561,plain,
    ( k2_relset_1(X0_48,X1_48,X0_46) = k2_relat_1(X0_46)
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_285])).

cnf(c_1545,plain,
    ( k2_relset_1(X0_48,X1_48,k1_partfun1(X0_48,X2_48,X3_48,X1_48,X0_46,X1_46)) = k2_relat_1(k1_partfun1(X0_48,X2_48,X3_48,X1_48,X0_46,X1_46))
    | m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X3_48,X1_48))) != iProver_top
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_48,X2_48))) != iProver_top
    | v1_funct_1(X1_46) != iProver_top
    | v1_funct_1(X0_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_562,c_561])).

cnf(c_4151,plain,
    ( k2_relset_1(X0_48,sK2,k1_partfun1(X0_48,X1_48,sK1,sK2,X0_46,sK4)) = k2_relat_1(k1_partfun1(X0_48,X1_48,sK1,sK2,X0_46,sK4))
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
    | v1_funct_1(X0_46) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_565,c_1545])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_20,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4319,plain,
    ( v1_funct_1(X0_46) != iProver_top
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
    | k2_relset_1(X0_48,sK2,k1_partfun1(X0_48,X1_48,sK1,sK2,X0_46,sK4)) = k2_relat_1(k1_partfun1(X0_48,X1_48,sK1,sK2,X0_46,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4151,c_20])).

cnf(c_4320,plain,
    ( k2_relset_1(X0_48,sK2,k1_partfun1(X0_48,X1_48,sK1,sK2,X0_46,sK4)) = k2_relat_1(k1_partfun1(X0_48,X1_48,sK1,sK2,X0_46,sK4))
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
    | v1_funct_1(X0_46) != iProver_top ),
    inference(renaming,[status(thm)],[c_4319])).

cnf(c_4329,plain,
    ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = k2_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_567,c_4320])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_282,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
    | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X2_48,X3_48)))
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(X1_46)
    | k1_partfun1(X2_48,X3_48,X0_48,X1_48,X1_46,X0_46) = k5_relat_1(X1_46,X0_46) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_564,plain,
    ( k1_partfun1(X0_48,X1_48,X2_48,X3_48,X0_46,X1_46) = k5_relat_1(X0_46,X1_46)
    | m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X2_48,X3_48))) != iProver_top
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
    | v1_funct_1(X1_46) != iProver_top
    | v1_funct_1(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_282])).

cnf(c_1904,plain,
    ( k1_partfun1(sK0,sK1,X0_48,X1_48,sK3,X0_46) = k5_relat_1(sK3,X0_46)
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
    | v1_funct_1(X0_46) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_567,c_564])).

cnf(c_17,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_18,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2444,plain,
    ( v1_funct_1(X0_46) != iProver_top
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
    | k1_partfun1(sK0,sK1,X0_48,X1_48,sK3,X0_46) = k5_relat_1(sK3,X0_46) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1904,c_18])).

cnf(c_2445,plain,
    ( k1_partfun1(sK0,sK1,X0_48,X1_48,sK3,X0_46) = k5_relat_1(sK3,X0_46)
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
    | v1_funct_1(X0_46) != iProver_top ),
    inference(renaming,[status(thm)],[c_2444])).

cnf(c_2451,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_565,c_2445])).

cnf(c_732,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(sK4)
    | k1_partfun1(X0_48,X1_48,sK1,sK2,X0_46,sK4) = k5_relat_1(X0_46,sK4) ),
    inference(instantiation,[status(thm)],[c_282])).

cnf(c_799,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_732])).

cnf(c_2704,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2451,c_17,c_16,c_15,c_14,c_799])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_289,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
    | ~ v1_relat_1(X1_46)
    | v1_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_557,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(X1_46)) != iProver_top
    | v1_relat_1(X1_46) != iProver_top
    | v1_relat_1(X0_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_289])).

cnf(c_834,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_567,c_557])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_288,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_48,X1_48)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1144,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_288])).

cnf(c_1145,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1144])).

cnf(c_1245,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_834,c_1145])).

cnf(c_833,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_565,c_557])).

cnf(c_1141,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_288])).

cnf(c_1142,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1141])).

cnf(c_1237,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_833,c_1142])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_286,plain,
    ( ~ v1_relat_1(X0_46)
    | ~ v1_relat_1(X1_46)
    | k9_relat_1(X1_46,k2_relat_1(X0_46)) = k2_relat_1(k5_relat_1(X0_46,X1_46)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_560,plain,
    ( k9_relat_1(X0_46,k2_relat_1(X1_46)) = k2_relat_1(k5_relat_1(X1_46,X0_46))
    | v1_relat_1(X1_46) != iProver_top
    | v1_relat_1(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_286])).

cnf(c_1446,plain,
    ( k9_relat_1(sK4,k2_relat_1(X0_46)) = k2_relat_1(k5_relat_1(X0_46,sK4))
    | v1_relat_1(X0_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_1237,c_560])).

cnf(c_2757,plain,
    ( k9_relat_1(sK4,k2_relat_1(sK3)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_1245,c_1446])).

cnf(c_927,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_567,c_561])).

cnf(c_13,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK3) = sK1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_278,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK3) = sK1 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_929,plain,
    ( k2_relat_1(sK3) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_927,c_278])).

cnf(c_2763,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = k9_relat_1(sK4,sK1) ),
    inference(light_normalisation,[status(thm)],[c_2757,c_929])).

cnf(c_5,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_4,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_163,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_5,c_4])).

cnf(c_273,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
    | ~ v1_relat_1(X0_46)
    | k7_relat_1(X0_46,X0_48) = X0_46 ),
    inference(subtyping,[status(esa)],[c_163])).

cnf(c_569,plain,
    ( k7_relat_1(X0_46,X0_48) = X0_46
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
    | v1_relat_1(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_273])).

cnf(c_319,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_48,X1_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_288])).

cnf(c_342,plain,
    ( k7_relat_1(X0_46,X0_48) = X0_46
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
    | v1_relat_1(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_273])).

cnf(c_675,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
    | v1_relat_1(X0_46)
    | ~ v1_relat_1(k2_zfmisc_1(X0_48,X1_48)) ),
    inference(instantiation,[status(thm)],[c_289])).

cnf(c_676,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
    | v1_relat_1(X0_46) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X0_48,X1_48)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_675])).

cnf(c_3001,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
    | k7_relat_1(X0_46,X0_48) = X0_46 ),
    inference(global_propositional_subsumption,[status(thm)],[c_569,c_319,c_342,c_676])).

cnf(c_3002,plain,
    ( k7_relat_1(X0_46,X0_48) = X0_46
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3001])).

cnf(c_3009,plain,
    ( k7_relat_1(sK4,sK1) = sK4 ),
    inference(superposition,[status(thm)],[c_565,c_3002])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_287,plain,
    ( ~ v1_relat_1(X0_46)
    | k2_relat_1(k7_relat_1(X0_46,X0_48)) = k9_relat_1(X0_46,X0_48) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_559,plain,
    ( k2_relat_1(k7_relat_1(X0_46,X0_48)) = k9_relat_1(X0_46,X0_48)
    | v1_relat_1(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_287])).

cnf(c_1242,plain,
    ( k2_relat_1(k7_relat_1(sK4,X0_48)) = k9_relat_1(sK4,X0_48) ),
    inference(superposition,[status(thm)],[c_1237,c_559])).

cnf(c_3030,plain,
    ( k9_relat_1(sK4,sK1) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_3009,c_1242])).

cnf(c_926,plain,
    ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_565,c_561])).

cnf(c_12,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK4) = sK2 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_279,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK4) = sK2 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_932,plain,
    ( k2_relat_1(sK4) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_926,c_279])).

cnf(c_3031,plain,
    ( k9_relat_1(sK4,sK1) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_3030,c_932])).

cnf(c_3804,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_2763,c_3031])).

cnf(c_4360,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4329,c_2704,c_3804])).

cnf(c_10,negated_conjecture,
    ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) != sK2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_281,negated_conjecture,
    ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) != sK2 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_2707,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) != sK2 ),
    inference(demodulation,[status(thm)],[c_2704,c_281])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4360,c_2707,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:13:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.79/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/0.98  
% 2.79/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.79/0.98  
% 2.79/0.98  ------  iProver source info
% 2.79/0.98  
% 2.79/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.79/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.79/0.98  git: non_committed_changes: false
% 2.79/0.98  git: last_make_outside_of_git: false
% 2.79/0.98  
% 2.79/0.98  ------ 
% 2.79/0.98  
% 2.79/0.98  ------ Input Options
% 2.79/0.98  
% 2.79/0.98  --out_options                           all
% 2.79/0.98  --tptp_safe_out                         true
% 2.79/0.98  --problem_path                          ""
% 2.79/0.98  --include_path                          ""
% 2.79/0.98  --clausifier                            res/vclausify_rel
% 2.79/0.98  --clausifier_options                    --mode clausify
% 2.79/0.98  --stdin                                 false
% 2.79/0.98  --stats_out                             all
% 2.79/0.98  
% 2.79/0.98  ------ General Options
% 2.79/0.98  
% 2.79/0.98  --fof                                   false
% 2.79/0.98  --time_out_real                         305.
% 2.79/0.98  --time_out_virtual                      -1.
% 2.79/0.98  --symbol_type_check                     false
% 2.79/0.98  --clausify_out                          false
% 2.79/0.98  --sig_cnt_out                           false
% 2.79/0.98  --trig_cnt_out                          false
% 2.79/0.98  --trig_cnt_out_tolerance                1.
% 2.79/0.98  --trig_cnt_out_sk_spl                   false
% 2.79/0.98  --abstr_cl_out                          false
% 2.79/0.98  
% 2.79/0.98  ------ Global Options
% 2.79/0.98  
% 2.79/0.98  --schedule                              default
% 2.79/0.98  --add_important_lit                     false
% 2.79/0.98  --prop_solver_per_cl                    1000
% 2.79/0.98  --min_unsat_core                        false
% 2.79/0.98  --soft_assumptions                      false
% 2.79/0.98  --soft_lemma_size                       3
% 2.79/0.98  --prop_impl_unit_size                   0
% 2.79/0.98  --prop_impl_unit                        []
% 2.79/0.98  --share_sel_clauses                     true
% 2.79/0.98  --reset_solvers                         false
% 2.79/0.98  --bc_imp_inh                            [conj_cone]
% 2.79/0.98  --conj_cone_tolerance                   3.
% 2.79/0.98  --extra_neg_conj                        none
% 2.79/0.98  --large_theory_mode                     true
% 2.79/0.98  --prolific_symb_bound                   200
% 2.79/0.98  --lt_threshold                          2000
% 2.79/0.98  --clause_weak_htbl                      true
% 2.79/0.98  --gc_record_bc_elim                     false
% 2.79/0.98  
% 2.79/0.98  ------ Preprocessing Options
% 2.79/0.98  
% 2.79/0.98  --preprocessing_flag                    true
% 2.79/0.98  --time_out_prep_mult                    0.1
% 2.79/0.98  --splitting_mode                        input
% 2.79/0.98  --splitting_grd                         true
% 2.79/0.98  --splitting_cvd                         false
% 2.79/0.98  --splitting_cvd_svl                     false
% 2.79/0.98  --splitting_nvd                         32
% 2.79/0.98  --sub_typing                            true
% 2.79/0.98  --prep_gs_sim                           true
% 2.79/0.98  --prep_unflatten                        true
% 2.79/0.98  --prep_res_sim                          true
% 2.79/0.98  --prep_upred                            true
% 2.79/0.98  --prep_sem_filter                       exhaustive
% 2.79/0.98  --prep_sem_filter_out                   false
% 2.79/0.98  --pred_elim                             true
% 2.79/0.98  --res_sim_input                         true
% 2.79/0.98  --eq_ax_congr_red                       true
% 2.79/0.98  --pure_diseq_elim                       true
% 2.79/0.98  --brand_transform                       false
% 2.79/0.98  --non_eq_to_eq                          false
% 2.79/0.98  --prep_def_merge                        true
% 2.79/0.98  --prep_def_merge_prop_impl              false
% 2.79/0.98  --prep_def_merge_mbd                    true
% 2.79/0.98  --prep_def_merge_tr_red                 false
% 2.79/0.98  --prep_def_merge_tr_cl                  false
% 2.79/0.98  --smt_preprocessing                     true
% 2.79/0.98  --smt_ac_axioms                         fast
% 2.79/0.98  --preprocessed_out                      false
% 2.79/0.98  --preprocessed_stats                    false
% 2.79/0.98  
% 2.79/0.98  ------ Abstraction refinement Options
% 2.79/0.98  
% 2.79/0.98  --abstr_ref                             []
% 2.79/0.98  --abstr_ref_prep                        false
% 2.79/0.98  --abstr_ref_until_sat                   false
% 2.79/0.98  --abstr_ref_sig_restrict                funpre
% 2.79/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.79/0.98  --abstr_ref_under                       []
% 2.79/0.98  
% 2.79/0.98  ------ SAT Options
% 2.79/0.98  
% 2.79/0.98  --sat_mode                              false
% 2.79/0.98  --sat_fm_restart_options                ""
% 2.79/0.98  --sat_gr_def                            false
% 2.79/0.98  --sat_epr_types                         true
% 2.79/0.98  --sat_non_cyclic_types                  false
% 2.79/0.98  --sat_finite_models                     false
% 2.79/0.98  --sat_fm_lemmas                         false
% 2.79/0.98  --sat_fm_prep                           false
% 2.79/0.98  --sat_fm_uc_incr                        true
% 2.79/0.98  --sat_out_model                         small
% 2.79/0.98  --sat_out_clauses                       false
% 2.79/0.98  
% 2.79/0.98  ------ QBF Options
% 2.79/0.98  
% 2.79/0.98  --qbf_mode                              false
% 2.79/0.98  --qbf_elim_univ                         false
% 2.79/0.98  --qbf_dom_inst                          none
% 2.79/0.98  --qbf_dom_pre_inst                      false
% 2.79/0.98  --qbf_sk_in                             false
% 2.79/0.98  --qbf_pred_elim                         true
% 2.79/0.98  --qbf_split                             512
% 2.79/0.98  
% 2.79/0.98  ------ BMC1 Options
% 2.79/0.98  
% 2.79/0.98  --bmc1_incremental                      false
% 2.79/0.98  --bmc1_axioms                           reachable_all
% 2.79/0.98  --bmc1_min_bound                        0
% 2.79/0.98  --bmc1_max_bound                        -1
% 2.79/0.98  --bmc1_max_bound_default                -1
% 2.79/0.98  --bmc1_symbol_reachability              true
% 2.79/0.98  --bmc1_property_lemmas                  false
% 2.79/0.98  --bmc1_k_induction                      false
% 2.79/0.98  --bmc1_non_equiv_states                 false
% 2.79/0.98  --bmc1_deadlock                         false
% 2.79/0.98  --bmc1_ucm                              false
% 2.79/0.98  --bmc1_add_unsat_core                   none
% 2.79/0.98  --bmc1_unsat_core_children              false
% 2.79/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.79/0.98  --bmc1_out_stat                         full
% 2.79/0.98  --bmc1_ground_init                      false
% 2.79/0.98  --bmc1_pre_inst_next_state              false
% 2.79/0.98  --bmc1_pre_inst_state                   false
% 2.79/0.98  --bmc1_pre_inst_reach_state             false
% 2.79/0.98  --bmc1_out_unsat_core                   false
% 2.79/0.98  --bmc1_aig_witness_out                  false
% 2.79/0.98  --bmc1_verbose                          false
% 2.79/0.98  --bmc1_dump_clauses_tptp                false
% 2.79/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.79/0.98  --bmc1_dump_file                        -
% 2.79/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.79/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.79/0.98  --bmc1_ucm_extend_mode                  1
% 2.79/0.98  --bmc1_ucm_init_mode                    2
% 2.79/0.98  --bmc1_ucm_cone_mode                    none
% 2.79/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.79/0.98  --bmc1_ucm_relax_model                  4
% 2.79/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.79/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.79/0.98  --bmc1_ucm_layered_model                none
% 2.79/0.98  --bmc1_ucm_max_lemma_size               10
% 2.79/0.98  
% 2.79/0.98  ------ AIG Options
% 2.79/0.98  
% 2.79/0.98  --aig_mode                              false
% 2.79/0.98  
% 2.79/0.98  ------ Instantiation Options
% 2.79/0.98  
% 2.79/0.98  --instantiation_flag                    true
% 2.79/0.98  --inst_sos_flag                         false
% 2.79/0.98  --inst_sos_phase                        true
% 2.79/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.79/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.79/0.98  --inst_lit_sel_side                     num_symb
% 2.79/0.98  --inst_solver_per_active                1400
% 2.79/0.98  --inst_solver_calls_frac                1.
% 2.79/0.98  --inst_passive_queue_type               priority_queues
% 2.79/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.79/0.98  --inst_passive_queues_freq              [25;2]
% 2.79/0.98  --inst_dismatching                      true
% 2.79/0.98  --inst_eager_unprocessed_to_passive     true
% 2.79/0.98  --inst_prop_sim_given                   true
% 2.79/0.98  --inst_prop_sim_new                     false
% 2.79/0.98  --inst_subs_new                         false
% 2.79/0.98  --inst_eq_res_simp                      false
% 2.79/0.98  --inst_subs_given                       false
% 2.79/0.98  --inst_orphan_elimination               true
% 2.79/0.98  --inst_learning_loop_flag               true
% 2.79/0.98  --inst_learning_start                   3000
% 2.79/0.98  --inst_learning_factor                  2
% 2.79/0.98  --inst_start_prop_sim_after_learn       3
% 2.79/0.98  --inst_sel_renew                        solver
% 2.79/0.98  --inst_lit_activity_flag                true
% 2.79/0.98  --inst_restr_to_given                   false
% 2.79/0.98  --inst_activity_threshold               500
% 2.79/0.98  --inst_out_proof                        true
% 2.79/0.98  
% 2.79/0.98  ------ Resolution Options
% 2.79/0.98  
% 2.79/0.98  --resolution_flag                       true
% 2.79/0.98  --res_lit_sel                           adaptive
% 2.79/0.98  --res_lit_sel_side                      none
% 2.79/0.98  --res_ordering                          kbo
% 2.79/0.98  --res_to_prop_solver                    active
% 2.79/0.98  --res_prop_simpl_new                    false
% 2.79/0.98  --res_prop_simpl_given                  true
% 2.79/0.98  --res_passive_queue_type                priority_queues
% 2.79/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.79/0.98  --res_passive_queues_freq               [15;5]
% 2.79/0.98  --res_forward_subs                      full
% 2.79/0.98  --res_backward_subs                     full
% 2.79/0.98  --res_forward_subs_resolution           true
% 2.79/0.98  --res_backward_subs_resolution          true
% 2.79/0.98  --res_orphan_elimination                true
% 2.79/0.98  --res_time_limit                        2.
% 2.79/0.98  --res_out_proof                         true
% 2.79/0.98  
% 2.79/0.98  ------ Superposition Options
% 2.79/0.98  
% 2.79/0.98  --superposition_flag                    true
% 2.79/0.98  --sup_passive_queue_type                priority_queues
% 2.79/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.79/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.79/0.98  --demod_completeness_check              fast
% 2.79/0.98  --demod_use_ground                      true
% 2.79/0.98  --sup_to_prop_solver                    passive
% 2.79/0.98  --sup_prop_simpl_new                    true
% 2.79/0.98  --sup_prop_simpl_given                  true
% 2.79/0.98  --sup_fun_splitting                     false
% 2.79/0.98  --sup_smt_interval                      50000
% 2.79/0.98  
% 2.79/0.98  ------ Superposition Simplification Setup
% 2.79/0.98  
% 2.79/0.98  --sup_indices_passive                   []
% 2.79/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.79/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/0.98  --sup_full_bw                           [BwDemod]
% 2.79/0.98  --sup_immed_triv                        [TrivRules]
% 2.79/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.79/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/0.98  --sup_immed_bw_main                     []
% 2.79/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.79/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.79/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.79/0.98  
% 2.79/0.98  ------ Combination Options
% 2.79/0.98  
% 2.79/0.98  --comb_res_mult                         3
% 2.79/0.98  --comb_sup_mult                         2
% 2.79/0.98  --comb_inst_mult                        10
% 2.79/0.98  
% 2.79/0.98  ------ Debug Options
% 2.79/0.98  
% 2.79/0.98  --dbg_backtrace                         false
% 2.79/0.98  --dbg_dump_prop_clauses                 false
% 2.79/0.98  --dbg_dump_prop_clauses_file            -
% 2.79/0.98  --dbg_out_stat                          false
% 2.79/0.98  ------ Parsing...
% 2.79/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.79/0.98  
% 2.79/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.79/0.98  
% 2.79/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.79/0.98  
% 2.79/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.79/0.98  ------ Proving...
% 2.79/0.98  ------ Problem Properties 
% 2.79/0.98  
% 2.79/0.98  
% 2.79/0.98  clauses                                 17
% 2.79/0.98  conjectures                             8
% 2.79/0.98  EPR                                     3
% 2.79/0.98  Horn                                    17
% 2.79/0.98  unary                                   9
% 2.79/0.98  binary                                  2
% 2.79/0.98  lits                                    37
% 2.79/0.98  lits eq                                 9
% 2.79/0.98  fd_pure                                 0
% 2.79/0.98  fd_pseudo                               0
% 2.79/0.98  fd_cond                                 0
% 2.79/0.98  fd_pseudo_cond                          0
% 2.79/0.98  AC symbols                              0
% 2.79/0.98  
% 2.79/0.98  ------ Schedule dynamic 5 is on 
% 2.79/0.98  
% 2.79/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.79/0.98  
% 2.79/0.98  
% 2.79/0.98  ------ 
% 2.79/0.98  Current options:
% 2.79/0.98  ------ 
% 2.79/0.98  
% 2.79/0.98  ------ Input Options
% 2.79/0.98  
% 2.79/0.98  --out_options                           all
% 2.79/0.98  --tptp_safe_out                         true
% 2.79/0.98  --problem_path                          ""
% 2.79/0.98  --include_path                          ""
% 2.79/0.98  --clausifier                            res/vclausify_rel
% 2.79/0.98  --clausifier_options                    --mode clausify
% 2.79/0.98  --stdin                                 false
% 2.79/0.98  --stats_out                             all
% 2.79/0.98  
% 2.79/0.98  ------ General Options
% 2.79/0.98  
% 2.79/0.98  --fof                                   false
% 2.79/0.98  --time_out_real                         305.
% 2.79/0.98  --time_out_virtual                      -1.
% 2.79/0.98  --symbol_type_check                     false
% 2.79/0.98  --clausify_out                          false
% 2.79/0.98  --sig_cnt_out                           false
% 2.79/0.98  --trig_cnt_out                          false
% 2.79/0.98  --trig_cnt_out_tolerance                1.
% 2.79/0.98  --trig_cnt_out_sk_spl                   false
% 2.79/0.98  --abstr_cl_out                          false
% 2.79/0.98  
% 2.79/0.98  ------ Global Options
% 2.79/0.98  
% 2.79/0.98  --schedule                              default
% 2.79/0.98  --add_important_lit                     false
% 2.79/0.98  --prop_solver_per_cl                    1000
% 2.79/0.98  --min_unsat_core                        false
% 2.79/0.98  --soft_assumptions                      false
% 2.79/0.98  --soft_lemma_size                       3
% 2.79/0.98  --prop_impl_unit_size                   0
% 2.79/0.98  --prop_impl_unit                        []
% 2.79/0.98  --share_sel_clauses                     true
% 2.79/0.98  --reset_solvers                         false
% 2.79/0.98  --bc_imp_inh                            [conj_cone]
% 2.79/0.98  --conj_cone_tolerance                   3.
% 2.79/0.98  --extra_neg_conj                        none
% 2.79/0.98  --large_theory_mode                     true
% 2.79/0.98  --prolific_symb_bound                   200
% 2.79/0.98  --lt_threshold                          2000
% 2.79/0.98  --clause_weak_htbl                      true
% 2.79/0.98  --gc_record_bc_elim                     false
% 2.79/0.98  
% 2.79/0.98  ------ Preprocessing Options
% 2.79/0.98  
% 2.79/0.98  --preprocessing_flag                    true
% 2.79/0.98  --time_out_prep_mult                    0.1
% 2.79/0.98  --splitting_mode                        input
% 2.79/0.98  --splitting_grd                         true
% 2.79/0.98  --splitting_cvd                         false
% 2.79/0.98  --splitting_cvd_svl                     false
% 2.79/0.98  --splitting_nvd                         32
% 2.79/0.98  --sub_typing                            true
% 2.79/0.98  --prep_gs_sim                           true
% 2.79/0.98  --prep_unflatten                        true
% 2.79/0.98  --prep_res_sim                          true
% 2.79/0.98  --prep_upred                            true
% 2.79/0.98  --prep_sem_filter                       exhaustive
% 2.79/0.98  --prep_sem_filter_out                   false
% 2.79/0.98  --pred_elim                             true
% 2.79/0.98  --res_sim_input                         true
% 2.79/0.98  --eq_ax_congr_red                       true
% 2.79/0.98  --pure_diseq_elim                       true
% 2.79/0.98  --brand_transform                       false
% 2.79/0.98  --non_eq_to_eq                          false
% 2.79/0.98  --prep_def_merge                        true
% 2.79/0.98  --prep_def_merge_prop_impl              false
% 2.79/0.98  --prep_def_merge_mbd                    true
% 2.79/0.98  --prep_def_merge_tr_red                 false
% 2.79/0.98  --prep_def_merge_tr_cl                  false
% 2.79/0.98  --smt_preprocessing                     true
% 2.79/0.98  --smt_ac_axioms                         fast
% 2.79/0.98  --preprocessed_out                      false
% 2.79/0.98  --preprocessed_stats                    false
% 2.79/0.98  
% 2.79/0.98  ------ Abstraction refinement Options
% 2.79/0.98  
% 2.79/0.98  --abstr_ref                             []
% 2.79/0.98  --abstr_ref_prep                        false
% 2.79/0.98  --abstr_ref_until_sat                   false
% 2.79/0.98  --abstr_ref_sig_restrict                funpre
% 2.79/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.79/0.98  --abstr_ref_under                       []
% 2.79/0.98  
% 2.79/0.98  ------ SAT Options
% 2.79/0.98  
% 2.79/0.98  --sat_mode                              false
% 2.79/0.98  --sat_fm_restart_options                ""
% 2.79/0.98  --sat_gr_def                            false
% 2.79/0.98  --sat_epr_types                         true
% 2.79/0.98  --sat_non_cyclic_types                  false
% 2.79/0.98  --sat_finite_models                     false
% 2.79/0.98  --sat_fm_lemmas                         false
% 2.79/0.98  --sat_fm_prep                           false
% 2.79/0.98  --sat_fm_uc_incr                        true
% 2.79/0.98  --sat_out_model                         small
% 2.79/0.98  --sat_out_clauses                       false
% 2.79/0.98  
% 2.79/0.98  ------ QBF Options
% 2.79/0.98  
% 2.79/0.98  --qbf_mode                              false
% 2.79/0.98  --qbf_elim_univ                         false
% 2.79/0.98  --qbf_dom_inst                          none
% 2.79/0.98  --qbf_dom_pre_inst                      false
% 2.79/0.98  --qbf_sk_in                             false
% 2.79/0.98  --qbf_pred_elim                         true
% 2.79/0.98  --qbf_split                             512
% 2.79/0.98  
% 2.79/0.98  ------ BMC1 Options
% 2.79/0.98  
% 2.79/0.98  --bmc1_incremental                      false
% 2.79/0.98  --bmc1_axioms                           reachable_all
% 2.79/0.98  --bmc1_min_bound                        0
% 2.79/0.98  --bmc1_max_bound                        -1
% 2.79/0.98  --bmc1_max_bound_default                -1
% 2.79/0.98  --bmc1_symbol_reachability              true
% 2.79/0.98  --bmc1_property_lemmas                  false
% 2.79/0.98  --bmc1_k_induction                      false
% 2.79/0.98  --bmc1_non_equiv_states                 false
% 2.79/0.98  --bmc1_deadlock                         false
% 2.79/0.98  --bmc1_ucm                              false
% 2.79/0.98  --bmc1_add_unsat_core                   none
% 2.79/0.98  --bmc1_unsat_core_children              false
% 2.79/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.79/0.98  --bmc1_out_stat                         full
% 2.79/0.98  --bmc1_ground_init                      false
% 2.79/0.98  --bmc1_pre_inst_next_state              false
% 2.79/0.98  --bmc1_pre_inst_state                   false
% 2.79/0.98  --bmc1_pre_inst_reach_state             false
% 2.79/0.98  --bmc1_out_unsat_core                   false
% 2.79/0.98  --bmc1_aig_witness_out                  false
% 2.79/0.98  --bmc1_verbose                          false
% 2.79/0.98  --bmc1_dump_clauses_tptp                false
% 2.79/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.79/0.98  --bmc1_dump_file                        -
% 2.79/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.79/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.79/0.98  --bmc1_ucm_extend_mode                  1
% 2.79/0.98  --bmc1_ucm_init_mode                    2
% 2.79/0.98  --bmc1_ucm_cone_mode                    none
% 2.79/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.79/0.98  --bmc1_ucm_relax_model                  4
% 2.79/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.79/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.79/0.98  --bmc1_ucm_layered_model                none
% 2.79/0.98  --bmc1_ucm_max_lemma_size               10
% 2.79/0.98  
% 2.79/0.98  ------ AIG Options
% 2.79/0.98  
% 2.79/0.98  --aig_mode                              false
% 2.79/0.98  
% 2.79/0.98  ------ Instantiation Options
% 2.79/0.98  
% 2.79/0.98  --instantiation_flag                    true
% 2.79/0.98  --inst_sos_flag                         false
% 2.79/0.98  --inst_sos_phase                        true
% 2.79/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.79/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.79/0.98  --inst_lit_sel_side                     none
% 2.79/0.98  --inst_solver_per_active                1400
% 2.79/0.98  --inst_solver_calls_frac                1.
% 2.79/0.98  --inst_passive_queue_type               priority_queues
% 2.79/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.79/0.98  --inst_passive_queues_freq              [25;2]
% 2.79/0.98  --inst_dismatching                      true
% 2.79/0.98  --inst_eager_unprocessed_to_passive     true
% 2.79/0.98  --inst_prop_sim_given                   true
% 2.79/0.98  --inst_prop_sim_new                     false
% 2.79/0.98  --inst_subs_new                         false
% 2.79/0.98  --inst_eq_res_simp                      false
% 2.79/0.98  --inst_subs_given                       false
% 2.79/0.98  --inst_orphan_elimination               true
% 2.79/0.98  --inst_learning_loop_flag               true
% 2.79/0.98  --inst_learning_start                   3000
% 2.79/0.98  --inst_learning_factor                  2
% 2.79/0.98  --inst_start_prop_sim_after_learn       3
% 2.79/0.98  --inst_sel_renew                        solver
% 2.79/0.98  --inst_lit_activity_flag                true
% 2.79/0.98  --inst_restr_to_given                   false
% 2.79/0.98  --inst_activity_threshold               500
% 2.79/0.98  --inst_out_proof                        true
% 2.79/0.98  
% 2.79/0.98  ------ Resolution Options
% 2.79/0.98  
% 2.79/0.98  --resolution_flag                       false
% 2.79/0.98  --res_lit_sel                           adaptive
% 2.79/0.98  --res_lit_sel_side                      none
% 2.79/0.98  --res_ordering                          kbo
% 2.79/0.98  --res_to_prop_solver                    active
% 2.79/0.98  --res_prop_simpl_new                    false
% 2.79/0.98  --res_prop_simpl_given                  true
% 2.79/0.98  --res_passive_queue_type                priority_queues
% 2.79/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.79/0.98  --res_passive_queues_freq               [15;5]
% 2.79/0.98  --res_forward_subs                      full
% 2.79/0.98  --res_backward_subs                     full
% 2.79/0.98  --res_forward_subs_resolution           true
% 2.79/0.98  --res_backward_subs_resolution          true
% 2.79/0.98  --res_orphan_elimination                true
% 2.79/0.98  --res_time_limit                        2.
% 2.79/0.98  --res_out_proof                         true
% 2.79/0.98  
% 2.79/0.98  ------ Superposition Options
% 2.79/0.98  
% 2.79/0.98  --superposition_flag                    true
% 2.79/0.98  --sup_passive_queue_type                priority_queues
% 2.79/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.79/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.79/0.98  --demod_completeness_check              fast
% 2.79/0.99  --demod_use_ground                      true
% 2.79/0.99  --sup_to_prop_solver                    passive
% 2.79/0.99  --sup_prop_simpl_new                    true
% 2.79/0.99  --sup_prop_simpl_given                  true
% 2.79/0.99  --sup_fun_splitting                     false
% 2.79/0.99  --sup_smt_interval                      50000
% 2.79/0.99  
% 2.79/0.99  ------ Superposition Simplification Setup
% 2.79/0.99  
% 2.79/0.99  --sup_indices_passive                   []
% 2.79/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.79/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/0.99  --sup_full_bw                           [BwDemod]
% 2.79/0.99  --sup_immed_triv                        [TrivRules]
% 2.79/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.79/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/0.99  --sup_immed_bw_main                     []
% 2.79/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.79/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.79/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.79/0.99  
% 2.79/0.99  ------ Combination Options
% 2.79/0.99  
% 2.79/0.99  --comb_res_mult                         3
% 2.79/0.99  --comb_sup_mult                         2
% 2.79/0.99  --comb_inst_mult                        10
% 2.79/0.99  
% 2.79/0.99  ------ Debug Options
% 2.79/0.99  
% 2.79/0.99  --dbg_backtrace                         false
% 2.79/0.99  --dbg_dump_prop_clauses                 false
% 2.79/0.99  --dbg_dump_prop_clauses_file            -
% 2.79/0.99  --dbg_out_stat                          false
% 2.79/0.99  
% 2.79/0.99  
% 2.79/0.99  
% 2.79/0.99  
% 2.79/0.99  ------ Proving...
% 2.79/0.99  
% 2.79/0.99  
% 2.79/0.99  % SZS status Theorem for theBenchmark.p
% 2.79/0.99  
% 2.79/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.79/0.99  
% 2.79/0.99  fof(f10,conjecture,(
% 2.79/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1) => (k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 | k1_xboole_0 = X2))))),
% 2.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f11,negated_conjecture,(
% 2.79/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1) => (k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 | k1_xboole_0 = X2))))),
% 2.79/0.99    inference(negated_conjecture,[],[f10])).
% 2.79/0.99  
% 2.79/0.99  fof(f12,plain,(
% 2.79/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4)) => ((k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1) => (k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 | k1_xboole_0 = X2))))),
% 2.79/0.99    inference(pure_predicate_removal,[],[f11])).
% 2.79/0.99  
% 2.79/0.99  fof(f25,plain,(
% 2.79/0.99    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2 & k1_xboole_0 != X2) & (k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 2.79/0.99    inference(ennf_transformation,[],[f12])).
% 2.79/0.99  
% 2.79/0.99  fof(f26,plain,(
% 2.79/0.99    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2 & k1_xboole_0 != X2 & k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 2.79/0.99    inference(flattening,[],[f25])).
% 2.79/0.99  
% 2.79/0.99  fof(f28,plain,(
% 2.79/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2 & k1_xboole_0 != X2 & k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4)) => (k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,sK4)) != X2 & k1_xboole_0 != X2 & k2_relset_1(X1,X2,sK4) = X2 & k2_relset_1(X0,X1,X3) = X1 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK4))) )),
% 2.79/0.99    introduced(choice_axiom,[])).
% 2.79/0.99  
% 2.79/0.99  fof(f27,plain,(
% 2.79/0.99    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2 & k1_xboole_0 != X2 & k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (? [X4] : (k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) != sK2 & k1_xboole_0 != sK2 & k2_relset_1(sK1,sK2,X4) = sK2 & k2_relset_1(sK0,sK1,sK3) = sK1 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK3))),
% 2.79/0.99    introduced(choice_axiom,[])).
% 2.79/0.99  
% 2.79/0.99  fof(f29,plain,(
% 2.79/0.99    (k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) != sK2 & k1_xboole_0 != sK2 & k2_relset_1(sK1,sK2,sK4) = sK2 & k2_relset_1(sK0,sK1,sK3) = sK1 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK3)),
% 2.79/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f26,f28,f27])).
% 2.79/0.99  
% 2.79/0.99  fof(f41,plain,(
% 2.79/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.79/0.99    inference(cnf_transformation,[],[f29])).
% 2.79/0.99  
% 2.79/0.99  fof(f43,plain,(
% 2.79/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.79/0.99    inference(cnf_transformation,[],[f29])).
% 2.79/0.99  
% 2.79/0.99  fof(f8,axiom,(
% 2.79/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f21,plain,(
% 2.79/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.79/0.99    inference(ennf_transformation,[],[f8])).
% 2.79/0.99  
% 2.79/0.99  fof(f22,plain,(
% 2.79/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.79/0.99    inference(flattening,[],[f21])).
% 2.79/0.99  
% 2.79/0.99  fof(f38,plain,(
% 2.79/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.79/0.99    inference(cnf_transformation,[],[f22])).
% 2.79/0.99  
% 2.79/0.99  fof(f7,axiom,(
% 2.79/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f20,plain,(
% 2.79/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.79/0.99    inference(ennf_transformation,[],[f7])).
% 2.79/0.99  
% 2.79/0.99  fof(f36,plain,(
% 2.79/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.79/0.99    inference(cnf_transformation,[],[f20])).
% 2.79/0.99  
% 2.79/0.99  fof(f42,plain,(
% 2.79/0.99    v1_funct_1(sK4)),
% 2.79/0.99    inference(cnf_transformation,[],[f29])).
% 2.79/0.99  
% 2.79/0.99  fof(f9,axiom,(
% 2.79/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 2.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f23,plain,(
% 2.79/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.79/0.99    inference(ennf_transformation,[],[f9])).
% 2.79/0.99  
% 2.79/0.99  fof(f24,plain,(
% 2.79/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.79/0.99    inference(flattening,[],[f23])).
% 2.79/0.99  
% 2.79/0.99  fof(f39,plain,(
% 2.79/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.79/0.99    inference(cnf_transformation,[],[f24])).
% 2.79/0.99  
% 2.79/0.99  fof(f40,plain,(
% 2.79/0.99    v1_funct_1(sK3)),
% 2.79/0.99    inference(cnf_transformation,[],[f29])).
% 2.79/0.99  
% 2.79/0.99  fof(f1,axiom,(
% 2.79/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f14,plain,(
% 2.79/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.79/0.99    inference(ennf_transformation,[],[f1])).
% 2.79/0.99  
% 2.79/0.99  fof(f30,plain,(
% 2.79/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.79/0.99    inference(cnf_transformation,[],[f14])).
% 2.79/0.99  
% 2.79/0.99  fof(f2,axiom,(
% 2.79/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f31,plain,(
% 2.79/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.79/0.99    inference(cnf_transformation,[],[f2])).
% 2.79/0.99  
% 2.79/0.99  fof(f4,axiom,(
% 2.79/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 2.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f16,plain,(
% 2.79/0.99    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.79/0.99    inference(ennf_transformation,[],[f4])).
% 2.79/0.99  
% 2.79/0.99  fof(f33,plain,(
% 2.79/0.99    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.79/0.99    inference(cnf_transformation,[],[f16])).
% 2.79/0.99  
% 2.79/0.99  fof(f44,plain,(
% 2.79/0.99    k2_relset_1(sK0,sK1,sK3) = sK1),
% 2.79/0.99    inference(cnf_transformation,[],[f29])).
% 2.79/0.99  
% 2.79/0.99  fof(f6,axiom,(
% 2.79/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f13,plain,(
% 2.79/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.79/0.99    inference(pure_predicate_removal,[],[f6])).
% 2.79/0.99  
% 2.79/0.99  fof(f19,plain,(
% 2.79/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.79/0.99    inference(ennf_transformation,[],[f13])).
% 2.79/0.99  
% 2.79/0.99  fof(f35,plain,(
% 2.79/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.79/0.99    inference(cnf_transformation,[],[f19])).
% 2.79/0.99  
% 2.79/0.99  fof(f5,axiom,(
% 2.79/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f17,plain,(
% 2.79/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.79/0.99    inference(ennf_transformation,[],[f5])).
% 2.79/0.99  
% 2.79/0.99  fof(f18,plain,(
% 2.79/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.79/0.99    inference(flattening,[],[f17])).
% 2.79/0.99  
% 2.79/0.99  fof(f34,plain,(
% 2.79/0.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.79/0.99    inference(cnf_transformation,[],[f18])).
% 2.79/0.99  
% 2.79/0.99  fof(f3,axiom,(
% 2.79/0.99    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f15,plain,(
% 2.79/0.99    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.79/0.99    inference(ennf_transformation,[],[f3])).
% 2.79/0.99  
% 2.79/0.99  fof(f32,plain,(
% 2.79/0.99    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.79/0.99    inference(cnf_transformation,[],[f15])).
% 2.79/0.99  
% 2.79/0.99  fof(f45,plain,(
% 2.79/0.99    k2_relset_1(sK1,sK2,sK4) = sK2),
% 2.79/0.99    inference(cnf_transformation,[],[f29])).
% 2.79/0.99  
% 2.79/0.99  fof(f47,plain,(
% 2.79/0.99    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) != sK2),
% 2.79/0.99    inference(cnf_transformation,[],[f29])).
% 2.79/0.99  
% 2.79/0.99  cnf(c_16,negated_conjecture,
% 2.79/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.79/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_275,negated_conjecture,
% 2.79/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.79/0.99      inference(subtyping,[status(esa)],[c_16]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_567,plain,
% 2.79/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_275]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_14,negated_conjecture,
% 2.79/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.79/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_277,negated_conjecture,
% 2.79/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.79/0.99      inference(subtyping,[status(esa)],[c_14]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_565,plain,
% 2.79/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_277]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_7,plain,
% 2.79/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.79/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.79/0.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 2.79/0.99      | ~ v1_funct_1(X0)
% 2.79/0.99      | ~ v1_funct_1(X3) ),
% 2.79/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_284,plain,
% 2.79/0.99      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
% 2.79/0.99      | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X2_48,X3_48)))
% 2.79/0.99      | m1_subset_1(k1_partfun1(X2_48,X3_48,X0_48,X1_48,X1_46,X0_46),k1_zfmisc_1(k2_zfmisc_1(X2_48,X1_48)))
% 2.79/0.99      | ~ v1_funct_1(X0_46)
% 2.79/0.99      | ~ v1_funct_1(X1_46) ),
% 2.79/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_562,plain,
% 2.79/0.99      ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
% 2.79/0.99      | m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X2_48,X3_48))) != iProver_top
% 2.79/0.99      | m1_subset_1(k1_partfun1(X2_48,X3_48,X0_48,X1_48,X1_46,X0_46),k1_zfmisc_1(k2_zfmisc_1(X2_48,X1_48))) = iProver_top
% 2.79/0.99      | v1_funct_1(X0_46) != iProver_top
% 2.79/0.99      | v1_funct_1(X1_46) != iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_284]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_6,plain,
% 2.79/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.79/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.79/0.99      inference(cnf_transformation,[],[f36]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_285,plain,
% 2.79/0.99      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
% 2.79/0.99      | k2_relset_1(X0_48,X1_48,X0_46) = k2_relat_1(X0_46) ),
% 2.79/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_561,plain,
% 2.79/0.99      ( k2_relset_1(X0_48,X1_48,X0_46) = k2_relat_1(X0_46)
% 2.79/0.99      | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_285]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1545,plain,
% 2.79/0.99      ( k2_relset_1(X0_48,X1_48,k1_partfun1(X0_48,X2_48,X3_48,X1_48,X0_46,X1_46)) = k2_relat_1(k1_partfun1(X0_48,X2_48,X3_48,X1_48,X0_46,X1_46))
% 2.79/0.99      | m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X3_48,X1_48))) != iProver_top
% 2.79/0.99      | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_48,X2_48))) != iProver_top
% 2.79/0.99      | v1_funct_1(X1_46) != iProver_top
% 2.79/0.99      | v1_funct_1(X0_46) != iProver_top ),
% 2.79/0.99      inference(superposition,[status(thm)],[c_562,c_561]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_4151,plain,
% 2.79/0.99      ( k2_relset_1(X0_48,sK2,k1_partfun1(X0_48,X1_48,sK1,sK2,X0_46,sK4)) = k2_relat_1(k1_partfun1(X0_48,X1_48,sK1,sK2,X0_46,sK4))
% 2.79/0.99      | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
% 2.79/0.99      | v1_funct_1(X0_46) != iProver_top
% 2.79/0.99      | v1_funct_1(sK4) != iProver_top ),
% 2.79/0.99      inference(superposition,[status(thm)],[c_565,c_1545]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_15,negated_conjecture,
% 2.79/0.99      ( v1_funct_1(sK4) ),
% 2.79/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_20,plain,
% 2.79/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_4319,plain,
% 2.79/0.99      ( v1_funct_1(X0_46) != iProver_top
% 2.79/0.99      | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
% 2.79/0.99      | k2_relset_1(X0_48,sK2,k1_partfun1(X0_48,X1_48,sK1,sK2,X0_46,sK4)) = k2_relat_1(k1_partfun1(X0_48,X1_48,sK1,sK2,X0_46,sK4)) ),
% 2.79/0.99      inference(global_propositional_subsumption,
% 2.79/0.99                [status(thm)],
% 2.79/0.99                [c_4151,c_20]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_4320,plain,
% 2.79/0.99      ( k2_relset_1(X0_48,sK2,k1_partfun1(X0_48,X1_48,sK1,sK2,X0_46,sK4)) = k2_relat_1(k1_partfun1(X0_48,X1_48,sK1,sK2,X0_46,sK4))
% 2.79/0.99      | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
% 2.79/0.99      | v1_funct_1(X0_46) != iProver_top ),
% 2.79/0.99      inference(renaming,[status(thm)],[c_4319]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_4329,plain,
% 2.79/0.99      ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = k2_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
% 2.79/0.99      | v1_funct_1(sK3) != iProver_top ),
% 2.79/0.99      inference(superposition,[status(thm)],[c_567,c_4320]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_9,plain,
% 2.79/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.79/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.79/0.99      | ~ v1_funct_1(X0)
% 2.79/0.99      | ~ v1_funct_1(X3)
% 2.79/0.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 2.79/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_282,plain,
% 2.79/0.99      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
% 2.79/0.99      | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X2_48,X3_48)))
% 2.79/0.99      | ~ v1_funct_1(X0_46)
% 2.79/0.99      | ~ v1_funct_1(X1_46)
% 2.79/0.99      | k1_partfun1(X2_48,X3_48,X0_48,X1_48,X1_46,X0_46) = k5_relat_1(X1_46,X0_46) ),
% 2.79/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_564,plain,
% 2.79/0.99      ( k1_partfun1(X0_48,X1_48,X2_48,X3_48,X0_46,X1_46) = k5_relat_1(X0_46,X1_46)
% 2.79/0.99      | m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X2_48,X3_48))) != iProver_top
% 2.79/0.99      | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
% 2.79/0.99      | v1_funct_1(X1_46) != iProver_top
% 2.79/0.99      | v1_funct_1(X0_46) != iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_282]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1904,plain,
% 2.79/0.99      ( k1_partfun1(sK0,sK1,X0_48,X1_48,sK3,X0_46) = k5_relat_1(sK3,X0_46)
% 2.79/0.99      | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
% 2.79/0.99      | v1_funct_1(X0_46) != iProver_top
% 2.79/0.99      | v1_funct_1(sK3) != iProver_top ),
% 2.79/0.99      inference(superposition,[status(thm)],[c_567,c_564]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_17,negated_conjecture,
% 2.79/0.99      ( v1_funct_1(sK3) ),
% 2.79/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_18,plain,
% 2.79/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2444,plain,
% 2.79/0.99      ( v1_funct_1(X0_46) != iProver_top
% 2.79/0.99      | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
% 2.79/0.99      | k1_partfun1(sK0,sK1,X0_48,X1_48,sK3,X0_46) = k5_relat_1(sK3,X0_46) ),
% 2.79/0.99      inference(global_propositional_subsumption,
% 2.79/0.99                [status(thm)],
% 2.79/0.99                [c_1904,c_18]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2445,plain,
% 2.79/0.99      ( k1_partfun1(sK0,sK1,X0_48,X1_48,sK3,X0_46) = k5_relat_1(sK3,X0_46)
% 2.79/0.99      | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
% 2.79/0.99      | v1_funct_1(X0_46) != iProver_top ),
% 2.79/0.99      inference(renaming,[status(thm)],[c_2444]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2451,plain,
% 2.79/0.99      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
% 2.79/0.99      | v1_funct_1(sK4) != iProver_top ),
% 2.79/0.99      inference(superposition,[status(thm)],[c_565,c_2445]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_732,plain,
% 2.79/0.99      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
% 2.79/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.79/0.99      | ~ v1_funct_1(X0_46)
% 2.79/0.99      | ~ v1_funct_1(sK4)
% 2.79/0.99      | k1_partfun1(X0_48,X1_48,sK1,sK2,X0_46,sK4) = k5_relat_1(X0_46,sK4) ),
% 2.79/0.99      inference(instantiation,[status(thm)],[c_282]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_799,plain,
% 2.79/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.79/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.79/0.99      | ~ v1_funct_1(sK4)
% 2.79/0.99      | ~ v1_funct_1(sK3)
% 2.79/0.99      | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 2.79/0.99      inference(instantiation,[status(thm)],[c_732]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2704,plain,
% 2.79/0.99      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 2.79/0.99      inference(global_propositional_subsumption,
% 2.79/0.99                [status(thm)],
% 2.79/0.99                [c_2451,c_17,c_16,c_15,c_14,c_799]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_0,plain,
% 2.79/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.79/0.99      | ~ v1_relat_1(X1)
% 2.79/0.99      | v1_relat_1(X0) ),
% 2.79/0.99      inference(cnf_transformation,[],[f30]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_289,plain,
% 2.79/0.99      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
% 2.79/0.99      | ~ v1_relat_1(X1_46)
% 2.79/0.99      | v1_relat_1(X0_46) ),
% 2.79/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_557,plain,
% 2.79/0.99      ( m1_subset_1(X0_46,k1_zfmisc_1(X1_46)) != iProver_top
% 2.79/0.99      | v1_relat_1(X1_46) != iProver_top
% 2.79/0.99      | v1_relat_1(X0_46) = iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_289]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_834,plain,
% 2.79/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 2.79/0.99      | v1_relat_1(sK3) = iProver_top ),
% 2.79/0.99      inference(superposition,[status(thm)],[c_567,c_557]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1,plain,
% 2.79/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.79/0.99      inference(cnf_transformation,[],[f31]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_288,plain,
% 2.79/0.99      ( v1_relat_1(k2_zfmisc_1(X0_48,X1_48)) ),
% 2.79/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1144,plain,
% 2.79/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 2.79/0.99      inference(instantiation,[status(thm)],[c_288]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1145,plain,
% 2.79/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_1144]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1245,plain,
% 2.79/0.99      ( v1_relat_1(sK3) = iProver_top ),
% 2.79/0.99      inference(global_propositional_subsumption,
% 2.79/0.99                [status(thm)],
% 2.79/0.99                [c_834,c_1145]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_833,plain,
% 2.79/0.99      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 2.79/0.99      | v1_relat_1(sK4) = iProver_top ),
% 2.79/0.99      inference(superposition,[status(thm)],[c_565,c_557]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1141,plain,
% 2.79/0.99      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.79/0.99      inference(instantiation,[status(thm)],[c_288]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1142,plain,
% 2.79/0.99      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_1141]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1237,plain,
% 2.79/0.99      ( v1_relat_1(sK4) = iProver_top ),
% 2.79/0.99      inference(global_propositional_subsumption,
% 2.79/0.99                [status(thm)],
% 2.79/0.99                [c_833,c_1142]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_3,plain,
% 2.79/0.99      ( ~ v1_relat_1(X0)
% 2.79/0.99      | ~ v1_relat_1(X1)
% 2.79/0.99      | k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1)) ),
% 2.79/0.99      inference(cnf_transformation,[],[f33]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_286,plain,
% 2.79/0.99      ( ~ v1_relat_1(X0_46)
% 2.79/0.99      | ~ v1_relat_1(X1_46)
% 2.79/0.99      | k9_relat_1(X1_46,k2_relat_1(X0_46)) = k2_relat_1(k5_relat_1(X0_46,X1_46)) ),
% 2.79/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_560,plain,
% 2.79/0.99      ( k9_relat_1(X0_46,k2_relat_1(X1_46)) = k2_relat_1(k5_relat_1(X1_46,X0_46))
% 2.79/0.99      | v1_relat_1(X1_46) != iProver_top
% 2.79/0.99      | v1_relat_1(X0_46) != iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_286]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1446,plain,
% 2.79/0.99      ( k9_relat_1(sK4,k2_relat_1(X0_46)) = k2_relat_1(k5_relat_1(X0_46,sK4))
% 2.79/0.99      | v1_relat_1(X0_46) != iProver_top ),
% 2.79/0.99      inference(superposition,[status(thm)],[c_1237,c_560]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2757,plain,
% 2.79/0.99      ( k9_relat_1(sK4,k2_relat_1(sK3)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
% 2.79/0.99      inference(superposition,[status(thm)],[c_1245,c_1446]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_927,plain,
% 2.79/0.99      ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
% 2.79/0.99      inference(superposition,[status(thm)],[c_567,c_561]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_13,negated_conjecture,
% 2.79/0.99      ( k2_relset_1(sK0,sK1,sK3) = sK1 ),
% 2.79/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_278,negated_conjecture,
% 2.79/0.99      ( k2_relset_1(sK0,sK1,sK3) = sK1 ),
% 2.79/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_929,plain,
% 2.79/0.99      ( k2_relat_1(sK3) = sK1 ),
% 2.79/0.99      inference(light_normalisation,[status(thm)],[c_927,c_278]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2763,plain,
% 2.79/0.99      ( k2_relat_1(k5_relat_1(sK3,sK4)) = k9_relat_1(sK4,sK1) ),
% 2.79/0.99      inference(light_normalisation,[status(thm)],[c_2757,c_929]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_5,plain,
% 2.79/0.99      ( v4_relat_1(X0,X1)
% 2.79/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.79/0.99      inference(cnf_transformation,[],[f35]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_4,plain,
% 2.79/0.99      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.79/0.99      inference(cnf_transformation,[],[f34]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_163,plain,
% 2.79/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.79/0.99      | ~ v1_relat_1(X0)
% 2.79/0.99      | k7_relat_1(X0,X1) = X0 ),
% 2.79/0.99      inference(resolution,[status(thm)],[c_5,c_4]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_273,plain,
% 2.79/0.99      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
% 2.79/0.99      | ~ v1_relat_1(X0_46)
% 2.79/0.99      | k7_relat_1(X0_46,X0_48) = X0_46 ),
% 2.79/0.99      inference(subtyping,[status(esa)],[c_163]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_569,plain,
% 2.79/0.99      ( k7_relat_1(X0_46,X0_48) = X0_46
% 2.79/0.99      | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
% 2.79/0.99      | v1_relat_1(X0_46) != iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_273]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_319,plain,
% 2.79/0.99      ( v1_relat_1(k2_zfmisc_1(X0_48,X1_48)) = iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_288]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_342,plain,
% 2.79/0.99      ( k7_relat_1(X0_46,X0_48) = X0_46
% 2.79/0.99      | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
% 2.79/0.99      | v1_relat_1(X0_46) != iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_273]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_675,plain,
% 2.79/0.99      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
% 2.79/0.99      | v1_relat_1(X0_46)
% 2.79/0.99      | ~ v1_relat_1(k2_zfmisc_1(X0_48,X1_48)) ),
% 2.79/0.99      inference(instantiation,[status(thm)],[c_289]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_676,plain,
% 2.79/0.99      ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
% 2.79/0.99      | v1_relat_1(X0_46) = iProver_top
% 2.79/0.99      | v1_relat_1(k2_zfmisc_1(X0_48,X1_48)) != iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_675]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_3001,plain,
% 2.79/0.99      ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
% 2.79/0.99      | k7_relat_1(X0_46,X0_48) = X0_46 ),
% 2.79/0.99      inference(global_propositional_subsumption,
% 2.79/0.99                [status(thm)],
% 2.79/0.99                [c_569,c_319,c_342,c_676]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_3002,plain,
% 2.79/0.99      ( k7_relat_1(X0_46,X0_48) = X0_46
% 2.79/0.99      | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
% 2.79/0.99      inference(renaming,[status(thm)],[c_3001]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_3009,plain,
% 2.79/0.99      ( k7_relat_1(sK4,sK1) = sK4 ),
% 2.79/0.99      inference(superposition,[status(thm)],[c_565,c_3002]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2,plain,
% 2.79/0.99      ( ~ v1_relat_1(X0)
% 2.79/0.99      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.79/0.99      inference(cnf_transformation,[],[f32]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_287,plain,
% 2.79/0.99      ( ~ v1_relat_1(X0_46)
% 2.79/0.99      | k2_relat_1(k7_relat_1(X0_46,X0_48)) = k9_relat_1(X0_46,X0_48) ),
% 2.79/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_559,plain,
% 2.79/0.99      ( k2_relat_1(k7_relat_1(X0_46,X0_48)) = k9_relat_1(X0_46,X0_48)
% 2.79/0.99      | v1_relat_1(X0_46) != iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_287]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1242,plain,
% 2.79/0.99      ( k2_relat_1(k7_relat_1(sK4,X0_48)) = k9_relat_1(sK4,X0_48) ),
% 2.79/0.99      inference(superposition,[status(thm)],[c_1237,c_559]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_3030,plain,
% 2.79/0.99      ( k9_relat_1(sK4,sK1) = k2_relat_1(sK4) ),
% 2.79/0.99      inference(superposition,[status(thm)],[c_3009,c_1242]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_926,plain,
% 2.79/0.99      ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
% 2.79/0.99      inference(superposition,[status(thm)],[c_565,c_561]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_12,negated_conjecture,
% 2.79/0.99      ( k2_relset_1(sK1,sK2,sK4) = sK2 ),
% 2.79/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_279,negated_conjecture,
% 2.79/0.99      ( k2_relset_1(sK1,sK2,sK4) = sK2 ),
% 2.79/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_932,plain,
% 2.79/0.99      ( k2_relat_1(sK4) = sK2 ),
% 2.79/0.99      inference(light_normalisation,[status(thm)],[c_926,c_279]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_3031,plain,
% 2.79/0.99      ( k9_relat_1(sK4,sK1) = sK2 ),
% 2.79/0.99      inference(light_normalisation,[status(thm)],[c_3030,c_932]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_3804,plain,
% 2.79/0.99      ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
% 2.79/0.99      inference(light_normalisation,[status(thm)],[c_2763,c_3031]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_4360,plain,
% 2.79/0.99      ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2
% 2.79/0.99      | v1_funct_1(sK3) != iProver_top ),
% 2.79/0.99      inference(light_normalisation,[status(thm)],[c_4329,c_2704,c_3804]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_10,negated_conjecture,
% 2.79/0.99      ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) != sK2 ),
% 2.79/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_281,negated_conjecture,
% 2.79/0.99      ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) != sK2 ),
% 2.79/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2707,plain,
% 2.79/0.99      ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) != sK2 ),
% 2.79/0.99      inference(demodulation,[status(thm)],[c_2704,c_281]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(contradiction,plain,
% 2.79/0.99      ( $false ),
% 2.79/0.99      inference(minisat,[status(thm)],[c_4360,c_2707,c_18]) ).
% 2.79/0.99  
% 2.79/0.99  
% 2.79/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.79/0.99  
% 2.79/0.99  ------                               Statistics
% 2.79/0.99  
% 2.79/0.99  ------ General
% 2.79/0.99  
% 2.79/0.99  abstr_ref_over_cycles:                  0
% 2.79/0.99  abstr_ref_under_cycles:                 0
% 2.79/0.99  gc_basic_clause_elim:                   0
% 2.79/0.99  forced_gc_time:                         0
% 2.79/0.99  parsing_time:                           0.009
% 2.79/0.99  unif_index_cands_time:                  0.
% 2.79/0.99  unif_index_add_time:                    0.
% 2.79/0.99  orderings_time:                         0.
% 2.79/0.99  out_proof_time:                         0.016
% 2.79/0.99  total_time:                             0.249
% 2.79/0.99  num_of_symbols:                         52
% 2.79/0.99  num_of_terms:                           4576
% 2.79/0.99  
% 2.79/0.99  ------ Preprocessing
% 2.79/0.99  
% 2.79/0.99  num_of_splits:                          0
% 2.79/0.99  num_of_split_atoms:                     0
% 2.79/0.99  num_of_reused_defs:                     0
% 2.79/0.99  num_eq_ax_congr_red:                    17
% 2.79/0.99  num_of_sem_filtered_clauses:            1
% 2.79/0.99  num_of_subtypes:                        3
% 2.79/0.99  monotx_restored_types:                  0
% 2.79/0.99  sat_num_of_epr_types:                   0
% 2.79/0.99  sat_num_of_non_cyclic_types:            0
% 2.79/0.99  sat_guarded_non_collapsed_types:        1
% 2.79/0.99  num_pure_diseq_elim:                    0
% 2.79/0.99  simp_replaced_by:                       0
% 2.79/0.99  res_preprocessed:                       98
% 2.79/0.99  prep_upred:                             0
% 2.79/0.99  prep_unflattend:                        0
% 2.79/0.99  smt_new_axioms:                         0
% 2.79/0.99  pred_elim_cands:                        3
% 2.79/0.99  pred_elim:                              1
% 2.79/0.99  pred_elim_cl:                           1
% 2.79/0.99  pred_elim_cycles:                       3
% 2.79/0.99  merged_defs:                            0
% 2.79/0.99  merged_defs_ncl:                        0
% 2.79/0.99  bin_hyper_res:                          0
% 2.79/0.99  prep_cycles:                            4
% 2.79/0.99  pred_elim_time:                         0.
% 2.79/0.99  splitting_time:                         0.
% 2.79/0.99  sem_filter_time:                        0.
% 2.79/0.99  monotx_time:                            0.
% 2.79/0.99  subtype_inf_time:                       0.
% 2.79/0.99  
% 2.79/0.99  ------ Problem properties
% 2.79/0.99  
% 2.79/0.99  clauses:                                17
% 2.79/0.99  conjectures:                            8
% 2.79/0.99  epr:                                    3
% 2.79/0.99  horn:                                   17
% 2.79/0.99  ground:                                 8
% 2.79/0.99  unary:                                  9
% 2.79/0.99  binary:                                 2
% 2.79/0.99  lits:                                   37
% 2.79/0.99  lits_eq:                                9
% 2.79/0.99  fd_pure:                                0
% 2.79/0.99  fd_pseudo:                              0
% 2.79/0.99  fd_cond:                                0
% 2.79/0.99  fd_pseudo_cond:                         0
% 2.79/0.99  ac_symbols:                             0
% 2.79/0.99  
% 2.79/0.99  ------ Propositional Solver
% 2.79/0.99  
% 2.79/0.99  prop_solver_calls:                      28
% 2.79/0.99  prop_fast_solver_calls:                 626
% 2.79/0.99  smt_solver_calls:                       0
% 2.79/0.99  smt_fast_solver_calls:                  0
% 2.79/0.99  prop_num_of_clauses:                    1877
% 2.79/0.99  prop_preprocess_simplified:             5172
% 2.79/0.99  prop_fo_subsumed:                       36
% 2.79/0.99  prop_solver_time:                       0.
% 2.79/0.99  smt_solver_time:                        0.
% 2.79/0.99  smt_fast_solver_time:                   0.
% 2.79/0.99  prop_fast_solver_time:                  0.
% 2.79/0.99  prop_unsat_core_time:                   0.
% 2.79/0.99  
% 2.79/0.99  ------ QBF
% 2.79/0.99  
% 2.79/0.99  qbf_q_res:                              0
% 2.79/0.99  qbf_num_tautologies:                    0
% 2.79/0.99  qbf_prep_cycles:                        0
% 2.79/0.99  
% 2.79/0.99  ------ BMC1
% 2.79/0.99  
% 2.79/0.99  bmc1_current_bound:                     -1
% 2.79/0.99  bmc1_last_solved_bound:                 -1
% 2.79/0.99  bmc1_unsat_core_size:                   -1
% 2.79/0.99  bmc1_unsat_core_parents_size:           -1
% 2.79/0.99  bmc1_merge_next_fun:                    0
% 2.79/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.79/0.99  
% 2.79/0.99  ------ Instantiation
% 2.79/0.99  
% 2.79/0.99  inst_num_of_clauses:                    663
% 2.79/0.99  inst_num_in_passive:                    269
% 2.79/0.99  inst_num_in_active:                     300
% 2.79/0.99  inst_num_in_unprocessed:                94
% 2.79/0.99  inst_num_of_loops:                      330
% 2.79/0.99  inst_num_of_learning_restarts:          0
% 2.79/0.99  inst_num_moves_active_passive:          28
% 2.79/0.99  inst_lit_activity:                      0
% 2.79/0.99  inst_lit_activity_moves:                1
% 2.79/0.99  inst_num_tautologies:                   0
% 2.79/0.99  inst_num_prop_implied:                  0
% 2.79/0.99  inst_num_existing_simplified:           0
% 2.79/0.99  inst_num_eq_res_simplified:             0
% 2.79/0.99  inst_num_child_elim:                    0
% 2.79/0.99  inst_num_of_dismatching_blockings:      136
% 2.79/0.99  inst_num_of_non_proper_insts:           304
% 2.79/0.99  inst_num_of_duplicates:                 0
% 2.79/0.99  inst_inst_num_from_inst_to_res:         0
% 2.79/0.99  inst_dismatching_checking_time:         0.
% 2.79/0.99  
% 2.79/0.99  ------ Resolution
% 2.79/0.99  
% 2.79/0.99  res_num_of_clauses:                     0
% 2.79/0.99  res_num_in_passive:                     0
% 2.79/0.99  res_num_in_active:                      0
% 2.79/0.99  res_num_of_loops:                       102
% 2.79/0.99  res_forward_subset_subsumed:            12
% 2.79/0.99  res_backward_subset_subsumed:           0
% 2.79/0.99  res_forward_subsumed:                   0
% 2.79/0.99  res_backward_subsumed:                  0
% 2.79/0.99  res_forward_subsumption_resolution:     0
% 2.79/0.99  res_backward_subsumption_resolution:    0
% 2.79/0.99  res_clause_to_clause_subsumption:       176
% 2.79/0.99  res_orphan_elimination:                 0
% 2.79/0.99  res_tautology_del:                      3
% 2.79/0.99  res_num_eq_res_simplified:              0
% 2.79/0.99  res_num_sel_changes:                    0
% 2.79/0.99  res_moves_from_active_to_pass:          0
% 2.79/0.99  
% 2.79/0.99  ------ Superposition
% 2.79/0.99  
% 2.79/0.99  sup_time_total:                         0.
% 2.79/0.99  sup_time_generating:                    0.
% 2.79/0.99  sup_time_sim_full:                      0.
% 2.79/0.99  sup_time_sim_immed:                     0.
% 2.79/0.99  
% 2.79/0.99  sup_num_of_clauses:                     107
% 2.79/0.99  sup_num_in_active:                      65
% 2.79/0.99  sup_num_in_passive:                     42
% 2.79/0.99  sup_num_of_loops:                       65
% 2.79/0.99  sup_fw_superposition:                   41
% 2.79/0.99  sup_bw_superposition:                   50
% 2.79/0.99  sup_immediate_simplified:               21
% 2.79/0.99  sup_given_eliminated:                   0
% 2.79/0.99  comparisons_done:                       0
% 2.79/0.99  comparisons_avoided:                    0
% 2.79/0.99  
% 2.79/0.99  ------ Simplifications
% 2.79/0.99  
% 2.79/0.99  
% 2.79/0.99  sim_fw_subset_subsumed:                 0
% 2.79/0.99  sim_bw_subset_subsumed:                 0
% 2.79/0.99  sim_fw_subsumed:                        0
% 2.79/0.99  sim_bw_subsumed:                        0
% 2.79/0.99  sim_fw_subsumption_res:                 0
% 2.79/0.99  sim_bw_subsumption_res:                 0
% 2.79/0.99  sim_tautology_del:                      0
% 2.79/0.99  sim_eq_tautology_del:                   1
% 2.79/0.99  sim_eq_res_simp:                        0
% 2.79/0.99  sim_fw_demodulated:                     0
% 2.79/0.99  sim_bw_demodulated:                     1
% 2.79/0.99  sim_light_normalised:                   22
% 2.79/0.99  sim_joinable_taut:                      0
% 2.79/0.99  sim_joinable_simp:                      0
% 2.79/0.99  sim_ac_normalised:                      0
% 2.79/0.99  sim_smt_subsumption:                    0
% 2.79/0.99  
%------------------------------------------------------------------------------
