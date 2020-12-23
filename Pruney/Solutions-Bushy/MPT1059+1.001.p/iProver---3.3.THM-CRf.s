%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1059+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:48 EST 2020

% Result     : Theorem 1.46s
% Output     : CNFRefutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 357 expanded)
%              Number of clauses        :   56 ( 103 expanded)
%              Number of leaves         :   15 ( 118 expanded)
%              Depth                    :   19
%              Number of atoms          :  372 (1958 expanded)
%              Number of equality atoms :  135 ( 451 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => k7_partfun1(X1,X2,X3) = k3_funct_2(X0,X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X2,X0,X1)
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,X0)
                   => k7_partfun1(X1,X2,X3) = k3_funct_2(X0,X1,X2,X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k7_partfun1(X1,X2,X3) != k3_funct_2(X0,X1,X2,X3)
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k7_partfun1(X1,X2,X3) != k3_funct_2(X0,X1,X2,X3)
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k7_partfun1(X1,X2,X3) != k3_funct_2(X0,X1,X2,X3)
          & m1_subset_1(X3,X0) )
     => ( k7_partfun1(X1,X2,sK3) != k3_funct_2(X0,X1,X2,sK3)
        & m1_subset_1(sK3,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k7_partfun1(X1,X2,X3) != k3_funct_2(X0,X1,X2,X3)
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( k7_partfun1(X1,sK2,X3) != k3_funct_2(X0,X1,sK2,X3)
            & m1_subset_1(X3,X0) )
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK2,X0,X1)
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k7_partfun1(X1,X2,X3) != k3_funct_2(X0,X1,X2,X3)
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( k7_partfun1(sK1,X2,X3) != k3_funct_2(X0,sK1,X2,X3)
                & m1_subset_1(X3,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
            & v1_funct_2(X2,X0,sK1)
            & v1_funct_1(X2) )
        & ~ v1_xboole_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( k7_partfun1(X1,X2,X3) != k3_funct_2(X0,X1,X2,X3)
                    & m1_subset_1(X3,X0) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k7_partfun1(X1,X2,X3) != k3_funct_2(sK0,X1,X2,X3)
                  & m1_subset_1(X3,sK0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
              & v1_funct_2(X2,sK0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( k7_partfun1(sK1,sK2,sK3) != k3_funct_2(sK0,sK1,sK2,sK3)
    & m1_subset_1(sK3,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f31,f30,f29,f28])).

fof(f52,plain,(
    m1_subset_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f51,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f49,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f48,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f46,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f47,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
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

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f53,plain,(
    k7_partfun1(sK1,sK2,sK3) != k3_funct_2(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1451,plain,
    ( m1_subset_1(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1450,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v5_relat_1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k7_partfun1(X2,X1,X0) = k1_funct_1(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_250,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | X1 != X2
    | X5 != X4
    | k7_partfun1(X5,X1,X0) = k1_funct_1(X1,X0) ),
    inference(resolution_lifted,[status(thm)],[c_1,c_8])).

cnf(c_251,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k7_partfun1(X3,X1,X0) = k1_funct_1(X1,X0) ),
    inference(unflattening,[status(thm)],[c_250])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_265,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1)
    | k7_partfun1(X3,X1,X0) = k1_funct_1(X1,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_251,c_0])).

cnf(c_12,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_278,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X2)
    | X0 != X5
    | k7_partfun1(X4,X2,X5) = k1_funct_1(X2,X5)
    | k1_relat_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_265,c_12])).

cnf(c_279,plain,
    ( ~ m1_subset_1(X0,k1_relat_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | v1_xboole_0(k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | k7_partfun1(X3,X1,X0) = k1_funct_1(X1,X0) ),
    inference(unflattening,[status(thm)],[c_278])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_305,plain,
    ( ~ m1_subset_1(X0,k1_relat_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | v1_xboole_0(k1_relat_1(X1))
    | k7_partfun1(X3,X1,X0) = k1_funct_1(X1,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_279,c_18])).

cnf(c_306,plain,
    ( ~ m1_subset_1(X0,k1_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(k1_relat_1(sK2))
    | k7_partfun1(X2,sK2,X0) = k1_funct_1(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_305])).

cnf(c_1447,plain,
    ( k7_partfun1(X0,sK2,X1) = k1_funct_1(sK2,X1)
    | m1_subset_1(X1,k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_306])).

cnf(c_19,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_9,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_13,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_375,plain,
    ( o_0_0_xboole_0 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_13])).

cnf(c_376,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(unflattening,[status(thm)],[c_375])).

cnf(c_20,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_459,plain,
    ( ~ m1_subset_1(X0,k1_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_partfun1(X2,sK2,X0) = k1_funct_1(sK2,X0)
    | k1_relat_1(sK2) != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_306])).

cnf(c_460,plain,
    ( k7_partfun1(X0,sK2,X1) = k1_funct_1(sK2,X1)
    | k1_relat_1(sK2) != sK0
    | m1_subset_1(X1,k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_459])).

cnf(c_1200,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1575,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | X0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1200])).

cnf(c_1577,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1575])).

cnf(c_1782,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_1200])).

cnf(c_1784,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1782])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_17,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_599,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X1
    | sK2 != X0
    | sK1 != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_17])).

cnf(c_600,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_599])).

cnf(c_602,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_600,c_16])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1453,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1882,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1450,c_1453])).

cnf(c_1884,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_602,c_1882])).

cnf(c_2057,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | m1_subset_1(X1,k1_relat_1(sK2)) != iProver_top
    | k7_partfun1(X0,sK2,X1) = k1_funct_1(sK2,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1447,c_19,c_9,c_376,c_460,c_1577,c_1784,c_1884])).

cnf(c_2058,plain,
    ( k7_partfun1(X0,sK2,X1) = k1_funct_1(sK2,X1)
    | m1_subset_1(X1,k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2057])).

cnf(c_1963,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1884,c_19,c_9,c_376,c_1577,c_1784])).

cnf(c_2063,plain,
    ( k7_partfun1(X0,sK2,X1) = k1_funct_1(sK2,X1)
    | m1_subset_1(X1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2058,c_1963])).

cnf(c_2070,plain,
    ( k7_partfun1(sK1,sK2,X0) = k1_funct_1(sK2,X0)
    | m1_subset_1(X0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1450,c_2063])).

cnf(c_2196,plain,
    ( k7_partfun1(sK1,sK2,sK3) = k1_funct_1(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_1451,c_2070])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_323,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_18])).

cnf(c_324,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(X2,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X0)
    | k3_funct_2(X0,X1,sK2,X2) = k1_funct_1(sK2,X2) ),
    inference(unflattening,[status(thm)],[c_323])).

cnf(c_633,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,sK2,X0) = k1_funct_1(sK2,X0)
    | sK0 != X1
    | sK2 != sK2
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_324])).

cnf(c_634,plain,
    ( ~ m1_subset_1(X0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_xboole_0(sK0)
    | k3_funct_2(sK0,sK1,sK2,X0) = k1_funct_1(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_633])).

cnf(c_638,plain,
    ( ~ m1_subset_1(X0,sK0)
    | k3_funct_2(sK0,sK1,sK2,X0) = k1_funct_1(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_634,c_20,c_16])).

cnf(c_1441,plain,
    ( k3_funct_2(sK0,sK1,sK2,X0) = k1_funct_1(sK2,X0)
    | m1_subset_1(X0,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_638])).

cnf(c_1682,plain,
    ( k3_funct_2(sK0,sK1,sK2,sK3) = k1_funct_1(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_1451,c_1441])).

cnf(c_14,negated_conjecture,
    ( k7_partfun1(sK1,sK2,sK3) != k3_funct_2(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1684,plain,
    ( k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_1682,c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2196,c_1684])).


%------------------------------------------------------------------------------
