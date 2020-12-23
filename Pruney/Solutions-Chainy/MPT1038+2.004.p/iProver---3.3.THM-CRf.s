%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:43 EST 2020

% Result     : Theorem 0.89s
% Output     : CNFRefutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 279 expanded)
%              Number of clauses        :   68 (  91 expanded)
%              Number of leaves         :   11 (  86 expanded)
%              Depth                    :   20
%              Number of atoms          :  497 (2421 expanded)
%              Number of equality atoms :   86 ( 115 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_1(X4) )
             => ( ( v1_partfun1(X4,X0)
                  & r1_partfun1(X3,X4)
                  & r1_partfun1(X2,X4) )
               => r1_partfun1(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( r1_partfun1(X2,X3)
              | ~ v1_partfun1(X4,X0)
              | ~ r1_partfun1(X3,X4)
              | ~ r1_partfun1(X2,X4)
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( r1_partfun1(X2,X3)
              | ~ v1_partfun1(X4,X0)
              | ~ r1_partfun1(X3,X4)
              | ~ r1_partfun1(X2,X4)
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f17,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | ~ v1_partfun1(X4,X0)
      | ~ r1_partfun1(X3,X4)
      | ~ r1_partfun1(X2,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f5])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X2,X1] :
      ( v1_partfun1(X2,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f16])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_1(X2) )
         => ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
                & v1_funct_2(X3,X0,X0)
                & v1_funct_1(X3) )
             => ( ( r1_partfun1(X2,X3)
                  & r1_partfun1(X1,X3) )
               => r1_partfun1(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_1(X2) )
           => ! [X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
                  & v1_funct_2(X3,X0,X0)
                  & v1_funct_1(X3) )
               => ( ( r1_partfun1(X2,X3)
                    & r1_partfun1(X1,X3) )
                 => r1_partfun1(X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_partfun1(X1,X2)
              & r1_partfun1(X2,X3)
              & r1_partfun1(X1,X3)
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X3,X0,X0)
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_partfun1(X1,X2)
              & r1_partfun1(X2,X3)
              & r1_partfun1(X1,X3)
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X3,X0,X0)
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_partfun1(X1,X2)
          & r1_partfun1(X2,X3)
          & r1_partfun1(X1,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X3,X0,X0)
          & v1_funct_1(X3) )
     => ( ~ r1_partfun1(X1,X2)
        & r1_partfun1(X2,sK3)
        & r1_partfun1(X1,sK3)
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(sK3,X0,X0)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_partfun1(X1,X2)
              & r1_partfun1(X2,X3)
              & r1_partfun1(X1,X3)
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X3,X0,X0)
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( ~ r1_partfun1(X1,sK2)
            & r1_partfun1(sK2,X3)
            & r1_partfun1(X1,X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X3,X0,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_partfun1(X1,X2)
                & r1_partfun1(X2,X3)
                & r1_partfun1(X1,X3)
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
                & v1_funct_2(X3,X0,X0)
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_partfun1(sK1,X2)
              & r1_partfun1(X2,X3)
              & r1_partfun1(sK1,X3)
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
              & v1_funct_2(X3,sK0,sK0)
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ~ r1_partfun1(sK1,sK2)
    & r1_partfun1(sK2,sK3)
    & r1_partfun1(sK1,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK3,sK0,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f13,f12,f11])).

fof(f23,plain,(
    v1_funct_2(sK3,sK0,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f22,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f24,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f27,plain,(
    ~ r1_partfun1(sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f26,plain,(
    r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f25,plain,(
    r1_partfun1(sK1,sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f21,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f20,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f19,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f18,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_365,plain,
    ( ~ m1_subset_1(X0_40,X0_41)
    | m1_subset_1(X0_40,X1_41)
    | X1_41 != X0_41 ),
    theory(equality)).

cnf(c_671,plain,
    ( m1_subset_1(sK1,X0_41)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | X0_41 != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_365])).

cnf(c_705,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(X0_42))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_zfmisc_1(X0_42) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_671])).

cnf(c_755,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_43,X1_43)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_zfmisc_1(k2_zfmisc_1(X0_43,X1_43)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_705])).

cnf(c_902,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_43)))
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_43)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_755])).

cnf(c_904,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_902])).

cnf(c_666,plain,
    ( m1_subset_1(sK2,X0_41)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | X0_41 != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_365])).

cnf(c_706,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(X0_42))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_zfmisc_1(X0_42) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_666])).

cnf(c_754,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_43,X1_43)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_zfmisc_1(k2_zfmisc_1(X0_43,X1_43)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_706])).

cnf(c_893,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_43)))
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_43)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_754])).

cnf(c_895,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_893])).

cnf(c_2,plain,
    ( ~ r1_partfun1(X0,X1)
    | ~ r1_partfun1(X2,X1)
    | r1_partfun1(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_partfun1(X1,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_0,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | v1_partfun1(X0,k1_xboole_0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_7,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_131,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | v1_partfun1(X0,k1_xboole_0)
    | ~ v1_funct_1(X0)
    | sK0 != X1
    | sK0 != k1_xboole_0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_7])).

cnf(c_132,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | v1_partfun1(sK3,k1_xboole_0)
    | ~ v1_funct_1(sK3)
    | sK0 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_131])).

cnf(c_8,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_134,plain,
    ( v1_partfun1(sK3,k1_xboole_0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | sK0 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_132,c_8])).

cnf(c_135,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | v1_partfun1(sK3,k1_xboole_0)
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_134])).

cnf(c_169,plain,
    ( ~ r1_partfun1(X0,X1)
    | ~ r1_partfun1(X2,X1)
    | r1_partfun1(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | sK0 != k1_xboole_0
    | sK3 != X1
    | k1_xboole_0 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_135])).

cnf(c_170,plain,
    ( r1_partfun1(X0,X1)
    | ~ r1_partfun1(X0,sK3)
    | ~ r1_partfun1(X1,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | sK0 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_169])).

cnf(c_174,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
    | ~ r1_partfun1(X1,sK3)
    | ~ r1_partfun1(X0,sK3)
    | r1_partfun1(X0,X1)
    | sK0 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_170,c_8])).

cnf(c_175,plain,
    ( r1_partfun1(X0,X1)
    | ~ r1_partfun1(X0,sK3)
    | ~ r1_partfun1(X1,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_174])).

cnf(c_346,plain,
    ( r1_partfun1(X0_40,X1_40)
    | ~ r1_partfun1(X0_40,sK3)
    | ~ r1_partfun1(X1_40,sK3)
    | ~ m1_subset_1(X1_40,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_43)))
    | ~ m1_subset_1(X0_40,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_43)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_43)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_1(X0_40)
    | ~ v1_funct_1(X1_40)
    | sK0 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_175])).

cnf(c_356,plain,
    ( r1_partfun1(X0_40,X1_40)
    | ~ r1_partfun1(X0_40,sK3)
    | ~ r1_partfun1(X1_40,sK3)
    | ~ m1_subset_1(X1_40,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_43)))
    | ~ m1_subset_1(X0_40,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_43)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_43)))
    | ~ v1_funct_1(X0_40)
    | ~ v1_funct_1(X1_40)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_346])).

cnf(c_851,plain,
    ( ~ r1_partfun1(X0_40,sK3)
    | r1_partfun1(sK1,X0_40)
    | ~ r1_partfun1(sK1,sK3)
    | ~ m1_subset_1(X0_40,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_43)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_43)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_43)))
    | ~ v1_funct_1(X0_40)
    | ~ v1_funct_1(sK1)
    | ~ sP0_iProver_split ),
    inference(instantiation,[status(thm)],[c_356])).

cnf(c_875,plain,
    ( ~ r1_partfun1(sK2,sK3)
    | ~ r1_partfun1(sK1,sK3)
    | r1_partfun1(sK1,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_43)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_43)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_43)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK1)
    | ~ sP0_iProver_split ),
    inference(instantiation,[status(thm)],[c_851])).

cnf(c_877,plain,
    ( ~ r1_partfun1(sK2,sK3)
    | ~ r1_partfun1(sK1,sK3)
    | r1_partfun1(sK1,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK1)
    | ~ sP0_iProver_split ),
    inference(instantiation,[status(thm)],[c_875])).

cnf(c_363,plain,
    ( X0_43 != X1_43
    | X2_43 != X3_43
    | k2_zfmisc_1(X0_43,X2_43) = k2_zfmisc_1(X1_43,X3_43) ),
    theory(equality)).

cnf(c_730,plain,
    ( X0_43 != sK0
    | X1_43 != sK0
    | k2_zfmisc_1(X0_43,X1_43) = k2_zfmisc_1(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_363])).

cnf(c_818,plain,
    ( sK0 != sK0
    | k1_xboole_0 != sK0
    | k2_zfmisc_1(k1_xboole_0,sK0) = k2_zfmisc_1(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_730])).

cnf(c_364,plain,
    ( X0_42 != X1_42
    | k1_zfmisc_1(X0_42) = k1_zfmisc_1(X1_42) ),
    theory(equality)).

cnf(c_684,plain,
    ( X0_42 != k2_zfmisc_1(sK0,sK0)
    | k1_zfmisc_1(X0_42) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_364])).

cnf(c_729,plain,
    ( k2_zfmisc_1(X0_43,X1_43) != k2_zfmisc_1(sK0,sK0)
    | k1_zfmisc_1(k2_zfmisc_1(X0_43,X1_43)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_684])).

cnf(c_799,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK0) != k2_zfmisc_1(sK0,sK0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_729])).

cnf(c_661,plain,
    ( m1_subset_1(sK3,X0_41)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | X0_41 != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_365])).

cnf(c_683,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(X0_42))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_zfmisc_1(X0_42) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_661])).

cnf(c_756,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_43,X1_43)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_zfmisc_1(k2_zfmisc_1(X0_43,X1_43)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_683])).

cnf(c_773,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_756])).

cnf(c_361,plain,
    ( X0_43 = X0_43 ),
    theory(equality)).

cnf(c_732,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_361])).

cnf(c_362,plain,
    ( X0_43 != X1_43
    | X2_43 != X1_43
    | X2_43 = X0_43 ),
    theory(equality)).

cnf(c_704,plain,
    ( X0_43 != X1_43
    | k1_xboole_0 != X1_43
    | k1_xboole_0 = X0_43 ),
    inference(instantiation,[status(thm)],[c_362])).

cnf(c_731,plain,
    ( X0_43 != k1_xboole_0
    | k1_xboole_0 = X0_43
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_704])).

cnf(c_733,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_731])).

cnf(c_1,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_partfun1(X0,X1)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f15])).

cnf(c_148,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_partfun1(X0,X1)
    | ~ v1_funct_1(X0)
    | sK0 != X1
    | sK0 != X2
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_7])).

cnf(c_149,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_partfun1(sK3,sK0)
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_148])).

cnf(c_6,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_151,plain,
    ( v1_partfun1(sK3,sK0)
    | k1_xboole_0 = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_149,c_8,c_6])).

cnf(c_211,plain,
    ( ~ r1_partfun1(X0,X1)
    | ~ r1_partfun1(X2,X1)
    | r1_partfun1(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | sK0 != X3
    | sK0 = k1_xboole_0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_151])).

cnf(c_212,plain,
    ( r1_partfun1(X0,X1)
    | ~ r1_partfun1(X0,sK3)
    | ~ r1_partfun1(X1,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | sK0 = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_211])).

cnf(c_216,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
    | ~ r1_partfun1(X1,sK3)
    | ~ r1_partfun1(X0,sK3)
    | r1_partfun1(X0,X1)
    | sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_212,c_8])).

cnf(c_217,plain,
    ( r1_partfun1(X0,X1)
    | ~ r1_partfun1(X0,sK3)
    | ~ r1_partfun1(X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_216])).

cnf(c_345,plain,
    ( r1_partfun1(X0_40,X1_40)
    | ~ r1_partfun1(X0_40,sK3)
    | ~ r1_partfun1(X1_40,sK3)
    | ~ m1_subset_1(X0_40,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_43)))
    | ~ m1_subset_1(X1_40,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_43)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_43)))
    | ~ v1_funct_1(X0_40)
    | ~ v1_funct_1(X1_40)
    | sK0 = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_217])).

cnf(c_658,plain,
    ( ~ r1_partfun1(X0_40,sK3)
    | r1_partfun1(sK1,X0_40)
    | ~ r1_partfun1(sK1,sK3)
    | ~ m1_subset_1(X0_40,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_43)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_43)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_43)))
    | ~ v1_funct_1(X0_40)
    | ~ v1_funct_1(sK1)
    | sK0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_345])).

cnf(c_697,plain,
    ( ~ r1_partfun1(sK2,sK3)
    | ~ r1_partfun1(sK1,sK3)
    | r1_partfun1(sK1,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_43)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_43)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_43)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK1)
    | sK0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_658])).

cnf(c_699,plain,
    ( ~ r1_partfun1(sK2,sK3)
    | ~ r1_partfun1(sK1,sK3)
    | r1_partfun1(sK1,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK1)
    | sK0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_697])).

cnf(c_357,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | sP0_iProver_split
    | sK0 != k1_xboole_0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_346])).

cnf(c_372,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_361])).

cnf(c_3,negated_conjecture,
    ( ~ r1_partfun1(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_4,negated_conjecture,
    ( r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_5,negated_conjecture,
    ( r1_partfun1(sK1,sK3) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_9,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_10,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_12,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_904,c_895,c_877,c_818,c_799,c_773,c_732,c_733,c_699,c_357,c_372,c_3,c_4,c_5,c_6,c_9,c_10,c_11,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:11:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 0.89/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.89/1.00  
% 0.89/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.89/1.00  
% 0.89/1.00  ------  iProver source info
% 0.89/1.00  
% 0.89/1.00  git: date: 2020-06-30 10:37:57 +0100
% 0.89/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.89/1.00  git: non_committed_changes: false
% 0.89/1.00  git: last_make_outside_of_git: false
% 0.89/1.00  
% 0.89/1.00  ------ 
% 0.89/1.00  
% 0.89/1.00  ------ Input Options
% 0.89/1.00  
% 0.89/1.00  --out_options                           all
% 0.89/1.00  --tptp_safe_out                         true
% 0.89/1.00  --problem_path                          ""
% 0.89/1.00  --include_path                          ""
% 0.89/1.00  --clausifier                            res/vclausify_rel
% 0.89/1.00  --clausifier_options                    --mode clausify
% 0.89/1.00  --stdin                                 false
% 0.89/1.00  --stats_out                             all
% 0.89/1.00  
% 0.89/1.00  ------ General Options
% 0.89/1.00  
% 0.89/1.00  --fof                                   false
% 0.89/1.00  --time_out_real                         305.
% 0.89/1.00  --time_out_virtual                      -1.
% 0.89/1.00  --symbol_type_check                     false
% 0.89/1.00  --clausify_out                          false
% 0.89/1.00  --sig_cnt_out                           false
% 0.89/1.00  --trig_cnt_out                          false
% 0.89/1.00  --trig_cnt_out_tolerance                1.
% 0.89/1.00  --trig_cnt_out_sk_spl                   false
% 0.89/1.00  --abstr_cl_out                          false
% 0.89/1.00  
% 0.89/1.00  ------ Global Options
% 0.89/1.00  
% 0.89/1.00  --schedule                              default
% 0.89/1.00  --add_important_lit                     false
% 0.89/1.00  --prop_solver_per_cl                    1000
% 0.89/1.00  --min_unsat_core                        false
% 0.89/1.00  --soft_assumptions                      false
% 0.89/1.00  --soft_lemma_size                       3
% 0.89/1.00  --prop_impl_unit_size                   0
% 0.89/1.00  --prop_impl_unit                        []
% 0.89/1.00  --share_sel_clauses                     true
% 0.89/1.00  --reset_solvers                         false
% 0.89/1.00  --bc_imp_inh                            [conj_cone]
% 0.89/1.00  --conj_cone_tolerance                   3.
% 0.89/1.00  --extra_neg_conj                        none
% 0.89/1.00  --large_theory_mode                     true
% 0.89/1.00  --prolific_symb_bound                   200
% 0.89/1.00  --lt_threshold                          2000
% 0.89/1.00  --clause_weak_htbl                      true
% 0.89/1.00  --gc_record_bc_elim                     false
% 0.89/1.00  
% 0.89/1.00  ------ Preprocessing Options
% 0.89/1.00  
% 0.89/1.00  --preprocessing_flag                    true
% 0.89/1.00  --time_out_prep_mult                    0.1
% 0.89/1.00  --splitting_mode                        input
% 0.89/1.00  --splitting_grd                         true
% 0.89/1.00  --splitting_cvd                         false
% 0.89/1.00  --splitting_cvd_svl                     false
% 0.89/1.00  --splitting_nvd                         32
% 0.89/1.00  --sub_typing                            true
% 0.89/1.00  --prep_gs_sim                           true
% 0.89/1.00  --prep_unflatten                        true
% 0.89/1.00  --prep_res_sim                          true
% 0.89/1.00  --prep_upred                            true
% 0.89/1.00  --prep_sem_filter                       exhaustive
% 0.89/1.00  --prep_sem_filter_out                   false
% 0.89/1.00  --pred_elim                             true
% 0.89/1.00  --res_sim_input                         true
% 0.89/1.00  --eq_ax_congr_red                       true
% 0.89/1.00  --pure_diseq_elim                       true
% 0.89/1.00  --brand_transform                       false
% 0.89/1.00  --non_eq_to_eq                          false
% 0.89/1.00  --prep_def_merge                        true
% 0.89/1.00  --prep_def_merge_prop_impl              false
% 0.89/1.00  --prep_def_merge_mbd                    true
% 0.89/1.00  --prep_def_merge_tr_red                 false
% 0.89/1.00  --prep_def_merge_tr_cl                  false
% 0.89/1.00  --smt_preprocessing                     true
% 0.89/1.00  --smt_ac_axioms                         fast
% 0.89/1.00  --preprocessed_out                      false
% 0.89/1.00  --preprocessed_stats                    false
% 0.89/1.00  
% 0.89/1.00  ------ Abstraction refinement Options
% 0.89/1.00  
% 0.89/1.00  --abstr_ref                             []
% 0.89/1.00  --abstr_ref_prep                        false
% 0.89/1.00  --abstr_ref_until_sat                   false
% 0.89/1.00  --abstr_ref_sig_restrict                funpre
% 0.89/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 0.89/1.00  --abstr_ref_under                       []
% 0.89/1.00  
% 0.89/1.00  ------ SAT Options
% 0.89/1.00  
% 0.89/1.00  --sat_mode                              false
% 0.89/1.00  --sat_fm_restart_options                ""
% 0.89/1.00  --sat_gr_def                            false
% 0.89/1.00  --sat_epr_types                         true
% 0.89/1.00  --sat_non_cyclic_types                  false
% 0.89/1.00  --sat_finite_models                     false
% 0.89/1.00  --sat_fm_lemmas                         false
% 0.89/1.00  --sat_fm_prep                           false
% 0.89/1.00  --sat_fm_uc_incr                        true
% 0.89/1.00  --sat_out_model                         small
% 0.89/1.00  --sat_out_clauses                       false
% 0.89/1.00  
% 0.89/1.00  ------ QBF Options
% 0.89/1.00  
% 0.89/1.00  --qbf_mode                              false
% 0.89/1.00  --qbf_elim_univ                         false
% 0.89/1.00  --qbf_dom_inst                          none
% 0.89/1.00  --qbf_dom_pre_inst                      false
% 0.89/1.00  --qbf_sk_in                             false
% 0.89/1.00  --qbf_pred_elim                         true
% 0.89/1.00  --qbf_split                             512
% 0.89/1.00  
% 0.89/1.00  ------ BMC1 Options
% 0.89/1.00  
% 0.89/1.00  --bmc1_incremental                      false
% 0.89/1.00  --bmc1_axioms                           reachable_all
% 0.89/1.00  --bmc1_min_bound                        0
% 0.89/1.00  --bmc1_max_bound                        -1
% 0.89/1.00  --bmc1_max_bound_default                -1
% 0.89/1.00  --bmc1_symbol_reachability              true
% 0.89/1.00  --bmc1_property_lemmas                  false
% 0.89/1.00  --bmc1_k_induction                      false
% 0.89/1.00  --bmc1_non_equiv_states                 false
% 0.89/1.00  --bmc1_deadlock                         false
% 0.89/1.00  --bmc1_ucm                              false
% 0.89/1.00  --bmc1_add_unsat_core                   none
% 0.89/1.00  --bmc1_unsat_core_children              false
% 0.89/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 0.89/1.00  --bmc1_out_stat                         full
% 0.89/1.00  --bmc1_ground_init                      false
% 0.89/1.00  --bmc1_pre_inst_next_state              false
% 0.89/1.00  --bmc1_pre_inst_state                   false
% 0.89/1.00  --bmc1_pre_inst_reach_state             false
% 0.89/1.00  --bmc1_out_unsat_core                   false
% 0.89/1.00  --bmc1_aig_witness_out                  false
% 0.89/1.00  --bmc1_verbose                          false
% 0.89/1.00  --bmc1_dump_clauses_tptp                false
% 0.89/1.00  --bmc1_dump_unsat_core_tptp             false
% 0.89/1.00  --bmc1_dump_file                        -
% 0.89/1.00  --bmc1_ucm_expand_uc_limit              128
% 0.89/1.00  --bmc1_ucm_n_expand_iterations          6
% 0.89/1.00  --bmc1_ucm_extend_mode                  1
% 0.89/1.00  --bmc1_ucm_init_mode                    2
% 0.89/1.00  --bmc1_ucm_cone_mode                    none
% 0.89/1.00  --bmc1_ucm_reduced_relation_type        0
% 0.89/1.00  --bmc1_ucm_relax_model                  4
% 0.89/1.00  --bmc1_ucm_full_tr_after_sat            true
% 0.89/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 0.89/1.00  --bmc1_ucm_layered_model                none
% 0.89/1.00  --bmc1_ucm_max_lemma_size               10
% 0.89/1.00  
% 0.89/1.00  ------ AIG Options
% 0.89/1.00  
% 0.89/1.00  --aig_mode                              false
% 0.89/1.00  
% 0.89/1.00  ------ Instantiation Options
% 0.89/1.00  
% 0.89/1.00  --instantiation_flag                    true
% 0.89/1.00  --inst_sos_flag                         false
% 0.89/1.00  --inst_sos_phase                        true
% 0.89/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.89/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.89/1.00  --inst_lit_sel_side                     num_symb
% 0.89/1.00  --inst_solver_per_active                1400
% 0.89/1.00  --inst_solver_calls_frac                1.
% 0.89/1.00  --inst_passive_queue_type               priority_queues
% 0.89/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.89/1.00  --inst_passive_queues_freq              [25;2]
% 0.89/1.00  --inst_dismatching                      true
% 0.89/1.00  --inst_eager_unprocessed_to_passive     true
% 0.89/1.00  --inst_prop_sim_given                   true
% 0.89/1.00  --inst_prop_sim_new                     false
% 0.89/1.00  --inst_subs_new                         false
% 0.89/1.00  --inst_eq_res_simp                      false
% 0.89/1.00  --inst_subs_given                       false
% 0.89/1.00  --inst_orphan_elimination               true
% 0.89/1.00  --inst_learning_loop_flag               true
% 0.89/1.00  --inst_learning_start                   3000
% 0.89/1.00  --inst_learning_factor                  2
% 0.89/1.00  --inst_start_prop_sim_after_learn       3
% 0.89/1.00  --inst_sel_renew                        solver
% 0.89/1.00  --inst_lit_activity_flag                true
% 0.89/1.00  --inst_restr_to_given                   false
% 0.89/1.00  --inst_activity_threshold               500
% 0.89/1.00  --inst_out_proof                        true
% 0.89/1.00  
% 0.89/1.00  ------ Resolution Options
% 0.89/1.00  
% 0.89/1.00  --resolution_flag                       true
% 0.89/1.00  --res_lit_sel                           adaptive
% 0.89/1.00  --res_lit_sel_side                      none
% 0.89/1.00  --res_ordering                          kbo
% 0.89/1.00  --res_to_prop_solver                    active
% 0.89/1.00  --res_prop_simpl_new                    false
% 0.89/1.00  --res_prop_simpl_given                  true
% 0.89/1.00  --res_passive_queue_type                priority_queues
% 0.89/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.89/1.00  --res_passive_queues_freq               [15;5]
% 0.89/1.00  --res_forward_subs                      full
% 0.89/1.00  --res_backward_subs                     full
% 0.89/1.00  --res_forward_subs_resolution           true
% 0.89/1.00  --res_backward_subs_resolution          true
% 0.89/1.00  --res_orphan_elimination                true
% 0.89/1.00  --res_time_limit                        2.
% 0.89/1.00  --res_out_proof                         true
% 0.89/1.00  
% 0.89/1.00  ------ Superposition Options
% 0.89/1.00  
% 0.89/1.00  --superposition_flag                    true
% 0.89/1.00  --sup_passive_queue_type                priority_queues
% 0.89/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.89/1.00  --sup_passive_queues_freq               [8;1;4]
% 0.89/1.00  --demod_completeness_check              fast
% 0.89/1.00  --demod_use_ground                      true
% 0.89/1.00  --sup_to_prop_solver                    passive
% 0.89/1.00  --sup_prop_simpl_new                    true
% 0.89/1.00  --sup_prop_simpl_given                  true
% 0.89/1.00  --sup_fun_splitting                     false
% 0.89/1.00  --sup_smt_interval                      50000
% 0.89/1.00  
% 0.89/1.00  ------ Superposition Simplification Setup
% 0.89/1.00  
% 0.89/1.00  --sup_indices_passive                   []
% 0.89/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.89/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.89/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.89/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 0.89/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.89/1.00  --sup_full_bw                           [BwDemod]
% 0.89/1.00  --sup_immed_triv                        [TrivRules]
% 0.89/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.89/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.89/1.00  --sup_immed_bw_main                     []
% 0.89/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.89/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 0.89/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.89/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.89/1.00  
% 0.89/1.00  ------ Combination Options
% 0.89/1.00  
% 0.89/1.00  --comb_res_mult                         3
% 0.89/1.00  --comb_sup_mult                         2
% 0.89/1.00  --comb_inst_mult                        10
% 0.89/1.00  
% 0.89/1.00  ------ Debug Options
% 0.89/1.00  
% 0.89/1.00  --dbg_backtrace                         false
% 0.89/1.00  --dbg_dump_prop_clauses                 false
% 0.89/1.00  --dbg_dump_prop_clauses_file            -
% 0.89/1.00  --dbg_out_stat                          false
% 0.89/1.00  ------ Parsing...
% 0.89/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.89/1.00  
% 0.89/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 0.89/1.00  
% 0.89/1.00  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.89/1.00  
% 0.89/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.89/1.00  ------ Proving...
% 0.89/1.00  ------ Problem Properties 
% 0.89/1.00  
% 0.89/1.00  
% 0.89/1.00  clauses                                 12
% 0.89/1.00  conjectures                             9
% 0.89/1.00  EPR                                     6
% 0.89/1.00  Horn                                    11
% 0.89/1.00  unary                                   9
% 0.89/1.00  binary                                  0
% 0.89/1.00  lits                                    30
% 0.89/1.00  lits eq                                 2
% 0.89/1.00  fd_pure                                 0
% 0.89/1.00  fd_pseudo                               0
% 0.89/1.00  fd_cond                                 0
% 0.89/1.00  fd_pseudo_cond                          0
% 0.89/1.00  AC symbols                              0
% 0.89/1.00  
% 0.89/1.00  ------ Schedule dynamic 5 is on 
% 0.89/1.00  
% 0.89/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.89/1.00  
% 0.89/1.00  
% 0.89/1.00  ------ 
% 0.89/1.00  Current options:
% 0.89/1.00  ------ 
% 0.89/1.00  
% 0.89/1.00  ------ Input Options
% 0.89/1.00  
% 0.89/1.00  --out_options                           all
% 0.89/1.00  --tptp_safe_out                         true
% 0.89/1.00  --problem_path                          ""
% 0.89/1.00  --include_path                          ""
% 0.89/1.00  --clausifier                            res/vclausify_rel
% 0.89/1.00  --clausifier_options                    --mode clausify
% 0.89/1.00  --stdin                                 false
% 0.89/1.00  --stats_out                             all
% 0.89/1.00  
% 0.89/1.00  ------ General Options
% 0.89/1.00  
% 0.89/1.00  --fof                                   false
% 0.89/1.00  --time_out_real                         305.
% 0.89/1.00  --time_out_virtual                      -1.
% 0.89/1.00  --symbol_type_check                     false
% 0.89/1.00  --clausify_out                          false
% 0.89/1.00  --sig_cnt_out                           false
% 0.89/1.00  --trig_cnt_out                          false
% 0.89/1.00  --trig_cnt_out_tolerance                1.
% 0.89/1.00  --trig_cnt_out_sk_spl                   false
% 0.89/1.00  --abstr_cl_out                          false
% 0.89/1.00  
% 0.89/1.00  ------ Global Options
% 0.89/1.00  
% 0.89/1.00  --schedule                              default
% 0.89/1.00  --add_important_lit                     false
% 0.89/1.00  --prop_solver_per_cl                    1000
% 0.89/1.00  --min_unsat_core                        false
% 0.89/1.00  --soft_assumptions                      false
% 0.89/1.00  --soft_lemma_size                       3
% 0.89/1.00  --prop_impl_unit_size                   0
% 0.89/1.00  --prop_impl_unit                        []
% 0.89/1.00  --share_sel_clauses                     true
% 0.89/1.00  --reset_solvers                         false
% 0.89/1.00  --bc_imp_inh                            [conj_cone]
% 0.89/1.00  --conj_cone_tolerance                   3.
% 0.89/1.00  --extra_neg_conj                        none
% 0.89/1.00  --large_theory_mode                     true
% 0.89/1.00  --prolific_symb_bound                   200
% 0.89/1.00  --lt_threshold                          2000
% 0.89/1.00  --clause_weak_htbl                      true
% 0.89/1.00  --gc_record_bc_elim                     false
% 0.89/1.00  
% 0.89/1.00  ------ Preprocessing Options
% 0.89/1.00  
% 0.89/1.00  --preprocessing_flag                    true
% 0.89/1.00  --time_out_prep_mult                    0.1
% 0.89/1.00  --splitting_mode                        input
% 0.89/1.00  --splitting_grd                         true
% 0.89/1.00  --splitting_cvd                         false
% 0.89/1.00  --splitting_cvd_svl                     false
% 0.89/1.00  --splitting_nvd                         32
% 0.89/1.00  --sub_typing                            true
% 0.89/1.00  --prep_gs_sim                           true
% 0.89/1.00  --prep_unflatten                        true
% 0.89/1.00  --prep_res_sim                          true
% 0.89/1.00  --prep_upred                            true
% 0.89/1.00  --prep_sem_filter                       exhaustive
% 0.89/1.00  --prep_sem_filter_out                   false
% 0.89/1.00  --pred_elim                             true
% 0.89/1.00  --res_sim_input                         true
% 0.89/1.00  --eq_ax_congr_red                       true
% 0.89/1.00  --pure_diseq_elim                       true
% 0.89/1.00  --brand_transform                       false
% 0.89/1.00  --non_eq_to_eq                          false
% 0.89/1.00  --prep_def_merge                        true
% 0.89/1.00  --prep_def_merge_prop_impl              false
% 0.89/1.00  --prep_def_merge_mbd                    true
% 0.89/1.00  --prep_def_merge_tr_red                 false
% 0.89/1.00  --prep_def_merge_tr_cl                  false
% 0.89/1.00  --smt_preprocessing                     true
% 0.89/1.00  --smt_ac_axioms                         fast
% 0.89/1.00  --preprocessed_out                      false
% 0.89/1.00  --preprocessed_stats                    false
% 0.89/1.00  
% 0.89/1.00  ------ Abstraction refinement Options
% 0.89/1.00  
% 0.89/1.00  --abstr_ref                             []
% 0.89/1.00  --abstr_ref_prep                        false
% 0.89/1.00  --abstr_ref_until_sat                   false
% 0.89/1.00  --abstr_ref_sig_restrict                funpre
% 0.89/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 0.89/1.00  --abstr_ref_under                       []
% 0.89/1.00  
% 0.89/1.00  ------ SAT Options
% 0.89/1.00  
% 0.89/1.00  --sat_mode                              false
% 0.89/1.00  --sat_fm_restart_options                ""
% 0.89/1.00  --sat_gr_def                            false
% 0.89/1.00  --sat_epr_types                         true
% 0.89/1.00  --sat_non_cyclic_types                  false
% 0.89/1.00  --sat_finite_models                     false
% 0.89/1.00  --sat_fm_lemmas                         false
% 0.89/1.00  --sat_fm_prep                           false
% 0.89/1.00  --sat_fm_uc_incr                        true
% 0.89/1.00  --sat_out_model                         small
% 0.89/1.00  --sat_out_clauses                       false
% 0.89/1.00  
% 0.89/1.00  ------ QBF Options
% 0.89/1.00  
% 0.89/1.00  --qbf_mode                              false
% 0.89/1.00  --qbf_elim_univ                         false
% 0.89/1.00  --qbf_dom_inst                          none
% 0.89/1.00  --qbf_dom_pre_inst                      false
% 0.89/1.00  --qbf_sk_in                             false
% 0.89/1.00  --qbf_pred_elim                         true
% 0.89/1.00  --qbf_split                             512
% 0.89/1.00  
% 0.89/1.00  ------ BMC1 Options
% 0.89/1.00  
% 0.89/1.00  --bmc1_incremental                      false
% 0.89/1.00  --bmc1_axioms                           reachable_all
% 0.89/1.00  --bmc1_min_bound                        0
% 0.89/1.00  --bmc1_max_bound                        -1
% 0.89/1.00  --bmc1_max_bound_default                -1
% 0.89/1.00  --bmc1_symbol_reachability              true
% 0.89/1.00  --bmc1_property_lemmas                  false
% 0.89/1.00  --bmc1_k_induction                      false
% 0.89/1.00  --bmc1_non_equiv_states                 false
% 0.89/1.00  --bmc1_deadlock                         false
% 0.89/1.00  --bmc1_ucm                              false
% 0.89/1.00  --bmc1_add_unsat_core                   none
% 0.89/1.00  --bmc1_unsat_core_children              false
% 0.89/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 0.89/1.00  --bmc1_out_stat                         full
% 0.89/1.00  --bmc1_ground_init                      false
% 0.89/1.00  --bmc1_pre_inst_next_state              false
% 0.89/1.00  --bmc1_pre_inst_state                   false
% 0.89/1.00  --bmc1_pre_inst_reach_state             false
% 0.89/1.00  --bmc1_out_unsat_core                   false
% 0.89/1.00  --bmc1_aig_witness_out                  false
% 0.89/1.00  --bmc1_verbose                          false
% 0.89/1.00  --bmc1_dump_clauses_tptp                false
% 0.89/1.00  --bmc1_dump_unsat_core_tptp             false
% 0.89/1.00  --bmc1_dump_file                        -
% 0.89/1.00  --bmc1_ucm_expand_uc_limit              128
% 0.89/1.00  --bmc1_ucm_n_expand_iterations          6
% 0.89/1.00  --bmc1_ucm_extend_mode                  1
% 0.89/1.00  --bmc1_ucm_init_mode                    2
% 0.89/1.00  --bmc1_ucm_cone_mode                    none
% 0.89/1.00  --bmc1_ucm_reduced_relation_type        0
% 0.89/1.00  --bmc1_ucm_relax_model                  4
% 0.89/1.00  --bmc1_ucm_full_tr_after_sat            true
% 0.89/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 0.89/1.00  --bmc1_ucm_layered_model                none
% 0.89/1.00  --bmc1_ucm_max_lemma_size               10
% 0.89/1.00  
% 0.89/1.00  ------ AIG Options
% 0.89/1.00  
% 0.89/1.00  --aig_mode                              false
% 0.89/1.00  
% 0.89/1.00  ------ Instantiation Options
% 0.89/1.00  
% 0.89/1.00  --instantiation_flag                    true
% 0.89/1.00  --inst_sos_flag                         false
% 0.89/1.00  --inst_sos_phase                        true
% 0.89/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.89/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.89/1.00  --inst_lit_sel_side                     none
% 0.89/1.00  --inst_solver_per_active                1400
% 0.89/1.00  --inst_solver_calls_frac                1.
% 0.89/1.00  --inst_passive_queue_type               priority_queues
% 0.89/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.89/1.00  --inst_passive_queues_freq              [25;2]
% 0.89/1.00  --inst_dismatching                      true
% 0.89/1.00  --inst_eager_unprocessed_to_passive     true
% 0.89/1.00  --inst_prop_sim_given                   true
% 0.89/1.00  --inst_prop_sim_new                     false
% 0.89/1.00  --inst_subs_new                         false
% 0.89/1.00  --inst_eq_res_simp                      false
% 0.89/1.00  --inst_subs_given                       false
% 0.89/1.00  --inst_orphan_elimination               true
% 0.89/1.00  --inst_learning_loop_flag               true
% 0.89/1.00  --inst_learning_start                   3000
% 0.89/1.00  --inst_learning_factor                  2
% 0.89/1.00  --inst_start_prop_sim_after_learn       3
% 0.89/1.00  --inst_sel_renew                        solver
% 0.89/1.00  --inst_lit_activity_flag                true
% 0.89/1.00  --inst_restr_to_given                   false
% 0.89/1.00  --inst_activity_threshold               500
% 0.89/1.00  --inst_out_proof                        true
% 0.89/1.00  
% 0.89/1.00  ------ Resolution Options
% 0.89/1.00  
% 0.89/1.00  --resolution_flag                       false
% 0.89/1.00  --res_lit_sel                           adaptive
% 0.89/1.00  --res_lit_sel_side                      none
% 0.89/1.00  --res_ordering                          kbo
% 0.89/1.00  --res_to_prop_solver                    active
% 0.89/1.00  --res_prop_simpl_new                    false
% 0.89/1.00  --res_prop_simpl_given                  true
% 0.89/1.00  --res_passive_queue_type                priority_queues
% 0.89/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.89/1.00  --res_passive_queues_freq               [15;5]
% 0.89/1.00  --res_forward_subs                      full
% 0.89/1.00  --res_backward_subs                     full
% 0.89/1.00  --res_forward_subs_resolution           true
% 0.89/1.00  --res_backward_subs_resolution          true
% 0.89/1.00  --res_orphan_elimination                true
% 0.89/1.00  --res_time_limit                        2.
% 0.89/1.00  --res_out_proof                         true
% 0.89/1.00  
% 0.89/1.00  ------ Superposition Options
% 0.89/1.00  
% 0.89/1.00  --superposition_flag                    true
% 0.89/1.00  --sup_passive_queue_type                priority_queues
% 0.89/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.89/1.00  --sup_passive_queues_freq               [8;1;4]
% 0.89/1.00  --demod_completeness_check              fast
% 0.89/1.00  --demod_use_ground                      true
% 0.89/1.00  --sup_to_prop_solver                    passive
% 0.89/1.00  --sup_prop_simpl_new                    true
% 0.89/1.00  --sup_prop_simpl_given                  true
% 0.89/1.00  --sup_fun_splitting                     false
% 0.89/1.00  --sup_smt_interval                      50000
% 0.89/1.00  
% 0.89/1.00  ------ Superposition Simplification Setup
% 0.89/1.00  
% 0.89/1.00  --sup_indices_passive                   []
% 0.89/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.89/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.89/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.89/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 0.89/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.89/1.00  --sup_full_bw                           [BwDemod]
% 0.89/1.00  --sup_immed_triv                        [TrivRules]
% 0.89/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.89/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.89/1.00  --sup_immed_bw_main                     []
% 0.89/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.89/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 0.89/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.89/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.89/1.00  
% 0.89/1.00  ------ Combination Options
% 0.89/1.00  
% 0.89/1.00  --comb_res_mult                         3
% 0.89/1.00  --comb_sup_mult                         2
% 0.89/1.00  --comb_inst_mult                        10
% 0.89/1.00  
% 0.89/1.00  ------ Debug Options
% 0.89/1.00  
% 0.89/1.00  --dbg_backtrace                         false
% 0.89/1.00  --dbg_dump_prop_clauses                 false
% 0.89/1.00  --dbg_dump_prop_clauses_file            -
% 0.89/1.00  --dbg_out_stat                          false
% 0.89/1.00  
% 0.89/1.00  
% 0.89/1.00  
% 0.89/1.00  
% 0.89/1.00  ------ Proving...
% 0.89/1.00  
% 0.89/1.00  
% 0.89/1.00  % SZS status Theorem for theBenchmark.p
% 0.89/1.00  
% 0.89/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 0.89/1.00  
% 0.89/1.00  fof(f2,axiom,(
% 0.89/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => ((v1_partfun1(X4,X0) & r1_partfun1(X3,X4) & r1_partfun1(X2,X4)) => r1_partfun1(X2,X3)))))),
% 0.89/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.89/1.00  
% 0.89/1.00  fof(f7,plain,(
% 0.89/1.00    ! [X0,X1,X2] : (! [X3] : (! [X4] : ((r1_partfun1(X2,X3) | (~v1_partfun1(X4,X0) | ~r1_partfun1(X3,X4) | ~r1_partfun1(X2,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.89/1.00    inference(ennf_transformation,[],[f2])).
% 0.89/1.00  
% 0.89/1.00  fof(f8,plain,(
% 0.89/1.00    ! [X0,X1,X2] : (! [X3] : (! [X4] : (r1_partfun1(X2,X3) | ~v1_partfun1(X4,X0) | ~r1_partfun1(X3,X4) | ~r1_partfun1(X2,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.89/1.00    inference(flattening,[],[f7])).
% 0.89/1.00  
% 0.89/1.00  fof(f17,plain,(
% 0.89/1.00    ( ! [X4,X2,X0,X3,X1] : (r1_partfun1(X2,X3) | ~v1_partfun1(X4,X0) | ~r1_partfun1(X3,X4) | ~r1_partfun1(X2,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.89/1.00    inference(cnf_transformation,[],[f8])).
% 0.89/1.00  
% 0.89/1.00  fof(f1,axiom,(
% 0.89/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.89/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.89/1.00  
% 0.89/1.00  fof(f5,plain,(
% 0.89/1.00    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.89/1.00    inference(ennf_transformation,[],[f1])).
% 0.89/1.00  
% 0.89/1.00  fof(f6,plain,(
% 0.89/1.00    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.89/1.00    inference(flattening,[],[f5])).
% 0.89/1.00  
% 0.89/1.00  fof(f16,plain,(
% 0.89/1.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.89/1.00    inference(cnf_transformation,[],[f6])).
% 0.89/1.00  
% 0.89/1.00  fof(f28,plain,(
% 0.89/1.00    ( ! [X2,X1] : (v1_partfun1(X2,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2)) )),
% 0.89/1.00    inference(equality_resolution,[],[f16])).
% 0.89/1.00  
% 0.89/1.00  fof(f3,conjecture,(
% 0.89/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X3,X0,X0) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & r1_partfun1(X1,X3)) => r1_partfun1(X1,X2)))))),
% 0.89/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.89/1.00  
% 0.89/1.00  fof(f4,negated_conjecture,(
% 0.89/1.00    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X3,X0,X0) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & r1_partfun1(X1,X3)) => r1_partfun1(X1,X2)))))),
% 0.89/1.00    inference(negated_conjecture,[],[f3])).
% 0.89/1.00  
% 0.89/1.00  fof(f9,plain,(
% 0.89/1.00    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_partfun1(X1,X2) & (r1_partfun1(X2,X3) & r1_partfun1(X1,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X3,X0,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)))),
% 0.89/1.00    inference(ennf_transformation,[],[f4])).
% 0.89/1.00  
% 0.89/1.00  fof(f10,plain,(
% 0.89/1.00    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_partfun1(X1,X2) & r1_partfun1(X2,X3) & r1_partfun1(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X3,X0,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 0.89/1.00    inference(flattening,[],[f9])).
% 0.89/1.00  
% 0.89/1.00  fof(f13,plain,(
% 0.89/1.00    ( ! [X2,X0,X1] : (? [X3] : (~r1_partfun1(X1,X2) & r1_partfun1(X2,X3) & r1_partfun1(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X3,X0,X0) & v1_funct_1(X3)) => (~r1_partfun1(X1,X2) & r1_partfun1(X2,sK3) & r1_partfun1(X1,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(sK3,X0,X0) & v1_funct_1(sK3))) )),
% 0.89/1.00    introduced(choice_axiom,[])).
% 0.89/1.00  
% 0.89/1.00  fof(f12,plain,(
% 0.89/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_partfun1(X1,X2) & r1_partfun1(X2,X3) & r1_partfun1(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X3,X0,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X2)) => (? [X3] : (~r1_partfun1(X1,sK2) & r1_partfun1(sK2,X3) & r1_partfun1(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X3,X0,X0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(sK2))) )),
% 0.89/1.00    introduced(choice_axiom,[])).
% 0.89/1.00  
% 0.89/1.00  fof(f11,plain,(
% 0.89/1.00    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_partfun1(X1,X2) & r1_partfun1(X2,X3) & r1_partfun1(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X3,X0,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => (? [X2] : (? [X3] : (~r1_partfun1(sK1,X2) & r1_partfun1(X2,X3) & r1_partfun1(sK1,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X3,sK0,sK0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(sK1))),
% 0.89/1.00    introduced(choice_axiom,[])).
% 0.89/1.00  
% 0.89/1.00  fof(f14,plain,(
% 0.89/1.00    ((~r1_partfun1(sK1,sK2) & r1_partfun1(sK2,sK3) & r1_partfun1(sK1,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK3,sK0,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(sK1)),
% 0.89/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f13,f12,f11])).
% 0.89/1.00  
% 0.89/1.00  fof(f23,plain,(
% 0.89/1.00    v1_funct_2(sK3,sK0,sK0)),
% 0.89/1.00    inference(cnf_transformation,[],[f14])).
% 0.89/1.00  
% 0.89/1.00  fof(f22,plain,(
% 0.89/1.00    v1_funct_1(sK3)),
% 0.89/1.00    inference(cnf_transformation,[],[f14])).
% 0.89/1.00  
% 0.89/1.00  fof(f15,plain,(
% 0.89/1.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.89/1.00    inference(cnf_transformation,[],[f6])).
% 0.89/1.00  
% 0.89/1.00  fof(f24,plain,(
% 0.89/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.89/1.00    inference(cnf_transformation,[],[f14])).
% 0.89/1.00  
% 0.89/1.00  fof(f27,plain,(
% 0.89/1.00    ~r1_partfun1(sK1,sK2)),
% 0.89/1.00    inference(cnf_transformation,[],[f14])).
% 0.89/1.00  
% 0.89/1.00  fof(f26,plain,(
% 0.89/1.00    r1_partfun1(sK2,sK3)),
% 0.89/1.00    inference(cnf_transformation,[],[f14])).
% 0.89/1.00  
% 0.89/1.00  fof(f25,plain,(
% 0.89/1.00    r1_partfun1(sK1,sK3)),
% 0.89/1.00    inference(cnf_transformation,[],[f14])).
% 0.89/1.00  
% 0.89/1.00  fof(f21,plain,(
% 0.89/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.89/1.00    inference(cnf_transformation,[],[f14])).
% 0.89/1.00  
% 0.89/1.00  fof(f20,plain,(
% 0.89/1.00    v1_funct_1(sK2)),
% 0.89/1.00    inference(cnf_transformation,[],[f14])).
% 0.89/1.00  
% 0.89/1.00  fof(f19,plain,(
% 0.89/1.00    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.89/1.00    inference(cnf_transformation,[],[f14])).
% 0.89/1.00  
% 0.89/1.00  fof(f18,plain,(
% 0.89/1.00    v1_funct_1(sK1)),
% 0.89/1.00    inference(cnf_transformation,[],[f14])).
% 0.89/1.00  
% 0.89/1.00  cnf(c_365,plain,
% 0.89/1.00      ( ~ m1_subset_1(X0_40,X0_41)
% 0.89/1.00      | m1_subset_1(X0_40,X1_41)
% 0.89/1.00      | X1_41 != X0_41 ),
% 0.89/1.00      theory(equality) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_671,plain,
% 0.89/1.00      ( m1_subset_1(sK1,X0_41)
% 0.89/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 0.89/1.00      | X0_41 != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 0.89/1.00      inference(instantiation,[status(thm)],[c_365]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_705,plain,
% 0.89/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(X0_42))
% 0.89/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 0.89/1.00      | k1_zfmisc_1(X0_42) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 0.89/1.00      inference(instantiation,[status(thm)],[c_671]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_755,plain,
% 0.89/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_43,X1_43)))
% 0.89/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 0.89/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0_43,X1_43)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 0.89/1.00      inference(instantiation,[status(thm)],[c_705]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_902,plain,
% 0.89/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 0.89/1.00      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_43)))
% 0.89/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_43)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 0.89/1.00      inference(instantiation,[status(thm)],[c_755]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_904,plain,
% 0.89/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 0.89/1.00      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 0.89/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 0.89/1.00      inference(instantiation,[status(thm)],[c_902]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_666,plain,
% 0.89/1.00      ( m1_subset_1(sK2,X0_41)
% 0.89/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 0.89/1.00      | X0_41 != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 0.89/1.00      inference(instantiation,[status(thm)],[c_365]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_706,plain,
% 0.89/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(X0_42))
% 0.89/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 0.89/1.00      | k1_zfmisc_1(X0_42) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 0.89/1.00      inference(instantiation,[status(thm)],[c_666]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_754,plain,
% 0.89/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_43,X1_43)))
% 0.89/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 0.89/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0_43,X1_43)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 0.89/1.00      inference(instantiation,[status(thm)],[c_706]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_893,plain,
% 0.89/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 0.89/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_43)))
% 0.89/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_43)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 0.89/1.00      inference(instantiation,[status(thm)],[c_754]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_895,plain,
% 0.89/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 0.89/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 0.89/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 0.89/1.00      inference(instantiation,[status(thm)],[c_893]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_2,plain,
% 0.89/1.00      ( ~ r1_partfun1(X0,X1)
% 0.89/1.00      | ~ r1_partfun1(X2,X1)
% 0.89/1.00      | r1_partfun1(X2,X0)
% 0.89/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 0.89/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 0.89/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 0.89/1.00      | ~ v1_partfun1(X1,X3)
% 0.89/1.00      | ~ v1_funct_1(X2)
% 0.89/1.00      | ~ v1_funct_1(X1)
% 0.89/1.00      | ~ v1_funct_1(X0) ),
% 0.89/1.00      inference(cnf_transformation,[],[f17]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_0,plain,
% 0.89/1.00      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 0.89/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 0.89/1.00      | v1_partfun1(X0,k1_xboole_0)
% 0.89/1.00      | ~ v1_funct_1(X0) ),
% 0.89/1.00      inference(cnf_transformation,[],[f28]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_7,negated_conjecture,
% 0.89/1.00      ( v1_funct_2(sK3,sK0,sK0) ),
% 0.89/1.00      inference(cnf_transformation,[],[f23]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_131,plain,
% 0.89/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 0.89/1.00      | v1_partfun1(X0,k1_xboole_0)
% 0.89/1.00      | ~ v1_funct_1(X0)
% 0.89/1.00      | sK0 != X1
% 0.89/1.00      | sK0 != k1_xboole_0
% 0.89/1.00      | sK3 != X0 ),
% 0.89/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_7]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_132,plain,
% 0.89/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 0.89/1.00      | v1_partfun1(sK3,k1_xboole_0)
% 0.89/1.00      | ~ v1_funct_1(sK3)
% 0.89/1.00      | sK0 != k1_xboole_0 ),
% 0.89/1.00      inference(unflattening,[status(thm)],[c_131]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_8,negated_conjecture,
% 0.89/1.00      ( v1_funct_1(sK3) ),
% 0.89/1.00      inference(cnf_transformation,[],[f22]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_134,plain,
% 0.89/1.00      ( v1_partfun1(sK3,k1_xboole_0)
% 0.89/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 0.89/1.00      | sK0 != k1_xboole_0 ),
% 0.89/1.00      inference(global_propositional_subsumption,
% 0.89/1.00                [status(thm)],
% 0.89/1.00                [c_132,c_8]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_135,plain,
% 0.89/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 0.89/1.00      | v1_partfun1(sK3,k1_xboole_0)
% 0.89/1.00      | sK0 != k1_xboole_0 ),
% 0.89/1.00      inference(renaming,[status(thm)],[c_134]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_169,plain,
% 0.89/1.00      ( ~ r1_partfun1(X0,X1)
% 0.89/1.00      | ~ r1_partfun1(X2,X1)
% 0.89/1.00      | r1_partfun1(X2,X0)
% 0.89/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 0.89/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 0.89/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 0.89/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 0.89/1.00      | ~ v1_funct_1(X0)
% 0.89/1.00      | ~ v1_funct_1(X2)
% 0.89/1.00      | ~ v1_funct_1(X1)
% 0.89/1.00      | sK0 != k1_xboole_0
% 0.89/1.00      | sK3 != X1
% 0.89/1.00      | k1_xboole_0 != X3 ),
% 0.89/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_135]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_170,plain,
% 0.89/1.00      ( r1_partfun1(X0,X1)
% 0.89/1.00      | ~ r1_partfun1(X0,sK3)
% 0.89/1.00      | ~ r1_partfun1(X1,sK3)
% 0.89/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
% 0.89/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
% 0.89/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
% 0.89/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 0.89/1.00      | ~ v1_funct_1(X1)
% 0.89/1.00      | ~ v1_funct_1(X0)
% 0.89/1.00      | ~ v1_funct_1(sK3)
% 0.89/1.00      | sK0 != k1_xboole_0 ),
% 0.89/1.00      inference(unflattening,[status(thm)],[c_169]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_174,plain,
% 0.89/1.00      ( ~ v1_funct_1(X0)
% 0.89/1.00      | ~ v1_funct_1(X1)
% 0.89/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 0.89/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
% 0.89/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
% 0.89/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
% 0.89/1.00      | ~ r1_partfun1(X1,sK3)
% 0.89/1.00      | ~ r1_partfun1(X0,sK3)
% 0.89/1.00      | r1_partfun1(X0,X1)
% 0.89/1.00      | sK0 != k1_xboole_0 ),
% 0.89/1.00      inference(global_propositional_subsumption,
% 0.89/1.00                [status(thm)],
% 0.89/1.00                [c_170,c_8]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_175,plain,
% 0.89/1.00      ( r1_partfun1(X0,X1)
% 0.89/1.00      | ~ r1_partfun1(X0,sK3)
% 0.89/1.00      | ~ r1_partfun1(X1,sK3)
% 0.89/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
% 0.89/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
% 0.89/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
% 0.89/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 0.89/1.00      | ~ v1_funct_1(X0)
% 0.89/1.00      | ~ v1_funct_1(X1)
% 0.89/1.00      | sK0 != k1_xboole_0 ),
% 0.89/1.00      inference(renaming,[status(thm)],[c_174]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_346,plain,
% 0.89/1.00      ( r1_partfun1(X0_40,X1_40)
% 0.89/1.00      | ~ r1_partfun1(X0_40,sK3)
% 0.89/1.00      | ~ r1_partfun1(X1_40,sK3)
% 0.89/1.00      | ~ m1_subset_1(X1_40,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_43)))
% 0.89/1.00      | ~ m1_subset_1(X0_40,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_43)))
% 0.89/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_43)))
% 0.89/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 0.89/1.00      | ~ v1_funct_1(X0_40)
% 0.89/1.00      | ~ v1_funct_1(X1_40)
% 0.89/1.00      | sK0 != k1_xboole_0 ),
% 0.89/1.00      inference(subtyping,[status(esa)],[c_175]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_356,plain,
% 0.89/1.00      ( r1_partfun1(X0_40,X1_40)
% 0.89/1.00      | ~ r1_partfun1(X0_40,sK3)
% 0.89/1.00      | ~ r1_partfun1(X1_40,sK3)
% 0.89/1.00      | ~ m1_subset_1(X1_40,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_43)))
% 0.89/1.00      | ~ m1_subset_1(X0_40,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_43)))
% 0.89/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_43)))
% 0.89/1.00      | ~ v1_funct_1(X0_40)
% 0.89/1.00      | ~ v1_funct_1(X1_40)
% 0.89/1.00      | ~ sP0_iProver_split ),
% 0.89/1.00      inference(splitting,
% 0.89/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 0.89/1.00                [c_346]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_851,plain,
% 0.89/1.00      ( ~ r1_partfun1(X0_40,sK3)
% 0.89/1.00      | r1_partfun1(sK1,X0_40)
% 0.89/1.00      | ~ r1_partfun1(sK1,sK3)
% 0.89/1.00      | ~ m1_subset_1(X0_40,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_43)))
% 0.89/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_43)))
% 0.89/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_43)))
% 0.89/1.00      | ~ v1_funct_1(X0_40)
% 0.89/1.00      | ~ v1_funct_1(sK1)
% 0.89/1.00      | ~ sP0_iProver_split ),
% 0.89/1.00      inference(instantiation,[status(thm)],[c_356]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_875,plain,
% 0.89/1.00      ( ~ r1_partfun1(sK2,sK3)
% 0.89/1.00      | ~ r1_partfun1(sK1,sK3)
% 0.89/1.00      | r1_partfun1(sK1,sK2)
% 0.89/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_43)))
% 0.89/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_43)))
% 0.89/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_43)))
% 0.89/1.00      | ~ v1_funct_1(sK2)
% 0.89/1.00      | ~ v1_funct_1(sK1)
% 0.89/1.00      | ~ sP0_iProver_split ),
% 0.89/1.00      inference(instantiation,[status(thm)],[c_851]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_877,plain,
% 0.89/1.00      ( ~ r1_partfun1(sK2,sK3)
% 0.89/1.00      | ~ r1_partfun1(sK1,sK3)
% 0.89/1.00      | r1_partfun1(sK1,sK2)
% 0.89/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 0.89/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 0.89/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 0.89/1.00      | ~ v1_funct_1(sK2)
% 0.89/1.00      | ~ v1_funct_1(sK1)
% 0.89/1.00      | ~ sP0_iProver_split ),
% 0.89/1.00      inference(instantiation,[status(thm)],[c_875]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_363,plain,
% 0.89/1.00      ( X0_43 != X1_43
% 0.89/1.00      | X2_43 != X3_43
% 0.89/1.00      | k2_zfmisc_1(X0_43,X2_43) = k2_zfmisc_1(X1_43,X3_43) ),
% 0.89/1.00      theory(equality) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_730,plain,
% 0.89/1.00      ( X0_43 != sK0
% 0.89/1.00      | X1_43 != sK0
% 0.89/1.00      | k2_zfmisc_1(X0_43,X1_43) = k2_zfmisc_1(sK0,sK0) ),
% 0.89/1.00      inference(instantiation,[status(thm)],[c_363]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_818,plain,
% 0.89/1.00      ( sK0 != sK0
% 0.89/1.00      | k1_xboole_0 != sK0
% 0.89/1.00      | k2_zfmisc_1(k1_xboole_0,sK0) = k2_zfmisc_1(sK0,sK0) ),
% 0.89/1.00      inference(instantiation,[status(thm)],[c_730]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_364,plain,
% 0.89/1.00      ( X0_42 != X1_42 | k1_zfmisc_1(X0_42) = k1_zfmisc_1(X1_42) ),
% 0.89/1.00      theory(equality) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_684,plain,
% 0.89/1.00      ( X0_42 != k2_zfmisc_1(sK0,sK0)
% 0.89/1.00      | k1_zfmisc_1(X0_42) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 0.89/1.00      inference(instantiation,[status(thm)],[c_364]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_729,plain,
% 0.89/1.00      ( k2_zfmisc_1(X0_43,X1_43) != k2_zfmisc_1(sK0,sK0)
% 0.89/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0_43,X1_43)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 0.89/1.00      inference(instantiation,[status(thm)],[c_684]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_799,plain,
% 0.89/1.00      ( k2_zfmisc_1(k1_xboole_0,sK0) != k2_zfmisc_1(sK0,sK0)
% 0.89/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 0.89/1.00      inference(instantiation,[status(thm)],[c_729]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_661,plain,
% 0.89/1.00      ( m1_subset_1(sK3,X0_41)
% 0.89/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 0.89/1.00      | X0_41 != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 0.89/1.00      inference(instantiation,[status(thm)],[c_365]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_683,plain,
% 0.89/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(X0_42))
% 0.89/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 0.89/1.00      | k1_zfmisc_1(X0_42) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 0.89/1.00      inference(instantiation,[status(thm)],[c_661]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_756,plain,
% 0.89/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_43,X1_43)))
% 0.89/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 0.89/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0_43,X1_43)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 0.89/1.00      inference(instantiation,[status(thm)],[c_683]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_773,plain,
% 0.89/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 0.89/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 0.89/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 0.89/1.00      inference(instantiation,[status(thm)],[c_756]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_361,plain,( X0_43 = X0_43 ),theory(equality) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_732,plain,
% 0.89/1.00      ( k1_xboole_0 = k1_xboole_0 ),
% 0.89/1.00      inference(instantiation,[status(thm)],[c_361]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_362,plain,
% 0.89/1.00      ( X0_43 != X1_43 | X2_43 != X1_43 | X2_43 = X0_43 ),
% 0.89/1.00      theory(equality) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_704,plain,
% 0.89/1.00      ( X0_43 != X1_43 | k1_xboole_0 != X1_43 | k1_xboole_0 = X0_43 ),
% 0.89/1.00      inference(instantiation,[status(thm)],[c_362]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_731,plain,
% 0.89/1.00      ( X0_43 != k1_xboole_0
% 0.89/1.00      | k1_xboole_0 = X0_43
% 0.89/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 0.89/1.00      inference(instantiation,[status(thm)],[c_704]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_733,plain,
% 0.89/1.00      ( sK0 != k1_xboole_0
% 0.89/1.00      | k1_xboole_0 = sK0
% 0.89/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 0.89/1.00      inference(instantiation,[status(thm)],[c_731]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_1,plain,
% 0.89/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 0.89/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.89/1.00      | v1_partfun1(X0,X1)
% 0.89/1.00      | ~ v1_funct_1(X0)
% 0.89/1.00      | k1_xboole_0 = X2 ),
% 0.89/1.00      inference(cnf_transformation,[],[f15]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_148,plain,
% 0.89/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.89/1.00      | v1_partfun1(X0,X1)
% 0.89/1.00      | ~ v1_funct_1(X0)
% 0.89/1.00      | sK0 != X1
% 0.89/1.00      | sK0 != X2
% 0.89/1.00      | sK3 != X0
% 0.89/1.00      | k1_xboole_0 = X2 ),
% 0.89/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_7]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_149,plain,
% 0.89/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 0.89/1.00      | v1_partfun1(sK3,sK0)
% 0.89/1.00      | ~ v1_funct_1(sK3)
% 0.89/1.00      | k1_xboole_0 = sK0 ),
% 0.89/1.00      inference(unflattening,[status(thm)],[c_148]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_6,negated_conjecture,
% 0.89/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 0.89/1.00      inference(cnf_transformation,[],[f24]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_151,plain,
% 0.89/1.00      ( v1_partfun1(sK3,sK0) | k1_xboole_0 = sK0 ),
% 0.89/1.00      inference(global_propositional_subsumption,
% 0.89/1.00                [status(thm)],
% 0.89/1.00                [c_149,c_8,c_6]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_211,plain,
% 0.89/1.00      ( ~ r1_partfun1(X0,X1)
% 0.89/1.00      | ~ r1_partfun1(X2,X1)
% 0.89/1.00      | r1_partfun1(X2,X0)
% 0.89/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 0.89/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 0.89/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 0.89/1.00      | ~ v1_funct_1(X0)
% 0.89/1.00      | ~ v1_funct_1(X2)
% 0.89/1.00      | ~ v1_funct_1(X1)
% 0.89/1.00      | sK0 != X3
% 0.89/1.00      | sK0 = k1_xboole_0
% 0.89/1.00      | sK3 != X1 ),
% 0.89/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_151]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_212,plain,
% 0.89/1.00      ( r1_partfun1(X0,X1)
% 0.89/1.00      | ~ r1_partfun1(X0,sK3)
% 0.89/1.00      | ~ r1_partfun1(X1,sK3)
% 0.89/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
% 0.89/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
% 0.89/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
% 0.89/1.00      | ~ v1_funct_1(X1)
% 0.89/1.00      | ~ v1_funct_1(X0)
% 0.89/1.00      | ~ v1_funct_1(sK3)
% 0.89/1.00      | sK0 = k1_xboole_0 ),
% 0.89/1.00      inference(unflattening,[status(thm)],[c_211]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_216,plain,
% 0.89/1.00      ( ~ v1_funct_1(X0)
% 0.89/1.00      | ~ v1_funct_1(X1)
% 0.89/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
% 0.89/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
% 0.89/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
% 0.89/1.00      | ~ r1_partfun1(X1,sK3)
% 0.89/1.00      | ~ r1_partfun1(X0,sK3)
% 0.89/1.00      | r1_partfun1(X0,X1)
% 0.89/1.00      | sK0 = k1_xboole_0 ),
% 0.89/1.00      inference(global_propositional_subsumption,
% 0.89/1.00                [status(thm)],
% 0.89/1.00                [c_212,c_8]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_217,plain,
% 0.89/1.00      ( r1_partfun1(X0,X1)
% 0.89/1.00      | ~ r1_partfun1(X0,sK3)
% 0.89/1.00      | ~ r1_partfun1(X1,sK3)
% 0.89/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
% 0.89/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
% 0.89/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
% 0.89/1.00      | ~ v1_funct_1(X0)
% 0.89/1.00      | ~ v1_funct_1(X1)
% 0.89/1.00      | sK0 = k1_xboole_0 ),
% 0.89/1.00      inference(renaming,[status(thm)],[c_216]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_345,plain,
% 0.89/1.00      ( r1_partfun1(X0_40,X1_40)
% 0.89/1.00      | ~ r1_partfun1(X0_40,sK3)
% 0.89/1.00      | ~ r1_partfun1(X1_40,sK3)
% 0.89/1.00      | ~ m1_subset_1(X0_40,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_43)))
% 0.89/1.00      | ~ m1_subset_1(X1_40,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_43)))
% 0.89/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_43)))
% 0.89/1.00      | ~ v1_funct_1(X0_40)
% 0.89/1.00      | ~ v1_funct_1(X1_40)
% 0.89/1.00      | sK0 = k1_xboole_0 ),
% 0.89/1.00      inference(subtyping,[status(esa)],[c_217]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_658,plain,
% 0.89/1.00      ( ~ r1_partfun1(X0_40,sK3)
% 0.89/1.00      | r1_partfun1(sK1,X0_40)
% 0.89/1.00      | ~ r1_partfun1(sK1,sK3)
% 0.89/1.00      | ~ m1_subset_1(X0_40,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_43)))
% 0.89/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_43)))
% 0.89/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_43)))
% 0.89/1.00      | ~ v1_funct_1(X0_40)
% 0.89/1.00      | ~ v1_funct_1(sK1)
% 0.89/1.00      | sK0 = k1_xboole_0 ),
% 0.89/1.00      inference(instantiation,[status(thm)],[c_345]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_697,plain,
% 0.89/1.00      ( ~ r1_partfun1(sK2,sK3)
% 0.89/1.00      | ~ r1_partfun1(sK1,sK3)
% 0.89/1.00      | r1_partfun1(sK1,sK2)
% 0.89/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_43)))
% 0.89/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_43)))
% 0.89/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_43)))
% 0.89/1.00      | ~ v1_funct_1(sK2)
% 0.89/1.00      | ~ v1_funct_1(sK1)
% 0.89/1.00      | sK0 = k1_xboole_0 ),
% 0.89/1.00      inference(instantiation,[status(thm)],[c_658]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_699,plain,
% 0.89/1.00      ( ~ r1_partfun1(sK2,sK3)
% 0.89/1.00      | ~ r1_partfun1(sK1,sK3)
% 0.89/1.00      | r1_partfun1(sK1,sK2)
% 0.89/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 0.89/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 0.89/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 0.89/1.00      | ~ v1_funct_1(sK2)
% 0.89/1.00      | ~ v1_funct_1(sK1)
% 0.89/1.00      | sK0 = k1_xboole_0 ),
% 0.89/1.00      inference(instantiation,[status(thm)],[c_697]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_357,plain,
% 0.89/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 0.89/1.00      | sP0_iProver_split
% 0.89/1.00      | sK0 != k1_xboole_0 ),
% 0.89/1.00      inference(splitting,
% 0.89/1.00                [splitting(split),new_symbols(definition,[])],
% 0.89/1.00                [c_346]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_372,plain,
% 0.89/1.00      ( sK0 = sK0 ),
% 0.89/1.00      inference(instantiation,[status(thm)],[c_361]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_3,negated_conjecture,
% 0.89/1.00      ( ~ r1_partfun1(sK1,sK2) ),
% 0.89/1.00      inference(cnf_transformation,[],[f27]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_4,negated_conjecture,
% 0.89/1.00      ( r1_partfun1(sK2,sK3) ),
% 0.89/1.00      inference(cnf_transformation,[],[f26]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_5,negated_conjecture,
% 0.89/1.00      ( r1_partfun1(sK1,sK3) ),
% 0.89/1.00      inference(cnf_transformation,[],[f25]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_9,negated_conjecture,
% 0.89/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 0.89/1.00      inference(cnf_transformation,[],[f21]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_10,negated_conjecture,
% 0.89/1.00      ( v1_funct_1(sK2) ),
% 0.89/1.00      inference(cnf_transformation,[],[f20]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_11,negated_conjecture,
% 0.89/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 0.89/1.00      inference(cnf_transformation,[],[f19]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(c_12,negated_conjecture,
% 0.89/1.00      ( v1_funct_1(sK1) ),
% 0.89/1.00      inference(cnf_transformation,[],[f18]) ).
% 0.89/1.00  
% 0.89/1.00  cnf(contradiction,plain,
% 0.89/1.00      ( $false ),
% 0.89/1.00      inference(minisat,
% 0.89/1.00                [status(thm)],
% 0.89/1.00                [c_904,c_895,c_877,c_818,c_799,c_773,c_732,c_733,c_699,
% 0.89/1.00                 c_357,c_372,c_3,c_4,c_5,c_6,c_9,c_10,c_11,c_12]) ).
% 0.89/1.00  
% 0.89/1.00  
% 0.89/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 0.89/1.00  
% 0.89/1.00  ------                               Statistics
% 0.89/1.00  
% 0.89/1.00  ------ General
% 0.89/1.00  
% 0.89/1.00  abstr_ref_over_cycles:                  0
% 0.89/1.00  abstr_ref_under_cycles:                 0
% 0.89/1.00  gc_basic_clause_elim:                   0
% 0.89/1.00  forced_gc_time:                         0
% 0.89/1.00  parsing_time:                           0.012
% 0.89/1.00  unif_index_cands_time:                  0.
% 0.89/1.00  unif_index_add_time:                    0.
% 0.89/1.00  orderings_time:                         0.
% 0.89/1.00  out_proof_time:                         0.012
% 0.89/1.00  total_time:                             0.075
% 0.89/1.00  num_of_symbols:                         45
% 0.89/1.00  num_of_terms:                           756
% 0.89/1.00  
% 0.89/1.00  ------ Preprocessing
% 0.89/1.00  
% 0.89/1.00  num_of_splits:                          1
% 0.89/1.00  num_of_split_atoms:                     1
% 0.89/1.00  num_of_reused_defs:                     0
% 0.89/1.00  num_eq_ax_congr_red:                    5
% 0.89/1.00  num_of_sem_filtered_clauses:            1
% 0.89/1.00  num_of_subtypes:                        4
% 0.89/1.00  monotx_restored_types:                  0
% 0.89/1.00  sat_num_of_epr_types:                   0
% 0.89/1.00  sat_num_of_non_cyclic_types:            0
% 0.89/1.00  sat_guarded_non_collapsed_types:        0
% 0.89/1.00  num_pure_diseq_elim:                    0
% 0.89/1.00  simp_replaced_by:                       0
% 0.89/1.00  res_preprocessed:                       63
% 0.89/1.00  prep_upred:                             0
% 0.89/1.00  prep_unflattend:                        9
% 0.89/1.00  smt_new_axioms:                         0
% 0.89/1.00  pred_elim_cands:                        3
% 0.89/1.00  pred_elim:                              2
% 0.89/1.00  pred_elim_cl:                           2
% 0.89/1.00  pred_elim_cycles:                       4
% 0.89/1.00  merged_defs:                            0
% 0.89/1.00  merged_defs_ncl:                        0
% 0.89/1.00  bin_hyper_res:                          0
% 0.89/1.00  prep_cycles:                            4
% 0.89/1.00  pred_elim_time:                         0.003
% 0.89/1.00  splitting_time:                         0.
% 0.89/1.00  sem_filter_time:                        0.
% 0.89/1.00  monotx_time:                            0.
% 0.89/1.00  subtype_inf_time:                       0.
% 0.89/1.00  
% 0.89/1.00  ------ Problem properties
% 0.89/1.00  
% 0.89/1.00  clauses:                                12
% 0.89/1.00  conjectures:                            9
% 0.89/1.00  epr:                                    6
% 0.89/1.00  horn:                                   11
% 0.89/1.00  ground:                                 10
% 0.89/1.00  unary:                                  9
% 0.89/1.00  binary:                                 0
% 0.89/1.00  lits:                                   30
% 0.89/1.00  lits_eq:                                2
% 0.89/1.00  fd_pure:                                0
% 0.89/1.00  fd_pseudo:                              0
% 0.89/1.00  fd_cond:                                0
% 0.89/1.00  fd_pseudo_cond:                         0
% 0.89/1.00  ac_symbols:                             0
% 0.89/1.00  
% 0.89/1.00  ------ Propositional Solver
% 0.89/1.00  
% 0.89/1.00  prop_solver_calls:                      30
% 0.89/1.00  prop_fast_solver_calls:                 371
% 0.89/1.00  smt_solver_calls:                       0
% 0.89/1.00  smt_fast_solver_calls:                  0
% 0.89/1.00  prop_num_of_clauses:                    175
% 0.89/1.00  prop_preprocess_simplified:             1310
% 0.89/1.00  prop_fo_subsumed:                       15
% 0.89/1.00  prop_solver_time:                       0.
% 0.89/1.00  smt_solver_time:                        0.
% 0.89/1.00  smt_fast_solver_time:                   0.
% 0.89/1.00  prop_fast_solver_time:                  0.
% 0.89/1.00  prop_unsat_core_time:                   0.
% 0.89/1.00  
% 0.89/1.00  ------ QBF
% 0.89/1.00  
% 0.89/1.00  qbf_q_res:                              0
% 0.89/1.00  qbf_num_tautologies:                    0
% 0.89/1.00  qbf_prep_cycles:                        0
% 0.89/1.00  
% 0.89/1.00  ------ BMC1
% 0.89/1.00  
% 0.89/1.00  bmc1_current_bound:                     -1
% 0.89/1.00  bmc1_last_solved_bound:                 -1
% 0.89/1.00  bmc1_unsat_core_size:                   -1
% 0.89/1.00  bmc1_unsat_core_parents_size:           -1
% 0.89/1.00  bmc1_merge_next_fun:                    0
% 0.89/1.00  bmc1_unsat_core_clauses_time:           0.
% 0.89/1.00  
% 0.89/1.00  ------ Instantiation
% 0.89/1.00  
% 0.89/1.00  inst_num_of_clauses:                    60
% 0.89/1.00  inst_num_in_passive:                    1
% 0.89/1.00  inst_num_in_active:                     58
% 0.89/1.00  inst_num_in_unprocessed:                0
% 0.89/1.00  inst_num_of_loops:                      78
% 0.89/1.00  inst_num_of_learning_restarts:          0
% 0.89/1.00  inst_num_moves_active_passive:          10
% 0.89/1.00  inst_lit_activity:                      0
% 0.89/1.00  inst_lit_activity_moves:                0
% 0.89/1.00  inst_num_tautologies:                   0
% 0.89/1.00  inst_num_prop_implied:                  0
% 0.89/1.00  inst_num_existing_simplified:           0
% 0.89/1.00  inst_num_eq_res_simplified:             0
% 0.89/1.00  inst_num_child_elim:                    0
% 0.89/1.00  inst_num_of_dismatching_blockings:      17
% 0.89/1.00  inst_num_of_non_proper_insts:           55
% 0.89/1.00  inst_num_of_duplicates:                 0
% 0.89/1.00  inst_inst_num_from_inst_to_res:         0
% 0.89/1.00  inst_dismatching_checking_time:         0.
% 0.89/1.00  
% 0.89/1.00  ------ Resolution
% 0.89/1.00  
% 0.89/1.00  res_num_of_clauses:                     0
% 0.89/1.00  res_num_in_passive:                     0
% 0.89/1.00  res_num_in_active:                      0
% 0.89/1.00  res_num_of_loops:                       67
% 0.89/1.00  res_forward_subset_subsumed:            20
% 0.89/1.00  res_backward_subset_subsumed:           0
% 0.89/1.00  res_forward_subsumed:                   0
% 0.89/1.00  res_backward_subsumed:                  0
% 0.89/1.00  res_forward_subsumption_resolution:     0
% 0.89/1.00  res_backward_subsumption_resolution:    0
% 0.89/1.00  res_clause_to_clause_subsumption:       15
% 0.89/1.00  res_orphan_elimination:                 0
% 0.89/1.00  res_tautology_del:                      9
% 0.89/1.00  res_num_eq_res_simplified:              0
% 0.89/1.00  res_num_sel_changes:                    0
% 0.89/1.00  res_moves_from_active_to_pass:          0
% 0.89/1.00  
% 0.89/1.00  ------ Superposition
% 0.89/1.00  
% 0.89/1.00  sup_time_total:                         0.
% 0.89/1.00  sup_time_generating:                    0.
% 0.89/1.00  sup_time_sim_full:                      0.
% 0.89/1.00  sup_time_sim_immed:                     0.
% 0.89/1.00  
% 0.89/1.00  sup_num_of_clauses:                     12
% 0.89/1.00  sup_num_in_active:                      11
% 0.89/1.00  sup_num_in_passive:                     1
% 0.89/1.00  sup_num_of_loops:                       14
% 0.89/1.00  sup_fw_superposition:                   0
% 0.89/1.00  sup_bw_superposition:                   0
% 0.89/1.00  sup_immediate_simplified:               0
% 0.89/1.00  sup_given_eliminated:                   0
% 0.89/1.00  comparisons_done:                       0
% 0.89/1.00  comparisons_avoided:                    0
% 0.89/1.00  
% 0.89/1.00  ------ Simplifications
% 0.89/1.00  
% 0.89/1.00  
% 0.89/1.00  sim_fw_subset_subsumed:                 0
% 0.89/1.00  sim_bw_subset_subsumed:                 0
% 0.89/1.00  sim_fw_subsumed:                        0
% 0.89/1.00  sim_bw_subsumed:                        0
% 0.89/1.00  sim_fw_subsumption_res:                 0
% 0.89/1.00  sim_bw_subsumption_res:                 0
% 0.89/1.00  sim_tautology_del:                      0
% 0.89/1.00  sim_eq_tautology_del:                   0
% 0.89/1.00  sim_eq_res_simp:                        0
% 0.89/1.00  sim_fw_demodulated:                     0
% 0.89/1.00  sim_bw_demodulated:                     3
% 0.89/1.00  sim_light_normalised:                   0
% 0.89/1.00  sim_joinable_taut:                      0
% 0.89/1.00  sim_joinable_simp:                      0
% 0.89/1.00  sim_ac_normalised:                      0
% 0.89/1.00  sim_smt_subsumption:                    0
% 0.89/1.00  
%------------------------------------------------------------------------------
