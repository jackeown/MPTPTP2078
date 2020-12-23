%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1037+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:44 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :  139 (4082 expanded)
%              Number of clauses        :   99 (1348 expanded)
%              Number of leaves         :    8 ( 872 expanded)
%              Depth                    :   32
%              Number of atoms          :  660 (27676 expanded)
%              Number of equality atoms :  330 (9009 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ~ ( ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X3,X0,X1)
                & v1_funct_1(X3) )
             => ~ r1_partfun1(X2,X3) )
          & ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ~ ( ! [X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X3,X0,X1)
                  & v1_funct_1(X3) )
               => ~ r1_partfun1(X2,X3) )
            & ( k1_xboole_0 = X1
             => k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( ! [X3] :
            ( ~ r1_partfun1(X2,X3)
            | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            | ~ v1_funct_2(X3,X0,X1)
            | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ! [X3] :
          ( ~ r1_partfun1(sK4,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
          | ~ v1_funct_2(X3,sK2,sK3)
          | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = sK2
        | k1_xboole_0 != sK3 )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ! [X3] :
        ( ~ r1_partfun1(sK4,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
        | ~ v1_funct_2(X3,sK2,sK3)
        | ~ v1_funct_1(X3) )
    & ( k1_xboole_0 = sK2
      | k1_xboole_0 != sK3 )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f10,f17])).

fof(f34,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ~ ( ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X3,X0,X1)
                & v1_funct_1(X3) )
             => ? [X4] :
                  ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                  & r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
          & ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f5])).

fof(f11,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ! [X4] :
            ( k1_funct_1(X2,X4) = k1_funct_1(sK0(X0,X1,X2),X4)
            | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK0(X0,X1,X2),X0,X1)
        & v1_funct_1(sK0(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X4] :
            ( k1_funct_1(X2,X4) = k1_funct_1(sK0(X0,X1,X2),X4)
            | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK0(X0,X1,X2),X0,X1)
        & v1_funct_1(sK0(X0,X1,X2)) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f11])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(sK0(X0,X1,X2),X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ( k1_xboole_0 = X1
             => k1_xboole_0 = X0 )
           => ( r1_partfun1(X2,X3)
            <=> ! [X4] :
                  ( r2_hidden(X4,k1_relset_1(X0,X1,X2))
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r1_partfun1(X2,X3)
          <=> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r1_partfun1(X2,X3)
          <=> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r1_partfun1(X2,X3)
              | ? [X4] :
                  ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                  & r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
            & ( ! [X4] :
                  ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                  | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
              | ~ r1_partfun1(X2,X3) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r1_partfun1(X2,X3)
              | ? [X4] :
                  ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                  & r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
            & ( ! [X5] :
                  ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                  | ~ r2_hidden(X5,k1_relset_1(X0,X1,X2)) )
              | ~ r1_partfun1(X2,X3) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(rectify,[],[f13])).

fof(f15,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
     => ( k1_funct_1(X2,sK1(X0,X1,X2,X3)) != k1_funct_1(X3,sK1(X0,X1,X2,X3))
        & r2_hidden(sK1(X0,X1,X2,X3),k1_relset_1(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r1_partfun1(X2,X3)
              | ( k1_funct_1(X2,sK1(X0,X1,X2,X3)) != k1_funct_1(X3,sK1(X0,X1,X2,X3))
                & r2_hidden(sK1(X0,X1,X2,X3),k1_relset_1(X0,X1,X2)) ) )
            & ( ! [X5] :
                  ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                  | ~ r2_hidden(X5,k1_relset_1(X0,X1,X2)) )
              | ~ r1_partfun1(X2,X3) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f15])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | r2_hidden(sK1(X0,X1,X2,X3),k1_relset_1(X0,X1,X2))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( k1_funct_1(X2,X4) = k1_funct_1(sK0(X0,X1,X2),X4)
      | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f33,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f18])).

fof(f36,plain,(
    ! [X3] :
      ( ~ r1_partfun1(sK4,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      | ~ v1_funct_2(X3,sK2,sK3)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(sK0(X0,X1,X2))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | k1_funct_1(X2,sK1(X0,X1,X2,X3)) != k1_funct_1(X3,sK1(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f35,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f18])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X2,X1] :
      ( m1_subset_1(sK0(k1_xboole_0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f24])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | r2_hidden(sK1(X0,X1,X2,X3),k1_relset_1(X0,X1,X2))
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X2,X3,X1] :
      ( r1_partfun1(X2,X3)
      | r2_hidden(sK1(k1_xboole_0,X1,X2,X3),k1_relset_1(k1_xboole_0,X1,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f30])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( k1_funct_1(X2,X4) = k1_funct_1(sK0(X0,X1,X2),X4)
      | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2))
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X4,X2,X1] :
      ( k1_funct_1(X2,X4) = k1_funct_1(sK0(k1_xboole_0,X1,X2),X4)
      | ~ r2_hidden(X4,k1_relset_1(k1_xboole_0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f26])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(sK0(X0,X1,X2))
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f40,plain,(
    ! [X2,X1] :
      ( v1_funct_1(sK0(k1_xboole_0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f20])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(sK0(X0,X1,X2),X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X2,X1] :
      ( v1_funct_2(sK0(k1_xboole_0,X1,X2),k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f22])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | k1_funct_1(X2,sK1(X0,X1,X2,X3)) != k1_funct_1(X3,sK1(X0,X1,X2,X3))
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f41,plain,(
    ! [X2,X3,X1] :
      ( r1_partfun1(X2,X3)
      | k1_funct_1(X2,sK1(k1_xboole_0,X1,X2,X3)) != k1_funct_1(X3,sK1(k1_xboole_0,X1,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f32])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1747,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5,plain,
    ( v1_funct_2(sK0(X0,X1,X2),X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_1757,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(sK0(X1,X0,X2),X1,X0) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_1759,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | m1_subset_1(sK0(X2,X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X0))) = iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | r1_partfun1(X3,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(sK1(X1,X2,X3,X0),k1_relset_1(X1,X2,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1751,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | r1_partfun1(X3,X1) = iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r2_hidden(sK1(X2,X0,X3,X1),k1_relset_1(X2,X0,X3)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | k1_funct_1(sK0(X1,X2,X0),X3) = k1_funct_1(X0,X3)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_1761,plain,
    ( k1_funct_1(sK0(X0,X1,X2),X3) = k1_funct_1(X2,X3)
    | k1_xboole_0 = X1
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(X3,k1_relset_1(X0,X1,X2)) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3132,plain,
    ( k1_funct_1(sK0(sK2,sK3,sK4),X0) = k1_funct_1(sK4,X0)
    | sK3 = k1_xboole_0
    | r2_hidden(X0,k1_relset_1(sK2,sK3,sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1747,c_1761])).

cnf(c_17,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_18,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3374,plain,
    ( r2_hidden(X0,k1_relset_1(sK2,sK3,sK4)) != iProver_top
    | sK3 = k1_xboole_0
    | k1_funct_1(sK0(sK2,sK3,sK4),X0) = k1_funct_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3132,c_18])).

cnf(c_3375,plain,
    ( k1_funct_1(sK0(sK2,sK3,sK4),X0) = k1_funct_1(sK4,X0)
    | sK3 = k1_xboole_0
    | r2_hidden(X0,k1_relset_1(sK2,sK3,sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3374])).

cnf(c_3383,plain,
    ( k1_funct_1(sK0(sK2,sK3,sK4),sK1(sK2,sK3,sK4,X0)) = k1_funct_1(sK4,sK1(sK2,sK3,sK4,X0))
    | sK3 = k1_xboole_0
    | v1_funct_2(X0,sK2,sK3) != iProver_top
    | r1_partfun1(sK4,X0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1751,c_3375])).

cnf(c_19,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_14,negated_conjecture,
    ( ~ v1_funct_2(X0,sK2,sK3)
    | ~ r1_partfun1(sK4,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_20,plain,
    ( v1_funct_2(X0,sK2,sK3) != iProver_top
    | r1_partfun1(sK4,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3388,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_2(X0,sK2,sK3) != iProver_top
    | sK3 = k1_xboole_0
    | k1_funct_1(sK0(sK2,sK3,sK4),sK1(sK2,sK3,sK4,X0)) = k1_funct_1(sK4,sK1(sK2,sK3,sK4,X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3383,c_18,c_19,c_20])).

cnf(c_3389,plain,
    ( k1_funct_1(sK0(sK2,sK3,sK4),sK1(sK2,sK3,sK4,X0)) = k1_funct_1(sK4,sK1(sK2,sK3,sK4,X0))
    | sK3 = k1_xboole_0
    | v1_funct_2(X0,sK2,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3388])).

cnf(c_3400,plain,
    ( k1_funct_1(sK0(sK2,sK3,sK4),sK1(sK2,sK3,sK4,sK0(sK2,sK3,X0))) = k1_funct_1(sK4,sK1(sK2,sK3,sK4,sK0(sK2,sK3,X0)))
    | sK3 = k1_xboole_0
    | v1_funct_2(sK0(sK2,sK3,X0),sK2,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK0(sK2,sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1759,c_3389])).

cnf(c_3680,plain,
    ( k1_funct_1(sK0(sK2,sK3,sK4),sK1(sK2,sK3,sK4,sK0(sK2,sK3,X0))) = k1_funct_1(sK4,sK1(sK2,sK3,sK4,sK0(sK2,sK3,X0)))
    | sK3 = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK0(sK2,sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1757,c_3400])).

cnf(c_3720,plain,
    ( k1_funct_1(sK0(sK2,sK3,sK4),sK1(sK2,sK3,sK4,sK0(sK2,sK3,sK4))) = k1_funct_1(sK4,sK1(sK2,sK3,sK4,sK0(sK2,sK3,sK4)))
    | sK3 = k1_xboole_0
    | v1_funct_1(sK0(sK2,sK3,sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1747,c_3680])).

cnf(c_2011,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK3)))
    | m1_subset_1(sK0(X1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,sK3)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2154,plain,
    ( m1_subset_1(sK0(X0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X0,sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK3)))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_2011])).

cnf(c_2180,plain,
    ( m1_subset_1(sK0(sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_2154])).

cnf(c_2025,plain,
    ( v1_funct_2(sK0(X0,sK3,X1),X0,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3)))
    | ~ v1_funct_1(X1)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2159,plain,
    ( v1_funct_2(sK0(X0,sK3,sK4),X0,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK3)))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_2025])).

cnf(c_2183,plain,
    ( v1_funct_2(sK0(sK2,sK3,sK4),sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_2159])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(sK0(X1,X2,X0))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_1755,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK0(X2,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2253,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_1(sK0(sK2,sK3,sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1747,c_1755])).

cnf(c_2270,plain,
    ( v1_funct_1(sK0(sK2,sK3,sK4))
    | ~ v1_funct_1(sK4)
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2253])).

cnf(c_1418,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2114,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_1418])).

cnf(c_2342,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2114])).

cnf(c_2344,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_2342])).

cnf(c_1417,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2343,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1417])).

cnf(c_1748,plain,
    ( v1_funct_2(X0,sK2,sK3) != iProver_top
    | r1_partfun1(sK4,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2367,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK0(sK2,sK3,X0),sK2,sK3) != iProver_top
    | r1_partfun1(sK4,sK0(sK2,sK3,X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK0(sK2,sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1759,c_1748])).

cnf(c_849,plain,
    ( ~ r1_partfun1(sK4,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | sK0(X2,X3,X1) != X0
    | sK3 != X3
    | sK2 != X2
    | k1_xboole_0 = X3 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_14])).

cnf(c_850,plain,
    ( ~ r1_partfun1(sK4,sK0(sK2,sK3,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ m1_subset_1(sK0(sK2,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK0(sK2,sK3,X0))
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_849])).

cnf(c_866,plain,
    ( ~ r1_partfun1(sK4,sK0(sK2,sK3,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = sK3 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_850,c_7,c_3])).

cnf(c_871,plain,
    ( k1_xboole_0 = sK3
    | r1_partfun1(sK4,sK0(sK2,sK3,X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_866])).

cnf(c_2698,plain,
    ( v1_funct_1(X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | r1_partfun1(sK4,sK0(sK2,sK3,X0)) != iProver_top
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2367,c_871,c_2344,c_2343])).

cnf(c_2699,plain,
    ( sK3 = k1_xboole_0
    | r1_partfun1(sK4,sK0(sK2,sK3,X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2698])).

cnf(c_2708,plain,
    ( sK3 = k1_xboole_0
    | r1_partfun1(sK4,sK0(sK2,sK3,sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1747,c_2699])).

cnf(c_2726,plain,
    ( ~ r1_partfun1(sK4,sK0(sK2,sK3,sK4))
    | ~ v1_funct_1(sK4)
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2708])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | r1_partfun1(X3,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_funct_1(X0,sK1(X1,X2,X3,X0)) != k1_funct_1(X3,sK1(X1,X2,X3,X0))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_2071,plain,
    ( ~ v1_funct_2(X0,X1,sK3)
    | r1_partfun1(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK3)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_funct_1(X0,sK1(X1,sK3,X2,X0)) != k1_funct_1(X2,sK1(X1,sK3,X2,X0))
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2442,plain,
    ( ~ v1_funct_2(sK0(sK2,sK3,sK4),X0,sK3)
    | r1_partfun1(X1,sK0(sK2,sK3,sK4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3)))
    | ~ m1_subset_1(sK0(sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X0,sK3)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(sK0(sK2,sK3,sK4))
    | k1_funct_1(sK0(sK2,sK3,sK4),sK1(X0,sK3,X1,sK0(sK2,sK3,sK4))) != k1_funct_1(X1,sK1(X0,sK3,X1,sK0(sK2,sK3,sK4)))
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_2071])).

cnf(c_3115,plain,
    ( ~ v1_funct_2(sK0(sK2,sK3,sK4),X0,sK3)
    | r1_partfun1(sK4,sK0(sK2,sK3,sK4))
    | ~ m1_subset_1(sK0(sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X0,sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK3)))
    | ~ v1_funct_1(sK0(sK2,sK3,sK4))
    | ~ v1_funct_1(sK4)
    | k1_funct_1(sK0(sK2,sK3,sK4),sK1(X0,sK3,sK4,sK0(sK2,sK3,sK4))) != k1_funct_1(sK4,sK1(X0,sK3,sK4,sK0(sK2,sK3,sK4)))
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_2442])).

cnf(c_3689,plain,
    ( ~ v1_funct_2(sK0(sK2,sK3,sK4),sK2,sK3)
    | r1_partfun1(sK4,sK0(sK2,sK3,sK4))
    | ~ m1_subset_1(sK0(sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK0(sK2,sK3,sK4))
    | ~ v1_funct_1(sK4)
    | k1_funct_1(sK0(sK2,sK3,sK4),sK1(sK2,sK3,sK4,sK0(sK2,sK3,sK4))) != k1_funct_1(sK4,sK1(sK2,sK3,sK4,sK0(sK2,sK3,sK4)))
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_3115])).

cnf(c_3747,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3720,c_17,c_18,c_16,c_2180,c_2183,c_2253,c_2270,c_2344,c_2343,c_2726,c_3689])).

cnf(c_3757,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3747,c_1747])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_3758,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3747,c_15])).

cnf(c_3759,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_3758])).

cnf(c_3762,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3757,c_3759])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | m1_subset_1(sK0(k1_xboole_0,X1,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1760,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
    | m1_subset_1(sK0(k1_xboole_0,X1,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | r1_partfun1(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | r2_hidden(sK1(k1_xboole_0,X1,X2,X0),k1_relset_1(k1_xboole_0,X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1752,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1) != iProver_top
    | r1_partfun1(X2,X0) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
    | r2_hidden(sK1(k1_xboole_0,X1,X2,X0),k1_relset_1(k1_xboole_0,X1,X2)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ r2_hidden(X2,k1_relset_1(k1_xboole_0,X1,X0))
    | ~ v1_funct_1(X0)
    | k1_funct_1(sK0(k1_xboole_0,X1,X0),X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1762,plain,
    ( k1_funct_1(sK0(k1_xboole_0,X0,X1),X2) = k1_funct_1(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | r2_hidden(X2,k1_relset_1(k1_xboole_0,X0,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4136,plain,
    ( k1_funct_1(sK0(k1_xboole_0,k1_xboole_0,sK4),X0) = k1_funct_1(sK4,X0)
    | r2_hidden(X0,k1_relset_1(k1_xboole_0,k1_xboole_0,sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3762,c_1762])).

cnf(c_4259,plain,
    ( r2_hidden(X0,k1_relset_1(k1_xboole_0,k1_xboole_0,sK4)) != iProver_top
    | k1_funct_1(sK0(k1_xboole_0,k1_xboole_0,sK4),X0) = k1_funct_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4136,c_18])).

cnf(c_4260,plain,
    ( k1_funct_1(sK0(k1_xboole_0,k1_xboole_0,sK4),X0) = k1_funct_1(sK4,X0)
    | r2_hidden(X0,k1_relset_1(k1_xboole_0,k1_xboole_0,sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4259])).

cnf(c_4267,plain,
    ( k1_funct_1(sK0(k1_xboole_0,k1_xboole_0,sK4),sK1(k1_xboole_0,k1_xboole_0,sK4,X0)) = k1_funct_1(sK4,sK1(k1_xboole_0,k1_xboole_0,sK4,X0))
    | v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
    | r1_partfun1(sK4,X0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1752,c_4260])).

cnf(c_3756,plain,
    ( v1_funct_2(X0,sK2,k1_xboole_0) != iProver_top
    | r1_partfun1(sK4,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3747,c_1748])).

cnf(c_3765,plain,
    ( v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
    | r1_partfun1(sK4,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3756,c_3759])).

cnf(c_4454,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
    | k1_funct_1(sK0(k1_xboole_0,k1_xboole_0,sK4),sK1(k1_xboole_0,k1_xboole_0,sK4,X0)) = k1_funct_1(sK4,sK1(k1_xboole_0,k1_xboole_0,sK4,X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4267,c_18,c_3762,c_3765])).

cnf(c_4455,plain,
    ( k1_funct_1(sK0(k1_xboole_0,k1_xboole_0,sK4),sK1(k1_xboole_0,k1_xboole_0,sK4,X0)) = k1_funct_1(sK4,sK1(k1_xboole_0,k1_xboole_0,sK4,X0))
    | v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4454])).

cnf(c_4464,plain,
    ( k1_funct_1(sK0(k1_xboole_0,k1_xboole_0,sK4),sK1(k1_xboole_0,k1_xboole_0,sK4,sK0(k1_xboole_0,k1_xboole_0,X0))) = k1_funct_1(sK4,sK1(k1_xboole_0,k1_xboole_0,sK4,sK0(k1_xboole_0,k1_xboole_0,X0)))
    | v1_funct_2(sK0(k1_xboole_0,k1_xboole_0,X0),k1_xboole_0,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK0(k1_xboole_0,k1_xboole_0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1760,c_4455])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(sK0(k1_xboole_0,X1,X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1756,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK0(k1_xboole_0,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4,plain,
    ( v1_funct_2(sK0(k1_xboole_0,X0,X1),k1_xboole_0,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1758,plain,
    ( v1_funct_2(sK0(k1_xboole_0,X0,X1),k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4883,plain,
    ( k1_funct_1(sK0(k1_xboole_0,k1_xboole_0,sK4),sK1(k1_xboole_0,k1_xboole_0,sK4,sK0(k1_xboole_0,k1_xboole_0,X0))) = k1_funct_1(sK4,sK1(k1_xboole_0,k1_xboole_0,sK4,sK0(k1_xboole_0,k1_xboole_0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4464,c_1756,c_1758])).

cnf(c_4889,plain,
    ( k1_funct_1(sK0(k1_xboole_0,k1_xboole_0,sK4),sK1(k1_xboole_0,k1_xboole_0,sK4,sK0(k1_xboole_0,k1_xboole_0,sK4))) = k1_funct_1(sK4,sK1(k1_xboole_0,k1_xboole_0,sK4,sK0(k1_xboole_0,k1_xboole_0,sK4)))
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3762,c_4883])).

cnf(c_4907,plain,
    ( k1_funct_1(sK0(k1_xboole_0,k1_xboole_0,sK4),sK1(k1_xboole_0,k1_xboole_0,sK4,sK0(k1_xboole_0,k1_xboole_0,sK4))) = k1_funct_1(sK4,sK1(k1_xboole_0,k1_xboole_0,sK4,sK0(k1_xboole_0,k1_xboole_0,sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4889,c_18])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | r1_partfun1(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_funct_1(X0,sK1(k1_xboole_0,X1,X2,X0)) != k1_funct_1(X2,sK1(k1_xboole_0,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1754,plain,
    ( k1_funct_1(X0,sK1(k1_xboole_0,X1,X2,X0)) != k1_funct_1(X2,sK1(k1_xboole_0,X1,X2,X0))
    | v1_funct_2(X0,k1_xboole_0,X1) != iProver_top
    | r1_partfun1(X2,X0) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4910,plain,
    ( v1_funct_2(sK0(k1_xboole_0,k1_xboole_0,sK4),k1_xboole_0,k1_xboole_0) != iProver_top
    | r1_partfun1(sK4,sK0(k1_xboole_0,k1_xboole_0,sK4)) = iProver_top
    | m1_subset_1(sK0(k1_xboole_0,k1_xboole_0,sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(sK0(k1_xboole_0,k1_xboole_0,sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4907,c_1754])).

cnf(c_4356,plain,
    ( v1_funct_2(sK0(k1_xboole_0,k1_xboole_0,X0),k1_xboole_0,k1_xboole_0) != iProver_top
    | r1_partfun1(sK4,sK0(k1_xboole_0,k1_xboole_0,X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK0(k1_xboole_0,k1_xboole_0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1760,c_3765])).

cnf(c_4378,plain,
    ( r1_partfun1(sK4,sK0(k1_xboole_0,k1_xboole_0,X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4356,c_1756,c_1758])).

cnf(c_4384,plain,
    ( r1_partfun1(sK4,sK0(k1_xboole_0,k1_xboole_0,sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3762,c_4378])).

cnf(c_1990,plain,
    ( v1_funct_2(sK0(k1_xboole_0,X0,sK4),k1_xboole_0,X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1991,plain,
    ( v1_funct_2(sK0(k1_xboole_0,X0,sK4),k1_xboole_0,X0) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1990])).

cnf(c_1993,plain,
    ( v1_funct_2(sK0(k1_xboole_0,k1_xboole_0,sK4),k1_xboole_0,k1_xboole_0) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1991])).

cnf(c_1985,plain,
    ( m1_subset_1(sK0(k1_xboole_0,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1986,plain,
    ( m1_subset_1(sK0(k1_xboole_0,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1985])).

cnf(c_1988,plain,
    ( m1_subset_1(sK0(k1_xboole_0,k1_xboole_0,sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1986])).

cnf(c_1980,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | v1_funct_1(sK0(k1_xboole_0,X0,sK4))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1981,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | v1_funct_1(sK0(k1_xboole_0,X0,sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1980])).

cnf(c_1983,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(sK0(k1_xboole_0,k1_xboole_0,sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1981])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4910,c_4384,c_3762,c_1993,c_1988,c_1983,c_18])).


%------------------------------------------------------------------------------
