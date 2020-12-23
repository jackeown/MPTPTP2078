%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1036+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:43 EST 2020

% Result     : Theorem 1.41s
% Output     : CNFRefutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :  168 (7216 expanded)
%              Number of clauses        :  133 (1464 expanded)
%              Number of leaves         :   16 (1916 expanded)
%              Depth                    :   35
%              Number of atoms          :  811 (63753 expanded)
%              Number of equality atoms :  331 (13723 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   22 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f5,plain,(
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
    inference(flattening,[],[f4])).

fof(f8,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f9,plain,(
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
    inference(rectify,[],[f8])).

fof(f10,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
     => ( k1_funct_1(X2,sK0(X0,X1,X2,X3)) != k1_funct_1(X3,sK0(X0,X1,X2,X3))
        & r2_hidden(sK0(X0,X1,X2,X3),k1_relset_1(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r1_partfun1(X2,X3)
              | ( k1_funct_1(X2,sK0(X0,X1,X2,X3)) != k1_funct_1(X3,sK0(X0,X1,X2,X3))
                & r2_hidden(sK0(X0,X1,X2,X3),k1_relset_1(X0,X1,X2)) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).

fof(f19,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
      | ~ r2_hidden(X5,k1_relset_1(X0,X1,X2))
      | ~ r1_partfun1(X2,X3)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r1_partfun1(X1,X2)
          <=> ! [X3] :
                ( r2_hidden(X3,k1_relset_1(X0,X0,X1))
               => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r1_partfun1(X1,X2)
            <=> ! [X3] :
                  ( r2_hidden(X3,k1_relset_1(X0,X0,X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_partfun1(X1,X2)
          <~> ! [X3] :
                ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                | ~ r2_hidden(X3,k1_relset_1(X0,X0,X1)) ) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_partfun1(X1,X2)
          <~> ! [X3] :
                ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                | ~ r2_hidden(X3,k1_relset_1(X0,X0,X1)) ) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
                & r2_hidden(X3,k1_relset_1(X0,X0,X1)) )
            | ~ r1_partfun1(X1,X2) )
          & ( ! [X3] :
                ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                | ~ r2_hidden(X3,k1_relset_1(X0,X0,X1)) )
            | r1_partfun1(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
                & r2_hidden(X3,k1_relset_1(X0,X0,X1)) )
            | ~ r1_partfun1(X1,X2) )
          & ( ! [X3] :
                ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                | ~ r2_hidden(X3,k1_relset_1(X0,X0,X1)) )
            | r1_partfun1(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
                & r2_hidden(X3,k1_relset_1(X0,X0,X1)) )
            | ~ r1_partfun1(X1,X2) )
          & ( ! [X4] :
                ( k1_funct_1(X1,X4) = k1_funct_1(X2,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X0,X1)) )
            | r1_partfun1(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(rectify,[],[f13])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
          & r2_hidden(X3,k1_relset_1(X0,X0,X1)) )
     => ( k1_funct_1(X1,sK4) != k1_funct_1(X2,sK4)
        & r2_hidden(sK4,k1_relset_1(X0,X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
                & r2_hidden(X3,k1_relset_1(X0,X0,X1)) )
            | ~ r1_partfun1(X1,X2) )
          & ( ! [X4] :
                ( k1_funct_1(X1,X4) = k1_funct_1(X2,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X0,X1)) )
            | r1_partfun1(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
     => ( ( ? [X3] :
              ( k1_funct_1(sK3,X3) != k1_funct_1(X1,X3)
              & r2_hidden(X3,k1_relset_1(X0,X0,X1)) )
          | ~ r1_partfun1(X1,sK3) )
        & ( ! [X4] :
              ( k1_funct_1(sK3,X4) = k1_funct_1(X1,X4)
              | ~ r2_hidden(X4,k1_relset_1(X0,X0,X1)) )
          | r1_partfun1(X1,sK3) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(sK3,X0,X0)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ? [X3] :
                  ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
                  & r2_hidden(X3,k1_relset_1(X0,X0,X1)) )
              | ~ r1_partfun1(X1,X2) )
            & ( ! [X4] :
                  ( k1_funct_1(X1,X4) = k1_funct_1(X2,X4)
                  | ~ r2_hidden(X4,k1_relset_1(X0,X0,X1)) )
              | r1_partfun1(X1,X2) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ( ? [X3] :
                ( k1_funct_1(sK2,X3) != k1_funct_1(X2,X3)
                & r2_hidden(X3,k1_relset_1(sK1,sK1,sK2)) )
            | ~ r1_partfun1(sK2,X2) )
          & ( ! [X4] :
                ( k1_funct_1(sK2,X4) = k1_funct_1(X2,X4)
                | ~ r2_hidden(X4,k1_relset_1(sK1,sK1,sK2)) )
            | r1_partfun1(sK2,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
          & v1_funct_2(X2,sK1,sK1)
          & v1_funct_1(X2) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ( ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
        & r2_hidden(sK4,k1_relset_1(sK1,sK1,sK2)) )
      | ~ r1_partfun1(sK2,sK3) )
    & ( ! [X4] :
          ( k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
          | ~ r2_hidden(X4,k1_relset_1(sK1,sK1,sK2)) )
      | r1_partfun1(sK2,sK3) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    & v1_funct_2(sK3,sK1,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f14,f17,f16,f15])).

fof(f28,plain,(
    v1_funct_2(sK3,sK1,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f27,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f29,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f25,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f26,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f30,plain,(
    ! [X4] :
      ( k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
      | ~ r2_hidden(X4,k1_relset_1(sK1,sK1,sK2))
      | r1_partfun1(sK2,sK3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | r2_hidden(sK0(X0,X1,X2,X3),k1_relset_1(X0,X1,X2))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f31,plain,
    ( r2_hidden(sK4,k1_relset_1(sK1,sK1,sK2))
    | ~ r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | k1_funct_1(X2,sK0(X0,X1,X2,X3)) != k1_funct_1(X3,sK0(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f32,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
    | ~ r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | k1_funct_1(X2,sK0(X0,X1,X2,X3)) != k1_funct_1(X3,sK0(X0,X1,X2,X3))
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X2,X3,X1] :
      ( r1_partfun1(X2,X3)
      | k1_funct_1(X2,sK0(k1_xboole_0,X1,X2,X3)) != k1_funct_1(X3,sK0(k1_xboole_0,X1,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f24])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | r2_hidden(sK0(X0,X1,X2,X3),k1_relset_1(X0,X1,X2))
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X2,X3,X1] :
      ( r1_partfun1(X2,X3)
      | r2_hidden(sK0(k1_xboole_0,X1,X2,X3),k1_relset_1(k1_xboole_0,X1,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f22])).

fof(f20,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
      | ~ r2_hidden(X5,k1_relset_1(X0,X1,X2))
      | ~ r1_partfun1(X2,X3)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X2,X5,X3,X1] :
      ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
      | ~ r2_hidden(X5,k1_relset_1(k1_xboole_0,X1,X2))
      | ~ r1_partfun1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f20])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X3,k1_relset_1(X1,X2,X4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_partfun1(X4,X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X4)
    | k1_funct_1(X0,X3) = k1_funct_1(X4,X3)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_10,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_248,plain,
    ( ~ r2_hidden(X0,k1_relset_1(X1,X2,X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_partfun1(X3,X4)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X3)
    | k1_funct_1(X3,X0) = k1_funct_1(X4,X0)
    | sK1 != X1
    | sK1 != X2
    | sK3 != X4
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_10])).

cnf(c_249,plain,
    ( ~ r2_hidden(X0,k1_relset_1(sK1,sK1,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ r1_partfun1(X1,sK3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(sK3)
    | k1_funct_1(X1,X0) = k1_funct_1(sK3,X0)
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_248])).

cnf(c_11,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_9,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_253,plain,
    ( ~ v1_funct_1(X1)
    | ~ r1_partfun1(X1,sK3)
    | ~ r2_hidden(X0,k1_relset_1(sK1,sK1,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k1_funct_1(X1,X0) = k1_funct_1(sK3,X0)
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_249,c_11,c_9])).

cnf(c_254,plain,
    ( ~ r2_hidden(X0,k1_relset_1(sK1,sK1,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ r1_partfun1(X1,sK3)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X1,X0) = k1_funct_1(sK3,X0)
    | k1_xboole_0 = sK1 ),
    inference(renaming,[status(thm)],[c_253])).

cnf(c_13,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_377,plain,
    ( ~ r2_hidden(X0,k1_relset_1(sK1,sK1,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ r1_partfun1(X1,sK3)
    | k1_funct_1(X1,X0) = k1_funct_1(sK3,X0)
    | sK1 = k1_xboole_0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_254,c_13])).

cnf(c_378,plain,
    ( ~ r2_hidden(X0,k1_relset_1(sK1,sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ r1_partfun1(sK2,sK3)
    | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)
    | sK1 = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_377])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_8,negated_conjecture,
    ( ~ r2_hidden(X0,k1_relset_1(sK1,sK1,sK2))
    | r1_partfun1(sK2,sK3)
    | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_382,plain,
    ( ~ r2_hidden(X0,k1_relset_1(sK1,sK1,sK2))
    | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_378,c_12,c_8])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | r2_hidden(sK0(X1,X2,X3,X0),k1_relset_1(X1,X2,X3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_partfun1(X3,X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_278,plain,
    ( r2_hidden(sK0(X0,X1,X2,X3),k1_relset_1(X0,X1,X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | r1_partfun1(X2,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | sK1 != X0
    | sK1 != X1
    | sK3 != X3
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_10])).

cnf(c_279,plain,
    ( r2_hidden(sK0(sK1,sK1,X0,sK3),k1_relset_1(sK1,sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | r1_partfun1(X0,sK3)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_278])).

cnf(c_283,plain,
    ( ~ v1_funct_1(X0)
    | r1_partfun1(X0,sK3)
    | r2_hidden(sK0(sK1,sK1,X0,sK3),k1_relset_1(sK1,sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_279,c_11,c_9])).

cnf(c_284,plain,
    ( r2_hidden(sK0(sK1,sK1,X0,sK3),k1_relset_1(sK1,sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | r1_partfun1(X0,sK3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = sK1 ),
    inference(renaming,[status(thm)],[c_283])).

cnf(c_505,plain,
    ( r2_hidden(sK0(sK1,sK1,X0,sK3),k1_relset_1(sK1,sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | r1_partfun1(X0,sK3)
    | sK1 = k1_xboole_0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_284,c_13])).

cnf(c_506,plain,
    ( r2_hidden(sK0(sK1,sK1,sK2,sK3),k1_relset_1(sK1,sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | r1_partfun1(sK2,sK3)
    | sK1 = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_505])).

cnf(c_508,plain,
    ( r2_hidden(sK0(sK1,sK1,sK2,sK3),k1_relset_1(sK1,sK1,sK2))
    | r1_partfun1(sK2,sK3)
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_506,c_12])).

cnf(c_694,plain,
    ( r1_partfun1(sK2,sK3)
    | sK0(sK1,sK1,sK2,sK3) != X0
    | k1_relset_1(sK1,sK1,sK2) != k1_relset_1(sK1,sK1,sK2)
    | k1_funct_1(sK3,X0) = k1_funct_1(sK2,X0)
    | sK1 = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_382,c_508])).

cnf(c_695,plain,
    ( r1_partfun1(sK2,sK3)
    | k1_funct_1(sK3,sK0(sK1,sK1,sK2,sK3)) = k1_funct_1(sK2,sK0(sK1,sK1,sK2,sK3))
    | sK1 = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_694])).

cnf(c_807,plain,
    ( r1_partfun1(sK2,sK3)
    | k1_funct_1(sK3,sK0(sK1,sK1,sK2,sK3)) = k1_funct_1(sK2,sK0(sK1,sK1,sK2,sK3))
    | sK1 = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_695])).

cnf(c_1041,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK1,sK2,sK3)) = k1_funct_1(sK2,sK0(sK1,sK1,sK2,sK3))
    | sK1 = k1_xboole_0
    | r1_partfun1(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_807])).

cnf(c_7,negated_conjecture,
    ( r2_hidden(sK4,k1_relset_1(sK1,sK1,sK2))
    | ~ r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_609,plain,
    ( ~ r1_partfun1(sK2,sK3)
    | k1_relset_1(sK1,sK1,sK2) != k1_relset_1(sK1,sK1,sK2)
    | k1_funct_1(sK3,X0) = k1_funct_1(sK2,X0)
    | sK1 = k1_xboole_0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_382])).

cnf(c_610,plain,
    ( ~ r1_partfun1(sK2,sK3)
    | k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4)
    | sK1 = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_609])).

cnf(c_811,plain,
    ( ~ r1_partfun1(sK2,sK3)
    | k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4)
    | sK1 = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_610])).

cnf(c_1037,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4)
    | sK1 = k1_xboole_0
    | r1_partfun1(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_811])).

cnf(c_1262,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK1,sK2,sK3)) = k1_funct_1(sK2,sK0(sK1,sK1,sK2,sK3))
    | k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4)
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1041,c_1037])).

cnf(c_1,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_partfun1(X3,X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_funct_1(X0,sK0(X1,X2,X3,X0)) != k1_funct_1(X3,sK0(X1,X2,X3,X0))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_305,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_partfun1(X3,X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_funct_1(X3,sK0(X1,X2,X3,X0)) != k1_funct_1(X0,sK0(X1,X2,X3,X0))
    | sK1 != X1
    | sK1 != X2
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_10])).

cnf(c_306,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | r1_partfun1(X0,sK3)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | k1_funct_1(X0,sK0(sK1,sK1,X0,sK3)) != k1_funct_1(sK3,sK0(sK1,sK1,X0,sK3))
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_305])).

cnf(c_310,plain,
    ( ~ v1_funct_1(X0)
    | r1_partfun1(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k1_funct_1(X0,sK0(sK1,sK1,X0,sK3)) != k1_funct_1(sK3,sK0(sK1,sK1,X0,sK3))
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_306,c_11,c_9])).

cnf(c_311,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | r1_partfun1(X0,sK3)
    | ~ v1_funct_1(X0)
    | k1_funct_1(X0,sK0(sK1,sK1,X0,sK3)) != k1_funct_1(sK3,sK0(sK1,sK1,X0,sK3))
    | k1_xboole_0 = sK1 ),
    inference(renaming,[status(thm)],[c_310])).

cnf(c_488,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | r1_partfun1(X0,sK3)
    | k1_funct_1(X0,sK0(sK1,sK1,X0,sK3)) != k1_funct_1(sK3,sK0(sK1,sK1,X0,sK3))
    | sK1 = k1_xboole_0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_311,c_13])).

cnf(c_489,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | r1_partfun1(sK2,sK3)
    | k1_funct_1(sK2,sK0(sK1,sK1,sK2,sK3)) != k1_funct_1(sK3,sK0(sK1,sK1,sK2,sK3))
    | sK1 = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_488])).

cnf(c_491,plain,
    ( r1_partfun1(sK2,sK3)
    | k1_funct_1(sK2,sK0(sK1,sK1,sK2,sK3)) != k1_funct_1(sK3,sK0(sK1,sK1,sK2,sK3))
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_489,c_12])).

cnf(c_813,plain,
    ( r1_partfun1(sK2,sK3)
    | k1_funct_1(sK2,sK0(sK1,sK1,sK2,sK3)) != k1_funct_1(sK3,sK0(sK1,sK1,sK2,sK3))
    | sK1 = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_491])).

cnf(c_1035,plain,
    ( k1_funct_1(sK2,sK0(sK1,sK1,sK2,sK3)) != k1_funct_1(sK3,sK0(sK1,sK1,sK2,sK3))
    | sK1 = k1_xboole_0
    | r1_partfun1(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_813])).

cnf(c_1266,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4)
    | sK1 = k1_xboole_0
    | r1_partfun1(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1262,c_1035])).

cnf(c_855,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4)
    | sK1 = k1_xboole_0
    | r1_partfun1(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_811])).

cnf(c_1310,plain,
    ( sK1 = k1_xboole_0
    | k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1266,c_855])).

cnf(c_1311,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4)
    | sK1 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_1310])).

cnf(c_6,negated_conjecture,
    ( ~ r1_partfun1(sK2,sK3)
    | k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_818,negated_conjecture,
    ( ~ r1_partfun1(sK2,sK3)
    | k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1030,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
    | r1_partfun1(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_818])).

cnf(c_1314,plain,
    ( sK1 = k1_xboole_0
    | r1_partfun1(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1311,c_1030])).

cnf(c_1343,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK1,sK2,sK3)) = k1_funct_1(sK2,sK0(sK1,sK1,sK2,sK3))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1041,c_1314])).

cnf(c_1346,plain,
    ( sK1 = k1_xboole_0
    | r1_partfun1(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1343,c_1035])).

cnf(c_15,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_18,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_822,plain,
    ( X0_46 = X0_46 ),
    theory(equality)).

cnf(c_844,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_822])).

cnf(c_0,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | r1_partfun1(X2,X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_funct_1(X0,sK0(k1_xboole_0,X1,X2,X0)) != k1_funct_1(X2,sK0(k1_xboole_0,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_218,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | r1_partfun1(X2,X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_funct_1(X2,sK0(k1_xboole_0,X1,X2,X0)) != k1_funct_1(X0,sK0(k1_xboole_0,X1,X2,X0))
    | sK1 != X1
    | sK1 != k1_xboole_0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_10])).

cnf(c_219,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | r1_partfun1(X0,sK3)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | k1_funct_1(X0,sK0(k1_xboole_0,sK1,X0,sK3)) != k1_funct_1(sK3,sK0(k1_xboole_0,sK1,X0,sK3))
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_218])).

cnf(c_223,plain,
    ( ~ v1_funct_1(X0)
    | r1_partfun1(X0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | k1_funct_1(X0,sK0(k1_xboole_0,sK1,X0,sK3)) != k1_funct_1(sK3,sK0(k1_xboole_0,sK1,X0,sK3))
    | sK1 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_219,c_11])).

cnf(c_224,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | r1_partfun1(X0,sK3)
    | ~ v1_funct_1(X0)
    | k1_funct_1(X0,sK0(k1_xboole_0,sK1,X0,sK3)) != k1_funct_1(sK3,sK0(k1_xboole_0,sK1,X0,sK3))
    | sK1 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_223])).

cnf(c_522,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | r1_partfun1(X0,sK3)
    | k1_funct_1(X0,sK0(k1_xboole_0,sK1,X0,sK3)) != k1_funct_1(sK3,sK0(k1_xboole_0,sK1,X0,sK3))
    | sK1 != k1_xboole_0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_224,c_13])).

cnf(c_523,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | r1_partfun1(sK2,sK3)
    | k1_funct_1(sK2,sK0(k1_xboole_0,sK1,sK2,sK3)) != k1_funct_1(sK3,sK0(k1_xboole_0,sK1,sK2,sK3))
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_522])).

cnf(c_812,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | r1_partfun1(sK2,sK3)
    | k1_funct_1(sK2,sK0(k1_xboole_0,sK1,sK2,sK3)) != k1_funct_1(sK3,sK0(k1_xboole_0,sK1,sK2,sK3))
    | sK1 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_523])).

cnf(c_854,plain,
    ( k1_funct_1(sK2,sK0(k1_xboole_0,sK1,sK2,sK3)) != k1_funct_1(sK3,sK0(k1_xboole_0,sK1,sK2,sK3))
    | sK1 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | r1_partfun1(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_812])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | r2_hidden(sK0(k1_xboole_0,X1,X2,X0),k1_relset_1(k1_xboole_0,X1,X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | r1_partfun1(X2,X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_188,plain,
    ( r2_hidden(sK0(k1_xboole_0,X0,X1,X2),k1_relset_1(k1_xboole_0,X0,X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | r1_partfun1(X1,X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | sK1 != X0
    | sK1 != k1_xboole_0
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_10])).

cnf(c_189,plain,
    ( r2_hidden(sK0(k1_xboole_0,sK1,X0,sK3),k1_relset_1(k1_xboole_0,sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | r1_partfun1(X0,sK3)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_188])).

cnf(c_193,plain,
    ( ~ v1_funct_1(X0)
    | r1_partfun1(X0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | r2_hidden(sK0(k1_xboole_0,sK1,X0,sK3),k1_relset_1(k1_xboole_0,sK1,X0))
    | sK1 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_189,c_11])).

cnf(c_194,plain,
    ( r2_hidden(sK0(k1_xboole_0,sK1,X0,sK3),k1_relset_1(k1_xboole_0,sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | r1_partfun1(X0,sK3)
    | ~ v1_funct_1(X0)
    | sK1 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_193])).

cnf(c_541,plain,
    ( r2_hidden(sK0(k1_xboole_0,sK1,X0,sK3),k1_relset_1(k1_xboole_0,sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | r1_partfun1(X0,sK3)
    | sK1 != k1_xboole_0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_194,c_13])).

cnf(c_542,plain,
    ( r2_hidden(sK0(k1_xboole_0,sK1,sK2,sK3),k1_relset_1(k1_xboole_0,sK1,sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | r1_partfun1(sK2,sK3)
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_541])).

cnf(c_711,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | r1_partfun1(sK2,sK3)
    | sK0(k1_xboole_0,sK1,sK2,sK3) != X0
    | k1_relset_1(k1_xboole_0,sK1,sK2) != k1_relset_1(sK1,sK1,sK2)
    | k1_funct_1(sK3,X0) = k1_funct_1(sK2,X0)
    | sK1 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_542])).

cnf(c_712,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | r1_partfun1(sK2,sK3)
    | k1_relset_1(k1_xboole_0,sK1,sK2) != k1_relset_1(sK1,sK1,sK2)
    | k1_funct_1(sK3,sK0(k1_xboole_0,sK1,sK2,sK3)) = k1_funct_1(sK2,sK0(k1_xboole_0,sK1,sK2,sK3))
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_711])).

cnf(c_806,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | r1_partfun1(sK2,sK3)
    | k1_funct_1(sK3,sK0(k1_xboole_0,sK1,sK2,sK3)) = k1_funct_1(sK2,sK0(k1_xboole_0,sK1,sK2,sK3))
    | k1_relset_1(k1_xboole_0,sK1,sK2) != k1_relset_1(sK1,sK1,sK2)
    | sK1 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_712])).

cnf(c_860,plain,
    ( k1_funct_1(sK3,sK0(k1_xboole_0,sK1,sK2,sK3)) = k1_funct_1(sK2,sK0(k1_xboole_0,sK1,sK2,sK3))
    | k1_relset_1(k1_xboole_0,sK1,sK2) != k1_relset_1(sK1,sK1,sK2)
    | sK1 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | r1_partfun1(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_806])).

cnf(c_833,plain,
    ( ~ m1_subset_1(X0_43,X0_44)
    | m1_subset_1(X0_43,X1_44)
    | X1_44 != X0_44 ),
    theory(equality)).

cnf(c_1148,plain,
    ( m1_subset_1(sK3,X0_44)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | X0_44 != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_833])).

cnf(c_1158,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_1148])).

cnf(c_1159,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1158])).

cnf(c_832,plain,
    ( X0_45 != X1_45
    | k1_zfmisc_1(X0_45) = k1_zfmisc_1(X1_45) ),
    theory(equality)).

cnf(c_1166,plain,
    ( X0_45 != k2_zfmisc_1(sK1,sK1)
    | k1_zfmisc_1(X0_45) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_832])).

cnf(c_1198,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK1) != k2_zfmisc_1(sK1,sK1)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_1166])).

cnf(c_831,plain,
    ( X0_46 != X1_46
    | X2_46 != X3_46
    | k2_zfmisc_1(X0_46,X2_46) = k2_zfmisc_1(X1_46,X3_46) ),
    theory(equality)).

cnf(c_1206,plain,
    ( sK1 != sK1
    | k1_xboole_0 != sK1
    | k2_zfmisc_1(k1_xboole_0,sK1) = k2_zfmisc_1(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_831])).

cnf(c_1250,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_822])).

cnf(c_826,plain,
    ( X0_46 != X1_46
    | X2_46 != X1_46
    | X2_46 = X0_46 ),
    theory(equality)).

cnf(c_1270,plain,
    ( X0_46 != X1_46
    | X0_46 = sK1
    | sK1 != X1_46 ),
    inference(instantiation,[status(thm)],[c_826])).

cnf(c_1271,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1270])).

cnf(c_1153,plain,
    ( m1_subset_1(sK2,X0_44)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | X0_44 != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_833])).

cnf(c_1165,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(X0_45))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k1_zfmisc_1(X0_45) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_1153])).

cnf(c_1239,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_1165])).

cnf(c_1316,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_1239])).

cnf(c_1317,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1316])).

cnf(c_834,plain,
    ( k1_relset_1(X0_46,X1_46,X0_43) = k1_relset_1(X2_46,X3_46,X0_43)
    | X0_46 != X2_46
    | X1_46 != X3_46 ),
    theory(equality)).

cnf(c_1330,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK2) = k1_relset_1(sK1,sK1,sK2)
    | sK1 != sK1
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_834])).

cnf(c_828,plain,
    ( X0_48 != X1_48
    | X2_48 != X1_48
    | X2_48 = X0_48 ),
    theory(equality)).

cnf(c_1331,plain,
    ( k1_funct_1(sK3,sK0(k1_xboole_0,sK1,sK2,sK3)) != X0_48
    | k1_funct_1(sK2,sK0(k1_xboole_0,sK1,sK2,sK3)) != X0_48
    | k1_funct_1(sK2,sK0(k1_xboole_0,sK1,sK2,sK3)) = k1_funct_1(sK3,sK0(k1_xboole_0,sK1,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_828])).

cnf(c_1333,plain,
    ( k1_funct_1(sK3,sK0(k1_xboole_0,sK1,sK2,sK3)) != k1_funct_1(sK2,sK0(k1_xboole_0,sK1,sK2,sK3))
    | k1_funct_1(sK2,sK0(k1_xboole_0,sK1,sK2,sK3)) = k1_funct_1(sK3,sK0(k1_xboole_0,sK1,sK2,sK3))
    | k1_funct_1(sK2,sK0(k1_xboole_0,sK1,sK2,sK3)) != k1_funct_1(sK2,sK0(k1_xboole_0,sK1,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1331])).

cnf(c_824,plain,
    ( X0_48 = X0_48 ),
    theory(equality)).

cnf(c_1373,plain,
    ( k1_funct_1(sK2,sK0(k1_xboole_0,sK1,sK2,sK3)) = k1_funct_1(sK2,sK0(k1_xboole_0,sK1,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_824])).

cnf(c_1396,plain,
    ( r1_partfun1(sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1346,c_15,c_18,c_844,c_854,c_860,c_1159,c_1198,c_1206,c_1250,c_1271,c_1317,c_1330,c_1333,c_1373])).

cnf(c_1401,plain,
    ( sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1396,c_1314])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ r2_hidden(X2,k1_relset_1(k1_xboole_0,X1,X3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ r1_partfun1(X3,X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_funct_1(X0,X2) = k1_funct_1(X3,X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_155,plain,
    ( ~ r2_hidden(X0,k1_relset_1(k1_xboole_0,X1,X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ r1_partfun1(X2,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | k1_funct_1(X2,X0) = k1_funct_1(X3,X0)
    | sK1 != X1
    | sK1 != k1_xboole_0
    | sK3 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_10])).

cnf(c_156,plain,
    ( ~ r2_hidden(X0,k1_relset_1(k1_xboole_0,sK1,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ r1_partfun1(X1,sK3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(sK3)
    | k1_funct_1(X1,X0) = k1_funct_1(sK3,X0)
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_155])).

cnf(c_160,plain,
    ( ~ v1_funct_1(X1)
    | ~ r1_partfun1(X1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ r2_hidden(X0,k1_relset_1(k1_xboole_0,sK1,X1))
    | k1_funct_1(X1,X0) = k1_funct_1(sK3,X0)
    | sK1 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_156,c_11])).

cnf(c_161,plain,
    ( ~ r2_hidden(X0,k1_relset_1(k1_xboole_0,sK1,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ r1_partfun1(X1,sK3)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X1,X0) = k1_funct_1(sK3,X0)
    | sK1 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_160])).

cnf(c_398,plain,
    ( ~ r2_hidden(X0,k1_relset_1(k1_xboole_0,sK1,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ r1_partfun1(X1,sK3)
    | k1_funct_1(X1,X0) = k1_funct_1(sK3,X0)
    | sK1 != k1_xboole_0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_161,c_13])).

cnf(c_399,plain,
    ( ~ r2_hidden(X0,k1_relset_1(k1_xboole_0,sK1,sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ r1_partfun1(sK2,sK3)
    | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_398])).

cnf(c_624,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ r1_partfun1(sK2,sK3)
    | k1_relset_1(k1_xboole_0,sK1,sK2) != k1_relset_1(sK1,sK1,sK2)
    | k1_funct_1(sK3,X0) = k1_funct_1(sK2,X0)
    | sK1 != k1_xboole_0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_399])).

cnf(c_625,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ r1_partfun1(sK2,sK3)
    | k1_relset_1(k1_xboole_0,sK1,sK2) != k1_relset_1(sK1,sK1,sK2)
    | k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4)
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_624])).

cnf(c_627,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4)
    | k1_relset_1(k1_xboole_0,sK1,sK2) != k1_relset_1(sK1,sK1,sK2)
    | ~ r1_partfun1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_625,c_610])).

cnf(c_628,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ r1_partfun1(sK2,sK3)
    | k1_relset_1(k1_xboole_0,sK1,sK2) != k1_relset_1(sK1,sK1,sK2)
    | k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4) ),
    inference(renaming,[status(thm)],[c_627])).

cnf(c_810,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ r1_partfun1(sK2,sK3)
    | k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4)
    | k1_relset_1(k1_xboole_0,sK1,sK2) != k1_relset_1(sK1,sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_628])).

cnf(c_1038,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4)
    | k1_relset_1(k1_xboole_0,sK1,sK2) != k1_relset_1(sK1,sK1,sK2)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | r1_partfun1(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_810])).

cnf(c_1408,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4)
    | k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | r1_partfun1(sK2,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1401,c_1038])).

cnf(c_1415,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | r1_partfun1(sK2,sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1408])).

cnf(c_816,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1032,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_816])).

cnf(c_1409,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1401,c_1032])).

cnf(c_817,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1031,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_817])).

cnf(c_1410,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1401,c_1031])).

cnf(c_1420,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4)
    | r1_partfun1(sK2,sK3) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1415,c_1409,c_1410])).

cnf(c_856,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4)
    | k1_relset_1(k1_xboole_0,sK1,sK2) != k1_relset_1(sK1,sK1,sK2)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | r1_partfun1(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_810])).

cnf(c_1496,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1420,c_15,c_18,c_844,c_854,c_856,c_860,c_1159,c_1198,c_1206,c_1250,c_1271,c_1314,c_1317,c_1330,c_1333,c_1346,c_1373])).

cnf(c_1499,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK2,sK4)
    | r1_partfun1(sK2,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1496,c_1030])).

cnf(c_825,plain,
    ( X0_49 = X0_49 ),
    theory(equality)).

cnf(c_847,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_825])).

cnf(c_830,plain,
    ( X0_49 != X1_49
    | k1_funct_1(X0_43,X0_49) = k1_funct_1(X0_43,X1_49) ),
    theory(equality)).

cnf(c_836,plain,
    ( sK4 != sK4
    | k1_funct_1(sK2,sK4) = k1_funct_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_830])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1499,c_1396,c_847,c_836])).


%------------------------------------------------------------------------------
