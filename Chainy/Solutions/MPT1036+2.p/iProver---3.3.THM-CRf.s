%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1036+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:00 EST 2020

% Result     : Theorem 47.29s
% Output     : CNFRefutation 47.29s
% Verified   : 
% Statistics : Number of formulae       :  138 (107566 expanded)
%              Number of clauses        :   86 (21225 expanded)
%              Number of leaves         :    9 (27823 expanded)
%              Depth                    :   46
%              Number of atoms          :  709 (916869 expanded)
%              Number of equality atoms :  386 (229871 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   22 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1536,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1537,negated_conjecture,(
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
    inference(negated_conjecture,[],[f1536])).

fof(f3191,plain,(
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
    inference(ennf_transformation,[],[f1537])).

fof(f3192,plain,(
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
    inference(flattening,[],[f3191])).

fof(f4593,plain,(
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
    inference(nnf_transformation,[],[f3192])).

fof(f4594,plain,(
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
    inference(flattening,[],[f4593])).

fof(f4595,plain,(
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
    inference(rectify,[],[f4594])).

fof(f4598,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
          & r2_hidden(X3,k1_relset_1(X0,X0,X1)) )
     => ( k1_funct_1(X1,sK542) != k1_funct_1(X2,sK542)
        & r2_hidden(sK542,k1_relset_1(X0,X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f4597,plain,(
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
              ( k1_funct_1(sK541,X3) != k1_funct_1(X1,X3)
              & r2_hidden(X3,k1_relset_1(X0,X0,X1)) )
          | ~ r1_partfun1(X1,sK541) )
        & ( ! [X4] :
              ( k1_funct_1(sK541,X4) = k1_funct_1(X1,X4)
              | ~ r2_hidden(X4,k1_relset_1(X0,X0,X1)) )
          | r1_partfun1(X1,sK541) )
        & m1_subset_1(sK541,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(sK541,X0,X0)
        & v1_funct_1(sK541) ) ) ),
    introduced(choice_axiom,[])).

fof(f4596,plain,
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
                ( k1_funct_1(sK540,X3) != k1_funct_1(X2,X3)
                & r2_hidden(X3,k1_relset_1(sK539,sK539,sK540)) )
            | ~ r1_partfun1(sK540,X2) )
          & ( ! [X4] :
                ( k1_funct_1(sK540,X4) = k1_funct_1(X2,X4)
                | ~ r2_hidden(X4,k1_relset_1(sK539,sK539,sK540)) )
            | r1_partfun1(sK540,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK539,sK539)))
          & v1_funct_2(X2,sK539,sK539)
          & v1_funct_1(X2) )
      & m1_subset_1(sK540,k1_zfmisc_1(k2_zfmisc_1(sK539,sK539)))
      & v1_funct_1(sK540) ) ),
    introduced(choice_axiom,[])).

fof(f4599,plain,
    ( ( ( k1_funct_1(sK540,sK542) != k1_funct_1(sK541,sK542)
        & r2_hidden(sK542,k1_relset_1(sK539,sK539,sK540)) )
      | ~ r1_partfun1(sK540,sK541) )
    & ( ! [X4] :
          ( k1_funct_1(sK540,X4) = k1_funct_1(sK541,X4)
          | ~ r2_hidden(X4,k1_relset_1(sK539,sK539,sK540)) )
      | r1_partfun1(sK540,sK541) )
    & m1_subset_1(sK541,k1_zfmisc_1(k2_zfmisc_1(sK539,sK539)))
    & v1_funct_2(sK541,sK539,sK539)
    & v1_funct_1(sK541)
    & m1_subset_1(sK540,k1_zfmisc_1(k2_zfmisc_1(sK539,sK539)))
    & v1_funct_1(sK540) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK539,sK540,sK541,sK542])],[f4595,f4598,f4597,f4596])).

fof(f7542,plain,(
    m1_subset_1(sK541,k1_zfmisc_1(k2_zfmisc_1(sK539,sK539))) ),
    inference(cnf_transformation,[],[f4599])).

fof(f1535,axiom,(
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

fof(f3189,plain,(
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
    inference(ennf_transformation,[],[f1535])).

fof(f3190,plain,(
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
    inference(flattening,[],[f3189])).

fof(f4589,plain,(
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
    inference(nnf_transformation,[],[f3190])).

fof(f4590,plain,(
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
    inference(rectify,[],[f4589])).

fof(f4591,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
     => ( k1_funct_1(X2,sK538(X0,X1,X2,X3)) != k1_funct_1(X3,sK538(X0,X1,X2,X3))
        & r2_hidden(sK538(X0,X1,X2,X3),k1_relset_1(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f4592,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r1_partfun1(X2,X3)
              | ( k1_funct_1(X2,sK538(X0,X1,X2,X3)) != k1_funct_1(X3,sK538(X0,X1,X2,X3))
                & r2_hidden(sK538(X0,X1,X2,X3),k1_relset_1(X0,X1,X2)) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK538])],[f4590,f4591])).

fof(f7534,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | r2_hidden(sK538(X0,X1,X2,X3),k1_relset_1(X0,X1,X2))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f4592])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4648,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f8761,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | r2_hidden(sK538(X0,X1,X2,X3),k1_relset_1(X0,X1,X2))
      | o_0_0_xboole_0 = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f7534,f4648])).

fof(f7539,plain,(
    m1_subset_1(sK540,k1_zfmisc_1(k2_zfmisc_1(sK539,sK539))) ),
    inference(cnf_transformation,[],[f4599])).

fof(f7532,plain,(
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
    inference(cnf_transformation,[],[f4592])).

fof(f8763,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
      | ~ r2_hidden(X5,k1_relset_1(X0,X1,X2))
      | ~ r1_partfun1(X2,X3)
      | o_0_0_xboole_0 = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f7532,f4648])).

fof(f7540,plain,(
    v1_funct_1(sK541) ),
    inference(cnf_transformation,[],[f4599])).

fof(f7541,plain,(
    v1_funct_2(sK541,sK539,sK539) ),
    inference(cnf_transformation,[],[f4599])).

fof(f7538,plain,(
    v1_funct_1(sK540) ),
    inference(cnf_transformation,[],[f4599])).

fof(f7543,plain,(
    ! [X4] :
      ( k1_funct_1(sK540,X4) = k1_funct_1(sK541,X4)
      | ~ r2_hidden(X4,k1_relset_1(sK539,sK539,sK540))
      | r1_partfun1(sK540,sK541) ) ),
    inference(cnf_transformation,[],[f4599])).

fof(f7544,plain,
    ( r2_hidden(sK542,k1_relset_1(sK539,sK539,sK540))
    | ~ r1_partfun1(sK540,sK541) ),
    inference(cnf_transformation,[],[f4599])).

fof(f7536,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | k1_funct_1(X2,sK538(X0,X1,X2,X3)) != k1_funct_1(X3,sK538(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f4592])).

fof(f8759,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | k1_funct_1(X2,sK538(X0,X1,X2,X3)) != k1_funct_1(X3,sK538(X0,X1,X2,X3))
      | o_0_0_xboole_0 = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f7536,f4648])).

fof(f7545,plain,
    ( k1_funct_1(sK540,sK542) != k1_funct_1(sK541,sK542)
    | ~ r1_partfun1(sK540,sK541) ),
    inference(cnf_transformation,[],[f4599])).

fof(f7535,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | r2_hidden(sK538(X0,X1,X2,X3),k1_relset_1(X0,X1,X2))
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f4592])).

fof(f8760,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | r2_hidden(sK538(X0,X1,X2,X3),k1_relset_1(X0,X1,X2))
      | o_0_0_xboole_0 != X0
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f7535,f4648])).

fof(f9173,plain,(
    ! [X2,X3,X1] :
      ( r1_partfun1(X2,X3)
      | r2_hidden(sK538(o_0_0_xboole_0,X1,X2,X3),k1_relset_1(o_0_0_xboole_0,X1,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1)))
      | ~ v1_funct_2(X3,o_0_0_xboole_0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f8760])).

fof(f329,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3528,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f329])).

fof(f3529,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f3528])).

fof(f5104,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f3529])).

fof(f7987,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k2_zfmisc_1(X0,X1)
      | o_0_0_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f5104,f4648,f4648])).

fof(f8901,plain,(
    ! [X1] : o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,X1) ),
    inference(equality_resolution,[],[f7987])).

fof(f376,axiom,(
    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5183,plain,(
    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f376])).

fof(f8035,plain,(
    k1_tarski(o_0_0_xboole_0) = k1_zfmisc_1(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f5183,f4648,f4648])).

fof(f7533,plain,(
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
    inference(cnf_transformation,[],[f4592])).

fof(f8762,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
      | ~ r2_hidden(X5,k1_relset_1(X0,X1,X2))
      | ~ r1_partfun1(X2,X3)
      | o_0_0_xboole_0 != X0
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f7533,f4648])).

fof(f9174,plain,(
    ! [X2,X5,X3,X1] :
      ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
      | ~ r2_hidden(X5,k1_relset_1(o_0_0_xboole_0,X1,X2))
      | ~ r1_partfun1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1)))
      | ~ v1_funct_2(X3,o_0_0_xboole_0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f8762])).

fof(f7537,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | k1_funct_1(X2,sK538(X0,X1,X2,X3)) != k1_funct_1(X3,sK538(X0,X1,X2,X3))
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f4592])).

fof(f8758,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | k1_funct_1(X2,sK538(X0,X1,X2,X3)) != k1_funct_1(X3,sK538(X0,X1,X2,X3))
      | o_0_0_xboole_0 != X0
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f7537,f4648])).

fof(f9172,plain,(
    ! [X2,X3,X1] :
      ( r1_partfun1(X2,X3)
      | k1_funct_1(X2,sK538(o_0_0_xboole_0,X1,X2,X3)) != k1_funct_1(X3,sK538(o_0_0_xboole_0,X1,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1)))
      | ~ v1_funct_2(X3,o_0_0_xboole_0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f8758])).

cnf(c_2876,negated_conjecture,
    ( m1_subset_1(sK541,k1_zfmisc_1(k2_zfmisc_1(sK539,sK539))) ),
    inference(cnf_transformation,[],[f7542])).

cnf(c_87172,plain,
    ( m1_subset_1(sK541,k1_zfmisc_1(k2_zfmisc_1(sK539,sK539))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2876])).

cnf(c_2870,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | r1_partfun1(X3,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(sK538(X1,X2,X3,X0),k1_relset_1(X1,X2,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | o_0_0_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f8761])).

cnf(c_87178,plain,
    ( o_0_0_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | r1_partfun1(X3,X1) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r2_hidden(sK538(X2,X0,X3,X1),k1_relset_1(X2,X0,X3)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2870])).

cnf(c_2879,negated_conjecture,
    ( m1_subset_1(sK540,k1_zfmisc_1(k2_zfmisc_1(sK539,sK539))) ),
    inference(cnf_transformation,[],[f7539])).

cnf(c_87169,plain,
    ( m1_subset_1(sK540,k1_zfmisc_1(k2_zfmisc_1(sK539,sK539))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2879])).

cnf(c_2872,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r1_partfun1(X3,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X4,k1_relset_1(X1,X2,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_funct_1(X0,X4) = k1_funct_1(X3,X4)
    | o_0_0_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f8763])).

cnf(c_87176,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(X2,X1)
    | o_0_0_xboole_0 = X3
    | v1_funct_2(X0,X4,X3) != iProver_top
    | r1_partfun1(X2,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,X3))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X4,X3))) != iProver_top
    | r2_hidden(X1,k1_relset_1(X4,X3,X2)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2872])).

cnf(c_113723,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(sK541,X1)
    | sK539 = o_0_0_xboole_0
    | v1_funct_2(sK541,sK539,sK539) != iProver_top
    | r1_partfun1(X0,sK541) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK539,sK539))) != iProver_top
    | r2_hidden(X1,k1_relset_1(sK539,sK539,X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK541) != iProver_top ),
    inference(superposition,[status(thm)],[c_87172,c_87176])).

cnf(c_2878,negated_conjecture,
    ( v1_funct_1(sK541) ),
    inference(cnf_transformation,[],[f7540])).

cnf(c_3036,plain,
    ( v1_funct_1(sK541) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2878])).

cnf(c_2877,negated_conjecture,
    ( v1_funct_2(sK541,sK539,sK539) ),
    inference(cnf_transformation,[],[f7541])).

cnf(c_3037,plain,
    ( v1_funct_2(sK541,sK539,sK539) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2877])).

cnf(c_113811,plain,
    ( v1_funct_1(X0) != iProver_top
    | r2_hidden(X1,k1_relset_1(sK539,sK539,X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK539,sK539))) != iProver_top
    | r1_partfun1(X0,sK541) != iProver_top
    | k1_funct_1(X0,X1) = k1_funct_1(sK541,X1)
    | sK539 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_113723,c_3036,c_3037])).

cnf(c_113812,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(sK541,X1)
    | sK539 = o_0_0_xboole_0
    | r1_partfun1(X0,sK541) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK539,sK539))) != iProver_top
    | r2_hidden(X1,k1_relset_1(sK539,sK539,X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_113811])).

cnf(c_113824,plain,
    ( k1_funct_1(sK541,X0) = k1_funct_1(sK540,X0)
    | sK539 = o_0_0_xboole_0
    | r1_partfun1(sK540,sK541) != iProver_top
    | r2_hidden(X0,k1_relset_1(sK539,sK539,sK540)) != iProver_top
    | v1_funct_1(sK540) != iProver_top ),
    inference(superposition,[status(thm)],[c_87169,c_113812])).

cnf(c_2880,negated_conjecture,
    ( v1_funct_1(sK540) ),
    inference(cnf_transformation,[],[f7538])).

cnf(c_3034,plain,
    ( v1_funct_1(sK540) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2880])).

cnf(c_113856,plain,
    ( r2_hidden(X0,k1_relset_1(sK539,sK539,sK540)) != iProver_top
    | r1_partfun1(sK540,sK541) != iProver_top
    | sK539 = o_0_0_xboole_0
    | k1_funct_1(sK541,X0) = k1_funct_1(sK540,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_113824,c_3034])).

cnf(c_113857,plain,
    ( k1_funct_1(sK541,X0) = k1_funct_1(sK540,X0)
    | sK539 = o_0_0_xboole_0
    | r1_partfun1(sK540,sK541) != iProver_top
    | r2_hidden(X0,k1_relset_1(sK539,sK539,sK540)) != iProver_top ),
    inference(renaming,[status(thm)],[c_113856])).

cnf(c_113976,plain,
    ( k1_funct_1(sK540,sK538(sK539,sK539,sK540,X0)) = k1_funct_1(sK541,sK538(sK539,sK539,sK540,X0))
    | sK539 = o_0_0_xboole_0
    | v1_funct_2(X0,sK539,sK539) != iProver_top
    | r1_partfun1(sK540,X0) = iProver_top
    | r1_partfun1(sK540,sK541) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK539,sK539))) != iProver_top
    | m1_subset_1(sK540,k1_zfmisc_1(k2_zfmisc_1(sK539,sK539))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK540) != iProver_top ),
    inference(superposition,[status(thm)],[c_87178,c_113857])).

cnf(c_2875,negated_conjecture,
    ( r1_partfun1(sK540,sK541)
    | ~ r2_hidden(X0,k1_relset_1(sK539,sK539,sK540))
    | k1_funct_1(sK540,X0) = k1_funct_1(sK541,X0) ),
    inference(cnf_transformation,[],[f7543])).

cnf(c_87173,plain,
    ( k1_funct_1(sK540,X0) = k1_funct_1(sK541,X0)
    | r1_partfun1(sK540,sK541) = iProver_top
    | r2_hidden(X0,k1_relset_1(sK539,sK539,sK540)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2875])).

cnf(c_113977,plain,
    ( k1_funct_1(sK540,sK538(sK539,sK539,sK540,X0)) = k1_funct_1(sK541,sK538(sK539,sK539,sK540,X0))
    | sK539 = o_0_0_xboole_0
    | v1_funct_2(X0,sK539,sK539) != iProver_top
    | r1_partfun1(sK540,X0) = iProver_top
    | r1_partfun1(sK540,sK541) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK539,sK539))) != iProver_top
    | m1_subset_1(sK540,k1_zfmisc_1(k2_zfmisc_1(sK539,sK539))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK540) != iProver_top ),
    inference(superposition,[status(thm)],[c_87178,c_87173])).

cnf(c_114026,plain,
    ( k1_funct_1(sK540,sK538(sK539,sK539,sK540,X0)) = k1_funct_1(sK541,sK538(sK539,sK539,sK540,X0))
    | sK539 = o_0_0_xboole_0
    | v1_funct_2(X0,sK539,sK539) != iProver_top
    | r1_partfun1(sK540,X0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK539,sK539))) != iProver_top
    | m1_subset_1(sK540,k1_zfmisc_1(k2_zfmisc_1(sK539,sK539))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK540) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_113976,c_113977])).

cnf(c_3035,plain,
    ( m1_subset_1(sK540,k1_zfmisc_1(k2_zfmisc_1(sK539,sK539))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2879])).

cnf(c_114212,plain,
    ( v1_funct_1(X0) != iProver_top
    | k1_funct_1(sK540,sK538(sK539,sK539,sK540,X0)) = k1_funct_1(sK541,sK538(sK539,sK539,sK540,X0))
    | sK539 = o_0_0_xboole_0
    | v1_funct_2(X0,sK539,sK539) != iProver_top
    | r1_partfun1(sK540,X0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK539,sK539))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_114026,c_3034,c_3035])).

cnf(c_114213,plain,
    ( k1_funct_1(sK540,sK538(sK539,sK539,sK540,X0)) = k1_funct_1(sK541,sK538(sK539,sK539,sK540,X0))
    | sK539 = o_0_0_xboole_0
    | v1_funct_2(X0,sK539,sK539) != iProver_top
    | r1_partfun1(sK540,X0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK539,sK539))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_114212])).

cnf(c_114224,plain,
    ( k1_funct_1(sK541,sK538(sK539,sK539,sK540,sK541)) = k1_funct_1(sK540,sK538(sK539,sK539,sK540,sK541))
    | sK539 = o_0_0_xboole_0
    | v1_funct_2(sK541,sK539,sK539) != iProver_top
    | r1_partfun1(sK540,sK541) = iProver_top
    | v1_funct_1(sK541) != iProver_top ),
    inference(superposition,[status(thm)],[c_87172,c_114213])).

cnf(c_114249,plain,
    ( r1_partfun1(sK540,sK541) = iProver_top
    | k1_funct_1(sK541,sK538(sK539,sK539,sK540,sK541)) = k1_funct_1(sK540,sK538(sK539,sK539,sK540,sK541))
    | sK539 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_114224,c_3036,c_3037])).

cnf(c_114250,plain,
    ( k1_funct_1(sK541,sK538(sK539,sK539,sK540,sK541)) = k1_funct_1(sK540,sK538(sK539,sK539,sK540,sK541))
    | sK539 = o_0_0_xboole_0
    | r1_partfun1(sK540,sK541) = iProver_top ),
    inference(renaming,[status(thm)],[c_114249])).

cnf(c_2874,negated_conjecture,
    ( ~ r1_partfun1(sK540,sK541)
    | r2_hidden(sK542,k1_relset_1(sK539,sK539,sK540)) ),
    inference(cnf_transformation,[],[f7544])).

cnf(c_87174,plain,
    ( r1_partfun1(sK540,sK541) != iProver_top
    | r2_hidden(sK542,k1_relset_1(sK539,sK539,sK540)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2874])).

cnf(c_113866,plain,
    ( k1_funct_1(sK541,sK542) = k1_funct_1(sK540,sK542)
    | sK539 = o_0_0_xboole_0
    | r1_partfun1(sK540,sK541) != iProver_top ),
    inference(superposition,[status(thm)],[c_87174,c_113857])).

cnf(c_114256,plain,
    ( k1_funct_1(sK541,sK538(sK539,sK539,sK540,sK541)) = k1_funct_1(sK540,sK538(sK539,sK539,sK540,sK541))
    | k1_funct_1(sK541,sK542) = k1_funct_1(sK540,sK542)
    | sK539 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_114250,c_113866])).

cnf(c_2868,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | r1_partfun1(X3,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_funct_1(X0,sK538(X1,X2,X3,X0)) != k1_funct_1(X3,sK538(X1,X2,X3,X0))
    | o_0_0_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f8759])).

cnf(c_87180,plain,
    ( k1_funct_1(X0,sK538(X1,X2,X3,X0)) != k1_funct_1(X3,sK538(X1,X2,X3,X0))
    | o_0_0_xboole_0 = X2
    | v1_funct_2(X0,X1,X2) != iProver_top
    | r1_partfun1(X3,X0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2868])).

cnf(c_114427,plain,
    ( k1_funct_1(sK541,sK542) = k1_funct_1(sK540,sK542)
    | sK539 = o_0_0_xboole_0
    | v1_funct_2(sK541,sK539,sK539) != iProver_top
    | r1_partfun1(sK540,sK541) = iProver_top
    | m1_subset_1(sK541,k1_zfmisc_1(k2_zfmisc_1(sK539,sK539))) != iProver_top
    | m1_subset_1(sK540,k1_zfmisc_1(k2_zfmisc_1(sK539,sK539))) != iProver_top
    | v1_funct_1(sK541) != iProver_top
    | v1_funct_1(sK540) != iProver_top ),
    inference(superposition,[status(thm)],[c_114256,c_87180])).

cnf(c_113867,plain,
    ( ~ r1_partfun1(sK540,sK541)
    | k1_funct_1(sK541,sK542) = k1_funct_1(sK540,sK542)
    | sK539 = o_0_0_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_113866])).

cnf(c_114455,plain,
    ( ~ v1_funct_2(sK541,sK539,sK539)
    | r1_partfun1(sK540,sK541)
    | ~ m1_subset_1(sK541,k1_zfmisc_1(k2_zfmisc_1(sK539,sK539)))
    | ~ m1_subset_1(sK540,k1_zfmisc_1(k2_zfmisc_1(sK539,sK539)))
    | ~ v1_funct_1(sK541)
    | ~ v1_funct_1(sK540)
    | k1_funct_1(sK541,sK542) = k1_funct_1(sK540,sK542)
    | sK539 = o_0_0_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_114427])).

cnf(c_114646,plain,
    ( k1_funct_1(sK541,sK542) = k1_funct_1(sK540,sK542)
    | sK539 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_114427,c_2880,c_2879,c_2878,c_2877,c_2876,c_113867,c_114455])).

cnf(c_2873,negated_conjecture,
    ( ~ r1_partfun1(sK540,sK541)
    | k1_funct_1(sK540,sK542) != k1_funct_1(sK541,sK542) ),
    inference(cnf_transformation,[],[f7545])).

cnf(c_87175,plain,
    ( k1_funct_1(sK540,sK542) != k1_funct_1(sK541,sK542)
    | r1_partfun1(sK540,sK541) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2873])).

cnf(c_114650,plain,
    ( sK539 = o_0_0_xboole_0
    | r1_partfun1(sK540,sK541) != iProver_top ),
    inference(superposition,[status(thm)],[c_114646,c_87175])).

cnf(c_114887,plain,
    ( k1_funct_1(sK541,sK538(sK539,sK539,sK540,sK541)) = k1_funct_1(sK540,sK538(sK539,sK539,sK540,sK541))
    | sK539 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_114250,c_114650])).

cnf(c_114890,plain,
    ( sK539 = o_0_0_xboole_0
    | v1_funct_2(sK541,sK539,sK539) != iProver_top
    | r1_partfun1(sK540,sK541) = iProver_top
    | m1_subset_1(sK541,k1_zfmisc_1(k2_zfmisc_1(sK539,sK539))) != iProver_top
    | m1_subset_1(sK540,k1_zfmisc_1(k2_zfmisc_1(sK539,sK539))) != iProver_top
    | v1_funct_1(sK541) != iProver_top
    | v1_funct_1(sK540) != iProver_top ),
    inference(superposition,[status(thm)],[c_114887,c_87180])).

cnf(c_114651,plain,
    ( ~ r1_partfun1(sK540,sK541)
    | sK539 = o_0_0_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_114650])).

cnf(c_114891,plain,
    ( ~ v1_funct_2(sK541,sK539,sK539)
    | r1_partfun1(sK540,sK541)
    | ~ m1_subset_1(sK541,k1_zfmisc_1(k2_zfmisc_1(sK539,sK539)))
    | ~ m1_subset_1(sK540,k1_zfmisc_1(k2_zfmisc_1(sK539,sK539)))
    | ~ v1_funct_1(sK541)
    | ~ v1_funct_1(sK540)
    | sK539 = o_0_0_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_114890])).

cnf(c_114961,plain,
    ( sK539 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_114890,c_2880,c_2879,c_2878,c_2877,c_2876,c_114651,c_114891])).

cnf(c_87171,plain,
    ( v1_funct_2(sK541,sK539,sK539) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2877])).

cnf(c_114982,plain,
    ( v1_funct_2(sK541,o_0_0_xboole_0,o_0_0_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_114961,c_87171])).

cnf(c_2869,plain,
    ( ~ v1_funct_2(X0,o_0_0_xboole_0,X1)
    | r1_partfun1(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1)))
    | r2_hidden(sK538(o_0_0_xboole_0,X1,X2,X0),k1_relset_1(o_0_0_xboole_0,X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f9173])).

cnf(c_87179,plain,
    ( v1_funct_2(X0,o_0_0_xboole_0,X1) != iProver_top
    | r1_partfun1(X2,X0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1))) != iProver_top
    | r2_hidden(sK538(o_0_0_xboole_0,X1,X2,X0),k1_relset_1(o_0_0_xboole_0,X1,X2)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2869])).

cnf(c_451,plain,
    ( k2_zfmisc_1(o_0_0_xboole_0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f8901])).

cnf(c_530,plain,
    ( k1_zfmisc_1(o_0_0_xboole_0) = k1_tarski(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f8035])).

cnf(c_105406,plain,
    ( v1_funct_2(X0,o_0_0_xboole_0,X1) != iProver_top
    | r1_partfun1(X2,X0) = iProver_top
    | m1_subset_1(X0,k1_tarski(o_0_0_xboole_0)) != iProver_top
    | m1_subset_1(X2,k1_tarski(o_0_0_xboole_0)) != iProver_top
    | r2_hidden(sK538(o_0_0_xboole_0,X1,X2,X0),k1_relset_1(o_0_0_xboole_0,X1,X2)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_87179,c_451,c_530])).

cnf(c_114978,plain,
    ( k1_funct_1(sK541,X0) = k1_funct_1(sK540,X0)
    | r1_partfun1(sK540,sK541) = iProver_top
    | r2_hidden(X0,k1_relset_1(o_0_0_xboole_0,o_0_0_xboole_0,sK540)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_114961,c_87173])).

cnf(c_151312,plain,
    ( k1_funct_1(sK541,sK538(o_0_0_xboole_0,o_0_0_xboole_0,sK540,X0)) = k1_funct_1(sK540,sK538(o_0_0_xboole_0,o_0_0_xboole_0,sK540,X0))
    | v1_funct_2(X0,o_0_0_xboole_0,o_0_0_xboole_0) != iProver_top
    | r1_partfun1(sK540,X0) = iProver_top
    | r1_partfun1(sK540,sK541) = iProver_top
    | m1_subset_1(X0,k1_tarski(o_0_0_xboole_0)) != iProver_top
    | m1_subset_1(sK540,k1_tarski(o_0_0_xboole_0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK540) != iProver_top ),
    inference(superposition,[status(thm)],[c_105406,c_114978])).

cnf(c_114981,plain,
    ( m1_subset_1(sK540,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_114961,c_87169])).

cnf(c_114986,plain,
    ( m1_subset_1(sK540,k1_tarski(o_0_0_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_114981,c_451,c_530])).

cnf(c_152590,plain,
    ( v1_funct_1(X0) != iProver_top
    | k1_funct_1(sK541,sK538(o_0_0_xboole_0,o_0_0_xboole_0,sK540,X0)) = k1_funct_1(sK540,sK538(o_0_0_xboole_0,o_0_0_xboole_0,sK540,X0))
    | v1_funct_2(X0,o_0_0_xboole_0,o_0_0_xboole_0) != iProver_top
    | r1_partfun1(sK540,X0) = iProver_top
    | r1_partfun1(sK540,sK541) = iProver_top
    | m1_subset_1(X0,k1_tarski(o_0_0_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_151312,c_3034,c_114986])).

cnf(c_152591,plain,
    ( k1_funct_1(sK541,sK538(o_0_0_xboole_0,o_0_0_xboole_0,sK540,X0)) = k1_funct_1(sK540,sK538(o_0_0_xboole_0,o_0_0_xboole_0,sK540,X0))
    | v1_funct_2(X0,o_0_0_xboole_0,o_0_0_xboole_0) != iProver_top
    | r1_partfun1(sK540,X0) = iProver_top
    | r1_partfun1(sK540,sK541) = iProver_top
    | m1_subset_1(X0,k1_tarski(o_0_0_xboole_0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_152590])).

cnf(c_152602,plain,
    ( k1_funct_1(sK540,sK538(o_0_0_xboole_0,o_0_0_xboole_0,sK540,sK541)) = k1_funct_1(sK541,sK538(o_0_0_xboole_0,o_0_0_xboole_0,sK540,sK541))
    | r1_partfun1(sK540,sK541) = iProver_top
    | m1_subset_1(sK541,k1_tarski(o_0_0_xboole_0)) != iProver_top
    | v1_funct_1(sK541) != iProver_top ),
    inference(superposition,[status(thm)],[c_114982,c_152591])).

cnf(c_114980,plain,
    ( m1_subset_1(sK541,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_114961,c_87172])).

cnf(c_114989,plain,
    ( m1_subset_1(sK541,k1_tarski(o_0_0_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_114980,c_451,c_530])).

cnf(c_152605,plain,
    ( k1_funct_1(sK540,sK538(o_0_0_xboole_0,o_0_0_xboole_0,sK540,sK541)) = k1_funct_1(sK541,sK538(o_0_0_xboole_0,o_0_0_xboole_0,sK540,sK541))
    | r1_partfun1(sK540,sK541) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_152602,c_3036,c_114989])).

cnf(c_114979,plain,
    ( r1_partfun1(sK540,sK541) != iProver_top
    | r2_hidden(sK542,k1_relset_1(o_0_0_xboole_0,o_0_0_xboole_0,sK540)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_114961,c_87174])).

cnf(c_2871,plain,
    ( ~ v1_funct_2(X0,o_0_0_xboole_0,X1)
    | ~ r1_partfun1(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1)))
    | ~ r2_hidden(X3,k1_relset_1(o_0_0_xboole_0,X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_funct_1(X0,X3) = k1_funct_1(X2,X3) ),
    inference(cnf_transformation,[],[f9174])).

cnf(c_87177,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(X2,X1)
    | v1_funct_2(X0,o_0_0_xboole_0,X3) != iProver_top
    | r1_partfun1(X2,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X3))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X3))) != iProver_top
    | r2_hidden(X1,k1_relset_1(o_0_0_xboole_0,X3,X2)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2871])).

cnf(c_105995,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(X2,X1)
    | v1_funct_2(X2,o_0_0_xboole_0,X3) != iProver_top
    | r1_partfun1(X0,X2) != iProver_top
    | m1_subset_1(X2,k1_tarski(o_0_0_xboole_0)) != iProver_top
    | m1_subset_1(X0,k1_tarski(o_0_0_xboole_0)) != iProver_top
    | r2_hidden(X1,k1_relset_1(o_0_0_xboole_0,X3,X0)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_87177,c_451,c_530])).

cnf(c_157497,plain,
    ( k1_funct_1(X0,sK542) = k1_funct_1(sK540,sK542)
    | v1_funct_2(X0,o_0_0_xboole_0,o_0_0_xboole_0) != iProver_top
    | r1_partfun1(sK540,X0) != iProver_top
    | r1_partfun1(sK540,sK541) != iProver_top
    | m1_subset_1(X0,k1_tarski(o_0_0_xboole_0)) != iProver_top
    | m1_subset_1(sK540,k1_tarski(o_0_0_xboole_0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK540) != iProver_top ),
    inference(superposition,[status(thm)],[c_114979,c_105995])).

cnf(c_157939,plain,
    ( v1_funct_1(X0) != iProver_top
    | k1_funct_1(X0,sK542) = k1_funct_1(sK540,sK542)
    | v1_funct_2(X0,o_0_0_xboole_0,o_0_0_xboole_0) != iProver_top
    | r1_partfun1(sK540,X0) != iProver_top
    | r1_partfun1(sK540,sK541) != iProver_top
    | m1_subset_1(X0,k1_tarski(o_0_0_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_157497,c_3034,c_114986])).

cnf(c_157940,plain,
    ( k1_funct_1(X0,sK542) = k1_funct_1(sK540,sK542)
    | v1_funct_2(X0,o_0_0_xboole_0,o_0_0_xboole_0) != iProver_top
    | r1_partfun1(sK540,X0) != iProver_top
    | r1_partfun1(sK540,sK541) != iProver_top
    | m1_subset_1(X0,k1_tarski(o_0_0_xboole_0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_157939])).

cnf(c_157951,plain,
    ( k1_funct_1(sK541,sK542) = k1_funct_1(sK540,sK542)
    | r1_partfun1(sK540,sK541) != iProver_top
    | m1_subset_1(sK541,k1_tarski(o_0_0_xboole_0)) != iProver_top
    | v1_funct_1(sK541) != iProver_top ),
    inference(superposition,[status(thm)],[c_114982,c_157940])).

cnf(c_158059,plain,
    ( k1_funct_1(sK541,sK542) = k1_funct_1(sK540,sK542)
    | r1_partfun1(sK540,sK541) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_157951,c_3036,c_114989])).

cnf(c_158065,plain,
    ( k1_funct_1(sK541,sK542) = k1_funct_1(sK540,sK542)
    | k1_funct_1(sK540,sK538(o_0_0_xboole_0,o_0_0_xboole_0,sK540,sK541)) = k1_funct_1(sK541,sK538(o_0_0_xboole_0,o_0_0_xboole_0,sK540,sK541)) ),
    inference(superposition,[status(thm)],[c_152605,c_158059])).

cnf(c_2867,plain,
    ( ~ v1_funct_2(X0,o_0_0_xboole_0,X1)
    | r1_partfun1(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_funct_1(X0,sK538(o_0_0_xboole_0,X1,X2,X0)) != k1_funct_1(X2,sK538(o_0_0_xboole_0,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f9172])).

cnf(c_87181,plain,
    ( k1_funct_1(X0,sK538(o_0_0_xboole_0,X1,X2,X0)) != k1_funct_1(X2,sK538(o_0_0_xboole_0,X1,X2,X0))
    | v1_funct_2(X0,o_0_0_xboole_0,X1) != iProver_top
    | r1_partfun1(X2,X0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2867])).

cnf(c_105720,plain,
    ( k1_funct_1(X0,sK538(o_0_0_xboole_0,X1,X0,X2)) != k1_funct_1(X2,sK538(o_0_0_xboole_0,X1,X0,X2))
    | v1_funct_2(X2,o_0_0_xboole_0,X1) != iProver_top
    | r1_partfun1(X0,X2) = iProver_top
    | m1_subset_1(X2,k1_tarski(o_0_0_xboole_0)) != iProver_top
    | m1_subset_1(X0,k1_tarski(o_0_0_xboole_0)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_87181,c_451,c_530])).

cnf(c_158069,plain,
    ( k1_funct_1(sK541,sK542) = k1_funct_1(sK540,sK542)
    | v1_funct_2(sK541,o_0_0_xboole_0,o_0_0_xboole_0) != iProver_top
    | r1_partfun1(sK540,sK541) = iProver_top
    | m1_subset_1(sK541,k1_tarski(o_0_0_xboole_0)) != iProver_top
    | m1_subset_1(sK540,k1_tarski(o_0_0_xboole_0)) != iProver_top
    | v1_funct_1(sK541) != iProver_top
    | v1_funct_1(sK540) != iProver_top ),
    inference(superposition,[status(thm)],[c_158065,c_105720])).

cnf(c_158413,plain,
    ( k1_funct_1(sK541,sK542) = k1_funct_1(sK540,sK542) ),
    inference(global_propositional_subsumption,[status(thm)],[c_158069,c_3034,c_3036,c_114982,c_114986,c_114989,c_157951])).

cnf(c_158416,plain,
    ( k1_funct_1(sK540,sK542) != k1_funct_1(sK540,sK542)
    | r1_partfun1(sK540,sK541) != iProver_top ),
    inference(demodulation,[status(thm)],[c_158413,c_87175])).

cnf(c_158417,plain,
    ( r1_partfun1(sK540,sK541) != iProver_top ),
    inference(theory_normalisation,[status(thm)],[c_158416])).

cnf(c_158937,plain,
    ( k1_funct_1(sK540,sK538(o_0_0_xboole_0,o_0_0_xboole_0,sK540,sK541)) = k1_funct_1(sK541,sK538(o_0_0_xboole_0,o_0_0_xboole_0,sK540,sK541)) ),
    inference(superposition,[status(thm)],[c_152605,c_158417])).

cnf(c_159814,plain,
    ( v1_funct_2(sK541,o_0_0_xboole_0,o_0_0_xboole_0) != iProver_top
    | r1_partfun1(sK540,sK541) = iProver_top
    | m1_subset_1(sK541,k1_tarski(o_0_0_xboole_0)) != iProver_top
    | m1_subset_1(sK540,k1_tarski(o_0_0_xboole_0)) != iProver_top
    | v1_funct_1(sK541) != iProver_top
    | v1_funct_1(sK540) != iProver_top ),
    inference(superposition,[status(thm)],[c_158937,c_105720])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_159814,c_158417,c_114989,c_114986,c_114982,c_3036,c_3034])).

%------------------------------------------------------------------------------
