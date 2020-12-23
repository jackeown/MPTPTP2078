%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1035+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:43 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :  209 (274141 expanded)
%              Number of clauses        :  157 (79844 expanded)
%              Number of leaves         :   15 (62798 expanded)
%              Depth                    :   61
%              Number of atoms          :  854 (2237376 expanded)
%              Number of equality atoms :  490 (761249 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
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

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,conjecture,(
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

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
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
    inference(negated_conjecture,[],[f7])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( r1_partfun1(X2,X3)
          <~> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( r1_partfun1(X2,X3)
          <~> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | ~ r1_partfun1(X2,X3) )
          & ( ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | r1_partfun1(X2,X3) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | ~ r1_partfun1(X2,X3) )
          & ( ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | r1_partfun1(X2,X3) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | ~ r1_partfun1(X2,X3) )
          & ( ! [X5] :
                ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                | ~ r2_hidden(X5,k1_relset_1(X0,X1,X2)) )
            | r1_partfun1(X2,X3) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(rectify,[],[f26])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
     => ( k1_funct_1(X2,sK5) != k1_funct_1(X3,sK5)
        & r2_hidden(sK5,k1_relset_1(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | ~ r1_partfun1(X2,X3) )
          & ( ! [X5] :
                ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                | ~ r2_hidden(X5,k1_relset_1(X0,X1,X2)) )
            | r1_partfun1(X2,X3) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ( ? [X4] :
              ( k1_funct_1(sK4,X4) != k1_funct_1(X2,X4)
              & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
          | ~ r1_partfun1(X2,sK4) )
        & ( ! [X5] :
              ( k1_funct_1(sK4,X5) = k1_funct_1(X2,X5)
              | ~ r2_hidden(X5,k1_relset_1(X0,X1,X2)) )
          | r1_partfun1(X2,sK4) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK4,X0,X1)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ? [X4] :
                  ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                  & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
              | ~ r1_partfun1(X2,X3) )
            & ( ! [X5] :
                  ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                  | ~ r2_hidden(X5,k1_relset_1(X0,X1,X2)) )
              | r1_partfun1(X2,X3) )
            & ( k1_xboole_0 = X0
              | k1_xboole_0 != X1 )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ? [X4] :
                ( k1_funct_1(sK3,X4) != k1_funct_1(X3,X4)
                & r2_hidden(X4,k1_relset_1(sK1,sK2,sK3)) )
            | ~ r1_partfun1(sK3,X3) )
          & ( ! [X5] :
                ( k1_funct_1(sK3,X5) = k1_funct_1(X3,X5)
                | ~ r2_hidden(X5,k1_relset_1(sK1,sK2,sK3)) )
            | r1_partfun1(sK3,X3) )
          & ( k1_xboole_0 = sK1
            | k1_xboole_0 != sK2 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X3,sK1,sK2)
          & v1_funct_1(X3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ( ( k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5)
        & r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3)) )
      | ~ r1_partfun1(sK3,sK4) )
    & ( ! [X5] :
          ( k1_funct_1(sK3,X5) = k1_funct_1(sK4,X5)
          | ~ r2_hidden(X5,k1_relset_1(sK1,sK2,sK3)) )
      | r1_partfun1(sK3,sK4) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK2 )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f27,f30,f29,f28])).

fof(f48,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f49,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
           => ( r1_partfun1(X0,X1)
            <=> ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_partfun1(X0,X1)
          <=> ! [X2] :
                ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                | ~ r2_hidden(X2,k1_relat_1(X0)) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_partfun1(X0,X1)
          <=> ! [X2] :
                ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                | ~ r2_hidden(X2,k1_relat_1(X0)) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_partfun1(X0,X1)
              | ? [X2] :
                  ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
                  & r2_hidden(X2,k1_relat_1(X0)) ) )
            & ( ! [X2] :
                  ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                  | ~ r2_hidden(X2,k1_relat_1(X0)) )
              | ~ r1_partfun1(X0,X1) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_partfun1(X0,X1)
              | ? [X2] :
                  ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
                  & r2_hidden(X2,k1_relat_1(X0)) ) )
            & ( ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
              | ~ r1_partfun1(X0,X1) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
        & r2_hidden(sK0(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_partfun1(X0,X1)
              | ( k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
                & r2_hidden(sK0(X0,X1),k1_relat_1(X0)) ) )
            & ( ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
              | ~ r1_partfun1(X0,X1) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X0,X1)
      | r2_hidden(sK0(X0,X1),k1_relat_1(X0))
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f47,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f46,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r1_partfun1(X0,X1)
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f45,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f51,plain,(
    ! [X5] :
      ( k1_funct_1(sK3,X5) = k1_funct_1(sK4,X5)
      | ~ r2_hidden(X5,k1_relset_1(sK1,sK2,sK3))
      | r1_partfun1(sK3,sK4) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f52,plain,
    ( r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3))
    | ~ r1_partfun1(sK3,sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X0,X1)
      | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f53,plain,
    ( k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5)
    | ~ r1_partfun1(sK3,sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f58,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f34])).

fof(f50,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f31])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f56,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f37])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_18,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_523,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK2 != X2
    | sK1 != X1
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_18])).

cnf(c_524,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_523])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_526,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_524,c_17])).

cnf(c_1291,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(subtyping,[status(esa)],[c_526])).

cnf(c_1300,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1622,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1300])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1305,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | k1_relset_1(X1_47,X2_47,X0_47) = k1_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1618,plain,
    ( k1_relset_1(X0_47,X1_47,X2_47) = k1_relat_1(X2_47)
    | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1305])).

cnf(c_1925,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1622,c_1618])).

cnf(c_2144,plain,
    ( k1_relat_1(sK4) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1291,c_1925])).

cnf(c_10,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | r1_partfun1(X0,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_12,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_267,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
    | r1_partfun1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X1) != X3
    | k1_relat_1(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_12])).

cnf(c_268,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
    | r1_partfun1(X0,X1)
    | ~ m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(k1_relat_1(X1)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_267])).

cnf(c_1295,plain,
    ( r2_hidden(sK0(X0_47,X1_47),k1_relat_1(X0_47))
    | r1_partfun1(X0_47,X1_47)
    | ~ m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(k1_relat_1(X1_47)))
    | ~ v1_funct_1(X1_47)
    | ~ v1_funct_1(X0_47)
    | ~ v1_relat_1(X1_47)
    | ~ v1_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_268])).

cnf(c_1627,plain,
    ( r2_hidden(sK0(X0_47,X1_47),k1_relat_1(X0_47)) = iProver_top
    | r1_partfun1(X0_47,X1_47) = iProver_top
    | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(k1_relat_1(X1_47))) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_funct_1(X1_47) != iProver_top
    | v1_relat_1(X0_47) != iProver_top
    | v1_relat_1(X1_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1295])).

cnf(c_2746,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK0(X0_47,sK4),k1_relat_1(X0_47)) = iProver_top
    | r1_partfun1(X0_47,sK4) = iProver_top
    | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0_47) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2144,c_1627])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_24,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_26,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1307,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | v1_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1769,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1307])).

cnf(c_1770,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1769])).

cnf(c_3010,plain,
    ( v1_relat_1(X0_47) != iProver_top
    | sK2 = k1_xboole_0
    | r2_hidden(sK0(X0_47,sK4),k1_relat_1(X0_47)) = iProver_top
    | r1_partfun1(X0_47,sK4) = iProver_top
    | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(X0_47) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2746,c_24,c_26,c_1770])).

cnf(c_3011,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK0(X0_47,sK4),k1_relat_1(X0_47)) = iProver_top
    | r1_partfun1(X0_47,sK4) = iProver_top
    | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_relat_1(X0_47) != iProver_top ),
    inference(renaming,[status(thm)],[c_3010])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1298,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1624,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1298])).

cnf(c_1926,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1624,c_1618])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1306,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | m1_subset_1(k1_relset_1(X1_47,X2_47,X0_47),k1_zfmisc_1(X1_47)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1617,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47))) != iProver_top
    | m1_subset_1(k1_relset_1(X1_47,X2_47,X0_47),k1_zfmisc_1(X1_47)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1306])).

cnf(c_2173,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1926,c_1617])).

cnf(c_23,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2386,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2173,c_23])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_partfun1(X1,X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X2,X0) = k1_funct_1(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_237,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r1_partfun1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,X0) = k1_funct_1(X2,X0)
    | k1_relat_1(X1) != X3
    | k1_relat_1(X2) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_12])).

cnf(c_238,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r1_partfun1(X1,X2)
    | ~ m1_subset_1(k1_relat_1(X1),k1_zfmisc_1(k1_relat_1(X2)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,X0) = k1_funct_1(X2,X0) ),
    inference(unflattening,[status(thm)],[c_237])).

cnf(c_1296,plain,
    ( ~ r2_hidden(X0_50,k1_relat_1(X0_47))
    | ~ r1_partfun1(X0_47,X1_47)
    | ~ m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(k1_relat_1(X1_47)))
    | ~ v1_funct_1(X1_47)
    | ~ v1_funct_1(X0_47)
    | ~ v1_relat_1(X1_47)
    | ~ v1_relat_1(X0_47)
    | k1_funct_1(X0_47,X0_50) = k1_funct_1(X1_47,X0_50) ),
    inference(subtyping,[status(esa)],[c_238])).

cnf(c_1626,plain,
    ( k1_funct_1(X0_47,X0_50) = k1_funct_1(X1_47,X0_50)
    | r2_hidden(X0_50,k1_relat_1(X0_47)) != iProver_top
    | r1_partfun1(X0_47,X1_47) != iProver_top
    | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(k1_relat_1(X1_47))) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_funct_1(X1_47) != iProver_top
    | v1_relat_1(X0_47) != iProver_top
    | v1_relat_1(X1_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1296])).

cnf(c_2313,plain,
    ( k1_funct_1(X0_47,X0_50) = k1_funct_1(sK4,X0_50)
    | sK2 = k1_xboole_0
    | r2_hidden(X0_50,k1_relat_1(X0_47)) != iProver_top
    | r1_partfun1(X0_47,sK4) != iProver_top
    | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0_47) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2144,c_1626])).

cnf(c_2494,plain,
    ( v1_relat_1(X0_47) != iProver_top
    | k1_funct_1(X0_47,X0_50) = k1_funct_1(sK4,X0_50)
    | sK2 = k1_xboole_0
    | r2_hidden(X0_50,k1_relat_1(X0_47)) != iProver_top
    | r1_partfun1(X0_47,sK4) != iProver_top
    | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(X0_47) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2313,c_24,c_26,c_1770])).

cnf(c_2495,plain,
    ( k1_funct_1(X0_47,X0_50) = k1_funct_1(sK4,X0_50)
    | sK2 = k1_xboole_0
    | r2_hidden(X0_50,k1_relat_1(X0_47)) != iProver_top
    | r1_partfun1(X0_47,sK4) != iProver_top
    | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_relat_1(X0_47) != iProver_top ),
    inference(renaming,[status(thm)],[c_2494])).

cnf(c_2508,plain,
    ( k1_funct_1(sK4,X0_50) = k1_funct_1(sK3,X0_50)
    | sK2 = k1_xboole_0
    | r2_hidden(X0_50,k1_relat_1(sK3)) != iProver_top
    | r1_partfun1(sK3,sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2386,c_2495])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_22,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1772,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1307])).

cnf(c_1773,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1772])).

cnf(c_15,negated_conjecture,
    ( ~ r2_hidden(X0,k1_relset_1(sK1,sK2,sK3))
    | r1_partfun1(sK3,sK4)
    | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1302,negated_conjecture,
    ( ~ r2_hidden(X0_50,k1_relset_1(sK1,sK2,sK3))
    | r1_partfun1(sK3,sK4)
    | k1_funct_1(sK3,X0_50) = k1_funct_1(sK4,X0_50) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1621,plain,
    ( k1_funct_1(sK3,X0_50) = k1_funct_1(sK4,X0_50)
    | r2_hidden(X0_50,k1_relset_1(sK1,sK2,sK3)) != iProver_top
    | r1_partfun1(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1302])).

cnf(c_2157,plain,
    ( k1_funct_1(sK4,X0_50) = k1_funct_1(sK3,X0_50)
    | r2_hidden(X0_50,k1_relat_1(sK3)) != iProver_top
    | r1_partfun1(sK3,sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1926,c_1621])).

cnf(c_2617,plain,
    ( r2_hidden(X0_50,k1_relat_1(sK3)) != iProver_top
    | sK2 = k1_xboole_0
    | k1_funct_1(sK4,X0_50) = k1_funct_1(sK3,X0_50) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2508,c_22,c_23,c_1773,c_2157])).

cnf(c_2618,plain,
    ( k1_funct_1(sK4,X0_50) = k1_funct_1(sK3,X0_50)
    | sK2 = k1_xboole_0
    | r2_hidden(X0_50,k1_relat_1(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2617])).

cnf(c_3023,plain,
    ( k1_funct_1(sK4,sK0(sK3,sK4)) = k1_funct_1(sK3,sK0(sK3,sK4))
    | sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) = iProver_top
    | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3011,c_2618])).

cnf(c_3039,plain,
    ( r1_partfun1(sK3,sK4) = iProver_top
    | sK2 = k1_xboole_0
    | k1_funct_1(sK4,sK0(sK3,sK4)) = k1_funct_1(sK3,sK0(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3023,c_22,c_23,c_1773,c_2173])).

cnf(c_3040,plain,
    ( k1_funct_1(sK4,sK0(sK3,sK4)) = k1_funct_1(sK3,sK0(sK3,sK4))
    | sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_3039])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3))
    | ~ r1_partfun1(sK3,sK4) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1303,negated_conjecture,
    ( r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3))
    | ~ r1_partfun1(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1620,plain,
    ( r2_hidden(sK5,k1_relset_1(sK1,sK2,sK3)) = iProver_top
    | r1_partfun1(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1303])).

cnf(c_2158,plain,
    ( r2_hidden(sK5,k1_relat_1(sK3)) = iProver_top
    | r1_partfun1(sK3,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1926,c_1620])).

cnf(c_2626,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2158,c_2618])).

cnf(c_3046,plain,
    ( k1_funct_1(sK4,sK0(sK3,sK4)) = k1_funct_1(sK3,sK0(sK3,sK4))
    | k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3040,c_2626])).

cnf(c_9,plain,
    ( ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | r1_partfun1(X0,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_294,plain,
    ( r1_partfun1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
    | k1_relat_1(X1) != X3
    | k1_relat_1(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_12])).

cnf(c_295,plain,
    ( r1_partfun1(X0,X1)
    | ~ m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(k1_relat_1(X1)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_294])).

cnf(c_1294,plain,
    ( r1_partfun1(X0_47,X1_47)
    | ~ m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(k1_relat_1(X1_47)))
    | ~ v1_funct_1(X1_47)
    | ~ v1_funct_1(X0_47)
    | ~ v1_relat_1(X1_47)
    | ~ v1_relat_1(X0_47)
    | k1_funct_1(X0_47,sK0(X0_47,X1_47)) != k1_funct_1(X1_47,sK0(X0_47,X1_47)) ),
    inference(subtyping,[status(esa)],[c_295])).

cnf(c_1628,plain,
    ( k1_funct_1(X0_47,sK0(X0_47,X1_47)) != k1_funct_1(X1_47,sK0(X0_47,X1_47))
    | r1_partfun1(X0_47,X1_47) = iProver_top
    | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(k1_relat_1(X1_47))) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_funct_1(X1_47) != iProver_top
    | v1_relat_1(X0_47) != iProver_top
    | v1_relat_1(X1_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1294])).

cnf(c_3098,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) = iProver_top
    | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k1_relat_1(sK4))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3046,c_1628])).

cnf(c_3198,plain,
    ( sK2 = k1_xboole_0
    | k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k1_relat_1(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3098,c_22,c_23,c_24,c_26,c_1770,c_1773,c_2626])).

cnf(c_3199,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | sK2 = k1_xboole_0
    | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k1_relat_1(sK4))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3198])).

cnf(c_3205,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | sK2 = k1_xboole_0
    | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2144,c_3199])).

cnf(c_3379,plain,
    ( sK2 = k1_xboole_0
    | k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3205,c_23,c_2173])).

cnf(c_3380,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | sK2 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3379])).

cnf(c_13,negated_conjecture,
    ( ~ r1_partfun1(sK3,sK4)
    | k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1304,negated_conjecture,
    ( ~ r1_partfun1(sK3,sK4)
    | k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1619,plain,
    ( k1_funct_1(sK3,sK5) != k1_funct_1(sK4,sK5)
    | r1_partfun1(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1304])).

cnf(c_3383,plain,
    ( sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3380,c_1619])).

cnf(c_3388,plain,
    ( k1_funct_1(sK4,sK0(sK3,sK4)) = k1_funct_1(sK3,sK0(sK3,sK4))
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3040,c_3383])).

cnf(c_3474,plain,
    ( sK2 = k1_xboole_0
    | r1_partfun1(sK3,sK4) = iProver_top
    | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k1_relat_1(sK4))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3388,c_1628])).

cnf(c_3477,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k1_relat_1(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3474,c_22,c_23,c_24,c_26,c_1770,c_1773,c_3383])).

cnf(c_3483,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2144,c_3477])).

cnf(c_3504,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3483,c_23,c_2173])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_510,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK2 != X1
    | sK1 != k1_xboole_0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_18])).

cnf(c_511,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_510])).

cnf(c_1292,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_511])).

cnf(c_1630,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1292])).

cnf(c_3511,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3504,c_1630])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1301,negated_conjecture,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_3517,plain,
    ( sK1 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3504,c_1301])).

cnf(c_3518,plain,
    ( sK1 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_3517])).

cnf(c_3533,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3511,c_3518])).

cnf(c_3534,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3533])).

cnf(c_3513,plain,
    ( k1_relset_1(sK1,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_3504,c_1925])).

cnf(c_3527,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_3513,c_3518])).

cnf(c_3535,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3534,c_3527])).

cnf(c_3516,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3504,c_1622])).

cnf(c_3521,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3516,c_3518])).

cnf(c_3538,plain,
    ( k1_relat_1(sK4) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3535,c_3521])).

cnf(c_4308,plain,
    ( r2_hidden(sK0(X0_47,sK4),k1_relat_1(X0_47)) = iProver_top
    | r1_partfun1(X0_47,sK4) = iProver_top
    | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0_47) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3538,c_1627])).

cnf(c_5131,plain,
    ( v1_relat_1(X0_47) != iProver_top
    | r2_hidden(sK0(X0_47,sK4),k1_relat_1(X0_47)) = iProver_top
    | r1_partfun1(X0_47,sK4) = iProver_top
    | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0_47) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4308,c_24,c_26,c_1770])).

cnf(c_5132,plain,
    ( r2_hidden(sK0(X0_47,sK4),k1_relat_1(X0_47)) = iProver_top
    | r1_partfun1(X0_47,sK4) = iProver_top
    | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_relat_1(X0_47) != iProver_top ),
    inference(renaming,[status(thm)],[c_5131])).

cnf(c_3547,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3518,c_2386])).

cnf(c_4309,plain,
    ( k1_funct_1(X0_47,X0_50) = k1_funct_1(sK4,X0_50)
    | r2_hidden(X0_50,k1_relat_1(X0_47)) != iProver_top
    | r1_partfun1(X0_47,sK4) != iProver_top
    | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0_47) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3538,c_1626])).

cnf(c_5004,plain,
    ( v1_relat_1(X0_47) != iProver_top
    | k1_funct_1(X0_47,X0_50) = k1_funct_1(sK4,X0_50)
    | r2_hidden(X0_50,k1_relat_1(X0_47)) != iProver_top
    | r1_partfun1(X0_47,sK4) != iProver_top
    | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0_47) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4309,c_24,c_26,c_1770])).

cnf(c_5005,plain,
    ( k1_funct_1(X0_47,X0_50) = k1_funct_1(sK4,X0_50)
    | r2_hidden(X0_50,k1_relat_1(X0_47)) != iProver_top
    | r1_partfun1(X0_47,sK4) != iProver_top
    | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_relat_1(X0_47) != iProver_top ),
    inference(renaming,[status(thm)],[c_5004])).

cnf(c_5016,plain,
    ( k1_funct_1(sK4,X0_50) = k1_funct_1(sK3,X0_50)
    | r2_hidden(X0_50,k1_relat_1(sK3)) != iProver_top
    | r1_partfun1(sK3,sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3547,c_5005])).

cnf(c_5032,plain,
    ( r2_hidden(X0_50,k1_relat_1(sK3)) != iProver_top
    | k1_funct_1(sK4,X0_50) = k1_funct_1(sK3,X0_50) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5016,c_22,c_23,c_1773,c_2157])).

cnf(c_5033,plain,
    ( k1_funct_1(sK4,X0_50) = k1_funct_1(sK3,X0_50)
    | r2_hidden(X0_50,k1_relat_1(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5032])).

cnf(c_5143,plain,
    ( k1_funct_1(sK4,sK0(sK3,sK4)) = k1_funct_1(sK3,sK0(sK3,sK4))
    | r1_partfun1(sK3,sK4) = iProver_top
    | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5132,c_5033])).

cnf(c_1793,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1305])).

cnf(c_1799,plain,
    ( m1_subset_1(k1_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_1306])).

cnf(c_1800,plain,
    ( m1_subset_1(k1_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1799])).

cnf(c_1316,plain,
    ( k1_zfmisc_1(X0_47) = k1_zfmisc_1(X1_47)
    | X0_47 != X1_47 ),
    theory(equality)).

cnf(c_1953,plain,
    ( k1_zfmisc_1(X0_47) = k1_zfmisc_1(sK1)
    | X0_47 != sK1 ),
    inference(instantiation,[status(thm)],[c_1316])).

cnf(c_1958,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(sK1)
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_1953])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_490,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | sK1 != X1
    | sK4 != X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_18])).

cnf(c_491,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_490])).

cnf(c_1293,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4 ),
    inference(subtyping,[status(esa)],[c_491])).

cnf(c_1629,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1293])).

cnf(c_1309,plain,
    ( X0_47 = X0_47 ),
    theory(equality)).

cnf(c_1332,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1309])).

cnf(c_1313,plain,
    ( X0_47 != X1_47
    | X2_47 != X1_47
    | X2_47 = X0_47 ),
    theory(equality)).

cnf(c_2298,plain,
    ( sK2 != X0_47
    | k1_xboole_0 != X0_47
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1313])).

cnf(c_2299,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2298])).

cnf(c_2426,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1629,c_1332,c_1301,c_2299])).

cnf(c_2253,plain,
    ( X0_47 != X1_47
    | X0_47 = k1_relset_1(sK1,sK2,sK3)
    | k1_relset_1(sK1,sK2,sK3) != X1_47 ),
    inference(instantiation,[status(thm)],[c_1313])).

cnf(c_2612,plain,
    ( X0_47 = k1_relset_1(sK1,sK2,sK3)
    | X0_47 != k1_relat_1(sK3)
    | k1_relset_1(sK1,sK2,sK3) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2253])).

cnf(c_2713,plain,
    ( k1_relset_1(sK1,sK2,sK3) != k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3)
    | k1_relat_1(sK3) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2612])).

cnf(c_2714,plain,
    ( k1_relat_1(sK3) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1309])).

cnf(c_1317,plain,
    ( ~ m1_subset_1(X0_47,X0_48)
    | m1_subset_1(X1_47,X1_48)
    | X1_48 != X0_48
    | X1_47 != X0_47 ),
    theory(equality)).

cnf(c_1842,plain,
    ( m1_subset_1(X0_47,X0_48)
    | ~ m1_subset_1(k1_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
    | X0_48 != k1_zfmisc_1(sK1)
    | X0_47 != k1_relset_1(sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1317])).

cnf(c_2137,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(X1_47))
    | ~ m1_subset_1(k1_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
    | k1_zfmisc_1(X1_47) != k1_zfmisc_1(sK1)
    | X0_47 != k1_relset_1(sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1842])).

cnf(c_3151,plain,
    ( ~ m1_subset_1(k1_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
    | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(X0_47))
    | k1_zfmisc_1(X0_47) != k1_zfmisc_1(sK1)
    | k1_relat_1(sK3) != k1_relset_1(sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2137])).

cnf(c_3155,plain,
    ( k1_zfmisc_1(X0_47) != k1_zfmisc_1(sK1)
    | k1_relat_1(sK3) != k1_relset_1(sK1,sK2,sK3)
    | m1_subset_1(k1_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(X0_47)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3151])).

cnf(c_3157,plain,
    ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(sK1)
    | k1_relat_1(sK3) != k1_relset_1(sK1,sK2,sK3)
    | m1_subset_1(k1_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3155])).

cnf(c_5156,plain,
    ( r1_partfun1(sK3,sK4) = iProver_top
    | k1_funct_1(sK4,sK0(sK3,sK4)) = k1_funct_1(sK3,sK0(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5143,c_22,c_20,c_23,c_1773,c_1793,c_1800,c_1958,c_2173,c_2426,c_2713,c_2714,c_3157,c_3483])).

cnf(c_5157,plain,
    ( k1_funct_1(sK4,sK0(sK3,sK4)) = k1_funct_1(sK3,sK0(sK3,sK4))
    | r1_partfun1(sK3,sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_5156])).

cnf(c_5040,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | r1_partfun1(sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2158,c_5033])).

cnf(c_5162,plain,
    ( k1_funct_1(sK4,sK0(sK3,sK4)) = k1_funct_1(sK3,sK0(sK3,sK4))
    | k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5) ),
    inference(superposition,[status(thm)],[c_5157,c_5040])).

cnf(c_5259,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | r1_partfun1(sK3,sK4) = iProver_top
    | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k1_relat_1(sK4))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5162,c_1628])).

cnf(c_5260,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5)
    | r1_partfun1(sK3,sK4) = iProver_top
    | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5259,c_3538])).

cnf(c_5388,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK3,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5260,c_22,c_20,c_23,c_24,c_26,c_1770,c_1773,c_1793,c_1800,c_1958,c_2173,c_2426,c_2713,c_2714,c_3157,c_3483,c_5040])).

cnf(c_5391,plain,
    ( k1_funct_1(sK3,sK5) != k1_funct_1(sK3,sK5)
    | r1_partfun1(sK3,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5388,c_1619])).

cnf(c_5393,plain,
    ( r1_partfun1(sK3,sK4) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5391])).

cnf(c_5396,plain,
    ( k1_funct_1(sK4,sK0(sK3,sK4)) = k1_funct_1(sK3,sK0(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_5157,c_5393])).

cnf(c_5417,plain,
    ( r1_partfun1(sK3,sK4) = iProver_top
    | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k1_relat_1(sK4))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5396,c_1628])).

cnf(c_5418,plain,
    ( r1_partfun1(sK3,sK4) = iProver_top
    | m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5417,c_3538])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5418,c_5393,c_3483,c_3157,c_2714,c_2713,c_2426,c_2173,c_1958,c_1800,c_1793,c_1773,c_1770,c_26,c_24,c_23,c_20,c_22])).


%------------------------------------------------------------------------------
