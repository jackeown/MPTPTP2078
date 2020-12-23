%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:41 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :  191 (61731 expanded)
%              Number of clauses        :  142 (18297 expanded)
%              Number of leaves         :   15 (13996 expanded)
%              Depth                    :   45
%              Number of atoms          :  779 (431966 expanded)
%              Number of equality atoms :  410 (102041 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
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

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
          & r2_hidden(X3,k1_relset_1(X0,X0,X1)) )
     => ( k1_funct_1(X1,sK4) != k1_funct_1(X2,sK4)
        & r2_hidden(sK4,k1_relset_1(X0,X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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

fof(f28,plain,
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

fof(f31,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f27,f30,f29,f28])).

fof(f46,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f51,plain,
    ( r2_hidden(sK4,k1_relset_1(sK1,sK1,sK2))
    | ~ r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
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

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f5])).

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
    inference(flattening,[],[f14])).

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
    inference(nnf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f48,plain,(
    v1_funct_2(sK3,sK1,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f49,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

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
    inference(nnf_transformation,[],[f17])).

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

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X0,X1)
      | r2_hidden(sK0(X0,X1),k1_relat_1(X0))
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f47,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f50,plain,(
    ! [X4] :
      ( k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
      | ~ r2_hidden(X4,k1_relset_1(sK1,sK1,sK2))
      | r1_partfun1(sK2,sK3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f45,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f42,plain,(
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

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X0,X1)
      | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
    | ~ r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f57,plain,(
    ! [X2,X1] :
      ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f37])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1297,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1622,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1297])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1303,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
    | k1_relset_1(X1_46,X2_46,X0_46) = k1_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1616,plain,
    ( k1_relset_1(X0_46,X1_46,X2_46) = k1_relat_1(X2_46)
    | m1_subset_1(X2_46,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1303])).

cnf(c_1924,plain,
    ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1622,c_1616])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(sK4,k1_relset_1(sK1,sK1,sK2))
    | ~ r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1301,negated_conjecture,
    ( r2_hidden(sK4,k1_relset_1(sK1,sK1,sK2))
    | ~ r1_partfun1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1618,plain,
    ( r2_hidden(sK4,k1_relset_1(sK1,sK1,sK2)) = iProver_top
    | r1_partfun1(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1301])).

cnf(c_2172,plain,
    ( r2_hidden(sK4,k1_relat_1(sK2)) = iProver_top
    | r1_partfun1(sK2,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1924,c_1618])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_17,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_522,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK1 != X1
    | sK1 != X2
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_17])).

cnf(c_523,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k1_relset_1(sK1,sK1,sK3) = sK1
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_522])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_525,plain,
    ( k1_relset_1(sK1,sK1,sK3) = sK1
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_523,c_16])).

cnf(c_1290,plain,
    ( k1_relset_1(sK1,sK1,sK3) = sK1
    | k1_xboole_0 = sK1 ),
    inference(subtyping,[status(esa)],[c_525])).

cnf(c_1299,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1620,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1299])).

cnf(c_1923,plain,
    ( k1_relset_1(sK1,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1620,c_1616])).

cnf(c_2053,plain,
    ( k1_relat_1(sK3) = sK1
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1290,c_1923])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_11,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
    | r1_partfun1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_236,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
    | r1_partfun1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(X1) != X3
    | k1_relat_1(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_11])).

cnf(c_237,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
    | r1_partfun1(X0,X1)
    | ~ m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(k1_relat_1(X1)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_236])).

cnf(c_1295,plain,
    ( r2_hidden(sK0(X0_46,X1_46),k1_relat_1(X0_46))
    | r1_partfun1(X0_46,X1_46)
    | ~ m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(k1_relat_1(X1_46)))
    | ~ v1_funct_1(X1_46)
    | ~ v1_funct_1(X0_46)
    | ~ v1_relat_1(X1_46)
    | ~ v1_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_237])).

cnf(c_1624,plain,
    ( r2_hidden(sK0(X0_46,X1_46),k1_relat_1(X0_46)) = iProver_top
    | r1_partfun1(X0_46,X1_46) = iProver_top
    | m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(k1_relat_1(X1_46))) != iProver_top
    | v1_funct_1(X0_46) != iProver_top
    | v1_funct_1(X1_46) != iProver_top
    | v1_relat_1(X0_46) != iProver_top
    | v1_relat_1(X1_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1295])).

cnf(c_2308,plain,
    ( sK1 = k1_xboole_0
    | r2_hidden(sK0(X0_46,sK3),k1_relat_1(X0_46)) = iProver_top
    | r1_partfun1(X0_46,sK3) = iProver_top
    | m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(X0_46) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0_46) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2053,c_1624])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_23,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_25,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1305,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
    | v1_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1763,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1305])).

cnf(c_1764,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1763])).

cnf(c_2620,plain,
    ( v1_relat_1(X0_46) != iProver_top
    | sK1 = k1_xboole_0
    | r2_hidden(sK0(X0_46,sK3),k1_relat_1(X0_46)) = iProver_top
    | r1_partfun1(X0_46,sK3) = iProver_top
    | m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(X0_46) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2308,c_23,c_25,c_1764])).

cnf(c_2621,plain,
    ( sK1 = k1_xboole_0
    | r2_hidden(sK0(X0_46,sK3),k1_relat_1(X0_46)) = iProver_top
    | r1_partfun1(X0_46,sK3) = iProver_top
    | m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(X0_46) != iProver_top
    | v1_relat_1(X0_46) != iProver_top ),
    inference(renaming,[status(thm)],[c_2620])).

cnf(c_15,negated_conjecture,
    ( ~ r2_hidden(X0,k1_relset_1(sK1,sK1,sK2))
    | r1_partfun1(sK2,sK3)
    | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1300,negated_conjecture,
    ( ~ r2_hidden(X0_48,k1_relset_1(sK1,sK1,sK2))
    | r1_partfun1(sK2,sK3)
    | k1_funct_1(sK2,X0_48) = k1_funct_1(sK3,X0_48) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1619,plain,
    ( k1_funct_1(sK2,X0_48) = k1_funct_1(sK3,X0_48)
    | r2_hidden(X0_48,k1_relset_1(sK1,sK1,sK2)) != iProver_top
    | r1_partfun1(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1300])).

cnf(c_2171,plain,
    ( k1_funct_1(sK3,X0_48) = k1_funct_1(sK2,X0_48)
    | r2_hidden(X0_48,k1_relat_1(sK2)) != iProver_top
    | r1_partfun1(sK2,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1924,c_1619])).

cnf(c_2633,plain,
    ( k1_funct_1(sK2,sK0(sK2,sK3)) = k1_funct_1(sK3,sK0(sK2,sK3))
    | sK1 = k1_xboole_0
    | r1_partfun1(sK2,sK3) = iProver_top
    | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2621,c_2171])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_21,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_22,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1766,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1305])).

cnf(c_1767,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1766])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1304,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
    | m1_subset_1(k1_relset_1(X1_46,X2_46,X0_46),k1_zfmisc_1(X1_46)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1615,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46))) != iProver_top
    | m1_subset_1(k1_relset_1(X1_46,X2_46,X0_46),k1_zfmisc_1(X1_46)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1304])).

cnf(c_2187,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1924,c_1615])).

cnf(c_2693,plain,
    ( r1_partfun1(sK2,sK3) = iProver_top
    | sK1 = k1_xboole_0
    | k1_funct_1(sK2,sK0(sK2,sK3)) = k1_funct_1(sK3,sK0(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2633,c_21,c_22,c_1767,c_2187])).

cnf(c_2694,plain,
    ( k1_funct_1(sK2,sK0(sK2,sK3)) = k1_funct_1(sK3,sK0(sK2,sK3))
    | sK1 = k1_xboole_0
    | r1_partfun1(sK2,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_2693])).

cnf(c_2382,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2187,c_22])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r1_partfun1(X1,X2)
    | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X2,X0) = k1_funct_1(X1,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_290,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r1_partfun1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X1,X0) = k1_funct_1(X2,X0)
    | k1_relat_1(X2) != X4
    | k1_relat_1(X1) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_12])).

cnf(c_291,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r1_partfun1(X1,X2)
    | ~ m1_subset_1(k1_relat_1(X1),k1_zfmisc_1(k1_relat_1(X2)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X1,X0) = k1_funct_1(X2,X0) ),
    inference(unflattening,[status(thm)],[c_290])).

cnf(c_1293,plain,
    ( ~ r2_hidden(X0_48,k1_relat_1(X0_46))
    | ~ r1_partfun1(X0_46,X1_46)
    | ~ m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(k1_relat_1(X1_46)))
    | ~ v1_funct_1(X1_46)
    | ~ v1_funct_1(X0_46)
    | ~ v1_relat_1(X1_46)
    | ~ v1_relat_1(X0_46)
    | k1_funct_1(X0_46,X0_48) = k1_funct_1(X1_46,X0_48) ),
    inference(subtyping,[status(esa)],[c_291])).

cnf(c_1626,plain,
    ( k1_funct_1(X0_46,X0_48) = k1_funct_1(X1_46,X0_48)
    | r2_hidden(X0_48,k1_relat_1(X0_46)) != iProver_top
    | r1_partfun1(X0_46,X1_46) != iProver_top
    | m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(k1_relat_1(X1_46))) != iProver_top
    | v1_funct_1(X0_46) != iProver_top
    | v1_funct_1(X1_46) != iProver_top
    | v1_relat_1(X0_46) != iProver_top
    | v1_relat_1(X1_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1293])).

cnf(c_3009,plain,
    ( k1_funct_1(X0_46,X0_48) = k1_funct_1(sK3,X0_48)
    | sK1 = k1_xboole_0
    | r2_hidden(X0_48,k1_relat_1(X0_46)) != iProver_top
    | r1_partfun1(X0_46,sK3) != iProver_top
    | m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(X0_46) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0_46) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2053,c_1626])).

cnf(c_3133,plain,
    ( v1_relat_1(X0_46) != iProver_top
    | k1_funct_1(X0_46,X0_48) = k1_funct_1(sK3,X0_48)
    | sK1 = k1_xboole_0
    | r2_hidden(X0_48,k1_relat_1(X0_46)) != iProver_top
    | r1_partfun1(X0_46,sK3) != iProver_top
    | m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(X0_46) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3009,c_23,c_25,c_1764])).

cnf(c_3134,plain,
    ( k1_funct_1(X0_46,X0_48) = k1_funct_1(sK3,X0_48)
    | sK1 = k1_xboole_0
    | r2_hidden(X0_48,k1_relat_1(X0_46)) != iProver_top
    | r1_partfun1(X0_46,sK3) != iProver_top
    | m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(sK1)) != iProver_top
    | v1_funct_1(X0_46) != iProver_top
    | v1_relat_1(X0_46) != iProver_top ),
    inference(renaming,[status(thm)],[c_3133])).

cnf(c_3147,plain,
    ( k1_funct_1(sK3,X0_48) = k1_funct_1(sK2,X0_48)
    | sK1 = k1_xboole_0
    | r2_hidden(X0_48,k1_relat_1(sK2)) != iProver_top
    | r1_partfun1(sK2,sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2382,c_3134])).

cnf(c_3165,plain,
    ( r2_hidden(X0_48,k1_relat_1(sK2)) != iProver_top
    | sK1 = k1_xboole_0
    | k1_funct_1(sK3,X0_48) = k1_funct_1(sK2,X0_48) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3147,c_21,c_22,c_1767,c_2171])).

cnf(c_3166,plain,
    ( k1_funct_1(sK3,X0_48) = k1_funct_1(sK2,X0_48)
    | sK1 = k1_xboole_0
    | r2_hidden(X0_48,k1_relat_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3165])).

cnf(c_3175,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4)
    | sK1 = k1_xboole_0
    | r1_partfun1(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2172,c_3166])).

cnf(c_3251,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4)
    | k1_funct_1(sK2,sK0(sK2,sK3)) = k1_funct_1(sK3,sK0(sK2,sK3))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2694,c_3175])).

cnf(c_10,plain,
    ( r1_partfun1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_263,plain,
    ( r1_partfun1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
    | k1_relat_1(X1) != X3
    | k1_relat_1(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_10])).

cnf(c_264,plain,
    ( r1_partfun1(X0,X1)
    | ~ m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(k1_relat_1(X1)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_263])).

cnf(c_1294,plain,
    ( r1_partfun1(X0_46,X1_46)
    | ~ m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(k1_relat_1(X1_46)))
    | ~ v1_funct_1(X1_46)
    | ~ v1_funct_1(X0_46)
    | ~ v1_relat_1(X1_46)
    | ~ v1_relat_1(X0_46)
    | k1_funct_1(X0_46,sK0(X0_46,X1_46)) != k1_funct_1(X1_46,sK0(X0_46,X1_46)) ),
    inference(subtyping,[status(esa)],[c_264])).

cnf(c_1625,plain,
    ( k1_funct_1(X0_46,sK0(X0_46,X1_46)) != k1_funct_1(X1_46,sK0(X0_46,X1_46))
    | r1_partfun1(X0_46,X1_46) = iProver_top
    | m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(k1_relat_1(X1_46))) != iProver_top
    | v1_funct_1(X0_46) != iProver_top
    | v1_funct_1(X1_46) != iProver_top
    | v1_relat_1(X0_46) != iProver_top
    | v1_relat_1(X1_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1294])).

cnf(c_3392,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4)
    | sK1 = k1_xboole_0
    | r1_partfun1(sK2,sK3) = iProver_top
    | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_relat_1(sK3))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3251,c_1625])).

cnf(c_1816,plain,
    ( r1_partfun1(X0_46,sK3)
    | ~ m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(k1_relat_1(sK3)))
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(X0_46)
    | ~ v1_relat_1(sK3)
    | k1_funct_1(X0_46,sK0(X0_46,sK3)) != k1_funct_1(sK3,sK0(X0_46,sK3)) ),
    inference(instantiation,[status(thm)],[c_1294])).

cnf(c_1885,plain,
    ( r1_partfun1(sK2,sK3)
    | ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_relat_1(sK3)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK0(sK2,sK3)) != k1_funct_1(sK3,sK0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1816])).

cnf(c_1886,plain,
    ( k1_funct_1(sK2,sK0(sK2,sK3)) != k1_funct_1(sK3,sK0(sK2,sK3))
    | r1_partfun1(sK2,sK3) = iProver_top
    | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_relat_1(sK3))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1885])).

cnf(c_3395,plain,
    ( sK1 = k1_xboole_0
    | r1_partfun1(sK2,sK3) = iProver_top
    | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_relat_1(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3392,c_21,c_22,c_23,c_25,c_1764,c_1767,c_1886,c_2187,c_2633])).

cnf(c_3402,plain,
    ( sK1 = k1_xboole_0
    | r1_partfun1(sK2,sK3) = iProver_top
    | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2053,c_3395])).

cnf(c_3425,plain,
    ( r1_partfun1(sK2,sK3) = iProver_top
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3402,c_22,c_2187])).

cnf(c_3426,plain,
    ( sK1 = k1_xboole_0
    | r1_partfun1(sK2,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_3425])).

cnf(c_3431,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4)
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3426,c_3175])).

cnf(c_13,negated_conjecture,
    ( ~ r1_partfun1(sK2,sK3)
    | k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1302,negated_conjecture,
    ( ~ r1_partfun1(sK2,sK3)
    | k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1617,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
    | r1_partfun1(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1302])).

cnf(c_3434,plain,
    ( sK1 = k1_xboole_0
    | r1_partfun1(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3431,c_1617])).

cnf(c_3562,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3434,c_22,c_2187,c_3402])).

cnf(c_3570,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3562,c_2382])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_509,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK1 != X1
    | sK1 != k1_xboole_0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_17])).

cnf(c_510,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_509])).

cnf(c_1291,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_510])).

cnf(c_1628,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1291])).

cnf(c_3573,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3562,c_1628])).

cnf(c_3587,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3573])).

cnf(c_3575,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_3562,c_1923])).

cnf(c_3588,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3587,c_3575])).

cnf(c_3578,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3562,c_1620])).

cnf(c_3591,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3588,c_3578])).

cnf(c_3672,plain,
    ( k1_funct_1(X0_46,X0_48) = k1_funct_1(sK3,X0_48)
    | r2_hidden(X0_48,k1_relat_1(X0_46)) != iProver_top
    | r1_partfun1(X0_46,sK3) != iProver_top
    | m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0_46) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0_46) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3591,c_1626])).

cnf(c_4364,plain,
    ( v1_relat_1(X0_46) != iProver_top
    | k1_funct_1(X0_46,X0_48) = k1_funct_1(sK3,X0_48)
    | r2_hidden(X0_48,k1_relat_1(X0_46)) != iProver_top
    | r1_partfun1(X0_46,sK3) != iProver_top
    | m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0_46) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3672,c_23,c_25,c_1764])).

cnf(c_4365,plain,
    ( k1_funct_1(X0_46,X0_48) = k1_funct_1(sK3,X0_48)
    | r2_hidden(X0_48,k1_relat_1(X0_46)) != iProver_top
    | r1_partfun1(X0_46,sK3) != iProver_top
    | m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0_46) != iProver_top
    | v1_relat_1(X0_46) != iProver_top ),
    inference(renaming,[status(thm)],[c_4364])).

cnf(c_4376,plain,
    ( k1_funct_1(sK3,X0_48) = k1_funct_1(sK2,X0_48)
    | r2_hidden(X0_48,k1_relat_1(sK2)) != iProver_top
    | r1_partfun1(sK2,sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3570,c_4365])).

cnf(c_3673,plain,
    ( r2_hidden(sK0(X0_46,sK3),k1_relat_1(X0_46)) = iProver_top
    | r1_partfun1(X0_46,sK3) = iProver_top
    | m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0_46) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0_46) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3591,c_1624])).

cnf(c_4453,plain,
    ( v1_relat_1(X0_46) != iProver_top
    | r2_hidden(sK0(X0_46,sK3),k1_relat_1(X0_46)) = iProver_top
    | r1_partfun1(X0_46,sK3) = iProver_top
    | m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0_46) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3673,c_23,c_25,c_1764])).

cnf(c_4454,plain,
    ( r2_hidden(sK0(X0_46,sK3),k1_relat_1(X0_46)) = iProver_top
    | r1_partfun1(X0_46,sK3) = iProver_top
    | m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0_46) != iProver_top
    | v1_relat_1(X0_46) != iProver_top ),
    inference(renaming,[status(thm)],[c_4453])).

cnf(c_4465,plain,
    ( k1_funct_1(sK2,sK0(sK2,sK3)) = k1_funct_1(sK3,sK0(sK2,sK3))
    | r1_partfun1(sK2,sK3) = iProver_top
    | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4454,c_2171])).

cnf(c_1307,plain,
    ( X0_46 = X0_46 ),
    theory(equality)).

cnf(c_1330,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1307])).

cnf(c_1783,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1303])).

cnf(c_1793,plain,
    ( m1_subset_1(k1_relset_1(sK1,sK1,sK2),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(instantiation,[status(thm)],[c_1304])).

cnf(c_1794,plain,
    ( m1_subset_1(k1_relset_1(sK1,sK1,sK2),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1793])).

cnf(c_1313,plain,
    ( k1_zfmisc_1(X0_46) = k1_zfmisc_1(X1_46)
    | X0_46 != X1_46 ),
    theory(equality)).

cnf(c_1951,plain,
    ( k1_zfmisc_1(X0_46) = k1_zfmisc_1(sK1)
    | X0_46 != sK1 ),
    inference(instantiation,[status(thm)],[c_1313])).

cnf(c_1956,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(sK1)
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_1951])).

cnf(c_1311,plain,
    ( X0_46 != X1_46
    | X2_46 != X1_46
    | X2_46 = X0_46 ),
    theory(equality)).

cnf(c_2291,plain,
    ( X0_46 != X1_46
    | X0_46 = sK1
    | sK1 != X1_46 ),
    inference(instantiation,[status(thm)],[c_1311])).

cnf(c_2292,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2291])).

cnf(c_2247,plain,
    ( X0_46 != X1_46
    | X0_46 = k1_relset_1(sK1,sK1,sK2)
    | k1_relset_1(sK1,sK1,sK2) != X1_46 ),
    inference(instantiation,[status(thm)],[c_1311])).

cnf(c_2556,plain,
    ( X0_46 = k1_relset_1(sK1,sK1,sK2)
    | X0_46 != k1_relat_1(sK2)
    | k1_relset_1(sK1,sK1,sK2) != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2247])).

cnf(c_2703,plain,
    ( k1_relset_1(sK1,sK1,sK2) != k1_relat_1(sK2)
    | k1_relat_1(sK2) = k1_relset_1(sK1,sK1,sK2)
    | k1_relat_1(sK2) != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2556])).

cnf(c_2704,plain,
    ( k1_relat_1(sK2) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1307])).

cnf(c_1314,plain,
    ( ~ m1_subset_1(X0_46,X0_47)
    | m1_subset_1(X1_46,X1_47)
    | X1_47 != X0_47
    | X1_46 != X0_46 ),
    theory(equality)).

cnf(c_1837,plain,
    ( m1_subset_1(X0_46,X0_47)
    | ~ m1_subset_1(k1_relset_1(sK1,sK1,sK2),k1_zfmisc_1(sK1))
    | X0_47 != k1_zfmisc_1(sK1)
    | X0_46 != k1_relset_1(sK1,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1314])).

cnf(c_2142,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
    | ~ m1_subset_1(k1_relset_1(sK1,sK1,sK2),k1_zfmisc_1(sK1))
    | k1_zfmisc_1(X1_46) != k1_zfmisc_1(sK1)
    | X0_46 != k1_relset_1(sK1,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1837])).

cnf(c_3190,plain,
    ( ~ m1_subset_1(k1_relset_1(sK1,sK1,sK2),k1_zfmisc_1(sK1))
    | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(X0_46))
    | k1_zfmisc_1(X0_46) != k1_zfmisc_1(sK1)
    | k1_relat_1(sK2) != k1_relset_1(sK1,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2142])).

cnf(c_3194,plain,
    ( k1_zfmisc_1(X0_46) != k1_zfmisc_1(sK1)
    | k1_relat_1(sK2) != k1_relset_1(sK1,sK1,sK2)
    | m1_subset_1(k1_relset_1(sK1,sK1,sK2),k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(X0_46)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3190])).

cnf(c_3196,plain,
    ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(sK1)
    | k1_relat_1(sK2) != k1_relset_1(sK1,sK1,sK2)
    | m1_subset_1(k1_relset_1(sK1,sK1,sK2),k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3194])).

cnf(c_3529,plain,
    ( k1_relat_1(sK3) != X0_46
    | k1_relat_1(sK3) = sK1
    | sK1 != X0_46 ),
    inference(instantiation,[status(thm)],[c_2291])).

cnf(c_3531,plain,
    ( k1_relat_1(sK3) = sK1
    | k1_relat_1(sK3) != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3529])).

cnf(c_3941,plain,
    ( ~ m1_subset_1(k1_relset_1(sK1,sK1,sK2),k1_zfmisc_1(sK1))
    | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_relat_1(sK3)))
    | k1_zfmisc_1(k1_relat_1(sK3)) != k1_zfmisc_1(sK1)
    | k1_relat_1(sK2) != k1_relset_1(sK1,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_3190])).

cnf(c_3942,plain,
    ( k1_zfmisc_1(k1_relat_1(sK3)) != k1_zfmisc_1(sK1)
    | k1_relat_1(sK2) != k1_relset_1(sK1,sK1,sK2)
    | m1_subset_1(k1_relset_1(sK1,sK1,sK2),k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_relat_1(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3941])).

cnf(c_4330,plain,
    ( k1_zfmisc_1(k1_relat_1(sK3)) = k1_zfmisc_1(sK1)
    | k1_relat_1(sK3) != sK1 ),
    inference(instantiation,[status(thm)],[c_1951])).

cnf(c_4767,plain,
    ( r1_partfun1(sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4465,c_21,c_19,c_22,c_23,c_25,c_1330,c_1764,c_1767,c_1783,c_1794,c_1886,c_1956,c_2187,c_2292,c_2703,c_2704,c_3196,c_3402,c_3434,c_3531,c_3591,c_3942,c_4330])).

cnf(c_4841,plain,
    ( r2_hidden(X0_48,k1_relat_1(sK2)) != iProver_top
    | k1_funct_1(sK3,X0_48) = k1_funct_1(sK2,X0_48) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4376,c_21,c_19,c_22,c_23,c_25,c_1330,c_1764,c_1767,c_1783,c_1794,c_1886,c_1956,c_2187,c_2292,c_2703,c_2704,c_3196,c_3402,c_3434,c_3531,c_3591,c_3942,c_4330,c_4465])).

cnf(c_4842,plain,
    ( k1_funct_1(sK3,X0_48) = k1_funct_1(sK2,X0_48)
    | r2_hidden(X0_48,k1_relat_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4841])).

cnf(c_4850,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4)
    | r1_partfun1(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2172,c_4842])).

cnf(c_4389,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4)
    | r2_hidden(sK4,k1_relat_1(sK2)) != iProver_top
    | r1_partfun1(sK2,sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4376])).

cnf(c_4857,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4850,c_21,c_19,c_22,c_23,c_25,c_1330,c_1764,c_1767,c_1783,c_1794,c_1886,c_1956,c_2172,c_2187,c_2292,c_2703,c_2704,c_3196,c_3402,c_3434,c_3531,c_3591,c_3942,c_4330,c_4389,c_4465])).

cnf(c_4860,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK2,sK4)
    | r1_partfun1(sK2,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4857,c_1617])).

cnf(c_4997,plain,
    ( r1_partfun1(sK2,sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4860])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4997,c_4767])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n024.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:30:36 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.74/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/0.98  
% 2.74/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.74/0.98  
% 2.74/0.98  ------  iProver source info
% 2.74/0.98  
% 2.74/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.74/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.74/0.98  git: non_committed_changes: false
% 2.74/0.98  git: last_make_outside_of_git: false
% 2.74/0.98  
% 2.74/0.98  ------ 
% 2.74/0.98  
% 2.74/0.98  ------ Input Options
% 2.74/0.98  
% 2.74/0.98  --out_options                           all
% 2.74/0.98  --tptp_safe_out                         true
% 2.74/0.98  --problem_path                          ""
% 2.74/0.98  --include_path                          ""
% 2.74/0.98  --clausifier                            res/vclausify_rel
% 2.74/0.98  --clausifier_options                    --mode clausify
% 2.74/0.98  --stdin                                 false
% 2.74/0.98  --stats_out                             all
% 2.74/0.98  
% 2.74/0.98  ------ General Options
% 2.74/0.98  
% 2.74/0.98  --fof                                   false
% 2.74/0.98  --time_out_real                         305.
% 2.74/0.98  --time_out_virtual                      -1.
% 2.74/0.98  --symbol_type_check                     false
% 2.74/0.98  --clausify_out                          false
% 2.74/0.98  --sig_cnt_out                           false
% 2.74/0.98  --trig_cnt_out                          false
% 2.74/0.98  --trig_cnt_out_tolerance                1.
% 2.74/0.98  --trig_cnt_out_sk_spl                   false
% 2.74/0.98  --abstr_cl_out                          false
% 2.74/0.98  
% 2.74/0.98  ------ Global Options
% 2.74/0.98  
% 2.74/0.98  --schedule                              default
% 2.74/0.98  --add_important_lit                     false
% 2.74/0.98  --prop_solver_per_cl                    1000
% 2.74/0.98  --min_unsat_core                        false
% 2.74/0.98  --soft_assumptions                      false
% 2.74/0.98  --soft_lemma_size                       3
% 2.74/0.98  --prop_impl_unit_size                   0
% 2.74/0.98  --prop_impl_unit                        []
% 2.74/0.98  --share_sel_clauses                     true
% 2.74/0.98  --reset_solvers                         false
% 2.74/0.98  --bc_imp_inh                            [conj_cone]
% 2.74/0.98  --conj_cone_tolerance                   3.
% 2.74/0.98  --extra_neg_conj                        none
% 2.74/0.98  --large_theory_mode                     true
% 2.74/0.98  --prolific_symb_bound                   200
% 2.74/0.98  --lt_threshold                          2000
% 2.74/0.98  --clause_weak_htbl                      true
% 2.74/0.98  --gc_record_bc_elim                     false
% 2.74/0.98  
% 2.74/0.98  ------ Preprocessing Options
% 2.74/0.98  
% 2.74/0.98  --preprocessing_flag                    true
% 2.74/0.98  --time_out_prep_mult                    0.1
% 2.74/0.98  --splitting_mode                        input
% 2.74/0.98  --splitting_grd                         true
% 2.74/0.98  --splitting_cvd                         false
% 2.74/0.98  --splitting_cvd_svl                     false
% 2.74/0.98  --splitting_nvd                         32
% 2.74/0.98  --sub_typing                            true
% 2.74/0.98  --prep_gs_sim                           true
% 2.74/0.98  --prep_unflatten                        true
% 2.74/0.98  --prep_res_sim                          true
% 2.74/0.98  --prep_upred                            true
% 2.74/0.98  --prep_sem_filter                       exhaustive
% 2.74/0.98  --prep_sem_filter_out                   false
% 2.74/0.98  --pred_elim                             true
% 2.74/0.98  --res_sim_input                         true
% 2.74/0.98  --eq_ax_congr_red                       true
% 2.74/0.98  --pure_diseq_elim                       true
% 2.74/0.98  --brand_transform                       false
% 2.74/0.98  --non_eq_to_eq                          false
% 2.74/0.98  --prep_def_merge                        true
% 2.74/0.98  --prep_def_merge_prop_impl              false
% 2.74/0.98  --prep_def_merge_mbd                    true
% 2.74/0.98  --prep_def_merge_tr_red                 false
% 2.74/0.98  --prep_def_merge_tr_cl                  false
% 2.74/0.98  --smt_preprocessing                     true
% 2.74/0.98  --smt_ac_axioms                         fast
% 2.74/0.98  --preprocessed_out                      false
% 2.74/0.98  --preprocessed_stats                    false
% 2.74/0.98  
% 2.74/0.98  ------ Abstraction refinement Options
% 2.74/0.98  
% 2.74/0.98  --abstr_ref                             []
% 2.74/0.98  --abstr_ref_prep                        false
% 2.74/0.98  --abstr_ref_until_sat                   false
% 2.74/0.98  --abstr_ref_sig_restrict                funpre
% 2.74/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.74/0.98  --abstr_ref_under                       []
% 2.74/0.98  
% 2.74/0.98  ------ SAT Options
% 2.74/0.98  
% 2.74/0.98  --sat_mode                              false
% 2.74/0.98  --sat_fm_restart_options                ""
% 2.74/0.98  --sat_gr_def                            false
% 2.74/0.98  --sat_epr_types                         true
% 2.74/0.98  --sat_non_cyclic_types                  false
% 2.74/0.98  --sat_finite_models                     false
% 2.74/0.98  --sat_fm_lemmas                         false
% 2.74/0.98  --sat_fm_prep                           false
% 2.74/0.98  --sat_fm_uc_incr                        true
% 2.74/0.98  --sat_out_model                         small
% 2.74/0.98  --sat_out_clauses                       false
% 2.74/0.98  
% 2.74/0.98  ------ QBF Options
% 2.74/0.98  
% 2.74/0.98  --qbf_mode                              false
% 2.74/0.98  --qbf_elim_univ                         false
% 2.74/0.98  --qbf_dom_inst                          none
% 2.74/0.98  --qbf_dom_pre_inst                      false
% 2.74/0.98  --qbf_sk_in                             false
% 2.74/0.98  --qbf_pred_elim                         true
% 2.74/0.98  --qbf_split                             512
% 2.74/0.98  
% 2.74/0.98  ------ BMC1 Options
% 2.74/0.98  
% 2.74/0.98  --bmc1_incremental                      false
% 2.74/0.98  --bmc1_axioms                           reachable_all
% 2.74/0.98  --bmc1_min_bound                        0
% 2.74/0.98  --bmc1_max_bound                        -1
% 2.74/0.98  --bmc1_max_bound_default                -1
% 2.74/0.98  --bmc1_symbol_reachability              true
% 2.74/0.98  --bmc1_property_lemmas                  false
% 2.74/0.98  --bmc1_k_induction                      false
% 2.74/0.98  --bmc1_non_equiv_states                 false
% 2.74/0.98  --bmc1_deadlock                         false
% 2.74/0.98  --bmc1_ucm                              false
% 2.74/0.98  --bmc1_add_unsat_core                   none
% 2.74/0.98  --bmc1_unsat_core_children              false
% 2.74/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.74/0.98  --bmc1_out_stat                         full
% 2.74/0.98  --bmc1_ground_init                      false
% 2.74/0.98  --bmc1_pre_inst_next_state              false
% 2.74/0.98  --bmc1_pre_inst_state                   false
% 2.74/0.98  --bmc1_pre_inst_reach_state             false
% 2.74/0.98  --bmc1_out_unsat_core                   false
% 2.74/0.98  --bmc1_aig_witness_out                  false
% 2.74/0.98  --bmc1_verbose                          false
% 2.74/0.98  --bmc1_dump_clauses_tptp                false
% 2.74/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.74/0.98  --bmc1_dump_file                        -
% 2.74/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.74/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.74/0.98  --bmc1_ucm_extend_mode                  1
% 2.74/0.98  --bmc1_ucm_init_mode                    2
% 2.74/0.98  --bmc1_ucm_cone_mode                    none
% 2.74/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.74/0.98  --bmc1_ucm_relax_model                  4
% 2.74/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.74/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.74/0.98  --bmc1_ucm_layered_model                none
% 2.74/0.98  --bmc1_ucm_max_lemma_size               10
% 2.74/0.98  
% 2.74/0.98  ------ AIG Options
% 2.74/0.98  
% 2.74/0.98  --aig_mode                              false
% 2.74/0.98  
% 2.74/0.98  ------ Instantiation Options
% 2.74/0.98  
% 2.74/0.98  --instantiation_flag                    true
% 2.74/0.98  --inst_sos_flag                         false
% 2.74/0.98  --inst_sos_phase                        true
% 2.74/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.74/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.74/0.98  --inst_lit_sel_side                     num_symb
% 2.74/0.98  --inst_solver_per_active                1400
% 2.74/0.98  --inst_solver_calls_frac                1.
% 2.74/0.98  --inst_passive_queue_type               priority_queues
% 2.74/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.74/0.98  --inst_passive_queues_freq              [25;2]
% 2.74/0.98  --inst_dismatching                      true
% 2.74/0.98  --inst_eager_unprocessed_to_passive     true
% 2.74/0.98  --inst_prop_sim_given                   true
% 2.74/0.98  --inst_prop_sim_new                     false
% 2.74/0.98  --inst_subs_new                         false
% 2.74/0.98  --inst_eq_res_simp                      false
% 2.74/0.98  --inst_subs_given                       false
% 2.74/0.98  --inst_orphan_elimination               true
% 2.74/0.98  --inst_learning_loop_flag               true
% 2.74/0.98  --inst_learning_start                   3000
% 2.74/0.98  --inst_learning_factor                  2
% 2.74/0.98  --inst_start_prop_sim_after_learn       3
% 2.74/0.98  --inst_sel_renew                        solver
% 2.74/0.98  --inst_lit_activity_flag                true
% 2.74/0.98  --inst_restr_to_given                   false
% 2.74/0.98  --inst_activity_threshold               500
% 2.74/0.98  --inst_out_proof                        true
% 2.74/0.98  
% 2.74/0.98  ------ Resolution Options
% 2.74/0.98  
% 2.74/0.98  --resolution_flag                       true
% 2.74/0.98  --res_lit_sel                           adaptive
% 2.74/0.98  --res_lit_sel_side                      none
% 2.74/0.98  --res_ordering                          kbo
% 2.74/0.98  --res_to_prop_solver                    active
% 2.74/0.98  --res_prop_simpl_new                    false
% 2.74/0.98  --res_prop_simpl_given                  true
% 2.74/0.98  --res_passive_queue_type                priority_queues
% 2.74/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.74/0.98  --res_passive_queues_freq               [15;5]
% 2.74/0.98  --res_forward_subs                      full
% 2.74/0.98  --res_backward_subs                     full
% 2.74/0.98  --res_forward_subs_resolution           true
% 2.74/0.98  --res_backward_subs_resolution          true
% 2.74/0.98  --res_orphan_elimination                true
% 2.74/0.98  --res_time_limit                        2.
% 2.74/0.98  --res_out_proof                         true
% 2.74/0.98  
% 2.74/0.98  ------ Superposition Options
% 2.74/0.98  
% 2.74/0.98  --superposition_flag                    true
% 2.74/0.98  --sup_passive_queue_type                priority_queues
% 2.74/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.74/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.74/0.98  --demod_completeness_check              fast
% 2.74/0.98  --demod_use_ground                      true
% 2.74/0.98  --sup_to_prop_solver                    passive
% 2.74/0.98  --sup_prop_simpl_new                    true
% 2.74/0.98  --sup_prop_simpl_given                  true
% 2.74/0.98  --sup_fun_splitting                     false
% 2.74/0.98  --sup_smt_interval                      50000
% 2.74/0.98  
% 2.74/0.98  ------ Superposition Simplification Setup
% 2.74/0.98  
% 2.74/0.98  --sup_indices_passive                   []
% 2.74/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.74/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.98  --sup_full_bw                           [BwDemod]
% 2.74/0.98  --sup_immed_triv                        [TrivRules]
% 2.74/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.74/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.98  --sup_immed_bw_main                     []
% 2.74/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.74/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/0.98  
% 2.74/0.98  ------ Combination Options
% 2.74/0.98  
% 2.74/0.98  --comb_res_mult                         3
% 2.74/0.98  --comb_sup_mult                         2
% 2.74/0.98  --comb_inst_mult                        10
% 2.74/0.98  
% 2.74/0.98  ------ Debug Options
% 2.74/0.98  
% 2.74/0.98  --dbg_backtrace                         false
% 2.74/0.98  --dbg_dump_prop_clauses                 false
% 2.74/0.98  --dbg_dump_prop_clauses_file            -
% 2.74/0.98  --dbg_out_stat                          false
% 2.74/0.98  ------ Parsing...
% 2.74/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.74/0.98  
% 2.74/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.74/0.98  
% 2.74/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.74/0.98  
% 2.74/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.74/0.98  ------ Proving...
% 2.74/0.98  ------ Problem Properties 
% 2.74/0.98  
% 2.74/0.98  
% 2.74/0.98  clauses                                 16
% 2.74/0.98  conjectures                             7
% 2.74/0.98  EPR                                     2
% 2.74/0.98  Horn                                    12
% 2.74/0.98  unary                                   4
% 2.74/0.98  binary                                  6
% 2.74/0.98  lits                                    48
% 2.74/0.98  lits eq                                 12
% 2.74/0.98  fd_pure                                 0
% 2.74/0.98  fd_pseudo                               0
% 2.74/0.98  fd_cond                                 0
% 2.74/0.98  fd_pseudo_cond                          0
% 2.74/0.98  AC symbols                              0
% 2.74/0.98  
% 2.74/0.98  ------ Schedule dynamic 5 is on 
% 2.74/0.98  
% 2.74/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.74/0.98  
% 2.74/0.98  
% 2.74/0.98  ------ 
% 2.74/0.98  Current options:
% 2.74/0.98  ------ 
% 2.74/0.98  
% 2.74/0.98  ------ Input Options
% 2.74/0.98  
% 2.74/0.98  --out_options                           all
% 2.74/0.98  --tptp_safe_out                         true
% 2.74/0.98  --problem_path                          ""
% 2.74/0.98  --include_path                          ""
% 2.74/0.98  --clausifier                            res/vclausify_rel
% 2.74/0.98  --clausifier_options                    --mode clausify
% 2.74/0.98  --stdin                                 false
% 2.74/0.98  --stats_out                             all
% 2.74/0.98  
% 2.74/0.98  ------ General Options
% 2.74/0.98  
% 2.74/0.98  --fof                                   false
% 2.74/0.98  --time_out_real                         305.
% 2.74/0.98  --time_out_virtual                      -1.
% 2.74/0.98  --symbol_type_check                     false
% 2.74/0.98  --clausify_out                          false
% 2.74/0.98  --sig_cnt_out                           false
% 2.74/0.98  --trig_cnt_out                          false
% 2.74/0.98  --trig_cnt_out_tolerance                1.
% 2.74/0.98  --trig_cnt_out_sk_spl                   false
% 2.74/0.98  --abstr_cl_out                          false
% 2.74/0.98  
% 2.74/0.98  ------ Global Options
% 2.74/0.98  
% 2.74/0.98  --schedule                              default
% 2.74/0.98  --add_important_lit                     false
% 2.74/0.98  --prop_solver_per_cl                    1000
% 2.74/0.98  --min_unsat_core                        false
% 2.74/0.98  --soft_assumptions                      false
% 2.74/0.98  --soft_lemma_size                       3
% 2.74/0.98  --prop_impl_unit_size                   0
% 2.74/0.98  --prop_impl_unit                        []
% 2.74/0.98  --share_sel_clauses                     true
% 2.74/0.98  --reset_solvers                         false
% 2.74/0.98  --bc_imp_inh                            [conj_cone]
% 2.74/0.98  --conj_cone_tolerance                   3.
% 2.74/0.98  --extra_neg_conj                        none
% 2.74/0.98  --large_theory_mode                     true
% 2.74/0.98  --prolific_symb_bound                   200
% 2.74/0.98  --lt_threshold                          2000
% 2.74/0.98  --clause_weak_htbl                      true
% 2.74/0.98  --gc_record_bc_elim                     false
% 2.74/0.98  
% 2.74/0.98  ------ Preprocessing Options
% 2.74/0.98  
% 2.74/0.98  --preprocessing_flag                    true
% 2.74/0.98  --time_out_prep_mult                    0.1
% 2.74/0.98  --splitting_mode                        input
% 2.74/0.98  --splitting_grd                         true
% 2.74/0.98  --splitting_cvd                         false
% 2.74/0.98  --splitting_cvd_svl                     false
% 2.74/0.98  --splitting_nvd                         32
% 2.74/0.98  --sub_typing                            true
% 2.74/0.98  --prep_gs_sim                           true
% 2.74/0.98  --prep_unflatten                        true
% 2.74/0.98  --prep_res_sim                          true
% 2.74/0.98  --prep_upred                            true
% 2.74/0.98  --prep_sem_filter                       exhaustive
% 2.74/0.98  --prep_sem_filter_out                   false
% 2.74/0.98  --pred_elim                             true
% 2.74/0.98  --res_sim_input                         true
% 2.74/0.98  --eq_ax_congr_red                       true
% 2.74/0.98  --pure_diseq_elim                       true
% 2.74/0.98  --brand_transform                       false
% 2.74/0.98  --non_eq_to_eq                          false
% 2.74/0.98  --prep_def_merge                        true
% 2.74/0.98  --prep_def_merge_prop_impl              false
% 2.74/0.98  --prep_def_merge_mbd                    true
% 2.74/0.98  --prep_def_merge_tr_red                 false
% 2.74/0.98  --prep_def_merge_tr_cl                  false
% 2.74/0.98  --smt_preprocessing                     true
% 2.74/0.98  --smt_ac_axioms                         fast
% 2.74/0.98  --preprocessed_out                      false
% 2.74/0.98  --preprocessed_stats                    false
% 2.74/0.98  
% 2.74/0.98  ------ Abstraction refinement Options
% 2.74/0.98  
% 2.74/0.98  --abstr_ref                             []
% 2.74/0.98  --abstr_ref_prep                        false
% 2.74/0.98  --abstr_ref_until_sat                   false
% 2.74/0.98  --abstr_ref_sig_restrict                funpre
% 2.74/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.74/0.98  --abstr_ref_under                       []
% 2.74/0.98  
% 2.74/0.98  ------ SAT Options
% 2.74/0.98  
% 2.74/0.98  --sat_mode                              false
% 2.74/0.98  --sat_fm_restart_options                ""
% 2.74/0.98  --sat_gr_def                            false
% 2.74/0.98  --sat_epr_types                         true
% 2.74/0.98  --sat_non_cyclic_types                  false
% 2.74/0.98  --sat_finite_models                     false
% 2.74/0.98  --sat_fm_lemmas                         false
% 2.74/0.98  --sat_fm_prep                           false
% 2.74/0.98  --sat_fm_uc_incr                        true
% 2.74/0.98  --sat_out_model                         small
% 2.74/0.98  --sat_out_clauses                       false
% 2.74/0.98  
% 2.74/0.98  ------ QBF Options
% 2.74/0.98  
% 2.74/0.98  --qbf_mode                              false
% 2.74/0.98  --qbf_elim_univ                         false
% 2.74/0.98  --qbf_dom_inst                          none
% 2.74/0.98  --qbf_dom_pre_inst                      false
% 2.74/0.98  --qbf_sk_in                             false
% 2.74/0.98  --qbf_pred_elim                         true
% 2.74/0.98  --qbf_split                             512
% 2.74/0.98  
% 2.74/0.98  ------ BMC1 Options
% 2.74/0.98  
% 2.74/0.98  --bmc1_incremental                      false
% 2.74/0.98  --bmc1_axioms                           reachable_all
% 2.74/0.98  --bmc1_min_bound                        0
% 2.74/0.98  --bmc1_max_bound                        -1
% 2.74/0.98  --bmc1_max_bound_default                -1
% 2.74/0.98  --bmc1_symbol_reachability              true
% 2.74/0.98  --bmc1_property_lemmas                  false
% 2.74/0.98  --bmc1_k_induction                      false
% 2.74/0.98  --bmc1_non_equiv_states                 false
% 2.74/0.98  --bmc1_deadlock                         false
% 2.74/0.98  --bmc1_ucm                              false
% 2.74/0.98  --bmc1_add_unsat_core                   none
% 2.74/0.98  --bmc1_unsat_core_children              false
% 2.74/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.74/0.98  --bmc1_out_stat                         full
% 2.74/0.98  --bmc1_ground_init                      false
% 2.74/0.98  --bmc1_pre_inst_next_state              false
% 2.74/0.98  --bmc1_pre_inst_state                   false
% 2.74/0.98  --bmc1_pre_inst_reach_state             false
% 2.74/0.98  --bmc1_out_unsat_core                   false
% 2.74/0.98  --bmc1_aig_witness_out                  false
% 2.74/0.98  --bmc1_verbose                          false
% 2.74/0.98  --bmc1_dump_clauses_tptp                false
% 2.74/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.74/0.98  --bmc1_dump_file                        -
% 2.74/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.74/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.74/0.98  --bmc1_ucm_extend_mode                  1
% 2.74/0.98  --bmc1_ucm_init_mode                    2
% 2.74/0.98  --bmc1_ucm_cone_mode                    none
% 2.74/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.74/0.98  --bmc1_ucm_relax_model                  4
% 2.74/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.74/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.74/0.98  --bmc1_ucm_layered_model                none
% 2.74/0.98  --bmc1_ucm_max_lemma_size               10
% 2.74/0.98  
% 2.74/0.98  ------ AIG Options
% 2.74/0.98  
% 2.74/0.98  --aig_mode                              false
% 2.74/0.98  
% 2.74/0.98  ------ Instantiation Options
% 2.74/0.98  
% 2.74/0.98  --instantiation_flag                    true
% 2.74/0.98  --inst_sos_flag                         false
% 2.74/0.98  --inst_sos_phase                        true
% 2.74/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.74/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.74/0.98  --inst_lit_sel_side                     none
% 2.74/0.98  --inst_solver_per_active                1400
% 2.74/0.98  --inst_solver_calls_frac                1.
% 2.74/0.98  --inst_passive_queue_type               priority_queues
% 2.74/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.74/0.98  --inst_passive_queues_freq              [25;2]
% 2.74/0.98  --inst_dismatching                      true
% 2.74/0.98  --inst_eager_unprocessed_to_passive     true
% 2.74/0.98  --inst_prop_sim_given                   true
% 2.74/0.98  --inst_prop_sim_new                     false
% 2.74/0.98  --inst_subs_new                         false
% 2.74/0.98  --inst_eq_res_simp                      false
% 2.74/0.98  --inst_subs_given                       false
% 2.74/0.98  --inst_orphan_elimination               true
% 2.74/0.98  --inst_learning_loop_flag               true
% 2.74/0.98  --inst_learning_start                   3000
% 2.74/0.98  --inst_learning_factor                  2
% 2.74/0.98  --inst_start_prop_sim_after_learn       3
% 2.74/0.98  --inst_sel_renew                        solver
% 2.74/0.98  --inst_lit_activity_flag                true
% 2.74/0.98  --inst_restr_to_given                   false
% 2.74/0.98  --inst_activity_threshold               500
% 2.74/0.98  --inst_out_proof                        true
% 2.74/0.98  
% 2.74/0.98  ------ Resolution Options
% 2.74/0.98  
% 2.74/0.98  --resolution_flag                       false
% 2.74/0.98  --res_lit_sel                           adaptive
% 2.74/0.98  --res_lit_sel_side                      none
% 2.74/0.98  --res_ordering                          kbo
% 2.74/0.98  --res_to_prop_solver                    active
% 2.74/0.98  --res_prop_simpl_new                    false
% 2.74/0.98  --res_prop_simpl_given                  true
% 2.74/0.98  --res_passive_queue_type                priority_queues
% 2.74/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.74/0.98  --res_passive_queues_freq               [15;5]
% 2.74/0.98  --res_forward_subs                      full
% 2.74/0.98  --res_backward_subs                     full
% 2.74/0.98  --res_forward_subs_resolution           true
% 2.74/0.98  --res_backward_subs_resolution          true
% 2.74/0.98  --res_orphan_elimination                true
% 2.74/0.98  --res_time_limit                        2.
% 2.74/0.98  --res_out_proof                         true
% 2.74/0.98  
% 2.74/0.98  ------ Superposition Options
% 2.74/0.98  
% 2.74/0.98  --superposition_flag                    true
% 2.74/0.98  --sup_passive_queue_type                priority_queues
% 2.74/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.74/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.74/0.98  --demod_completeness_check              fast
% 2.74/0.98  --demod_use_ground                      true
% 2.74/0.98  --sup_to_prop_solver                    passive
% 2.74/0.98  --sup_prop_simpl_new                    true
% 2.74/0.98  --sup_prop_simpl_given                  true
% 2.74/0.98  --sup_fun_splitting                     false
% 2.74/0.98  --sup_smt_interval                      50000
% 2.74/0.98  
% 2.74/0.98  ------ Superposition Simplification Setup
% 2.74/0.98  
% 2.74/0.98  --sup_indices_passive                   []
% 2.74/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.74/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.98  --sup_full_bw                           [BwDemod]
% 2.74/0.98  --sup_immed_triv                        [TrivRules]
% 2.74/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.74/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.98  --sup_immed_bw_main                     []
% 2.74/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.74/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/0.98  
% 2.74/0.98  ------ Combination Options
% 2.74/0.98  
% 2.74/0.98  --comb_res_mult                         3
% 2.74/0.98  --comb_sup_mult                         2
% 2.74/0.98  --comb_inst_mult                        10
% 2.74/0.98  
% 2.74/0.98  ------ Debug Options
% 2.74/0.98  
% 2.74/0.98  --dbg_backtrace                         false
% 2.74/0.98  --dbg_dump_prop_clauses                 false
% 2.74/0.98  --dbg_dump_prop_clauses_file            -
% 2.74/0.98  --dbg_out_stat                          false
% 2.74/0.98  
% 2.74/0.98  
% 2.74/0.98  
% 2.74/0.98  
% 2.74/0.98  ------ Proving...
% 2.74/0.98  
% 2.74/0.98  
% 2.74/0.98  % SZS status Theorem for theBenchmark.p
% 2.74/0.98  
% 2.74/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.74/0.98  
% 2.74/0.98  fof(f7,conjecture,(
% 2.74/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_partfun1(X1,X2) <=> ! [X3] : (r2_hidden(X3,k1_relset_1(X0,X0,X1)) => k1_funct_1(X1,X3) = k1_funct_1(X2,X3)))))),
% 2.74/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.98  
% 2.74/0.98  fof(f8,negated_conjecture,(
% 2.74/0.98    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_partfun1(X1,X2) <=> ! [X3] : (r2_hidden(X3,k1_relset_1(X0,X0,X1)) => k1_funct_1(X1,X3) = k1_funct_1(X2,X3)))))),
% 2.74/0.98    inference(negated_conjecture,[],[f7])).
% 2.74/0.98  
% 2.74/0.98  fof(f18,plain,(
% 2.74/0.98    ? [X0,X1] : (? [X2] : ((r1_partfun1(X1,X2) <~> ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relset_1(X0,X0,X1)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)))),
% 2.74/0.98    inference(ennf_transformation,[],[f8])).
% 2.74/0.98  
% 2.74/0.98  fof(f19,plain,(
% 2.74/0.98    ? [X0,X1] : (? [X2] : ((r1_partfun1(X1,X2) <~> ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relset_1(X0,X0,X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 2.74/0.98    inference(flattening,[],[f18])).
% 2.74/0.98  
% 2.74/0.98  fof(f25,plain,(
% 2.74/0.98    ? [X0,X1] : (? [X2] : (((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,X2)) & (! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 2.74/0.98    inference(nnf_transformation,[],[f19])).
% 2.74/0.98  
% 2.74/0.98  fof(f26,plain,(
% 2.74/0.98    ? [X0,X1] : (? [X2] : ((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,X2)) & (! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 2.74/0.98    inference(flattening,[],[f25])).
% 2.74/0.98  
% 2.74/0.98  fof(f27,plain,(
% 2.74/0.98    ? [X0,X1] : (? [X2] : ((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,X2)) & (! [X4] : (k1_funct_1(X1,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 2.74/0.98    inference(rectify,[],[f26])).
% 2.74/0.98  
% 2.74/0.98  fof(f30,plain,(
% 2.74/0.98    ( ! [X2,X0,X1] : (? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) => (k1_funct_1(X1,sK4) != k1_funct_1(X2,sK4) & r2_hidden(sK4,k1_relset_1(X0,X0,X1)))) )),
% 2.74/0.98    introduced(choice_axiom,[])).
% 2.74/0.98  
% 2.74/0.98  fof(f29,plain,(
% 2.74/0.98    ( ! [X0,X1] : (? [X2] : ((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,X2)) & (! [X4] : (k1_funct_1(X1,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((? [X3] : (k1_funct_1(sK3,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,sK3)) & (! [X4] : (k1_funct_1(sK3,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(sK3,X0,X0) & v1_funct_1(sK3))) )),
% 2.74/0.98    introduced(choice_axiom,[])).
% 2.74/0.98  
% 2.74/0.98  fof(f28,plain,(
% 2.74/0.98    ? [X0,X1] : (? [X2] : ((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,X2)) & (! [X4] : (k1_funct_1(X1,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => (? [X2] : ((? [X3] : (k1_funct_1(sK2,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(sK1,sK1,sK2))) | ~r1_partfun1(sK2,X2)) & (! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,k1_relset_1(sK1,sK1,sK2))) | r1_partfun1(sK2,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v1_funct_2(X2,sK1,sK1) & v1_funct_1(X2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v1_funct_1(sK2))),
% 2.74/0.98    introduced(choice_axiom,[])).
% 2.74/0.98  
% 2.74/0.98  fof(f31,plain,(
% 2.74/0.98    (((k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) & r2_hidden(sK4,k1_relset_1(sK1,sK1,sK2))) | ~r1_partfun1(sK2,sK3)) & (! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,k1_relset_1(sK1,sK1,sK2))) | r1_partfun1(sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v1_funct_2(sK3,sK1,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v1_funct_1(sK2)),
% 2.74/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f27,f30,f29,f28])).
% 2.74/0.98  
% 2.74/0.98  fof(f46,plain,(
% 2.74/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 2.74/0.98    inference(cnf_transformation,[],[f31])).
% 2.74/0.98  
% 2.74/0.98  fof(f4,axiom,(
% 2.74/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.74/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.98  
% 2.74/0.98  fof(f13,plain,(
% 2.74/0.98    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.74/0.98    inference(ennf_transformation,[],[f4])).
% 2.74/0.98  
% 2.74/0.98  fof(f35,plain,(
% 2.74/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.74/0.98    inference(cnf_transformation,[],[f13])).
% 2.74/0.98  
% 2.74/0.98  fof(f51,plain,(
% 2.74/0.98    r2_hidden(sK4,k1_relset_1(sK1,sK1,sK2)) | ~r1_partfun1(sK2,sK3)),
% 2.74/0.98    inference(cnf_transformation,[],[f31])).
% 2.74/0.98  
% 2.74/0.98  fof(f5,axiom,(
% 2.74/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.74/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.98  
% 2.74/0.98  fof(f14,plain,(
% 2.74/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.74/0.98    inference(ennf_transformation,[],[f5])).
% 2.74/0.98  
% 2.74/0.98  fof(f15,plain,(
% 2.74/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.74/0.98    inference(flattening,[],[f14])).
% 2.74/0.98  
% 2.74/0.98  fof(f20,plain,(
% 2.74/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.74/0.98    inference(nnf_transformation,[],[f15])).
% 2.74/0.98  
% 2.74/0.98  fof(f36,plain,(
% 2.74/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.74/0.98    inference(cnf_transformation,[],[f20])).
% 2.74/0.98  
% 2.74/0.98  fof(f48,plain,(
% 2.74/0.98    v1_funct_2(sK3,sK1,sK1)),
% 2.74/0.98    inference(cnf_transformation,[],[f31])).
% 2.74/0.98  
% 2.74/0.98  fof(f49,plain,(
% 2.74/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 2.74/0.98    inference(cnf_transformation,[],[f31])).
% 2.74/0.98  
% 2.74/0.98  fof(f1,axiom,(
% 2.74/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.74/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.98  
% 2.74/0.98  fof(f9,plain,(
% 2.74/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 2.74/0.98    inference(unused_predicate_definition_removal,[],[f1])).
% 2.74/0.98  
% 2.74/0.98  fof(f10,plain,(
% 2.74/0.98    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 2.74/0.98    inference(ennf_transformation,[],[f9])).
% 2.74/0.99  
% 2.74/0.99  fof(f32,plain,(
% 2.74/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.74/0.99    inference(cnf_transformation,[],[f10])).
% 2.74/0.99  
% 2.74/0.99  fof(f6,axiom,(
% 2.74/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) => (r1_partfun1(X0,X1) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2))))))),
% 2.74/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f16,plain,(
% 2.74/0.99    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.74/0.99    inference(ennf_transformation,[],[f6])).
% 2.74/0.99  
% 2.74/0.99  fof(f17,plain,(
% 2.74/0.99    ! [X0] : (! [X1] : ((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.74/0.99    inference(flattening,[],[f16])).
% 2.74/0.99  
% 2.74/0.99  fof(f21,plain,(
% 2.74/0.99    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0)))) & (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.74/0.99    inference(nnf_transformation,[],[f17])).
% 2.74/0.99  
% 2.74/0.99  fof(f22,plain,(
% 2.74/0.99    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0)))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.74/0.99    inference(rectify,[],[f21])).
% 2.74/0.99  
% 2.74/0.99  fof(f23,plain,(
% 2.74/0.99    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0))))),
% 2.74/0.99    introduced(choice_axiom,[])).
% 2.74/0.99  
% 2.74/0.99  fof(f24,plain,(
% 2.74/0.99    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0)))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.74/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 2.74/0.99  
% 2.74/0.99  fof(f43,plain,(
% 2.74/0.99    ( ! [X0,X1] : (r1_partfun1(X0,X1) | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.74/0.99    inference(cnf_transformation,[],[f24])).
% 2.74/0.99  
% 2.74/0.99  fof(f47,plain,(
% 2.74/0.99    v1_funct_1(sK3)),
% 2.74/0.99    inference(cnf_transformation,[],[f31])).
% 2.74/0.99  
% 2.74/0.99  fof(f2,axiom,(
% 2.74/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.74/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f11,plain,(
% 2.74/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.74/0.99    inference(ennf_transformation,[],[f2])).
% 2.74/0.99  
% 2.74/0.99  fof(f33,plain,(
% 2.74/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.74/0.99    inference(cnf_transformation,[],[f11])).
% 2.74/0.99  
% 2.74/0.99  fof(f50,plain,(
% 2.74/0.99    ( ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,k1_relset_1(sK1,sK1,sK2)) | r1_partfun1(sK2,sK3)) )),
% 2.74/0.99    inference(cnf_transformation,[],[f31])).
% 2.74/0.99  
% 2.74/0.99  fof(f45,plain,(
% 2.74/0.99    v1_funct_1(sK2)),
% 2.74/0.99    inference(cnf_transformation,[],[f31])).
% 2.74/0.99  
% 2.74/0.99  fof(f3,axiom,(
% 2.74/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.74/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f12,plain,(
% 2.74/0.99    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.74/0.99    inference(ennf_transformation,[],[f3])).
% 2.74/0.99  
% 2.74/0.99  fof(f34,plain,(
% 2.74/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.74/0.99    inference(cnf_transformation,[],[f12])).
% 2.74/0.99  
% 2.74/0.99  fof(f42,plain,(
% 2.74/0.99    ( ! [X0,X3,X1] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r1_partfun1(X0,X1) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.74/0.99    inference(cnf_transformation,[],[f24])).
% 2.74/0.99  
% 2.74/0.99  fof(f44,plain,(
% 2.74/0.99    ( ! [X0,X1] : (r1_partfun1(X0,X1) | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.74/0.99    inference(cnf_transformation,[],[f24])).
% 2.74/0.99  
% 2.74/0.99  fof(f52,plain,(
% 2.74/0.99    k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) | ~r1_partfun1(sK2,sK3)),
% 2.74/0.99    inference(cnf_transformation,[],[f31])).
% 2.74/0.99  
% 2.74/0.99  fof(f37,plain,(
% 2.74/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.74/0.99    inference(cnf_transformation,[],[f20])).
% 2.74/0.99  
% 2.74/0.99  fof(f57,plain,(
% 2.74/0.99    ( ! [X2,X1] : (k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0 | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.74/0.99    inference(equality_resolution,[],[f37])).
% 2.74/0.99  
% 2.74/0.99  cnf(c_19,negated_conjecture,
% 2.74/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 2.74/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1297,negated_conjecture,
% 2.74/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 2.74/0.99      inference(subtyping,[status(esa)],[c_19]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1622,plain,
% 2.74/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_1297]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3,plain,
% 2.74/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.74/0.99      inference(cnf_transformation,[],[f35]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1303,plain,
% 2.74/0.99      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
% 2.74/0.99      | k1_relset_1(X1_46,X2_46,X0_46) = k1_relat_1(X0_46) ),
% 2.74/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1616,plain,
% 2.74/0.99      ( k1_relset_1(X0_46,X1_46,X2_46) = k1_relat_1(X2_46)
% 2.74/0.99      | m1_subset_1(X2_46,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_1303]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1924,plain,
% 2.74/0.99      ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_1622,c_1616]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_14,negated_conjecture,
% 2.74/0.99      ( r2_hidden(sK4,k1_relset_1(sK1,sK1,sK2))
% 2.74/0.99      | ~ r1_partfun1(sK2,sK3) ),
% 2.74/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1301,negated_conjecture,
% 2.74/0.99      ( r2_hidden(sK4,k1_relset_1(sK1,sK1,sK2))
% 2.74/0.99      | ~ r1_partfun1(sK2,sK3) ),
% 2.74/0.99      inference(subtyping,[status(esa)],[c_14]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1618,plain,
% 2.74/0.99      ( r2_hidden(sK4,k1_relset_1(sK1,sK1,sK2)) = iProver_top
% 2.74/0.99      | r1_partfun1(sK2,sK3) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_1301]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2172,plain,
% 2.74/0.99      ( r2_hidden(sK4,k1_relat_1(sK2)) = iProver_top
% 2.74/0.99      | r1_partfun1(sK2,sK3) != iProver_top ),
% 2.74/0.99      inference(demodulation,[status(thm)],[c_1924,c_1618]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_9,plain,
% 2.74/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.74/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.74/0.99      | k1_xboole_0 = X2 ),
% 2.74/0.99      inference(cnf_transformation,[],[f36]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_17,negated_conjecture,
% 2.74/0.99      ( v1_funct_2(sK3,sK1,sK1) ),
% 2.74/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_522,plain,
% 2.74/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.74/0.99      | sK1 != X1
% 2.74/0.99      | sK1 != X2
% 2.74/0.99      | sK3 != X0
% 2.74/0.99      | k1_xboole_0 = X2 ),
% 2.74/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_17]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_523,plain,
% 2.74/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.74/0.99      | k1_relset_1(sK1,sK1,sK3) = sK1
% 2.74/0.99      | k1_xboole_0 = sK1 ),
% 2.74/0.99      inference(unflattening,[status(thm)],[c_522]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_16,negated_conjecture,
% 2.74/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 2.74/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_525,plain,
% 2.74/0.99      ( k1_relset_1(sK1,sK1,sK3) = sK1 | k1_xboole_0 = sK1 ),
% 2.74/0.99      inference(global_propositional_subsumption,
% 2.74/0.99                [status(thm)],
% 2.74/0.99                [c_523,c_16]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1290,plain,
% 2.74/0.99      ( k1_relset_1(sK1,sK1,sK3) = sK1 | k1_xboole_0 = sK1 ),
% 2.74/0.99      inference(subtyping,[status(esa)],[c_525]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1299,negated_conjecture,
% 2.74/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 2.74/0.99      inference(subtyping,[status(esa)],[c_16]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1620,plain,
% 2.74/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_1299]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1923,plain,
% 2.74/0.99      ( k1_relset_1(sK1,sK1,sK3) = k1_relat_1(sK3) ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_1620,c_1616]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2053,plain,
% 2.74/0.99      ( k1_relat_1(sK3) = sK1 | sK1 = k1_xboole_0 ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_1290,c_1923]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_0,plain,
% 2.74/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.74/0.99      inference(cnf_transformation,[],[f32]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_11,plain,
% 2.74/0.99      ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
% 2.74/0.99      | r1_partfun1(X0,X1)
% 2.74/0.99      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 2.74/0.99      | ~ v1_funct_1(X1)
% 2.74/0.99      | ~ v1_funct_1(X0)
% 2.74/0.99      | ~ v1_relat_1(X1)
% 2.74/0.99      | ~ v1_relat_1(X0) ),
% 2.74/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_236,plain,
% 2.74/0.99      ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
% 2.74/0.99      | r1_partfun1(X0,X1)
% 2.74/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 2.74/0.99      | ~ v1_funct_1(X0)
% 2.74/0.99      | ~ v1_funct_1(X1)
% 2.74/0.99      | ~ v1_relat_1(X0)
% 2.74/0.99      | ~ v1_relat_1(X1)
% 2.74/0.99      | k1_relat_1(X1) != X3
% 2.74/0.99      | k1_relat_1(X0) != X2 ),
% 2.74/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_11]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_237,plain,
% 2.74/0.99      ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
% 2.74/0.99      | r1_partfun1(X0,X1)
% 2.74/0.99      | ~ m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(k1_relat_1(X1)))
% 2.74/0.99      | ~ v1_funct_1(X1)
% 2.74/0.99      | ~ v1_funct_1(X0)
% 2.74/0.99      | ~ v1_relat_1(X1)
% 2.74/0.99      | ~ v1_relat_1(X0) ),
% 2.74/0.99      inference(unflattening,[status(thm)],[c_236]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1295,plain,
% 2.74/0.99      ( r2_hidden(sK0(X0_46,X1_46),k1_relat_1(X0_46))
% 2.74/0.99      | r1_partfun1(X0_46,X1_46)
% 2.74/0.99      | ~ m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(k1_relat_1(X1_46)))
% 2.74/0.99      | ~ v1_funct_1(X1_46)
% 2.74/0.99      | ~ v1_funct_1(X0_46)
% 2.74/0.99      | ~ v1_relat_1(X1_46)
% 2.74/0.99      | ~ v1_relat_1(X0_46) ),
% 2.74/0.99      inference(subtyping,[status(esa)],[c_237]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1624,plain,
% 2.74/0.99      ( r2_hidden(sK0(X0_46,X1_46),k1_relat_1(X0_46)) = iProver_top
% 2.74/0.99      | r1_partfun1(X0_46,X1_46) = iProver_top
% 2.74/0.99      | m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(k1_relat_1(X1_46))) != iProver_top
% 2.74/0.99      | v1_funct_1(X0_46) != iProver_top
% 2.74/0.99      | v1_funct_1(X1_46) != iProver_top
% 2.74/0.99      | v1_relat_1(X0_46) != iProver_top
% 2.74/0.99      | v1_relat_1(X1_46) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_1295]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2308,plain,
% 2.74/0.99      ( sK1 = k1_xboole_0
% 2.74/0.99      | r2_hidden(sK0(X0_46,sK3),k1_relat_1(X0_46)) = iProver_top
% 2.74/0.99      | r1_partfun1(X0_46,sK3) = iProver_top
% 2.74/0.99      | m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(sK1)) != iProver_top
% 2.74/0.99      | v1_funct_1(X0_46) != iProver_top
% 2.74/0.99      | v1_funct_1(sK3) != iProver_top
% 2.74/0.99      | v1_relat_1(X0_46) != iProver_top
% 2.74/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_2053,c_1624]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_18,negated_conjecture,
% 2.74/0.99      ( v1_funct_1(sK3) ),
% 2.74/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_23,plain,
% 2.74/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_25,plain,
% 2.74/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1,plain,
% 2.74/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/0.99      | v1_relat_1(X0) ),
% 2.74/0.99      inference(cnf_transformation,[],[f33]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1305,plain,
% 2.74/0.99      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
% 2.74/0.99      | v1_relat_1(X0_46) ),
% 2.74/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1763,plain,
% 2.74/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.74/0.99      | v1_relat_1(sK3) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_1305]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1764,plain,
% 2.74/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 2.74/0.99      | v1_relat_1(sK3) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_1763]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2620,plain,
% 2.74/0.99      ( v1_relat_1(X0_46) != iProver_top
% 2.74/0.99      | sK1 = k1_xboole_0
% 2.74/0.99      | r2_hidden(sK0(X0_46,sK3),k1_relat_1(X0_46)) = iProver_top
% 2.74/0.99      | r1_partfun1(X0_46,sK3) = iProver_top
% 2.74/0.99      | m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(sK1)) != iProver_top
% 2.74/0.99      | v1_funct_1(X0_46) != iProver_top ),
% 2.74/0.99      inference(global_propositional_subsumption,
% 2.74/0.99                [status(thm)],
% 2.74/0.99                [c_2308,c_23,c_25,c_1764]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2621,plain,
% 2.74/0.99      ( sK1 = k1_xboole_0
% 2.74/0.99      | r2_hidden(sK0(X0_46,sK3),k1_relat_1(X0_46)) = iProver_top
% 2.74/0.99      | r1_partfun1(X0_46,sK3) = iProver_top
% 2.74/0.99      | m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(sK1)) != iProver_top
% 2.74/0.99      | v1_funct_1(X0_46) != iProver_top
% 2.74/0.99      | v1_relat_1(X0_46) != iProver_top ),
% 2.74/0.99      inference(renaming,[status(thm)],[c_2620]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_15,negated_conjecture,
% 2.74/0.99      ( ~ r2_hidden(X0,k1_relset_1(sK1,sK1,sK2))
% 2.74/0.99      | r1_partfun1(sK2,sK3)
% 2.74/0.99      | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) ),
% 2.74/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1300,negated_conjecture,
% 2.74/0.99      ( ~ r2_hidden(X0_48,k1_relset_1(sK1,sK1,sK2))
% 2.74/0.99      | r1_partfun1(sK2,sK3)
% 2.74/0.99      | k1_funct_1(sK2,X0_48) = k1_funct_1(sK3,X0_48) ),
% 2.74/0.99      inference(subtyping,[status(esa)],[c_15]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1619,plain,
% 2.74/0.99      ( k1_funct_1(sK2,X0_48) = k1_funct_1(sK3,X0_48)
% 2.74/0.99      | r2_hidden(X0_48,k1_relset_1(sK1,sK1,sK2)) != iProver_top
% 2.74/0.99      | r1_partfun1(sK2,sK3) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_1300]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2171,plain,
% 2.74/0.99      ( k1_funct_1(sK3,X0_48) = k1_funct_1(sK2,X0_48)
% 2.74/0.99      | r2_hidden(X0_48,k1_relat_1(sK2)) != iProver_top
% 2.74/0.99      | r1_partfun1(sK2,sK3) = iProver_top ),
% 2.74/0.99      inference(demodulation,[status(thm)],[c_1924,c_1619]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2633,plain,
% 2.74/0.99      ( k1_funct_1(sK2,sK0(sK2,sK3)) = k1_funct_1(sK3,sK0(sK2,sK3))
% 2.74/0.99      | sK1 = k1_xboole_0
% 2.74/0.99      | r1_partfun1(sK2,sK3) = iProver_top
% 2.74/0.99      | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) != iProver_top
% 2.74/0.99      | v1_funct_1(sK2) != iProver_top
% 2.74/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_2621,c_2171]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_20,negated_conjecture,
% 2.74/0.99      ( v1_funct_1(sK2) ),
% 2.74/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_21,plain,
% 2.74/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_22,plain,
% 2.74/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1766,plain,
% 2.74/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.74/0.99      | v1_relat_1(sK2) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_1305]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1767,plain,
% 2.74/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 2.74/0.99      | v1_relat_1(sK2) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_1766]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2,plain,
% 2.74/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/0.99      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 2.74/0.99      inference(cnf_transformation,[],[f34]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1304,plain,
% 2.74/0.99      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
% 2.74/0.99      | m1_subset_1(k1_relset_1(X1_46,X2_46,X0_46),k1_zfmisc_1(X1_46)) ),
% 2.74/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1615,plain,
% 2.74/0.99      ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46))) != iProver_top
% 2.74/0.99      | m1_subset_1(k1_relset_1(X1_46,X2_46,X0_46),k1_zfmisc_1(X1_46)) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_1304]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2187,plain,
% 2.74/0.99      ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top
% 2.74/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_1924,c_1615]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2693,plain,
% 2.74/0.99      ( r1_partfun1(sK2,sK3) = iProver_top
% 2.74/0.99      | sK1 = k1_xboole_0
% 2.74/0.99      | k1_funct_1(sK2,sK0(sK2,sK3)) = k1_funct_1(sK3,sK0(sK2,sK3)) ),
% 2.74/0.99      inference(global_propositional_subsumption,
% 2.74/0.99                [status(thm)],
% 2.74/0.99                [c_2633,c_21,c_22,c_1767,c_2187]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2694,plain,
% 2.74/0.99      ( k1_funct_1(sK2,sK0(sK2,sK3)) = k1_funct_1(sK3,sK0(sK2,sK3))
% 2.74/0.99      | sK1 = k1_xboole_0
% 2.74/0.99      | r1_partfun1(sK2,sK3) = iProver_top ),
% 2.74/0.99      inference(renaming,[status(thm)],[c_2693]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2382,plain,
% 2.74/0.99      ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top ),
% 2.74/0.99      inference(global_propositional_subsumption,
% 2.74/0.99                [status(thm)],
% 2.74/0.99                [c_2187,c_22]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_12,plain,
% 2.74/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.74/0.99      | ~ r1_partfun1(X1,X2)
% 2.74/0.99      | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
% 2.74/0.99      | ~ v1_funct_1(X2)
% 2.74/0.99      | ~ v1_funct_1(X1)
% 2.74/0.99      | ~ v1_relat_1(X2)
% 2.74/0.99      | ~ v1_relat_1(X1)
% 2.74/0.99      | k1_funct_1(X2,X0) = k1_funct_1(X1,X0) ),
% 2.74/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_290,plain,
% 2.74/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.74/0.99      | ~ r1_partfun1(X1,X2)
% 2.74/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
% 2.74/0.99      | ~ v1_funct_1(X1)
% 2.74/0.99      | ~ v1_funct_1(X2)
% 2.74/0.99      | ~ v1_relat_1(X1)
% 2.74/0.99      | ~ v1_relat_1(X2)
% 2.74/0.99      | k1_funct_1(X1,X0) = k1_funct_1(X2,X0)
% 2.74/0.99      | k1_relat_1(X2) != X4
% 2.74/0.99      | k1_relat_1(X1) != X3 ),
% 2.74/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_12]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_291,plain,
% 2.74/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.74/0.99      | ~ r1_partfun1(X1,X2)
% 2.74/0.99      | ~ m1_subset_1(k1_relat_1(X1),k1_zfmisc_1(k1_relat_1(X2)))
% 2.74/0.99      | ~ v1_funct_1(X1)
% 2.74/0.99      | ~ v1_funct_1(X2)
% 2.74/0.99      | ~ v1_relat_1(X1)
% 2.74/0.99      | ~ v1_relat_1(X2)
% 2.74/0.99      | k1_funct_1(X1,X0) = k1_funct_1(X2,X0) ),
% 2.74/0.99      inference(unflattening,[status(thm)],[c_290]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1293,plain,
% 2.74/0.99      ( ~ r2_hidden(X0_48,k1_relat_1(X0_46))
% 2.74/0.99      | ~ r1_partfun1(X0_46,X1_46)
% 2.74/0.99      | ~ m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(k1_relat_1(X1_46)))
% 2.74/0.99      | ~ v1_funct_1(X1_46)
% 2.74/0.99      | ~ v1_funct_1(X0_46)
% 2.74/0.99      | ~ v1_relat_1(X1_46)
% 2.74/0.99      | ~ v1_relat_1(X0_46)
% 2.74/0.99      | k1_funct_1(X0_46,X0_48) = k1_funct_1(X1_46,X0_48) ),
% 2.74/0.99      inference(subtyping,[status(esa)],[c_291]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1626,plain,
% 2.74/0.99      ( k1_funct_1(X0_46,X0_48) = k1_funct_1(X1_46,X0_48)
% 2.74/0.99      | r2_hidden(X0_48,k1_relat_1(X0_46)) != iProver_top
% 2.74/0.99      | r1_partfun1(X0_46,X1_46) != iProver_top
% 2.74/0.99      | m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(k1_relat_1(X1_46))) != iProver_top
% 2.74/0.99      | v1_funct_1(X0_46) != iProver_top
% 2.74/0.99      | v1_funct_1(X1_46) != iProver_top
% 2.74/0.99      | v1_relat_1(X0_46) != iProver_top
% 2.74/0.99      | v1_relat_1(X1_46) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_1293]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3009,plain,
% 2.74/0.99      ( k1_funct_1(X0_46,X0_48) = k1_funct_1(sK3,X0_48)
% 2.74/0.99      | sK1 = k1_xboole_0
% 2.74/0.99      | r2_hidden(X0_48,k1_relat_1(X0_46)) != iProver_top
% 2.74/0.99      | r1_partfun1(X0_46,sK3) != iProver_top
% 2.74/0.99      | m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(sK1)) != iProver_top
% 2.74/0.99      | v1_funct_1(X0_46) != iProver_top
% 2.74/0.99      | v1_funct_1(sK3) != iProver_top
% 2.74/0.99      | v1_relat_1(X0_46) != iProver_top
% 2.74/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_2053,c_1626]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3133,plain,
% 2.74/0.99      ( v1_relat_1(X0_46) != iProver_top
% 2.74/0.99      | k1_funct_1(X0_46,X0_48) = k1_funct_1(sK3,X0_48)
% 2.74/0.99      | sK1 = k1_xboole_0
% 2.74/0.99      | r2_hidden(X0_48,k1_relat_1(X0_46)) != iProver_top
% 2.74/0.99      | r1_partfun1(X0_46,sK3) != iProver_top
% 2.74/0.99      | m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(sK1)) != iProver_top
% 2.74/0.99      | v1_funct_1(X0_46) != iProver_top ),
% 2.74/0.99      inference(global_propositional_subsumption,
% 2.74/0.99                [status(thm)],
% 2.74/0.99                [c_3009,c_23,c_25,c_1764]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3134,plain,
% 2.74/0.99      ( k1_funct_1(X0_46,X0_48) = k1_funct_1(sK3,X0_48)
% 2.74/0.99      | sK1 = k1_xboole_0
% 2.74/0.99      | r2_hidden(X0_48,k1_relat_1(X0_46)) != iProver_top
% 2.74/0.99      | r1_partfun1(X0_46,sK3) != iProver_top
% 2.74/0.99      | m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(sK1)) != iProver_top
% 2.74/0.99      | v1_funct_1(X0_46) != iProver_top
% 2.74/0.99      | v1_relat_1(X0_46) != iProver_top ),
% 2.74/0.99      inference(renaming,[status(thm)],[c_3133]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3147,plain,
% 2.74/0.99      ( k1_funct_1(sK3,X0_48) = k1_funct_1(sK2,X0_48)
% 2.74/0.99      | sK1 = k1_xboole_0
% 2.74/0.99      | r2_hidden(X0_48,k1_relat_1(sK2)) != iProver_top
% 2.74/0.99      | r1_partfun1(sK2,sK3) != iProver_top
% 2.74/0.99      | v1_funct_1(sK2) != iProver_top
% 2.74/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_2382,c_3134]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3165,plain,
% 2.74/0.99      ( r2_hidden(X0_48,k1_relat_1(sK2)) != iProver_top
% 2.74/0.99      | sK1 = k1_xboole_0
% 2.74/0.99      | k1_funct_1(sK3,X0_48) = k1_funct_1(sK2,X0_48) ),
% 2.74/0.99      inference(global_propositional_subsumption,
% 2.74/0.99                [status(thm)],
% 2.74/0.99                [c_3147,c_21,c_22,c_1767,c_2171]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3166,plain,
% 2.74/0.99      ( k1_funct_1(sK3,X0_48) = k1_funct_1(sK2,X0_48)
% 2.74/0.99      | sK1 = k1_xboole_0
% 2.74/0.99      | r2_hidden(X0_48,k1_relat_1(sK2)) != iProver_top ),
% 2.74/0.99      inference(renaming,[status(thm)],[c_3165]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3175,plain,
% 2.74/0.99      ( k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4)
% 2.74/0.99      | sK1 = k1_xboole_0
% 2.74/0.99      | r1_partfun1(sK2,sK3) != iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_2172,c_3166]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3251,plain,
% 2.74/0.99      ( k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4)
% 2.74/0.99      | k1_funct_1(sK2,sK0(sK2,sK3)) = k1_funct_1(sK3,sK0(sK2,sK3))
% 2.74/0.99      | sK1 = k1_xboole_0 ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_2694,c_3175]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_10,plain,
% 2.74/0.99      ( r1_partfun1(X0,X1)
% 2.74/0.99      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 2.74/0.99      | ~ v1_funct_1(X1)
% 2.74/0.99      | ~ v1_funct_1(X0)
% 2.74/0.99      | ~ v1_relat_1(X1)
% 2.74/0.99      | ~ v1_relat_1(X0)
% 2.74/0.99      | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1)) ),
% 2.74/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_263,plain,
% 2.74/0.99      ( r1_partfun1(X0,X1)
% 2.74/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 2.74/0.99      | ~ v1_funct_1(X0)
% 2.74/0.99      | ~ v1_funct_1(X1)
% 2.74/0.99      | ~ v1_relat_1(X0)
% 2.74/0.99      | ~ v1_relat_1(X1)
% 2.74/0.99      | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
% 2.74/0.99      | k1_relat_1(X1) != X3
% 2.74/0.99      | k1_relat_1(X0) != X2 ),
% 2.74/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_10]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_264,plain,
% 2.74/0.99      ( r1_partfun1(X0,X1)
% 2.74/0.99      | ~ m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(k1_relat_1(X1)))
% 2.74/0.99      | ~ v1_funct_1(X1)
% 2.74/0.99      | ~ v1_funct_1(X0)
% 2.74/0.99      | ~ v1_relat_1(X1)
% 2.74/0.99      | ~ v1_relat_1(X0)
% 2.74/0.99      | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) ),
% 2.74/0.99      inference(unflattening,[status(thm)],[c_263]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1294,plain,
% 2.74/0.99      ( r1_partfun1(X0_46,X1_46)
% 2.74/0.99      | ~ m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(k1_relat_1(X1_46)))
% 2.74/0.99      | ~ v1_funct_1(X1_46)
% 2.74/0.99      | ~ v1_funct_1(X0_46)
% 2.74/0.99      | ~ v1_relat_1(X1_46)
% 2.74/0.99      | ~ v1_relat_1(X0_46)
% 2.74/0.99      | k1_funct_1(X0_46,sK0(X0_46,X1_46)) != k1_funct_1(X1_46,sK0(X0_46,X1_46)) ),
% 2.74/0.99      inference(subtyping,[status(esa)],[c_264]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1625,plain,
% 2.74/0.99      ( k1_funct_1(X0_46,sK0(X0_46,X1_46)) != k1_funct_1(X1_46,sK0(X0_46,X1_46))
% 2.74/0.99      | r1_partfun1(X0_46,X1_46) = iProver_top
% 2.74/0.99      | m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(k1_relat_1(X1_46))) != iProver_top
% 2.74/0.99      | v1_funct_1(X0_46) != iProver_top
% 2.74/0.99      | v1_funct_1(X1_46) != iProver_top
% 2.74/0.99      | v1_relat_1(X0_46) != iProver_top
% 2.74/0.99      | v1_relat_1(X1_46) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_1294]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3392,plain,
% 2.74/0.99      ( k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4)
% 2.74/0.99      | sK1 = k1_xboole_0
% 2.74/0.99      | r1_partfun1(sK2,sK3) = iProver_top
% 2.74/0.99      | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_relat_1(sK3))) != iProver_top
% 2.74/0.99      | v1_funct_1(sK3) != iProver_top
% 2.74/0.99      | v1_funct_1(sK2) != iProver_top
% 2.74/0.99      | v1_relat_1(sK3) != iProver_top
% 2.74/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_3251,c_1625]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1816,plain,
% 2.74/0.99      ( r1_partfun1(X0_46,sK3)
% 2.74/0.99      | ~ m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(k1_relat_1(sK3)))
% 2.74/0.99      | ~ v1_funct_1(X0_46)
% 2.74/0.99      | ~ v1_funct_1(sK3)
% 2.74/0.99      | ~ v1_relat_1(X0_46)
% 2.74/0.99      | ~ v1_relat_1(sK3)
% 2.74/0.99      | k1_funct_1(X0_46,sK0(X0_46,sK3)) != k1_funct_1(sK3,sK0(X0_46,sK3)) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_1294]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1885,plain,
% 2.74/0.99      ( r1_partfun1(sK2,sK3)
% 2.74/0.99      | ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_relat_1(sK3)))
% 2.74/0.99      | ~ v1_funct_1(sK3)
% 2.74/0.99      | ~ v1_funct_1(sK2)
% 2.74/0.99      | ~ v1_relat_1(sK3)
% 2.74/0.99      | ~ v1_relat_1(sK2)
% 2.74/0.99      | k1_funct_1(sK2,sK0(sK2,sK3)) != k1_funct_1(sK3,sK0(sK2,sK3)) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_1816]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1886,plain,
% 2.74/0.99      ( k1_funct_1(sK2,sK0(sK2,sK3)) != k1_funct_1(sK3,sK0(sK2,sK3))
% 2.74/0.99      | r1_partfun1(sK2,sK3) = iProver_top
% 2.74/0.99      | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_relat_1(sK3))) != iProver_top
% 2.74/0.99      | v1_funct_1(sK3) != iProver_top
% 2.74/0.99      | v1_funct_1(sK2) != iProver_top
% 2.74/0.99      | v1_relat_1(sK3) != iProver_top
% 2.74/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_1885]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3395,plain,
% 2.74/0.99      ( sK1 = k1_xboole_0
% 2.74/0.99      | r1_partfun1(sK2,sK3) = iProver_top
% 2.74/0.99      | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_relat_1(sK3))) != iProver_top ),
% 2.74/0.99      inference(global_propositional_subsumption,
% 2.74/0.99                [status(thm)],
% 2.74/0.99                [c_3392,c_21,c_22,c_23,c_25,c_1764,c_1767,c_1886,c_2187,
% 2.74/0.99                 c_2633]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3402,plain,
% 2.74/0.99      ( sK1 = k1_xboole_0
% 2.74/0.99      | r1_partfun1(sK2,sK3) = iProver_top
% 2.74/0.99      | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) != iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_2053,c_3395]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3425,plain,
% 2.74/0.99      ( r1_partfun1(sK2,sK3) = iProver_top | sK1 = k1_xboole_0 ),
% 2.74/0.99      inference(global_propositional_subsumption,
% 2.74/0.99                [status(thm)],
% 2.74/0.99                [c_3402,c_22,c_2187]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3426,plain,
% 2.74/0.99      ( sK1 = k1_xboole_0 | r1_partfun1(sK2,sK3) = iProver_top ),
% 2.74/0.99      inference(renaming,[status(thm)],[c_3425]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3431,plain,
% 2.74/0.99      ( k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4) | sK1 = k1_xboole_0 ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_3426,c_3175]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_13,negated_conjecture,
% 2.74/0.99      ( ~ r1_partfun1(sK2,sK3)
% 2.74/0.99      | k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) ),
% 2.74/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1302,negated_conjecture,
% 2.74/0.99      ( ~ r1_partfun1(sK2,sK3)
% 2.74/0.99      | k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) ),
% 2.74/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1617,plain,
% 2.74/0.99      ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
% 2.74/0.99      | r1_partfun1(sK2,sK3) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_1302]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3434,plain,
% 2.74/0.99      ( sK1 = k1_xboole_0 | r1_partfun1(sK2,sK3) != iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_3431,c_1617]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3562,plain,
% 2.74/0.99      ( sK1 = k1_xboole_0 ),
% 2.74/0.99      inference(global_propositional_subsumption,
% 2.74/0.99                [status(thm)],
% 2.74/0.99                [c_3434,c_22,c_2187,c_3402]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3570,plain,
% 2.74/0.99      ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.74/0.99      inference(demodulation,[status(thm)],[c_3562,c_2382]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_8,plain,
% 2.74/0.99      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.74/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.74/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.74/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_509,plain,
% 2.74/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.74/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 2.74/0.99      | sK1 != X1
% 2.74/0.99      | sK1 != k1_xboole_0
% 2.74/0.99      | sK3 != X0 ),
% 2.74/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_17]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_510,plain,
% 2.74/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 2.74/0.99      | k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 2.74/0.99      | sK1 != k1_xboole_0 ),
% 2.74/0.99      inference(unflattening,[status(thm)],[c_509]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1291,plain,
% 2.74/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 2.74/0.99      | k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 2.74/0.99      | sK1 != k1_xboole_0 ),
% 2.74/0.99      inference(subtyping,[status(esa)],[c_510]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1628,plain,
% 2.74/0.99      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 2.74/0.99      | sK1 != k1_xboole_0
% 2.74/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_1291]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3573,plain,
% 2.74/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 2.74/0.99      | k1_xboole_0 != k1_xboole_0
% 2.74/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 2.74/0.99      inference(demodulation,[status(thm)],[c_3562,c_1628]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3587,plain,
% 2.74/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 2.74/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 2.74/0.99      inference(equality_resolution_simp,[status(thm)],[c_3573]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3575,plain,
% 2.74/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
% 2.74/0.99      inference(demodulation,[status(thm)],[c_3562,c_1923]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3588,plain,
% 2.74/0.99      ( k1_relat_1(sK3) = k1_xboole_0
% 2.74/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 2.74/0.99      inference(demodulation,[status(thm)],[c_3587,c_3575]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3578,plain,
% 2.74/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 2.74/0.99      inference(demodulation,[status(thm)],[c_3562,c_1620]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3591,plain,
% 2.74/0.99      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 2.74/0.99      inference(forward_subsumption_resolution,
% 2.74/0.99                [status(thm)],
% 2.74/0.99                [c_3588,c_3578]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3672,plain,
% 2.74/0.99      ( k1_funct_1(X0_46,X0_48) = k1_funct_1(sK3,X0_48)
% 2.74/0.99      | r2_hidden(X0_48,k1_relat_1(X0_46)) != iProver_top
% 2.74/0.99      | r1_partfun1(X0_46,sK3) != iProver_top
% 2.74/0.99      | m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.74/0.99      | v1_funct_1(X0_46) != iProver_top
% 2.74/0.99      | v1_funct_1(sK3) != iProver_top
% 2.74/0.99      | v1_relat_1(X0_46) != iProver_top
% 2.74/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_3591,c_1626]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4364,plain,
% 2.74/0.99      ( v1_relat_1(X0_46) != iProver_top
% 2.74/0.99      | k1_funct_1(X0_46,X0_48) = k1_funct_1(sK3,X0_48)
% 2.74/0.99      | r2_hidden(X0_48,k1_relat_1(X0_46)) != iProver_top
% 2.74/0.99      | r1_partfun1(X0_46,sK3) != iProver_top
% 2.74/0.99      | m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.74/0.99      | v1_funct_1(X0_46) != iProver_top ),
% 2.74/0.99      inference(global_propositional_subsumption,
% 2.74/0.99                [status(thm)],
% 2.74/0.99                [c_3672,c_23,c_25,c_1764]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4365,plain,
% 2.74/0.99      ( k1_funct_1(X0_46,X0_48) = k1_funct_1(sK3,X0_48)
% 2.74/0.99      | r2_hidden(X0_48,k1_relat_1(X0_46)) != iProver_top
% 2.74/0.99      | r1_partfun1(X0_46,sK3) != iProver_top
% 2.74/0.99      | m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.74/0.99      | v1_funct_1(X0_46) != iProver_top
% 2.74/0.99      | v1_relat_1(X0_46) != iProver_top ),
% 2.74/0.99      inference(renaming,[status(thm)],[c_4364]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4376,plain,
% 2.74/0.99      ( k1_funct_1(sK3,X0_48) = k1_funct_1(sK2,X0_48)
% 2.74/0.99      | r2_hidden(X0_48,k1_relat_1(sK2)) != iProver_top
% 2.74/0.99      | r1_partfun1(sK2,sK3) != iProver_top
% 2.74/0.99      | v1_funct_1(sK2) != iProver_top
% 2.74/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_3570,c_4365]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3673,plain,
% 2.74/0.99      ( r2_hidden(sK0(X0_46,sK3),k1_relat_1(X0_46)) = iProver_top
% 2.74/0.99      | r1_partfun1(X0_46,sK3) = iProver_top
% 2.74/0.99      | m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.74/0.99      | v1_funct_1(X0_46) != iProver_top
% 2.74/0.99      | v1_funct_1(sK3) != iProver_top
% 2.74/0.99      | v1_relat_1(X0_46) != iProver_top
% 2.74/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_3591,c_1624]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4453,plain,
% 2.74/0.99      ( v1_relat_1(X0_46) != iProver_top
% 2.74/0.99      | r2_hidden(sK0(X0_46,sK3),k1_relat_1(X0_46)) = iProver_top
% 2.74/0.99      | r1_partfun1(X0_46,sK3) = iProver_top
% 2.74/0.99      | m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.74/0.99      | v1_funct_1(X0_46) != iProver_top ),
% 2.74/0.99      inference(global_propositional_subsumption,
% 2.74/0.99                [status(thm)],
% 2.74/0.99                [c_3673,c_23,c_25,c_1764]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4454,plain,
% 2.74/0.99      ( r2_hidden(sK0(X0_46,sK3),k1_relat_1(X0_46)) = iProver_top
% 2.74/0.99      | r1_partfun1(X0_46,sK3) = iProver_top
% 2.74/0.99      | m1_subset_1(k1_relat_1(X0_46),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.74/0.99      | v1_funct_1(X0_46) != iProver_top
% 2.74/0.99      | v1_relat_1(X0_46) != iProver_top ),
% 2.74/0.99      inference(renaming,[status(thm)],[c_4453]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4465,plain,
% 2.74/0.99      ( k1_funct_1(sK2,sK0(sK2,sK3)) = k1_funct_1(sK3,sK0(sK2,sK3))
% 2.74/0.99      | r1_partfun1(sK2,sK3) = iProver_top
% 2.74/0.99      | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.74/0.99      | v1_funct_1(sK2) != iProver_top
% 2.74/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_4454,c_2171]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1307,plain,( X0_46 = X0_46 ),theory(equality) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1330,plain,
% 2.74/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_1307]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1783,plain,
% 2.74/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.74/0.99      | k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_1303]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1793,plain,
% 2.74/0.99      ( m1_subset_1(k1_relset_1(sK1,sK1,sK2),k1_zfmisc_1(sK1))
% 2.74/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_1304]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1794,plain,
% 2.74/0.99      ( m1_subset_1(k1_relset_1(sK1,sK1,sK2),k1_zfmisc_1(sK1)) = iProver_top
% 2.74/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_1793]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1313,plain,
% 2.74/0.99      ( k1_zfmisc_1(X0_46) = k1_zfmisc_1(X1_46) | X0_46 != X1_46 ),
% 2.74/0.99      theory(equality) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1951,plain,
% 2.74/0.99      ( k1_zfmisc_1(X0_46) = k1_zfmisc_1(sK1) | X0_46 != sK1 ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_1313]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1956,plain,
% 2.74/0.99      ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(sK1)
% 2.74/0.99      | k1_xboole_0 != sK1 ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_1951]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1311,plain,
% 2.74/0.99      ( X0_46 != X1_46 | X2_46 != X1_46 | X2_46 = X0_46 ),
% 2.74/0.99      theory(equality) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2291,plain,
% 2.74/0.99      ( X0_46 != X1_46 | X0_46 = sK1 | sK1 != X1_46 ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_1311]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2292,plain,
% 2.74/0.99      ( sK1 != k1_xboole_0
% 2.74/0.99      | k1_xboole_0 = sK1
% 2.74/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_2291]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2247,plain,
% 2.74/0.99      ( X0_46 != X1_46
% 2.74/0.99      | X0_46 = k1_relset_1(sK1,sK1,sK2)
% 2.74/0.99      | k1_relset_1(sK1,sK1,sK2) != X1_46 ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_1311]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2556,plain,
% 2.74/0.99      ( X0_46 = k1_relset_1(sK1,sK1,sK2)
% 2.74/0.99      | X0_46 != k1_relat_1(sK2)
% 2.74/0.99      | k1_relset_1(sK1,sK1,sK2) != k1_relat_1(sK2) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_2247]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2703,plain,
% 2.74/0.99      ( k1_relset_1(sK1,sK1,sK2) != k1_relat_1(sK2)
% 2.74/0.99      | k1_relat_1(sK2) = k1_relset_1(sK1,sK1,sK2)
% 2.74/0.99      | k1_relat_1(sK2) != k1_relat_1(sK2) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_2556]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2704,plain,
% 2.74/0.99      ( k1_relat_1(sK2) = k1_relat_1(sK2) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_1307]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1314,plain,
% 2.74/0.99      ( ~ m1_subset_1(X0_46,X0_47)
% 2.74/0.99      | m1_subset_1(X1_46,X1_47)
% 2.74/0.99      | X1_47 != X0_47
% 2.74/0.99      | X1_46 != X0_46 ),
% 2.74/0.99      theory(equality) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1837,plain,
% 2.74/0.99      ( m1_subset_1(X0_46,X0_47)
% 2.74/0.99      | ~ m1_subset_1(k1_relset_1(sK1,sK1,sK2),k1_zfmisc_1(sK1))
% 2.74/0.99      | X0_47 != k1_zfmisc_1(sK1)
% 2.74/0.99      | X0_46 != k1_relset_1(sK1,sK1,sK2) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_1314]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2142,plain,
% 2.74/0.99      ( m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
% 2.74/0.99      | ~ m1_subset_1(k1_relset_1(sK1,sK1,sK2),k1_zfmisc_1(sK1))
% 2.74/0.99      | k1_zfmisc_1(X1_46) != k1_zfmisc_1(sK1)
% 2.74/0.99      | X0_46 != k1_relset_1(sK1,sK1,sK2) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_1837]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3190,plain,
% 2.74/0.99      ( ~ m1_subset_1(k1_relset_1(sK1,sK1,sK2),k1_zfmisc_1(sK1))
% 2.74/0.99      | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(X0_46))
% 2.74/0.99      | k1_zfmisc_1(X0_46) != k1_zfmisc_1(sK1)
% 2.74/0.99      | k1_relat_1(sK2) != k1_relset_1(sK1,sK1,sK2) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_2142]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3194,plain,
% 2.74/0.99      ( k1_zfmisc_1(X0_46) != k1_zfmisc_1(sK1)
% 2.74/0.99      | k1_relat_1(sK2) != k1_relset_1(sK1,sK1,sK2)
% 2.74/0.99      | m1_subset_1(k1_relset_1(sK1,sK1,sK2),k1_zfmisc_1(sK1)) != iProver_top
% 2.74/0.99      | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(X0_46)) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_3190]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3196,plain,
% 2.74/0.99      ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(sK1)
% 2.74/0.99      | k1_relat_1(sK2) != k1_relset_1(sK1,sK1,sK2)
% 2.74/0.99      | m1_subset_1(k1_relset_1(sK1,sK1,sK2),k1_zfmisc_1(sK1)) != iProver_top
% 2.74/0.99      | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_3194]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3529,plain,
% 2.74/0.99      ( k1_relat_1(sK3) != X0_46 | k1_relat_1(sK3) = sK1 | sK1 != X0_46 ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_2291]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3531,plain,
% 2.74/0.99      ( k1_relat_1(sK3) = sK1
% 2.74/0.99      | k1_relat_1(sK3) != k1_xboole_0
% 2.74/0.99      | sK1 != k1_xboole_0 ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_3529]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3941,plain,
% 2.74/0.99      ( ~ m1_subset_1(k1_relset_1(sK1,sK1,sK2),k1_zfmisc_1(sK1))
% 2.74/0.99      | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_relat_1(sK3)))
% 2.74/0.99      | k1_zfmisc_1(k1_relat_1(sK3)) != k1_zfmisc_1(sK1)
% 2.74/0.99      | k1_relat_1(sK2) != k1_relset_1(sK1,sK1,sK2) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_3190]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3942,plain,
% 2.74/0.99      ( k1_zfmisc_1(k1_relat_1(sK3)) != k1_zfmisc_1(sK1)
% 2.74/0.99      | k1_relat_1(sK2) != k1_relset_1(sK1,sK1,sK2)
% 2.74/0.99      | m1_subset_1(k1_relset_1(sK1,sK1,sK2),k1_zfmisc_1(sK1)) != iProver_top
% 2.74/0.99      | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_relat_1(sK3))) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_3941]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4330,plain,
% 2.74/0.99      ( k1_zfmisc_1(k1_relat_1(sK3)) = k1_zfmisc_1(sK1)
% 2.74/0.99      | k1_relat_1(sK3) != sK1 ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_1951]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4767,plain,
% 2.74/0.99      ( r1_partfun1(sK2,sK3) = iProver_top ),
% 2.74/0.99      inference(global_propositional_subsumption,
% 2.74/0.99                [status(thm)],
% 2.74/0.99                [c_4465,c_21,c_19,c_22,c_23,c_25,c_1330,c_1764,c_1767,
% 2.74/0.99                 c_1783,c_1794,c_1886,c_1956,c_2187,c_2292,c_2703,c_2704,
% 2.74/0.99                 c_3196,c_3402,c_3434,c_3531,c_3591,c_3942,c_4330]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4841,plain,
% 2.74/0.99      ( r2_hidden(X0_48,k1_relat_1(sK2)) != iProver_top
% 2.74/0.99      | k1_funct_1(sK3,X0_48) = k1_funct_1(sK2,X0_48) ),
% 2.74/0.99      inference(global_propositional_subsumption,
% 2.74/0.99                [status(thm)],
% 2.74/0.99                [c_4376,c_21,c_19,c_22,c_23,c_25,c_1330,c_1764,c_1767,
% 2.74/0.99                 c_1783,c_1794,c_1886,c_1956,c_2187,c_2292,c_2703,c_2704,
% 2.74/0.99                 c_3196,c_3402,c_3434,c_3531,c_3591,c_3942,c_4330,c_4465]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4842,plain,
% 2.74/0.99      ( k1_funct_1(sK3,X0_48) = k1_funct_1(sK2,X0_48)
% 2.74/0.99      | r2_hidden(X0_48,k1_relat_1(sK2)) != iProver_top ),
% 2.74/0.99      inference(renaming,[status(thm)],[c_4841]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4850,plain,
% 2.74/0.99      ( k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4)
% 2.74/0.99      | r1_partfun1(sK2,sK3) != iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_2172,c_4842]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4389,plain,
% 2.74/0.99      ( k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4)
% 2.74/0.99      | r2_hidden(sK4,k1_relat_1(sK2)) != iProver_top
% 2.74/0.99      | r1_partfun1(sK2,sK3) != iProver_top
% 2.74/0.99      | v1_funct_1(sK2) != iProver_top
% 2.74/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_4376]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4857,plain,
% 2.74/0.99      ( k1_funct_1(sK3,sK4) = k1_funct_1(sK2,sK4) ),
% 2.74/0.99      inference(global_propositional_subsumption,
% 2.74/0.99                [status(thm)],
% 2.74/0.99                [c_4850,c_21,c_19,c_22,c_23,c_25,c_1330,c_1764,c_1767,
% 2.74/0.99                 c_1783,c_1794,c_1886,c_1956,c_2172,c_2187,c_2292,c_2703,
% 2.74/0.99                 c_2704,c_3196,c_3402,c_3434,c_3531,c_3591,c_3942,c_4330,
% 2.74/0.99                 c_4389,c_4465]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4860,plain,
% 2.74/0.99      ( k1_funct_1(sK2,sK4) != k1_funct_1(sK2,sK4)
% 2.74/0.99      | r1_partfun1(sK2,sK3) != iProver_top ),
% 2.74/0.99      inference(demodulation,[status(thm)],[c_4857,c_1617]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4997,plain,
% 2.74/0.99      ( r1_partfun1(sK2,sK3) != iProver_top ),
% 2.74/0.99      inference(equality_resolution_simp,[status(thm)],[c_4860]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(contradiction,plain,
% 2.74/0.99      ( $false ),
% 2.74/0.99      inference(minisat,[status(thm)],[c_4997,c_4767]) ).
% 2.74/0.99  
% 2.74/0.99  
% 2.74/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.74/0.99  
% 2.74/0.99  ------                               Statistics
% 2.74/0.99  
% 2.74/0.99  ------ General
% 2.74/0.99  
% 2.74/0.99  abstr_ref_over_cycles:                  0
% 2.74/0.99  abstr_ref_under_cycles:                 0
% 2.74/0.99  gc_basic_clause_elim:                   0
% 2.74/0.99  forced_gc_time:                         0
% 2.74/0.99  parsing_time:                           0.011
% 2.74/0.99  unif_index_cands_time:                  0.
% 2.74/0.99  unif_index_add_time:                    0.
% 2.74/0.99  orderings_time:                         0.
% 2.74/0.99  out_proof_time:                         0.014
% 2.74/0.99  total_time:                             0.216
% 2.74/0.99  num_of_symbols:                         53
% 2.74/0.99  num_of_terms:                           4518
% 2.74/0.99  
% 2.74/0.99  ------ Preprocessing
% 2.74/0.99  
% 2.74/0.99  num_of_splits:                          0
% 2.74/0.99  num_of_split_atoms:                     0
% 2.74/0.99  num_of_reused_defs:                     0
% 2.74/0.99  num_eq_ax_congr_red:                    12
% 2.74/0.99  num_of_sem_filtered_clauses:            1
% 2.74/0.99  num_of_subtypes:                        4
% 2.74/0.99  monotx_restored_types:                  0
% 2.74/0.99  sat_num_of_epr_types:                   0
% 2.74/0.99  sat_num_of_non_cyclic_types:            0
% 2.74/0.99  sat_guarded_non_collapsed_types:        0
% 2.74/0.99  num_pure_diseq_elim:                    0
% 2.74/0.99  simp_replaced_by:                       0
% 2.74/0.99  res_preprocessed:                       98
% 2.74/0.99  prep_upred:                             0
% 2.74/0.99  prep_unflattend:                        69
% 2.74/0.99  smt_new_axioms:                         0
% 2.74/0.99  pred_elim_cands:                        5
% 2.74/0.99  pred_elim:                              2
% 2.74/0.99  pred_elim_cl:                           5
% 2.74/0.99  pred_elim_cycles:                       6
% 2.74/0.99  merged_defs:                            0
% 2.74/0.99  merged_defs_ncl:                        0
% 2.74/0.99  bin_hyper_res:                          0
% 2.74/0.99  prep_cycles:                            4
% 2.74/0.99  pred_elim_time:                         0.02
% 2.74/0.99  splitting_time:                         0.
% 2.74/0.99  sem_filter_time:                        0.
% 2.74/0.99  monotx_time:                            0.
% 2.74/0.99  subtype_inf_time:                       0.
% 2.74/0.99  
% 2.74/0.99  ------ Problem properties
% 2.74/0.99  
% 2.74/0.99  clauses:                                16
% 2.74/0.99  conjectures:                            7
% 2.74/0.99  epr:                                    2
% 2.74/0.99  horn:                                   12
% 2.74/0.99  ground:                                 9
% 2.74/0.99  unary:                                  4
% 2.74/0.99  binary:                                 6
% 2.74/0.99  lits:                                   48
% 2.74/0.99  lits_eq:                                12
% 2.74/0.99  fd_pure:                                0
% 2.74/0.99  fd_pseudo:                              0
% 2.74/0.99  fd_cond:                                0
% 2.74/0.99  fd_pseudo_cond:                         0
% 2.74/0.99  ac_symbols:                             0
% 2.74/0.99  
% 2.74/0.99  ------ Propositional Solver
% 2.74/0.99  
% 2.74/0.99  prop_solver_calls:                      30
% 2.74/0.99  prop_fast_solver_calls:                 1149
% 2.74/0.99  smt_solver_calls:                       0
% 2.74/0.99  smt_fast_solver_calls:                  0
% 2.74/0.99  prop_num_of_clauses:                    1473
% 2.74/0.99  prop_preprocess_simplified:             3799
% 2.74/0.99  prop_fo_subsumed:                       70
% 2.74/0.99  prop_solver_time:                       0.
% 2.74/0.99  smt_solver_time:                        0.
% 2.74/0.99  smt_fast_solver_time:                   0.
% 2.74/0.99  prop_fast_solver_time:                  0.
% 2.74/0.99  prop_unsat_core_time:                   0.
% 2.74/0.99  
% 2.74/0.99  ------ QBF
% 2.74/0.99  
% 2.74/0.99  qbf_q_res:                              0
% 2.74/0.99  qbf_num_tautologies:                    0
% 2.74/0.99  qbf_prep_cycles:                        0
% 2.74/0.99  
% 2.74/0.99  ------ BMC1
% 2.74/0.99  
% 2.74/0.99  bmc1_current_bound:                     -1
% 2.74/0.99  bmc1_last_solved_bound:                 -1
% 2.74/0.99  bmc1_unsat_core_size:                   -1
% 2.74/0.99  bmc1_unsat_core_parents_size:           -1
% 2.74/0.99  bmc1_merge_next_fun:                    0
% 2.74/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.74/0.99  
% 2.74/0.99  ------ Instantiation
% 2.74/0.99  
% 2.74/0.99  inst_num_of_clauses:                    470
% 2.74/0.99  inst_num_in_passive:                    111
% 2.74/0.99  inst_num_in_active:                     258
% 2.74/0.99  inst_num_in_unprocessed:                101
% 2.74/0.99  inst_num_of_loops:                      400
% 2.74/0.99  inst_num_of_learning_restarts:          0
% 2.74/0.99  inst_num_moves_active_passive:          136
% 2.74/0.99  inst_lit_activity:                      0
% 2.74/0.99  inst_lit_activity_moves:                0
% 2.74/0.99  inst_num_tautologies:                   0
% 2.74/0.99  inst_num_prop_implied:                  0
% 2.74/0.99  inst_num_existing_simplified:           0
% 2.74/0.99  inst_num_eq_res_simplified:             0
% 2.74/0.99  inst_num_child_elim:                    0
% 2.74/0.99  inst_num_of_dismatching_blockings:      198
% 2.74/0.99  inst_num_of_non_proper_insts:           577
% 2.74/0.99  inst_num_of_duplicates:                 0
% 2.74/0.99  inst_inst_num_from_inst_to_res:         0
% 2.74/0.99  inst_dismatching_checking_time:         0.
% 2.74/0.99  
% 2.74/0.99  ------ Resolution
% 2.74/0.99  
% 2.74/0.99  res_num_of_clauses:                     0
% 2.74/0.99  res_num_in_passive:                     0
% 2.74/0.99  res_num_in_active:                      0
% 2.74/0.99  res_num_of_loops:                       102
% 2.74/0.99  res_forward_subset_subsumed:            81
% 2.74/0.99  res_backward_subset_subsumed:           0
% 2.74/0.99  res_forward_subsumed:                   0
% 2.74/0.99  res_backward_subsumed:                  0
% 2.74/0.99  res_forward_subsumption_resolution:     0
% 2.74/0.99  res_backward_subsumption_resolution:    0
% 2.74/0.99  res_clause_to_clause_subsumption:       538
% 2.74/0.99  res_orphan_elimination:                 0
% 2.74/0.99  res_tautology_del:                      93
% 2.74/0.99  res_num_eq_res_simplified:              0
% 2.74/0.99  res_num_sel_changes:                    0
% 2.74/0.99  res_moves_from_active_to_pass:          0
% 2.74/0.99  
% 2.74/0.99  ------ Superposition
% 2.74/0.99  
% 2.74/0.99  sup_time_total:                         0.
% 2.74/0.99  sup_time_generating:                    0.
% 2.74/0.99  sup_time_sim_full:                      0.
% 2.74/0.99  sup_time_sim_immed:                     0.
% 2.74/0.99  
% 2.74/0.99  sup_num_of_clauses:                     54
% 2.74/0.99  sup_num_in_active:                      49
% 2.74/0.99  sup_num_in_passive:                     5
% 2.74/0.99  sup_num_of_loops:                       78
% 2.74/0.99  sup_fw_superposition:                   53
% 2.74/0.99  sup_bw_superposition:                   22
% 2.74/0.99  sup_immediate_simplified:               9
% 2.74/0.99  sup_given_eliminated:                   0
% 2.74/0.99  comparisons_done:                       0
% 2.74/0.99  comparisons_avoided:                    24
% 2.74/0.99  
% 2.74/0.99  ------ Simplifications
% 2.74/0.99  
% 2.74/0.99  
% 2.74/0.99  sim_fw_subset_subsumed:                 4
% 2.74/0.99  sim_bw_subset_subsumed:                 13
% 2.74/0.99  sim_fw_subsumed:                        0
% 2.74/0.99  sim_bw_subsumed:                        0
% 2.74/0.99  sim_fw_subsumption_res:                 1
% 2.74/0.99  sim_bw_subsumption_res:                 0
% 2.74/0.99  sim_tautology_del:                      2
% 2.74/0.99  sim_eq_tautology_del:                   10
% 2.74/0.99  sim_eq_res_simp:                        2
% 2.74/0.99  sim_fw_demodulated:                     1
% 2.74/0.99  sim_bw_demodulated:                     18
% 2.74/0.99  sim_light_normalised:                   3
% 2.74/0.99  sim_joinable_taut:                      0
% 2.74/0.99  sim_joinable_simp:                      0
% 2.74/0.99  sim_ac_normalised:                      0
% 2.74/0.99  sim_smt_subsumption:                    0
% 2.74/0.99  
%------------------------------------------------------------------------------
