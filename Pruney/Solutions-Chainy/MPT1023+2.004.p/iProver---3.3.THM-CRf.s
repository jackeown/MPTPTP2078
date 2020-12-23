%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:41 EST 2020

% Result     : Theorem 3.88s
% Output     : CNFRefutation 3.88s
% Verified   : 
% Statistics : Number of formulae       :  187 (18950 expanded)
%              Number of clauses        :  120 (5659 expanded)
%              Number of leaves         :   17 (4583 expanded)
%              Depth                    :   39
%              Number of atoms          :  631 (121301 expanded)
%              Number of equality atoms :  331 (27592 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
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

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

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
    inference(nnf_transformation,[],[f33])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( m1_subset_1(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ~ r2_relset_1(X0,X1,X2,sK7)
        & ! [X4] :
            ( k1_funct_1(sK7,X4) = k1_funct_1(X2,X4)
            | ~ m1_subset_1(X4,X0) )
        & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK7,X0,X1)
        & v1_funct_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK4,sK5,sK6,X3)
          & ! [X4] :
              ( k1_funct_1(sK6,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,sK4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
          & v1_funct_2(X3,sK4,sK5)
          & v1_funct_1(X3) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_2(sK6,sK4,sK5)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ~ r2_relset_1(sK4,sK5,sK6,sK7)
    & ! [X4] :
        ( k1_funct_1(sK6,X4) = k1_funct_1(sK7,X4)
        | ~ m1_subset_1(X4,sK4) )
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK7,sK4,sK5)
    & v1_funct_1(sK7)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK6,sK4,sK5)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f35,f51,f50])).

fof(f86,plain,(
    v1_funct_2(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f87,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f52])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f83,plain,(
    v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f84,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f52])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
        & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
            & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f44])).

fof(f66,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK1(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f85,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f52])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f82,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f52])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f88,plain,(
    ! [X4] :
      ( k1_funct_1(sK6,X4) = k1_funct_1(sK7,X4)
      | ~ m1_subset_1(X4,sK4) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f67,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f92,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f72])).

fof(f89,plain,(
    ~ r2_relset_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f52])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f95,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f80])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f97,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f77])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_593,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK7 != X0
    | sK5 != X2
    | sK4 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_32])).

cnf(c_594,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | k1_relset_1(sK4,sK5,sK7) = sK4
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_593])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_596,plain,
    ( k1_relset_1(sK4,sK5,sK7) = sK4
    | k1_xboole_0 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_594,c_31])).

cnf(c_18337,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_18339,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_18711,plain,
    ( k1_relset_1(sK4,sK5,sK7) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_18337,c_18339])).

cnf(c_18810,plain,
    ( k1_relat_1(sK7) = sK4
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_596,c_18711])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_604,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK6 != X0
    | sK5 != X2
    | sK4 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_35])).

cnf(c_605,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | k1_relset_1(sK4,sK5,sK6) = sK4
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_604])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_607,plain,
    ( k1_relset_1(sK4,sK5,sK6) = sK4
    | k1_xboole_0 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_605,c_34])).

cnf(c_18335,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_18712,plain,
    ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_18335,c_18339])).

cnf(c_18813,plain,
    ( k1_relat_1(sK6) = sK4
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_607,c_18712])).

cnf(c_14,plain,
    ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | X0 = X1
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_18341,plain,
    ( X0 = X1
    | k1_relat_1(X0) != k1_relat_1(X1)
    | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_18817,plain,
    ( k1_relat_1(X0) != sK4
    | sK7 = X0
    | sK5 = k1_xboole_0
    | r2_hidden(sK1(sK7,X0),k1_relat_1(sK7)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_18810,c_18341])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_40,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_42,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_15719,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_15720,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15719])).

cnf(c_19017,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_relat_1(X0) != sK4
    | sK7 = X0
    | sK5 = k1_xboole_0
    | r2_hidden(sK1(sK7,X0),k1_relat_1(sK7)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18817,c_40,c_42,c_15720])).

cnf(c_19018,plain,
    ( k1_relat_1(X0) != sK4
    | sK7 = X0
    | sK5 = k1_xboole_0
    | r2_hidden(sK1(sK7,X0),k1_relat_1(sK7)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_19017])).

cnf(c_19030,plain,
    ( sK7 = sK6
    | sK5 = k1_xboole_0
    | r2_hidden(sK1(sK7,sK6),k1_relat_1(sK7)) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_18813,c_19018])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_37,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_39,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_15740,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_15741,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15740])).

cnf(c_19128,plain,
    ( sK7 = sK6
    | sK5 = k1_xboole_0
    | r2_hidden(sK1(sK7,sK6),k1_relat_1(sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19030,c_37,c_39,c_15741])).

cnf(c_16,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_12,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_498,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_16,c_12])).

cnf(c_502,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_498,c_15])).

cnf(c_503,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_502])).

cnf(c_18328,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_503])).

cnf(c_18677,plain,
    ( r1_tarski(k1_relat_1(sK7),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_18337,c_18328])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_18348,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_18783,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_18677,c_18348])).

cnf(c_19137,plain,
    ( sK7 = sK6
    | sK5 = k1_xboole_0
    | r2_hidden(sK1(sK7,sK6),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_19128,c_18783])).

cnf(c_8,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_18345,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_19300,plain,
    ( sK7 = sK6
    | sK5 = k1_xboole_0
    | m1_subset_1(sK1(sK7,sK6),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_19137,c_18345])).

cnf(c_30,negated_conjecture,
    ( ~ m1_subset_1(X0,sK4)
    | k1_funct_1(sK6,X0) = k1_funct_1(sK7,X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_18338,plain,
    ( k1_funct_1(sK6,X0) = k1_funct_1(sK7,X0)
    | m1_subset_1(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_19376,plain,
    ( k1_funct_1(sK7,sK1(sK7,sK6)) = k1_funct_1(sK6,sK1(sK7,sK6))
    | sK7 = sK6
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_19300,c_18338])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | X1 = X0
    | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_18342,plain,
    ( X0 = X1
    | k1_funct_1(X1,sK1(X0,X1)) != k1_funct_1(X0,sK1(X0,X1))
    | k1_relat_1(X0) != k1_relat_1(X1)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_19399,plain,
    ( k1_relat_1(sK6) != k1_relat_1(sK7)
    | sK7 = sK6
    | sK5 = k1_xboole_0
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_19376,c_18342])).

cnf(c_19400,plain,
    ( ~ v1_funct_1(sK7)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK7)
    | ~ v1_relat_1(sK6)
    | k1_relat_1(sK6) != k1_relat_1(sK7)
    | sK7 = sK6
    | sK5 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_19399])).

cnf(c_19406,plain,
    ( k1_relat_1(sK6) != k1_relat_1(sK7)
    | sK7 = sK6
    | sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_19399,c_37,c_39,c_40,c_42,c_15720,c_15741])).

cnf(c_19411,plain,
    ( k1_relat_1(sK6) != sK4
    | sK7 = sK6
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_18810,c_19406])).

cnf(c_19412,plain,
    ( sK7 = sK6
    | sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_19411,c_18813])).

cnf(c_18,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_29,negated_conjecture,
    ( ~ r2_relset_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_489,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK7 != X0
    | sK6 != X0
    | sK5 != X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_29])).

cnf(c_490,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | sK6 != sK7 ),
    inference(unflattening,[status(thm)],[c_489])).

cnf(c_492,plain,
    ( sK6 != sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_490,c_31])).

cnf(c_19432,plain,
    ( sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_19412,c_492])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_547,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK6 != X0
    | sK5 != k1_xboole_0
    | sK4 != X1
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_35])).

cnf(c_548,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0)))
    | sK5 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_547])).

cnf(c_18326,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK4
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_548])).

cnf(c_19452,plain,
    ( sK6 = k1_xboole_0
    | sK4 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19432,c_18326])).

cnf(c_19481,plain,
    ( sK6 = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_19452])).

cnf(c_19460,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_19432,c_18335])).

cnf(c_19485,plain,
    ( sK6 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_19481,c_19460])).

cnf(c_2430,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_10014,plain,
    ( X0 = X1
    | X0 != k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2430])).

cnf(c_10104,plain,
    ( sK7 != k1_xboole_0
    | sK6 = sK7
    | sK6 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10014])).

cnf(c_531,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK7 != X0
    | sK5 != k1_xboole_0
    | sK4 != X1
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_32])).

cnf(c_532,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0)))
    | sK5 != k1_xboole_0
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_531])).

cnf(c_18327,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK4
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_532])).

cnf(c_19451,plain,
    ( sK7 = k1_xboole_0
    | sK4 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19432,c_18327])).

cnf(c_19488,plain,
    ( sK7 = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_19451])).

cnf(c_19459,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_19432,c_18337])).

cnf(c_19492,plain,
    ( sK7 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_19488,c_19459])).

cnf(c_19774,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_19485,c_31,c_490,c_10104,c_19492])).

cnf(c_19449,plain,
    ( k1_relset_1(sK4,k1_xboole_0,sK6) = k1_relat_1(sK6) ),
    inference(demodulation,[status(thm)],[c_19432,c_18712])).

cnf(c_19786,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_relat_1(sK6) ),
    inference(demodulation,[status(thm)],[c_19774,c_19449])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_580,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK6 != X0
    | sK5 != X1
    | sK4 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_35])).

cnf(c_581,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5)))
    | k1_relset_1(k1_xboole_0,sK5,sK6) = k1_xboole_0
    | sK4 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_580])).

cnf(c_18324,plain,
    ( k1_relset_1(k1_xboole_0,sK5,sK6) = k1_xboole_0
    | sK4 != k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_581])).

cnf(c_19456,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0
    | sK4 != k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19432,c_18324])).

cnf(c_19787,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_19774,c_19460])).

cnf(c_19997,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_19456,c_31,c_490,c_10104,c_19485,c_19492,c_19787])).

cnf(c_20131,plain,
    ( k1_relat_1(sK6) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_19786,c_19997])).

cnf(c_19450,plain,
    ( k1_relset_1(sK4,k1_xboole_0,sK7) = k1_relat_1(sK7) ),
    inference(demodulation,[status(thm)],[c_19432,c_18711])).

cnf(c_19785,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK7) = k1_relat_1(sK7) ),
    inference(demodulation,[status(thm)],[c_19774,c_19450])).

cnf(c_19788,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_19774,c_19459])).

cnf(c_567,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK7 != X0
    | sK5 != X1
    | sK4 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_32])).

cnf(c_568,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5)))
    | k1_relset_1(k1_xboole_0,sK5,sK7) = k1_xboole_0
    | sK4 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_567])).

cnf(c_18325,plain,
    ( k1_relset_1(k1_xboole_0,sK5,sK7) = k1_xboole_0
    | sK4 != k1_xboole_0
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_568])).

cnf(c_19453,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK7) = k1_xboole_0
    | sK4 != k1_xboole_0
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19432,c_18325])).

cnf(c_19659,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK7) = k1_xboole_0
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19453,c_31,c_490,c_10104,c_19485,c_19492])).

cnf(c_19973,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK7) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_19788,c_19659])).

cnf(c_20091,plain,
    ( k1_relat_1(sK7) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_19785,c_19973])).

cnf(c_20095,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | sK7 = X0
    | r2_hidden(sK1(X0,sK7),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_20091,c_18341])).

cnf(c_20208,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_relat_1(X0) != k1_xboole_0
    | sK7 = X0
    | r2_hidden(sK1(X0,sK7),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20095,c_40,c_42,c_15720])).

cnf(c_20209,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | sK7 = X0
    | r2_hidden(sK1(X0,sK7),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_20208])).

cnf(c_20220,plain,
    ( sK7 = sK6
    | r2_hidden(sK1(sK6,sK7),k1_relat_1(sK6)) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_20131,c_20209])).

cnf(c_20225,plain,
    ( sK7 = sK6
    | r2_hidden(sK1(sK6,sK7),k1_xboole_0) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20220,c_20131])).

cnf(c_20319,plain,
    ( sK7 = sK6
    | r2_hidden(sK1(sK6,sK7),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20225,c_37,c_39,c_15741])).

cnf(c_0,negated_conjecture,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_4,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_476,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_4])).

cnf(c_477,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_476])).

cnf(c_18329,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_477])).

cnf(c_20325,plain,
    ( sK7 = sK6 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_20319,c_18329])).

cnf(c_20339,plain,
    ( sK6 != sK6 ),
    inference(demodulation,[status(thm)],[c_20325,c_492])).

cnf(c_20340,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_20339])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:09:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.88/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/0.99  
% 3.88/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.88/0.99  
% 3.88/0.99  ------  iProver source info
% 3.88/0.99  
% 3.88/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.88/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.88/0.99  git: non_committed_changes: false
% 3.88/0.99  git: last_make_outside_of_git: false
% 3.88/0.99  
% 3.88/0.99  ------ 
% 3.88/0.99  ------ Parsing...
% 3.88/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.88/0.99  
% 3.88/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.88/0.99  
% 3.88/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.88/0.99  
% 3.88/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.88/0.99  ------ Proving...
% 3.88/0.99  ------ Problem Properties 
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  clauses                                 29
% 3.88/0.99  conjectures                             5
% 3.88/0.99  EPR                                     8
% 3.88/0.99  Horn                                    23
% 3.88/0.99  unary                                   7
% 3.88/0.99  binary                                  11
% 3.88/0.99  lits                                    72
% 3.88/0.99  lits eq                                 24
% 3.88/0.99  fd_pure                                 0
% 3.88/0.99  fd_pseudo                               0
% 3.88/0.99  fd_cond                                 0
% 3.88/0.99  fd_pseudo_cond                          3
% 3.88/0.99  AC symbols                              0
% 3.88/0.99  
% 3.88/0.99  ------ Input Options Time Limit: Unbounded
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.88/0.99  Current options:
% 3.88/0.99  ------ 
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  ------ Proving...
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.88/0.99  
% 3.88/0.99  ------ Proving...
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.88/0.99  
% 3.88/0.99  ------ Proving...
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.88/0.99  
% 3.88/0.99  ------ Proving...
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.88/0.99  
% 3.88/0.99  ------ Proving...
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.88/0.99  
% 3.88/0.99  ------ Proving...
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.88/0.99  
% 3.88/0.99  ------ Proving...
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.88/0.99  
% 3.88/0.99  ------ Proving...
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.88/0.99  
% 3.88/0.99  ------ Proving...
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.88/0.99  
% 3.88/0.99  ------ Proving...
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.88/0.99  
% 3.88/0.99  ------ Proving...
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.88/0.99  
% 3.88/0.99  ------ Proving...
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.88/0.99  
% 3.88/0.99  ------ Proving...
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.88/0.99  
% 3.88/0.99  ------ Proving...
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.88/0.99  
% 3.88/0.99  ------ Proving...
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.88/0.99  
% 3.88/0.99  ------ Proving...
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.88/0.99  
% 3.88/0.99  ------ Proving...
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.88/0.99  
% 3.88/0.99  ------ Proving...
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.88/0.99  
% 3.88/0.99  ------ Proving...
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.88/0.99  
% 3.88/0.99  ------ Proving...
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  ------ Preprocessing... sf_s  rm: 10 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.88/0.99  
% 3.88/0.99  ------ Proving...
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.88/0.99  
% 3.88/0.99  ------ Proving...
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  ------ Preprocessing... sf_s  rm: 14 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.88/0.99  
% 3.88/0.99  ------ Proving...
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.88/0.99  
% 3.88/0.99  ------ Proving...
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  % SZS status Theorem for theBenchmark.p
% 3.88/0.99  
% 3.88/0.99   Resolution empty clause
% 3.88/0.99  
% 3.88/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.88/0.99  
% 3.88/0.99  fof(f14,axiom,(
% 3.88/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f32,plain,(
% 3.88/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.88/0.99    inference(ennf_transformation,[],[f14])).
% 3.88/0.99  
% 3.88/0.99  fof(f33,plain,(
% 3.88/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.88/0.99    inference(flattening,[],[f32])).
% 3.88/0.99  
% 3.88/0.99  fof(f49,plain,(
% 3.88/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.88/0.99    inference(nnf_transformation,[],[f33])).
% 3.88/0.99  
% 3.88/0.99  fof(f76,plain,(
% 3.88/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.88/0.99    inference(cnf_transformation,[],[f49])).
% 3.88/0.99  
% 3.88/0.99  fof(f15,conjecture,(
% 3.88/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 3.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f16,negated_conjecture,(
% 3.88/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 3.88/0.99    inference(negated_conjecture,[],[f15])).
% 3.88/0.99  
% 3.88/0.99  fof(f34,plain,(
% 3.88/0.99    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.88/0.99    inference(ennf_transformation,[],[f16])).
% 3.88/0.99  
% 3.88/0.99  fof(f35,plain,(
% 3.88/0.99    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.88/0.99    inference(flattening,[],[f34])).
% 3.88/0.99  
% 3.88/0.99  fof(f51,plain,(
% 3.88/0.99    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK7) & ! [X4] : (k1_funct_1(sK7,X4) = k1_funct_1(X2,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK7,X0,X1) & v1_funct_1(sK7))) )),
% 3.88/0.99    introduced(choice_axiom,[])).
% 3.88/0.99  
% 3.88/0.99  fof(f50,plain,(
% 3.88/0.99    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK4,sK5,sK6,X3) & ! [X4] : (k1_funct_1(sK6,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,sK4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(X3,sK4,sK5) & v1_funct_1(X3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6))),
% 3.88/0.99    introduced(choice_axiom,[])).
% 3.88/0.99  
% 3.88/0.99  fof(f52,plain,(
% 3.88/0.99    (~r2_relset_1(sK4,sK5,sK6,sK7) & ! [X4] : (k1_funct_1(sK6,X4) = k1_funct_1(sK7,X4) | ~m1_subset_1(X4,sK4)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6)),
% 3.88/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f35,f51,f50])).
% 3.88/0.99  
% 3.88/0.99  fof(f86,plain,(
% 3.88/0.99    v1_funct_2(sK7,sK4,sK5)),
% 3.88/0.99    inference(cnf_transformation,[],[f52])).
% 3.88/0.99  
% 3.88/0.99  fof(f87,plain,(
% 3.88/0.99    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 3.88/0.99    inference(cnf_transformation,[],[f52])).
% 3.88/0.99  
% 3.88/0.99  fof(f11,axiom,(
% 3.88/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f27,plain,(
% 3.88/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.88/0.99    inference(ennf_transformation,[],[f11])).
% 3.88/0.99  
% 3.88/0.99  fof(f70,plain,(
% 3.88/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.88/0.99    inference(cnf_transformation,[],[f27])).
% 3.88/0.99  
% 3.88/0.99  fof(f83,plain,(
% 3.88/0.99    v1_funct_2(sK6,sK4,sK5)),
% 3.88/0.99    inference(cnf_transformation,[],[f52])).
% 3.88/0.99  
% 3.88/0.99  fof(f84,plain,(
% 3.88/0.99    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 3.88/0.99    inference(cnf_transformation,[],[f52])).
% 3.88/0.99  
% 3.88/0.99  fof(f8,axiom,(
% 3.88/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 3.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f23,plain,(
% 3.88/0.99    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.88/0.99    inference(ennf_transformation,[],[f8])).
% 3.88/0.99  
% 3.88/0.99  fof(f24,plain,(
% 3.88/0.99    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.88/0.99    inference(flattening,[],[f23])).
% 3.88/0.99  
% 3.88/0.99  fof(f44,plain,(
% 3.88/0.99    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))))),
% 3.88/0.99    introduced(choice_axiom,[])).
% 3.88/0.99  
% 3.88/0.99  fof(f45,plain,(
% 3.88/0.99    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.88/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f44])).
% 3.88/0.99  
% 3.88/0.99  fof(f66,plain,(
% 3.88/0.99    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.88/0.99    inference(cnf_transformation,[],[f45])).
% 3.88/0.99  
% 3.88/0.99  fof(f85,plain,(
% 3.88/0.99    v1_funct_1(sK7)),
% 3.88/0.99    inference(cnf_transformation,[],[f52])).
% 3.88/0.99  
% 3.88/0.99  fof(f9,axiom,(
% 3.88/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f25,plain,(
% 3.88/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.88/0.99    inference(ennf_transformation,[],[f9])).
% 3.88/0.99  
% 3.88/0.99  fof(f68,plain,(
% 3.88/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.88/0.99    inference(cnf_transformation,[],[f25])).
% 3.88/0.99  
% 3.88/0.99  fof(f82,plain,(
% 3.88/0.99    v1_funct_1(sK6)),
% 3.88/0.99    inference(cnf_transformation,[],[f52])).
% 3.88/0.99  
% 3.88/0.99  fof(f10,axiom,(
% 3.88/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f18,plain,(
% 3.88/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.88/0.99    inference(pure_predicate_removal,[],[f10])).
% 3.88/0.99  
% 3.88/0.99  fof(f26,plain,(
% 3.88/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.88/0.99    inference(ennf_transformation,[],[f18])).
% 3.88/0.99  
% 3.88/0.99  fof(f69,plain,(
% 3.88/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.88/0.99    inference(cnf_transformation,[],[f26])).
% 3.88/0.99  
% 3.88/0.99  fof(f7,axiom,(
% 3.88/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f22,plain,(
% 3.88/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.88/0.99    inference(ennf_transformation,[],[f7])).
% 3.88/0.99  
% 3.88/0.99  fof(f43,plain,(
% 3.88/0.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.88/0.99    inference(nnf_transformation,[],[f22])).
% 3.88/0.99  
% 3.88/0.99  fof(f64,plain,(
% 3.88/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.88/0.99    inference(cnf_transformation,[],[f43])).
% 3.88/0.99  
% 3.88/0.99  fof(f2,axiom,(
% 3.88/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f20,plain,(
% 3.88/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.88/0.99    inference(ennf_transformation,[],[f2])).
% 3.88/0.99  
% 3.88/0.99  fof(f36,plain,(
% 3.88/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.88/0.99    inference(nnf_transformation,[],[f20])).
% 3.88/0.99  
% 3.88/0.99  fof(f37,plain,(
% 3.88/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.88/0.99    inference(rectify,[],[f36])).
% 3.88/0.99  
% 3.88/0.99  fof(f38,plain,(
% 3.88/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.88/0.99    introduced(choice_axiom,[])).
% 3.88/0.99  
% 3.88/0.99  fof(f39,plain,(
% 3.88/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.88/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 3.88/0.99  
% 3.88/0.99  fof(f54,plain,(
% 3.88/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.88/0.99    inference(cnf_transformation,[],[f39])).
% 3.88/0.99  
% 3.88/0.99  fof(f5,axiom,(
% 3.88/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f21,plain,(
% 3.88/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.88/0.99    inference(ennf_transformation,[],[f5])).
% 3.88/0.99  
% 3.88/0.99  fof(f61,plain,(
% 3.88/0.99    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.88/0.99    inference(cnf_transformation,[],[f21])).
% 3.88/0.99  
% 3.88/0.99  fof(f88,plain,(
% 3.88/0.99    ( ! [X4] : (k1_funct_1(sK6,X4) = k1_funct_1(sK7,X4) | ~m1_subset_1(X4,sK4)) )),
% 3.88/0.99    inference(cnf_transformation,[],[f52])).
% 3.88/0.99  
% 3.88/0.99  fof(f67,plain,(
% 3.88/0.99    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.88/0.99    inference(cnf_transformation,[],[f45])).
% 3.88/0.99  
% 3.88/0.99  fof(f12,axiom,(
% 3.88/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f28,plain,(
% 3.88/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.88/0.99    inference(ennf_transformation,[],[f12])).
% 3.88/0.99  
% 3.88/0.99  fof(f29,plain,(
% 3.88/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.88/0.99    inference(flattening,[],[f28])).
% 3.88/0.99  
% 3.88/0.99  fof(f46,plain,(
% 3.88/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.88/0.99    inference(nnf_transformation,[],[f29])).
% 3.88/0.99  
% 3.88/0.99  fof(f72,plain,(
% 3.88/0.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.88/0.99    inference(cnf_transformation,[],[f46])).
% 3.88/0.99  
% 3.88/0.99  fof(f92,plain,(
% 3.88/0.99    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.88/0.99    inference(equality_resolution,[],[f72])).
% 3.88/0.99  
% 3.88/0.99  fof(f89,plain,(
% 3.88/0.99    ~r2_relset_1(sK4,sK5,sK6,sK7)),
% 3.88/0.99    inference(cnf_transformation,[],[f52])).
% 3.88/0.99  
% 3.88/0.99  fof(f80,plain,(
% 3.88/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.88/0.99    inference(cnf_transformation,[],[f49])).
% 3.88/0.99  
% 3.88/0.99  fof(f95,plain,(
% 3.88/0.99    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.88/0.99    inference(equality_resolution,[],[f80])).
% 3.88/0.99  
% 3.88/0.99  fof(f77,plain,(
% 3.88/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.88/0.99    inference(cnf_transformation,[],[f49])).
% 3.88/0.99  
% 3.88/0.99  fof(f97,plain,(
% 3.88/0.99    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.88/0.99    inference(equality_resolution,[],[f77])).
% 3.88/0.99  
% 3.88/0.99  fof(f1,axiom,(
% 3.88/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f17,plain,(
% 3.88/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 3.88/0.99    inference(unused_predicate_definition_removal,[],[f1])).
% 3.88/0.99  
% 3.88/0.99  fof(f19,plain,(
% 3.88/0.99    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 3.88/0.99    inference(ennf_transformation,[],[f17])).
% 3.88/0.99  
% 3.88/0.99  fof(f53,plain,(
% 3.88/0.99    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.88/0.99    inference(cnf_transformation,[],[f19])).
% 3.88/0.99  
% 3.88/0.99  fof(f3,axiom,(
% 3.88/0.99    v1_xboole_0(k1_xboole_0)),
% 3.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f57,plain,(
% 3.88/0.99    v1_xboole_0(k1_xboole_0)),
% 3.88/0.99    inference(cnf_transformation,[],[f3])).
% 3.88/0.99  
% 3.88/0.99  cnf(c_28,plain,
% 3.88/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.88/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.88/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.88/0.99      | k1_xboole_0 = X2 ),
% 3.88/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_32,negated_conjecture,
% 3.88/0.99      ( v1_funct_2(sK7,sK4,sK5) ),
% 3.88/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_593,plain,
% 3.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.88/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.88/0.99      | sK7 != X0
% 3.88/0.99      | sK5 != X2
% 3.88/0.99      | sK4 != X1
% 3.88/0.99      | k1_xboole_0 = X2 ),
% 3.88/0.99      inference(resolution_lifted,[status(thm)],[c_28,c_32]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_594,plain,
% 3.88/0.99      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.88/0.99      | k1_relset_1(sK4,sK5,sK7) = sK4
% 3.88/0.99      | k1_xboole_0 = sK5 ),
% 3.88/0.99      inference(unflattening,[status(thm)],[c_593]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_31,negated_conjecture,
% 3.88/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 3.88/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_596,plain,
% 3.88/0.99      ( k1_relset_1(sK4,sK5,sK7) = sK4 | k1_xboole_0 = sK5 ),
% 3.88/0.99      inference(global_propositional_subsumption,[status(thm)],[c_594,c_31]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_18337,plain,
% 3.88/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_17,plain,
% 3.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.88/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.88/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_18339,plain,
% 3.88/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.88/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_18711,plain,
% 3.88/0.99      ( k1_relset_1(sK4,sK5,sK7) = k1_relat_1(sK7) ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_18337,c_18339]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_18810,plain,
% 3.88/0.99      ( k1_relat_1(sK7) = sK4 | sK5 = k1_xboole_0 ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_596,c_18711]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_35,negated_conjecture,
% 3.88/0.99      ( v1_funct_2(sK6,sK4,sK5) ),
% 3.88/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_604,plain,
% 3.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.88/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.88/0.99      | sK6 != X0
% 3.88/0.99      | sK5 != X2
% 3.88/0.99      | sK4 != X1
% 3.88/0.99      | k1_xboole_0 = X2 ),
% 3.88/0.99      inference(resolution_lifted,[status(thm)],[c_28,c_35]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_605,plain,
% 3.88/0.99      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.88/0.99      | k1_relset_1(sK4,sK5,sK6) = sK4
% 3.88/0.99      | k1_xboole_0 = sK5 ),
% 3.88/0.99      inference(unflattening,[status(thm)],[c_604]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_34,negated_conjecture,
% 3.88/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 3.88/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_607,plain,
% 3.88/0.99      ( k1_relset_1(sK4,sK5,sK6) = sK4 | k1_xboole_0 = sK5 ),
% 3.88/0.99      inference(global_propositional_subsumption,[status(thm)],[c_605,c_34]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_18335,plain,
% 3.88/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_18712,plain,
% 3.88/0.99      ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_18335,c_18339]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_18813,plain,
% 3.88/0.99      ( k1_relat_1(sK6) = sK4 | sK5 = k1_xboole_0 ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_607,c_18712]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_14,plain,
% 3.88/0.99      ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
% 3.88/0.99      | ~ v1_funct_1(X1)
% 3.88/0.99      | ~ v1_funct_1(X0)
% 3.88/0.99      | ~ v1_relat_1(X1)
% 3.88/0.99      | ~ v1_relat_1(X0)
% 3.88/0.99      | X0 = X1
% 3.88/0.99      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 3.88/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_18341,plain,
% 3.88/0.99      ( X0 = X1
% 3.88/0.99      | k1_relat_1(X0) != k1_relat_1(X1)
% 3.88/0.99      | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) = iProver_top
% 3.88/0.99      | v1_funct_1(X1) != iProver_top
% 3.88/0.99      | v1_funct_1(X0) != iProver_top
% 3.88/0.99      | v1_relat_1(X0) != iProver_top
% 3.88/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_18817,plain,
% 3.88/0.99      ( k1_relat_1(X0) != sK4
% 3.88/0.99      | sK7 = X0
% 3.88/0.99      | sK5 = k1_xboole_0
% 3.88/0.99      | r2_hidden(sK1(sK7,X0),k1_relat_1(sK7)) = iProver_top
% 3.88/0.99      | v1_funct_1(X0) != iProver_top
% 3.88/0.99      | v1_funct_1(sK7) != iProver_top
% 3.88/0.99      | v1_relat_1(X0) != iProver_top
% 3.88/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_18810,c_18341]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_33,negated_conjecture,
% 3.88/0.99      ( v1_funct_1(sK7) ),
% 3.88/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_40,plain,
% 3.88/0.99      ( v1_funct_1(sK7) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_42,plain,
% 3.88/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_15,plain,
% 3.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.88/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_15719,plain,
% 3.88/0.99      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.88/0.99      | v1_relat_1(sK7) ),
% 3.88/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_15720,plain,
% 3.88/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 3.88/0.99      | v1_relat_1(sK7) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_15719]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_19017,plain,
% 3.88/0.99      ( v1_relat_1(X0) != iProver_top
% 3.88/0.99      | k1_relat_1(X0) != sK4
% 3.88/0.99      | sK7 = X0
% 3.88/0.99      | sK5 = k1_xboole_0
% 3.88/0.99      | r2_hidden(sK1(sK7,X0),k1_relat_1(sK7)) = iProver_top
% 3.88/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.88/0.99      inference(global_propositional_subsumption,
% 3.88/0.99                [status(thm)],
% 3.88/0.99                [c_18817,c_40,c_42,c_15720]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_19018,plain,
% 3.88/0.99      ( k1_relat_1(X0) != sK4
% 3.88/0.99      | sK7 = X0
% 3.88/0.99      | sK5 = k1_xboole_0
% 3.88/0.99      | r2_hidden(sK1(sK7,X0),k1_relat_1(sK7)) = iProver_top
% 3.88/0.99      | v1_funct_1(X0) != iProver_top
% 3.88/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.88/0.99      inference(renaming,[status(thm)],[c_19017]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_19030,plain,
% 3.88/0.99      ( sK7 = sK6
% 3.88/0.99      | sK5 = k1_xboole_0
% 3.88/0.99      | r2_hidden(sK1(sK7,sK6),k1_relat_1(sK7)) = iProver_top
% 3.88/0.99      | v1_funct_1(sK6) != iProver_top
% 3.88/0.99      | v1_relat_1(sK6) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_18813,c_19018]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_36,negated_conjecture,
% 3.88/0.99      ( v1_funct_1(sK6) ),
% 3.88/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_37,plain,
% 3.88/0.99      ( v1_funct_1(sK6) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_39,plain,
% 3.88/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_15740,plain,
% 3.88/0.99      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.88/0.99      | v1_relat_1(sK6) ),
% 3.88/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_15741,plain,
% 3.88/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 3.88/0.99      | v1_relat_1(sK6) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_15740]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_19128,plain,
% 3.88/0.99      ( sK7 = sK6
% 3.88/0.99      | sK5 = k1_xboole_0
% 3.88/0.99      | r2_hidden(sK1(sK7,sK6),k1_relat_1(sK7)) = iProver_top ),
% 3.88/0.99      inference(global_propositional_subsumption,
% 3.88/0.99                [status(thm)],
% 3.88/0.99                [c_19030,c_37,c_39,c_15741]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_16,plain,
% 3.88/0.99      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.88/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_12,plain,
% 3.88/0.99      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.88/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_498,plain,
% 3.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.88/0.99      | r1_tarski(k1_relat_1(X0),X1)
% 3.88/0.99      | ~ v1_relat_1(X0) ),
% 3.88/0.99      inference(resolution,[status(thm)],[c_16,c_12]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_502,plain,
% 3.88/0.99      ( r1_tarski(k1_relat_1(X0),X1)
% 3.88/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.88/0.99      inference(global_propositional_subsumption,[status(thm)],[c_498,c_15]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_503,plain,
% 3.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.88/0.99      | r1_tarski(k1_relat_1(X0),X1) ),
% 3.88/0.99      inference(renaming,[status(thm)],[c_502]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_18328,plain,
% 3.88/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.88/0.99      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_503]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_18677,plain,
% 3.88/0.99      ( r1_tarski(k1_relat_1(sK7),sK4) = iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_18337,c_18328]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_3,plain,
% 3.88/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.88/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_18348,plain,
% 3.88/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.88/0.99      | r2_hidden(X2,X0) != iProver_top
% 3.88/0.99      | r2_hidden(X2,X1) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_18783,plain,
% 3.88/0.99      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 3.88/0.99      | r2_hidden(X0,sK4) = iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_18677,c_18348]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_19137,plain,
% 3.88/0.99      ( sK7 = sK6
% 3.88/0.99      | sK5 = k1_xboole_0
% 3.88/0.99      | r2_hidden(sK1(sK7,sK6),sK4) = iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_19128,c_18783]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_8,plain,
% 3.88/0.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.88/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_18345,plain,
% 3.88/0.99      ( m1_subset_1(X0,X1) = iProver_top | r2_hidden(X0,X1) != iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_19300,plain,
% 3.88/0.99      ( sK7 = sK6
% 3.88/0.99      | sK5 = k1_xboole_0
% 3.88/0.99      | m1_subset_1(sK1(sK7,sK6),sK4) = iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_19137,c_18345]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_30,negated_conjecture,
% 3.88/0.99      ( ~ m1_subset_1(X0,sK4) | k1_funct_1(sK6,X0) = k1_funct_1(sK7,X0) ),
% 3.88/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_18338,plain,
% 3.88/0.99      ( k1_funct_1(sK6,X0) = k1_funct_1(sK7,X0)
% 3.88/0.99      | m1_subset_1(X0,sK4) != iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_19376,plain,
% 3.88/0.99      ( k1_funct_1(sK7,sK1(sK7,sK6)) = k1_funct_1(sK6,sK1(sK7,sK6))
% 3.88/0.99      | sK7 = sK6
% 3.88/0.99      | sK5 = k1_xboole_0 ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_19300,c_18338]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_13,plain,
% 3.88/0.99      ( ~ v1_funct_1(X0)
% 3.88/0.99      | ~ v1_funct_1(X1)
% 3.88/0.99      | ~ v1_relat_1(X0)
% 3.88/0.99      | ~ v1_relat_1(X1)
% 3.88/0.99      | X1 = X0
% 3.88/0.99      | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
% 3.88/0.99      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 3.88/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_18342,plain,
% 3.88/0.99      ( X0 = X1
% 3.88/0.99      | k1_funct_1(X1,sK1(X0,X1)) != k1_funct_1(X0,sK1(X0,X1))
% 3.88/0.99      | k1_relat_1(X0) != k1_relat_1(X1)
% 3.88/0.99      | v1_funct_1(X0) != iProver_top
% 3.88/0.99      | v1_funct_1(X1) != iProver_top
% 3.88/0.99      | v1_relat_1(X1) != iProver_top
% 3.88/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_19399,plain,
% 3.88/0.99      ( k1_relat_1(sK6) != k1_relat_1(sK7)
% 3.88/0.99      | sK7 = sK6
% 3.88/0.99      | sK5 = k1_xboole_0
% 3.88/0.99      | v1_funct_1(sK7) != iProver_top
% 3.88/0.99      | v1_funct_1(sK6) != iProver_top
% 3.88/0.99      | v1_relat_1(sK7) != iProver_top
% 3.88/0.99      | v1_relat_1(sK6) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_19376,c_18342]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_19400,plain,
% 3.88/0.99      ( ~ v1_funct_1(sK7)
% 3.88/0.99      | ~ v1_funct_1(sK6)
% 3.88/0.99      | ~ v1_relat_1(sK7)
% 3.88/0.99      | ~ v1_relat_1(sK6)
% 3.88/0.99      | k1_relat_1(sK6) != k1_relat_1(sK7)
% 3.88/0.99      | sK7 = sK6
% 3.88/0.99      | sK5 = k1_xboole_0 ),
% 3.88/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_19399]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_19406,plain,
% 3.88/0.99      ( k1_relat_1(sK6) != k1_relat_1(sK7) | sK7 = sK6 | sK5 = k1_xboole_0 ),
% 3.88/0.99      inference(global_propositional_subsumption,
% 3.88/0.99                [status(thm)],
% 3.88/0.99                [c_19399,c_37,c_39,c_40,c_42,c_15720,c_15741]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_19411,plain,
% 3.88/0.99      ( k1_relat_1(sK6) != sK4 | sK7 = sK6 | sK5 = k1_xboole_0 ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_18810,c_19406]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_19412,plain,
% 3.88/0.99      ( sK7 = sK6 | sK5 = k1_xboole_0 ),
% 3.88/0.99      inference(global_propositional_subsumption,
% 3.88/0.99                [status(thm)],
% 3.88/0.99                [c_19411,c_18813]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_18,plain,
% 3.88/0.99      ( r2_relset_1(X0,X1,X2,X2)
% 3.88/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.88/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_29,negated_conjecture,
% 3.88/0.99      ( ~ r2_relset_1(sK4,sK5,sK6,sK7) ),
% 3.88/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_489,plain,
% 3.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.88/0.99      | sK7 != X0
% 3.88/0.99      | sK6 != X0
% 3.88/0.99      | sK5 != X2
% 3.88/0.99      | sK4 != X1 ),
% 3.88/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_29]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_490,plain,
% 3.88/0.99      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | sK6 != sK7 ),
% 3.88/0.99      inference(unflattening,[status(thm)],[c_489]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_492,plain,
% 3.88/0.99      ( sK6 != sK7 ),
% 3.88/0.99      inference(global_propositional_subsumption,[status(thm)],[c_490,c_31]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_19432,plain,
% 3.88/0.99      ( sK5 = k1_xboole_0 ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_19412,c_492]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_24,plain,
% 3.88/0.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.88/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.88/0.99      | k1_xboole_0 = X1
% 3.88/0.99      | k1_xboole_0 = X0 ),
% 3.88/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_547,plain,
% 3.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.88/0.99      | sK6 != X0
% 3.88/0.99      | sK5 != k1_xboole_0
% 3.88/0.99      | sK4 != X1
% 3.88/0.99      | k1_xboole_0 = X1
% 3.88/0.99      | k1_xboole_0 = X0 ),
% 3.88/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_35]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_548,plain,
% 3.88/0.99      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0)))
% 3.88/0.99      | sK5 != k1_xboole_0
% 3.88/0.99      | k1_xboole_0 = sK6
% 3.88/0.99      | k1_xboole_0 = sK4 ),
% 3.88/0.99      inference(unflattening,[status(thm)],[c_547]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_18326,plain,
% 3.88/0.99      ( sK5 != k1_xboole_0
% 3.88/0.99      | k1_xboole_0 = sK6
% 3.88/0.99      | k1_xboole_0 = sK4
% 3.88/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) != iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_548]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_19452,plain,
% 3.88/0.99      ( sK6 = k1_xboole_0
% 3.88/0.99      | sK4 = k1_xboole_0
% 3.88/0.99      | k1_xboole_0 != k1_xboole_0
% 3.88/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) != iProver_top ),
% 3.88/0.99      inference(demodulation,[status(thm)],[c_19432,c_18326]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_19481,plain,
% 3.88/0.99      ( sK6 = k1_xboole_0
% 3.88/0.99      | sK4 = k1_xboole_0
% 3.88/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) != iProver_top ),
% 3.88/0.99      inference(equality_resolution_simp,[status(thm)],[c_19452]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_19460,plain,
% 3.88/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) = iProver_top ),
% 3.88/0.99      inference(demodulation,[status(thm)],[c_19432,c_18335]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_19485,plain,
% 3.88/0.99      ( sK6 = k1_xboole_0 | sK4 = k1_xboole_0 ),
% 3.88/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_19481,c_19460]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_2430,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_10014,plain,
% 3.88/0.99      ( X0 = X1 | X0 != k1_xboole_0 | X1 != k1_xboole_0 ),
% 3.88/0.99      inference(instantiation,[status(thm)],[c_2430]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_10104,plain,
% 3.88/0.99      ( sK7 != k1_xboole_0 | sK6 = sK7 | sK6 != k1_xboole_0 ),
% 3.88/0.99      inference(instantiation,[status(thm)],[c_10014]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_531,plain,
% 3.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.88/0.99      | sK7 != X0
% 3.88/0.99      | sK5 != k1_xboole_0
% 3.88/0.99      | sK4 != X1
% 3.88/0.99      | k1_xboole_0 = X1
% 3.88/0.99      | k1_xboole_0 = X0 ),
% 3.88/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_32]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_532,plain,
% 3.88/0.99      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0)))
% 3.88/0.99      | sK5 != k1_xboole_0
% 3.88/0.99      | k1_xboole_0 = sK7
% 3.88/0.99      | k1_xboole_0 = sK4 ),
% 3.88/0.99      inference(unflattening,[status(thm)],[c_531]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_18327,plain,
% 3.88/0.99      ( sK5 != k1_xboole_0
% 3.88/0.99      | k1_xboole_0 = sK7
% 3.88/0.99      | k1_xboole_0 = sK4
% 3.88/0.99      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) != iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_532]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_19451,plain,
% 3.88/0.99      ( sK7 = k1_xboole_0
% 3.88/0.99      | sK4 = k1_xboole_0
% 3.88/0.99      | k1_xboole_0 != k1_xboole_0
% 3.88/0.99      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) != iProver_top ),
% 3.88/0.99      inference(demodulation,[status(thm)],[c_19432,c_18327]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_19488,plain,
% 3.88/0.99      ( sK7 = k1_xboole_0
% 3.88/0.99      | sK4 = k1_xboole_0
% 3.88/0.99      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) != iProver_top ),
% 3.88/0.99      inference(equality_resolution_simp,[status(thm)],[c_19451]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_19459,plain,
% 3.88/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) = iProver_top ),
% 3.88/0.99      inference(demodulation,[status(thm)],[c_19432,c_18337]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_19492,plain,
% 3.88/0.99      ( sK7 = k1_xboole_0 | sK4 = k1_xboole_0 ),
% 3.88/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_19488,c_19459]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_19774,plain,
% 3.88/0.99      ( sK4 = k1_xboole_0 ),
% 3.88/0.99      inference(global_propositional_subsumption,
% 3.88/0.99                [status(thm)],
% 3.88/0.99                [c_19485,c_31,c_490,c_10104,c_19492]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_19449,plain,
% 3.88/0.99      ( k1_relset_1(sK4,k1_xboole_0,sK6) = k1_relat_1(sK6) ),
% 3.88/0.99      inference(demodulation,[status(thm)],[c_19432,c_18712]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_19786,plain,
% 3.88/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_relat_1(sK6) ),
% 3.88/0.99      inference(demodulation,[status(thm)],[c_19774,c_19449]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_27,plain,
% 3.88/0.99      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.88/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.88/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 3.88/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_580,plain,
% 3.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.88/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 3.88/0.99      | sK6 != X0
% 3.88/0.99      | sK5 != X1
% 3.88/0.99      | sK4 != k1_xboole_0 ),
% 3.88/0.99      inference(resolution_lifted,[status(thm)],[c_27,c_35]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_581,plain,
% 3.88/0.99      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5)))
% 3.88/0.99      | k1_relset_1(k1_xboole_0,sK5,sK6) = k1_xboole_0
% 3.88/0.99      | sK4 != k1_xboole_0 ),
% 3.88/0.99      inference(unflattening,[status(thm)],[c_580]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_18324,plain,
% 3.88/0.99      ( k1_relset_1(k1_xboole_0,sK5,sK6) = k1_xboole_0
% 3.88/0.99      | sK4 != k1_xboole_0
% 3.88/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5))) != iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_581]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_19456,plain,
% 3.88/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0
% 3.88/0.99      | sK4 != k1_xboole_0
% 3.88/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 3.88/0.99      inference(demodulation,[status(thm)],[c_19432,c_18324]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_19787,plain,
% 3.88/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.88/0.99      inference(demodulation,[status(thm)],[c_19774,c_19460]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_19997,plain,
% 3.88/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0 ),
% 3.88/0.99      inference(global_propositional_subsumption,
% 3.88/0.99                [status(thm)],
% 3.88/0.99                [c_19456,c_31,c_490,c_10104,c_19485,c_19492,c_19787]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_20131,plain,
% 3.88/0.99      ( k1_relat_1(sK6) = k1_xboole_0 ),
% 3.88/0.99      inference(light_normalisation,[status(thm)],[c_19786,c_19997]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_19450,plain,
% 3.88/0.99      ( k1_relset_1(sK4,k1_xboole_0,sK7) = k1_relat_1(sK7) ),
% 3.88/0.99      inference(demodulation,[status(thm)],[c_19432,c_18711]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_19785,plain,
% 3.88/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK7) = k1_relat_1(sK7) ),
% 3.88/0.99      inference(demodulation,[status(thm)],[c_19774,c_19450]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_19788,plain,
% 3.88/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.88/0.99      inference(demodulation,[status(thm)],[c_19774,c_19459]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_567,plain,
% 3.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.88/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 3.88/0.99      | sK7 != X0
% 3.88/0.99      | sK5 != X1
% 3.88/0.99      | sK4 != k1_xboole_0 ),
% 3.88/0.99      inference(resolution_lifted,[status(thm)],[c_27,c_32]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_568,plain,
% 3.88/0.99      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5)))
% 3.88/0.99      | k1_relset_1(k1_xboole_0,sK5,sK7) = k1_xboole_0
% 3.88/0.99      | sK4 != k1_xboole_0 ),
% 3.88/0.99      inference(unflattening,[status(thm)],[c_567]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_18325,plain,
% 3.88/0.99      ( k1_relset_1(k1_xboole_0,sK5,sK7) = k1_xboole_0
% 3.88/0.99      | sK4 != k1_xboole_0
% 3.88/0.99      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5))) != iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_568]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_19453,plain,
% 3.88/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK7) = k1_xboole_0
% 3.88/0.99      | sK4 != k1_xboole_0
% 3.88/0.99      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 3.88/0.99      inference(demodulation,[status(thm)],[c_19432,c_18325]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_19659,plain,
% 3.88/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK7) = k1_xboole_0
% 3.88/0.99      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 3.88/0.99      inference(global_propositional_subsumption,
% 3.88/0.99                [status(thm)],
% 3.88/0.99                [c_19453,c_31,c_490,c_10104,c_19485,c_19492]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_19973,plain,
% 3.88/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK7) = k1_xboole_0 ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_19788,c_19659]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_20091,plain,
% 3.88/0.99      ( k1_relat_1(sK7) = k1_xboole_0 ),
% 3.88/0.99      inference(light_normalisation,[status(thm)],[c_19785,c_19973]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_20095,plain,
% 3.88/0.99      ( k1_relat_1(X0) != k1_xboole_0
% 3.88/0.99      | sK7 = X0
% 3.88/0.99      | r2_hidden(sK1(X0,sK7),k1_relat_1(X0)) = iProver_top
% 3.88/0.99      | v1_funct_1(X0) != iProver_top
% 3.88/0.99      | v1_funct_1(sK7) != iProver_top
% 3.88/0.99      | v1_relat_1(X0) != iProver_top
% 3.88/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_20091,c_18341]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_20208,plain,
% 3.88/0.99      ( v1_relat_1(X0) != iProver_top
% 3.88/0.99      | k1_relat_1(X0) != k1_xboole_0
% 3.88/0.99      | sK7 = X0
% 3.88/0.99      | r2_hidden(sK1(X0,sK7),k1_relat_1(X0)) = iProver_top
% 3.88/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.88/0.99      inference(global_propositional_subsumption,
% 3.88/0.99                [status(thm)],
% 3.88/0.99                [c_20095,c_40,c_42,c_15720]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_20209,plain,
% 3.88/0.99      ( k1_relat_1(X0) != k1_xboole_0
% 3.88/0.99      | sK7 = X0
% 3.88/0.99      | r2_hidden(sK1(X0,sK7),k1_relat_1(X0)) = iProver_top
% 3.88/0.99      | v1_funct_1(X0) != iProver_top
% 3.88/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.88/0.99      inference(renaming,[status(thm)],[c_20208]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_20220,plain,
% 3.88/0.99      ( sK7 = sK6
% 3.88/0.99      | r2_hidden(sK1(sK6,sK7),k1_relat_1(sK6)) = iProver_top
% 3.88/0.99      | v1_funct_1(sK6) != iProver_top
% 3.88/0.99      | v1_relat_1(sK6) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_20131,c_20209]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_20225,plain,
% 3.88/0.99      ( sK7 = sK6
% 3.88/0.99      | r2_hidden(sK1(sK6,sK7),k1_xboole_0) = iProver_top
% 3.88/0.99      | v1_funct_1(sK6) != iProver_top
% 3.88/0.99      | v1_relat_1(sK6) != iProver_top ),
% 3.88/0.99      inference(light_normalisation,[status(thm)],[c_20220,c_20131]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_20319,plain,
% 3.88/0.99      ( sK7 = sK6 | r2_hidden(sK1(sK6,sK7),k1_xboole_0) = iProver_top ),
% 3.88/0.99      inference(global_propositional_subsumption,
% 3.88/0.99                [status(thm)],
% 3.88/0.99                [c_20225,c_37,c_39,c_15741]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_0,negated_conjecture,
% 3.88/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.88/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_4,plain,
% 3.88/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.88/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_476,plain,
% 3.88/0.99      ( ~ r2_hidden(X0,X1) | k1_xboole_0 != X1 ),
% 3.88/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_4]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_477,plain,
% 3.88/0.99      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.88/0.99      inference(unflattening,[status(thm)],[c_476]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_18329,plain,
% 3.88/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_477]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_20325,plain,
% 3.88/0.99      ( sK7 = sK6 ),
% 3.88/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_20319,c_18329]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_20339,plain,
% 3.88/0.99      ( sK6 != sK6 ),
% 3.88/0.99      inference(demodulation,[status(thm)],[c_20325,c_492]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_20340,plain,
% 3.88/0.99      ( $false ),
% 3.88/0.99      inference(equality_resolution_simp,[status(thm)],[c_20339]) ).
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.88/0.99  
% 3.88/0.99  ------                               Statistics
% 3.88/0.99  
% 3.88/0.99  ------ Selected
% 3.88/0.99  
% 3.88/0.99  total_time:                             0.43
% 3.88/0.99  
%------------------------------------------------------------------------------
