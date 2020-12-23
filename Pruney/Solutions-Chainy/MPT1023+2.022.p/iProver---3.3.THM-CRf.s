%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:44 EST 2020

% Result     : Theorem 3.12s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :  159 (1599 expanded)
%              Number of clauses        :   99 ( 489 expanded)
%              Number of leaves         :   15 ( 378 expanded)
%              Depth                    :   27
%              Number of atoms          :  525 (9890 expanded)
%              Number of equality atoms :  270 (2422 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
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

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ~ r2_relset_1(X0,X1,X2,sK4)
        & ! [X4] :
            ( k1_funct_1(sK4,X4) = k1_funct_1(X2,X4)
            | ~ m1_subset_1(X4,X0) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK4,X0,X1)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
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
          ( ~ r2_relset_1(sK1,sK2,sK3,X3)
          & ! [X4] :
              ( k1_funct_1(sK3,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,sK1) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X3,sK1,sK2)
          & v1_funct_1(X3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ~ r2_relset_1(sK1,sK2,sK3,sK4)
    & ! [X4] :
        ( k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4)
        | ~ m1_subset_1(X4,sK1) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f24,f35,f34])).

fof(f63,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f64,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f60,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f61,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
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

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
        & r2_hidden(sK0(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
            & r2_hidden(sK0(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f30])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f62,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f59,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f19])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f52])).

fof(f66,plain,(
    ~ r2_relset_1(sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f68,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f65,plain,(
    ! [X4] :
      ( k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4)
      | ~ m1_subset_1(X4,sK1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f27])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f69,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f42])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_485,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_25])).

cnf(c_486,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_485])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_488,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_486,c_24])).

cnf(c_1235,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1237,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1585,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1235,c_1237])).

cnf(c_1749,plain,
    ( k1_relat_1(sK4) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_488,c_1585])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_496,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_28])).

cnf(c_497,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_496])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_499,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_497,c_27])).

cnf(c_1233,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1586,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1233,c_1237])).

cnf(c_1817,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_499,c_1586])).

cnf(c_11,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | X1 = X0
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1239,plain,
    ( X0 = X1
    | k1_relat_1(X0) != k1_relat_1(X1)
    | r2_hidden(sK0(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2608,plain,
    ( k1_relat_1(X0) != sK1
    | sK4 = X0
    | sK2 = k1_xboole_0
    | r2_hidden(sK0(X0,sK4),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1749,c_1239])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_33,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_35,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1426,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1427,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1426])).

cnf(c_3054,plain,
    ( v1_funct_1(X0) != iProver_top
    | k1_relat_1(X0) != sK1
    | sK4 = X0
    | sK2 = k1_xboole_0
    | r2_hidden(sK0(X0,sK4),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2608,c_33,c_35,c_1427])).

cnf(c_3055,plain,
    ( k1_relat_1(X0) != sK1
    | sK4 = X0
    | sK2 = k1_xboole_0
    | r2_hidden(sK0(X0,sK4),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3054])).

cnf(c_3067,plain,
    ( sK4 = sK3
    | sK2 = k1_xboole_0
    | r2_hidden(sK0(sK3,sK4),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1817,c_3055])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_30,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_32,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_14,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_22,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_364,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK4 != X0
    | sK3 != X0
    | sK2 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_365,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | sK3 != sK4 ),
    inference(unflattening,[status(thm)],[c_364])).

cnf(c_1429,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1430,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1429])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1528,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | X0 = sK3 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1694,plain,
    ( ~ r1_tarski(sK3,sK3)
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1528])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1695,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_751,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1455,plain,
    ( sK4 != X0
    | sK3 != X0
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_751])).

cnf(c_1802,plain,
    ( sK4 != sK3
    | sK3 = sK4
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1455])).

cnf(c_3080,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK0(sK3,sK4),k1_relat_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3067,c_30,c_32,c_24,c_365,c_1430,c_1694,c_1695,c_1802])).

cnf(c_3086,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK0(sK3,sK4),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1817,c_3080])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1243,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1241,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2865,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1243,c_1241])).

cnf(c_3840,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(sK0(sK3,sK4),X0) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3086,c_2865])).

cnf(c_23,negated_conjecture,
    ( ~ m1_subset_1(X0,sK1)
    | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1236,plain,
    ( k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3886,plain,
    ( k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4))
    | sK2 = k1_xboole_0
    | r1_tarski(sK1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3840,c_1236])).

cnf(c_1245,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4068,plain,
    ( k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4))
    | sK2 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3886,c_1245])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X0 = X1
    | k1_funct_1(X0,sK0(X1,X0)) != k1_funct_1(X1,sK0(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1240,plain,
    ( X0 = X1
    | k1_funct_1(X0,sK0(X1,X0)) != k1_funct_1(X1,sK0(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4069,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK4)
    | sK4 = sK3
    | sK2 = k1_xboole_0
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4068,c_1240])).

cnf(c_4070,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | k1_relat_1(sK3) != k1_relat_1(sK4)
    | sK4 = sK3
    | sK2 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4069])).

cnf(c_4542,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK4)
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4069,c_29,c_27,c_26,c_24,c_365,c_1426,c_1429,c_1694,c_1695,c_1802,c_4070])).

cnf(c_4546,plain,
    ( k1_relat_1(sK3) != sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1749,c_4542])).

cnf(c_4578,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4546,c_1817])).

cnf(c_4600,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4578,c_1235])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_4606,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4600,c_3])).

cnf(c_4601,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4578,c_1233])).

cnf(c_4603,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4601,c_3])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_3148,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | r1_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3149,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3148])).

cnf(c_3151,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3149])).

cnf(c_3097,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
    | r1_tarski(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3098,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3097])).

cnf(c_3100,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3098])).

cnf(c_6,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2085,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2088,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2085])).

cnf(c_2076,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2079,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2076])).

cnf(c_1706,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1707,plain,
    ( sK3 = X0
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1706])).

cnf(c_1709,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1707])).

cnf(c_1689,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | r1_tarski(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1690,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(X0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1689])).

cnf(c_1692,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1690])).

cnf(c_1670,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4))
    | r1_tarski(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1671,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK4)) != iProver_top
    | r1_tarski(X0,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1670])).

cnf(c_1673,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) != iProver_top
    | r1_tarski(k1_xboole_0,sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1671])).

cnf(c_1607,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1608,plain,
    ( sK4 = X0
    | r1_tarski(X0,sK4) != iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1607])).

cnf(c_1610,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(sK4,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1608])).

cnf(c_1456,plain,
    ( sK4 != k1_xboole_0
    | sK3 = sK4
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1455])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4606,c_4603,c_3151,c_3100,c_2088,c_2079,c_1709,c_1692,c_1673,c_1610,c_1456,c_365,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:25:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.12/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/0.99  
% 3.12/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.12/0.99  
% 3.12/0.99  ------  iProver source info
% 3.12/0.99  
% 3.12/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.12/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.12/0.99  git: non_committed_changes: false
% 3.12/0.99  git: last_make_outside_of_git: false
% 3.12/0.99  
% 3.12/0.99  ------ 
% 3.12/0.99  
% 3.12/0.99  ------ Input Options
% 3.12/0.99  
% 3.12/0.99  --out_options                           all
% 3.12/0.99  --tptp_safe_out                         true
% 3.12/0.99  --problem_path                          ""
% 3.12/0.99  --include_path                          ""
% 3.12/0.99  --clausifier                            res/vclausify_rel
% 3.12/0.99  --clausifier_options                    --mode clausify
% 3.12/0.99  --stdin                                 false
% 3.12/0.99  --stats_out                             all
% 3.12/0.99  
% 3.12/0.99  ------ General Options
% 3.12/0.99  
% 3.12/0.99  --fof                                   false
% 3.12/0.99  --time_out_real                         305.
% 3.12/0.99  --time_out_virtual                      -1.
% 3.12/0.99  --symbol_type_check                     false
% 3.12/0.99  --clausify_out                          false
% 3.12/0.99  --sig_cnt_out                           false
% 3.12/0.99  --trig_cnt_out                          false
% 3.12/0.99  --trig_cnt_out_tolerance                1.
% 3.12/0.99  --trig_cnt_out_sk_spl                   false
% 3.12/0.99  --abstr_cl_out                          false
% 3.12/0.99  
% 3.12/0.99  ------ Global Options
% 3.12/0.99  
% 3.12/0.99  --schedule                              default
% 3.12/0.99  --add_important_lit                     false
% 3.12/0.99  --prop_solver_per_cl                    1000
% 3.12/0.99  --min_unsat_core                        false
% 3.12/0.99  --soft_assumptions                      false
% 3.12/0.99  --soft_lemma_size                       3
% 3.12/0.99  --prop_impl_unit_size                   0
% 3.12/0.99  --prop_impl_unit                        []
% 3.12/0.99  --share_sel_clauses                     true
% 3.12/0.99  --reset_solvers                         false
% 3.12/0.99  --bc_imp_inh                            [conj_cone]
% 3.12/0.99  --conj_cone_tolerance                   3.
% 3.12/0.99  --extra_neg_conj                        none
% 3.12/0.99  --large_theory_mode                     true
% 3.12/0.99  --prolific_symb_bound                   200
% 3.12/0.99  --lt_threshold                          2000
% 3.12/0.99  --clause_weak_htbl                      true
% 3.12/0.99  --gc_record_bc_elim                     false
% 3.12/0.99  
% 3.12/0.99  ------ Preprocessing Options
% 3.12/0.99  
% 3.12/0.99  --preprocessing_flag                    true
% 3.12/0.99  --time_out_prep_mult                    0.1
% 3.12/0.99  --splitting_mode                        input
% 3.12/0.99  --splitting_grd                         true
% 3.12/0.99  --splitting_cvd                         false
% 3.12/0.99  --splitting_cvd_svl                     false
% 3.12/0.99  --splitting_nvd                         32
% 3.12/0.99  --sub_typing                            true
% 3.12/0.99  --prep_gs_sim                           true
% 3.12/0.99  --prep_unflatten                        true
% 3.12/0.99  --prep_res_sim                          true
% 3.12/0.99  --prep_upred                            true
% 3.12/0.99  --prep_sem_filter                       exhaustive
% 3.12/0.99  --prep_sem_filter_out                   false
% 3.12/0.99  --pred_elim                             true
% 3.12/0.99  --res_sim_input                         true
% 3.12/0.99  --eq_ax_congr_red                       true
% 3.12/0.99  --pure_diseq_elim                       true
% 3.12/0.99  --brand_transform                       false
% 3.12/0.99  --non_eq_to_eq                          false
% 3.12/0.99  --prep_def_merge                        true
% 3.12/0.99  --prep_def_merge_prop_impl              false
% 3.12/0.99  --prep_def_merge_mbd                    true
% 3.12/0.99  --prep_def_merge_tr_red                 false
% 3.12/0.99  --prep_def_merge_tr_cl                  false
% 3.12/0.99  --smt_preprocessing                     true
% 3.12/0.99  --smt_ac_axioms                         fast
% 3.12/0.99  --preprocessed_out                      false
% 3.12/0.99  --preprocessed_stats                    false
% 3.12/0.99  
% 3.12/0.99  ------ Abstraction refinement Options
% 3.12/0.99  
% 3.12/0.99  --abstr_ref                             []
% 3.12/0.99  --abstr_ref_prep                        false
% 3.12/0.99  --abstr_ref_until_sat                   false
% 3.12/0.99  --abstr_ref_sig_restrict                funpre
% 3.12/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.12/0.99  --abstr_ref_under                       []
% 3.12/0.99  
% 3.12/0.99  ------ SAT Options
% 3.12/0.99  
% 3.12/0.99  --sat_mode                              false
% 3.12/0.99  --sat_fm_restart_options                ""
% 3.12/0.99  --sat_gr_def                            false
% 3.12/0.99  --sat_epr_types                         true
% 3.12/0.99  --sat_non_cyclic_types                  false
% 3.12/0.99  --sat_finite_models                     false
% 3.12/0.99  --sat_fm_lemmas                         false
% 3.12/0.99  --sat_fm_prep                           false
% 3.12/0.99  --sat_fm_uc_incr                        true
% 3.12/0.99  --sat_out_model                         small
% 3.12/0.99  --sat_out_clauses                       false
% 3.12/0.99  
% 3.12/0.99  ------ QBF Options
% 3.12/0.99  
% 3.12/0.99  --qbf_mode                              false
% 3.12/0.99  --qbf_elim_univ                         false
% 3.12/0.99  --qbf_dom_inst                          none
% 3.12/0.99  --qbf_dom_pre_inst                      false
% 3.12/0.99  --qbf_sk_in                             false
% 3.12/0.99  --qbf_pred_elim                         true
% 3.12/0.99  --qbf_split                             512
% 3.12/0.99  
% 3.12/0.99  ------ BMC1 Options
% 3.12/0.99  
% 3.12/0.99  --bmc1_incremental                      false
% 3.12/0.99  --bmc1_axioms                           reachable_all
% 3.12/0.99  --bmc1_min_bound                        0
% 3.12/0.99  --bmc1_max_bound                        -1
% 3.12/0.99  --bmc1_max_bound_default                -1
% 3.12/0.99  --bmc1_symbol_reachability              true
% 3.12/0.99  --bmc1_property_lemmas                  false
% 3.12/0.99  --bmc1_k_induction                      false
% 3.12/0.99  --bmc1_non_equiv_states                 false
% 3.12/0.99  --bmc1_deadlock                         false
% 3.12/0.99  --bmc1_ucm                              false
% 3.12/0.99  --bmc1_add_unsat_core                   none
% 3.12/0.99  --bmc1_unsat_core_children              false
% 3.12/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.12/0.99  --bmc1_out_stat                         full
% 3.12/0.99  --bmc1_ground_init                      false
% 3.12/0.99  --bmc1_pre_inst_next_state              false
% 3.12/0.99  --bmc1_pre_inst_state                   false
% 3.12/0.99  --bmc1_pre_inst_reach_state             false
% 3.12/0.99  --bmc1_out_unsat_core                   false
% 3.12/0.99  --bmc1_aig_witness_out                  false
% 3.12/0.99  --bmc1_verbose                          false
% 3.12/0.99  --bmc1_dump_clauses_tptp                false
% 3.12/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.12/0.99  --bmc1_dump_file                        -
% 3.12/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.12/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.12/0.99  --bmc1_ucm_extend_mode                  1
% 3.12/0.99  --bmc1_ucm_init_mode                    2
% 3.12/0.99  --bmc1_ucm_cone_mode                    none
% 3.12/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.12/0.99  --bmc1_ucm_relax_model                  4
% 3.12/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.12/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.12/0.99  --bmc1_ucm_layered_model                none
% 3.12/0.99  --bmc1_ucm_max_lemma_size               10
% 3.12/0.99  
% 3.12/0.99  ------ AIG Options
% 3.12/0.99  
% 3.12/0.99  --aig_mode                              false
% 3.12/0.99  
% 3.12/0.99  ------ Instantiation Options
% 3.12/0.99  
% 3.12/0.99  --instantiation_flag                    true
% 3.12/0.99  --inst_sos_flag                         false
% 3.12/0.99  --inst_sos_phase                        true
% 3.12/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.12/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.12/0.99  --inst_lit_sel_side                     num_symb
% 3.12/0.99  --inst_solver_per_active                1400
% 3.12/0.99  --inst_solver_calls_frac                1.
% 3.12/0.99  --inst_passive_queue_type               priority_queues
% 3.12/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.12/0.99  --inst_passive_queues_freq              [25;2]
% 3.12/0.99  --inst_dismatching                      true
% 3.12/0.99  --inst_eager_unprocessed_to_passive     true
% 3.12/0.99  --inst_prop_sim_given                   true
% 3.12/0.99  --inst_prop_sim_new                     false
% 3.12/0.99  --inst_subs_new                         false
% 3.12/0.99  --inst_eq_res_simp                      false
% 3.12/0.99  --inst_subs_given                       false
% 3.12/0.99  --inst_orphan_elimination               true
% 3.12/0.99  --inst_learning_loop_flag               true
% 3.12/0.99  --inst_learning_start                   3000
% 3.12/0.99  --inst_learning_factor                  2
% 3.12/0.99  --inst_start_prop_sim_after_learn       3
% 3.12/0.99  --inst_sel_renew                        solver
% 3.12/0.99  --inst_lit_activity_flag                true
% 3.12/0.99  --inst_restr_to_given                   false
% 3.12/0.99  --inst_activity_threshold               500
% 3.12/0.99  --inst_out_proof                        true
% 3.12/0.99  
% 3.12/0.99  ------ Resolution Options
% 3.12/0.99  
% 3.12/0.99  --resolution_flag                       true
% 3.12/0.99  --res_lit_sel                           adaptive
% 3.12/0.99  --res_lit_sel_side                      none
% 3.12/0.99  --res_ordering                          kbo
% 3.12/0.99  --res_to_prop_solver                    active
% 3.12/0.99  --res_prop_simpl_new                    false
% 3.12/0.99  --res_prop_simpl_given                  true
% 3.12/0.99  --res_passive_queue_type                priority_queues
% 3.12/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.12/0.99  --res_passive_queues_freq               [15;5]
% 3.12/0.99  --res_forward_subs                      full
% 3.12/0.99  --res_backward_subs                     full
% 3.12/0.99  --res_forward_subs_resolution           true
% 3.12/0.99  --res_backward_subs_resolution          true
% 3.12/0.99  --res_orphan_elimination                true
% 3.12/0.99  --res_time_limit                        2.
% 3.12/0.99  --res_out_proof                         true
% 3.12/0.99  
% 3.12/0.99  ------ Superposition Options
% 3.12/0.99  
% 3.12/0.99  --superposition_flag                    true
% 3.12/0.99  --sup_passive_queue_type                priority_queues
% 3.12/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.12/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.12/0.99  --demod_completeness_check              fast
% 3.12/0.99  --demod_use_ground                      true
% 3.12/0.99  --sup_to_prop_solver                    passive
% 3.12/0.99  --sup_prop_simpl_new                    true
% 3.12/0.99  --sup_prop_simpl_given                  true
% 3.12/0.99  --sup_fun_splitting                     false
% 3.12/0.99  --sup_smt_interval                      50000
% 3.12/0.99  
% 3.12/0.99  ------ Superposition Simplification Setup
% 3.12/0.99  
% 3.12/0.99  --sup_indices_passive                   []
% 3.12/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.12/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/0.99  --sup_full_bw                           [BwDemod]
% 3.12/0.99  --sup_immed_triv                        [TrivRules]
% 3.12/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.12/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/0.99  --sup_immed_bw_main                     []
% 3.12/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.12/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.12/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.12/0.99  
% 3.12/0.99  ------ Combination Options
% 3.12/0.99  
% 3.12/0.99  --comb_res_mult                         3
% 3.12/0.99  --comb_sup_mult                         2
% 3.12/0.99  --comb_inst_mult                        10
% 3.12/0.99  
% 3.12/0.99  ------ Debug Options
% 3.12/0.99  
% 3.12/0.99  --dbg_backtrace                         false
% 3.12/0.99  --dbg_dump_prop_clauses                 false
% 3.12/0.99  --dbg_dump_prop_clauses_file            -
% 3.12/0.99  --dbg_out_stat                          false
% 3.12/0.99  ------ Parsing...
% 3.12/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.12/0.99  
% 3.12/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.12/0.99  
% 3.12/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.12/0.99  
% 3.12/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.12/0.99  ------ Proving...
% 3.12/0.99  ------ Problem Properties 
% 3.12/0.99  
% 3.12/0.99  
% 3.12/0.99  clauses                                 25
% 3.12/0.99  conjectures                             5
% 3.12/0.99  EPR                                     5
% 3.12/0.99  Horn                                    19
% 3.12/0.99  unary                                   9
% 3.12/0.99  binary                                  7
% 3.12/0.99  lits                                    60
% 3.12/0.99  lits eq                                 28
% 3.12/0.99  fd_pure                                 0
% 3.12/0.99  fd_pseudo                               0
% 3.12/0.99  fd_cond                                 1
% 3.12/0.99  fd_pseudo_cond                          3
% 3.12/0.99  AC symbols                              0
% 3.12/0.99  
% 3.12/0.99  ------ Schedule dynamic 5 is on 
% 3.12/0.99  
% 3.12/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.12/0.99  
% 3.12/0.99  
% 3.12/0.99  ------ 
% 3.12/0.99  Current options:
% 3.12/0.99  ------ 
% 3.12/0.99  
% 3.12/0.99  ------ Input Options
% 3.12/0.99  
% 3.12/0.99  --out_options                           all
% 3.12/0.99  --tptp_safe_out                         true
% 3.12/0.99  --problem_path                          ""
% 3.12/0.99  --include_path                          ""
% 3.12/0.99  --clausifier                            res/vclausify_rel
% 3.12/0.99  --clausifier_options                    --mode clausify
% 3.12/0.99  --stdin                                 false
% 3.12/0.99  --stats_out                             all
% 3.12/0.99  
% 3.12/0.99  ------ General Options
% 3.12/0.99  
% 3.12/0.99  --fof                                   false
% 3.12/0.99  --time_out_real                         305.
% 3.12/0.99  --time_out_virtual                      -1.
% 3.12/0.99  --symbol_type_check                     false
% 3.12/0.99  --clausify_out                          false
% 3.12/0.99  --sig_cnt_out                           false
% 3.12/0.99  --trig_cnt_out                          false
% 3.12/0.99  --trig_cnt_out_tolerance                1.
% 3.12/0.99  --trig_cnt_out_sk_spl                   false
% 3.12/0.99  --abstr_cl_out                          false
% 3.12/0.99  
% 3.12/0.99  ------ Global Options
% 3.12/0.99  
% 3.12/0.99  --schedule                              default
% 3.12/0.99  --add_important_lit                     false
% 3.12/0.99  --prop_solver_per_cl                    1000
% 3.12/0.99  --min_unsat_core                        false
% 3.12/0.99  --soft_assumptions                      false
% 3.12/0.99  --soft_lemma_size                       3
% 3.12/0.99  --prop_impl_unit_size                   0
% 3.12/0.99  --prop_impl_unit                        []
% 3.12/0.99  --share_sel_clauses                     true
% 3.12/0.99  --reset_solvers                         false
% 3.12/0.99  --bc_imp_inh                            [conj_cone]
% 3.12/0.99  --conj_cone_tolerance                   3.
% 3.12/0.99  --extra_neg_conj                        none
% 3.12/0.99  --large_theory_mode                     true
% 3.12/0.99  --prolific_symb_bound                   200
% 3.12/0.99  --lt_threshold                          2000
% 3.12/0.99  --clause_weak_htbl                      true
% 3.12/0.99  --gc_record_bc_elim                     false
% 3.12/0.99  
% 3.12/0.99  ------ Preprocessing Options
% 3.12/0.99  
% 3.12/0.99  --preprocessing_flag                    true
% 3.12/0.99  --time_out_prep_mult                    0.1
% 3.12/0.99  --splitting_mode                        input
% 3.12/0.99  --splitting_grd                         true
% 3.12/0.99  --splitting_cvd                         false
% 3.12/0.99  --splitting_cvd_svl                     false
% 3.12/0.99  --splitting_nvd                         32
% 3.12/0.99  --sub_typing                            true
% 3.12/0.99  --prep_gs_sim                           true
% 3.12/0.99  --prep_unflatten                        true
% 3.12/0.99  --prep_res_sim                          true
% 3.12/0.99  --prep_upred                            true
% 3.12/0.99  --prep_sem_filter                       exhaustive
% 3.12/0.99  --prep_sem_filter_out                   false
% 3.12/0.99  --pred_elim                             true
% 3.12/0.99  --res_sim_input                         true
% 3.12/0.99  --eq_ax_congr_red                       true
% 3.12/0.99  --pure_diseq_elim                       true
% 3.12/0.99  --brand_transform                       false
% 3.12/0.99  --non_eq_to_eq                          false
% 3.12/0.99  --prep_def_merge                        true
% 3.12/0.99  --prep_def_merge_prop_impl              false
% 3.12/0.99  --prep_def_merge_mbd                    true
% 3.12/0.99  --prep_def_merge_tr_red                 false
% 3.12/0.99  --prep_def_merge_tr_cl                  false
% 3.12/0.99  --smt_preprocessing                     true
% 3.12/0.99  --smt_ac_axioms                         fast
% 3.12/0.99  --preprocessed_out                      false
% 3.12/0.99  --preprocessed_stats                    false
% 3.12/0.99  
% 3.12/0.99  ------ Abstraction refinement Options
% 3.12/0.99  
% 3.12/0.99  --abstr_ref                             []
% 3.12/0.99  --abstr_ref_prep                        false
% 3.12/0.99  --abstr_ref_until_sat                   false
% 3.12/0.99  --abstr_ref_sig_restrict                funpre
% 3.12/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.12/0.99  --abstr_ref_under                       []
% 3.12/0.99  
% 3.12/0.99  ------ SAT Options
% 3.12/0.99  
% 3.12/0.99  --sat_mode                              false
% 3.12/0.99  --sat_fm_restart_options                ""
% 3.12/0.99  --sat_gr_def                            false
% 3.12/0.99  --sat_epr_types                         true
% 3.12/0.99  --sat_non_cyclic_types                  false
% 3.12/0.99  --sat_finite_models                     false
% 3.12/0.99  --sat_fm_lemmas                         false
% 3.12/0.99  --sat_fm_prep                           false
% 3.12/0.99  --sat_fm_uc_incr                        true
% 3.12/0.99  --sat_out_model                         small
% 3.12/0.99  --sat_out_clauses                       false
% 3.12/0.99  
% 3.12/0.99  ------ QBF Options
% 3.12/0.99  
% 3.12/0.99  --qbf_mode                              false
% 3.12/0.99  --qbf_elim_univ                         false
% 3.12/0.99  --qbf_dom_inst                          none
% 3.12/0.99  --qbf_dom_pre_inst                      false
% 3.12/0.99  --qbf_sk_in                             false
% 3.12/0.99  --qbf_pred_elim                         true
% 3.12/0.99  --qbf_split                             512
% 3.12/0.99  
% 3.12/0.99  ------ BMC1 Options
% 3.12/0.99  
% 3.12/0.99  --bmc1_incremental                      false
% 3.12/0.99  --bmc1_axioms                           reachable_all
% 3.12/0.99  --bmc1_min_bound                        0
% 3.12/0.99  --bmc1_max_bound                        -1
% 3.12/0.99  --bmc1_max_bound_default                -1
% 3.12/0.99  --bmc1_symbol_reachability              true
% 3.12/0.99  --bmc1_property_lemmas                  false
% 3.12/0.99  --bmc1_k_induction                      false
% 3.12/0.99  --bmc1_non_equiv_states                 false
% 3.12/0.99  --bmc1_deadlock                         false
% 3.12/0.99  --bmc1_ucm                              false
% 3.12/0.99  --bmc1_add_unsat_core                   none
% 3.12/0.99  --bmc1_unsat_core_children              false
% 3.12/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.12/0.99  --bmc1_out_stat                         full
% 3.12/0.99  --bmc1_ground_init                      false
% 3.12/0.99  --bmc1_pre_inst_next_state              false
% 3.12/0.99  --bmc1_pre_inst_state                   false
% 3.12/0.99  --bmc1_pre_inst_reach_state             false
% 3.12/0.99  --bmc1_out_unsat_core                   false
% 3.12/0.99  --bmc1_aig_witness_out                  false
% 3.12/0.99  --bmc1_verbose                          false
% 3.12/0.99  --bmc1_dump_clauses_tptp                false
% 3.12/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.12/0.99  --bmc1_dump_file                        -
% 3.12/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.12/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.12/0.99  --bmc1_ucm_extend_mode                  1
% 3.12/0.99  --bmc1_ucm_init_mode                    2
% 3.12/0.99  --bmc1_ucm_cone_mode                    none
% 3.12/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.12/0.99  --bmc1_ucm_relax_model                  4
% 3.12/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.12/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.12/0.99  --bmc1_ucm_layered_model                none
% 3.12/0.99  --bmc1_ucm_max_lemma_size               10
% 3.12/0.99  
% 3.12/0.99  ------ AIG Options
% 3.12/0.99  
% 3.12/0.99  --aig_mode                              false
% 3.12/0.99  
% 3.12/0.99  ------ Instantiation Options
% 3.12/0.99  
% 3.12/0.99  --instantiation_flag                    true
% 3.12/0.99  --inst_sos_flag                         false
% 3.12/0.99  --inst_sos_phase                        true
% 3.12/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.12/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.12/0.99  --inst_lit_sel_side                     none
% 3.12/0.99  --inst_solver_per_active                1400
% 3.12/0.99  --inst_solver_calls_frac                1.
% 3.12/0.99  --inst_passive_queue_type               priority_queues
% 3.12/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.12/0.99  --inst_passive_queues_freq              [25;2]
% 3.12/0.99  --inst_dismatching                      true
% 3.12/0.99  --inst_eager_unprocessed_to_passive     true
% 3.12/0.99  --inst_prop_sim_given                   true
% 3.12/0.99  --inst_prop_sim_new                     false
% 3.12/0.99  --inst_subs_new                         false
% 3.12/0.99  --inst_eq_res_simp                      false
% 3.12/0.99  --inst_subs_given                       false
% 3.12/0.99  --inst_orphan_elimination               true
% 3.12/0.99  --inst_learning_loop_flag               true
% 3.12/0.99  --inst_learning_start                   3000
% 3.12/0.99  --inst_learning_factor                  2
% 3.12/0.99  --inst_start_prop_sim_after_learn       3
% 3.12/0.99  --inst_sel_renew                        solver
% 3.12/0.99  --inst_lit_activity_flag                true
% 3.12/0.99  --inst_restr_to_given                   false
% 3.12/0.99  --inst_activity_threshold               500
% 3.12/0.99  --inst_out_proof                        true
% 3.12/0.99  
% 3.12/0.99  ------ Resolution Options
% 3.12/0.99  
% 3.12/0.99  --resolution_flag                       false
% 3.12/0.99  --res_lit_sel                           adaptive
% 3.12/0.99  --res_lit_sel_side                      none
% 3.12/0.99  --res_ordering                          kbo
% 3.12/0.99  --res_to_prop_solver                    active
% 3.12/0.99  --res_prop_simpl_new                    false
% 3.12/0.99  --res_prop_simpl_given                  true
% 3.12/0.99  --res_passive_queue_type                priority_queues
% 3.12/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.12/0.99  --res_passive_queues_freq               [15;5]
% 3.12/0.99  --res_forward_subs                      full
% 3.12/0.99  --res_backward_subs                     full
% 3.12/0.99  --res_forward_subs_resolution           true
% 3.12/0.99  --res_backward_subs_resolution          true
% 3.12/0.99  --res_orphan_elimination                true
% 3.12/0.99  --res_time_limit                        2.
% 3.12/0.99  --res_out_proof                         true
% 3.12/0.99  
% 3.12/0.99  ------ Superposition Options
% 3.12/0.99  
% 3.12/0.99  --superposition_flag                    true
% 3.12/0.99  --sup_passive_queue_type                priority_queues
% 3.12/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.12/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.12/0.99  --demod_completeness_check              fast
% 3.12/0.99  --demod_use_ground                      true
% 3.12/0.99  --sup_to_prop_solver                    passive
% 3.12/0.99  --sup_prop_simpl_new                    true
% 3.12/0.99  --sup_prop_simpl_given                  true
% 3.12/0.99  --sup_fun_splitting                     false
% 3.12/0.99  --sup_smt_interval                      50000
% 3.12/0.99  
% 3.12/0.99  ------ Superposition Simplification Setup
% 3.12/0.99  
% 3.12/0.99  --sup_indices_passive                   []
% 3.12/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.12/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/0.99  --sup_full_bw                           [BwDemod]
% 3.12/0.99  --sup_immed_triv                        [TrivRules]
% 3.12/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.12/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/0.99  --sup_immed_bw_main                     []
% 3.12/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.12/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.12/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.12/0.99  
% 3.12/0.99  ------ Combination Options
% 3.12/0.99  
% 3.12/0.99  --comb_res_mult                         3
% 3.12/0.99  --comb_sup_mult                         2
% 3.12/0.99  --comb_inst_mult                        10
% 3.12/0.99  
% 3.12/0.99  ------ Debug Options
% 3.12/0.99  
% 3.12/0.99  --dbg_backtrace                         false
% 3.12/0.99  --dbg_dump_prop_clauses                 false
% 3.12/0.99  --dbg_dump_prop_clauses_file            -
% 3.12/0.99  --dbg_out_stat                          false
% 3.12/0.99  
% 3.12/0.99  
% 3.12/0.99  
% 3.12/0.99  
% 3.12/0.99  ------ Proving...
% 3.12/0.99  
% 3.12/0.99  
% 3.12/0.99  % SZS status Theorem for theBenchmark.p
% 3.12/0.99  
% 3.12/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.12/0.99  
% 3.12/0.99  fof(f10,axiom,(
% 3.12/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f21,plain,(
% 3.12/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.12/0.99    inference(ennf_transformation,[],[f10])).
% 3.12/0.99  
% 3.12/0.99  fof(f22,plain,(
% 3.12/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.12/0.99    inference(flattening,[],[f21])).
% 3.12/0.99  
% 3.12/0.99  fof(f33,plain,(
% 3.12/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.12/0.99    inference(nnf_transformation,[],[f22])).
% 3.12/0.99  
% 3.12/0.99  fof(f53,plain,(
% 3.12/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.12/0.99    inference(cnf_transformation,[],[f33])).
% 3.12/0.99  
% 3.12/0.99  fof(f11,conjecture,(
% 3.12/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 3.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f12,negated_conjecture,(
% 3.12/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 3.12/0.99    inference(negated_conjecture,[],[f11])).
% 3.12/0.99  
% 3.12/0.99  fof(f23,plain,(
% 3.12/0.99    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.12/0.99    inference(ennf_transformation,[],[f12])).
% 3.12/0.99  
% 3.12/0.99  fof(f24,plain,(
% 3.12/0.99    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.12/0.99    inference(flattening,[],[f23])).
% 3.12/0.99  
% 3.12/0.99  fof(f35,plain,(
% 3.12/0.99    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK4) & ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(X2,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK4,X0,X1) & v1_funct_1(sK4))) )),
% 3.12/0.99    introduced(choice_axiom,[])).
% 3.12/0.99  
% 3.12/0.99  fof(f34,plain,(
% 3.12/0.99    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK1,sK2,sK3,X3) & ! [X4] : (k1_funct_1(sK3,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 3.12/0.99    introduced(choice_axiom,[])).
% 3.12/0.99  
% 3.12/0.99  fof(f36,plain,(
% 3.12/0.99    (~r2_relset_1(sK1,sK2,sK3,sK4) & ! [X4] : (k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4) | ~m1_subset_1(X4,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 3.12/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f24,f35,f34])).
% 3.12/0.99  
% 3.12/0.99  fof(f63,plain,(
% 3.12/0.99    v1_funct_2(sK4,sK1,sK2)),
% 3.12/0.99    inference(cnf_transformation,[],[f36])).
% 3.12/0.99  
% 3.12/0.99  fof(f64,plain,(
% 3.12/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.12/0.99    inference(cnf_transformation,[],[f36])).
% 3.12/0.99  
% 3.12/0.99  fof(f8,axiom,(
% 3.12/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f18,plain,(
% 3.12/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.12/0.99    inference(ennf_transformation,[],[f8])).
% 3.12/0.99  
% 3.12/0.99  fof(f50,plain,(
% 3.12/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.12/0.99    inference(cnf_transformation,[],[f18])).
% 3.12/0.99  
% 3.12/0.99  fof(f60,plain,(
% 3.12/0.99    v1_funct_2(sK3,sK1,sK2)),
% 3.12/0.99    inference(cnf_transformation,[],[f36])).
% 3.12/0.99  
% 3.12/0.99  fof(f61,plain,(
% 3.12/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.12/0.99    inference(cnf_transformation,[],[f36])).
% 3.12/0.99  
% 3.12/0.99  fof(f6,axiom,(
% 3.12/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 3.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f15,plain,(
% 3.12/0.99    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.12/0.99    inference(ennf_transformation,[],[f6])).
% 3.12/0.99  
% 3.12/0.99  fof(f16,plain,(
% 3.12/0.99    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.12/0.99    inference(flattening,[],[f15])).
% 3.12/0.99  
% 3.12/0.99  fof(f30,plain,(
% 3.12/0.99    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0))))),
% 3.12/0.99    introduced(choice_axiom,[])).
% 3.12/0.99  
% 3.12/0.99  fof(f31,plain,(
% 3.12/0.99    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.12/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f30])).
% 3.12/0.99  
% 3.12/0.99  fof(f47,plain,(
% 3.12/0.99    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.12/0.99    inference(cnf_transformation,[],[f31])).
% 3.12/0.99  
% 3.12/0.99  fof(f62,plain,(
% 3.12/0.99    v1_funct_1(sK4)),
% 3.12/0.99    inference(cnf_transformation,[],[f36])).
% 3.12/0.99  
% 3.12/0.99  fof(f7,axiom,(
% 3.12/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f17,plain,(
% 3.12/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.12/0.99    inference(ennf_transformation,[],[f7])).
% 3.12/0.99  
% 3.12/0.99  fof(f49,plain,(
% 3.12/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.12/0.99    inference(cnf_transformation,[],[f17])).
% 3.12/0.99  
% 3.12/0.99  fof(f59,plain,(
% 3.12/0.99    v1_funct_1(sK3)),
% 3.12/0.99    inference(cnf_transformation,[],[f36])).
% 3.12/0.99  
% 3.12/0.99  fof(f9,axiom,(
% 3.12/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f19,plain,(
% 3.12/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.12/0.99    inference(ennf_transformation,[],[f9])).
% 3.12/0.99  
% 3.12/0.99  fof(f20,plain,(
% 3.12/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.12/0.99    inference(flattening,[],[f19])).
% 3.12/0.99  
% 3.12/0.99  fof(f32,plain,(
% 3.12/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.12/0.99    inference(nnf_transformation,[],[f20])).
% 3.12/0.99  
% 3.12/0.99  fof(f52,plain,(
% 3.12/0.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.12/0.99    inference(cnf_transformation,[],[f32])).
% 3.12/0.99  
% 3.12/0.99  fof(f71,plain,(
% 3.12/0.99    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.12/0.99    inference(equality_resolution,[],[f52])).
% 3.12/0.99  
% 3.12/0.99  fof(f66,plain,(
% 3.12/0.99    ~r2_relset_1(sK1,sK2,sK3,sK4)),
% 3.12/0.99    inference(cnf_transformation,[],[f36])).
% 3.12/0.99  
% 3.12/0.99  fof(f1,axiom,(
% 3.12/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f25,plain,(
% 3.12/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.12/0.99    inference(nnf_transformation,[],[f1])).
% 3.12/0.99  
% 3.12/0.99  fof(f26,plain,(
% 3.12/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.12/0.99    inference(flattening,[],[f25])).
% 3.12/0.99  
% 3.12/0.99  fof(f39,plain,(
% 3.12/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.12/0.99    inference(cnf_transformation,[],[f26])).
% 3.12/0.99  
% 3.12/0.99  fof(f37,plain,(
% 3.12/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.12/0.99    inference(cnf_transformation,[],[f26])).
% 3.12/0.99  
% 3.12/0.99  fof(f68,plain,(
% 3.12/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.12/0.99    inference(equality_resolution,[],[f37])).
% 3.12/0.99  
% 3.12/0.99  fof(f4,axiom,(
% 3.12/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f29,plain,(
% 3.12/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.12/0.99    inference(nnf_transformation,[],[f4])).
% 3.12/0.99  
% 3.12/0.99  fof(f45,plain,(
% 3.12/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.12/0.99    inference(cnf_transformation,[],[f29])).
% 3.12/0.99  
% 3.12/0.99  fof(f5,axiom,(
% 3.12/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f13,plain,(
% 3.12/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.12/0.99    inference(ennf_transformation,[],[f5])).
% 3.12/0.99  
% 3.12/0.99  fof(f14,plain,(
% 3.12/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.12/0.99    inference(flattening,[],[f13])).
% 3.12/0.99  
% 3.12/0.99  fof(f46,plain,(
% 3.12/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.12/0.99    inference(cnf_transformation,[],[f14])).
% 3.12/0.99  
% 3.12/0.99  fof(f65,plain,(
% 3.12/0.99    ( ! [X4] : (k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4) | ~m1_subset_1(X4,sK1)) )),
% 3.12/0.99    inference(cnf_transformation,[],[f36])).
% 3.12/0.99  
% 3.12/0.99  fof(f48,plain,(
% 3.12/0.99    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.12/0.99    inference(cnf_transformation,[],[f31])).
% 3.12/0.99  
% 3.12/0.99  fof(f2,axiom,(
% 3.12/0.99    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f27,plain,(
% 3.12/0.99    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.12/0.99    inference(nnf_transformation,[],[f2])).
% 3.12/0.99  
% 3.12/0.99  fof(f28,plain,(
% 3.12/0.99    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.12/0.99    inference(flattening,[],[f27])).
% 3.12/0.99  
% 3.12/0.99  fof(f42,plain,(
% 3.12/0.99    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 3.12/0.99    inference(cnf_transformation,[],[f28])).
% 3.12/0.99  
% 3.12/0.99  fof(f69,plain,(
% 3.12/0.99    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.12/0.99    inference(equality_resolution,[],[f42])).
% 3.12/0.99  
% 3.12/0.99  fof(f44,plain,(
% 3.12/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.12/0.99    inference(cnf_transformation,[],[f29])).
% 3.12/0.99  
% 3.12/0.99  fof(f3,axiom,(
% 3.12/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f43,plain,(
% 3.12/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.12/0.99    inference(cnf_transformation,[],[f3])).
% 3.12/0.99  
% 3.12/0.99  cnf(c_21,plain,
% 3.12/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.12/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.12/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.12/0.99      | k1_xboole_0 = X2 ),
% 3.12/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_25,negated_conjecture,
% 3.12/0.99      ( v1_funct_2(sK4,sK1,sK2) ),
% 3.12/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_485,plain,
% 3.12/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.12/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.12/0.99      | sK4 != X0
% 3.12/0.99      | sK2 != X2
% 3.12/0.99      | sK1 != X1
% 3.12/0.99      | k1_xboole_0 = X2 ),
% 3.12/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_25]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_486,plain,
% 3.12/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.12/0.99      | k1_relset_1(sK1,sK2,sK4) = sK1
% 3.12/0.99      | k1_xboole_0 = sK2 ),
% 3.12/0.99      inference(unflattening,[status(thm)],[c_485]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_24,negated_conjecture,
% 3.12/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.12/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_488,plain,
% 3.12/0.99      ( k1_relset_1(sK1,sK2,sK4) = sK1 | k1_xboole_0 = sK2 ),
% 3.12/0.99      inference(global_propositional_subsumption,
% 3.12/0.99                [status(thm)],
% 3.12/0.99                [c_486,c_24]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1235,plain,
% 3.12/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_13,plain,
% 3.12/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.12/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.12/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1237,plain,
% 3.12/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.12/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1585,plain,
% 3.12/0.99      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_1235,c_1237]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1749,plain,
% 3.12/0.99      ( k1_relat_1(sK4) = sK1 | sK2 = k1_xboole_0 ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_488,c_1585]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_28,negated_conjecture,
% 3.12/0.99      ( v1_funct_2(sK3,sK1,sK2) ),
% 3.12/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_496,plain,
% 3.12/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.12/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.12/0.99      | sK3 != X0
% 3.12/0.99      | sK2 != X2
% 3.12/0.99      | sK1 != X1
% 3.12/0.99      | k1_xboole_0 = X2 ),
% 3.12/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_28]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_497,plain,
% 3.12/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.12/0.99      | k1_relset_1(sK1,sK2,sK3) = sK1
% 3.12/0.99      | k1_xboole_0 = sK2 ),
% 3.12/0.99      inference(unflattening,[status(thm)],[c_496]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_27,negated_conjecture,
% 3.12/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.12/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_499,plain,
% 3.12/0.99      ( k1_relset_1(sK1,sK2,sK3) = sK1 | k1_xboole_0 = sK2 ),
% 3.12/0.99      inference(global_propositional_subsumption,
% 3.12/0.99                [status(thm)],
% 3.12/0.99                [c_497,c_27]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1233,plain,
% 3.12/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1586,plain,
% 3.12/0.99      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_1233,c_1237]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1817,plain,
% 3.12/0.99      ( k1_relat_1(sK3) = sK1 | sK2 = k1_xboole_0 ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_499,c_1586]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_11,plain,
% 3.12/0.99      ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
% 3.12/0.99      | ~ v1_relat_1(X1)
% 3.12/0.99      | ~ v1_relat_1(X0)
% 3.12/0.99      | ~ v1_funct_1(X1)
% 3.12/0.99      | ~ v1_funct_1(X0)
% 3.12/0.99      | X1 = X0
% 3.12/0.99      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 3.12/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1239,plain,
% 3.12/0.99      ( X0 = X1
% 3.12/0.99      | k1_relat_1(X0) != k1_relat_1(X1)
% 3.12/0.99      | r2_hidden(sK0(X1,X0),k1_relat_1(X1)) = iProver_top
% 3.12/0.99      | v1_relat_1(X1) != iProver_top
% 3.12/0.99      | v1_relat_1(X0) != iProver_top
% 3.12/0.99      | v1_funct_1(X0) != iProver_top
% 3.12/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_2608,plain,
% 3.12/0.99      ( k1_relat_1(X0) != sK1
% 3.12/0.99      | sK4 = X0
% 3.12/0.99      | sK2 = k1_xboole_0
% 3.12/0.99      | r2_hidden(sK0(X0,sK4),k1_relat_1(X0)) = iProver_top
% 3.12/0.99      | v1_relat_1(X0) != iProver_top
% 3.12/0.99      | v1_relat_1(sK4) != iProver_top
% 3.12/0.99      | v1_funct_1(X0) != iProver_top
% 3.12/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_1749,c_1239]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_26,negated_conjecture,
% 3.12/0.99      ( v1_funct_1(sK4) ),
% 3.12/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_33,plain,
% 3.12/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_35,plain,
% 3.12/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_12,plain,
% 3.12/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.12/0.99      | v1_relat_1(X0) ),
% 3.12/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1426,plain,
% 3.12/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.12/0.99      | v1_relat_1(sK4) ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1427,plain,
% 3.12/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.12/0.99      | v1_relat_1(sK4) = iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_1426]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_3054,plain,
% 3.12/0.99      ( v1_funct_1(X0) != iProver_top
% 3.12/0.99      | k1_relat_1(X0) != sK1
% 3.12/0.99      | sK4 = X0
% 3.12/0.99      | sK2 = k1_xboole_0
% 3.12/0.99      | r2_hidden(sK0(X0,sK4),k1_relat_1(X0)) = iProver_top
% 3.12/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.12/0.99      inference(global_propositional_subsumption,
% 3.12/0.99                [status(thm)],
% 3.12/0.99                [c_2608,c_33,c_35,c_1427]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_3055,plain,
% 3.12/0.99      ( k1_relat_1(X0) != sK1
% 3.12/0.99      | sK4 = X0
% 3.12/0.99      | sK2 = k1_xboole_0
% 3.12/0.99      | r2_hidden(sK0(X0,sK4),k1_relat_1(X0)) = iProver_top
% 3.12/0.99      | v1_relat_1(X0) != iProver_top
% 3.12/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.12/0.99      inference(renaming,[status(thm)],[c_3054]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_3067,plain,
% 3.12/0.99      ( sK4 = sK3
% 3.12/0.99      | sK2 = k1_xboole_0
% 3.12/0.99      | r2_hidden(sK0(sK3,sK4),k1_relat_1(sK3)) = iProver_top
% 3.12/0.99      | v1_relat_1(sK3) != iProver_top
% 3.12/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_1817,c_3055]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_29,negated_conjecture,
% 3.12/0.99      ( v1_funct_1(sK3) ),
% 3.12/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_30,plain,
% 3.12/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_32,plain,
% 3.12/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_14,plain,
% 3.12/0.99      ( r2_relset_1(X0,X1,X2,X2)
% 3.12/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.12/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_22,negated_conjecture,
% 3.12/0.99      ( ~ r2_relset_1(sK1,sK2,sK3,sK4) ),
% 3.12/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_364,plain,
% 3.12/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.12/0.99      | sK4 != X0
% 3.12/0.99      | sK3 != X0
% 3.12/0.99      | sK2 != X2
% 3.12/0.99      | sK1 != X1 ),
% 3.12/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_365,plain,
% 3.12/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.12/0.99      | sK3 != sK4 ),
% 3.12/0.99      inference(unflattening,[status(thm)],[c_364]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1429,plain,
% 3.12/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.12/0.99      | v1_relat_1(sK3) ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1430,plain,
% 3.12/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.12/0.99      | v1_relat_1(sK3) = iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_1429]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_0,plain,
% 3.12/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.12/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1528,plain,
% 3.12/0.99      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | X0 = sK3 ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1694,plain,
% 3.12/0.99      ( ~ r1_tarski(sK3,sK3) | sK3 = sK3 ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_1528]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_2,plain,
% 3.12/0.99      ( r1_tarski(X0,X0) ),
% 3.12/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1695,plain,
% 3.12/0.99      ( r1_tarski(sK3,sK3) ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_751,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1455,plain,
% 3.12/0.99      ( sK4 != X0 | sK3 != X0 | sK3 = sK4 ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_751]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1802,plain,
% 3.12/0.99      ( sK4 != sK3 | sK3 = sK4 | sK3 != sK3 ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_1455]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_3080,plain,
% 3.12/0.99      ( sK2 = k1_xboole_0
% 3.12/0.99      | r2_hidden(sK0(sK3,sK4),k1_relat_1(sK3)) = iProver_top ),
% 3.12/0.99      inference(global_propositional_subsumption,
% 3.12/0.99                [status(thm)],
% 3.12/0.99                [c_3067,c_30,c_32,c_24,c_365,c_1430,c_1694,c_1695,c_1802]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_3086,plain,
% 3.12/0.99      ( sK2 = k1_xboole_0 | r2_hidden(sK0(sK3,sK4),sK1) = iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_1817,c_3080]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_7,plain,
% 3.12/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.12/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1243,plain,
% 3.12/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.12/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_9,plain,
% 3.12/0.99      ( ~ r2_hidden(X0,X1)
% 3.12/0.99      | m1_subset_1(X0,X2)
% 3.12/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 3.12/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1241,plain,
% 3.12/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.12/0.99      | m1_subset_1(X0,X2) = iProver_top
% 3.12/0.99      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_2865,plain,
% 3.12/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.12/0.99      | m1_subset_1(X0,X2) = iProver_top
% 3.12/0.99      | r1_tarski(X1,X2) != iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_1243,c_1241]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_3840,plain,
% 3.12/0.99      ( sK2 = k1_xboole_0
% 3.12/0.99      | m1_subset_1(sK0(sK3,sK4),X0) = iProver_top
% 3.12/0.99      | r1_tarski(sK1,X0) != iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_3086,c_2865]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_23,negated_conjecture,
% 3.12/0.99      ( ~ m1_subset_1(X0,sK1) | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) ),
% 3.12/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1236,plain,
% 3.12/0.99      ( k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
% 3.12/0.99      | m1_subset_1(X0,sK1) != iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_3886,plain,
% 3.12/0.99      ( k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4))
% 3.12/0.99      | sK2 = k1_xboole_0
% 3.12/0.99      | r1_tarski(sK1,sK1) != iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_3840,c_1236]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1245,plain,
% 3.12/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_4068,plain,
% 3.12/0.99      ( k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4))
% 3.12/0.99      | sK2 = k1_xboole_0 ),
% 3.12/0.99      inference(forward_subsumption_resolution,
% 3.12/0.99                [status(thm)],
% 3.12/0.99                [c_3886,c_1245]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_10,plain,
% 3.12/0.99      ( ~ v1_relat_1(X0)
% 3.12/0.99      | ~ v1_relat_1(X1)
% 3.12/0.99      | ~ v1_funct_1(X0)
% 3.12/0.99      | ~ v1_funct_1(X1)
% 3.12/0.99      | X0 = X1
% 3.12/0.99      | k1_funct_1(X0,sK0(X1,X0)) != k1_funct_1(X1,sK0(X1,X0))
% 3.12/0.99      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 3.12/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1240,plain,
% 3.12/0.99      ( X0 = X1
% 3.12/0.99      | k1_funct_1(X0,sK0(X1,X0)) != k1_funct_1(X1,sK0(X1,X0))
% 3.12/0.99      | k1_relat_1(X0) != k1_relat_1(X1)
% 3.12/0.99      | v1_relat_1(X0) != iProver_top
% 3.12/0.99      | v1_relat_1(X1) != iProver_top
% 3.12/0.99      | v1_funct_1(X1) != iProver_top
% 3.12/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_4069,plain,
% 3.12/0.99      ( k1_relat_1(sK3) != k1_relat_1(sK4)
% 3.12/0.99      | sK4 = sK3
% 3.12/0.99      | sK2 = k1_xboole_0
% 3.12/0.99      | v1_relat_1(sK4) != iProver_top
% 3.12/0.99      | v1_relat_1(sK3) != iProver_top
% 3.12/0.99      | v1_funct_1(sK4) != iProver_top
% 3.12/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_4068,c_1240]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_4070,plain,
% 3.12/0.99      ( ~ v1_relat_1(sK4)
% 3.12/0.99      | ~ v1_relat_1(sK3)
% 3.12/0.99      | ~ v1_funct_1(sK4)
% 3.12/0.99      | ~ v1_funct_1(sK3)
% 3.12/0.99      | k1_relat_1(sK3) != k1_relat_1(sK4)
% 3.12/0.99      | sK4 = sK3
% 3.12/0.99      | sK2 = k1_xboole_0 ),
% 3.12/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4069]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_4542,plain,
% 3.12/0.99      ( k1_relat_1(sK3) != k1_relat_1(sK4) | sK2 = k1_xboole_0 ),
% 3.12/0.99      inference(global_propositional_subsumption,
% 3.12/0.99                [status(thm)],
% 3.12/0.99                [c_4069,c_29,c_27,c_26,c_24,c_365,c_1426,c_1429,c_1694,
% 3.12/0.99                 c_1695,c_1802,c_4070]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_4546,plain,
% 3.12/0.99      ( k1_relat_1(sK3) != sK1 | sK2 = k1_xboole_0 ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_1749,c_4542]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_4578,plain,
% 3.12/0.99      ( sK2 = k1_xboole_0 ),
% 3.12/0.99      inference(global_propositional_subsumption,
% 3.12/0.99                [status(thm)],
% 3.12/0.99                [c_4546,c_1817]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_4600,plain,
% 3.12/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
% 3.12/0.99      inference(demodulation,[status(thm)],[c_4578,c_1235]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_3,plain,
% 3.12/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.12/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_4606,plain,
% 3.12/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.12/0.99      inference(demodulation,[status(thm)],[c_4600,c_3]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_4601,plain,
% 3.12/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
% 3.12/0.99      inference(demodulation,[status(thm)],[c_4578,c_1233]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_4603,plain,
% 3.12/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.12/0.99      inference(demodulation,[status(thm)],[c_4601,c_3]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_8,plain,
% 3.12/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.12/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_3148,plain,
% 3.12/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0)) | r1_tarski(sK3,X0) ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_3149,plain,
% 3.12/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 3.12/0.99      | r1_tarski(sK3,X0) = iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_3148]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_3151,plain,
% 3.12/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.12/0.99      | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_3149]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_3097,plain,
% 3.12/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0)) | r1_tarski(sK4,X0) ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_3098,plain,
% 3.12/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 3.12/0.99      | r1_tarski(sK4,X0) = iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_3097]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_3100,plain,
% 3.12/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.12/0.99      | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_3098]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_6,plain,
% 3.12/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.12/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_2085,plain,
% 3.12/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_2088,plain,
% 3.12/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) = iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_2085]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_2076,plain,
% 3.12/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_2079,plain,
% 3.12/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) = iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_2076]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1706,plain,
% 3.12/0.99      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | sK3 = X0 ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1707,plain,
% 3.12/0.99      ( sK3 = X0
% 3.12/0.99      | r1_tarski(X0,sK3) != iProver_top
% 3.12/0.99      | r1_tarski(sK3,X0) != iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_1706]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1709,plain,
% 3.12/0.99      ( sK3 = k1_xboole_0
% 3.12/0.99      | r1_tarski(sK3,k1_xboole_0) != iProver_top
% 3.12/0.99      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_1707]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1689,plain,
% 3.12/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3)) | r1_tarski(X0,sK3) ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1690,plain,
% 3.12/0.99      ( m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top
% 3.12/0.99      | r1_tarski(X0,sK3) = iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_1689]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1692,plain,
% 3.12/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top
% 3.12/0.99      | r1_tarski(k1_xboole_0,sK3) = iProver_top ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_1690]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1670,plain,
% 3.12/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4)) | r1_tarski(X0,sK4) ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1671,plain,
% 3.12/0.99      ( m1_subset_1(X0,k1_zfmisc_1(sK4)) != iProver_top
% 3.12/0.99      | r1_tarski(X0,sK4) = iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_1670]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1673,plain,
% 3.12/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) != iProver_top
% 3.12/0.99      | r1_tarski(k1_xboole_0,sK4) = iProver_top ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_1671]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1607,plain,
% 3.12/0.99      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | sK4 = X0 ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1608,plain,
% 3.12/0.99      ( sK4 = X0
% 3.12/0.99      | r1_tarski(X0,sK4) != iProver_top
% 3.12/0.99      | r1_tarski(sK4,X0) != iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_1607]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1610,plain,
% 3.12/0.99      ( sK4 = k1_xboole_0
% 3.12/0.99      | r1_tarski(sK4,k1_xboole_0) != iProver_top
% 3.12/0.99      | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_1608]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1456,plain,
% 3.12/0.99      ( sK4 != k1_xboole_0 | sK3 = sK4 | sK3 != k1_xboole_0 ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_1455]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(contradiction,plain,
% 3.12/0.99      ( $false ),
% 3.12/0.99      inference(minisat,
% 3.12/0.99                [status(thm)],
% 3.12/0.99                [c_4606,c_4603,c_3151,c_3100,c_2088,c_2079,c_1709,c_1692,
% 3.12/0.99                 c_1673,c_1610,c_1456,c_365,c_24]) ).
% 3.12/0.99  
% 3.12/0.99  
% 3.12/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.12/0.99  
% 3.12/0.99  ------                               Statistics
% 3.12/0.99  
% 3.12/0.99  ------ General
% 3.12/0.99  
% 3.12/0.99  abstr_ref_over_cycles:                  0
% 3.12/0.99  abstr_ref_under_cycles:                 0
% 3.12/0.99  gc_basic_clause_elim:                   0
% 3.12/0.99  forced_gc_time:                         0
% 3.12/0.99  parsing_time:                           0.021
% 3.12/0.99  unif_index_cands_time:                  0.
% 3.12/0.99  unif_index_add_time:                    0.
% 3.12/0.99  orderings_time:                         0.
% 3.12/0.99  out_proof_time:                         0.021
% 3.12/0.99  total_time:                             0.191
% 3.12/0.99  num_of_symbols:                         49
% 3.12/0.99  num_of_terms:                           3904
% 3.12/0.99  
% 3.12/0.99  ------ Preprocessing
% 3.12/0.99  
% 3.12/0.99  num_of_splits:                          0
% 3.12/0.99  num_of_split_atoms:                     0
% 3.12/0.99  num_of_reused_defs:                     0
% 3.12/0.99  num_eq_ax_congr_red:                    20
% 3.12/0.99  num_of_sem_filtered_clauses:            1
% 3.12/0.99  num_of_subtypes:                        0
% 3.12/0.99  monotx_restored_types:                  0
% 3.12/0.99  sat_num_of_epr_types:                   0
% 3.12/0.99  sat_num_of_non_cyclic_types:            0
% 3.12/0.99  sat_guarded_non_collapsed_types:        0
% 3.12/0.99  num_pure_diseq_elim:                    0
% 3.12/0.99  simp_replaced_by:                       0
% 3.12/0.99  res_preprocessed:                       123
% 3.12/0.99  prep_upred:                             0
% 3.12/0.99  prep_unflattend:                        45
% 3.12/0.99  smt_new_axioms:                         0
% 3.12/0.99  pred_elim_cands:                        5
% 3.12/0.99  pred_elim:                              2
% 3.12/0.99  pred_elim_cl:                           4
% 3.12/0.99  pred_elim_cycles:                       5
% 3.12/0.99  merged_defs:                            8
% 3.12/0.99  merged_defs_ncl:                        0
% 3.12/0.99  bin_hyper_res:                          8
% 3.12/0.99  prep_cycles:                            4
% 3.12/0.99  pred_elim_time:                         0.005
% 3.12/0.99  splitting_time:                         0.
% 3.12/0.99  sem_filter_time:                        0.
% 3.12/0.99  monotx_time:                            0.
% 3.12/0.99  subtype_inf_time:                       0.
% 3.12/0.99  
% 3.12/0.99  ------ Problem properties
% 3.12/0.99  
% 3.12/0.99  clauses:                                25
% 3.12/0.99  conjectures:                            5
% 3.12/0.99  epr:                                    5
% 3.12/0.99  horn:                                   19
% 3.12/0.99  ground:                                 11
% 3.12/0.99  unary:                                  9
% 3.12/0.99  binary:                                 7
% 3.12/0.99  lits:                                   60
% 3.12/0.99  lits_eq:                                28
% 3.12/0.99  fd_pure:                                0
% 3.12/0.99  fd_pseudo:                              0
% 3.12/0.99  fd_cond:                                1
% 3.12/0.99  fd_pseudo_cond:                         3
% 3.12/0.99  ac_symbols:                             0
% 3.12/0.99  
% 3.12/0.99  ------ Propositional Solver
% 3.12/0.99  
% 3.12/0.99  prop_solver_calls:                      29
% 3.12/0.99  prop_fast_solver_calls:                 870
% 3.12/0.99  smt_solver_calls:                       0
% 3.12/0.99  smt_fast_solver_calls:                  0
% 3.12/0.99  prop_num_of_clauses:                    1519
% 3.12/0.99  prop_preprocess_simplified:             4658
% 3.12/0.99  prop_fo_subsumed:                       23
% 3.12/0.99  prop_solver_time:                       0.
% 3.12/0.99  smt_solver_time:                        0.
% 3.12/0.99  smt_fast_solver_time:                   0.
% 3.12/0.99  prop_fast_solver_time:                  0.
% 3.12/0.99  prop_unsat_core_time:                   0.
% 3.12/0.99  
% 3.12/0.99  ------ QBF
% 3.12/0.99  
% 3.12/0.99  qbf_q_res:                              0
% 3.12/0.99  qbf_num_tautologies:                    0
% 3.12/0.99  qbf_prep_cycles:                        0
% 3.12/0.99  
% 3.12/0.99  ------ BMC1
% 3.12/0.99  
% 3.12/0.99  bmc1_current_bound:                     -1
% 3.12/0.99  bmc1_last_solved_bound:                 -1
% 3.12/0.99  bmc1_unsat_core_size:                   -1
% 3.12/0.99  bmc1_unsat_core_parents_size:           -1
% 3.12/0.99  bmc1_merge_next_fun:                    0
% 3.12/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.12/0.99  
% 3.12/0.99  ------ Instantiation
% 3.12/0.99  
% 3.12/0.99  inst_num_of_clauses:                    512
% 3.12/0.99  inst_num_in_passive:                    145
% 3.12/0.99  inst_num_in_active:                     322
% 3.12/0.99  inst_num_in_unprocessed:                45
% 3.12/0.99  inst_num_of_loops:                      350
% 3.12/0.99  inst_num_of_learning_restarts:          0
% 3.12/0.99  inst_num_moves_active_passive:          24
% 3.12/0.99  inst_lit_activity:                      0
% 3.12/0.99  inst_lit_activity_moves:                0
% 3.12/0.99  inst_num_tautologies:                   0
% 3.12/0.99  inst_num_prop_implied:                  0
% 3.12/0.99  inst_num_existing_simplified:           0
% 3.12/0.99  inst_num_eq_res_simplified:             0
% 3.12/0.99  inst_num_child_elim:                    0
% 3.12/0.99  inst_num_of_dismatching_blockings:      156
% 3.12/0.99  inst_num_of_non_proper_insts:           652
% 3.12/0.99  inst_num_of_duplicates:                 0
% 3.12/0.99  inst_inst_num_from_inst_to_res:         0
% 3.12/0.99  inst_dismatching_checking_time:         0.
% 3.12/0.99  
% 3.12/0.99  ------ Resolution
% 3.12/0.99  
% 3.12/0.99  res_num_of_clauses:                     0
% 3.12/0.99  res_num_in_passive:                     0
% 3.12/0.99  res_num_in_active:                      0
% 3.12/0.99  res_num_of_loops:                       127
% 3.12/0.99  res_forward_subset_subsumed:            43
% 3.12/0.99  res_backward_subset_subsumed:           0
% 3.12/0.99  res_forward_subsumed:                   0
% 3.12/0.99  res_backward_subsumed:                  0
% 3.12/0.99  res_forward_subsumption_resolution:     0
% 3.12/0.99  res_backward_subsumption_resolution:    0
% 3.12/0.99  res_clause_to_clause_subsumption:       238
% 3.12/0.99  res_orphan_elimination:                 0
% 3.12/0.99  res_tautology_del:                      54
% 3.12/0.99  res_num_eq_res_simplified:              0
% 3.12/0.99  res_num_sel_changes:                    0
% 3.12/0.99  res_moves_from_active_to_pass:          0
% 3.12/0.99  
% 3.12/0.99  ------ Superposition
% 3.12/0.99  
% 3.12/0.99  sup_time_total:                         0.
% 3.12/0.99  sup_time_generating:                    0.
% 3.12/0.99  sup_time_sim_full:                      0.
% 3.12/0.99  sup_time_sim_immed:                     0.
% 3.12/0.99  
% 3.12/0.99  sup_num_of_clauses:                     59
% 3.12/0.99  sup_num_in_active:                      39
% 3.12/0.99  sup_num_in_passive:                     20
% 3.12/0.99  sup_num_of_loops:                       68
% 3.12/0.99  sup_fw_superposition:                   69
% 3.12/0.99  sup_bw_superposition:                   44
% 3.12/0.99  sup_immediate_simplified:               18
% 3.12/0.99  sup_given_eliminated:                   0
% 3.12/0.99  comparisons_done:                       0
% 3.12/0.99  comparisons_avoided:                    12
% 3.12/0.99  
% 3.12/0.99  ------ Simplifications
% 3.12/0.99  
% 3.12/0.99  
% 3.12/0.99  sim_fw_subset_subsumed:                 4
% 3.12/0.99  sim_bw_subset_subsumed:                 24
% 3.12/0.99  sim_fw_subsumed:                        2
% 3.12/0.99  sim_bw_subsumed:                        0
% 3.12/0.99  sim_fw_subsumption_res:                 6
% 3.12/0.99  sim_bw_subsumption_res:                 0
% 3.12/0.99  sim_tautology_del:                      1
% 3.12/0.99  sim_eq_tautology_del:                   16
% 3.12/0.99  sim_eq_res_simp:                        2
% 3.12/0.99  sim_fw_demodulated:                     12
% 3.12/0.99  sim_bw_demodulated:                     21
% 3.12/0.99  sim_light_normalised:                   2
% 3.12/0.99  sim_joinable_taut:                      0
% 3.12/0.99  sim_joinable_simp:                      0
% 3.12/0.99  sim_ac_normalised:                      0
% 3.12/0.99  sim_smt_subsumption:                    0
% 3.12/0.99  
%------------------------------------------------------------------------------
