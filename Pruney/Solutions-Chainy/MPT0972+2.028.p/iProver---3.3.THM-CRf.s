%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:13 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :  146 (1515 expanded)
%              Number of clauses        :   91 ( 453 expanded)
%              Number of leaves         :   14 ( 366 expanded)
%              Depth                    :   25
%              Number of atoms          :  491 (9654 expanded)
%              Number of equality atoms :  255 (2338 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
                ( r2_hidden(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
                  ( r2_hidden(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
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
              | ~ r2_hidden(X4,X0) )
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
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ~ r2_relset_1(X0,X1,X2,sK4)
        & ! [X4] :
            ( k1_funct_1(sK4,X4) = k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0) )
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
                | ~ r2_hidden(X4,X0) )
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
              | ~ r2_hidden(X4,sK1) )
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
        | ~ r2_hidden(X4,sK1) )
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f65,plain,(
    ! [X4] :
      ( k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4)
      | ~ r2_hidden(X4,sK1) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

cnf(c_523,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_25])).

cnf(c_524,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_523])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_526,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_524,c_24])).

cnf(c_1309,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1311,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1659,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1309,c_1311])).

cnf(c_1823,plain,
    ( k1_relat_1(sK4) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_526,c_1659])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_534,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_28])).

cnf(c_535,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_534])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_537,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_535,c_27])).

cnf(c_1307,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1660,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1307,c_1311])).

cnf(c_1891,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_537,c_1660])).

cnf(c_11,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | X1 = X0
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1313,plain,
    ( X0 = X1
    | k1_relat_1(X0) != k1_relat_1(X1)
    | r2_hidden(sK0(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2682,plain,
    ( k1_relat_1(X0) != sK1
    | sK4 = X0
    | sK2 = k1_xboole_0
    | r2_hidden(sK0(X0,sK4),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1823,c_1313])).

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

cnf(c_1500,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1501,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1500])).

cnf(c_3128,plain,
    ( v1_funct_1(X0) != iProver_top
    | k1_relat_1(X0) != sK1
    | sK4 = X0
    | sK2 = k1_xboole_0
    | r2_hidden(sK0(X0,sK4),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2682,c_33,c_35,c_1501])).

cnf(c_3129,plain,
    ( k1_relat_1(X0) != sK1
    | sK4 = X0
    | sK2 = k1_xboole_0
    | r2_hidden(sK0(X0,sK4),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3128])).

cnf(c_3141,plain,
    ( sK4 = sK3
    | sK2 = k1_xboole_0
    | r2_hidden(sK0(sK3,sK4),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1891,c_3129])).

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

cnf(c_1503,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1504,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1503])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1602,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | X0 = sK3 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1768,plain,
    ( ~ r1_tarski(sK3,sK3)
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1602])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1769,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_825,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1529,plain,
    ( sK4 != X0
    | sK3 != X0
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_825])).

cnf(c_1876,plain,
    ( sK4 != sK3
    | sK3 = sK4
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1529])).

cnf(c_3154,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK0(sK3,sK4),k1_relat_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3141,c_30,c_32,c_24,c_365,c_1504,c_1768,c_1769,c_1876])).

cnf(c_3160,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK0(sK3,sK4),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1891,c_3154])).

cnf(c_23,negated_conjecture,
    ( ~ r2_hidden(X0,sK1)
    | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1310,plain,
    ( k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
    | r2_hidden(X0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3181,plain,
    ( k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4))
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3160,c_1310])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X0 = X1
    | k1_funct_1(X0,sK0(X1,X0)) != k1_funct_1(X1,sK0(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1314,plain,
    ( X0 = X1
    | k1_funct_1(X0,sK0(X1,X0)) != k1_funct_1(X1,sK0(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3249,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK4)
    | sK4 = sK3
    | sK2 = k1_xboole_0
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3181,c_1314])).

cnf(c_3265,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | k1_relat_1(sK3) != k1_relat_1(sK4)
    | sK4 = sK3
    | sK2 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3249])).

cnf(c_3469,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK4)
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3249,c_29,c_27,c_26,c_24,c_365,c_1500,c_1503,c_1768,c_1769,c_1876,c_3265])).

cnf(c_3473,plain,
    ( k1_relat_1(sK3) != sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1823,c_3469])).

cnf(c_3474,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3473,c_1891])).

cnf(c_3493,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3474,c_1309])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3499,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3493,c_3])).

cnf(c_3494,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3474,c_1307])).

cnf(c_3496,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3494,c_3])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_3199,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | r1_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3200,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3199])).

cnf(c_3202,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3200])).

cnf(c_3171,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
    | r1_tarski(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3172,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3171])).

cnf(c_3174,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3172])).

cnf(c_6,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2159,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2162,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2159])).

cnf(c_2150,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2153,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2150])).

cnf(c_1780,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1781,plain,
    ( sK3 = X0
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1780])).

cnf(c_1783,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1781])).

cnf(c_1763,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | r1_tarski(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1764,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(X0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1763])).

cnf(c_1766,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1764])).

cnf(c_1744,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4))
    | r1_tarski(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1745,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK4)) != iProver_top
    | r1_tarski(X0,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1744])).

cnf(c_1747,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) != iProver_top
    | r1_tarski(k1_xboole_0,sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1745])).

cnf(c_1681,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1682,plain,
    ( sK4 = X0
    | r1_tarski(X0,sK4) != iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1681])).

cnf(c_1684,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(sK4,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1682])).

cnf(c_1530,plain,
    ( sK4 != k1_xboole_0
    | sK3 = sK4
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1529])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3499,c_3496,c_3202,c_3174,c_2162,c_2153,c_1783,c_1766,c_1747,c_1684,c_1530,c_365,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:52:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.82/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.00  
% 2.82/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.82/1.00  
% 2.82/1.00  ------  iProver source info
% 2.82/1.00  
% 2.82/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.82/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.82/1.00  git: non_committed_changes: false
% 2.82/1.00  git: last_make_outside_of_git: false
% 2.82/1.00  
% 2.82/1.00  ------ 
% 2.82/1.00  
% 2.82/1.00  ------ Input Options
% 2.82/1.00  
% 2.82/1.00  --out_options                           all
% 2.82/1.00  --tptp_safe_out                         true
% 2.82/1.00  --problem_path                          ""
% 2.82/1.00  --include_path                          ""
% 2.82/1.00  --clausifier                            res/vclausify_rel
% 2.82/1.00  --clausifier_options                    --mode clausify
% 2.82/1.00  --stdin                                 false
% 2.82/1.00  --stats_out                             all
% 2.82/1.00  
% 2.82/1.00  ------ General Options
% 2.82/1.00  
% 2.82/1.00  --fof                                   false
% 2.82/1.00  --time_out_real                         305.
% 2.82/1.00  --time_out_virtual                      -1.
% 2.82/1.00  --symbol_type_check                     false
% 2.82/1.00  --clausify_out                          false
% 2.82/1.00  --sig_cnt_out                           false
% 2.82/1.00  --trig_cnt_out                          false
% 2.82/1.00  --trig_cnt_out_tolerance                1.
% 2.82/1.00  --trig_cnt_out_sk_spl                   false
% 2.82/1.00  --abstr_cl_out                          false
% 2.82/1.00  
% 2.82/1.00  ------ Global Options
% 2.82/1.00  
% 2.82/1.00  --schedule                              default
% 2.82/1.00  --add_important_lit                     false
% 2.82/1.00  --prop_solver_per_cl                    1000
% 2.82/1.00  --min_unsat_core                        false
% 2.82/1.00  --soft_assumptions                      false
% 2.82/1.00  --soft_lemma_size                       3
% 2.82/1.00  --prop_impl_unit_size                   0
% 2.82/1.00  --prop_impl_unit                        []
% 2.82/1.00  --share_sel_clauses                     true
% 2.82/1.00  --reset_solvers                         false
% 2.82/1.00  --bc_imp_inh                            [conj_cone]
% 2.82/1.00  --conj_cone_tolerance                   3.
% 2.82/1.00  --extra_neg_conj                        none
% 2.82/1.00  --large_theory_mode                     true
% 2.82/1.00  --prolific_symb_bound                   200
% 2.82/1.00  --lt_threshold                          2000
% 2.82/1.00  --clause_weak_htbl                      true
% 2.82/1.00  --gc_record_bc_elim                     false
% 2.82/1.00  
% 2.82/1.00  ------ Preprocessing Options
% 2.82/1.00  
% 2.82/1.00  --preprocessing_flag                    true
% 2.82/1.00  --time_out_prep_mult                    0.1
% 2.82/1.00  --splitting_mode                        input
% 2.82/1.00  --splitting_grd                         true
% 2.82/1.00  --splitting_cvd                         false
% 2.82/1.00  --splitting_cvd_svl                     false
% 2.82/1.00  --splitting_nvd                         32
% 2.82/1.00  --sub_typing                            true
% 2.82/1.00  --prep_gs_sim                           true
% 2.82/1.00  --prep_unflatten                        true
% 2.82/1.00  --prep_res_sim                          true
% 2.82/1.00  --prep_upred                            true
% 2.82/1.00  --prep_sem_filter                       exhaustive
% 2.82/1.00  --prep_sem_filter_out                   false
% 2.82/1.00  --pred_elim                             true
% 2.82/1.00  --res_sim_input                         true
% 2.82/1.00  --eq_ax_congr_red                       true
% 2.82/1.00  --pure_diseq_elim                       true
% 2.82/1.00  --brand_transform                       false
% 2.82/1.00  --non_eq_to_eq                          false
% 2.82/1.00  --prep_def_merge                        true
% 2.82/1.00  --prep_def_merge_prop_impl              false
% 2.82/1.00  --prep_def_merge_mbd                    true
% 2.82/1.00  --prep_def_merge_tr_red                 false
% 2.82/1.00  --prep_def_merge_tr_cl                  false
% 2.82/1.00  --smt_preprocessing                     true
% 2.82/1.00  --smt_ac_axioms                         fast
% 2.82/1.00  --preprocessed_out                      false
% 2.82/1.00  --preprocessed_stats                    false
% 2.82/1.00  
% 2.82/1.00  ------ Abstraction refinement Options
% 2.82/1.00  
% 2.82/1.00  --abstr_ref                             []
% 2.82/1.00  --abstr_ref_prep                        false
% 2.82/1.00  --abstr_ref_until_sat                   false
% 2.82/1.00  --abstr_ref_sig_restrict                funpre
% 2.82/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.82/1.00  --abstr_ref_under                       []
% 2.82/1.00  
% 2.82/1.00  ------ SAT Options
% 2.82/1.00  
% 2.82/1.00  --sat_mode                              false
% 2.82/1.00  --sat_fm_restart_options                ""
% 2.82/1.00  --sat_gr_def                            false
% 2.82/1.00  --sat_epr_types                         true
% 2.82/1.00  --sat_non_cyclic_types                  false
% 2.82/1.00  --sat_finite_models                     false
% 2.82/1.00  --sat_fm_lemmas                         false
% 2.82/1.00  --sat_fm_prep                           false
% 2.82/1.00  --sat_fm_uc_incr                        true
% 2.82/1.00  --sat_out_model                         small
% 2.82/1.00  --sat_out_clauses                       false
% 2.82/1.00  
% 2.82/1.00  ------ QBF Options
% 2.82/1.00  
% 2.82/1.00  --qbf_mode                              false
% 2.82/1.00  --qbf_elim_univ                         false
% 2.82/1.00  --qbf_dom_inst                          none
% 2.82/1.00  --qbf_dom_pre_inst                      false
% 2.82/1.00  --qbf_sk_in                             false
% 2.82/1.00  --qbf_pred_elim                         true
% 2.82/1.00  --qbf_split                             512
% 2.82/1.00  
% 2.82/1.00  ------ BMC1 Options
% 2.82/1.00  
% 2.82/1.00  --bmc1_incremental                      false
% 2.82/1.00  --bmc1_axioms                           reachable_all
% 2.82/1.00  --bmc1_min_bound                        0
% 2.82/1.00  --bmc1_max_bound                        -1
% 2.82/1.00  --bmc1_max_bound_default                -1
% 2.82/1.00  --bmc1_symbol_reachability              true
% 2.82/1.00  --bmc1_property_lemmas                  false
% 2.82/1.00  --bmc1_k_induction                      false
% 2.82/1.00  --bmc1_non_equiv_states                 false
% 2.82/1.00  --bmc1_deadlock                         false
% 2.82/1.00  --bmc1_ucm                              false
% 2.82/1.00  --bmc1_add_unsat_core                   none
% 2.82/1.00  --bmc1_unsat_core_children              false
% 2.82/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.82/1.00  --bmc1_out_stat                         full
% 2.82/1.00  --bmc1_ground_init                      false
% 2.82/1.00  --bmc1_pre_inst_next_state              false
% 2.82/1.00  --bmc1_pre_inst_state                   false
% 2.82/1.00  --bmc1_pre_inst_reach_state             false
% 2.82/1.00  --bmc1_out_unsat_core                   false
% 2.82/1.00  --bmc1_aig_witness_out                  false
% 2.82/1.00  --bmc1_verbose                          false
% 2.82/1.00  --bmc1_dump_clauses_tptp                false
% 2.82/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.82/1.00  --bmc1_dump_file                        -
% 2.82/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.82/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.82/1.00  --bmc1_ucm_extend_mode                  1
% 2.82/1.00  --bmc1_ucm_init_mode                    2
% 2.82/1.00  --bmc1_ucm_cone_mode                    none
% 2.82/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.82/1.00  --bmc1_ucm_relax_model                  4
% 2.82/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.82/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.82/1.00  --bmc1_ucm_layered_model                none
% 2.82/1.00  --bmc1_ucm_max_lemma_size               10
% 2.82/1.00  
% 2.82/1.00  ------ AIG Options
% 2.82/1.00  
% 2.82/1.00  --aig_mode                              false
% 2.82/1.00  
% 2.82/1.00  ------ Instantiation Options
% 2.82/1.00  
% 2.82/1.00  --instantiation_flag                    true
% 2.82/1.00  --inst_sos_flag                         false
% 2.82/1.00  --inst_sos_phase                        true
% 2.82/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.82/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.82/1.00  --inst_lit_sel_side                     num_symb
% 2.82/1.00  --inst_solver_per_active                1400
% 2.82/1.00  --inst_solver_calls_frac                1.
% 2.82/1.00  --inst_passive_queue_type               priority_queues
% 2.82/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.82/1.00  --inst_passive_queues_freq              [25;2]
% 2.82/1.00  --inst_dismatching                      true
% 2.82/1.00  --inst_eager_unprocessed_to_passive     true
% 2.82/1.00  --inst_prop_sim_given                   true
% 2.82/1.00  --inst_prop_sim_new                     false
% 2.82/1.00  --inst_subs_new                         false
% 2.82/1.00  --inst_eq_res_simp                      false
% 2.82/1.00  --inst_subs_given                       false
% 2.82/1.00  --inst_orphan_elimination               true
% 2.82/1.00  --inst_learning_loop_flag               true
% 2.82/1.00  --inst_learning_start                   3000
% 2.82/1.00  --inst_learning_factor                  2
% 2.82/1.00  --inst_start_prop_sim_after_learn       3
% 2.82/1.00  --inst_sel_renew                        solver
% 2.82/1.00  --inst_lit_activity_flag                true
% 2.82/1.00  --inst_restr_to_given                   false
% 2.82/1.00  --inst_activity_threshold               500
% 2.82/1.00  --inst_out_proof                        true
% 2.82/1.00  
% 2.82/1.00  ------ Resolution Options
% 2.82/1.00  
% 2.82/1.00  --resolution_flag                       true
% 2.82/1.00  --res_lit_sel                           adaptive
% 2.82/1.00  --res_lit_sel_side                      none
% 2.82/1.00  --res_ordering                          kbo
% 2.82/1.00  --res_to_prop_solver                    active
% 2.82/1.00  --res_prop_simpl_new                    false
% 2.82/1.00  --res_prop_simpl_given                  true
% 2.82/1.00  --res_passive_queue_type                priority_queues
% 2.82/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.82/1.00  --res_passive_queues_freq               [15;5]
% 2.82/1.00  --res_forward_subs                      full
% 2.82/1.00  --res_backward_subs                     full
% 2.82/1.00  --res_forward_subs_resolution           true
% 2.82/1.00  --res_backward_subs_resolution          true
% 2.82/1.00  --res_orphan_elimination                true
% 2.82/1.00  --res_time_limit                        2.
% 2.82/1.00  --res_out_proof                         true
% 2.82/1.00  
% 2.82/1.00  ------ Superposition Options
% 2.82/1.00  
% 2.82/1.00  --superposition_flag                    true
% 2.82/1.00  --sup_passive_queue_type                priority_queues
% 2.82/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.82/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.82/1.00  --demod_completeness_check              fast
% 2.82/1.00  --demod_use_ground                      true
% 2.82/1.00  --sup_to_prop_solver                    passive
% 2.82/1.00  --sup_prop_simpl_new                    true
% 2.82/1.00  --sup_prop_simpl_given                  true
% 2.82/1.00  --sup_fun_splitting                     false
% 2.82/1.00  --sup_smt_interval                      50000
% 2.82/1.00  
% 2.82/1.00  ------ Superposition Simplification Setup
% 2.82/1.00  
% 2.82/1.00  --sup_indices_passive                   []
% 2.82/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.82/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/1.00  --sup_full_bw                           [BwDemod]
% 2.82/1.00  --sup_immed_triv                        [TrivRules]
% 2.82/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.82/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/1.00  --sup_immed_bw_main                     []
% 2.82/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.82/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.82/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.82/1.00  
% 2.82/1.00  ------ Combination Options
% 2.82/1.00  
% 2.82/1.00  --comb_res_mult                         3
% 2.82/1.00  --comb_sup_mult                         2
% 2.82/1.00  --comb_inst_mult                        10
% 2.82/1.00  
% 2.82/1.00  ------ Debug Options
% 2.82/1.00  
% 2.82/1.00  --dbg_backtrace                         false
% 2.82/1.00  --dbg_dump_prop_clauses                 false
% 2.82/1.00  --dbg_dump_prop_clauses_file            -
% 2.82/1.00  --dbg_out_stat                          false
% 2.82/1.00  ------ Parsing...
% 2.82/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.82/1.00  
% 2.82/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.82/1.00  
% 2.82/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.82/1.00  
% 2.82/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.82/1.00  ------ Proving...
% 2.82/1.00  ------ Problem Properties 
% 2.82/1.00  
% 2.82/1.00  
% 2.82/1.00  clauses                                 25
% 2.82/1.00  conjectures                             5
% 2.82/1.00  EPR                                     5
% 2.82/1.00  Horn                                    19
% 2.82/1.00  unary                                   9
% 2.82/1.00  binary                                  7
% 2.82/1.00  lits                                    60
% 2.82/1.00  lits eq                                 28
% 2.82/1.00  fd_pure                                 0
% 2.82/1.00  fd_pseudo                               0
% 2.82/1.00  fd_cond                                 1
% 2.82/1.00  fd_pseudo_cond                          3
% 2.82/1.00  AC symbols                              0
% 2.82/1.00  
% 2.82/1.00  ------ Schedule dynamic 5 is on 
% 2.82/1.00  
% 2.82/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.82/1.00  
% 2.82/1.00  
% 2.82/1.00  ------ 
% 2.82/1.00  Current options:
% 2.82/1.00  ------ 
% 2.82/1.00  
% 2.82/1.00  ------ Input Options
% 2.82/1.00  
% 2.82/1.00  --out_options                           all
% 2.82/1.00  --tptp_safe_out                         true
% 2.82/1.00  --problem_path                          ""
% 2.82/1.00  --include_path                          ""
% 2.82/1.00  --clausifier                            res/vclausify_rel
% 2.82/1.00  --clausifier_options                    --mode clausify
% 2.82/1.00  --stdin                                 false
% 2.82/1.00  --stats_out                             all
% 2.82/1.00  
% 2.82/1.00  ------ General Options
% 2.82/1.00  
% 2.82/1.00  --fof                                   false
% 2.82/1.00  --time_out_real                         305.
% 2.82/1.00  --time_out_virtual                      -1.
% 2.82/1.00  --symbol_type_check                     false
% 2.82/1.00  --clausify_out                          false
% 2.82/1.00  --sig_cnt_out                           false
% 2.82/1.00  --trig_cnt_out                          false
% 2.82/1.00  --trig_cnt_out_tolerance                1.
% 2.82/1.00  --trig_cnt_out_sk_spl                   false
% 2.82/1.00  --abstr_cl_out                          false
% 2.82/1.00  
% 2.82/1.00  ------ Global Options
% 2.82/1.00  
% 2.82/1.00  --schedule                              default
% 2.82/1.00  --add_important_lit                     false
% 2.82/1.00  --prop_solver_per_cl                    1000
% 2.82/1.00  --min_unsat_core                        false
% 2.82/1.00  --soft_assumptions                      false
% 2.82/1.00  --soft_lemma_size                       3
% 2.82/1.00  --prop_impl_unit_size                   0
% 2.82/1.00  --prop_impl_unit                        []
% 2.82/1.00  --share_sel_clauses                     true
% 2.82/1.00  --reset_solvers                         false
% 2.82/1.00  --bc_imp_inh                            [conj_cone]
% 2.82/1.00  --conj_cone_tolerance                   3.
% 2.82/1.00  --extra_neg_conj                        none
% 2.82/1.00  --large_theory_mode                     true
% 2.82/1.00  --prolific_symb_bound                   200
% 2.82/1.00  --lt_threshold                          2000
% 2.82/1.00  --clause_weak_htbl                      true
% 2.82/1.00  --gc_record_bc_elim                     false
% 2.82/1.00  
% 2.82/1.00  ------ Preprocessing Options
% 2.82/1.00  
% 2.82/1.00  --preprocessing_flag                    true
% 2.82/1.00  --time_out_prep_mult                    0.1
% 2.82/1.00  --splitting_mode                        input
% 2.82/1.00  --splitting_grd                         true
% 2.82/1.00  --splitting_cvd                         false
% 2.82/1.00  --splitting_cvd_svl                     false
% 2.82/1.00  --splitting_nvd                         32
% 2.82/1.00  --sub_typing                            true
% 2.82/1.00  --prep_gs_sim                           true
% 2.82/1.00  --prep_unflatten                        true
% 2.82/1.00  --prep_res_sim                          true
% 2.82/1.00  --prep_upred                            true
% 2.82/1.00  --prep_sem_filter                       exhaustive
% 2.82/1.00  --prep_sem_filter_out                   false
% 2.82/1.00  --pred_elim                             true
% 2.82/1.00  --res_sim_input                         true
% 2.82/1.00  --eq_ax_congr_red                       true
% 2.82/1.00  --pure_diseq_elim                       true
% 2.82/1.00  --brand_transform                       false
% 2.82/1.00  --non_eq_to_eq                          false
% 2.82/1.00  --prep_def_merge                        true
% 2.82/1.00  --prep_def_merge_prop_impl              false
% 2.82/1.00  --prep_def_merge_mbd                    true
% 2.82/1.00  --prep_def_merge_tr_red                 false
% 2.82/1.00  --prep_def_merge_tr_cl                  false
% 2.82/1.00  --smt_preprocessing                     true
% 2.82/1.00  --smt_ac_axioms                         fast
% 2.82/1.00  --preprocessed_out                      false
% 2.82/1.00  --preprocessed_stats                    false
% 2.82/1.00  
% 2.82/1.00  ------ Abstraction refinement Options
% 2.82/1.00  
% 2.82/1.00  --abstr_ref                             []
% 2.82/1.00  --abstr_ref_prep                        false
% 2.82/1.00  --abstr_ref_until_sat                   false
% 2.82/1.00  --abstr_ref_sig_restrict                funpre
% 2.82/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.82/1.00  --abstr_ref_under                       []
% 2.82/1.00  
% 2.82/1.00  ------ SAT Options
% 2.82/1.00  
% 2.82/1.00  --sat_mode                              false
% 2.82/1.00  --sat_fm_restart_options                ""
% 2.82/1.00  --sat_gr_def                            false
% 2.82/1.00  --sat_epr_types                         true
% 2.82/1.00  --sat_non_cyclic_types                  false
% 2.82/1.00  --sat_finite_models                     false
% 2.82/1.00  --sat_fm_lemmas                         false
% 2.82/1.00  --sat_fm_prep                           false
% 2.82/1.00  --sat_fm_uc_incr                        true
% 2.82/1.00  --sat_out_model                         small
% 2.82/1.00  --sat_out_clauses                       false
% 2.82/1.00  
% 2.82/1.00  ------ QBF Options
% 2.82/1.00  
% 2.82/1.00  --qbf_mode                              false
% 2.82/1.00  --qbf_elim_univ                         false
% 2.82/1.00  --qbf_dom_inst                          none
% 2.82/1.00  --qbf_dom_pre_inst                      false
% 2.82/1.00  --qbf_sk_in                             false
% 2.82/1.00  --qbf_pred_elim                         true
% 2.82/1.00  --qbf_split                             512
% 2.82/1.00  
% 2.82/1.00  ------ BMC1 Options
% 2.82/1.00  
% 2.82/1.00  --bmc1_incremental                      false
% 2.82/1.00  --bmc1_axioms                           reachable_all
% 2.82/1.00  --bmc1_min_bound                        0
% 2.82/1.00  --bmc1_max_bound                        -1
% 2.82/1.00  --bmc1_max_bound_default                -1
% 2.82/1.00  --bmc1_symbol_reachability              true
% 2.82/1.00  --bmc1_property_lemmas                  false
% 2.82/1.00  --bmc1_k_induction                      false
% 2.82/1.00  --bmc1_non_equiv_states                 false
% 2.82/1.00  --bmc1_deadlock                         false
% 2.82/1.00  --bmc1_ucm                              false
% 2.82/1.00  --bmc1_add_unsat_core                   none
% 2.82/1.00  --bmc1_unsat_core_children              false
% 2.82/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.82/1.00  --bmc1_out_stat                         full
% 2.82/1.00  --bmc1_ground_init                      false
% 2.82/1.00  --bmc1_pre_inst_next_state              false
% 2.82/1.00  --bmc1_pre_inst_state                   false
% 2.82/1.00  --bmc1_pre_inst_reach_state             false
% 2.82/1.00  --bmc1_out_unsat_core                   false
% 2.82/1.00  --bmc1_aig_witness_out                  false
% 2.82/1.00  --bmc1_verbose                          false
% 2.82/1.00  --bmc1_dump_clauses_tptp                false
% 2.82/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.82/1.00  --bmc1_dump_file                        -
% 2.82/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.82/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.82/1.00  --bmc1_ucm_extend_mode                  1
% 2.82/1.00  --bmc1_ucm_init_mode                    2
% 2.82/1.00  --bmc1_ucm_cone_mode                    none
% 2.82/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.82/1.00  --bmc1_ucm_relax_model                  4
% 2.82/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.82/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.82/1.00  --bmc1_ucm_layered_model                none
% 2.82/1.00  --bmc1_ucm_max_lemma_size               10
% 2.82/1.00  
% 2.82/1.00  ------ AIG Options
% 2.82/1.00  
% 2.82/1.00  --aig_mode                              false
% 2.82/1.00  
% 2.82/1.00  ------ Instantiation Options
% 2.82/1.00  
% 2.82/1.00  --instantiation_flag                    true
% 2.82/1.00  --inst_sos_flag                         false
% 2.82/1.00  --inst_sos_phase                        true
% 2.82/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.82/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.82/1.00  --inst_lit_sel_side                     none
% 2.82/1.00  --inst_solver_per_active                1400
% 2.82/1.00  --inst_solver_calls_frac                1.
% 2.82/1.00  --inst_passive_queue_type               priority_queues
% 2.82/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.82/1.00  --inst_passive_queues_freq              [25;2]
% 2.82/1.00  --inst_dismatching                      true
% 2.82/1.00  --inst_eager_unprocessed_to_passive     true
% 2.82/1.00  --inst_prop_sim_given                   true
% 2.82/1.00  --inst_prop_sim_new                     false
% 2.82/1.00  --inst_subs_new                         false
% 2.82/1.00  --inst_eq_res_simp                      false
% 2.82/1.00  --inst_subs_given                       false
% 2.82/1.00  --inst_orphan_elimination               true
% 2.82/1.00  --inst_learning_loop_flag               true
% 2.82/1.00  --inst_learning_start                   3000
% 2.82/1.00  --inst_learning_factor                  2
% 2.82/1.00  --inst_start_prop_sim_after_learn       3
% 2.82/1.00  --inst_sel_renew                        solver
% 2.82/1.00  --inst_lit_activity_flag                true
% 2.82/1.00  --inst_restr_to_given                   false
% 2.82/1.00  --inst_activity_threshold               500
% 2.82/1.00  --inst_out_proof                        true
% 2.82/1.00  
% 2.82/1.00  ------ Resolution Options
% 2.82/1.00  
% 2.82/1.00  --resolution_flag                       false
% 2.82/1.00  --res_lit_sel                           adaptive
% 2.82/1.00  --res_lit_sel_side                      none
% 2.82/1.00  --res_ordering                          kbo
% 2.82/1.00  --res_to_prop_solver                    active
% 2.82/1.00  --res_prop_simpl_new                    false
% 2.82/1.00  --res_prop_simpl_given                  true
% 2.82/1.00  --res_passive_queue_type                priority_queues
% 2.82/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.82/1.00  --res_passive_queues_freq               [15;5]
% 2.82/1.00  --res_forward_subs                      full
% 2.82/1.00  --res_backward_subs                     full
% 2.82/1.00  --res_forward_subs_resolution           true
% 2.82/1.00  --res_backward_subs_resolution          true
% 2.82/1.00  --res_orphan_elimination                true
% 2.82/1.00  --res_time_limit                        2.
% 2.82/1.00  --res_out_proof                         true
% 2.82/1.00  
% 2.82/1.00  ------ Superposition Options
% 2.82/1.00  
% 2.82/1.00  --superposition_flag                    true
% 2.82/1.00  --sup_passive_queue_type                priority_queues
% 2.82/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.82/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.82/1.00  --demod_completeness_check              fast
% 2.82/1.00  --demod_use_ground                      true
% 2.82/1.00  --sup_to_prop_solver                    passive
% 2.82/1.00  --sup_prop_simpl_new                    true
% 2.82/1.00  --sup_prop_simpl_given                  true
% 2.82/1.00  --sup_fun_splitting                     false
% 2.82/1.00  --sup_smt_interval                      50000
% 2.82/1.00  
% 2.82/1.00  ------ Superposition Simplification Setup
% 2.82/1.00  
% 2.82/1.00  --sup_indices_passive                   []
% 2.82/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.82/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/1.00  --sup_full_bw                           [BwDemod]
% 2.82/1.00  --sup_immed_triv                        [TrivRules]
% 2.82/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.82/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/1.00  --sup_immed_bw_main                     []
% 2.82/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.82/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.82/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.82/1.00  
% 2.82/1.00  ------ Combination Options
% 2.82/1.00  
% 2.82/1.00  --comb_res_mult                         3
% 2.82/1.00  --comb_sup_mult                         2
% 2.82/1.00  --comb_inst_mult                        10
% 2.82/1.00  
% 2.82/1.00  ------ Debug Options
% 2.82/1.00  
% 2.82/1.00  --dbg_backtrace                         false
% 2.82/1.00  --dbg_dump_prop_clauses                 false
% 2.82/1.00  --dbg_dump_prop_clauses_file            -
% 2.82/1.00  --dbg_out_stat                          false
% 2.82/1.00  
% 2.82/1.00  
% 2.82/1.00  
% 2.82/1.00  
% 2.82/1.00  ------ Proving...
% 2.82/1.00  
% 2.82/1.00  
% 2.82/1.00  % SZS status Theorem for theBenchmark.p
% 2.82/1.00  
% 2.82/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.82/1.00  
% 2.82/1.00  fof(f10,axiom,(
% 2.82/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.82/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/1.00  
% 2.82/1.00  fof(f21,plain,(
% 2.82/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.82/1.00    inference(ennf_transformation,[],[f10])).
% 2.82/1.00  
% 2.82/1.00  fof(f22,plain,(
% 2.82/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.82/1.00    inference(flattening,[],[f21])).
% 2.82/1.00  
% 2.82/1.00  fof(f33,plain,(
% 2.82/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.82/1.00    inference(nnf_transformation,[],[f22])).
% 2.82/1.00  
% 2.82/1.00  fof(f53,plain,(
% 2.82/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.82/1.00    inference(cnf_transformation,[],[f33])).
% 2.82/1.00  
% 2.82/1.00  fof(f11,conjecture,(
% 2.82/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.82/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/1.00  
% 2.82/1.00  fof(f12,negated_conjecture,(
% 2.82/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.82/1.00    inference(negated_conjecture,[],[f11])).
% 2.82/1.00  
% 2.82/1.00  fof(f23,plain,(
% 2.82/1.00    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.82/1.00    inference(ennf_transformation,[],[f12])).
% 2.82/1.00  
% 2.82/1.00  fof(f24,plain,(
% 2.82/1.00    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.82/1.00    inference(flattening,[],[f23])).
% 2.82/1.00  
% 2.82/1.00  fof(f35,plain,(
% 2.82/1.00    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK4) & ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK4,X0,X1) & v1_funct_1(sK4))) )),
% 2.82/1.00    introduced(choice_axiom,[])).
% 2.82/1.00  
% 2.82/1.00  fof(f34,plain,(
% 2.82/1.00    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK1,sK2,sK3,X3) & ! [X4] : (k1_funct_1(sK3,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 2.82/1.00    introduced(choice_axiom,[])).
% 2.82/1.00  
% 2.82/1.00  fof(f36,plain,(
% 2.82/1.00    (~r2_relset_1(sK1,sK2,sK3,sK4) & ! [X4] : (k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4) | ~r2_hidden(X4,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 2.82/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f24,f35,f34])).
% 2.82/1.00  
% 2.82/1.00  fof(f63,plain,(
% 2.82/1.00    v1_funct_2(sK4,sK1,sK2)),
% 2.82/1.00    inference(cnf_transformation,[],[f36])).
% 2.82/1.00  
% 2.82/1.00  fof(f64,plain,(
% 2.82/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.82/1.00    inference(cnf_transformation,[],[f36])).
% 2.82/1.00  
% 2.82/1.00  fof(f8,axiom,(
% 2.82/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.82/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/1.00  
% 2.82/1.00  fof(f18,plain,(
% 2.82/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.82/1.00    inference(ennf_transformation,[],[f8])).
% 2.82/1.00  
% 2.82/1.00  fof(f50,plain,(
% 2.82/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.82/1.00    inference(cnf_transformation,[],[f18])).
% 2.82/1.00  
% 2.82/1.00  fof(f60,plain,(
% 2.82/1.00    v1_funct_2(sK3,sK1,sK2)),
% 2.82/1.00    inference(cnf_transformation,[],[f36])).
% 2.82/1.00  
% 2.82/1.00  fof(f61,plain,(
% 2.82/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.82/1.00    inference(cnf_transformation,[],[f36])).
% 2.82/1.00  
% 2.82/1.00  fof(f6,axiom,(
% 2.82/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 2.82/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/1.00  
% 2.82/1.00  fof(f15,plain,(
% 2.82/1.00    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.82/1.00    inference(ennf_transformation,[],[f6])).
% 2.82/1.00  
% 2.82/1.00  fof(f16,plain,(
% 2.82/1.00    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.82/1.00    inference(flattening,[],[f15])).
% 2.82/1.00  
% 2.82/1.00  fof(f30,plain,(
% 2.82/1.00    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0))))),
% 2.82/1.00    introduced(choice_axiom,[])).
% 2.82/1.00  
% 2.82/1.00  fof(f31,plain,(
% 2.82/1.00    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.82/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f30])).
% 2.82/1.00  
% 2.82/1.00  fof(f47,plain,(
% 2.82/1.00    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.82/1.00    inference(cnf_transformation,[],[f31])).
% 2.82/1.00  
% 2.82/1.00  fof(f62,plain,(
% 2.82/1.00    v1_funct_1(sK4)),
% 2.82/1.00    inference(cnf_transformation,[],[f36])).
% 2.82/1.00  
% 2.82/1.00  fof(f7,axiom,(
% 2.82/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.82/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/1.00  
% 2.82/1.00  fof(f17,plain,(
% 2.82/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.82/1.00    inference(ennf_transformation,[],[f7])).
% 2.82/1.00  
% 2.82/1.00  fof(f49,plain,(
% 2.82/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.82/1.00    inference(cnf_transformation,[],[f17])).
% 2.82/1.00  
% 2.82/1.00  fof(f59,plain,(
% 2.82/1.00    v1_funct_1(sK3)),
% 2.82/1.00    inference(cnf_transformation,[],[f36])).
% 2.82/1.00  
% 2.82/1.00  fof(f9,axiom,(
% 2.82/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.82/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/1.00  
% 2.82/1.00  fof(f19,plain,(
% 2.82/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.82/1.00    inference(ennf_transformation,[],[f9])).
% 2.82/1.00  
% 2.82/1.00  fof(f20,plain,(
% 2.82/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.82/1.00    inference(flattening,[],[f19])).
% 2.82/1.00  
% 2.82/1.00  fof(f32,plain,(
% 2.82/1.00    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.82/1.00    inference(nnf_transformation,[],[f20])).
% 2.82/1.00  
% 2.82/1.00  fof(f52,plain,(
% 2.82/1.00    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.82/1.00    inference(cnf_transformation,[],[f32])).
% 2.82/1.00  
% 2.82/1.00  fof(f71,plain,(
% 2.82/1.00    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.82/1.00    inference(equality_resolution,[],[f52])).
% 2.82/1.00  
% 2.82/1.00  fof(f66,plain,(
% 2.82/1.00    ~r2_relset_1(sK1,sK2,sK3,sK4)),
% 2.82/1.00    inference(cnf_transformation,[],[f36])).
% 2.82/1.00  
% 2.82/1.00  fof(f1,axiom,(
% 2.82/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.82/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/1.00  
% 2.82/1.00  fof(f25,plain,(
% 2.82/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.82/1.00    inference(nnf_transformation,[],[f1])).
% 2.82/1.00  
% 2.82/1.00  fof(f26,plain,(
% 2.82/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.82/1.00    inference(flattening,[],[f25])).
% 2.82/1.00  
% 2.82/1.00  fof(f39,plain,(
% 2.82/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.82/1.00    inference(cnf_transformation,[],[f26])).
% 2.82/1.00  
% 2.82/1.00  fof(f37,plain,(
% 2.82/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.82/1.00    inference(cnf_transformation,[],[f26])).
% 2.82/1.00  
% 2.82/1.00  fof(f68,plain,(
% 2.82/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.82/1.00    inference(equality_resolution,[],[f37])).
% 2.82/1.00  
% 2.82/1.00  fof(f65,plain,(
% 2.82/1.00    ( ! [X4] : (k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4) | ~r2_hidden(X4,sK1)) )),
% 2.82/1.00    inference(cnf_transformation,[],[f36])).
% 2.82/1.00  
% 2.82/1.00  fof(f48,plain,(
% 2.82/1.00    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.82/1.00    inference(cnf_transformation,[],[f31])).
% 2.82/1.00  
% 2.82/1.00  fof(f2,axiom,(
% 2.82/1.00    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.82/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/1.00  
% 2.82/1.00  fof(f27,plain,(
% 2.82/1.00    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.82/1.00    inference(nnf_transformation,[],[f2])).
% 2.82/1.00  
% 2.82/1.00  fof(f28,plain,(
% 2.82/1.00    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.82/1.00    inference(flattening,[],[f27])).
% 2.82/1.00  
% 2.82/1.00  fof(f42,plain,(
% 2.82/1.00    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 2.82/1.00    inference(cnf_transformation,[],[f28])).
% 2.82/1.00  
% 2.82/1.00  fof(f69,plain,(
% 2.82/1.00    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 2.82/1.00    inference(equality_resolution,[],[f42])).
% 2.82/1.00  
% 2.82/1.00  fof(f4,axiom,(
% 2.82/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.82/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/1.00  
% 2.82/1.00  fof(f29,plain,(
% 2.82/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.82/1.00    inference(nnf_transformation,[],[f4])).
% 2.82/1.00  
% 2.82/1.00  fof(f44,plain,(
% 2.82/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.82/1.00    inference(cnf_transformation,[],[f29])).
% 2.82/1.00  
% 2.82/1.00  fof(f3,axiom,(
% 2.82/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.82/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/1.00  
% 2.82/1.00  fof(f43,plain,(
% 2.82/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.82/1.00    inference(cnf_transformation,[],[f3])).
% 2.82/1.00  
% 2.82/1.00  cnf(c_21,plain,
% 2.82/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.82/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.82/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.82/1.00      | k1_xboole_0 = X2 ),
% 2.82/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_25,negated_conjecture,
% 2.82/1.00      ( v1_funct_2(sK4,sK1,sK2) ),
% 2.82/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_523,plain,
% 2.82/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.82/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.82/1.00      | sK4 != X0
% 2.82/1.00      | sK2 != X2
% 2.82/1.00      | sK1 != X1
% 2.82/1.00      | k1_xboole_0 = X2 ),
% 2.82/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_25]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_524,plain,
% 2.82/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.82/1.00      | k1_relset_1(sK1,sK2,sK4) = sK1
% 2.82/1.00      | k1_xboole_0 = sK2 ),
% 2.82/1.00      inference(unflattening,[status(thm)],[c_523]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_24,negated_conjecture,
% 2.82/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.82/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_526,plain,
% 2.82/1.00      ( k1_relset_1(sK1,sK2,sK4) = sK1 | k1_xboole_0 = sK2 ),
% 2.82/1.00      inference(global_propositional_subsumption,
% 2.82/1.00                [status(thm)],
% 2.82/1.00                [c_524,c_24]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1309,plain,
% 2.82/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.82/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_13,plain,
% 2.82/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.82/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.82/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1311,plain,
% 2.82/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.82/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.82/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1659,plain,
% 2.82/1.00      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 2.82/1.00      inference(superposition,[status(thm)],[c_1309,c_1311]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1823,plain,
% 2.82/1.00      ( k1_relat_1(sK4) = sK1 | sK2 = k1_xboole_0 ),
% 2.82/1.00      inference(superposition,[status(thm)],[c_526,c_1659]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_28,negated_conjecture,
% 2.82/1.00      ( v1_funct_2(sK3,sK1,sK2) ),
% 2.82/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_534,plain,
% 2.82/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.82/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.82/1.00      | sK3 != X0
% 2.82/1.00      | sK2 != X2
% 2.82/1.00      | sK1 != X1
% 2.82/1.00      | k1_xboole_0 = X2 ),
% 2.82/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_28]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_535,plain,
% 2.82/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.82/1.00      | k1_relset_1(sK1,sK2,sK3) = sK1
% 2.82/1.00      | k1_xboole_0 = sK2 ),
% 2.82/1.00      inference(unflattening,[status(thm)],[c_534]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_27,negated_conjecture,
% 2.82/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.82/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_537,plain,
% 2.82/1.00      ( k1_relset_1(sK1,sK2,sK3) = sK1 | k1_xboole_0 = sK2 ),
% 2.82/1.00      inference(global_propositional_subsumption,
% 2.82/1.00                [status(thm)],
% 2.82/1.00                [c_535,c_27]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1307,plain,
% 2.82/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.82/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1660,plain,
% 2.82/1.00      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 2.82/1.00      inference(superposition,[status(thm)],[c_1307,c_1311]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1891,plain,
% 2.82/1.00      ( k1_relat_1(sK3) = sK1 | sK2 = k1_xboole_0 ),
% 2.82/1.00      inference(superposition,[status(thm)],[c_537,c_1660]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_11,plain,
% 2.82/1.00      ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
% 2.82/1.00      | ~ v1_relat_1(X1)
% 2.82/1.00      | ~ v1_relat_1(X0)
% 2.82/1.00      | ~ v1_funct_1(X1)
% 2.82/1.00      | ~ v1_funct_1(X0)
% 2.82/1.00      | X1 = X0
% 2.82/1.00      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 2.82/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1313,plain,
% 2.82/1.00      ( X0 = X1
% 2.82/1.00      | k1_relat_1(X0) != k1_relat_1(X1)
% 2.82/1.00      | r2_hidden(sK0(X1,X0),k1_relat_1(X1)) = iProver_top
% 2.82/1.00      | v1_relat_1(X1) != iProver_top
% 2.82/1.00      | v1_relat_1(X0) != iProver_top
% 2.82/1.00      | v1_funct_1(X0) != iProver_top
% 2.82/1.00      | v1_funct_1(X1) != iProver_top ),
% 2.82/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2682,plain,
% 2.82/1.00      ( k1_relat_1(X0) != sK1
% 2.82/1.00      | sK4 = X0
% 2.82/1.00      | sK2 = k1_xboole_0
% 2.82/1.00      | r2_hidden(sK0(X0,sK4),k1_relat_1(X0)) = iProver_top
% 2.82/1.00      | v1_relat_1(X0) != iProver_top
% 2.82/1.00      | v1_relat_1(sK4) != iProver_top
% 2.82/1.00      | v1_funct_1(X0) != iProver_top
% 2.82/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.82/1.00      inference(superposition,[status(thm)],[c_1823,c_1313]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_26,negated_conjecture,
% 2.82/1.00      ( v1_funct_1(sK4) ),
% 2.82/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_33,plain,
% 2.82/1.00      ( v1_funct_1(sK4) = iProver_top ),
% 2.82/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_35,plain,
% 2.82/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.82/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_12,plain,
% 2.82/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.82/1.00      | v1_relat_1(X0) ),
% 2.82/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1500,plain,
% 2.82/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.82/1.00      | v1_relat_1(sK4) ),
% 2.82/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1501,plain,
% 2.82/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.82/1.00      | v1_relat_1(sK4) = iProver_top ),
% 2.82/1.00      inference(predicate_to_equality,[status(thm)],[c_1500]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_3128,plain,
% 2.82/1.00      ( v1_funct_1(X0) != iProver_top
% 2.82/1.00      | k1_relat_1(X0) != sK1
% 2.82/1.00      | sK4 = X0
% 2.82/1.00      | sK2 = k1_xboole_0
% 2.82/1.00      | r2_hidden(sK0(X0,sK4),k1_relat_1(X0)) = iProver_top
% 2.82/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.82/1.00      inference(global_propositional_subsumption,
% 2.82/1.00                [status(thm)],
% 2.82/1.00                [c_2682,c_33,c_35,c_1501]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_3129,plain,
% 2.82/1.00      ( k1_relat_1(X0) != sK1
% 2.82/1.00      | sK4 = X0
% 2.82/1.00      | sK2 = k1_xboole_0
% 2.82/1.00      | r2_hidden(sK0(X0,sK4),k1_relat_1(X0)) = iProver_top
% 2.82/1.00      | v1_relat_1(X0) != iProver_top
% 2.82/1.00      | v1_funct_1(X0) != iProver_top ),
% 2.82/1.00      inference(renaming,[status(thm)],[c_3128]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_3141,plain,
% 2.82/1.00      ( sK4 = sK3
% 2.82/1.00      | sK2 = k1_xboole_0
% 2.82/1.00      | r2_hidden(sK0(sK3,sK4),k1_relat_1(sK3)) = iProver_top
% 2.82/1.00      | v1_relat_1(sK3) != iProver_top
% 2.82/1.00      | v1_funct_1(sK3) != iProver_top ),
% 2.82/1.00      inference(superposition,[status(thm)],[c_1891,c_3129]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_29,negated_conjecture,
% 2.82/1.00      ( v1_funct_1(sK3) ),
% 2.82/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_30,plain,
% 2.82/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 2.82/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_32,plain,
% 2.82/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.82/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_14,plain,
% 2.82/1.00      ( r2_relset_1(X0,X1,X2,X2)
% 2.82/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.82/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_22,negated_conjecture,
% 2.82/1.00      ( ~ r2_relset_1(sK1,sK2,sK3,sK4) ),
% 2.82/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_364,plain,
% 2.82/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.82/1.00      | sK4 != X0
% 2.82/1.00      | sK3 != X0
% 2.82/1.00      | sK2 != X2
% 2.82/1.00      | sK1 != X1 ),
% 2.82/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_365,plain,
% 2.82/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.82/1.00      | sK3 != sK4 ),
% 2.82/1.00      inference(unflattening,[status(thm)],[c_364]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1503,plain,
% 2.82/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.82/1.00      | v1_relat_1(sK3) ),
% 2.82/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1504,plain,
% 2.82/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.82/1.00      | v1_relat_1(sK3) = iProver_top ),
% 2.82/1.00      inference(predicate_to_equality,[status(thm)],[c_1503]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_0,plain,
% 2.82/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.82/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1602,plain,
% 2.82/1.00      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | X0 = sK3 ),
% 2.82/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1768,plain,
% 2.82/1.00      ( ~ r1_tarski(sK3,sK3) | sK3 = sK3 ),
% 2.82/1.00      inference(instantiation,[status(thm)],[c_1602]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2,plain,
% 2.82/1.00      ( r1_tarski(X0,X0) ),
% 2.82/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1769,plain,
% 2.82/1.00      ( r1_tarski(sK3,sK3) ),
% 2.82/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_825,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1529,plain,
% 2.82/1.00      ( sK4 != X0 | sK3 != X0 | sK3 = sK4 ),
% 2.82/1.00      inference(instantiation,[status(thm)],[c_825]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1876,plain,
% 2.82/1.00      ( sK4 != sK3 | sK3 = sK4 | sK3 != sK3 ),
% 2.82/1.00      inference(instantiation,[status(thm)],[c_1529]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_3154,plain,
% 2.82/1.00      ( sK2 = k1_xboole_0
% 2.82/1.00      | r2_hidden(sK0(sK3,sK4),k1_relat_1(sK3)) = iProver_top ),
% 2.82/1.00      inference(global_propositional_subsumption,
% 2.82/1.00                [status(thm)],
% 2.82/1.00                [c_3141,c_30,c_32,c_24,c_365,c_1504,c_1768,c_1769,c_1876]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_3160,plain,
% 2.82/1.00      ( sK2 = k1_xboole_0 | r2_hidden(sK0(sK3,sK4),sK1) = iProver_top ),
% 2.82/1.00      inference(superposition,[status(thm)],[c_1891,c_3154]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_23,negated_conjecture,
% 2.82/1.00      ( ~ r2_hidden(X0,sK1) | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) ),
% 2.82/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1310,plain,
% 2.82/1.00      ( k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
% 2.82/1.00      | r2_hidden(X0,sK1) != iProver_top ),
% 2.82/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_3181,plain,
% 2.82/1.00      ( k1_funct_1(sK3,sK0(sK3,sK4)) = k1_funct_1(sK4,sK0(sK3,sK4))
% 2.82/1.00      | sK2 = k1_xboole_0 ),
% 2.82/1.00      inference(superposition,[status(thm)],[c_3160,c_1310]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_10,plain,
% 2.82/1.00      ( ~ v1_relat_1(X0)
% 2.82/1.00      | ~ v1_relat_1(X1)
% 2.82/1.00      | ~ v1_funct_1(X0)
% 2.82/1.00      | ~ v1_funct_1(X1)
% 2.82/1.00      | X0 = X1
% 2.82/1.00      | k1_funct_1(X0,sK0(X1,X0)) != k1_funct_1(X1,sK0(X1,X0))
% 2.82/1.00      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 2.82/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1314,plain,
% 2.82/1.00      ( X0 = X1
% 2.82/1.00      | k1_funct_1(X0,sK0(X1,X0)) != k1_funct_1(X1,sK0(X1,X0))
% 2.82/1.00      | k1_relat_1(X0) != k1_relat_1(X1)
% 2.82/1.00      | v1_relat_1(X0) != iProver_top
% 2.82/1.00      | v1_relat_1(X1) != iProver_top
% 2.82/1.00      | v1_funct_1(X1) != iProver_top
% 2.82/1.00      | v1_funct_1(X0) != iProver_top ),
% 2.82/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_3249,plain,
% 2.82/1.00      ( k1_relat_1(sK3) != k1_relat_1(sK4)
% 2.82/1.00      | sK4 = sK3
% 2.82/1.00      | sK2 = k1_xboole_0
% 2.82/1.00      | v1_relat_1(sK4) != iProver_top
% 2.82/1.00      | v1_relat_1(sK3) != iProver_top
% 2.82/1.00      | v1_funct_1(sK4) != iProver_top
% 2.82/1.00      | v1_funct_1(sK3) != iProver_top ),
% 2.82/1.00      inference(superposition,[status(thm)],[c_3181,c_1314]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_3265,plain,
% 2.82/1.00      ( ~ v1_relat_1(sK4)
% 2.82/1.00      | ~ v1_relat_1(sK3)
% 2.82/1.00      | ~ v1_funct_1(sK4)
% 2.82/1.00      | ~ v1_funct_1(sK3)
% 2.82/1.00      | k1_relat_1(sK3) != k1_relat_1(sK4)
% 2.82/1.00      | sK4 = sK3
% 2.82/1.00      | sK2 = k1_xboole_0 ),
% 2.82/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_3249]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_3469,plain,
% 2.82/1.00      ( k1_relat_1(sK3) != k1_relat_1(sK4) | sK2 = k1_xboole_0 ),
% 2.82/1.00      inference(global_propositional_subsumption,
% 2.82/1.00                [status(thm)],
% 2.82/1.00                [c_3249,c_29,c_27,c_26,c_24,c_365,c_1500,c_1503,c_1768,
% 2.82/1.00                 c_1769,c_1876,c_3265]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_3473,plain,
% 2.82/1.00      ( k1_relat_1(sK3) != sK1 | sK2 = k1_xboole_0 ),
% 2.82/1.00      inference(superposition,[status(thm)],[c_1823,c_3469]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_3474,plain,
% 2.82/1.00      ( sK2 = k1_xboole_0 ),
% 2.82/1.00      inference(global_propositional_subsumption,
% 2.82/1.00                [status(thm)],
% 2.82/1.00                [c_3473,c_1891]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_3493,plain,
% 2.82/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
% 2.82/1.00      inference(demodulation,[status(thm)],[c_3474,c_1309]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_3,plain,
% 2.82/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.82/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_3499,plain,
% 2.82/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.82/1.00      inference(demodulation,[status(thm)],[c_3493,c_3]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_3494,plain,
% 2.82/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
% 2.82/1.00      inference(demodulation,[status(thm)],[c_3474,c_1307]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_3496,plain,
% 2.82/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.82/1.00      inference(demodulation,[status(thm)],[c_3494,c_3]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_8,plain,
% 2.82/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.82/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_3199,plain,
% 2.82/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0)) | r1_tarski(sK3,X0) ),
% 2.82/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_3200,plain,
% 2.82/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 2.82/1.00      | r1_tarski(sK3,X0) = iProver_top ),
% 2.82/1.00      inference(predicate_to_equality,[status(thm)],[c_3199]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_3202,plain,
% 2.82/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.82/1.00      | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 2.82/1.00      inference(instantiation,[status(thm)],[c_3200]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_3171,plain,
% 2.82/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0)) | r1_tarski(sK4,X0) ),
% 2.82/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_3172,plain,
% 2.82/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 2.82/1.00      | r1_tarski(sK4,X0) = iProver_top ),
% 2.82/1.00      inference(predicate_to_equality,[status(thm)],[c_3171]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_3174,plain,
% 2.82/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.82/1.00      | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
% 2.82/1.00      inference(instantiation,[status(thm)],[c_3172]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_6,plain,
% 2.82/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.82/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2159,plain,
% 2.82/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) ),
% 2.82/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2162,plain,
% 2.82/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) = iProver_top ),
% 2.82/1.00      inference(predicate_to_equality,[status(thm)],[c_2159]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2150,plain,
% 2.82/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) ),
% 2.82/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2153,plain,
% 2.82/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) = iProver_top ),
% 2.82/1.00      inference(predicate_to_equality,[status(thm)],[c_2150]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1780,plain,
% 2.82/1.00      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | sK3 = X0 ),
% 2.82/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1781,plain,
% 2.82/1.00      ( sK3 = X0
% 2.82/1.00      | r1_tarski(X0,sK3) != iProver_top
% 2.82/1.00      | r1_tarski(sK3,X0) != iProver_top ),
% 2.82/1.00      inference(predicate_to_equality,[status(thm)],[c_1780]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1783,plain,
% 2.82/1.00      ( sK3 = k1_xboole_0
% 2.82/1.00      | r1_tarski(sK3,k1_xboole_0) != iProver_top
% 2.82/1.00      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 2.82/1.00      inference(instantiation,[status(thm)],[c_1781]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1763,plain,
% 2.82/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3)) | r1_tarski(X0,sK3) ),
% 2.82/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1764,plain,
% 2.82/1.00      ( m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top
% 2.82/1.00      | r1_tarski(X0,sK3) = iProver_top ),
% 2.82/1.00      inference(predicate_to_equality,[status(thm)],[c_1763]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1766,plain,
% 2.82/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top
% 2.82/1.00      | r1_tarski(k1_xboole_0,sK3) = iProver_top ),
% 2.82/1.00      inference(instantiation,[status(thm)],[c_1764]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1744,plain,
% 2.82/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4)) | r1_tarski(X0,sK4) ),
% 2.82/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1745,plain,
% 2.82/1.00      ( m1_subset_1(X0,k1_zfmisc_1(sK4)) != iProver_top
% 2.82/1.00      | r1_tarski(X0,sK4) = iProver_top ),
% 2.82/1.00      inference(predicate_to_equality,[status(thm)],[c_1744]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1747,plain,
% 2.82/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) != iProver_top
% 2.82/1.00      | r1_tarski(k1_xboole_0,sK4) = iProver_top ),
% 2.82/1.00      inference(instantiation,[status(thm)],[c_1745]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1681,plain,
% 2.82/1.00      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | sK4 = X0 ),
% 2.82/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1682,plain,
% 2.82/1.00      ( sK4 = X0
% 2.82/1.00      | r1_tarski(X0,sK4) != iProver_top
% 2.82/1.00      | r1_tarski(sK4,X0) != iProver_top ),
% 2.82/1.00      inference(predicate_to_equality,[status(thm)],[c_1681]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1684,plain,
% 2.82/1.00      ( sK4 = k1_xboole_0
% 2.82/1.00      | r1_tarski(sK4,k1_xboole_0) != iProver_top
% 2.82/1.00      | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
% 2.82/1.00      inference(instantiation,[status(thm)],[c_1682]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1530,plain,
% 2.82/1.00      ( sK4 != k1_xboole_0 | sK3 = sK4 | sK3 != k1_xboole_0 ),
% 2.82/1.00      inference(instantiation,[status(thm)],[c_1529]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(contradiction,plain,
% 2.82/1.00      ( $false ),
% 2.82/1.00      inference(minisat,
% 2.82/1.00                [status(thm)],
% 2.82/1.00                [c_3499,c_3496,c_3202,c_3174,c_2162,c_2153,c_1783,c_1766,
% 2.82/1.00                 c_1747,c_1684,c_1530,c_365,c_24]) ).
% 2.82/1.00  
% 2.82/1.00  
% 2.82/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.82/1.00  
% 2.82/1.00  ------                               Statistics
% 2.82/1.00  
% 2.82/1.00  ------ General
% 2.82/1.00  
% 2.82/1.00  abstr_ref_over_cycles:                  0
% 2.82/1.00  abstr_ref_under_cycles:                 0
% 2.82/1.00  gc_basic_clause_elim:                   0
% 2.82/1.00  forced_gc_time:                         0
% 2.82/1.00  parsing_time:                           0.01
% 2.82/1.00  unif_index_cands_time:                  0.
% 2.82/1.00  unif_index_add_time:                    0.
% 2.82/1.00  orderings_time:                         0.
% 2.82/1.00  out_proof_time:                         0.01
% 2.82/1.00  total_time:                             0.151
% 2.82/1.00  num_of_symbols:                         49
% 2.82/1.00  num_of_terms:                           3159
% 2.82/1.00  
% 2.82/1.00  ------ Preprocessing
% 2.82/1.00  
% 2.82/1.00  num_of_splits:                          0
% 2.82/1.00  num_of_split_atoms:                     0
% 2.82/1.00  num_of_reused_defs:                     0
% 2.82/1.00  num_eq_ax_congr_red:                    20
% 2.82/1.00  num_of_sem_filtered_clauses:            1
% 2.82/1.00  num_of_subtypes:                        0
% 2.82/1.00  monotx_restored_types:                  0
% 2.82/1.00  sat_num_of_epr_types:                   0
% 2.82/1.00  sat_num_of_non_cyclic_types:            0
% 2.82/1.00  sat_guarded_non_collapsed_types:        0
% 2.82/1.00  num_pure_diseq_elim:                    0
% 2.82/1.00  simp_replaced_by:                       0
% 2.82/1.00  res_preprocessed:                       123
% 2.82/1.00  prep_upred:                             0
% 2.82/1.00  prep_unflattend:                        47
% 2.82/1.00  smt_new_axioms:                         0
% 2.82/1.00  pred_elim_cands:                        5
% 2.82/1.00  pred_elim:                              2
% 2.82/1.00  pred_elim_cl:                           4
% 2.82/1.00  pred_elim_cycles:                       5
% 2.82/1.00  merged_defs:                            8
% 2.82/1.00  merged_defs_ncl:                        0
% 2.82/1.00  bin_hyper_res:                          8
% 2.82/1.00  prep_cycles:                            4
% 2.82/1.00  pred_elim_time:                         0.006
% 2.82/1.00  splitting_time:                         0.
% 2.82/1.00  sem_filter_time:                        0.
% 2.82/1.00  monotx_time:                            0.013
% 2.82/1.00  subtype_inf_time:                       0.
% 2.82/1.00  
% 2.82/1.00  ------ Problem properties
% 2.82/1.00  
% 2.82/1.00  clauses:                                25
% 2.82/1.00  conjectures:                            5
% 2.82/1.00  epr:                                    5
% 2.82/1.00  horn:                                   19
% 2.82/1.00  ground:                                 11
% 2.82/1.00  unary:                                  9
% 2.82/1.00  binary:                                 7
% 2.82/1.00  lits:                                   60
% 2.82/1.00  lits_eq:                                28
% 2.82/1.00  fd_pure:                                0
% 2.82/1.00  fd_pseudo:                              0
% 2.82/1.00  fd_cond:                                1
% 2.82/1.00  fd_pseudo_cond:                         3
% 2.82/1.00  ac_symbols:                             0
% 2.82/1.00  
% 2.82/1.00  ------ Propositional Solver
% 2.82/1.00  
% 2.82/1.00  prop_solver_calls:                      28
% 2.82/1.00  prop_fast_solver_calls:                 802
% 2.82/1.00  smt_solver_calls:                       0
% 2.82/1.00  smt_fast_solver_calls:                  0
% 2.82/1.00  prop_num_of_clauses:                    1091
% 2.82/1.00  prop_preprocess_simplified:             4196
% 2.82/1.00  prop_fo_subsumed:                       14
% 2.82/1.00  prop_solver_time:                       0.
% 2.82/1.00  smt_solver_time:                        0.
% 2.82/1.00  smt_fast_solver_time:                   0.
% 2.82/1.00  prop_fast_solver_time:                  0.
% 2.82/1.00  prop_unsat_core_time:                   0.
% 2.82/1.00  
% 2.82/1.00  ------ QBF
% 2.82/1.00  
% 2.82/1.00  qbf_q_res:                              0
% 2.82/1.00  qbf_num_tautologies:                    0
% 2.82/1.00  qbf_prep_cycles:                        0
% 2.82/1.00  
% 2.82/1.00  ------ BMC1
% 2.82/1.00  
% 2.82/1.00  bmc1_current_bound:                     -1
% 2.82/1.00  bmc1_last_solved_bound:                 -1
% 2.82/1.00  bmc1_unsat_core_size:                   -1
% 2.82/1.00  bmc1_unsat_core_parents_size:           -1
% 2.82/1.00  bmc1_merge_next_fun:                    0
% 2.82/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.82/1.00  
% 2.82/1.00  ------ Instantiation
% 2.82/1.00  
% 2.82/1.00  inst_num_of_clauses:                    404
% 2.82/1.00  inst_num_in_passive:                    56
% 2.82/1.00  inst_num_in_active:                     234
% 2.82/1.00  inst_num_in_unprocessed:                114
% 2.82/1.00  inst_num_of_loops:                      260
% 2.82/1.00  inst_num_of_learning_restarts:          0
% 2.82/1.00  inst_num_moves_active_passive:          23
% 2.82/1.00  inst_lit_activity:                      0
% 2.82/1.00  inst_lit_activity_moves:                0
% 2.82/1.00  inst_num_tautologies:                   0
% 2.82/1.00  inst_num_prop_implied:                  0
% 2.82/1.00  inst_num_existing_simplified:           0
% 2.82/1.00  inst_num_eq_res_simplified:             0
% 2.82/1.00  inst_num_child_elim:                    0
% 2.82/1.00  inst_num_of_dismatching_blockings:      88
% 2.82/1.00  inst_num_of_non_proper_insts:           454
% 2.82/1.00  inst_num_of_duplicates:                 0
% 2.82/1.00  inst_inst_num_from_inst_to_res:         0
% 2.82/1.00  inst_dismatching_checking_time:         0.
% 2.82/1.00  
% 2.82/1.00  ------ Resolution
% 2.82/1.00  
% 2.82/1.00  res_num_of_clauses:                     0
% 2.82/1.00  res_num_in_passive:                     0
% 2.82/1.00  res_num_in_active:                      0
% 2.82/1.00  res_num_of_loops:                       127
% 2.82/1.00  res_forward_subset_subsumed:            24
% 2.82/1.00  res_backward_subset_subsumed:           0
% 2.82/1.00  res_forward_subsumed:                   0
% 2.82/1.00  res_backward_subsumed:                  0
% 2.82/1.00  res_forward_subsumption_resolution:     0
% 2.82/1.00  res_backward_subsumption_resolution:    0
% 2.82/1.00  res_clause_to_clause_subsumption:       159
% 2.82/1.00  res_orphan_elimination:                 0
% 2.82/1.00  res_tautology_del:                      48
% 2.82/1.00  res_num_eq_res_simplified:              0
% 2.82/1.00  res_num_sel_changes:                    0
% 2.82/1.00  res_moves_from_active_to_pass:          0
% 2.82/1.00  
% 2.82/1.00  ------ Superposition
% 2.82/1.00  
% 2.82/1.00  sup_time_total:                         0.
% 2.82/1.00  sup_time_generating:                    0.
% 2.82/1.00  sup_time_sim_full:                      0.
% 2.82/1.00  sup_time_sim_immed:                     0.
% 2.82/1.00  
% 2.82/1.00  sup_num_of_clauses:                     46
% 2.82/1.00  sup_num_in_active:                      31
% 2.82/1.00  sup_num_in_passive:                     15
% 2.82/1.00  sup_num_of_loops:                       51
% 2.82/1.00  sup_fw_superposition:                   39
% 2.82/1.00  sup_bw_superposition:                   11
% 2.82/1.00  sup_immediate_simplified:               12
% 2.82/1.00  sup_given_eliminated:                   0
% 2.82/1.00  comparisons_done:                       0
% 2.82/1.00  comparisons_avoided:                    9
% 2.82/1.00  
% 2.82/1.00  ------ Simplifications
% 2.82/1.00  
% 2.82/1.00  
% 2.82/1.00  sim_fw_subset_subsumed:                 0
% 2.82/1.00  sim_bw_subset_subsumed:                 2
% 2.82/1.00  sim_fw_subsumed:                        2
% 2.82/1.00  sim_bw_subsumed:                        0
% 2.82/1.00  sim_fw_subsumption_res:                 4
% 2.82/1.00  sim_bw_subsumption_res:                 0
% 2.82/1.00  sim_tautology_del:                      1
% 2.82/1.00  sim_eq_tautology_del:                   10
% 2.82/1.00  sim_eq_res_simp:                        2
% 2.82/1.00  sim_fw_demodulated:                     12
% 2.82/1.00  sim_bw_demodulated:                     18
% 2.82/1.00  sim_light_normalised:                   0
% 2.82/1.00  sim_joinable_taut:                      0
% 2.82/1.00  sim_joinable_simp:                      0
% 2.82/1.00  sim_ac_normalised:                      0
% 2.82/1.00  sim_smt_subsumption:                    0
% 2.82/1.00  
%------------------------------------------------------------------------------
