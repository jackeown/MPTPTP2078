%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:48 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :  159 (1749 expanded)
%              Number of clauses        :  100 ( 614 expanded)
%              Number of leaves         :   18 ( 393 expanded)
%              Depth                    :   24
%              Number of atoms          :  477 (7786 expanded)
%              Number of equality atoms :  214 (2259 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( ! [X4] :
                  ~ ( k1_funct_1(X2,X4) = X3
                    & r2_hidden(X4,X0) )
              & r2_hidden(X3,X1) )
       => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( ! [X4] :
                    ~ ( k1_funct_1(X2,X4) = X3
                      & r2_hidden(X4,X0) )
                & r2_hidden(X3,X1) )
         => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f40,plain,(
    ! [X2,X0,X3] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) = X3
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK5(X3)) = X3
        & r2_hidden(sK5(X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(X0,X1,X2) != X1
        & ! [X3] :
            ( ? [X4] :
                ( k1_funct_1(X2,X4) = X3
                & r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( k2_relset_1(sK2,sK3,sK4) != sK3
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK4,X4) = X3
              & r2_hidden(X4,sK2) )
          | ~ r2_hidden(X3,sK3) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK4,sK2,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( k2_relset_1(sK2,sK3,sK4) != sK3
    & ! [X3] :
        ( ( k1_funct_1(sK4,sK5(X3)) = X3
          & r2_hidden(sK5(X3),sK2) )
        | ~ r2_hidden(X3,sK3) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f29,f40,f39])).

fof(f63,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
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

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f64,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f62,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f66,plain,(
    ! [X3] :
      ( k1_funct_1(sK4,sK5(X3)) = X3
      | ~ r2_hidden(X3,sK3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f67,plain,(
    k2_relset_1(sK2,sK3,sK4) != sK3 ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    ! [X3] :
      ( r2_hidden(sK5(X3),sK2)
      | ~ r2_hidden(X3,sK3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1),X1)
          | ~ r2_hidden(sK1(X0,X1),X0) )
        & ( r2_hidden(sK1(X0,X1),X1)
          | r2_hidden(sK1(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK1(X0,X1),X1)
          | ~ r2_hidden(sK1(X0,X1),X0) )
        & ( r2_hidden(sK1(X0,X1),X1)
          | r2_hidden(sK1(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK1(X0,X1),X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK1(X0,X1),X1)
      | ~ r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_420,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_23])).

cnf(c_421,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_652,plain,
    ( k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != sK4
    | sK3 != X1
    | sK2 != X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_421])).

cnf(c_653,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_652])).

cnf(c_716,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_653])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_465,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_23])).

cnf(c_466,plain,
    ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_465])).

cnf(c_1248,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(equality_resolution,[status(thm)],[c_466])).

cnf(c_1501,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_716,c_1248])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_300,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_25])).

cnf(c_301,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_300])).

cnf(c_341,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(sK4))
    | r2_hidden(k1_funct_1(sK4,X3),k2_relat_1(sK4))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_301])).

cnf(c_342,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r2_hidden(X2,k1_relat_1(sK4))
    | r2_hidden(k1_funct_1(sK4,X2),k2_relat_1(sK4)) ),
    inference(unflattening,[status(thm)],[c_341])).

cnf(c_539,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_342])).

cnf(c_717,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(equality_resolution_simp,[status(thm)],[c_539])).

cnf(c_834,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_717])).

cnf(c_1072,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_834])).

cnf(c_835,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_717])).

cnf(c_859,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_835])).

cnf(c_860,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_834])).

cnf(c_833,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_717])).

cnf(c_1073,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_833])).

cnf(c_1693,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1073])).

cnf(c_1729,plain,
    ( r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1072,c_859,c_860,c_1693])).

cnf(c_1730,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1729])).

cnf(c_8,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_320,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X3),X4)
    | ~ v1_relat_1(X3)
    | X0 != X3
    | X2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_11])).

cnf(c_321,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_320])).

cnf(c_325,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_321,c_10])).

cnf(c_326,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_325])).

cnf(c_408,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_326,c_23])).

cnf(c_409,plain,
    ( r1_tarski(k2_relat_1(sK4),X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_408])).

cnf(c_1074,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | r1_tarski(k2_relat_1(sK4),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_409])).

cnf(c_1536,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1074])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1080,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1741,plain,
    ( r2_hidden(X0,k2_relat_1(sK4)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1536,c_1080])).

cnf(c_1998,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1730,c_1741])).

cnf(c_21,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | k1_funct_1(sK4,sK5(X0)) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1077,plain,
    ( k1_funct_1(sK4,sK5(X0)) = X0
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2844,plain,
    ( k1_funct_1(sK4,sK5(k1_funct_1(sK4,X0))) = k1_funct_1(sK4,X0)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1998,c_1077])).

cnf(c_2896,plain,
    ( k1_funct_1(sK4,sK5(k1_funct_1(sK4,X0))) = k1_funct_1(sK4,X0)
    | sK3 = k1_xboole_0
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1501,c_2844])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_456,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_23])).

cnf(c_457,plain,
    ( k2_relset_1(X0,X1,sK4) = k2_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_456])).

cnf(c_1208,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(equality_resolution,[status(thm)],[c_457])).

cnf(c_20,negated_conjecture,
    ( k2_relset_1(sK2,sK3,sK4) != sK3 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1290,plain,
    ( k2_relat_1(sK4) != sK3 ),
    inference(demodulation,[status(thm)],[c_1208,c_20])).

cnf(c_22,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | r2_hidden(sK5(X0),sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2798,plain,
    ( ~ r2_hidden(sK1(sK3,k2_relat_1(sK4)),sK3)
    | r2_hidden(sK5(sK1(sK3,k2_relat_1(sK4))),sK2) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2799,plain,
    ( r2_hidden(sK1(sK3,k2_relat_1(sK4)),sK3) != iProver_top
    | r2_hidden(sK5(sK1(sK3,k2_relat_1(sK4))),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2798])).

cnf(c_6,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | r2_hidden(sK1(X0,X1),X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1078,plain,
    ( X0 = X1
    | r2_hidden(sK1(X0,X1),X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1478,plain,
    ( k1_funct_1(sK4,sK5(sK1(sK3,X0))) = sK1(sK3,X0)
    | sK3 = X0
    | r2_hidden(sK1(sK3,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1078,c_1077])).

cnf(c_1999,plain,
    ( k1_funct_1(sK4,sK5(sK1(sK3,k2_relat_1(sK4)))) = sK1(sK3,k2_relat_1(sK4))
    | k2_relat_1(sK4) = sK3
    | r2_hidden(sK1(sK3,k2_relat_1(sK4)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1478,c_1741])).

cnf(c_2048,plain,
    ( k1_funct_1(sK4,sK5(sK1(sK3,k2_relat_1(sK4)))) = sK1(sK3,k2_relat_1(sK4))
    | r2_hidden(sK1(sK3,k2_relat_1(sK4)),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1999,c_1290])).

cnf(c_2054,plain,
    ( k1_funct_1(sK4,sK5(sK1(sK3,k2_relat_1(sK4)))) = sK1(sK3,k2_relat_1(sK4)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2048,c_1077])).

cnf(c_2842,plain,
    ( r2_hidden(sK1(sK3,k2_relat_1(sK4)),sK3) = iProver_top
    | r2_hidden(sK5(sK1(sK3,k2_relat_1(sK4))),k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2054,c_1998])).

cnf(c_838,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1209,plain,
    ( k2_relset_1(sK2,sK3,sK4) != X0
    | k2_relset_1(sK2,sK3,sK4) = sK3
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_838])).

cnf(c_1280,plain,
    ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
    | k2_relset_1(sK2,sK3,sK4) = sK3
    | sK3 != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1209])).

cnf(c_5,plain,
    ( ~ r2_hidden(sK1(X0,X1),X1)
    | ~ r2_hidden(sK1(X0,X1),X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1325,plain,
    ( ~ r2_hidden(sK1(sK3,X0),X0)
    | ~ r2_hidden(sK1(sK3,X0),sK3)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1699,plain,
    ( ~ r2_hidden(sK1(sK3,k2_relat_1(sK4)),k2_relat_1(sK4))
    | ~ r2_hidden(sK1(sK3,k2_relat_1(sK4)),sK3)
    | sK3 = k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1325])).

cnf(c_1700,plain,
    ( sK3 = k2_relat_1(sK4)
    | r2_hidden(sK1(sK3,k2_relat_1(sK4)),k2_relat_1(sK4)) != iProver_top
    | r2_hidden(sK1(sK3,k2_relat_1(sK4)),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1699])).

cnf(c_2055,plain,
    ( r2_hidden(sK1(sK3,k2_relat_1(sK4)),k2_relat_1(sK4)) = iProver_top
    | r2_hidden(sK5(sK1(sK3,k2_relat_1(sK4))),k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2054,c_1730])).

cnf(c_2958,plain,
    ( r2_hidden(sK5(sK1(sK3,k2_relat_1(sK4))),k1_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2842,c_20,c_1208,c_1280,c_1700,c_2055])).

cnf(c_2963,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK5(sK1(sK3,k2_relat_1(sK4))),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1501,c_2958])).

cnf(c_1996,plain,
    ( k2_relat_1(sK4) = X0
    | r2_hidden(sK1(X0,k2_relat_1(sK4)),X0) = iProver_top
    | r2_hidden(sK1(X0,k2_relat_1(sK4)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1078,c_1741])).

cnf(c_3079,plain,
    ( k2_relat_1(sK4) = sK3
    | r2_hidden(sK1(sK3,k2_relat_1(sK4)),sK3) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_1996])).

cnf(c_3081,plain,
    ( k2_relat_1(sK4) = sK3
    | r2_hidden(sK1(sK3,k2_relat_1(sK4)),sK3) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3079])).

cnf(c_3711,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2896,c_1290,c_2799,c_2963,c_3081])).

cnf(c_3730,plain,
    ( r1_tarski(k2_relat_1(sK4),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3711,c_1536])).

cnf(c_840,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_1413,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relset_1(sK2,sK3,sK4),X1)
    | k2_relset_1(sK2,sK3,sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_840])).

cnf(c_3340,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),X0)
    | ~ r1_tarski(k2_relat_1(sK4),X0)
    | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1413])).

cnf(c_3341,plain,
    ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
    | r1_tarski(k2_relset_1(sK2,sK3,sK4),X0) = iProver_top
    | r1_tarski(k2_relat_1(sK4),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3340])).

cnf(c_3343,plain,
    ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
    | r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_xboole_0) = iProver_top
    | r1_tarski(k2_relat_1(sK4),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3341])).

cnf(c_1683,plain,
    ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),X0)
    | r2_hidden(sK1(k2_relset_1(sK2,sK3,sK4),X1),X0)
    | ~ r2_hidden(sK1(k2_relset_1(sK2,sK3,sK4),X1),k2_relset_1(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1684,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),X0) != iProver_top
    | r2_hidden(sK1(k2_relset_1(sK2,sK3,sK4),X1),X0) = iProver_top
    | r2_hidden(sK1(k2_relset_1(sK2,sK3,sK4),X1),k2_relset_1(sK2,sK3,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1683])).

cnf(c_1686,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_xboole_0) != iProver_top
    | r2_hidden(sK1(k2_relset_1(sK2,sK3,sK4),k1_xboole_0),k2_relset_1(sK2,sK3,sK4)) != iProver_top
    | r2_hidden(sK1(k2_relset_1(sK2,sK3,sK4),k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1684])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_4,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_289,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_4])).

cnf(c_290,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_289])).

cnf(c_1593,plain,
    ( ~ r2_hidden(sK1(k2_relset_1(sK2,sK3,sK4),k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_290])).

cnf(c_1596,plain,
    ( r2_hidden(sK1(k2_relset_1(sK2,sK3,sK4),k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1593])).

cnf(c_1262,plain,
    ( r2_hidden(sK1(k2_relset_1(sK2,sK3,sK4),X0),X0)
    | r2_hidden(sK1(k2_relset_1(sK2,sK3,sK4),X0),k2_relset_1(sK2,sK3,sK4))
    | k2_relset_1(sK2,sK3,sK4) = X0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1268,plain,
    ( k2_relset_1(sK2,sK3,sK4) = X0
    | r2_hidden(sK1(k2_relset_1(sK2,sK3,sK4),X0),X0) = iProver_top
    | r2_hidden(sK1(k2_relset_1(sK2,sK3,sK4),X0),k2_relset_1(sK2,sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1262])).

cnf(c_1270,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k1_xboole_0
    | r2_hidden(sK1(k2_relset_1(sK2,sK3,sK4),k1_xboole_0),k2_relset_1(sK2,sK3,sK4)) = iProver_top
    | r2_hidden(sK1(k2_relset_1(sK2,sK3,sK4),k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1268])).

cnf(c_1210,plain,
    ( k2_relset_1(sK2,sK3,sK4) = sK3
    | k2_relset_1(sK2,sK3,sK4) != k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1209])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3730,c_3343,c_3081,c_2963,c_2799,c_1686,c_1596,c_1290,c_1270,c_1210,c_1208,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:42:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.94/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/0.99  
% 2.94/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.94/0.99  
% 2.94/0.99  ------  iProver source info
% 2.94/0.99  
% 2.94/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.94/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.94/0.99  git: non_committed_changes: false
% 2.94/0.99  git: last_make_outside_of_git: false
% 2.94/0.99  
% 2.94/0.99  ------ 
% 2.94/0.99  
% 2.94/0.99  ------ Input Options
% 2.94/0.99  
% 2.94/0.99  --out_options                           all
% 2.94/0.99  --tptp_safe_out                         true
% 2.94/0.99  --problem_path                          ""
% 2.94/0.99  --include_path                          ""
% 2.94/0.99  --clausifier                            res/vclausify_rel
% 2.94/0.99  --clausifier_options                    --mode clausify
% 2.94/0.99  --stdin                                 false
% 2.94/0.99  --stats_out                             all
% 2.94/0.99  
% 2.94/0.99  ------ General Options
% 2.94/0.99  
% 2.94/0.99  --fof                                   false
% 2.94/0.99  --time_out_real                         305.
% 2.94/0.99  --time_out_virtual                      -1.
% 2.94/0.99  --symbol_type_check                     false
% 2.94/0.99  --clausify_out                          false
% 2.94/0.99  --sig_cnt_out                           false
% 2.94/0.99  --trig_cnt_out                          false
% 2.94/0.99  --trig_cnt_out_tolerance                1.
% 2.94/0.99  --trig_cnt_out_sk_spl                   false
% 2.94/0.99  --abstr_cl_out                          false
% 2.94/0.99  
% 2.94/0.99  ------ Global Options
% 2.94/0.99  
% 2.94/0.99  --schedule                              default
% 2.94/0.99  --add_important_lit                     false
% 2.94/0.99  --prop_solver_per_cl                    1000
% 2.94/0.99  --min_unsat_core                        false
% 2.94/0.99  --soft_assumptions                      false
% 2.94/0.99  --soft_lemma_size                       3
% 2.94/0.99  --prop_impl_unit_size                   0
% 2.94/0.99  --prop_impl_unit                        []
% 2.94/0.99  --share_sel_clauses                     true
% 2.94/0.99  --reset_solvers                         false
% 2.94/0.99  --bc_imp_inh                            [conj_cone]
% 2.94/0.99  --conj_cone_tolerance                   3.
% 2.94/0.99  --extra_neg_conj                        none
% 2.94/0.99  --large_theory_mode                     true
% 2.94/0.99  --prolific_symb_bound                   200
% 2.94/0.99  --lt_threshold                          2000
% 2.94/0.99  --clause_weak_htbl                      true
% 2.94/0.99  --gc_record_bc_elim                     false
% 2.94/0.99  
% 2.94/0.99  ------ Preprocessing Options
% 2.94/0.99  
% 2.94/0.99  --preprocessing_flag                    true
% 2.94/0.99  --time_out_prep_mult                    0.1
% 2.94/0.99  --splitting_mode                        input
% 2.94/0.99  --splitting_grd                         true
% 2.94/0.99  --splitting_cvd                         false
% 2.94/0.99  --splitting_cvd_svl                     false
% 2.94/0.99  --splitting_nvd                         32
% 2.94/0.99  --sub_typing                            true
% 2.94/0.99  --prep_gs_sim                           true
% 2.94/0.99  --prep_unflatten                        true
% 2.94/0.99  --prep_res_sim                          true
% 2.94/0.99  --prep_upred                            true
% 2.94/0.99  --prep_sem_filter                       exhaustive
% 2.94/0.99  --prep_sem_filter_out                   false
% 2.94/0.99  --pred_elim                             true
% 2.94/0.99  --res_sim_input                         true
% 2.94/0.99  --eq_ax_congr_red                       true
% 2.94/0.99  --pure_diseq_elim                       true
% 2.94/0.99  --brand_transform                       false
% 2.94/0.99  --non_eq_to_eq                          false
% 2.94/0.99  --prep_def_merge                        true
% 2.94/0.99  --prep_def_merge_prop_impl              false
% 2.94/0.99  --prep_def_merge_mbd                    true
% 2.94/0.99  --prep_def_merge_tr_red                 false
% 2.94/0.99  --prep_def_merge_tr_cl                  false
% 2.94/0.99  --smt_preprocessing                     true
% 2.94/0.99  --smt_ac_axioms                         fast
% 2.94/0.99  --preprocessed_out                      false
% 2.94/0.99  --preprocessed_stats                    false
% 2.94/0.99  
% 2.94/0.99  ------ Abstraction refinement Options
% 2.94/0.99  
% 2.94/0.99  --abstr_ref                             []
% 2.94/0.99  --abstr_ref_prep                        false
% 2.94/0.99  --abstr_ref_until_sat                   false
% 2.94/0.99  --abstr_ref_sig_restrict                funpre
% 2.94/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.94/0.99  --abstr_ref_under                       []
% 2.94/0.99  
% 2.94/0.99  ------ SAT Options
% 2.94/0.99  
% 2.94/0.99  --sat_mode                              false
% 2.94/0.99  --sat_fm_restart_options                ""
% 2.94/0.99  --sat_gr_def                            false
% 2.94/0.99  --sat_epr_types                         true
% 2.94/0.99  --sat_non_cyclic_types                  false
% 2.94/0.99  --sat_finite_models                     false
% 2.94/0.99  --sat_fm_lemmas                         false
% 2.94/0.99  --sat_fm_prep                           false
% 2.94/0.99  --sat_fm_uc_incr                        true
% 2.94/0.99  --sat_out_model                         small
% 2.94/0.99  --sat_out_clauses                       false
% 2.94/0.99  
% 2.94/0.99  ------ QBF Options
% 2.94/0.99  
% 2.94/0.99  --qbf_mode                              false
% 2.94/0.99  --qbf_elim_univ                         false
% 2.94/0.99  --qbf_dom_inst                          none
% 2.94/0.99  --qbf_dom_pre_inst                      false
% 2.94/0.99  --qbf_sk_in                             false
% 2.94/0.99  --qbf_pred_elim                         true
% 2.94/0.99  --qbf_split                             512
% 2.94/0.99  
% 2.94/0.99  ------ BMC1 Options
% 2.94/0.99  
% 2.94/0.99  --bmc1_incremental                      false
% 2.94/0.99  --bmc1_axioms                           reachable_all
% 2.94/0.99  --bmc1_min_bound                        0
% 2.94/0.99  --bmc1_max_bound                        -1
% 2.94/0.99  --bmc1_max_bound_default                -1
% 2.94/0.99  --bmc1_symbol_reachability              true
% 2.94/0.99  --bmc1_property_lemmas                  false
% 2.94/0.99  --bmc1_k_induction                      false
% 2.94/0.99  --bmc1_non_equiv_states                 false
% 2.94/0.99  --bmc1_deadlock                         false
% 2.94/0.99  --bmc1_ucm                              false
% 2.94/0.99  --bmc1_add_unsat_core                   none
% 2.94/0.99  --bmc1_unsat_core_children              false
% 2.94/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.94/0.99  --bmc1_out_stat                         full
% 2.94/0.99  --bmc1_ground_init                      false
% 2.94/0.99  --bmc1_pre_inst_next_state              false
% 2.94/0.99  --bmc1_pre_inst_state                   false
% 2.94/0.99  --bmc1_pre_inst_reach_state             false
% 2.94/0.99  --bmc1_out_unsat_core                   false
% 2.94/0.99  --bmc1_aig_witness_out                  false
% 2.94/0.99  --bmc1_verbose                          false
% 2.94/0.99  --bmc1_dump_clauses_tptp                false
% 2.94/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.94/0.99  --bmc1_dump_file                        -
% 2.94/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.94/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.94/0.99  --bmc1_ucm_extend_mode                  1
% 2.94/0.99  --bmc1_ucm_init_mode                    2
% 2.94/0.99  --bmc1_ucm_cone_mode                    none
% 2.94/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.94/0.99  --bmc1_ucm_relax_model                  4
% 2.94/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.94/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.94/0.99  --bmc1_ucm_layered_model                none
% 2.94/0.99  --bmc1_ucm_max_lemma_size               10
% 2.94/0.99  
% 2.94/0.99  ------ AIG Options
% 2.94/0.99  
% 2.94/0.99  --aig_mode                              false
% 2.94/0.99  
% 2.94/0.99  ------ Instantiation Options
% 2.94/0.99  
% 2.94/0.99  --instantiation_flag                    true
% 2.94/0.99  --inst_sos_flag                         false
% 2.94/0.99  --inst_sos_phase                        true
% 2.94/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.94/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.94/0.99  --inst_lit_sel_side                     num_symb
% 2.94/0.99  --inst_solver_per_active                1400
% 2.94/0.99  --inst_solver_calls_frac                1.
% 2.94/0.99  --inst_passive_queue_type               priority_queues
% 2.94/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.94/0.99  --inst_passive_queues_freq              [25;2]
% 2.94/0.99  --inst_dismatching                      true
% 2.94/0.99  --inst_eager_unprocessed_to_passive     true
% 2.94/0.99  --inst_prop_sim_given                   true
% 2.94/0.99  --inst_prop_sim_new                     false
% 2.94/0.99  --inst_subs_new                         false
% 2.94/0.99  --inst_eq_res_simp                      false
% 2.94/0.99  --inst_subs_given                       false
% 2.94/0.99  --inst_orphan_elimination               true
% 2.94/0.99  --inst_learning_loop_flag               true
% 2.94/0.99  --inst_learning_start                   3000
% 2.94/0.99  --inst_learning_factor                  2
% 2.94/0.99  --inst_start_prop_sim_after_learn       3
% 2.94/0.99  --inst_sel_renew                        solver
% 2.94/0.99  --inst_lit_activity_flag                true
% 2.94/0.99  --inst_restr_to_given                   false
% 2.94/0.99  --inst_activity_threshold               500
% 2.94/0.99  --inst_out_proof                        true
% 2.94/0.99  
% 2.94/0.99  ------ Resolution Options
% 2.94/0.99  
% 2.94/0.99  --resolution_flag                       true
% 2.94/0.99  --res_lit_sel                           adaptive
% 2.94/0.99  --res_lit_sel_side                      none
% 2.94/0.99  --res_ordering                          kbo
% 2.94/0.99  --res_to_prop_solver                    active
% 2.94/0.99  --res_prop_simpl_new                    false
% 2.94/0.99  --res_prop_simpl_given                  true
% 2.94/0.99  --res_passive_queue_type                priority_queues
% 2.94/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.94/0.99  --res_passive_queues_freq               [15;5]
% 2.94/0.99  --res_forward_subs                      full
% 2.94/0.99  --res_backward_subs                     full
% 2.94/0.99  --res_forward_subs_resolution           true
% 2.94/0.99  --res_backward_subs_resolution          true
% 2.94/0.99  --res_orphan_elimination                true
% 2.94/0.99  --res_time_limit                        2.
% 2.94/0.99  --res_out_proof                         true
% 2.94/0.99  
% 2.94/0.99  ------ Superposition Options
% 2.94/0.99  
% 2.94/0.99  --superposition_flag                    true
% 2.94/0.99  --sup_passive_queue_type                priority_queues
% 2.94/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.94/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.94/0.99  --demod_completeness_check              fast
% 2.94/0.99  --demod_use_ground                      true
% 2.94/0.99  --sup_to_prop_solver                    passive
% 2.94/0.99  --sup_prop_simpl_new                    true
% 2.94/0.99  --sup_prop_simpl_given                  true
% 2.94/0.99  --sup_fun_splitting                     false
% 2.94/0.99  --sup_smt_interval                      50000
% 2.94/0.99  
% 2.94/0.99  ------ Superposition Simplification Setup
% 2.94/0.99  
% 2.94/0.99  --sup_indices_passive                   []
% 2.94/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.94/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/0.99  --sup_full_bw                           [BwDemod]
% 2.94/0.99  --sup_immed_triv                        [TrivRules]
% 2.94/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.94/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/0.99  --sup_immed_bw_main                     []
% 2.94/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.94/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.94/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.94/0.99  
% 2.94/0.99  ------ Combination Options
% 2.94/0.99  
% 2.94/0.99  --comb_res_mult                         3
% 2.94/0.99  --comb_sup_mult                         2
% 2.94/0.99  --comb_inst_mult                        10
% 2.94/0.99  
% 2.94/0.99  ------ Debug Options
% 2.94/0.99  
% 2.94/0.99  --dbg_backtrace                         false
% 2.94/0.99  --dbg_dump_prop_clauses                 false
% 2.94/0.99  --dbg_dump_prop_clauses_file            -
% 2.94/0.99  --dbg_out_stat                          false
% 2.94/0.99  ------ Parsing...
% 2.94/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.94/0.99  
% 2.94/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.94/0.99  
% 2.94/0.99  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.94/0.99  
% 2.94/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.94/0.99  ------ Proving...
% 2.94/0.99  ------ Problem Properties 
% 2.94/0.99  
% 2.94/0.99  
% 2.94/0.99  clauses                                 18
% 2.94/0.99  conjectures                             3
% 2.94/0.99  EPR                                     3
% 2.94/0.99  Horn                                    13
% 2.94/0.99  unary                                   2
% 2.94/0.99  binary                                  10
% 2.94/0.99  lits                                    41
% 2.94/0.99  lits eq                                 19
% 2.94/0.99  fd_pure                                 0
% 2.94/0.99  fd_pseudo                               0
% 2.94/0.99  fd_cond                                 0
% 2.94/0.99  fd_pseudo_cond                          2
% 2.94/0.99  AC symbols                              0
% 2.94/0.99  
% 2.94/0.99  ------ Schedule dynamic 5 is on 
% 2.94/0.99  
% 2.94/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.94/0.99  
% 2.94/0.99  
% 2.94/0.99  ------ 
% 2.94/0.99  Current options:
% 2.94/0.99  ------ 
% 2.94/0.99  
% 2.94/0.99  ------ Input Options
% 2.94/0.99  
% 2.94/0.99  --out_options                           all
% 2.94/0.99  --tptp_safe_out                         true
% 2.94/0.99  --problem_path                          ""
% 2.94/0.99  --include_path                          ""
% 2.94/0.99  --clausifier                            res/vclausify_rel
% 2.94/0.99  --clausifier_options                    --mode clausify
% 2.94/0.99  --stdin                                 false
% 2.94/0.99  --stats_out                             all
% 2.94/0.99  
% 2.94/0.99  ------ General Options
% 2.94/0.99  
% 2.94/0.99  --fof                                   false
% 2.94/0.99  --time_out_real                         305.
% 2.94/0.99  --time_out_virtual                      -1.
% 2.94/0.99  --symbol_type_check                     false
% 2.94/0.99  --clausify_out                          false
% 2.94/0.99  --sig_cnt_out                           false
% 2.94/0.99  --trig_cnt_out                          false
% 2.94/0.99  --trig_cnt_out_tolerance                1.
% 2.94/0.99  --trig_cnt_out_sk_spl                   false
% 2.94/0.99  --abstr_cl_out                          false
% 2.94/0.99  
% 2.94/0.99  ------ Global Options
% 2.94/0.99  
% 2.94/0.99  --schedule                              default
% 2.94/0.99  --add_important_lit                     false
% 2.94/0.99  --prop_solver_per_cl                    1000
% 2.94/0.99  --min_unsat_core                        false
% 2.94/0.99  --soft_assumptions                      false
% 2.94/0.99  --soft_lemma_size                       3
% 2.94/0.99  --prop_impl_unit_size                   0
% 2.94/0.99  --prop_impl_unit                        []
% 2.94/0.99  --share_sel_clauses                     true
% 2.94/0.99  --reset_solvers                         false
% 2.94/0.99  --bc_imp_inh                            [conj_cone]
% 2.94/0.99  --conj_cone_tolerance                   3.
% 2.94/0.99  --extra_neg_conj                        none
% 2.94/0.99  --large_theory_mode                     true
% 2.94/0.99  --prolific_symb_bound                   200
% 2.94/0.99  --lt_threshold                          2000
% 2.94/0.99  --clause_weak_htbl                      true
% 2.94/0.99  --gc_record_bc_elim                     false
% 2.94/0.99  
% 2.94/0.99  ------ Preprocessing Options
% 2.94/0.99  
% 2.94/0.99  --preprocessing_flag                    true
% 2.94/0.99  --time_out_prep_mult                    0.1
% 2.94/0.99  --splitting_mode                        input
% 2.94/0.99  --splitting_grd                         true
% 2.94/0.99  --splitting_cvd                         false
% 2.94/0.99  --splitting_cvd_svl                     false
% 2.94/0.99  --splitting_nvd                         32
% 2.94/0.99  --sub_typing                            true
% 2.94/0.99  --prep_gs_sim                           true
% 2.94/0.99  --prep_unflatten                        true
% 2.94/0.99  --prep_res_sim                          true
% 2.94/0.99  --prep_upred                            true
% 2.94/0.99  --prep_sem_filter                       exhaustive
% 2.94/0.99  --prep_sem_filter_out                   false
% 2.94/0.99  --pred_elim                             true
% 2.94/0.99  --res_sim_input                         true
% 2.94/0.99  --eq_ax_congr_red                       true
% 2.94/0.99  --pure_diseq_elim                       true
% 2.94/0.99  --brand_transform                       false
% 2.94/0.99  --non_eq_to_eq                          false
% 2.94/0.99  --prep_def_merge                        true
% 2.94/0.99  --prep_def_merge_prop_impl              false
% 2.94/0.99  --prep_def_merge_mbd                    true
% 2.94/0.99  --prep_def_merge_tr_red                 false
% 2.94/0.99  --prep_def_merge_tr_cl                  false
% 2.94/0.99  --smt_preprocessing                     true
% 2.94/0.99  --smt_ac_axioms                         fast
% 2.94/0.99  --preprocessed_out                      false
% 2.94/0.99  --preprocessed_stats                    false
% 2.94/0.99  
% 2.94/0.99  ------ Abstraction refinement Options
% 2.94/0.99  
% 2.94/0.99  --abstr_ref                             []
% 2.94/0.99  --abstr_ref_prep                        false
% 2.94/0.99  --abstr_ref_until_sat                   false
% 2.94/0.99  --abstr_ref_sig_restrict                funpre
% 2.94/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.94/0.99  --abstr_ref_under                       []
% 2.94/0.99  
% 2.94/0.99  ------ SAT Options
% 2.94/0.99  
% 2.94/0.99  --sat_mode                              false
% 2.94/0.99  --sat_fm_restart_options                ""
% 2.94/0.99  --sat_gr_def                            false
% 2.94/0.99  --sat_epr_types                         true
% 2.94/0.99  --sat_non_cyclic_types                  false
% 2.94/0.99  --sat_finite_models                     false
% 2.94/0.99  --sat_fm_lemmas                         false
% 2.94/0.99  --sat_fm_prep                           false
% 2.94/0.99  --sat_fm_uc_incr                        true
% 2.94/0.99  --sat_out_model                         small
% 2.94/0.99  --sat_out_clauses                       false
% 2.94/0.99  
% 2.94/0.99  ------ QBF Options
% 2.94/0.99  
% 2.94/0.99  --qbf_mode                              false
% 2.94/0.99  --qbf_elim_univ                         false
% 2.94/0.99  --qbf_dom_inst                          none
% 2.94/0.99  --qbf_dom_pre_inst                      false
% 2.94/0.99  --qbf_sk_in                             false
% 2.94/0.99  --qbf_pred_elim                         true
% 2.94/0.99  --qbf_split                             512
% 2.94/0.99  
% 2.94/0.99  ------ BMC1 Options
% 2.94/0.99  
% 2.94/0.99  --bmc1_incremental                      false
% 2.94/0.99  --bmc1_axioms                           reachable_all
% 2.94/0.99  --bmc1_min_bound                        0
% 2.94/0.99  --bmc1_max_bound                        -1
% 2.94/0.99  --bmc1_max_bound_default                -1
% 2.94/0.99  --bmc1_symbol_reachability              true
% 2.94/0.99  --bmc1_property_lemmas                  false
% 2.94/0.99  --bmc1_k_induction                      false
% 2.94/0.99  --bmc1_non_equiv_states                 false
% 2.94/0.99  --bmc1_deadlock                         false
% 2.94/0.99  --bmc1_ucm                              false
% 2.94/0.99  --bmc1_add_unsat_core                   none
% 2.94/0.99  --bmc1_unsat_core_children              false
% 2.94/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.94/0.99  --bmc1_out_stat                         full
% 2.94/0.99  --bmc1_ground_init                      false
% 2.94/0.99  --bmc1_pre_inst_next_state              false
% 2.94/0.99  --bmc1_pre_inst_state                   false
% 2.94/0.99  --bmc1_pre_inst_reach_state             false
% 2.94/0.99  --bmc1_out_unsat_core                   false
% 2.94/0.99  --bmc1_aig_witness_out                  false
% 2.94/0.99  --bmc1_verbose                          false
% 2.94/0.99  --bmc1_dump_clauses_tptp                false
% 2.94/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.94/0.99  --bmc1_dump_file                        -
% 2.94/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.94/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.94/0.99  --bmc1_ucm_extend_mode                  1
% 2.94/0.99  --bmc1_ucm_init_mode                    2
% 2.94/0.99  --bmc1_ucm_cone_mode                    none
% 2.94/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.94/0.99  --bmc1_ucm_relax_model                  4
% 2.94/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.94/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.94/0.99  --bmc1_ucm_layered_model                none
% 2.94/0.99  --bmc1_ucm_max_lemma_size               10
% 2.94/0.99  
% 2.94/0.99  ------ AIG Options
% 2.94/0.99  
% 2.94/0.99  --aig_mode                              false
% 2.94/0.99  
% 2.94/0.99  ------ Instantiation Options
% 2.94/0.99  
% 2.94/0.99  --instantiation_flag                    true
% 2.94/0.99  --inst_sos_flag                         false
% 2.94/0.99  --inst_sos_phase                        true
% 2.94/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.94/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.94/0.99  --inst_lit_sel_side                     none
% 2.94/0.99  --inst_solver_per_active                1400
% 2.94/0.99  --inst_solver_calls_frac                1.
% 2.94/0.99  --inst_passive_queue_type               priority_queues
% 2.94/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.94/0.99  --inst_passive_queues_freq              [25;2]
% 2.94/0.99  --inst_dismatching                      true
% 2.94/0.99  --inst_eager_unprocessed_to_passive     true
% 2.94/0.99  --inst_prop_sim_given                   true
% 2.94/0.99  --inst_prop_sim_new                     false
% 2.94/0.99  --inst_subs_new                         false
% 2.94/0.99  --inst_eq_res_simp                      false
% 2.94/0.99  --inst_subs_given                       false
% 2.94/0.99  --inst_orphan_elimination               true
% 2.94/0.99  --inst_learning_loop_flag               true
% 2.94/0.99  --inst_learning_start                   3000
% 2.94/0.99  --inst_learning_factor                  2
% 2.94/0.99  --inst_start_prop_sim_after_learn       3
% 2.94/0.99  --inst_sel_renew                        solver
% 2.94/0.99  --inst_lit_activity_flag                true
% 2.94/0.99  --inst_restr_to_given                   false
% 2.94/0.99  --inst_activity_threshold               500
% 2.94/0.99  --inst_out_proof                        true
% 2.94/0.99  
% 2.94/0.99  ------ Resolution Options
% 2.94/0.99  
% 2.94/0.99  --resolution_flag                       false
% 2.94/0.99  --res_lit_sel                           adaptive
% 2.94/0.99  --res_lit_sel_side                      none
% 2.94/0.99  --res_ordering                          kbo
% 2.94/0.99  --res_to_prop_solver                    active
% 2.94/0.99  --res_prop_simpl_new                    false
% 2.94/0.99  --res_prop_simpl_given                  true
% 2.94/0.99  --res_passive_queue_type                priority_queues
% 2.94/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.94/0.99  --res_passive_queues_freq               [15;5]
% 2.94/0.99  --res_forward_subs                      full
% 2.94/0.99  --res_backward_subs                     full
% 2.94/0.99  --res_forward_subs_resolution           true
% 2.94/0.99  --res_backward_subs_resolution          true
% 2.94/0.99  --res_orphan_elimination                true
% 2.94/0.99  --res_time_limit                        2.
% 2.94/0.99  --res_out_proof                         true
% 2.94/0.99  
% 2.94/0.99  ------ Superposition Options
% 2.94/0.99  
% 2.94/0.99  --superposition_flag                    true
% 2.94/0.99  --sup_passive_queue_type                priority_queues
% 2.94/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.94/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.94/0.99  --demod_completeness_check              fast
% 2.94/0.99  --demod_use_ground                      true
% 2.94/0.99  --sup_to_prop_solver                    passive
% 2.94/0.99  --sup_prop_simpl_new                    true
% 2.94/0.99  --sup_prop_simpl_given                  true
% 2.94/0.99  --sup_fun_splitting                     false
% 2.94/0.99  --sup_smt_interval                      50000
% 2.94/0.99  
% 2.94/0.99  ------ Superposition Simplification Setup
% 2.94/0.99  
% 2.94/0.99  --sup_indices_passive                   []
% 2.94/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.94/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/0.99  --sup_full_bw                           [BwDemod]
% 2.94/0.99  --sup_immed_triv                        [TrivRules]
% 2.94/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.94/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/0.99  --sup_immed_bw_main                     []
% 2.94/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.94/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.94/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.94/0.99  
% 2.94/0.99  ------ Combination Options
% 2.94/0.99  
% 2.94/0.99  --comb_res_mult                         3
% 2.94/0.99  --comb_sup_mult                         2
% 2.94/0.99  --comb_inst_mult                        10
% 2.94/0.99  
% 2.94/0.99  ------ Debug Options
% 2.94/0.99  
% 2.94/0.99  --dbg_backtrace                         false
% 2.94/0.99  --dbg_dump_prop_clauses                 false
% 2.94/0.99  --dbg_dump_prop_clauses_file            -
% 2.94/0.99  --dbg_out_stat                          false
% 2.94/0.99  
% 2.94/0.99  
% 2.94/0.99  
% 2.94/0.99  
% 2.94/0.99  ------ Proving...
% 2.94/0.99  
% 2.94/0.99  
% 2.94/0.99  % SZS status Theorem for theBenchmark.p
% 2.94/0.99  
% 2.94/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.94/0.99  
% 2.94/0.99  fof(f12,conjecture,(
% 2.94/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 2.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f13,negated_conjecture,(
% 2.94/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 2.94/0.99    inference(negated_conjecture,[],[f12])).
% 2.94/0.99  
% 2.94/0.99  fof(f28,plain,(
% 2.94/0.99    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.94/0.99    inference(ennf_transformation,[],[f13])).
% 2.94/0.99  
% 2.94/0.99  fof(f29,plain,(
% 2.94/0.99    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.94/0.99    inference(flattening,[],[f28])).
% 2.94/0.99  
% 2.94/0.99  fof(f40,plain,(
% 2.94/0.99    ( ! [X2,X0] : (! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) => (k1_funct_1(X2,sK5(X3)) = X3 & r2_hidden(sK5(X3),X0)))) )),
% 2.94/0.99    introduced(choice_axiom,[])).
% 2.94/0.99  
% 2.94/0.99  fof(f39,plain,(
% 2.94/0.99    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (k2_relset_1(sK2,sK3,sK4) != sK3 & ! [X3] : (? [X4] : (k1_funct_1(sK4,X4) = X3 & r2_hidden(X4,sK2)) | ~r2_hidden(X3,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 2.94/0.99    introduced(choice_axiom,[])).
% 2.94/0.99  
% 2.94/0.99  fof(f41,plain,(
% 2.94/0.99    k2_relset_1(sK2,sK3,sK4) != sK3 & ! [X3] : ((k1_funct_1(sK4,sK5(X3)) = X3 & r2_hidden(sK5(X3),sK2)) | ~r2_hidden(X3,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 2.94/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f29,f40,f39])).
% 2.94/0.99  
% 2.94/0.99  fof(f63,plain,(
% 2.94/0.99    v1_funct_2(sK4,sK2,sK3)),
% 2.94/0.99    inference(cnf_transformation,[],[f41])).
% 2.94/0.99  
% 2.94/0.99  fof(f11,axiom,(
% 2.94/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f26,plain,(
% 2.94/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.94/0.99    inference(ennf_transformation,[],[f11])).
% 2.94/0.99  
% 2.94/0.99  fof(f27,plain,(
% 2.94/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.94/0.99    inference(flattening,[],[f26])).
% 2.94/0.99  
% 2.94/0.99  fof(f38,plain,(
% 2.94/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.94/0.99    inference(nnf_transformation,[],[f27])).
% 2.94/0.99  
% 2.94/0.99  fof(f56,plain,(
% 2.94/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.94/0.99    inference(cnf_transformation,[],[f38])).
% 2.94/0.99  
% 2.94/0.99  fof(f64,plain,(
% 2.94/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.94/0.99    inference(cnf_transformation,[],[f41])).
% 2.94/0.99  
% 2.94/0.99  fof(f9,axiom,(
% 2.94/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f24,plain,(
% 2.94/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.94/0.99    inference(ennf_transformation,[],[f9])).
% 2.94/0.99  
% 2.94/0.99  fof(f54,plain,(
% 2.94/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.94/0.99    inference(cnf_transformation,[],[f24])).
% 2.94/0.99  
% 2.94/0.99  fof(f7,axiom,(
% 2.94/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f22,plain,(
% 2.94/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.94/0.99    inference(ennf_transformation,[],[f7])).
% 2.94/0.99  
% 2.94/0.99  fof(f52,plain,(
% 2.94/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.94/0.99    inference(cnf_transformation,[],[f22])).
% 2.94/0.99  
% 2.94/0.99  fof(f6,axiom,(
% 2.94/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 2.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f20,plain,(
% 2.94/0.99    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.94/0.99    inference(ennf_transformation,[],[f6])).
% 2.94/0.99  
% 2.94/0.99  fof(f21,plain,(
% 2.94/0.99    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.94/0.99    inference(flattening,[],[f20])).
% 2.94/0.99  
% 2.94/0.99  fof(f51,plain,(
% 2.94/0.99    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.94/0.99    inference(cnf_transformation,[],[f21])).
% 2.94/0.99  
% 2.94/0.99  fof(f62,plain,(
% 2.94/0.99    v1_funct_1(sK4)),
% 2.94/0.99    inference(cnf_transformation,[],[f41])).
% 2.94/0.99  
% 2.94/0.99  fof(f5,axiom,(
% 2.94/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f19,plain,(
% 2.94/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.94/0.99    inference(ennf_transformation,[],[f5])).
% 2.94/0.99  
% 2.94/0.99  fof(f37,plain,(
% 2.94/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.94/0.99    inference(nnf_transformation,[],[f19])).
% 2.94/0.99  
% 2.94/0.99  fof(f49,plain,(
% 2.94/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.94/0.99    inference(cnf_transformation,[],[f37])).
% 2.94/0.99  
% 2.94/0.99  fof(f8,axiom,(
% 2.94/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f15,plain,(
% 2.94/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.94/0.99    inference(pure_predicate_removal,[],[f8])).
% 2.94/0.99  
% 2.94/0.99  fof(f23,plain,(
% 2.94/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.94/0.99    inference(ennf_transformation,[],[f15])).
% 2.94/0.99  
% 2.94/0.99  fof(f53,plain,(
% 2.94/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.94/0.99    inference(cnf_transformation,[],[f23])).
% 2.94/0.99  
% 2.94/0.99  fof(f2,axiom,(
% 2.94/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f17,plain,(
% 2.94/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.94/0.99    inference(ennf_transformation,[],[f2])).
% 2.94/0.99  
% 2.94/0.99  fof(f30,plain,(
% 2.94/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.94/0.99    inference(nnf_transformation,[],[f17])).
% 2.94/0.99  
% 2.94/0.99  fof(f31,plain,(
% 2.94/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.94/0.99    inference(rectify,[],[f30])).
% 2.94/0.99  
% 2.94/0.99  fof(f32,plain,(
% 2.94/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.94/0.99    introduced(choice_axiom,[])).
% 2.94/0.99  
% 2.94/0.99  fof(f33,plain,(
% 2.94/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.94/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 2.94/0.99  
% 2.94/0.99  fof(f43,plain,(
% 2.94/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.94/0.99    inference(cnf_transformation,[],[f33])).
% 2.94/0.99  
% 2.94/0.99  fof(f66,plain,(
% 2.94/0.99    ( ! [X3] : (k1_funct_1(sK4,sK5(X3)) = X3 | ~r2_hidden(X3,sK3)) )),
% 2.94/0.99    inference(cnf_transformation,[],[f41])).
% 2.94/0.99  
% 2.94/0.99  fof(f10,axiom,(
% 2.94/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f25,plain,(
% 2.94/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.94/0.99    inference(ennf_transformation,[],[f10])).
% 2.94/0.99  
% 2.94/0.99  fof(f55,plain,(
% 2.94/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.94/0.99    inference(cnf_transformation,[],[f25])).
% 2.94/0.99  
% 2.94/0.99  fof(f67,plain,(
% 2.94/0.99    k2_relset_1(sK2,sK3,sK4) != sK3),
% 2.94/0.99    inference(cnf_transformation,[],[f41])).
% 2.94/0.99  
% 2.94/0.99  fof(f65,plain,(
% 2.94/0.99    ( ! [X3] : (r2_hidden(sK5(X3),sK2) | ~r2_hidden(X3,sK3)) )),
% 2.94/0.99    inference(cnf_transformation,[],[f41])).
% 2.94/0.99  
% 2.94/0.99  fof(f4,axiom,(
% 2.94/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 2.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f18,plain,(
% 2.94/0.99    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 2.94/0.99    inference(ennf_transformation,[],[f4])).
% 2.94/0.99  
% 2.94/0.99  fof(f34,plain,(
% 2.94/0.99    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 2.94/0.99    inference(nnf_transformation,[],[f18])).
% 2.94/0.99  
% 2.94/0.99  fof(f35,plain,(
% 2.94/0.99    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 2.94/0.99    introduced(choice_axiom,[])).
% 2.94/0.99  
% 2.94/0.99  fof(f36,plain,(
% 2.94/0.99    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 2.94/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).
% 2.94/0.99  
% 2.94/0.99  fof(f47,plain,(
% 2.94/0.99    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 2.94/0.99    inference(cnf_transformation,[],[f36])).
% 2.94/0.99  
% 2.94/0.99  fof(f48,plain,(
% 2.94/0.99    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) )),
% 2.94/0.99    inference(cnf_transformation,[],[f36])).
% 2.94/0.99  
% 2.94/0.99  fof(f1,axiom,(
% 2.94/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f14,plain,(
% 2.94/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 2.94/0.99    inference(unused_predicate_definition_removal,[],[f1])).
% 2.94/0.99  
% 2.94/0.99  fof(f16,plain,(
% 2.94/0.99    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 2.94/0.99    inference(ennf_transformation,[],[f14])).
% 2.94/0.99  
% 2.94/0.99  fof(f42,plain,(
% 2.94/0.99    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 2.94/0.99    inference(cnf_transformation,[],[f16])).
% 2.94/0.99  
% 2.94/0.99  fof(f3,axiom,(
% 2.94/0.99    v1_xboole_0(k1_xboole_0)),
% 2.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f46,plain,(
% 2.94/0.99    v1_xboole_0(k1_xboole_0)),
% 2.94/0.99    inference(cnf_transformation,[],[f3])).
% 2.94/0.99  
% 2.94/0.99  cnf(c_24,negated_conjecture,
% 2.94/0.99      ( v1_funct_2(sK4,sK2,sK3) ),
% 2.94/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_19,plain,
% 2.94/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.94/0.99      | k1_xboole_0 = X2 ),
% 2.94/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_23,negated_conjecture,
% 2.94/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.94/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_420,plain,
% 2.94/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.94/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.94/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.94/0.99      | sK4 != X0
% 2.94/0.99      | k1_xboole_0 = X2 ),
% 2.94/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_23]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_421,plain,
% 2.94/0.99      ( ~ v1_funct_2(sK4,X0,X1)
% 2.94/0.99      | k1_relset_1(X0,X1,sK4) = X0
% 2.94/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.94/0.99      | k1_xboole_0 = X1 ),
% 2.94/0.99      inference(unflattening,[status(thm)],[c_420]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_652,plain,
% 2.94/0.99      ( k1_relset_1(X0,X1,sK4) = X0
% 2.94/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.94/0.99      | sK4 != sK4
% 2.94/0.99      | sK3 != X1
% 2.94/0.99      | sK2 != X0
% 2.94/0.99      | k1_xboole_0 = X1 ),
% 2.94/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_421]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_653,plain,
% 2.94/0.99      ( k1_relset_1(sK2,sK3,sK4) = sK2
% 2.94/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.94/0.99      | k1_xboole_0 = sK3 ),
% 2.94/0.99      inference(unflattening,[status(thm)],[c_652]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_716,plain,
% 2.94/0.99      ( k1_relset_1(sK2,sK3,sK4) = sK2 | k1_xboole_0 = sK3 ),
% 2.94/0.99      inference(equality_resolution_simp,[status(thm)],[c_653]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_12,plain,
% 2.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.94/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_465,plain,
% 2.94/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.94/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.94/0.99      | sK4 != X2 ),
% 2.94/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_23]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_466,plain,
% 2.94/0.99      ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
% 2.94/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 2.94/0.99      inference(unflattening,[status(thm)],[c_465]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1248,plain,
% 2.94/0.99      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 2.94/0.99      inference(equality_resolution,[status(thm)],[c_466]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1501,plain,
% 2.94/0.99      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_716,c_1248]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_10,plain,
% 2.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/0.99      | v1_relat_1(X0) ),
% 2.94/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_9,plain,
% 2.94/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.94/0.99      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 2.94/0.99      | ~ v1_funct_1(X1)
% 2.94/0.99      | ~ v1_relat_1(X1) ),
% 2.94/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_25,negated_conjecture,
% 2.94/0.99      ( v1_funct_1(sK4) ),
% 2.94/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_300,plain,
% 2.94/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.94/0.99      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 2.94/0.99      | ~ v1_relat_1(X1)
% 2.94/0.99      | sK4 != X1 ),
% 2.94/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_25]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_301,plain,
% 2.94/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 2.94/0.99      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
% 2.94/0.99      | ~ v1_relat_1(sK4) ),
% 2.94/0.99      inference(unflattening,[status(thm)],[c_300]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_341,plain,
% 2.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/0.99      | ~ r2_hidden(X3,k1_relat_1(sK4))
% 2.94/0.99      | r2_hidden(k1_funct_1(sK4,X3),k2_relat_1(sK4))
% 2.94/0.99      | sK4 != X0 ),
% 2.94/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_301]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_342,plain,
% 2.94/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.94/0.99      | ~ r2_hidden(X2,k1_relat_1(sK4))
% 2.94/0.99      | r2_hidden(k1_funct_1(sK4,X2),k2_relat_1(sK4)) ),
% 2.94/0.99      inference(unflattening,[status(thm)],[c_341]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_539,plain,
% 2.94/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 2.94/0.99      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
% 2.94/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.94/0.99      | sK4 != sK4 ),
% 2.94/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_342]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_717,plain,
% 2.94/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 2.94/0.99      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
% 2.94/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 2.94/0.99      inference(equality_resolution_simp,[status(thm)],[c_539]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_834,plain,
% 2.94/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 2.94/0.99      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
% 2.94/0.99      | ~ sP1_iProver_split ),
% 2.94/0.99      inference(splitting,
% 2.94/0.99                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.94/0.99                [c_717]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1072,plain,
% 2.94/0.99      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.94/0.99      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top
% 2.94/0.99      | sP1_iProver_split != iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_834]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_835,plain,
% 2.94/0.99      ( sP1_iProver_split | sP0_iProver_split ),
% 2.94/0.99      inference(splitting,
% 2.94/0.99                [splitting(split),new_symbols(definition,[])],
% 2.94/0.99                [c_717]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_859,plain,
% 2.94/0.99      ( sP1_iProver_split = iProver_top
% 2.94/0.99      | sP0_iProver_split = iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_835]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_860,plain,
% 2.94/0.99      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.94/0.99      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top
% 2.94/0.99      | sP1_iProver_split != iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_834]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_833,plain,
% 2.94/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.94/0.99      | ~ sP0_iProver_split ),
% 2.94/0.99      inference(splitting,
% 2.94/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.94/0.99                [c_717]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1073,plain,
% 2.94/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.94/0.99      | sP0_iProver_split != iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_833]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1693,plain,
% 2.94/0.99      ( sP0_iProver_split != iProver_top ),
% 2.94/0.99      inference(equality_resolution,[status(thm)],[c_1073]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1729,plain,
% 2.94/0.99      ( r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top
% 2.94/0.99      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 2.94/0.99      inference(global_propositional_subsumption,
% 2.94/0.99                [status(thm)],
% 2.94/0.99                [c_1072,c_859,c_860,c_1693]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1730,plain,
% 2.94/0.99      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.94/0.99      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top ),
% 2.94/0.99      inference(renaming,[status(thm)],[c_1729]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_8,plain,
% 2.94/0.99      ( ~ v5_relat_1(X0,X1)
% 2.94/0.99      | r1_tarski(k2_relat_1(X0),X1)
% 2.94/0.99      | ~ v1_relat_1(X0) ),
% 2.94/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_11,plain,
% 2.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/0.99      | v5_relat_1(X0,X2) ),
% 2.94/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_320,plain,
% 2.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/0.99      | r1_tarski(k2_relat_1(X3),X4)
% 2.94/0.99      | ~ v1_relat_1(X3)
% 2.94/0.99      | X0 != X3
% 2.94/0.99      | X2 != X4 ),
% 2.94/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_11]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_321,plain,
% 2.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/0.99      | r1_tarski(k2_relat_1(X0),X2)
% 2.94/0.99      | ~ v1_relat_1(X0) ),
% 2.94/0.99      inference(unflattening,[status(thm)],[c_320]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_325,plain,
% 2.94/0.99      ( r1_tarski(k2_relat_1(X0),X2)
% 2.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.94/0.99      inference(global_propositional_subsumption,
% 2.94/0.99                [status(thm)],
% 2.94/0.99                [c_321,c_10]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_326,plain,
% 2.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/0.99      | r1_tarski(k2_relat_1(X0),X2) ),
% 2.94/0.99      inference(renaming,[status(thm)],[c_325]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_408,plain,
% 2.94/0.99      ( r1_tarski(k2_relat_1(X0),X1)
% 2.94/0.99      | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.94/0.99      | sK4 != X0 ),
% 2.94/0.99      inference(resolution_lifted,[status(thm)],[c_326,c_23]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_409,plain,
% 2.94/0.99      ( r1_tarski(k2_relat_1(sK4),X0)
% 2.94/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 2.94/0.99      inference(unflattening,[status(thm)],[c_408]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1074,plain,
% 2.94/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.94/0.99      | r1_tarski(k2_relat_1(sK4),X1) = iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_409]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1536,plain,
% 2.94/0.99      ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
% 2.94/0.99      inference(equality_resolution,[status(thm)],[c_1074]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3,plain,
% 2.94/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 2.94/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1080,plain,
% 2.94/0.99      ( r1_tarski(X0,X1) != iProver_top
% 2.94/0.99      | r2_hidden(X2,X0) != iProver_top
% 2.94/0.99      | r2_hidden(X2,X1) = iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1741,plain,
% 2.94/0.99      ( r2_hidden(X0,k2_relat_1(sK4)) != iProver_top
% 2.94/0.99      | r2_hidden(X0,sK3) = iProver_top ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_1536,c_1080]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1998,plain,
% 2.94/0.99      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.94/0.99      | r2_hidden(k1_funct_1(sK4,X0),sK3) = iProver_top ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_1730,c_1741]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_21,negated_conjecture,
% 2.94/0.99      ( ~ r2_hidden(X0,sK3) | k1_funct_1(sK4,sK5(X0)) = X0 ),
% 2.94/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1077,plain,
% 2.94/0.99      ( k1_funct_1(sK4,sK5(X0)) = X0 | r2_hidden(X0,sK3) != iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2844,plain,
% 2.94/0.99      ( k1_funct_1(sK4,sK5(k1_funct_1(sK4,X0))) = k1_funct_1(sK4,X0)
% 2.94/0.99      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_1998,c_1077]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2896,plain,
% 2.94/0.99      ( k1_funct_1(sK4,sK5(k1_funct_1(sK4,X0))) = k1_funct_1(sK4,X0)
% 2.94/0.99      | sK3 = k1_xboole_0
% 2.94/0.99      | r2_hidden(X0,sK2) != iProver_top ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_1501,c_2844]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_13,plain,
% 2.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.94/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_456,plain,
% 2.94/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.94/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 2.94/0.99      | sK4 != X2 ),
% 2.94/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_23]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_457,plain,
% 2.94/0.99      ( k2_relset_1(X0,X1,sK4) = k2_relat_1(sK4)
% 2.94/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 2.94/0.99      inference(unflattening,[status(thm)],[c_456]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1208,plain,
% 2.94/0.99      ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 2.94/0.99      inference(equality_resolution,[status(thm)],[c_457]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_20,negated_conjecture,
% 2.94/0.99      ( k2_relset_1(sK2,sK3,sK4) != sK3 ),
% 2.94/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1290,plain,
% 2.94/0.99      ( k2_relat_1(sK4) != sK3 ),
% 2.94/0.99      inference(demodulation,[status(thm)],[c_1208,c_20]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_22,negated_conjecture,
% 2.94/0.99      ( ~ r2_hidden(X0,sK3) | r2_hidden(sK5(X0),sK2) ),
% 2.94/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2798,plain,
% 2.94/0.99      ( ~ r2_hidden(sK1(sK3,k2_relat_1(sK4)),sK3)
% 2.94/0.99      | r2_hidden(sK5(sK1(sK3,k2_relat_1(sK4))),sK2) ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_22]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2799,plain,
% 2.94/0.99      ( r2_hidden(sK1(sK3,k2_relat_1(sK4)),sK3) != iProver_top
% 2.94/0.99      | r2_hidden(sK5(sK1(sK3,k2_relat_1(sK4))),sK2) = iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_2798]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_6,plain,
% 2.94/0.99      ( r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0) | X0 = X1 ),
% 2.94/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1078,plain,
% 2.94/0.99      ( X0 = X1
% 2.94/0.99      | r2_hidden(sK1(X0,X1),X1) = iProver_top
% 2.94/0.99      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1478,plain,
% 2.94/0.99      ( k1_funct_1(sK4,sK5(sK1(sK3,X0))) = sK1(sK3,X0)
% 2.94/0.99      | sK3 = X0
% 2.94/0.99      | r2_hidden(sK1(sK3,X0),X0) = iProver_top ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_1078,c_1077]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1999,plain,
% 2.94/0.99      ( k1_funct_1(sK4,sK5(sK1(sK3,k2_relat_1(sK4)))) = sK1(sK3,k2_relat_1(sK4))
% 2.94/0.99      | k2_relat_1(sK4) = sK3
% 2.94/0.99      | r2_hidden(sK1(sK3,k2_relat_1(sK4)),sK3) = iProver_top ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_1478,c_1741]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2048,plain,
% 2.94/0.99      ( k1_funct_1(sK4,sK5(sK1(sK3,k2_relat_1(sK4)))) = sK1(sK3,k2_relat_1(sK4))
% 2.94/0.99      | r2_hidden(sK1(sK3,k2_relat_1(sK4)),sK3) = iProver_top ),
% 2.94/0.99      inference(global_propositional_subsumption,
% 2.94/0.99                [status(thm)],
% 2.94/0.99                [c_1999,c_1290]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2054,plain,
% 2.94/0.99      ( k1_funct_1(sK4,sK5(sK1(sK3,k2_relat_1(sK4)))) = sK1(sK3,k2_relat_1(sK4)) ),
% 2.94/0.99      inference(forward_subsumption_resolution,
% 2.94/0.99                [status(thm)],
% 2.94/0.99                [c_2048,c_1077]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2842,plain,
% 2.94/0.99      ( r2_hidden(sK1(sK3,k2_relat_1(sK4)),sK3) = iProver_top
% 2.94/0.99      | r2_hidden(sK5(sK1(sK3,k2_relat_1(sK4))),k1_relat_1(sK4)) != iProver_top ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_2054,c_1998]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_838,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1209,plain,
% 2.94/0.99      ( k2_relset_1(sK2,sK3,sK4) != X0
% 2.94/0.99      | k2_relset_1(sK2,sK3,sK4) = sK3
% 2.94/0.99      | sK3 != X0 ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_838]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1280,plain,
% 2.94/0.99      ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
% 2.94/0.99      | k2_relset_1(sK2,sK3,sK4) = sK3
% 2.94/0.99      | sK3 != k2_relat_1(sK4) ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_1209]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_5,plain,
% 2.94/0.99      ( ~ r2_hidden(sK1(X0,X1),X1)
% 2.94/0.99      | ~ r2_hidden(sK1(X0,X1),X0)
% 2.94/0.99      | X0 = X1 ),
% 2.94/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1325,plain,
% 2.94/0.99      ( ~ r2_hidden(sK1(sK3,X0),X0)
% 2.94/0.99      | ~ r2_hidden(sK1(sK3,X0),sK3)
% 2.94/0.99      | sK3 = X0 ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1699,plain,
% 2.94/0.99      ( ~ r2_hidden(sK1(sK3,k2_relat_1(sK4)),k2_relat_1(sK4))
% 2.94/0.99      | ~ r2_hidden(sK1(sK3,k2_relat_1(sK4)),sK3)
% 2.94/0.99      | sK3 = k2_relat_1(sK4) ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_1325]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1700,plain,
% 2.94/0.99      ( sK3 = k2_relat_1(sK4)
% 2.94/0.99      | r2_hidden(sK1(sK3,k2_relat_1(sK4)),k2_relat_1(sK4)) != iProver_top
% 2.94/0.99      | r2_hidden(sK1(sK3,k2_relat_1(sK4)),sK3) != iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_1699]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2055,plain,
% 2.94/0.99      ( r2_hidden(sK1(sK3,k2_relat_1(sK4)),k2_relat_1(sK4)) = iProver_top
% 2.94/0.99      | r2_hidden(sK5(sK1(sK3,k2_relat_1(sK4))),k1_relat_1(sK4)) != iProver_top ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_2054,c_1730]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2958,plain,
% 2.94/0.99      ( r2_hidden(sK5(sK1(sK3,k2_relat_1(sK4))),k1_relat_1(sK4)) != iProver_top ),
% 2.94/0.99      inference(global_propositional_subsumption,
% 2.94/0.99                [status(thm)],
% 2.94/0.99                [c_2842,c_20,c_1208,c_1280,c_1700,c_2055]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2963,plain,
% 2.94/0.99      ( sK3 = k1_xboole_0
% 2.94/0.99      | r2_hidden(sK5(sK1(sK3,k2_relat_1(sK4))),sK2) != iProver_top ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_1501,c_2958]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1996,plain,
% 2.94/0.99      ( k2_relat_1(sK4) = X0
% 2.94/0.99      | r2_hidden(sK1(X0,k2_relat_1(sK4)),X0) = iProver_top
% 2.94/0.99      | r2_hidden(sK1(X0,k2_relat_1(sK4)),sK3) = iProver_top ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_1078,c_1741]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3079,plain,
% 2.94/0.99      ( k2_relat_1(sK4) = sK3
% 2.94/0.99      | r2_hidden(sK1(sK3,k2_relat_1(sK4)),sK3) = iProver_top
% 2.94/0.99      | iProver_top != iProver_top ),
% 2.94/0.99      inference(equality_factoring,[status(thm)],[c_1996]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3081,plain,
% 2.94/0.99      ( k2_relat_1(sK4) = sK3
% 2.94/0.99      | r2_hidden(sK1(sK3,k2_relat_1(sK4)),sK3) = iProver_top ),
% 2.94/0.99      inference(equality_resolution_simp,[status(thm)],[c_3079]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3711,plain,
% 2.94/0.99      ( sK3 = k1_xboole_0 ),
% 2.94/0.99      inference(global_propositional_subsumption,
% 2.94/0.99                [status(thm)],
% 2.94/0.99                [c_2896,c_1290,c_2799,c_2963,c_3081]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3730,plain,
% 2.94/0.99      ( r1_tarski(k2_relat_1(sK4),k1_xboole_0) = iProver_top ),
% 2.94/0.99      inference(demodulation,[status(thm)],[c_3711,c_1536]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_840,plain,
% 2.94/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 2.94/0.99      theory(equality) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1413,plain,
% 2.94/0.99      ( ~ r1_tarski(X0,X1)
% 2.94/0.99      | r1_tarski(k2_relset_1(sK2,sK3,sK4),X1)
% 2.94/0.99      | k2_relset_1(sK2,sK3,sK4) != X0 ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_840]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3340,plain,
% 2.94/0.99      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),X0)
% 2.94/0.99      | ~ r1_tarski(k2_relat_1(sK4),X0)
% 2.94/0.99      | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4) ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_1413]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3341,plain,
% 2.94/0.99      ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
% 2.94/0.99      | r1_tarski(k2_relset_1(sK2,sK3,sK4),X0) = iProver_top
% 2.94/0.99      | r1_tarski(k2_relat_1(sK4),X0) != iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_3340]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3343,plain,
% 2.94/0.99      ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
% 2.94/0.99      | r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_xboole_0) = iProver_top
% 2.94/0.99      | r1_tarski(k2_relat_1(sK4),k1_xboole_0) != iProver_top ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_3341]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1683,plain,
% 2.94/0.99      ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),X0)
% 2.94/0.99      | r2_hidden(sK1(k2_relset_1(sK2,sK3,sK4),X1),X0)
% 2.94/0.99      | ~ r2_hidden(sK1(k2_relset_1(sK2,sK3,sK4),X1),k2_relset_1(sK2,sK3,sK4)) ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1684,plain,
% 2.94/0.99      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),X0) != iProver_top
% 2.94/0.99      | r2_hidden(sK1(k2_relset_1(sK2,sK3,sK4),X1),X0) = iProver_top
% 2.94/0.99      | r2_hidden(sK1(k2_relset_1(sK2,sK3,sK4),X1),k2_relset_1(sK2,sK3,sK4)) != iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_1683]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1686,plain,
% 2.94/0.99      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_xboole_0) != iProver_top
% 2.94/0.99      | r2_hidden(sK1(k2_relset_1(sK2,sK3,sK4),k1_xboole_0),k2_relset_1(sK2,sK3,sK4)) != iProver_top
% 2.94/0.99      | r2_hidden(sK1(k2_relset_1(sK2,sK3,sK4),k1_xboole_0),k1_xboole_0) = iProver_top ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_1684]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_0,plain,
% 2.94/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.94/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_4,plain,
% 2.94/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.94/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_289,plain,
% 2.94/0.99      ( ~ r2_hidden(X0,X1) | k1_xboole_0 != X1 ),
% 2.94/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_4]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_290,plain,
% 2.94/0.99      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.94/0.99      inference(unflattening,[status(thm)],[c_289]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1593,plain,
% 2.94/0.99      ( ~ r2_hidden(sK1(k2_relset_1(sK2,sK3,sK4),k1_xboole_0),k1_xboole_0) ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_290]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1596,plain,
% 2.94/0.99      ( r2_hidden(sK1(k2_relset_1(sK2,sK3,sK4),k1_xboole_0),k1_xboole_0) != iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_1593]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1262,plain,
% 2.94/0.99      ( r2_hidden(sK1(k2_relset_1(sK2,sK3,sK4),X0),X0)
% 2.94/0.99      | r2_hidden(sK1(k2_relset_1(sK2,sK3,sK4),X0),k2_relset_1(sK2,sK3,sK4))
% 2.94/0.99      | k2_relset_1(sK2,sK3,sK4) = X0 ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1268,plain,
% 2.94/0.99      ( k2_relset_1(sK2,sK3,sK4) = X0
% 2.94/0.99      | r2_hidden(sK1(k2_relset_1(sK2,sK3,sK4),X0),X0) = iProver_top
% 2.94/0.99      | r2_hidden(sK1(k2_relset_1(sK2,sK3,sK4),X0),k2_relset_1(sK2,sK3,sK4)) = iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_1262]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1270,plain,
% 2.94/0.99      ( k2_relset_1(sK2,sK3,sK4) = k1_xboole_0
% 2.94/0.99      | r2_hidden(sK1(k2_relset_1(sK2,sK3,sK4),k1_xboole_0),k2_relset_1(sK2,sK3,sK4)) = iProver_top
% 2.94/0.99      | r2_hidden(sK1(k2_relset_1(sK2,sK3,sK4),k1_xboole_0),k1_xboole_0) = iProver_top ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_1268]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1210,plain,
% 2.94/0.99      ( k2_relset_1(sK2,sK3,sK4) = sK3
% 2.94/0.99      | k2_relset_1(sK2,sK3,sK4) != k1_xboole_0
% 2.94/0.99      | sK3 != k1_xboole_0 ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_1209]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(contradiction,plain,
% 2.94/0.99      ( $false ),
% 2.94/0.99      inference(minisat,
% 2.94/0.99                [status(thm)],
% 2.94/0.99                [c_3730,c_3343,c_3081,c_2963,c_2799,c_1686,c_1596,c_1290,
% 2.94/0.99                 c_1270,c_1210,c_1208,c_20]) ).
% 2.94/0.99  
% 2.94/0.99  
% 2.94/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.94/0.99  
% 2.94/0.99  ------                               Statistics
% 2.94/0.99  
% 2.94/0.99  ------ General
% 2.94/0.99  
% 2.94/0.99  abstr_ref_over_cycles:                  0
% 2.94/0.99  abstr_ref_under_cycles:                 0
% 2.94/0.99  gc_basic_clause_elim:                   0
% 2.94/0.99  forced_gc_time:                         0
% 2.94/0.99  parsing_time:                           0.009
% 2.94/0.99  unif_index_cands_time:                  0.
% 2.94/0.99  unif_index_add_time:                    0.
% 2.94/0.99  orderings_time:                         0.
% 2.94/0.99  out_proof_time:                         0.014
% 2.94/0.99  total_time:                             0.165
% 2.94/0.99  num_of_symbols:                         55
% 2.94/0.99  num_of_terms:                           3005
% 2.94/0.99  
% 2.94/0.99  ------ Preprocessing
% 2.94/0.99  
% 2.94/0.99  num_of_splits:                          2
% 2.94/0.99  num_of_split_atoms:                     2
% 2.94/0.99  num_of_reused_defs:                     0
% 2.94/0.99  num_eq_ax_congr_red:                    25
% 2.94/0.99  num_of_sem_filtered_clauses:            1
% 2.94/0.99  num_of_subtypes:                        0
% 2.94/0.99  monotx_restored_types:                  0
% 2.94/0.99  sat_num_of_epr_types:                   0
% 2.94/0.99  sat_num_of_non_cyclic_types:            0
% 2.94/0.99  sat_guarded_non_collapsed_types:        0
% 2.94/0.99  num_pure_diseq_elim:                    0
% 2.94/0.99  simp_replaced_by:                       0
% 2.94/0.99  res_preprocessed:                       101
% 2.94/0.99  prep_upred:                             0
% 2.94/0.99  prep_unflattend:                        36
% 2.94/0.99  smt_new_axioms:                         0
% 2.94/0.99  pred_elim_cands:                        2
% 2.94/0.99  pred_elim:                              6
% 2.94/0.99  pred_elim_cl:                           10
% 2.94/0.99  pred_elim_cycles:                       10
% 2.94/0.99  merged_defs:                            0
% 2.94/0.99  merged_defs_ncl:                        0
% 2.94/0.99  bin_hyper_res:                          0
% 2.94/0.99  prep_cycles:                            4
% 2.94/0.99  pred_elim_time:                         0.008
% 2.94/0.99  splitting_time:                         0.
% 2.94/0.99  sem_filter_time:                        0.
% 2.94/0.99  monotx_time:                            0.
% 2.94/0.99  subtype_inf_time:                       0.
% 2.94/0.99  
% 2.94/0.99  ------ Problem properties
% 2.94/0.99  
% 2.94/0.99  clauses:                                18
% 2.94/0.99  conjectures:                            3
% 2.94/0.99  epr:                                    3
% 2.94/0.99  horn:                                   13
% 2.94/0.99  ground:                                 5
% 2.94/0.99  unary:                                  2
% 2.94/0.99  binary:                                 10
% 2.94/0.99  lits:                                   41
% 2.94/0.99  lits_eq:                                19
% 2.94/0.99  fd_pure:                                0
% 2.94/0.99  fd_pseudo:                              0
% 2.94/0.99  fd_cond:                                0
% 2.94/0.99  fd_pseudo_cond:                         2
% 2.94/0.99  ac_symbols:                             0
% 2.94/0.99  
% 2.94/0.99  ------ Propositional Solver
% 2.94/0.99  
% 2.94/0.99  prop_solver_calls:                      28
% 2.94/0.99  prop_fast_solver_calls:                 709
% 2.94/0.99  smt_solver_calls:                       0
% 2.94/0.99  smt_fast_solver_calls:                  0
% 2.94/0.99  prop_num_of_clauses:                    1285
% 2.94/0.99  prop_preprocess_simplified:             3808
% 2.94/0.99  prop_fo_subsumed:                       11
% 2.94/0.99  prop_solver_time:                       0.
% 2.94/0.99  smt_solver_time:                        0.
% 2.94/0.99  smt_fast_solver_time:                   0.
% 2.94/0.99  prop_fast_solver_time:                  0.
% 2.94/0.99  prop_unsat_core_time:                   0.
% 2.94/0.99  
% 2.94/0.99  ------ QBF
% 2.94/0.99  
% 2.94/0.99  qbf_q_res:                              0
% 2.94/0.99  qbf_num_tautologies:                    0
% 2.94/0.99  qbf_prep_cycles:                        0
% 2.94/0.99  
% 2.94/0.99  ------ BMC1
% 2.94/0.99  
% 2.94/0.99  bmc1_current_bound:                     -1
% 2.94/0.99  bmc1_last_solved_bound:                 -1
% 2.94/0.99  bmc1_unsat_core_size:                   -1
% 2.94/0.99  bmc1_unsat_core_parents_size:           -1
% 2.94/0.99  bmc1_merge_next_fun:                    0
% 2.94/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.94/0.99  
% 2.94/0.99  ------ Instantiation
% 2.94/0.99  
% 2.94/0.99  inst_num_of_clauses:                    361
% 2.94/0.99  inst_num_in_passive:                    71
% 2.94/0.99  inst_num_in_active:                     190
% 2.94/0.99  inst_num_in_unprocessed:                100
% 2.94/0.99  inst_num_of_loops:                      290
% 2.94/0.99  inst_num_of_learning_restarts:          0
% 2.94/0.99  inst_num_moves_active_passive:          97
% 2.94/0.99  inst_lit_activity:                      0
% 2.94/0.99  inst_lit_activity_moves:                0
% 2.94/0.99  inst_num_tautologies:                   0
% 2.94/0.99  inst_num_prop_implied:                  0
% 2.94/0.99  inst_num_existing_simplified:           0
% 2.94/0.99  inst_num_eq_res_simplified:             0
% 2.94/0.99  inst_num_child_elim:                    0
% 2.94/0.99  inst_num_of_dismatching_blockings:      58
% 2.94/0.99  inst_num_of_non_proper_insts:           322
% 2.94/0.99  inst_num_of_duplicates:                 0
% 2.94/0.99  inst_inst_num_from_inst_to_res:         0
% 2.94/0.99  inst_dismatching_checking_time:         0.
% 2.94/0.99  
% 2.94/0.99  ------ Resolution
% 2.94/0.99  
% 2.94/0.99  res_num_of_clauses:                     0
% 2.94/0.99  res_num_in_passive:                     0
% 2.94/0.99  res_num_in_active:                      0
% 2.94/0.99  res_num_of_loops:                       105
% 2.94/0.99  res_forward_subset_subsumed:            61
% 2.94/0.99  res_backward_subset_subsumed:           0
% 2.94/0.99  res_forward_subsumed:                   0
% 2.94/0.99  res_backward_subsumed:                  0
% 2.94/0.99  res_forward_subsumption_resolution:     0
% 2.94/0.99  res_backward_subsumption_resolution:    0
% 2.94/0.99  res_clause_to_clause_subsumption:       289
% 2.94/0.99  res_orphan_elimination:                 0
% 2.94/0.99  res_tautology_del:                      34
% 2.94/0.99  res_num_eq_res_simplified:              2
% 2.94/0.99  res_num_sel_changes:                    0
% 2.94/0.99  res_moves_from_active_to_pass:          0
% 2.94/0.99  
% 2.94/0.99  ------ Superposition
% 2.94/0.99  
% 2.94/0.99  sup_time_total:                         0.
% 2.94/0.99  sup_time_generating:                    0.
% 2.94/0.99  sup_time_sim_full:                      0.
% 2.94/0.99  sup_time_sim_immed:                     0.
% 2.94/0.99  
% 2.94/0.99  sup_num_of_clauses:                     79
% 2.94/0.99  sup_num_in_active:                      24
% 2.94/0.99  sup_num_in_passive:                     55
% 2.94/0.99  sup_num_of_loops:                       56
% 2.94/0.99  sup_fw_superposition:                   50
% 2.94/0.99  sup_bw_superposition:                   80
% 2.94/0.99  sup_immediate_simplified:               19
% 2.94/0.99  sup_given_eliminated:                   0
% 2.94/0.99  comparisons_done:                       0
% 2.94/0.99  comparisons_avoided:                    23
% 2.94/0.99  
% 2.94/0.99  ------ Simplifications
% 2.94/0.99  
% 2.94/0.99  
% 2.94/0.99  sim_fw_subset_subsumed:                 13
% 2.94/0.99  sim_bw_subset_subsumed:                 7
% 2.94/0.99  sim_fw_subsumed:                        11
% 2.94/0.99  sim_bw_subsumed:                        0
% 2.94/0.99  sim_fw_subsumption_res:                 2
% 2.94/0.99  sim_bw_subsumption_res:                 0
% 2.94/0.99  sim_tautology_del:                      3
% 2.94/0.99  sim_eq_tautology_del:                   19
% 2.94/0.99  sim_eq_res_simp:                        3
% 2.94/0.99  sim_fw_demodulated:                     0
% 2.94/0.99  sim_bw_demodulated:                     32
% 2.94/0.99  sim_light_normalised:                   0
% 2.94/0.99  sim_joinable_taut:                      0
% 2.94/0.99  sim_joinable_simp:                      0
% 2.94/0.99  sim_ac_normalised:                      0
% 2.94/0.99  sim_smt_subsumption:                    0
% 2.94/0.99  
%------------------------------------------------------------------------------
