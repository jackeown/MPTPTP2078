%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:06 EST 2020

% Result     : Theorem 3.12s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 663 expanded)
%              Number of clauses        :  111 ( 247 expanded)
%              Number of leaves         :   21 ( 126 expanded)
%              Depth                    :   23
%              Number of atoms          :  504 (2707 expanded)
%              Number of equality atoms :  204 ( 637 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,axiom,(
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

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ( m1_subset_1(X4,X1)
             => k1_funct_1(X3,X4) != X0 )
          & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f41,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f42,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f41])).

fof(f52,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( k1_funct_1(X3,X4) != X0
            | ~ m1_subset_1(X4,X1) )
        & r2_hidden(X0,k2_relset_1(X1,X2,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
   => ( ! [X4] :
          ( k1_funct_1(sK5,X4) != sK2
          | ~ m1_subset_1(X4,sK3) )
      & r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5))
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK5,sK3,sK4)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ! [X4] :
        ( k1_funct_1(sK5,X4) != sK2
        | ~ m1_subset_1(X4,sK3) )
    & r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5))
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f42,f52])).

fof(f82,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f83,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f53])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f84,plain,(
    r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f53])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f66,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
            & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f46,f47])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f49])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f81,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f53])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f86,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f69])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f85,plain,(
    ! [X4] :
      ( k1_funct_1(sK5,X4) != sK2
      | ~ m1_subset_1(X4,sK3) ) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_644,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X2
    | sK3 != X1
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_30])).

cnf(c_645,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_644])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_647,plain,
    ( k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_645,c_29])).

cnf(c_1425,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1429,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2224,plain,
    ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1425,c_1429])).

cnf(c_2522,plain,
    ( k1_relat_1(sK5) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_647,c_2224])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1428,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2164,plain,
    ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1425,c_1428])).

cnf(c_28,negated_conjecture,
    ( r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1426,plain,
    ( r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2477,plain,
    ( r2_hidden(sK2,k2_relat_1(sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2164,c_1426])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1431,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2207,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1425,c_1431])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1432,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2473,plain,
    ( k9_relat_1(sK5,k1_relat_1(sK5)) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_2207,c_1432])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1434,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_14,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_395,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_31])).

cnf(c_396,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK5)
    | ~ v1_relat_1(sK5)
    | k1_funct_1(sK5,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_395])).

cnf(c_1423,plain,
    ( k1_funct_1(sK5,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_396])).

cnf(c_34,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_397,plain,
    ( k1_funct_1(sK5,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_396])).

cnf(c_1654,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1655,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1654])).

cnf(c_1712,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top
    | k1_funct_1(sK5,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1423,c_34,c_397,c_1655])).

cnf(c_1713,plain,
    ( k1_funct_1(sK5,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_1712])).

cnf(c_3101,plain,
    ( k1_funct_1(sK5,sK1(X0,X1,sK5)) = X0
    | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1434,c_1713])).

cnf(c_3449,plain,
    ( r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
    | k1_funct_1(sK5,sK1(X0,X1,sK5)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3101,c_34,c_1655])).

cnf(c_3450,plain,
    ( k1_funct_1(sK5,sK1(X0,X1,sK5)) = X0
    | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3449])).

cnf(c_3459,plain,
    ( k1_funct_1(sK5,sK1(X0,k1_relat_1(sK5),sK5)) = X0
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2473,c_3450])).

cnf(c_5365,plain,
    ( k1_funct_1(sK5,sK1(sK2,k1_relat_1(sK5),sK5)) = sK2 ),
    inference(superposition,[status(thm)],[c_2477,c_3459])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_425,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_31])).

cnf(c_426,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5)
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_425])).

cnf(c_1421,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_426])).

cnf(c_427,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_426])).

cnf(c_1754,plain,
    ( r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1421,c_34,c_427,c_1655])).

cnf(c_1755,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top ),
    inference(renaming,[status(thm)],[c_1754])).

cnf(c_5404,plain,
    ( r2_hidden(sK1(sK2,k1_relat_1(sK5),sK5),k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k4_tarski(sK1(sK2,k1_relat_1(sK5),sK5),sK2),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_5365,c_1755])).

cnf(c_35,plain,
    ( r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1708,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_986,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1816,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_986])).

cnf(c_987,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1921,plain,
    ( X0 != X1
    | X0 = k2_relset_1(sK3,sK4,sK5)
    | k2_relset_1(sK3,sK4,sK5) != X1 ),
    inference(instantiation,[status(thm)],[c_987])).

cnf(c_2287,plain,
    ( X0 = k2_relset_1(sK3,sK4,sK5)
    | X0 != k2_relat_1(sK5)
    | k2_relset_1(sK3,sK4,sK5) != k2_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1921])).

cnf(c_2388,plain,
    ( k2_relset_1(sK3,sK4,sK5) != k2_relat_1(sK5)
    | k9_relat_1(sK5,k1_relat_1(sK5)) = k2_relset_1(sK3,sK4,sK5)
    | k9_relat_1(sK5,k1_relat_1(sK5)) != k2_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_2287])).

cnf(c_2389,plain,
    ( ~ v1_relat_1(sK5)
    | k9_relat_1(sK5,k1_relat_1(sK5)) = k2_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_988,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1724,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5))
    | X1 != k2_relset_1(sK3,sK4,sK5)
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_988])).

cnf(c_1815,plain,
    ( r2_hidden(sK2,X0)
    | ~ r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5))
    | X0 != k2_relset_1(sK3,sK4,sK5)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1724])).

cnf(c_3180,plain,
    ( ~ r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5))
    | r2_hidden(sK2,k9_relat_1(sK5,k1_relat_1(sK5)))
    | k9_relat_1(sK5,k1_relat_1(sK5)) != k2_relset_1(sK3,sK4,sK5)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1815])).

cnf(c_3181,plain,
    ( k9_relat_1(sK5,k1_relat_1(sK5)) != k2_relset_1(sK3,sK4,sK5)
    | sK2 != sK2
    | r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5)) != iProver_top
    | r2_hidden(sK2,k9_relat_1(sK5,k1_relat_1(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3180])).

cnf(c_2998,plain,
    ( r2_hidden(k4_tarski(sK1(sK2,X0,X1),sK2),X1)
    | ~ r2_hidden(sK2,k9_relat_1(X1,X0))
    | ~ v1_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_4010,plain,
    ( r2_hidden(k4_tarski(sK1(sK2,k1_relat_1(sK5),sK5),sK2),sK5)
    | ~ r2_hidden(sK2,k9_relat_1(sK5,k1_relat_1(sK5)))
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_2998])).

cnf(c_4011,plain,
    ( r2_hidden(k4_tarski(sK1(sK2,k1_relat_1(sK5),sK5),sK2),sK5) = iProver_top
    | r2_hidden(sK2,k9_relat_1(sK5,k1_relat_1(sK5))) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4010])).

cnf(c_5506,plain,
    ( r2_hidden(k4_tarski(sK1(sK2,k1_relat_1(sK5),sK5),sK2),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5404,c_29,c_34,c_35,c_1654,c_1655,c_1708,c_1816,c_2388,c_2389,c_3181,c_4011])).

cnf(c_15,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_410,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_31])).

cnf(c_411,plain,
    ( r2_hidden(X0,k1_relat_1(sK5))
    | ~ r2_hidden(k4_tarski(X0,X1),sK5)
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_1422,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_411])).

cnf(c_412,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_411])).

cnf(c_1745,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1422,c_34,c_412,c_1655])).

cnf(c_1746,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_1745])).

cnf(c_5515,plain,
    ( r2_hidden(sK1(sK2,k1_relat_1(sK5),sK5),k1_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5506,c_1746])).

cnf(c_5728,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK1(sK2,sK3,sK5),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2522,c_5515])).

cnf(c_3,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_109,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_990,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_1001,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_990])).

cnf(c_1011,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_986])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1694,plain,
    ( m1_subset_1(k2_relset_1(sK3,sK4,sK5),k1_zfmisc_1(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1678,plain,
    ( ~ m1_subset_1(k2_relset_1(sK3,sK4,sK5),k1_zfmisc_1(X0))
    | r2_hidden(sK2,X0)
    | ~ r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1802,plain,
    ( ~ m1_subset_1(k2_relset_1(sK3,sK4,sK5),k1_zfmisc_1(sK4))
    | ~ r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5))
    | r2_hidden(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_1678])).

cnf(c_1891,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
    | r2_hidden(sK2,X0)
    | ~ r2_hidden(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1893,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))
    | ~ r2_hidden(sK2,sK4)
    | r2_hidden(sK2,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1891])).

cnf(c_989,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1734,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | X1 != k1_zfmisc_1(X2)
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_989])).

cnf(c_2044,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | X0 != k1_xboole_0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1734])).

cnf(c_2667,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(X0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | k1_zfmisc_1(X0) != k1_zfmisc_1(X0)
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2044])).

cnf(c_2669,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2667])).

cnf(c_2888,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_366,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X1,X0) ),
    inference(resolution,[status(thm)],[c_6,c_16])).

cnf(c_2989,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
    | ~ r2_hidden(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_366])).

cnf(c_2991,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2))
    | ~ r2_hidden(sK2,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2989])).

cnf(c_6084,plain,
    ( r2_hidden(sK1(sK2,sK3,sK5),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5728,c_29,c_28,c_109,c_1001,c_1011,c_1694,c_1802,c_1893,c_2669,c_2888,c_2991])).

cnf(c_4,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1439,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6090,plain,
    ( m1_subset_1(sK1(sK2,sK3,sK5),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6084,c_1439])).

cnf(c_3218,plain,
    ( k9_relat_1(sK5,sK3) = k2_relat_1(sK5)
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2522,c_2473])).

cnf(c_3667,plain,
    ( k9_relat_1(sK5,sK3) = k2_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3218,c_29,c_28,c_109,c_1001,c_1011,c_1694,c_1802,c_1893,c_2669,c_2888,c_2991])).

cnf(c_3670,plain,
    ( k1_funct_1(sK5,sK1(X0,sK3,sK5)) = X0
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3667,c_3450])).

cnf(c_4661,plain,
    ( k1_funct_1(sK5,sK1(sK2,sK3,sK5)) = sK2 ),
    inference(superposition,[status(thm)],[c_2477,c_3670])).

cnf(c_27,negated_conjecture,
    ( ~ m1_subset_1(X0,sK3)
    | k1_funct_1(sK5,X0) != sK2 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1427,plain,
    ( k1_funct_1(sK5,X0) != sK2
    | m1_subset_1(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5084,plain,
    ( m1_subset_1(sK1(sK2,sK3,sK5),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4661,c_1427])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6090,c_5084])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:46:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.12/1.04  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/1.04  
% 3.12/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.12/1.04  
% 3.12/1.04  ------  iProver source info
% 3.12/1.04  
% 3.12/1.04  git: date: 2020-06-30 10:37:57 +0100
% 3.12/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.12/1.04  git: non_committed_changes: false
% 3.12/1.04  git: last_make_outside_of_git: false
% 3.12/1.04  
% 3.12/1.04  ------ 
% 3.12/1.04  
% 3.12/1.04  ------ Input Options
% 3.12/1.04  
% 3.12/1.04  --out_options                           all
% 3.12/1.04  --tptp_safe_out                         true
% 3.12/1.04  --problem_path                          ""
% 3.12/1.04  --include_path                          ""
% 3.12/1.04  --clausifier                            res/vclausify_rel
% 3.12/1.04  --clausifier_options                    --mode clausify
% 3.12/1.04  --stdin                                 false
% 3.12/1.04  --stats_out                             all
% 3.12/1.04  
% 3.12/1.04  ------ General Options
% 3.12/1.04  
% 3.12/1.04  --fof                                   false
% 3.12/1.04  --time_out_real                         305.
% 3.12/1.04  --time_out_virtual                      -1.
% 3.12/1.04  --symbol_type_check                     false
% 3.12/1.04  --clausify_out                          false
% 3.12/1.04  --sig_cnt_out                           false
% 3.12/1.04  --trig_cnt_out                          false
% 3.12/1.04  --trig_cnt_out_tolerance                1.
% 3.12/1.04  --trig_cnt_out_sk_spl                   false
% 3.12/1.04  --abstr_cl_out                          false
% 3.12/1.04  
% 3.12/1.04  ------ Global Options
% 3.12/1.04  
% 3.12/1.04  --schedule                              default
% 3.12/1.04  --add_important_lit                     false
% 3.12/1.04  --prop_solver_per_cl                    1000
% 3.12/1.04  --min_unsat_core                        false
% 3.12/1.04  --soft_assumptions                      false
% 3.12/1.04  --soft_lemma_size                       3
% 3.12/1.04  --prop_impl_unit_size                   0
% 3.12/1.04  --prop_impl_unit                        []
% 3.12/1.04  --share_sel_clauses                     true
% 3.12/1.04  --reset_solvers                         false
% 3.12/1.04  --bc_imp_inh                            [conj_cone]
% 3.12/1.04  --conj_cone_tolerance                   3.
% 3.12/1.04  --extra_neg_conj                        none
% 3.12/1.04  --large_theory_mode                     true
% 3.12/1.04  --prolific_symb_bound                   200
% 3.12/1.04  --lt_threshold                          2000
% 3.12/1.04  --clause_weak_htbl                      true
% 3.12/1.04  --gc_record_bc_elim                     false
% 3.12/1.04  
% 3.12/1.04  ------ Preprocessing Options
% 3.12/1.04  
% 3.12/1.04  --preprocessing_flag                    true
% 3.12/1.04  --time_out_prep_mult                    0.1
% 3.12/1.04  --splitting_mode                        input
% 3.12/1.04  --splitting_grd                         true
% 3.12/1.04  --splitting_cvd                         false
% 3.12/1.04  --splitting_cvd_svl                     false
% 3.12/1.04  --splitting_nvd                         32
% 3.12/1.04  --sub_typing                            true
% 3.12/1.04  --prep_gs_sim                           true
% 3.12/1.04  --prep_unflatten                        true
% 3.12/1.04  --prep_res_sim                          true
% 3.12/1.04  --prep_upred                            true
% 3.12/1.04  --prep_sem_filter                       exhaustive
% 3.12/1.04  --prep_sem_filter_out                   false
% 3.12/1.04  --pred_elim                             true
% 3.12/1.04  --res_sim_input                         true
% 3.12/1.04  --eq_ax_congr_red                       true
% 3.12/1.04  --pure_diseq_elim                       true
% 3.12/1.04  --brand_transform                       false
% 3.12/1.04  --non_eq_to_eq                          false
% 3.12/1.04  --prep_def_merge                        true
% 3.12/1.04  --prep_def_merge_prop_impl              false
% 3.12/1.04  --prep_def_merge_mbd                    true
% 3.12/1.04  --prep_def_merge_tr_red                 false
% 3.12/1.04  --prep_def_merge_tr_cl                  false
% 3.12/1.04  --smt_preprocessing                     true
% 3.12/1.04  --smt_ac_axioms                         fast
% 3.12/1.04  --preprocessed_out                      false
% 3.12/1.04  --preprocessed_stats                    false
% 3.12/1.04  
% 3.12/1.04  ------ Abstraction refinement Options
% 3.12/1.04  
% 3.12/1.04  --abstr_ref                             []
% 3.12/1.04  --abstr_ref_prep                        false
% 3.12/1.04  --abstr_ref_until_sat                   false
% 3.12/1.04  --abstr_ref_sig_restrict                funpre
% 3.12/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 3.12/1.04  --abstr_ref_under                       []
% 3.12/1.04  
% 3.12/1.04  ------ SAT Options
% 3.12/1.04  
% 3.12/1.04  --sat_mode                              false
% 3.12/1.04  --sat_fm_restart_options                ""
% 3.12/1.04  --sat_gr_def                            false
% 3.12/1.04  --sat_epr_types                         true
% 3.12/1.04  --sat_non_cyclic_types                  false
% 3.12/1.04  --sat_finite_models                     false
% 3.12/1.04  --sat_fm_lemmas                         false
% 3.12/1.04  --sat_fm_prep                           false
% 3.12/1.04  --sat_fm_uc_incr                        true
% 3.12/1.04  --sat_out_model                         small
% 3.12/1.04  --sat_out_clauses                       false
% 3.12/1.04  
% 3.12/1.04  ------ QBF Options
% 3.12/1.04  
% 3.12/1.04  --qbf_mode                              false
% 3.12/1.04  --qbf_elim_univ                         false
% 3.12/1.04  --qbf_dom_inst                          none
% 3.12/1.04  --qbf_dom_pre_inst                      false
% 3.12/1.04  --qbf_sk_in                             false
% 3.12/1.04  --qbf_pred_elim                         true
% 3.12/1.04  --qbf_split                             512
% 3.12/1.04  
% 3.12/1.04  ------ BMC1 Options
% 3.12/1.04  
% 3.12/1.04  --bmc1_incremental                      false
% 3.12/1.04  --bmc1_axioms                           reachable_all
% 3.12/1.04  --bmc1_min_bound                        0
% 3.12/1.04  --bmc1_max_bound                        -1
% 3.12/1.04  --bmc1_max_bound_default                -1
% 3.12/1.04  --bmc1_symbol_reachability              true
% 3.12/1.04  --bmc1_property_lemmas                  false
% 3.12/1.04  --bmc1_k_induction                      false
% 3.12/1.04  --bmc1_non_equiv_states                 false
% 3.12/1.04  --bmc1_deadlock                         false
% 3.12/1.04  --bmc1_ucm                              false
% 3.12/1.04  --bmc1_add_unsat_core                   none
% 3.12/1.04  --bmc1_unsat_core_children              false
% 3.12/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 3.12/1.04  --bmc1_out_stat                         full
% 3.12/1.04  --bmc1_ground_init                      false
% 3.12/1.04  --bmc1_pre_inst_next_state              false
% 3.12/1.04  --bmc1_pre_inst_state                   false
% 3.12/1.04  --bmc1_pre_inst_reach_state             false
% 3.12/1.04  --bmc1_out_unsat_core                   false
% 3.12/1.04  --bmc1_aig_witness_out                  false
% 3.12/1.04  --bmc1_verbose                          false
% 3.12/1.04  --bmc1_dump_clauses_tptp                false
% 3.12/1.04  --bmc1_dump_unsat_core_tptp             false
% 3.12/1.04  --bmc1_dump_file                        -
% 3.12/1.04  --bmc1_ucm_expand_uc_limit              128
% 3.12/1.04  --bmc1_ucm_n_expand_iterations          6
% 3.12/1.04  --bmc1_ucm_extend_mode                  1
% 3.12/1.04  --bmc1_ucm_init_mode                    2
% 3.12/1.04  --bmc1_ucm_cone_mode                    none
% 3.12/1.04  --bmc1_ucm_reduced_relation_type        0
% 3.12/1.04  --bmc1_ucm_relax_model                  4
% 3.12/1.04  --bmc1_ucm_full_tr_after_sat            true
% 3.12/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 3.12/1.04  --bmc1_ucm_layered_model                none
% 3.12/1.04  --bmc1_ucm_max_lemma_size               10
% 3.12/1.04  
% 3.12/1.04  ------ AIG Options
% 3.12/1.04  
% 3.12/1.04  --aig_mode                              false
% 3.12/1.04  
% 3.12/1.04  ------ Instantiation Options
% 3.12/1.04  
% 3.12/1.04  --instantiation_flag                    true
% 3.12/1.04  --inst_sos_flag                         false
% 3.12/1.04  --inst_sos_phase                        true
% 3.12/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.12/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.12/1.04  --inst_lit_sel_side                     num_symb
% 3.12/1.04  --inst_solver_per_active                1400
% 3.12/1.04  --inst_solver_calls_frac                1.
% 3.12/1.04  --inst_passive_queue_type               priority_queues
% 3.12/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.12/1.04  --inst_passive_queues_freq              [25;2]
% 3.12/1.04  --inst_dismatching                      true
% 3.12/1.04  --inst_eager_unprocessed_to_passive     true
% 3.12/1.04  --inst_prop_sim_given                   true
% 3.12/1.04  --inst_prop_sim_new                     false
% 3.12/1.04  --inst_subs_new                         false
% 3.12/1.04  --inst_eq_res_simp                      false
% 3.12/1.04  --inst_subs_given                       false
% 3.12/1.04  --inst_orphan_elimination               true
% 3.12/1.04  --inst_learning_loop_flag               true
% 3.12/1.04  --inst_learning_start                   3000
% 3.12/1.04  --inst_learning_factor                  2
% 3.12/1.04  --inst_start_prop_sim_after_learn       3
% 3.12/1.04  --inst_sel_renew                        solver
% 3.12/1.04  --inst_lit_activity_flag                true
% 3.12/1.04  --inst_restr_to_given                   false
% 3.12/1.04  --inst_activity_threshold               500
% 3.12/1.04  --inst_out_proof                        true
% 3.12/1.04  
% 3.12/1.04  ------ Resolution Options
% 3.12/1.04  
% 3.12/1.04  --resolution_flag                       true
% 3.12/1.04  --res_lit_sel                           adaptive
% 3.12/1.04  --res_lit_sel_side                      none
% 3.12/1.04  --res_ordering                          kbo
% 3.12/1.04  --res_to_prop_solver                    active
% 3.12/1.04  --res_prop_simpl_new                    false
% 3.12/1.04  --res_prop_simpl_given                  true
% 3.12/1.04  --res_passive_queue_type                priority_queues
% 3.12/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.12/1.04  --res_passive_queues_freq               [15;5]
% 3.12/1.04  --res_forward_subs                      full
% 3.12/1.04  --res_backward_subs                     full
% 3.12/1.04  --res_forward_subs_resolution           true
% 3.12/1.04  --res_backward_subs_resolution          true
% 3.12/1.04  --res_orphan_elimination                true
% 3.12/1.04  --res_time_limit                        2.
% 3.12/1.04  --res_out_proof                         true
% 3.12/1.04  
% 3.12/1.04  ------ Superposition Options
% 3.12/1.04  
% 3.12/1.04  --superposition_flag                    true
% 3.12/1.04  --sup_passive_queue_type                priority_queues
% 3.12/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.12/1.04  --sup_passive_queues_freq               [8;1;4]
% 3.12/1.04  --demod_completeness_check              fast
% 3.12/1.04  --demod_use_ground                      true
% 3.12/1.04  --sup_to_prop_solver                    passive
% 3.12/1.04  --sup_prop_simpl_new                    true
% 3.12/1.04  --sup_prop_simpl_given                  true
% 3.12/1.04  --sup_fun_splitting                     false
% 3.12/1.04  --sup_smt_interval                      50000
% 3.12/1.04  
% 3.12/1.04  ------ Superposition Simplification Setup
% 3.12/1.04  
% 3.12/1.04  --sup_indices_passive                   []
% 3.12/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 3.12/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/1.04  --sup_full_bw                           [BwDemod]
% 3.12/1.04  --sup_immed_triv                        [TrivRules]
% 3.12/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.12/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/1.04  --sup_immed_bw_main                     []
% 3.12/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.12/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 3.12/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.12/1.04  
% 3.12/1.04  ------ Combination Options
% 3.12/1.04  
% 3.12/1.04  --comb_res_mult                         3
% 3.12/1.04  --comb_sup_mult                         2
% 3.12/1.04  --comb_inst_mult                        10
% 3.12/1.04  
% 3.12/1.04  ------ Debug Options
% 3.12/1.04  
% 3.12/1.04  --dbg_backtrace                         false
% 3.12/1.04  --dbg_dump_prop_clauses                 false
% 3.12/1.04  --dbg_dump_prop_clauses_file            -
% 3.12/1.04  --dbg_out_stat                          false
% 3.12/1.04  ------ Parsing...
% 3.12/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.12/1.04  
% 3.12/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.12/1.04  
% 3.12/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.12/1.04  
% 3.12/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.12/1.04  ------ Proving...
% 3.12/1.04  ------ Problem Properties 
% 3.12/1.04  
% 3.12/1.04  
% 3.12/1.04  clauses                                 26
% 3.12/1.04  conjectures                             3
% 3.12/1.04  EPR                                     3
% 3.12/1.04  Horn                                    23
% 3.12/1.04  unary                                   4
% 3.12/1.04  binary                                  10
% 3.12/1.04  lits                                    63
% 3.12/1.04  lits eq                                 12
% 3.12/1.04  fd_pure                                 0
% 3.12/1.04  fd_pseudo                               0
% 3.12/1.04  fd_cond                                 0
% 3.12/1.04  fd_pseudo_cond                          1
% 3.12/1.04  AC symbols                              0
% 3.12/1.04  
% 3.12/1.04  ------ Schedule dynamic 5 is on 
% 3.12/1.04  
% 3.12/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.12/1.04  
% 3.12/1.04  
% 3.12/1.04  ------ 
% 3.12/1.04  Current options:
% 3.12/1.04  ------ 
% 3.12/1.04  
% 3.12/1.04  ------ Input Options
% 3.12/1.04  
% 3.12/1.04  --out_options                           all
% 3.12/1.04  --tptp_safe_out                         true
% 3.12/1.04  --problem_path                          ""
% 3.12/1.04  --include_path                          ""
% 3.12/1.04  --clausifier                            res/vclausify_rel
% 3.12/1.04  --clausifier_options                    --mode clausify
% 3.12/1.04  --stdin                                 false
% 3.12/1.04  --stats_out                             all
% 3.12/1.04  
% 3.12/1.04  ------ General Options
% 3.12/1.04  
% 3.12/1.04  --fof                                   false
% 3.12/1.04  --time_out_real                         305.
% 3.12/1.04  --time_out_virtual                      -1.
% 3.12/1.04  --symbol_type_check                     false
% 3.12/1.04  --clausify_out                          false
% 3.12/1.04  --sig_cnt_out                           false
% 3.12/1.04  --trig_cnt_out                          false
% 3.12/1.04  --trig_cnt_out_tolerance                1.
% 3.12/1.04  --trig_cnt_out_sk_spl                   false
% 3.12/1.04  --abstr_cl_out                          false
% 3.12/1.04  
% 3.12/1.04  ------ Global Options
% 3.12/1.04  
% 3.12/1.04  --schedule                              default
% 3.12/1.04  --add_important_lit                     false
% 3.12/1.04  --prop_solver_per_cl                    1000
% 3.12/1.04  --min_unsat_core                        false
% 3.12/1.04  --soft_assumptions                      false
% 3.12/1.04  --soft_lemma_size                       3
% 3.12/1.04  --prop_impl_unit_size                   0
% 3.12/1.04  --prop_impl_unit                        []
% 3.12/1.04  --share_sel_clauses                     true
% 3.12/1.04  --reset_solvers                         false
% 3.12/1.04  --bc_imp_inh                            [conj_cone]
% 3.12/1.04  --conj_cone_tolerance                   3.
% 3.12/1.04  --extra_neg_conj                        none
% 3.12/1.04  --large_theory_mode                     true
% 3.12/1.04  --prolific_symb_bound                   200
% 3.12/1.04  --lt_threshold                          2000
% 3.12/1.04  --clause_weak_htbl                      true
% 3.12/1.04  --gc_record_bc_elim                     false
% 3.12/1.04  
% 3.12/1.04  ------ Preprocessing Options
% 3.12/1.04  
% 3.12/1.04  --preprocessing_flag                    true
% 3.12/1.04  --time_out_prep_mult                    0.1
% 3.12/1.04  --splitting_mode                        input
% 3.12/1.04  --splitting_grd                         true
% 3.12/1.04  --splitting_cvd                         false
% 3.12/1.04  --splitting_cvd_svl                     false
% 3.12/1.04  --splitting_nvd                         32
% 3.12/1.04  --sub_typing                            true
% 3.12/1.04  --prep_gs_sim                           true
% 3.12/1.04  --prep_unflatten                        true
% 3.12/1.04  --prep_res_sim                          true
% 3.12/1.04  --prep_upred                            true
% 3.12/1.04  --prep_sem_filter                       exhaustive
% 3.12/1.04  --prep_sem_filter_out                   false
% 3.12/1.04  --pred_elim                             true
% 3.12/1.04  --res_sim_input                         true
% 3.12/1.04  --eq_ax_congr_red                       true
% 3.12/1.04  --pure_diseq_elim                       true
% 3.12/1.04  --brand_transform                       false
% 3.12/1.04  --non_eq_to_eq                          false
% 3.12/1.04  --prep_def_merge                        true
% 3.12/1.04  --prep_def_merge_prop_impl              false
% 3.12/1.04  --prep_def_merge_mbd                    true
% 3.12/1.04  --prep_def_merge_tr_red                 false
% 3.12/1.04  --prep_def_merge_tr_cl                  false
% 3.12/1.04  --smt_preprocessing                     true
% 3.12/1.04  --smt_ac_axioms                         fast
% 3.12/1.04  --preprocessed_out                      false
% 3.12/1.04  --preprocessed_stats                    false
% 3.12/1.04  
% 3.12/1.04  ------ Abstraction refinement Options
% 3.12/1.04  
% 3.12/1.04  --abstr_ref                             []
% 3.12/1.04  --abstr_ref_prep                        false
% 3.12/1.04  --abstr_ref_until_sat                   false
% 3.12/1.04  --abstr_ref_sig_restrict                funpre
% 3.12/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 3.12/1.04  --abstr_ref_under                       []
% 3.12/1.04  
% 3.12/1.04  ------ SAT Options
% 3.12/1.04  
% 3.12/1.04  --sat_mode                              false
% 3.12/1.04  --sat_fm_restart_options                ""
% 3.12/1.04  --sat_gr_def                            false
% 3.12/1.04  --sat_epr_types                         true
% 3.12/1.04  --sat_non_cyclic_types                  false
% 3.12/1.04  --sat_finite_models                     false
% 3.12/1.04  --sat_fm_lemmas                         false
% 3.12/1.04  --sat_fm_prep                           false
% 3.12/1.04  --sat_fm_uc_incr                        true
% 3.12/1.04  --sat_out_model                         small
% 3.12/1.04  --sat_out_clauses                       false
% 3.12/1.04  
% 3.12/1.04  ------ QBF Options
% 3.12/1.04  
% 3.12/1.04  --qbf_mode                              false
% 3.12/1.04  --qbf_elim_univ                         false
% 3.12/1.04  --qbf_dom_inst                          none
% 3.12/1.04  --qbf_dom_pre_inst                      false
% 3.12/1.04  --qbf_sk_in                             false
% 3.12/1.04  --qbf_pred_elim                         true
% 3.12/1.04  --qbf_split                             512
% 3.12/1.04  
% 3.12/1.04  ------ BMC1 Options
% 3.12/1.04  
% 3.12/1.04  --bmc1_incremental                      false
% 3.12/1.04  --bmc1_axioms                           reachable_all
% 3.12/1.04  --bmc1_min_bound                        0
% 3.12/1.04  --bmc1_max_bound                        -1
% 3.12/1.04  --bmc1_max_bound_default                -1
% 3.12/1.04  --bmc1_symbol_reachability              true
% 3.12/1.04  --bmc1_property_lemmas                  false
% 3.12/1.04  --bmc1_k_induction                      false
% 3.12/1.04  --bmc1_non_equiv_states                 false
% 3.12/1.04  --bmc1_deadlock                         false
% 3.12/1.04  --bmc1_ucm                              false
% 3.12/1.04  --bmc1_add_unsat_core                   none
% 3.12/1.04  --bmc1_unsat_core_children              false
% 3.12/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 3.12/1.04  --bmc1_out_stat                         full
% 3.12/1.04  --bmc1_ground_init                      false
% 3.12/1.04  --bmc1_pre_inst_next_state              false
% 3.12/1.04  --bmc1_pre_inst_state                   false
% 3.12/1.04  --bmc1_pre_inst_reach_state             false
% 3.12/1.04  --bmc1_out_unsat_core                   false
% 3.12/1.04  --bmc1_aig_witness_out                  false
% 3.12/1.04  --bmc1_verbose                          false
% 3.12/1.04  --bmc1_dump_clauses_tptp                false
% 3.12/1.04  --bmc1_dump_unsat_core_tptp             false
% 3.12/1.04  --bmc1_dump_file                        -
% 3.12/1.04  --bmc1_ucm_expand_uc_limit              128
% 3.12/1.04  --bmc1_ucm_n_expand_iterations          6
% 3.12/1.04  --bmc1_ucm_extend_mode                  1
% 3.12/1.04  --bmc1_ucm_init_mode                    2
% 3.12/1.04  --bmc1_ucm_cone_mode                    none
% 3.12/1.04  --bmc1_ucm_reduced_relation_type        0
% 3.12/1.04  --bmc1_ucm_relax_model                  4
% 3.12/1.04  --bmc1_ucm_full_tr_after_sat            true
% 3.12/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 3.12/1.04  --bmc1_ucm_layered_model                none
% 3.12/1.04  --bmc1_ucm_max_lemma_size               10
% 3.12/1.04  
% 3.12/1.04  ------ AIG Options
% 3.12/1.04  
% 3.12/1.04  --aig_mode                              false
% 3.12/1.04  
% 3.12/1.04  ------ Instantiation Options
% 3.12/1.04  
% 3.12/1.04  --instantiation_flag                    true
% 3.12/1.04  --inst_sos_flag                         false
% 3.12/1.04  --inst_sos_phase                        true
% 3.12/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.12/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.12/1.04  --inst_lit_sel_side                     none
% 3.12/1.04  --inst_solver_per_active                1400
% 3.12/1.04  --inst_solver_calls_frac                1.
% 3.12/1.04  --inst_passive_queue_type               priority_queues
% 3.12/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.12/1.04  --inst_passive_queues_freq              [25;2]
% 3.12/1.04  --inst_dismatching                      true
% 3.12/1.04  --inst_eager_unprocessed_to_passive     true
% 3.12/1.04  --inst_prop_sim_given                   true
% 3.12/1.04  --inst_prop_sim_new                     false
% 3.12/1.04  --inst_subs_new                         false
% 3.12/1.04  --inst_eq_res_simp                      false
% 3.12/1.04  --inst_subs_given                       false
% 3.12/1.04  --inst_orphan_elimination               true
% 3.12/1.04  --inst_learning_loop_flag               true
% 3.12/1.04  --inst_learning_start                   3000
% 3.12/1.04  --inst_learning_factor                  2
% 3.12/1.04  --inst_start_prop_sim_after_learn       3
% 3.12/1.04  --inst_sel_renew                        solver
% 3.12/1.04  --inst_lit_activity_flag                true
% 3.12/1.04  --inst_restr_to_given                   false
% 3.12/1.04  --inst_activity_threshold               500
% 3.12/1.04  --inst_out_proof                        true
% 3.12/1.04  
% 3.12/1.04  ------ Resolution Options
% 3.12/1.04  
% 3.12/1.04  --resolution_flag                       false
% 3.12/1.04  --res_lit_sel                           adaptive
% 3.12/1.04  --res_lit_sel_side                      none
% 3.12/1.04  --res_ordering                          kbo
% 3.12/1.04  --res_to_prop_solver                    active
% 3.12/1.04  --res_prop_simpl_new                    false
% 3.12/1.04  --res_prop_simpl_given                  true
% 3.12/1.04  --res_passive_queue_type                priority_queues
% 3.12/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.12/1.04  --res_passive_queues_freq               [15;5]
% 3.12/1.04  --res_forward_subs                      full
% 3.12/1.04  --res_backward_subs                     full
% 3.12/1.04  --res_forward_subs_resolution           true
% 3.12/1.04  --res_backward_subs_resolution          true
% 3.12/1.04  --res_orphan_elimination                true
% 3.12/1.04  --res_time_limit                        2.
% 3.12/1.04  --res_out_proof                         true
% 3.12/1.04  
% 3.12/1.04  ------ Superposition Options
% 3.12/1.04  
% 3.12/1.04  --superposition_flag                    true
% 3.12/1.04  --sup_passive_queue_type                priority_queues
% 3.12/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.12/1.04  --sup_passive_queues_freq               [8;1;4]
% 3.12/1.04  --demod_completeness_check              fast
% 3.12/1.04  --demod_use_ground                      true
% 3.12/1.04  --sup_to_prop_solver                    passive
% 3.12/1.04  --sup_prop_simpl_new                    true
% 3.12/1.04  --sup_prop_simpl_given                  true
% 3.12/1.04  --sup_fun_splitting                     false
% 3.12/1.04  --sup_smt_interval                      50000
% 3.12/1.04  
% 3.12/1.04  ------ Superposition Simplification Setup
% 3.12/1.04  
% 3.12/1.04  --sup_indices_passive                   []
% 3.12/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 3.12/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/1.04  --sup_full_bw                           [BwDemod]
% 3.12/1.04  --sup_immed_triv                        [TrivRules]
% 3.12/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.12/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/1.04  --sup_immed_bw_main                     []
% 3.12/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.12/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 3.12/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.12/1.04  
% 3.12/1.04  ------ Combination Options
% 3.12/1.04  
% 3.12/1.04  --comb_res_mult                         3
% 3.12/1.04  --comb_sup_mult                         2
% 3.12/1.04  --comb_inst_mult                        10
% 3.12/1.04  
% 3.12/1.04  ------ Debug Options
% 3.12/1.04  
% 3.12/1.04  --dbg_backtrace                         false
% 3.12/1.04  --dbg_dump_prop_clauses                 false
% 3.12/1.04  --dbg_dump_prop_clauses_file            -
% 3.12/1.04  --dbg_out_stat                          false
% 3.12/1.04  
% 3.12/1.04  
% 3.12/1.04  
% 3.12/1.04  
% 3.12/1.04  ------ Proving...
% 3.12/1.04  
% 3.12/1.04  
% 3.12/1.04  % SZS status Theorem for theBenchmark.p
% 3.12/1.04  
% 3.12/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 3.12/1.04  
% 3.12/1.04  fof(f17,axiom,(
% 3.12/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.12/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/1.04  
% 3.12/1.04  fof(f39,plain,(
% 3.12/1.04    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.12/1.04    inference(ennf_transformation,[],[f17])).
% 3.12/1.04  
% 3.12/1.04  fof(f40,plain,(
% 3.12/1.04    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.12/1.04    inference(flattening,[],[f39])).
% 3.12/1.04  
% 3.12/1.04  fof(f51,plain,(
% 3.12/1.04    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.12/1.04    inference(nnf_transformation,[],[f40])).
% 3.12/1.04  
% 3.12/1.04  fof(f75,plain,(
% 3.12/1.04    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.12/1.04    inference(cnf_transformation,[],[f51])).
% 3.12/1.04  
% 3.12/1.04  fof(f18,conjecture,(
% 3.12/1.04    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 3.12/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/1.04  
% 3.12/1.04  fof(f19,negated_conjecture,(
% 3.12/1.04    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 3.12/1.04    inference(negated_conjecture,[],[f18])).
% 3.12/1.04  
% 3.12/1.04  fof(f41,plain,(
% 3.12/1.04    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)))),
% 3.12/1.04    inference(ennf_transformation,[],[f19])).
% 3.12/1.04  
% 3.12/1.04  fof(f42,plain,(
% 3.12/1.04    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))),
% 3.12/1.04    inference(flattening,[],[f41])).
% 3.12/1.04  
% 3.12/1.04  fof(f52,plain,(
% 3.12/1.04    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (k1_funct_1(sK5,X4) != sK2 | ~m1_subset_1(X4,sK3)) & r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5))),
% 3.12/1.04    introduced(choice_axiom,[])).
% 3.12/1.04  
% 3.12/1.04  fof(f53,plain,(
% 3.12/1.04    ! [X4] : (k1_funct_1(sK5,X4) != sK2 | ~m1_subset_1(X4,sK3)) & r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)),
% 3.12/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f42,f52])).
% 3.12/1.04  
% 3.12/1.04  fof(f82,plain,(
% 3.12/1.04    v1_funct_2(sK5,sK3,sK4)),
% 3.12/1.04    inference(cnf_transformation,[],[f53])).
% 3.12/1.04  
% 3.12/1.04  fof(f83,plain,(
% 3.12/1.04    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 3.12/1.04    inference(cnf_transformation,[],[f53])).
% 3.12/1.04  
% 3.12/1.04  fof(f15,axiom,(
% 3.12/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.12/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/1.04  
% 3.12/1.04  fof(f37,plain,(
% 3.12/1.04    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.12/1.04    inference(ennf_transformation,[],[f15])).
% 3.12/1.04  
% 3.12/1.04  fof(f73,plain,(
% 3.12/1.04    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.12/1.04    inference(cnf_transformation,[],[f37])).
% 3.12/1.04  
% 3.12/1.04  fof(f16,axiom,(
% 3.12/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.12/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/1.04  
% 3.12/1.04  fof(f38,plain,(
% 3.12/1.04    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.12/1.04    inference(ennf_transformation,[],[f16])).
% 3.12/1.04  
% 3.12/1.04  fof(f74,plain,(
% 3.12/1.04    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.12/1.04    inference(cnf_transformation,[],[f38])).
% 3.12/1.04  
% 3.12/1.04  fof(f84,plain,(
% 3.12/1.04    r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5))),
% 3.12/1.04    inference(cnf_transformation,[],[f53])).
% 3.12/1.04  
% 3.12/1.04  fof(f13,axiom,(
% 3.12/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.12/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/1.04  
% 3.12/1.04  fof(f35,plain,(
% 3.12/1.04    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.12/1.04    inference(ennf_transformation,[],[f13])).
% 3.12/1.04  
% 3.12/1.04  fof(f71,plain,(
% 3.12/1.04    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.12/1.04    inference(cnf_transformation,[],[f35])).
% 3.12/1.04  
% 3.12/1.04  fof(f10,axiom,(
% 3.12/1.04    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 3.12/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/1.04  
% 3.12/1.04  fof(f31,plain,(
% 3.12/1.04    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 3.12/1.04    inference(ennf_transformation,[],[f10])).
% 3.12/1.04  
% 3.12/1.04  fof(f66,plain,(
% 3.12/1.04    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.12/1.04    inference(cnf_transformation,[],[f31])).
% 3.12/1.04  
% 3.12/1.04  fof(f9,axiom,(
% 3.12/1.04    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 3.12/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/1.04  
% 3.12/1.04  fof(f30,plain,(
% 3.12/1.04    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.12/1.04    inference(ennf_transformation,[],[f9])).
% 3.12/1.04  
% 3.12/1.04  fof(f45,plain,(
% 3.12/1.04    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.12/1.04    inference(nnf_transformation,[],[f30])).
% 3.12/1.04  
% 3.12/1.04  fof(f46,plain,(
% 3.12/1.04    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.12/1.04    inference(rectify,[],[f45])).
% 3.12/1.04  
% 3.12/1.04  fof(f47,plain,(
% 3.12/1.04    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))))),
% 3.12/1.04    introduced(choice_axiom,[])).
% 3.12/1.04  
% 3.12/1.04  fof(f48,plain,(
% 3.12/1.04    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.12/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f46,f47])).
% 3.12/1.04  
% 3.12/1.04  fof(f63,plain,(
% 3.12/1.04    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.12/1.04    inference(cnf_transformation,[],[f48])).
% 3.12/1.04  
% 3.12/1.04  fof(f11,axiom,(
% 3.12/1.04    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.12/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/1.04  
% 3.12/1.04  fof(f32,plain,(
% 3.12/1.04    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.12/1.04    inference(ennf_transformation,[],[f11])).
% 3.12/1.04  
% 3.12/1.04  fof(f33,plain,(
% 3.12/1.04    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.12/1.04    inference(flattening,[],[f32])).
% 3.12/1.04  
% 3.12/1.04  fof(f49,plain,(
% 3.12/1.04    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.12/1.04    inference(nnf_transformation,[],[f33])).
% 3.12/1.04  
% 3.12/1.04  fof(f50,plain,(
% 3.12/1.04    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.12/1.04    inference(flattening,[],[f49])).
% 3.12/1.04  
% 3.12/1.04  fof(f68,plain,(
% 3.12/1.04    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.12/1.04    inference(cnf_transformation,[],[f50])).
% 3.12/1.04  
% 3.12/1.04  fof(f81,plain,(
% 3.12/1.04    v1_funct_1(sK5)),
% 3.12/1.04    inference(cnf_transformation,[],[f53])).
% 3.12/1.04  
% 3.12/1.04  fof(f69,plain,(
% 3.12/1.04    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.12/1.04    inference(cnf_transformation,[],[f50])).
% 3.12/1.04  
% 3.12/1.04  fof(f86,plain,(
% 3.12/1.04    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.12/1.04    inference(equality_resolution,[],[f69])).
% 3.12/1.04  
% 3.12/1.04  fof(f67,plain,(
% 3.12/1.04    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.12/1.04    inference(cnf_transformation,[],[f50])).
% 3.12/1.04  
% 3.12/1.04  fof(f4,axiom,(
% 3.12/1.04    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.12/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/1.04  
% 3.12/1.04  fof(f57,plain,(
% 3.12/1.04    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.12/1.04    inference(cnf_transformation,[],[f4])).
% 3.12/1.04  
% 3.12/1.04  fof(f14,axiom,(
% 3.12/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 3.12/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/1.04  
% 3.12/1.04  fof(f36,plain,(
% 3.12/1.04    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.12/1.04    inference(ennf_transformation,[],[f14])).
% 3.12/1.04  
% 3.12/1.04  fof(f72,plain,(
% 3.12/1.04    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.12/1.04    inference(cnf_transformation,[],[f36])).
% 3.12/1.04  
% 3.12/1.04  fof(f3,axiom,(
% 3.12/1.04    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.12/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/1.04  
% 3.12/1.04  fof(f23,plain,(
% 3.12/1.04    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.12/1.04    inference(ennf_transformation,[],[f3])).
% 3.12/1.04  
% 3.12/1.04  fof(f56,plain,(
% 3.12/1.04    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.12/1.04    inference(cnf_transformation,[],[f23])).
% 3.12/1.04  
% 3.12/1.04  fof(f7,axiom,(
% 3.12/1.04    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.12/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/1.04  
% 3.12/1.04  fof(f20,plain,(
% 3.12/1.04    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 3.12/1.04    inference(unused_predicate_definition_removal,[],[f7])).
% 3.12/1.04  
% 3.12/1.04  fof(f27,plain,(
% 3.12/1.04    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 3.12/1.04    inference(ennf_transformation,[],[f20])).
% 3.12/1.04  
% 3.12/1.04  fof(f60,plain,(
% 3.12/1.04    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.12/1.04    inference(cnf_transformation,[],[f27])).
% 3.12/1.04  
% 3.12/1.04  fof(f12,axiom,(
% 3.12/1.04    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.12/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/1.04  
% 3.12/1.04  fof(f34,plain,(
% 3.12/1.04    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.12/1.04    inference(ennf_transformation,[],[f12])).
% 3.12/1.04  
% 3.12/1.04  fof(f70,plain,(
% 3.12/1.04    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.12/1.04    inference(cnf_transformation,[],[f34])).
% 3.12/1.04  
% 3.12/1.04  fof(f5,axiom,(
% 3.12/1.04    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.12/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/1.04  
% 3.12/1.04  fof(f24,plain,(
% 3.12/1.04    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.12/1.04    inference(ennf_transformation,[],[f5])).
% 3.12/1.04  
% 3.12/1.04  fof(f58,plain,(
% 3.12/1.04    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.12/1.04    inference(cnf_transformation,[],[f24])).
% 3.12/1.04  
% 3.12/1.04  fof(f85,plain,(
% 3.12/1.04    ( ! [X4] : (k1_funct_1(sK5,X4) != sK2 | ~m1_subset_1(X4,sK3)) )),
% 3.12/1.04    inference(cnf_transformation,[],[f53])).
% 3.12/1.04  
% 3.12/1.04  cnf(c_26,plain,
% 3.12/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 3.12/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.12/1.04      | k1_relset_1(X1,X2,X0) = X1
% 3.12/1.04      | k1_xboole_0 = X2 ),
% 3.12/1.04      inference(cnf_transformation,[],[f75]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_30,negated_conjecture,
% 3.12/1.04      ( v1_funct_2(sK5,sK3,sK4) ),
% 3.12/1.04      inference(cnf_transformation,[],[f82]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_644,plain,
% 3.12/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.12/1.04      | k1_relset_1(X1,X2,X0) = X1
% 3.12/1.04      | sK4 != X2
% 3.12/1.04      | sK3 != X1
% 3.12/1.04      | sK5 != X0
% 3.12/1.04      | k1_xboole_0 = X2 ),
% 3.12/1.04      inference(resolution_lifted,[status(thm)],[c_26,c_30]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_645,plain,
% 3.12/1.04      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.12/1.04      | k1_relset_1(sK3,sK4,sK5) = sK3
% 3.12/1.04      | k1_xboole_0 = sK4 ),
% 3.12/1.04      inference(unflattening,[status(thm)],[c_644]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_29,negated_conjecture,
% 3.12/1.04      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.12/1.04      inference(cnf_transformation,[],[f83]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_647,plain,
% 3.12/1.04      ( k1_relset_1(sK3,sK4,sK5) = sK3 | k1_xboole_0 = sK4 ),
% 3.12/1.04      inference(global_propositional_subsumption,
% 3.12/1.04                [status(thm)],
% 3.12/1.04                [c_645,c_29]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_1425,plain,
% 3.12/1.04      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.12/1.04      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_19,plain,
% 3.12/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.12/1.04      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.12/1.04      inference(cnf_transformation,[],[f73]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_1429,plain,
% 3.12/1.04      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.12/1.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.12/1.04      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_2224,plain,
% 3.12/1.04      ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
% 3.12/1.04      inference(superposition,[status(thm)],[c_1425,c_1429]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_2522,plain,
% 3.12/1.04      ( k1_relat_1(sK5) = sK3 | sK4 = k1_xboole_0 ),
% 3.12/1.04      inference(superposition,[status(thm)],[c_647,c_2224]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_20,plain,
% 3.12/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.12/1.04      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.12/1.04      inference(cnf_transformation,[],[f74]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_1428,plain,
% 3.12/1.04      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.12/1.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.12/1.04      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_2164,plain,
% 3.12/1.04      ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
% 3.12/1.04      inference(superposition,[status(thm)],[c_1425,c_1428]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_28,negated_conjecture,
% 3.12/1.04      ( r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5)) ),
% 3.12/1.04      inference(cnf_transformation,[],[f84]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_1426,plain,
% 3.12/1.04      ( r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5)) = iProver_top ),
% 3.12/1.04      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_2477,plain,
% 3.12/1.04      ( r2_hidden(sK2,k2_relat_1(sK5)) = iProver_top ),
% 3.12/1.04      inference(demodulation,[status(thm)],[c_2164,c_1426]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_17,plain,
% 3.12/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.12/1.04      | v1_relat_1(X0) ),
% 3.12/1.04      inference(cnf_transformation,[],[f71]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_1431,plain,
% 3.12/1.04      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.12/1.04      | v1_relat_1(X0) = iProver_top ),
% 3.12/1.04      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_2207,plain,
% 3.12/1.04      ( v1_relat_1(sK5) = iProver_top ),
% 3.12/1.04      inference(superposition,[status(thm)],[c_1425,c_1431]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_12,plain,
% 3.12/1.04      ( ~ v1_relat_1(X0)
% 3.12/1.04      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 3.12/1.04      inference(cnf_transformation,[],[f66]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_1432,plain,
% 3.12/1.04      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 3.12/1.04      | v1_relat_1(X0) != iProver_top ),
% 3.12/1.04      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_2473,plain,
% 3.12/1.04      ( k9_relat_1(sK5,k1_relat_1(sK5)) = k2_relat_1(sK5) ),
% 3.12/1.04      inference(superposition,[status(thm)],[c_2207,c_1432]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_10,plain,
% 3.12/1.04      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.12/1.04      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
% 3.12/1.04      | ~ v1_relat_1(X1) ),
% 3.12/1.04      inference(cnf_transformation,[],[f63]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_1434,plain,
% 3.12/1.04      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.12/1.04      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
% 3.12/1.04      | v1_relat_1(X1) != iProver_top ),
% 3.12/1.04      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_14,plain,
% 3.12/1.04      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.12/1.04      | ~ v1_funct_1(X2)
% 3.12/1.04      | ~ v1_relat_1(X2)
% 3.12/1.04      | k1_funct_1(X2,X0) = X1 ),
% 3.12/1.04      inference(cnf_transformation,[],[f68]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_31,negated_conjecture,
% 3.12/1.04      ( v1_funct_1(sK5) ),
% 3.12/1.04      inference(cnf_transformation,[],[f81]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_395,plain,
% 3.12/1.04      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.12/1.04      | ~ v1_relat_1(X2)
% 3.12/1.04      | k1_funct_1(X2,X0) = X1
% 3.12/1.04      | sK5 != X2 ),
% 3.12/1.04      inference(resolution_lifted,[status(thm)],[c_14,c_31]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_396,plain,
% 3.12/1.04      ( ~ r2_hidden(k4_tarski(X0,X1),sK5)
% 3.12/1.04      | ~ v1_relat_1(sK5)
% 3.12/1.04      | k1_funct_1(sK5,X0) = X1 ),
% 3.12/1.04      inference(unflattening,[status(thm)],[c_395]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_1423,plain,
% 3.12/1.04      ( k1_funct_1(sK5,X0) = X1
% 3.12/1.04      | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top
% 3.12/1.04      | v1_relat_1(sK5) != iProver_top ),
% 3.12/1.04      inference(predicate_to_equality,[status(thm)],[c_396]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_34,plain,
% 3.12/1.04      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.12/1.04      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_397,plain,
% 3.12/1.04      ( k1_funct_1(sK5,X0) = X1
% 3.12/1.04      | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top
% 3.12/1.04      | v1_relat_1(sK5) != iProver_top ),
% 3.12/1.04      inference(predicate_to_equality,[status(thm)],[c_396]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_1654,plain,
% 3.12/1.04      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.12/1.04      | v1_relat_1(sK5) ),
% 3.12/1.04      inference(instantiation,[status(thm)],[c_17]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_1655,plain,
% 3.12/1.04      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.12/1.04      | v1_relat_1(sK5) = iProver_top ),
% 3.12/1.04      inference(predicate_to_equality,[status(thm)],[c_1654]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_1712,plain,
% 3.12/1.04      ( r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top
% 3.12/1.04      | k1_funct_1(sK5,X0) = X1 ),
% 3.12/1.04      inference(global_propositional_subsumption,
% 3.12/1.04                [status(thm)],
% 3.12/1.04                [c_1423,c_34,c_397,c_1655]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_1713,plain,
% 3.12/1.04      ( k1_funct_1(sK5,X0) = X1
% 3.12/1.04      | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top ),
% 3.12/1.04      inference(renaming,[status(thm)],[c_1712]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_3101,plain,
% 3.12/1.04      ( k1_funct_1(sK5,sK1(X0,X1,sK5)) = X0
% 3.12/1.04      | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
% 3.12/1.04      | v1_relat_1(sK5) != iProver_top ),
% 3.12/1.04      inference(superposition,[status(thm)],[c_1434,c_1713]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_3449,plain,
% 3.12/1.04      ( r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
% 3.12/1.04      | k1_funct_1(sK5,sK1(X0,X1,sK5)) = X0 ),
% 3.12/1.04      inference(global_propositional_subsumption,
% 3.12/1.04                [status(thm)],
% 3.12/1.04                [c_3101,c_34,c_1655]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_3450,plain,
% 3.12/1.04      ( k1_funct_1(sK5,sK1(X0,X1,sK5)) = X0
% 3.12/1.04      | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top ),
% 3.12/1.04      inference(renaming,[status(thm)],[c_3449]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_3459,plain,
% 3.12/1.04      ( k1_funct_1(sK5,sK1(X0,k1_relat_1(sK5),sK5)) = X0
% 3.12/1.04      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 3.12/1.04      inference(superposition,[status(thm)],[c_2473,c_3450]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_5365,plain,
% 3.12/1.04      ( k1_funct_1(sK5,sK1(sK2,k1_relat_1(sK5),sK5)) = sK2 ),
% 3.12/1.04      inference(superposition,[status(thm)],[c_2477,c_3459]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_13,plain,
% 3.12/1.04      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.12/1.04      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.12/1.04      | ~ v1_funct_1(X1)
% 3.12/1.04      | ~ v1_relat_1(X1) ),
% 3.12/1.04      inference(cnf_transformation,[],[f86]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_425,plain,
% 3.12/1.04      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.12/1.04      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.12/1.04      | ~ v1_relat_1(X1)
% 3.12/1.04      | sK5 != X1 ),
% 3.12/1.04      inference(resolution_lifted,[status(thm)],[c_13,c_31]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_426,plain,
% 3.12/1.04      ( ~ r2_hidden(X0,k1_relat_1(sK5))
% 3.12/1.04      | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5)
% 3.12/1.04      | ~ v1_relat_1(sK5) ),
% 3.12/1.04      inference(unflattening,[status(thm)],[c_425]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_1421,plain,
% 3.12/1.04      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 3.12/1.04      | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top
% 3.12/1.04      | v1_relat_1(sK5) != iProver_top ),
% 3.12/1.04      inference(predicate_to_equality,[status(thm)],[c_426]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_427,plain,
% 3.12/1.04      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 3.12/1.04      | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top
% 3.12/1.04      | v1_relat_1(sK5) != iProver_top ),
% 3.12/1.04      inference(predicate_to_equality,[status(thm)],[c_426]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_1754,plain,
% 3.12/1.04      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top
% 3.12/1.04      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 3.12/1.04      inference(global_propositional_subsumption,
% 3.12/1.04                [status(thm)],
% 3.12/1.04                [c_1421,c_34,c_427,c_1655]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_1755,plain,
% 3.12/1.04      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 3.12/1.04      | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top ),
% 3.12/1.04      inference(renaming,[status(thm)],[c_1754]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_5404,plain,
% 3.12/1.04      ( r2_hidden(sK1(sK2,k1_relat_1(sK5),sK5),k1_relat_1(sK5)) != iProver_top
% 3.12/1.04      | r2_hidden(k4_tarski(sK1(sK2,k1_relat_1(sK5),sK5),sK2),sK5) = iProver_top ),
% 3.12/1.04      inference(superposition,[status(thm)],[c_5365,c_1755]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_35,plain,
% 3.12/1.04      ( r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5)) = iProver_top ),
% 3.12/1.04      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_1708,plain,
% 3.12/1.04      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.12/1.04      | k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
% 3.12/1.04      inference(instantiation,[status(thm)],[c_20]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_986,plain,( X0 = X0 ),theory(equality) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_1816,plain,
% 3.12/1.04      ( sK2 = sK2 ),
% 3.12/1.04      inference(instantiation,[status(thm)],[c_986]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_987,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_1921,plain,
% 3.12/1.04      ( X0 != X1
% 3.12/1.04      | X0 = k2_relset_1(sK3,sK4,sK5)
% 3.12/1.04      | k2_relset_1(sK3,sK4,sK5) != X1 ),
% 3.12/1.04      inference(instantiation,[status(thm)],[c_987]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_2287,plain,
% 3.12/1.04      ( X0 = k2_relset_1(sK3,sK4,sK5)
% 3.12/1.04      | X0 != k2_relat_1(sK5)
% 3.12/1.04      | k2_relset_1(sK3,sK4,sK5) != k2_relat_1(sK5) ),
% 3.12/1.04      inference(instantiation,[status(thm)],[c_1921]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_2388,plain,
% 3.12/1.04      ( k2_relset_1(sK3,sK4,sK5) != k2_relat_1(sK5)
% 3.12/1.04      | k9_relat_1(sK5,k1_relat_1(sK5)) = k2_relset_1(sK3,sK4,sK5)
% 3.12/1.04      | k9_relat_1(sK5,k1_relat_1(sK5)) != k2_relat_1(sK5) ),
% 3.12/1.04      inference(instantiation,[status(thm)],[c_2287]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_2389,plain,
% 3.12/1.04      ( ~ v1_relat_1(sK5)
% 3.12/1.04      | k9_relat_1(sK5,k1_relat_1(sK5)) = k2_relat_1(sK5) ),
% 3.12/1.04      inference(instantiation,[status(thm)],[c_12]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_988,plain,
% 3.12/1.04      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.12/1.04      theory(equality) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_1724,plain,
% 3.12/1.04      ( r2_hidden(X0,X1)
% 3.12/1.04      | ~ r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5))
% 3.12/1.04      | X1 != k2_relset_1(sK3,sK4,sK5)
% 3.12/1.04      | X0 != sK2 ),
% 3.12/1.04      inference(instantiation,[status(thm)],[c_988]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_1815,plain,
% 3.12/1.04      ( r2_hidden(sK2,X0)
% 3.12/1.04      | ~ r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5))
% 3.12/1.04      | X0 != k2_relset_1(sK3,sK4,sK5)
% 3.12/1.04      | sK2 != sK2 ),
% 3.12/1.04      inference(instantiation,[status(thm)],[c_1724]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_3180,plain,
% 3.12/1.04      ( ~ r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5))
% 3.12/1.04      | r2_hidden(sK2,k9_relat_1(sK5,k1_relat_1(sK5)))
% 3.12/1.04      | k9_relat_1(sK5,k1_relat_1(sK5)) != k2_relset_1(sK3,sK4,sK5)
% 3.12/1.04      | sK2 != sK2 ),
% 3.12/1.04      inference(instantiation,[status(thm)],[c_1815]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_3181,plain,
% 3.12/1.04      ( k9_relat_1(sK5,k1_relat_1(sK5)) != k2_relset_1(sK3,sK4,sK5)
% 3.12/1.04      | sK2 != sK2
% 3.12/1.04      | r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5)) != iProver_top
% 3.12/1.04      | r2_hidden(sK2,k9_relat_1(sK5,k1_relat_1(sK5))) = iProver_top ),
% 3.12/1.04      inference(predicate_to_equality,[status(thm)],[c_3180]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_2998,plain,
% 3.12/1.04      ( r2_hidden(k4_tarski(sK1(sK2,X0,X1),sK2),X1)
% 3.12/1.04      | ~ r2_hidden(sK2,k9_relat_1(X1,X0))
% 3.12/1.04      | ~ v1_relat_1(X1) ),
% 3.12/1.04      inference(instantiation,[status(thm)],[c_10]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_4010,plain,
% 3.12/1.04      ( r2_hidden(k4_tarski(sK1(sK2,k1_relat_1(sK5),sK5),sK2),sK5)
% 3.12/1.04      | ~ r2_hidden(sK2,k9_relat_1(sK5,k1_relat_1(sK5)))
% 3.12/1.04      | ~ v1_relat_1(sK5) ),
% 3.12/1.04      inference(instantiation,[status(thm)],[c_2998]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_4011,plain,
% 3.12/1.04      ( r2_hidden(k4_tarski(sK1(sK2,k1_relat_1(sK5),sK5),sK2),sK5) = iProver_top
% 3.12/1.04      | r2_hidden(sK2,k9_relat_1(sK5,k1_relat_1(sK5))) != iProver_top
% 3.12/1.04      | v1_relat_1(sK5) != iProver_top ),
% 3.12/1.04      inference(predicate_to_equality,[status(thm)],[c_4010]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_5506,plain,
% 3.12/1.04      ( r2_hidden(k4_tarski(sK1(sK2,k1_relat_1(sK5),sK5),sK2),sK5) = iProver_top ),
% 3.12/1.04      inference(global_propositional_subsumption,
% 3.12/1.04                [status(thm)],
% 3.12/1.04                [c_5404,c_29,c_34,c_35,c_1654,c_1655,c_1708,c_1816,
% 3.12/1.04                 c_2388,c_2389,c_3181,c_4011]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_15,plain,
% 3.12/1.04      ( r2_hidden(X0,k1_relat_1(X1))
% 3.12/1.04      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 3.12/1.04      | ~ v1_funct_1(X1)
% 3.12/1.04      | ~ v1_relat_1(X1) ),
% 3.12/1.04      inference(cnf_transformation,[],[f67]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_410,plain,
% 3.12/1.04      ( r2_hidden(X0,k1_relat_1(X1))
% 3.12/1.04      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 3.12/1.04      | ~ v1_relat_1(X1)
% 3.12/1.04      | sK5 != X1 ),
% 3.12/1.04      inference(resolution_lifted,[status(thm)],[c_15,c_31]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_411,plain,
% 3.12/1.04      ( r2_hidden(X0,k1_relat_1(sK5))
% 3.12/1.04      | ~ r2_hidden(k4_tarski(X0,X1),sK5)
% 3.12/1.04      | ~ v1_relat_1(sK5) ),
% 3.12/1.04      inference(unflattening,[status(thm)],[c_410]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_1422,plain,
% 3.12/1.04      ( r2_hidden(X0,k1_relat_1(sK5)) = iProver_top
% 3.12/1.04      | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top
% 3.12/1.04      | v1_relat_1(sK5) != iProver_top ),
% 3.12/1.04      inference(predicate_to_equality,[status(thm)],[c_411]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_412,plain,
% 3.12/1.04      ( r2_hidden(X0,k1_relat_1(sK5)) = iProver_top
% 3.12/1.04      | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top
% 3.12/1.04      | v1_relat_1(sK5) != iProver_top ),
% 3.12/1.04      inference(predicate_to_equality,[status(thm)],[c_411]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_1745,plain,
% 3.12/1.04      ( r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top
% 3.12/1.04      | r2_hidden(X0,k1_relat_1(sK5)) = iProver_top ),
% 3.12/1.04      inference(global_propositional_subsumption,
% 3.12/1.04                [status(thm)],
% 3.12/1.04                [c_1422,c_34,c_412,c_1655]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_1746,plain,
% 3.12/1.04      ( r2_hidden(X0,k1_relat_1(sK5)) = iProver_top
% 3.12/1.04      | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top ),
% 3.12/1.04      inference(renaming,[status(thm)],[c_1745]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_5515,plain,
% 3.12/1.04      ( r2_hidden(sK1(sK2,k1_relat_1(sK5),sK5),k1_relat_1(sK5)) = iProver_top ),
% 3.12/1.04      inference(superposition,[status(thm)],[c_5506,c_1746]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_5728,plain,
% 3.12/1.04      ( sK4 = k1_xboole_0
% 3.12/1.04      | r2_hidden(sK1(sK2,sK3,sK5),sK3) = iProver_top ),
% 3.12/1.04      inference(superposition,[status(thm)],[c_2522,c_5515]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_3,plain,
% 3.12/1.04      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.12/1.04      inference(cnf_transformation,[],[f57]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_109,plain,
% 3.12/1.04      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
% 3.12/1.04      inference(instantiation,[status(thm)],[c_3]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_990,plain,
% 3.12/1.04      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 3.12/1.04      theory(equality) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_1001,plain,
% 3.12/1.04      ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)
% 3.12/1.04      | k1_xboole_0 != k1_xboole_0 ),
% 3.12/1.04      inference(instantiation,[status(thm)],[c_990]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_1011,plain,
% 3.12/1.04      ( k1_xboole_0 = k1_xboole_0 ),
% 3.12/1.04      inference(instantiation,[status(thm)],[c_986]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_18,plain,
% 3.12/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.12/1.04      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 3.12/1.04      inference(cnf_transformation,[],[f72]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_1694,plain,
% 3.12/1.04      ( m1_subset_1(k2_relset_1(sK3,sK4,sK5),k1_zfmisc_1(sK4))
% 3.12/1.04      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.12/1.04      inference(instantiation,[status(thm)],[c_18]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_2,plain,
% 3.12/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.12/1.04      | ~ r2_hidden(X2,X0)
% 3.12/1.04      | r2_hidden(X2,X1) ),
% 3.12/1.04      inference(cnf_transformation,[],[f56]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_1678,plain,
% 3.12/1.04      ( ~ m1_subset_1(k2_relset_1(sK3,sK4,sK5),k1_zfmisc_1(X0))
% 3.12/1.04      | r2_hidden(sK2,X0)
% 3.12/1.04      | ~ r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5)) ),
% 3.12/1.04      inference(instantiation,[status(thm)],[c_2]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_1802,plain,
% 3.12/1.04      ( ~ m1_subset_1(k2_relset_1(sK3,sK4,sK5),k1_zfmisc_1(sK4))
% 3.12/1.04      | ~ r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5))
% 3.12/1.04      | r2_hidden(sK2,sK4) ),
% 3.12/1.04      inference(instantiation,[status(thm)],[c_1678]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_1891,plain,
% 3.12/1.04      ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
% 3.12/1.04      | r2_hidden(sK2,X0)
% 3.12/1.04      | ~ r2_hidden(sK2,sK4) ),
% 3.12/1.04      inference(instantiation,[status(thm)],[c_2]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_1893,plain,
% 3.12/1.04      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))
% 3.12/1.04      | ~ r2_hidden(sK2,sK4)
% 3.12/1.04      | r2_hidden(sK2,k1_xboole_0) ),
% 3.12/1.04      inference(instantiation,[status(thm)],[c_1891]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_989,plain,
% 3.12/1.04      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.12/1.04      theory(equality) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_1734,plain,
% 3.12/1.04      ( m1_subset_1(X0,X1)
% 3.12/1.04      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
% 3.12/1.04      | X1 != k1_zfmisc_1(X2)
% 3.12/1.04      | X0 != k1_xboole_0 ),
% 3.12/1.04      inference(instantiation,[status(thm)],[c_989]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_2044,plain,
% 3.12/1.04      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.12/1.04      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
% 3.12/1.04      | X0 != k1_xboole_0
% 3.12/1.04      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 3.12/1.04      inference(instantiation,[status(thm)],[c_1734]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_2667,plain,
% 3.12/1.04      ( m1_subset_1(sK4,k1_zfmisc_1(X0))
% 3.12/1.04      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
% 3.12/1.04      | k1_zfmisc_1(X0) != k1_zfmisc_1(X0)
% 3.12/1.04      | sK4 != k1_xboole_0 ),
% 3.12/1.04      inference(instantiation,[status(thm)],[c_2044]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_2669,plain,
% 3.12/1.04      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))
% 3.12/1.04      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 3.12/1.04      | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
% 3.12/1.04      | sK4 != k1_xboole_0 ),
% 3.12/1.04      inference(instantiation,[status(thm)],[c_2667]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_2888,plain,
% 3.12/1.04      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) ),
% 3.12/1.04      inference(instantiation,[status(thm)],[c_3]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_6,plain,
% 3.12/1.04      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.12/1.04      inference(cnf_transformation,[],[f60]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_16,plain,
% 3.12/1.04      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.12/1.04      inference(cnf_transformation,[],[f70]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_366,plain,
% 3.12/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r2_hidden(X1,X0) ),
% 3.12/1.04      inference(resolution,[status(thm)],[c_6,c_16]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_2989,plain,
% 3.12/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2)) | ~ r2_hidden(sK2,X0) ),
% 3.12/1.04      inference(instantiation,[status(thm)],[c_366]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_2991,plain,
% 3.12/1.04      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2))
% 3.12/1.04      | ~ r2_hidden(sK2,k1_xboole_0) ),
% 3.12/1.04      inference(instantiation,[status(thm)],[c_2989]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_6084,plain,
% 3.12/1.04      ( r2_hidden(sK1(sK2,sK3,sK5),sK3) = iProver_top ),
% 3.12/1.04      inference(global_propositional_subsumption,
% 3.12/1.04                [status(thm)],
% 3.12/1.04                [c_5728,c_29,c_28,c_109,c_1001,c_1011,c_1694,c_1802,
% 3.12/1.04                 c_1893,c_2669,c_2888,c_2991]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_4,plain,
% 3.12/1.04      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.12/1.04      inference(cnf_transformation,[],[f58]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_1439,plain,
% 3.12/1.04      ( m1_subset_1(X0,X1) = iProver_top
% 3.12/1.04      | r2_hidden(X0,X1) != iProver_top ),
% 3.12/1.04      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_6090,plain,
% 3.12/1.04      ( m1_subset_1(sK1(sK2,sK3,sK5),sK3) = iProver_top ),
% 3.12/1.04      inference(superposition,[status(thm)],[c_6084,c_1439]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_3218,plain,
% 3.12/1.04      ( k9_relat_1(sK5,sK3) = k2_relat_1(sK5) | sK4 = k1_xboole_0 ),
% 3.12/1.04      inference(superposition,[status(thm)],[c_2522,c_2473]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_3667,plain,
% 3.12/1.04      ( k9_relat_1(sK5,sK3) = k2_relat_1(sK5) ),
% 3.12/1.04      inference(global_propositional_subsumption,
% 3.12/1.04                [status(thm)],
% 3.12/1.04                [c_3218,c_29,c_28,c_109,c_1001,c_1011,c_1694,c_1802,
% 3.12/1.04                 c_1893,c_2669,c_2888,c_2991]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_3670,plain,
% 3.12/1.04      ( k1_funct_1(sK5,sK1(X0,sK3,sK5)) = X0
% 3.12/1.04      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 3.12/1.04      inference(superposition,[status(thm)],[c_3667,c_3450]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_4661,plain,
% 3.12/1.04      ( k1_funct_1(sK5,sK1(sK2,sK3,sK5)) = sK2 ),
% 3.12/1.04      inference(superposition,[status(thm)],[c_2477,c_3670]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_27,negated_conjecture,
% 3.12/1.04      ( ~ m1_subset_1(X0,sK3) | k1_funct_1(sK5,X0) != sK2 ),
% 3.12/1.04      inference(cnf_transformation,[],[f85]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_1427,plain,
% 3.12/1.04      ( k1_funct_1(sK5,X0) != sK2 | m1_subset_1(X0,sK3) != iProver_top ),
% 3.12/1.04      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(c_5084,plain,
% 3.12/1.04      ( m1_subset_1(sK1(sK2,sK3,sK5),sK3) != iProver_top ),
% 3.12/1.04      inference(superposition,[status(thm)],[c_4661,c_1427]) ).
% 3.12/1.04  
% 3.12/1.04  cnf(contradiction,plain,
% 3.12/1.04      ( $false ),
% 3.12/1.04      inference(minisat,[status(thm)],[c_6090,c_5084]) ).
% 3.12/1.04  
% 3.12/1.04  
% 3.12/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 3.12/1.04  
% 3.12/1.04  ------                               Statistics
% 3.12/1.04  
% 3.12/1.04  ------ General
% 3.12/1.04  
% 3.12/1.04  abstr_ref_over_cycles:                  0
% 3.12/1.04  abstr_ref_under_cycles:                 0
% 3.12/1.04  gc_basic_clause_elim:                   0
% 3.12/1.04  forced_gc_time:                         0
% 3.12/1.04  parsing_time:                           0.012
% 3.12/1.04  unif_index_cands_time:                  0.
% 3.12/1.04  unif_index_add_time:                    0.
% 3.12/1.04  orderings_time:                         0.
% 3.12/1.04  out_proof_time:                         0.01
% 3.12/1.04  total_time:                             0.236
% 3.12/1.04  num_of_symbols:                         54
% 3.12/1.04  num_of_terms:                           5263
% 3.12/1.04  
% 3.12/1.04  ------ Preprocessing
% 3.12/1.04  
% 3.12/1.04  num_of_splits:                          0
% 3.12/1.04  num_of_split_atoms:                     0
% 3.12/1.04  num_of_reused_defs:                     0
% 3.12/1.04  num_eq_ax_congr_red:                    30
% 3.12/1.04  num_of_sem_filtered_clauses:            1
% 3.12/1.04  num_of_subtypes:                        0
% 3.12/1.04  monotx_restored_types:                  0
% 3.12/1.04  sat_num_of_epr_types:                   0
% 3.12/1.04  sat_num_of_non_cyclic_types:            0
% 3.12/1.04  sat_guarded_non_collapsed_types:        0
% 3.12/1.04  num_pure_diseq_elim:                    0
% 3.12/1.04  simp_replaced_by:                       0
% 3.12/1.04  res_preprocessed:                       137
% 3.12/1.04  prep_upred:                             0
% 3.12/1.04  prep_unflattend:                        44
% 3.12/1.04  smt_new_axioms:                         0
% 3.12/1.04  pred_elim_cands:                        4
% 3.12/1.04  pred_elim:                              3
% 3.12/1.04  pred_elim_cl:                           6
% 3.12/1.04  pred_elim_cycles:                       8
% 3.12/1.04  merged_defs:                            0
% 3.12/1.04  merged_defs_ncl:                        0
% 3.12/1.04  bin_hyper_res:                          0
% 3.12/1.04  prep_cycles:                            4
% 3.12/1.04  pred_elim_time:                         0.021
% 3.12/1.04  splitting_time:                         0.
% 3.12/1.04  sem_filter_time:                        0.
% 3.12/1.04  monotx_time:                            0.
% 3.12/1.04  subtype_inf_time:                       0.
% 3.12/1.04  
% 3.12/1.04  ------ Problem properties
% 3.12/1.04  
% 3.12/1.04  clauses:                                26
% 3.12/1.04  conjectures:                            3
% 3.12/1.04  epr:                                    3
% 3.12/1.04  horn:                                   23
% 3.12/1.04  ground:                                 5
% 3.12/1.04  unary:                                  4
% 3.12/1.04  binary:                                 10
% 3.12/1.04  lits:                                   63
% 3.12/1.04  lits_eq:                                12
% 3.12/1.04  fd_pure:                                0
% 3.12/1.04  fd_pseudo:                              0
% 3.12/1.04  fd_cond:                                0
% 3.12/1.04  fd_pseudo_cond:                         1
% 3.12/1.04  ac_symbols:                             0
% 3.12/1.04  
% 3.12/1.04  ------ Propositional Solver
% 3.12/1.04  
% 3.12/1.04  prop_solver_calls:                      29
% 3.12/1.04  prop_fast_solver_calls:                 969
% 3.12/1.04  smt_solver_calls:                       0
% 3.12/1.04  smt_fast_solver_calls:                  0
% 3.12/1.04  prop_num_of_clauses:                    2217
% 3.12/1.04  prop_preprocess_simplified:             6167
% 3.12/1.04  prop_fo_subsumed:                       15
% 3.12/1.04  prop_solver_time:                       0.
% 3.12/1.04  smt_solver_time:                        0.
% 3.12/1.04  smt_fast_solver_time:                   0.
% 3.12/1.04  prop_fast_solver_time:                  0.
% 3.12/1.04  prop_unsat_core_time:                   0.
% 3.12/1.04  
% 3.12/1.04  ------ QBF
% 3.12/1.04  
% 3.12/1.04  qbf_q_res:                              0
% 3.12/1.04  qbf_num_tautologies:                    0
% 3.12/1.04  qbf_prep_cycles:                        0
% 3.12/1.04  
% 3.12/1.04  ------ BMC1
% 3.12/1.04  
% 3.12/1.04  bmc1_current_bound:                     -1
% 3.12/1.04  bmc1_last_solved_bound:                 -1
% 3.12/1.04  bmc1_unsat_core_size:                   -1
% 3.12/1.04  bmc1_unsat_core_parents_size:           -1
% 3.12/1.04  bmc1_merge_next_fun:                    0
% 3.12/1.04  bmc1_unsat_core_clauses_time:           0.
% 3.12/1.04  
% 3.12/1.04  ------ Instantiation
% 3.12/1.04  
% 3.12/1.04  inst_num_of_clauses:                    596
% 3.12/1.04  inst_num_in_passive:                    47
% 3.12/1.04  inst_num_in_active:                     401
% 3.12/1.04  inst_num_in_unprocessed:                148
% 3.12/1.04  inst_num_of_loops:                      470
% 3.12/1.04  inst_num_of_learning_restarts:          0
% 3.12/1.04  inst_num_moves_active_passive:          65
% 3.12/1.04  inst_lit_activity:                      0
% 3.12/1.04  inst_lit_activity_moves:                0
% 3.12/1.04  inst_num_tautologies:                   0
% 3.12/1.04  inst_num_prop_implied:                  0
% 3.12/1.04  inst_num_existing_simplified:           0
% 3.12/1.04  inst_num_eq_res_simplified:             0
% 3.12/1.04  inst_num_child_elim:                    0
% 3.12/1.04  inst_num_of_dismatching_blockings:      248
% 3.12/1.04  inst_num_of_non_proper_insts:           625
% 3.12/1.04  inst_num_of_duplicates:                 0
% 3.12/1.04  inst_inst_num_from_inst_to_res:         0
% 3.12/1.04  inst_dismatching_checking_time:         0.
% 3.12/1.04  
% 3.12/1.04  ------ Resolution
% 3.12/1.04  
% 3.12/1.04  res_num_of_clauses:                     0
% 3.12/1.04  res_num_in_passive:                     0
% 3.12/1.04  res_num_in_active:                      0
% 3.12/1.04  res_num_of_loops:                       141
% 3.12/1.04  res_forward_subset_subsumed:            87
% 3.12/1.04  res_backward_subset_subsumed:           0
% 3.12/1.04  res_forward_subsumed:                   0
% 3.12/1.04  res_backward_subsumed:                  0
% 3.12/1.04  res_forward_subsumption_resolution:     0
% 3.12/1.04  res_backward_subsumption_resolution:    0
% 3.12/1.04  res_clause_to_clause_subsumption:       409
% 3.12/1.04  res_orphan_elimination:                 0
% 3.12/1.04  res_tautology_del:                      103
% 3.12/1.04  res_num_eq_res_simplified:              0
% 3.12/1.04  res_num_sel_changes:                    0
% 3.12/1.04  res_moves_from_active_to_pass:          0
% 3.12/1.04  
% 3.12/1.04  ------ Superposition
% 3.12/1.04  
% 3.12/1.04  sup_time_total:                         0.
% 3.12/1.04  sup_time_generating:                    0.
% 3.12/1.04  sup_time_sim_full:                      0.
% 3.12/1.04  sup_time_sim_immed:                     0.
% 3.12/1.04  
% 3.12/1.04  sup_num_of_clauses:                     170
% 3.12/1.04  sup_num_in_active:                      89
% 3.12/1.04  sup_num_in_passive:                     81
% 3.12/1.04  sup_num_of_loops:                       92
% 3.12/1.04  sup_fw_superposition:                   100
% 3.12/1.04  sup_bw_superposition:                   101
% 3.12/1.04  sup_immediate_simplified:               34
% 3.12/1.04  sup_given_eliminated:                   1
% 3.12/1.04  comparisons_done:                       0
% 3.12/1.04  comparisons_avoided:                    3
% 3.12/1.04  
% 3.12/1.04  ------ Simplifications
% 3.12/1.04  
% 3.12/1.04  
% 3.12/1.04  sim_fw_subset_subsumed:                 32
% 3.12/1.04  sim_bw_subset_subsumed:                 1
% 3.12/1.04  sim_fw_subsumed:                        1
% 3.12/1.04  sim_bw_subsumed:                        2
% 3.12/1.04  sim_fw_subsumption_res:                 1
% 3.12/1.04  sim_bw_subsumption_res:                 0
% 3.12/1.04  sim_tautology_del:                      6
% 3.12/1.04  sim_eq_tautology_del:                   1
% 3.12/1.04  sim_eq_res_simp:                        0
% 3.12/1.04  sim_fw_demodulated:                     0
% 3.12/1.04  sim_bw_demodulated:                     3
% 3.12/1.04  sim_light_normalised:                   0
% 3.12/1.04  sim_joinable_taut:                      0
% 3.12/1.04  sim_joinable_simp:                      0
% 3.12/1.04  sim_ac_normalised:                      0
% 3.12/1.04  sim_smt_subsumption:                    0
% 3.12/1.04  
%------------------------------------------------------------------------------
