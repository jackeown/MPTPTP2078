%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:02 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 508 expanded)
%              Number of clauses        :   71 ( 179 expanded)
%              Number of leaves         :   15 (  93 expanded)
%              Depth                    :   23
%              Number of atoms          :  394 (2108 expanded)
%              Number of equality atoms :  153 ( 529 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ( m1_subset_1(X4,X1)
             => k1_funct_1(X3,X4) != X0 )
          & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f31])).

fof(f40,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( k1_funct_1(X3,X4) != X0
            | ~ m1_subset_1(X4,X1) )
        & r2_hidden(X0,k2_relset_1(X1,X2,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
   => ( ! [X4] :
          ( k1_funct_1(sK4,X4) != sK1
          | ~ m1_subset_1(X4,sK2) )
      & r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4))
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK4,sK2,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ! [X4] :
        ( k1_funct_1(sK4,X4) != sK1
        | ~ m1_subset_1(X4,sK2) )
    & r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f32,f40])).

fof(f66,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f67,plain,(
    r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f41])).

fof(f12,axiom,(
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

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f65,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK0(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
        & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
            & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f64,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f68,plain,(
    ! [X4] :
      ( k1_funct_1(sK4,X4) != sK1
      | ~ m1_subset_1(X4,sK2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k2_relat_1(X1))
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,k2_relat_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,k2_relat_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,k2_relat_1(X1))
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2003,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2006,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2391,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2003,c_2006])).

cnf(c_23,negated_conjecture,
    ( r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2004,plain,
    ( r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2430,plain,
    ( r2_hidden(sK1,k2_relat_1(sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2391,c_2004])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_973,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X2
    | sK2 != X1
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_25])).

cnf(c_974,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_973])).

cnf(c_976,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_974,c_24])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2007,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2639,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2003,c_2007])).

cnf(c_2803,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_976,c_2639])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2008,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2345,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2003,c_2008])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2009,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2394,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2345,c_2009])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2011,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_10,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_345,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_26])).

cnf(c_346,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK4)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_345])).

cnf(c_2000,plain,
    ( k1_funct_1(sK4,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_346])).

cnf(c_29,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_347,plain,
    ( k1_funct_1(sK4,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_346])).

cnf(c_2163,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2164,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2163])).

cnf(c_2190,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top
    | k1_funct_1(sK4,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2000,c_29,c_347,c_2164])).

cnf(c_2191,plain,
    ( k1_funct_1(sK4,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_2190])).

cnf(c_2777,plain,
    ( k1_funct_1(sK4,sK0(X0,X1,sK4)) = X0
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2011,c_2191])).

cnf(c_2967,plain,
    ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | k1_funct_1(sK4,sK0(X0,X1,sK4)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2777,c_29,c_2164])).

cnf(c_2968,plain,
    ( k1_funct_1(sK4,sK0(X0,X1,sK4)) = X0
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2967])).

cnf(c_2977,plain,
    ( k1_funct_1(sK4,sK0(X0,k1_relat_1(sK4),sK4)) = X0
    | r2_hidden(X0,k2_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2394,c_2968])).

cnf(c_3514,plain,
    ( k1_funct_1(sK4,sK0(sK1,k1_relat_1(sK4),sK4)) = sK1 ),
    inference(superposition,[status(thm)],[c_2430,c_2977])).

cnf(c_22,negated_conjecture,
    ( ~ m1_subset_1(X0,sK2)
    | k1_funct_1(sK4,X0) != sK1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2005,plain,
    ( k1_funct_1(sK4,X0) != sK1
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3631,plain,
    ( m1_subset_1(sK0(sK1,k1_relat_1(sK4),sK4),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3514,c_2005])).

cnf(c_3660,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK0(sK1,sK2,sK4),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2803,c_3631])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2010,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2885,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | r2_hidden(sK0(X0,X1,sK4),sK2) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2803,c_2010])).

cnf(c_3390,plain,
    ( r2_hidden(sK0(X0,X1,sK4),sK2) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2885,c_29,c_2164])).

cnf(c_3391,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | r2_hidden(sK0(X0,X1,sK4),sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_3390])).

cnf(c_2,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2014,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3399,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK0(X0,X1,sK4),sK2) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3391,c_2014])).

cnf(c_3844,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK1,k9_relat_1(sK4,k1_relat_1(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3399,c_3631])).

cnf(c_3845,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK1,k2_relat_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3844,c_2394])).

cnf(c_3953,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3660,c_2430,c_3845])).

cnf(c_13,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_8,plain,
    ( ~ v5_relat_1(X0,X1)
    | r2_hidden(X2,X1)
    | ~ r2_hidden(X2,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_321,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X3,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_13,c_8])).

cnf(c_325,plain,
    ( ~ r2_hidden(X3,k2_relat_1(X0))
    | r2_hidden(X3,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_321,c_12])).

cnf(c_326,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X3,k2_relat_1(X0)) ),
    inference(renaming,[status(thm)],[c_325])).

cnf(c_2001,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r2_hidden(X3,X2) = iProver_top
    | r2_hidden(X3,k2_relat_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_326])).

cnf(c_2632,plain,
    ( r2_hidden(X0,k2_relat_1(sK4)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2003,c_2001])).

cnf(c_3962,plain,
    ( r2_hidden(X0,k2_relat_1(sK4)) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3953,c_2632])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_310,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_311,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_310])).

cnf(c_312,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_311])).

cnf(c_4183,plain,
    ( r2_hidden(X0,k2_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3962,c_312])).

cnf(c_4192,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_2430,c_4183])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:38:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.54/1.05  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.05  
% 2.54/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.54/1.05  
% 2.54/1.05  ------  iProver source info
% 2.54/1.05  
% 2.54/1.05  git: date: 2020-06-30 10:37:57 +0100
% 2.54/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.54/1.05  git: non_committed_changes: false
% 2.54/1.05  git: last_make_outside_of_git: false
% 2.54/1.05  
% 2.54/1.05  ------ 
% 2.54/1.05  
% 2.54/1.05  ------ Input Options
% 2.54/1.05  
% 2.54/1.05  --out_options                           all
% 2.54/1.05  --tptp_safe_out                         true
% 2.54/1.05  --problem_path                          ""
% 2.54/1.05  --include_path                          ""
% 2.54/1.05  --clausifier                            res/vclausify_rel
% 2.54/1.05  --clausifier_options                    --mode clausify
% 2.54/1.05  --stdin                                 false
% 2.54/1.05  --stats_out                             all
% 2.54/1.05  
% 2.54/1.05  ------ General Options
% 2.54/1.05  
% 2.54/1.05  --fof                                   false
% 2.54/1.05  --time_out_real                         305.
% 2.54/1.05  --time_out_virtual                      -1.
% 2.54/1.05  --symbol_type_check                     false
% 2.54/1.05  --clausify_out                          false
% 2.54/1.05  --sig_cnt_out                           false
% 2.54/1.05  --trig_cnt_out                          false
% 2.54/1.05  --trig_cnt_out_tolerance                1.
% 2.54/1.05  --trig_cnt_out_sk_spl                   false
% 2.54/1.05  --abstr_cl_out                          false
% 2.54/1.05  
% 2.54/1.05  ------ Global Options
% 2.54/1.05  
% 2.54/1.05  --schedule                              default
% 2.54/1.05  --add_important_lit                     false
% 2.54/1.05  --prop_solver_per_cl                    1000
% 2.54/1.05  --min_unsat_core                        false
% 2.54/1.05  --soft_assumptions                      false
% 2.54/1.05  --soft_lemma_size                       3
% 2.54/1.05  --prop_impl_unit_size                   0
% 2.54/1.05  --prop_impl_unit                        []
% 2.54/1.05  --share_sel_clauses                     true
% 2.54/1.05  --reset_solvers                         false
% 2.54/1.05  --bc_imp_inh                            [conj_cone]
% 2.54/1.05  --conj_cone_tolerance                   3.
% 2.54/1.05  --extra_neg_conj                        none
% 2.54/1.05  --large_theory_mode                     true
% 2.54/1.05  --prolific_symb_bound                   200
% 2.54/1.05  --lt_threshold                          2000
% 2.54/1.05  --clause_weak_htbl                      true
% 2.54/1.05  --gc_record_bc_elim                     false
% 2.54/1.05  
% 2.54/1.05  ------ Preprocessing Options
% 2.54/1.05  
% 2.54/1.05  --preprocessing_flag                    true
% 2.54/1.05  --time_out_prep_mult                    0.1
% 2.54/1.05  --splitting_mode                        input
% 2.54/1.05  --splitting_grd                         true
% 2.54/1.05  --splitting_cvd                         false
% 2.54/1.05  --splitting_cvd_svl                     false
% 2.54/1.05  --splitting_nvd                         32
% 2.54/1.05  --sub_typing                            true
% 2.54/1.05  --prep_gs_sim                           true
% 2.54/1.05  --prep_unflatten                        true
% 2.54/1.05  --prep_res_sim                          true
% 2.54/1.05  --prep_upred                            true
% 2.54/1.05  --prep_sem_filter                       exhaustive
% 2.54/1.05  --prep_sem_filter_out                   false
% 2.54/1.05  --pred_elim                             true
% 2.54/1.05  --res_sim_input                         true
% 2.54/1.05  --eq_ax_congr_red                       true
% 2.54/1.05  --pure_diseq_elim                       true
% 2.54/1.05  --brand_transform                       false
% 2.54/1.05  --non_eq_to_eq                          false
% 2.54/1.05  --prep_def_merge                        true
% 2.54/1.05  --prep_def_merge_prop_impl              false
% 2.54/1.05  --prep_def_merge_mbd                    true
% 2.54/1.05  --prep_def_merge_tr_red                 false
% 2.54/1.05  --prep_def_merge_tr_cl                  false
% 2.54/1.05  --smt_preprocessing                     true
% 2.54/1.05  --smt_ac_axioms                         fast
% 2.54/1.05  --preprocessed_out                      false
% 2.54/1.05  --preprocessed_stats                    false
% 2.54/1.05  
% 2.54/1.05  ------ Abstraction refinement Options
% 2.54/1.05  
% 2.54/1.05  --abstr_ref                             []
% 2.54/1.05  --abstr_ref_prep                        false
% 2.54/1.05  --abstr_ref_until_sat                   false
% 2.54/1.05  --abstr_ref_sig_restrict                funpre
% 2.54/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 2.54/1.05  --abstr_ref_under                       []
% 2.54/1.05  
% 2.54/1.05  ------ SAT Options
% 2.54/1.05  
% 2.54/1.05  --sat_mode                              false
% 2.54/1.05  --sat_fm_restart_options                ""
% 2.54/1.05  --sat_gr_def                            false
% 2.54/1.05  --sat_epr_types                         true
% 2.54/1.05  --sat_non_cyclic_types                  false
% 2.54/1.05  --sat_finite_models                     false
% 2.54/1.05  --sat_fm_lemmas                         false
% 2.54/1.05  --sat_fm_prep                           false
% 2.54/1.05  --sat_fm_uc_incr                        true
% 2.54/1.05  --sat_out_model                         small
% 2.54/1.05  --sat_out_clauses                       false
% 2.54/1.05  
% 2.54/1.05  ------ QBF Options
% 2.54/1.05  
% 2.54/1.05  --qbf_mode                              false
% 2.54/1.05  --qbf_elim_univ                         false
% 2.54/1.05  --qbf_dom_inst                          none
% 2.54/1.05  --qbf_dom_pre_inst                      false
% 2.54/1.05  --qbf_sk_in                             false
% 2.54/1.05  --qbf_pred_elim                         true
% 2.54/1.05  --qbf_split                             512
% 2.54/1.05  
% 2.54/1.05  ------ BMC1 Options
% 2.54/1.05  
% 2.54/1.05  --bmc1_incremental                      false
% 2.54/1.05  --bmc1_axioms                           reachable_all
% 2.54/1.05  --bmc1_min_bound                        0
% 2.54/1.05  --bmc1_max_bound                        -1
% 2.54/1.05  --bmc1_max_bound_default                -1
% 2.54/1.05  --bmc1_symbol_reachability              true
% 2.54/1.05  --bmc1_property_lemmas                  false
% 2.54/1.05  --bmc1_k_induction                      false
% 2.54/1.05  --bmc1_non_equiv_states                 false
% 2.54/1.05  --bmc1_deadlock                         false
% 2.54/1.05  --bmc1_ucm                              false
% 2.54/1.05  --bmc1_add_unsat_core                   none
% 2.54/1.05  --bmc1_unsat_core_children              false
% 2.54/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 2.54/1.05  --bmc1_out_stat                         full
% 2.54/1.05  --bmc1_ground_init                      false
% 2.54/1.05  --bmc1_pre_inst_next_state              false
% 2.54/1.05  --bmc1_pre_inst_state                   false
% 2.54/1.05  --bmc1_pre_inst_reach_state             false
% 2.54/1.05  --bmc1_out_unsat_core                   false
% 2.54/1.05  --bmc1_aig_witness_out                  false
% 2.54/1.05  --bmc1_verbose                          false
% 2.54/1.05  --bmc1_dump_clauses_tptp                false
% 2.54/1.05  --bmc1_dump_unsat_core_tptp             false
% 2.54/1.05  --bmc1_dump_file                        -
% 2.54/1.05  --bmc1_ucm_expand_uc_limit              128
% 2.54/1.05  --bmc1_ucm_n_expand_iterations          6
% 2.54/1.05  --bmc1_ucm_extend_mode                  1
% 2.54/1.05  --bmc1_ucm_init_mode                    2
% 2.54/1.05  --bmc1_ucm_cone_mode                    none
% 2.54/1.05  --bmc1_ucm_reduced_relation_type        0
% 2.54/1.05  --bmc1_ucm_relax_model                  4
% 2.54/1.05  --bmc1_ucm_full_tr_after_sat            true
% 2.54/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 2.54/1.05  --bmc1_ucm_layered_model                none
% 2.54/1.05  --bmc1_ucm_max_lemma_size               10
% 2.54/1.05  
% 2.54/1.05  ------ AIG Options
% 2.54/1.05  
% 2.54/1.05  --aig_mode                              false
% 2.54/1.05  
% 2.54/1.05  ------ Instantiation Options
% 2.54/1.05  
% 2.54/1.05  --instantiation_flag                    true
% 2.54/1.05  --inst_sos_flag                         false
% 2.54/1.05  --inst_sos_phase                        true
% 2.54/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.54/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.54/1.05  --inst_lit_sel_side                     num_symb
% 2.54/1.05  --inst_solver_per_active                1400
% 2.54/1.05  --inst_solver_calls_frac                1.
% 2.54/1.05  --inst_passive_queue_type               priority_queues
% 2.54/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.54/1.05  --inst_passive_queues_freq              [25;2]
% 2.54/1.05  --inst_dismatching                      true
% 2.54/1.05  --inst_eager_unprocessed_to_passive     true
% 2.54/1.05  --inst_prop_sim_given                   true
% 2.54/1.05  --inst_prop_sim_new                     false
% 2.54/1.05  --inst_subs_new                         false
% 2.54/1.05  --inst_eq_res_simp                      false
% 2.54/1.05  --inst_subs_given                       false
% 2.54/1.05  --inst_orphan_elimination               true
% 2.54/1.05  --inst_learning_loop_flag               true
% 2.54/1.05  --inst_learning_start                   3000
% 2.54/1.05  --inst_learning_factor                  2
% 2.54/1.05  --inst_start_prop_sim_after_learn       3
% 2.54/1.05  --inst_sel_renew                        solver
% 2.54/1.05  --inst_lit_activity_flag                true
% 2.54/1.05  --inst_restr_to_given                   false
% 2.54/1.05  --inst_activity_threshold               500
% 2.54/1.05  --inst_out_proof                        true
% 2.54/1.05  
% 2.54/1.05  ------ Resolution Options
% 2.54/1.05  
% 2.54/1.05  --resolution_flag                       true
% 2.54/1.05  --res_lit_sel                           adaptive
% 2.54/1.05  --res_lit_sel_side                      none
% 2.54/1.05  --res_ordering                          kbo
% 2.54/1.05  --res_to_prop_solver                    active
% 2.54/1.05  --res_prop_simpl_new                    false
% 2.54/1.05  --res_prop_simpl_given                  true
% 2.54/1.05  --res_passive_queue_type                priority_queues
% 2.54/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.54/1.05  --res_passive_queues_freq               [15;5]
% 2.54/1.05  --res_forward_subs                      full
% 2.54/1.05  --res_backward_subs                     full
% 2.54/1.05  --res_forward_subs_resolution           true
% 2.54/1.05  --res_backward_subs_resolution          true
% 2.54/1.05  --res_orphan_elimination                true
% 2.54/1.05  --res_time_limit                        2.
% 2.54/1.05  --res_out_proof                         true
% 2.54/1.05  
% 2.54/1.05  ------ Superposition Options
% 2.54/1.05  
% 2.54/1.05  --superposition_flag                    true
% 2.54/1.05  --sup_passive_queue_type                priority_queues
% 2.54/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.54/1.05  --sup_passive_queues_freq               [8;1;4]
% 2.54/1.05  --demod_completeness_check              fast
% 2.54/1.05  --demod_use_ground                      true
% 2.54/1.05  --sup_to_prop_solver                    passive
% 2.54/1.05  --sup_prop_simpl_new                    true
% 2.54/1.05  --sup_prop_simpl_given                  true
% 2.54/1.05  --sup_fun_splitting                     false
% 2.54/1.05  --sup_smt_interval                      50000
% 2.54/1.05  
% 2.54/1.05  ------ Superposition Simplification Setup
% 2.54/1.05  
% 2.54/1.05  --sup_indices_passive                   []
% 2.54/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.54/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.54/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.54/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 2.54/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.54/1.05  --sup_full_bw                           [BwDemod]
% 2.54/1.05  --sup_immed_triv                        [TrivRules]
% 2.54/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.54/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.54/1.05  --sup_immed_bw_main                     []
% 2.54/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.54/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 2.54/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.54/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.54/1.05  
% 2.54/1.05  ------ Combination Options
% 2.54/1.05  
% 2.54/1.05  --comb_res_mult                         3
% 2.54/1.05  --comb_sup_mult                         2
% 2.54/1.05  --comb_inst_mult                        10
% 2.54/1.05  
% 2.54/1.05  ------ Debug Options
% 2.54/1.05  
% 2.54/1.05  --dbg_backtrace                         false
% 2.54/1.05  --dbg_dump_prop_clauses                 false
% 2.54/1.05  --dbg_dump_prop_clauses_file            -
% 2.54/1.05  --dbg_out_stat                          false
% 2.54/1.05  ------ Parsing...
% 2.54/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.54/1.05  
% 2.54/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.54/1.05  
% 2.54/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.54/1.05  
% 2.54/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.54/1.05  ------ Proving...
% 2.54/1.05  ------ Problem Properties 
% 2.54/1.05  
% 2.54/1.05  
% 2.54/1.05  clauses                                 20
% 2.54/1.05  conjectures                             3
% 2.54/1.05  EPR                                     2
% 2.54/1.05  Horn                                    18
% 2.54/1.05  unary                                   3
% 2.54/1.05  binary                                  7
% 2.54/1.05  lits                                    50
% 2.54/1.05  lits eq                                 12
% 2.54/1.05  fd_pure                                 0
% 2.54/1.05  fd_pseudo                               0
% 2.54/1.05  fd_cond                                 0
% 2.54/1.05  fd_pseudo_cond                          1
% 2.54/1.05  AC symbols                              0
% 2.54/1.05  
% 2.54/1.05  ------ Schedule dynamic 5 is on 
% 2.54/1.05  
% 2.54/1.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.54/1.05  
% 2.54/1.05  
% 2.54/1.05  ------ 
% 2.54/1.05  Current options:
% 2.54/1.05  ------ 
% 2.54/1.05  
% 2.54/1.05  ------ Input Options
% 2.54/1.05  
% 2.54/1.05  --out_options                           all
% 2.54/1.05  --tptp_safe_out                         true
% 2.54/1.05  --problem_path                          ""
% 2.54/1.05  --include_path                          ""
% 2.54/1.05  --clausifier                            res/vclausify_rel
% 2.54/1.05  --clausifier_options                    --mode clausify
% 2.54/1.05  --stdin                                 false
% 2.54/1.05  --stats_out                             all
% 2.54/1.05  
% 2.54/1.05  ------ General Options
% 2.54/1.05  
% 2.54/1.05  --fof                                   false
% 2.54/1.05  --time_out_real                         305.
% 2.54/1.05  --time_out_virtual                      -1.
% 2.54/1.05  --symbol_type_check                     false
% 2.54/1.05  --clausify_out                          false
% 2.54/1.05  --sig_cnt_out                           false
% 2.54/1.05  --trig_cnt_out                          false
% 2.54/1.05  --trig_cnt_out_tolerance                1.
% 2.54/1.05  --trig_cnt_out_sk_spl                   false
% 2.54/1.05  --abstr_cl_out                          false
% 2.54/1.05  
% 2.54/1.05  ------ Global Options
% 2.54/1.05  
% 2.54/1.05  --schedule                              default
% 2.54/1.05  --add_important_lit                     false
% 2.54/1.05  --prop_solver_per_cl                    1000
% 2.54/1.05  --min_unsat_core                        false
% 2.54/1.05  --soft_assumptions                      false
% 2.54/1.05  --soft_lemma_size                       3
% 2.54/1.05  --prop_impl_unit_size                   0
% 2.54/1.05  --prop_impl_unit                        []
% 2.54/1.05  --share_sel_clauses                     true
% 2.54/1.05  --reset_solvers                         false
% 2.54/1.05  --bc_imp_inh                            [conj_cone]
% 2.54/1.05  --conj_cone_tolerance                   3.
% 2.54/1.05  --extra_neg_conj                        none
% 2.54/1.05  --large_theory_mode                     true
% 2.54/1.05  --prolific_symb_bound                   200
% 2.54/1.05  --lt_threshold                          2000
% 2.54/1.05  --clause_weak_htbl                      true
% 2.54/1.05  --gc_record_bc_elim                     false
% 2.54/1.05  
% 2.54/1.05  ------ Preprocessing Options
% 2.54/1.05  
% 2.54/1.05  --preprocessing_flag                    true
% 2.54/1.05  --time_out_prep_mult                    0.1
% 2.54/1.05  --splitting_mode                        input
% 2.54/1.05  --splitting_grd                         true
% 2.54/1.05  --splitting_cvd                         false
% 2.54/1.05  --splitting_cvd_svl                     false
% 2.54/1.05  --splitting_nvd                         32
% 2.54/1.05  --sub_typing                            true
% 2.54/1.05  --prep_gs_sim                           true
% 2.54/1.05  --prep_unflatten                        true
% 2.54/1.05  --prep_res_sim                          true
% 2.54/1.05  --prep_upred                            true
% 2.54/1.05  --prep_sem_filter                       exhaustive
% 2.54/1.05  --prep_sem_filter_out                   false
% 2.54/1.05  --pred_elim                             true
% 2.54/1.05  --res_sim_input                         true
% 2.54/1.05  --eq_ax_congr_red                       true
% 2.54/1.05  --pure_diseq_elim                       true
% 2.54/1.05  --brand_transform                       false
% 2.54/1.05  --non_eq_to_eq                          false
% 2.54/1.05  --prep_def_merge                        true
% 2.54/1.05  --prep_def_merge_prop_impl              false
% 2.54/1.05  --prep_def_merge_mbd                    true
% 2.54/1.05  --prep_def_merge_tr_red                 false
% 2.54/1.05  --prep_def_merge_tr_cl                  false
% 2.54/1.05  --smt_preprocessing                     true
% 2.54/1.05  --smt_ac_axioms                         fast
% 2.54/1.05  --preprocessed_out                      false
% 2.54/1.05  --preprocessed_stats                    false
% 2.54/1.05  
% 2.54/1.05  ------ Abstraction refinement Options
% 2.54/1.05  
% 2.54/1.05  --abstr_ref                             []
% 2.54/1.05  --abstr_ref_prep                        false
% 2.54/1.05  --abstr_ref_until_sat                   false
% 2.54/1.05  --abstr_ref_sig_restrict                funpre
% 2.54/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 2.54/1.05  --abstr_ref_under                       []
% 2.54/1.05  
% 2.54/1.05  ------ SAT Options
% 2.54/1.05  
% 2.54/1.05  --sat_mode                              false
% 2.54/1.05  --sat_fm_restart_options                ""
% 2.54/1.05  --sat_gr_def                            false
% 2.54/1.05  --sat_epr_types                         true
% 2.54/1.05  --sat_non_cyclic_types                  false
% 2.54/1.05  --sat_finite_models                     false
% 2.54/1.05  --sat_fm_lemmas                         false
% 2.54/1.05  --sat_fm_prep                           false
% 2.54/1.05  --sat_fm_uc_incr                        true
% 2.54/1.05  --sat_out_model                         small
% 2.54/1.05  --sat_out_clauses                       false
% 2.54/1.05  
% 2.54/1.05  ------ QBF Options
% 2.54/1.05  
% 2.54/1.05  --qbf_mode                              false
% 2.54/1.05  --qbf_elim_univ                         false
% 2.54/1.05  --qbf_dom_inst                          none
% 2.54/1.05  --qbf_dom_pre_inst                      false
% 2.54/1.05  --qbf_sk_in                             false
% 2.54/1.05  --qbf_pred_elim                         true
% 2.54/1.05  --qbf_split                             512
% 2.54/1.05  
% 2.54/1.05  ------ BMC1 Options
% 2.54/1.05  
% 2.54/1.05  --bmc1_incremental                      false
% 2.54/1.05  --bmc1_axioms                           reachable_all
% 2.54/1.05  --bmc1_min_bound                        0
% 2.54/1.05  --bmc1_max_bound                        -1
% 2.54/1.05  --bmc1_max_bound_default                -1
% 2.54/1.05  --bmc1_symbol_reachability              true
% 2.54/1.05  --bmc1_property_lemmas                  false
% 2.54/1.05  --bmc1_k_induction                      false
% 2.54/1.05  --bmc1_non_equiv_states                 false
% 2.54/1.05  --bmc1_deadlock                         false
% 2.54/1.05  --bmc1_ucm                              false
% 2.54/1.05  --bmc1_add_unsat_core                   none
% 2.54/1.05  --bmc1_unsat_core_children              false
% 2.54/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 2.54/1.05  --bmc1_out_stat                         full
% 2.54/1.05  --bmc1_ground_init                      false
% 2.54/1.05  --bmc1_pre_inst_next_state              false
% 2.54/1.05  --bmc1_pre_inst_state                   false
% 2.54/1.05  --bmc1_pre_inst_reach_state             false
% 2.54/1.05  --bmc1_out_unsat_core                   false
% 2.54/1.05  --bmc1_aig_witness_out                  false
% 2.54/1.05  --bmc1_verbose                          false
% 2.54/1.05  --bmc1_dump_clauses_tptp                false
% 2.54/1.05  --bmc1_dump_unsat_core_tptp             false
% 2.54/1.05  --bmc1_dump_file                        -
% 2.54/1.05  --bmc1_ucm_expand_uc_limit              128
% 2.54/1.05  --bmc1_ucm_n_expand_iterations          6
% 2.54/1.05  --bmc1_ucm_extend_mode                  1
% 2.54/1.05  --bmc1_ucm_init_mode                    2
% 2.54/1.05  --bmc1_ucm_cone_mode                    none
% 2.54/1.05  --bmc1_ucm_reduced_relation_type        0
% 2.54/1.05  --bmc1_ucm_relax_model                  4
% 2.54/1.05  --bmc1_ucm_full_tr_after_sat            true
% 2.54/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 2.54/1.05  --bmc1_ucm_layered_model                none
% 2.54/1.05  --bmc1_ucm_max_lemma_size               10
% 2.54/1.05  
% 2.54/1.05  ------ AIG Options
% 2.54/1.05  
% 2.54/1.05  --aig_mode                              false
% 2.54/1.05  
% 2.54/1.05  ------ Instantiation Options
% 2.54/1.05  
% 2.54/1.05  --instantiation_flag                    true
% 2.54/1.05  --inst_sos_flag                         false
% 2.54/1.05  --inst_sos_phase                        true
% 2.54/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.54/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.54/1.05  --inst_lit_sel_side                     none
% 2.54/1.05  --inst_solver_per_active                1400
% 2.54/1.05  --inst_solver_calls_frac                1.
% 2.54/1.05  --inst_passive_queue_type               priority_queues
% 2.54/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.54/1.05  --inst_passive_queues_freq              [25;2]
% 2.54/1.05  --inst_dismatching                      true
% 2.54/1.05  --inst_eager_unprocessed_to_passive     true
% 2.54/1.05  --inst_prop_sim_given                   true
% 2.54/1.05  --inst_prop_sim_new                     false
% 2.54/1.05  --inst_subs_new                         false
% 2.54/1.05  --inst_eq_res_simp                      false
% 2.54/1.05  --inst_subs_given                       false
% 2.54/1.05  --inst_orphan_elimination               true
% 2.54/1.05  --inst_learning_loop_flag               true
% 2.54/1.05  --inst_learning_start                   3000
% 2.54/1.05  --inst_learning_factor                  2
% 2.54/1.05  --inst_start_prop_sim_after_learn       3
% 2.54/1.05  --inst_sel_renew                        solver
% 2.54/1.05  --inst_lit_activity_flag                true
% 2.54/1.05  --inst_restr_to_given                   false
% 2.54/1.05  --inst_activity_threshold               500
% 2.54/1.05  --inst_out_proof                        true
% 2.54/1.05  
% 2.54/1.05  ------ Resolution Options
% 2.54/1.05  
% 2.54/1.05  --resolution_flag                       false
% 2.54/1.05  --res_lit_sel                           adaptive
% 2.54/1.05  --res_lit_sel_side                      none
% 2.54/1.05  --res_ordering                          kbo
% 2.54/1.05  --res_to_prop_solver                    active
% 2.54/1.05  --res_prop_simpl_new                    false
% 2.54/1.05  --res_prop_simpl_given                  true
% 2.54/1.05  --res_passive_queue_type                priority_queues
% 2.54/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.54/1.05  --res_passive_queues_freq               [15;5]
% 2.54/1.05  --res_forward_subs                      full
% 2.54/1.05  --res_backward_subs                     full
% 2.54/1.05  --res_forward_subs_resolution           true
% 2.54/1.05  --res_backward_subs_resolution          true
% 2.54/1.05  --res_orphan_elimination                true
% 2.54/1.05  --res_time_limit                        2.
% 2.54/1.05  --res_out_proof                         true
% 2.54/1.05  
% 2.54/1.05  ------ Superposition Options
% 2.54/1.05  
% 2.54/1.05  --superposition_flag                    true
% 2.54/1.05  --sup_passive_queue_type                priority_queues
% 2.54/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.54/1.05  --sup_passive_queues_freq               [8;1;4]
% 2.54/1.05  --demod_completeness_check              fast
% 2.54/1.05  --demod_use_ground                      true
% 2.54/1.05  --sup_to_prop_solver                    passive
% 2.54/1.05  --sup_prop_simpl_new                    true
% 2.54/1.05  --sup_prop_simpl_given                  true
% 2.54/1.05  --sup_fun_splitting                     false
% 2.54/1.05  --sup_smt_interval                      50000
% 2.54/1.05  
% 2.54/1.05  ------ Superposition Simplification Setup
% 2.54/1.05  
% 2.54/1.05  --sup_indices_passive                   []
% 2.54/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.54/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.54/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.54/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 2.54/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.54/1.05  --sup_full_bw                           [BwDemod]
% 2.54/1.05  --sup_immed_triv                        [TrivRules]
% 2.54/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.54/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.54/1.05  --sup_immed_bw_main                     []
% 2.54/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.54/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 2.54/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.54/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.54/1.05  
% 2.54/1.05  ------ Combination Options
% 2.54/1.05  
% 2.54/1.05  --comb_res_mult                         3
% 2.54/1.05  --comb_sup_mult                         2
% 2.54/1.05  --comb_inst_mult                        10
% 2.54/1.05  
% 2.54/1.05  ------ Debug Options
% 2.54/1.05  
% 2.54/1.05  --dbg_backtrace                         false
% 2.54/1.05  --dbg_dump_prop_clauses                 false
% 2.54/1.05  --dbg_dump_prop_clauses_file            -
% 2.54/1.05  --dbg_out_stat                          false
% 2.54/1.05  
% 2.54/1.05  
% 2.54/1.05  
% 2.54/1.05  
% 2.54/1.05  ------ Proving...
% 2.54/1.05  
% 2.54/1.05  
% 2.54/1.05  % SZS status Theorem for theBenchmark.p
% 2.54/1.05  
% 2.54/1.05   Resolution empty clause
% 2.54/1.05  
% 2.54/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 2.54/1.05  
% 2.54/1.05  fof(f13,conjecture,(
% 2.54/1.05    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 2.54/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.54/1.05  
% 2.54/1.05  fof(f14,negated_conjecture,(
% 2.54/1.05    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 2.54/1.05    inference(negated_conjecture,[],[f13])).
% 2.54/1.05  
% 2.54/1.05  fof(f31,plain,(
% 2.54/1.05    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)))),
% 2.54/1.05    inference(ennf_transformation,[],[f14])).
% 2.54/1.05  
% 2.54/1.05  fof(f32,plain,(
% 2.54/1.05    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))),
% 2.54/1.05    inference(flattening,[],[f31])).
% 2.54/1.05  
% 2.54/1.05  fof(f40,plain,(
% 2.54/1.05    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (k1_funct_1(sK4,X4) != sK1 | ~m1_subset_1(X4,sK2)) & r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 2.54/1.05    introduced(choice_axiom,[])).
% 2.54/1.05  
% 2.54/1.05  fof(f41,plain,(
% 2.54/1.05    ! [X4] : (k1_funct_1(sK4,X4) != sK1 | ~m1_subset_1(X4,sK2)) & r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 2.54/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f32,f40])).
% 2.54/1.05  
% 2.54/1.05  fof(f66,plain,(
% 2.54/1.05    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.54/1.05    inference(cnf_transformation,[],[f41])).
% 2.54/1.05  
% 2.54/1.05  fof(f11,axiom,(
% 2.54/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.54/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.54/1.05  
% 2.54/1.05  fof(f28,plain,(
% 2.54/1.05    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.54/1.05    inference(ennf_transformation,[],[f11])).
% 2.54/1.05  
% 2.54/1.05  fof(f57,plain,(
% 2.54/1.05    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.54/1.05    inference(cnf_transformation,[],[f28])).
% 2.54/1.05  
% 2.54/1.05  fof(f67,plain,(
% 2.54/1.05    r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4))),
% 2.54/1.05    inference(cnf_transformation,[],[f41])).
% 2.54/1.05  
% 2.54/1.05  fof(f12,axiom,(
% 2.54/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.54/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.54/1.05  
% 2.54/1.05  fof(f29,plain,(
% 2.54/1.05    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.54/1.05    inference(ennf_transformation,[],[f12])).
% 2.54/1.05  
% 2.54/1.05  fof(f30,plain,(
% 2.54/1.05    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.54/1.05    inference(flattening,[],[f29])).
% 2.54/1.05  
% 2.54/1.05  fof(f39,plain,(
% 2.54/1.05    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.54/1.05    inference(nnf_transformation,[],[f30])).
% 2.54/1.05  
% 2.54/1.05  fof(f58,plain,(
% 2.54/1.05    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.54/1.05    inference(cnf_transformation,[],[f39])).
% 2.54/1.05  
% 2.54/1.05  fof(f65,plain,(
% 2.54/1.05    v1_funct_2(sK4,sK2,sK3)),
% 2.54/1.05    inference(cnf_transformation,[],[f41])).
% 2.54/1.05  
% 2.54/1.05  fof(f10,axiom,(
% 2.54/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.54/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.54/1.05  
% 2.54/1.05  fof(f27,plain,(
% 2.54/1.05    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.54/1.05    inference(ennf_transformation,[],[f10])).
% 2.54/1.05  
% 2.54/1.05  fof(f56,plain,(
% 2.54/1.05    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.54/1.05    inference(cnf_transformation,[],[f27])).
% 2.54/1.05  
% 2.54/1.05  fof(f8,axiom,(
% 2.54/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.54/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.54/1.05  
% 2.54/1.05  fof(f25,plain,(
% 2.54/1.05    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.54/1.05    inference(ennf_transformation,[],[f8])).
% 2.54/1.05  
% 2.54/1.05  fof(f54,plain,(
% 2.54/1.05    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.54/1.05    inference(cnf_transformation,[],[f25])).
% 2.54/1.05  
% 2.54/1.05  fof(f5,axiom,(
% 2.54/1.05    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 2.54/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.54/1.05  
% 2.54/1.05  fof(f20,plain,(
% 2.54/1.05    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 2.54/1.05    inference(ennf_transformation,[],[f5])).
% 2.54/1.05  
% 2.54/1.05  fof(f49,plain,(
% 2.54/1.05    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.54/1.05    inference(cnf_transformation,[],[f20])).
% 2.54/1.05  
% 2.54/1.05  fof(f4,axiom,(
% 2.54/1.05    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 2.54/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.54/1.05  
% 2.54/1.05  fof(f19,plain,(
% 2.54/1.05    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 2.54/1.05    inference(ennf_transformation,[],[f4])).
% 2.54/1.05  
% 2.54/1.05  fof(f33,plain,(
% 2.54/1.05    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.54/1.05    inference(nnf_transformation,[],[f19])).
% 2.54/1.05  
% 2.54/1.05  fof(f34,plain,(
% 2.54/1.05    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.54/1.05    inference(rectify,[],[f33])).
% 2.54/1.05  
% 2.54/1.05  fof(f35,plain,(
% 2.54/1.05    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))))),
% 2.54/1.05    introduced(choice_axiom,[])).
% 2.54/1.05  
% 2.54/1.05  fof(f36,plain,(
% 2.54/1.05    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.54/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 2.54/1.05  
% 2.54/1.05  fof(f46,plain,(
% 2.54/1.05    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.54/1.05    inference(cnf_transformation,[],[f36])).
% 2.54/1.05  
% 2.54/1.05  fof(f7,axiom,(
% 2.54/1.05    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 2.54/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.54/1.05  
% 2.54/1.05  fof(f23,plain,(
% 2.54/1.05    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.54/1.05    inference(ennf_transformation,[],[f7])).
% 2.54/1.05  
% 2.54/1.05  fof(f24,plain,(
% 2.54/1.05    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.54/1.05    inference(flattening,[],[f23])).
% 2.54/1.05  
% 2.54/1.05  fof(f37,plain,(
% 2.54/1.05    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.54/1.05    inference(nnf_transformation,[],[f24])).
% 2.54/1.05  
% 2.54/1.05  fof(f38,plain,(
% 2.54/1.05    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.54/1.05    inference(flattening,[],[f37])).
% 2.54/1.05  
% 2.54/1.05  fof(f52,plain,(
% 2.54/1.05    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.54/1.05    inference(cnf_transformation,[],[f38])).
% 2.54/1.05  
% 2.54/1.05  fof(f64,plain,(
% 2.54/1.05    v1_funct_1(sK4)),
% 2.54/1.05    inference(cnf_transformation,[],[f41])).
% 2.54/1.05  
% 2.54/1.05  fof(f68,plain,(
% 2.54/1.05    ( ! [X4] : (k1_funct_1(sK4,X4) != sK1 | ~m1_subset_1(X4,sK2)) )),
% 2.54/1.05    inference(cnf_transformation,[],[f41])).
% 2.54/1.05  
% 2.54/1.05  fof(f45,plain,(
% 2.54/1.05    ( ! [X2,X0,X1] : (r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.54/1.05    inference(cnf_transformation,[],[f36])).
% 2.54/1.05  
% 2.54/1.05  fof(f3,axiom,(
% 2.54/1.05    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.54/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.54/1.05  
% 2.54/1.05  fof(f18,plain,(
% 2.54/1.05    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.54/1.05    inference(ennf_transformation,[],[f3])).
% 2.54/1.05  
% 2.54/1.05  fof(f44,plain,(
% 2.54/1.05    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.54/1.05    inference(cnf_transformation,[],[f18])).
% 2.54/1.05  
% 2.54/1.05  fof(f9,axiom,(
% 2.54/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.54/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.54/1.05  
% 2.54/1.05  fof(f16,plain,(
% 2.54/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.54/1.05    inference(pure_predicate_removal,[],[f9])).
% 2.54/1.05  
% 2.54/1.05  fof(f26,plain,(
% 2.54/1.05    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.54/1.05    inference(ennf_transformation,[],[f16])).
% 2.54/1.05  
% 2.54/1.05  fof(f55,plain,(
% 2.54/1.05    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.54/1.05    inference(cnf_transformation,[],[f26])).
% 2.54/1.05  
% 2.54/1.05  fof(f6,axiom,(
% 2.54/1.05    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k2_relat_1(X1)) => r2_hidden(X2,X0)))),
% 2.54/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.54/1.05  
% 2.54/1.05  fof(f21,plain,(
% 2.54/1.05    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1))) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.54/1.05    inference(ennf_transformation,[],[f6])).
% 2.54/1.05  
% 2.54/1.05  fof(f22,plain,(
% 2.54/1.05    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.54/1.05    inference(flattening,[],[f21])).
% 2.54/1.05  
% 2.54/1.05  fof(f50,plain,(
% 2.54/1.05    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1)) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.54/1.05    inference(cnf_transformation,[],[f22])).
% 2.54/1.05  
% 2.54/1.05  fof(f1,axiom,(
% 2.54/1.05    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.54/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.54/1.05  
% 2.54/1.05  fof(f15,plain,(
% 2.54/1.05    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 2.54/1.05    inference(unused_predicate_definition_removal,[],[f1])).
% 2.54/1.05  
% 2.54/1.05  fof(f17,plain,(
% 2.54/1.05    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 2.54/1.05    inference(ennf_transformation,[],[f15])).
% 2.54/1.05  
% 2.54/1.05  fof(f42,plain,(
% 2.54/1.05    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 2.54/1.05    inference(cnf_transformation,[],[f17])).
% 2.54/1.05  
% 2.54/1.05  fof(f2,axiom,(
% 2.54/1.05    v1_xboole_0(k1_xboole_0)),
% 2.54/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.54/1.05  
% 2.54/1.05  fof(f43,plain,(
% 2.54/1.05    v1_xboole_0(k1_xboole_0)),
% 2.54/1.05    inference(cnf_transformation,[],[f2])).
% 2.54/1.05  
% 2.54/1.05  cnf(c_24,negated_conjecture,
% 2.54/1.05      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.54/1.05      inference(cnf_transformation,[],[f66]) ).
% 2.54/1.05  
% 2.54/1.05  cnf(c_2003,plain,
% 2.54/1.05      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.54/1.05      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.54/1.05  
% 2.54/1.05  cnf(c_15,plain,
% 2.54/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.54/1.05      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.54/1.05      inference(cnf_transformation,[],[f57]) ).
% 2.54/1.05  
% 2.54/1.05  cnf(c_2006,plain,
% 2.54/1.05      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.54/1.05      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.54/1.05      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.54/1.05  
% 2.54/1.05  cnf(c_2391,plain,
% 2.54/1.05      ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 2.54/1.05      inference(superposition,[status(thm)],[c_2003,c_2006]) ).
% 2.54/1.05  
% 2.54/1.05  cnf(c_23,negated_conjecture,
% 2.54/1.05      ( r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4)) ),
% 2.54/1.05      inference(cnf_transformation,[],[f67]) ).
% 2.54/1.05  
% 2.54/1.05  cnf(c_2004,plain,
% 2.54/1.05      ( r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4)) = iProver_top ),
% 2.54/1.05      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.54/1.05  
% 2.54/1.05  cnf(c_2430,plain,
% 2.54/1.05      ( r2_hidden(sK1,k2_relat_1(sK4)) = iProver_top ),
% 2.54/1.05      inference(demodulation,[status(thm)],[c_2391,c_2004]) ).
% 2.54/1.05  
% 2.54/1.05  cnf(c_21,plain,
% 2.54/1.05      ( ~ v1_funct_2(X0,X1,X2)
% 2.54/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.54/1.05      | k1_relset_1(X1,X2,X0) = X1
% 2.54/1.05      | k1_xboole_0 = X2 ),
% 2.54/1.05      inference(cnf_transformation,[],[f58]) ).
% 2.54/1.05  
% 2.54/1.05  cnf(c_25,negated_conjecture,
% 2.54/1.05      ( v1_funct_2(sK4,sK2,sK3) ),
% 2.54/1.05      inference(cnf_transformation,[],[f65]) ).
% 2.54/1.05  
% 2.54/1.05  cnf(c_973,plain,
% 2.54/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.54/1.05      | k1_relset_1(X1,X2,X0) = X1
% 2.54/1.05      | sK3 != X2
% 2.54/1.05      | sK2 != X1
% 2.54/1.05      | sK4 != X0
% 2.54/1.05      | k1_xboole_0 = X2 ),
% 2.54/1.05      inference(resolution_lifted,[status(thm)],[c_21,c_25]) ).
% 2.54/1.05  
% 2.54/1.05  cnf(c_974,plain,
% 2.54/1.05      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.54/1.05      | k1_relset_1(sK2,sK3,sK4) = sK2
% 2.54/1.05      | k1_xboole_0 = sK3 ),
% 2.54/1.05      inference(unflattening,[status(thm)],[c_973]) ).
% 2.54/1.05  
% 2.54/1.05  cnf(c_976,plain,
% 2.54/1.05      ( k1_relset_1(sK2,sK3,sK4) = sK2 | k1_xboole_0 = sK3 ),
% 2.54/1.05      inference(global_propositional_subsumption,[status(thm)],[c_974,c_24]) ).
% 2.54/1.05  
% 2.54/1.05  cnf(c_14,plain,
% 2.54/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.54/1.05      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.54/1.05      inference(cnf_transformation,[],[f56]) ).
% 2.54/1.05  
% 2.54/1.05  cnf(c_2007,plain,
% 2.54/1.05      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.54/1.05      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.54/1.05      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.54/1.05  
% 2.54/1.05  cnf(c_2639,plain,
% 2.54/1.05      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 2.54/1.05      inference(superposition,[status(thm)],[c_2003,c_2007]) ).
% 2.54/1.05  
% 2.54/1.05  cnf(c_2803,plain,
% 2.54/1.05      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 2.54/1.05      inference(superposition,[status(thm)],[c_976,c_2639]) ).
% 2.54/1.05  
% 2.54/1.05  cnf(c_12,plain,
% 2.54/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.54/1.05      inference(cnf_transformation,[],[f54]) ).
% 2.54/1.05  
% 2.54/1.05  cnf(c_2008,plain,
% 2.54/1.05      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.54/1.05      | v1_relat_1(X0) = iProver_top ),
% 2.54/1.05      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.54/1.05  
% 2.54/1.05  cnf(c_2345,plain,
% 2.54/1.05      ( v1_relat_1(sK4) = iProver_top ),
% 2.54/1.05      inference(superposition,[status(thm)],[c_2003,c_2008]) ).
% 2.54/1.05  
% 2.54/1.05  cnf(c_7,plain,
% 2.54/1.05      ( ~ v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 2.54/1.05      inference(cnf_transformation,[],[f49]) ).
% 2.54/1.05  
% 2.54/1.05  cnf(c_2009,plain,
% 2.54/1.05      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 2.54/1.05      | v1_relat_1(X0) != iProver_top ),
% 2.54/1.05      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.54/1.05  
% 2.54/1.05  cnf(c_2394,plain,
% 2.54/1.05      ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
% 2.54/1.05      inference(superposition,[status(thm)],[c_2345,c_2009]) ).
% 2.54/1.05  
% 2.54/1.05  cnf(c_5,plain,
% 2.54/1.05      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.54/1.05      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
% 2.54/1.05      | ~ v1_relat_1(X1) ),
% 2.54/1.05      inference(cnf_transformation,[],[f46]) ).
% 2.54/1.05  
% 2.54/1.05  cnf(c_2011,plain,
% 2.54/1.05      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 2.54/1.05      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
% 2.54/1.05      | v1_relat_1(X1) != iProver_top ),
% 2.54/1.05      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.54/1.05  
% 2.54/1.05  cnf(c_10,plain,
% 2.54/1.05      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 2.54/1.05      | ~ v1_funct_1(X2)
% 2.54/1.05      | ~ v1_relat_1(X2)
% 2.54/1.05      | k1_funct_1(X2,X0) = X1 ),
% 2.54/1.05      inference(cnf_transformation,[],[f52]) ).
% 2.54/1.05  
% 2.54/1.05  cnf(c_26,negated_conjecture,
% 2.54/1.05      ( v1_funct_1(sK4) ),
% 2.54/1.05      inference(cnf_transformation,[],[f64]) ).
% 2.54/1.05  
% 2.54/1.05  cnf(c_345,plain,
% 2.54/1.05      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 2.54/1.05      | ~ v1_relat_1(X2)
% 2.54/1.05      | k1_funct_1(X2,X0) = X1
% 2.54/1.05      | sK4 != X2 ),
% 2.54/1.05      inference(resolution_lifted,[status(thm)],[c_10,c_26]) ).
% 2.54/1.05  
% 2.54/1.05  cnf(c_346,plain,
% 2.54/1.05      ( ~ r2_hidden(k4_tarski(X0,X1),sK4)
% 2.54/1.05      | ~ v1_relat_1(sK4)
% 2.54/1.05      | k1_funct_1(sK4,X0) = X1 ),
% 2.54/1.05      inference(unflattening,[status(thm)],[c_345]) ).
% 2.54/1.05  
% 2.54/1.05  cnf(c_2000,plain,
% 2.54/1.05      ( k1_funct_1(sK4,X0) = X1
% 2.54/1.05      | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top
% 2.54/1.05      | v1_relat_1(sK4) != iProver_top ),
% 2.54/1.05      inference(predicate_to_equality,[status(thm)],[c_346]) ).
% 2.54/1.05  
% 2.54/1.05  cnf(c_29,plain,
% 2.54/1.05      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.54/1.05      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.54/1.05  
% 2.54/1.05  cnf(c_347,plain,
% 2.54/1.05      ( k1_funct_1(sK4,X0) = X1
% 2.54/1.05      | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top
% 2.54/1.05      | v1_relat_1(sK4) != iProver_top ),
% 2.54/1.05      inference(predicate_to_equality,[status(thm)],[c_346]) ).
% 2.54/1.05  
% 2.54/1.05  cnf(c_2163,plain,
% 2.54/1.05      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.54/1.05      | v1_relat_1(sK4) ),
% 2.54/1.05      inference(instantiation,[status(thm)],[c_12]) ).
% 2.54/1.05  
% 2.54/1.05  cnf(c_2164,plain,
% 2.54/1.05      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 2.54/1.05      | v1_relat_1(sK4) = iProver_top ),
% 2.54/1.05      inference(predicate_to_equality,[status(thm)],[c_2163]) ).
% 2.54/1.05  
% 2.54/1.05  cnf(c_2190,plain,
% 2.54/1.05      ( r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top
% 2.54/1.05      | k1_funct_1(sK4,X0) = X1 ),
% 2.54/1.05      inference(global_propositional_subsumption,
% 2.54/1.05                [status(thm)],
% 2.54/1.05                [c_2000,c_29,c_347,c_2164]) ).
% 2.54/1.05  
% 2.54/1.05  cnf(c_2191,plain,
% 2.54/1.05      ( k1_funct_1(sK4,X0) = X1
% 2.54/1.05      | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top ),
% 2.54/1.05      inference(renaming,[status(thm)],[c_2190]) ).
% 2.54/1.05  
% 2.54/1.05  cnf(c_2777,plain,
% 2.54/1.05      ( k1_funct_1(sK4,sK0(X0,X1,sK4)) = X0
% 2.54/1.05      | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 2.54/1.05      | v1_relat_1(sK4) != iProver_top ),
% 2.54/1.05      inference(superposition,[status(thm)],[c_2011,c_2191]) ).
% 2.54/1.05  
% 2.54/1.05  cnf(c_2967,plain,
% 2.54/1.05      ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 2.54/1.06      | k1_funct_1(sK4,sK0(X0,X1,sK4)) = X0 ),
% 2.54/1.06      inference(global_propositional_subsumption,
% 2.54/1.06                [status(thm)],
% 2.54/1.06                [c_2777,c_29,c_2164]) ).
% 2.54/1.06  
% 2.54/1.06  cnf(c_2968,plain,
% 2.54/1.06      ( k1_funct_1(sK4,sK0(X0,X1,sK4)) = X0
% 2.54/1.06      | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top ),
% 2.54/1.06      inference(renaming,[status(thm)],[c_2967]) ).
% 2.54/1.06  
% 2.54/1.06  cnf(c_2977,plain,
% 2.54/1.06      ( k1_funct_1(sK4,sK0(X0,k1_relat_1(sK4),sK4)) = X0
% 2.54/1.06      | r2_hidden(X0,k2_relat_1(sK4)) != iProver_top ),
% 2.54/1.06      inference(superposition,[status(thm)],[c_2394,c_2968]) ).
% 2.54/1.06  
% 2.54/1.06  cnf(c_3514,plain,
% 2.54/1.06      ( k1_funct_1(sK4,sK0(sK1,k1_relat_1(sK4),sK4)) = sK1 ),
% 2.54/1.06      inference(superposition,[status(thm)],[c_2430,c_2977]) ).
% 2.54/1.06  
% 2.54/1.06  cnf(c_22,negated_conjecture,
% 2.54/1.06      ( ~ m1_subset_1(X0,sK2) | k1_funct_1(sK4,X0) != sK1 ),
% 2.54/1.06      inference(cnf_transformation,[],[f68]) ).
% 2.54/1.06  
% 2.54/1.06  cnf(c_2005,plain,
% 2.54/1.06      ( k1_funct_1(sK4,X0) != sK1 | m1_subset_1(X0,sK2) != iProver_top ),
% 2.54/1.06      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.54/1.06  
% 2.54/1.06  cnf(c_3631,plain,
% 2.54/1.06      ( m1_subset_1(sK0(sK1,k1_relat_1(sK4),sK4),sK2) != iProver_top ),
% 2.54/1.06      inference(superposition,[status(thm)],[c_3514,c_2005]) ).
% 2.54/1.06  
% 2.54/1.06  cnf(c_3660,plain,
% 2.54/1.06      ( sK3 = k1_xboole_0 | m1_subset_1(sK0(sK1,sK2,sK4),sK2) != iProver_top ),
% 2.54/1.06      inference(superposition,[status(thm)],[c_2803,c_3631]) ).
% 2.54/1.06  
% 2.54/1.06  cnf(c_6,plain,
% 2.54/1.06      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.54/1.06      | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1))
% 2.54/1.06      | ~ v1_relat_1(X1) ),
% 2.54/1.06      inference(cnf_transformation,[],[f45]) ).
% 2.54/1.06  
% 2.54/1.06  cnf(c_2010,plain,
% 2.54/1.06      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 2.54/1.06      | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1)) = iProver_top
% 2.54/1.06      | v1_relat_1(X1) != iProver_top ),
% 2.54/1.06      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.54/1.06  
% 2.54/1.06  cnf(c_2885,plain,
% 2.54/1.06      ( sK3 = k1_xboole_0
% 2.54/1.06      | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 2.54/1.06      | r2_hidden(sK0(X0,X1,sK4),sK2) = iProver_top
% 2.54/1.06      | v1_relat_1(sK4) != iProver_top ),
% 2.54/1.06      inference(superposition,[status(thm)],[c_2803,c_2010]) ).
% 2.54/1.06  
% 2.54/1.06  cnf(c_3390,plain,
% 2.54/1.06      ( r2_hidden(sK0(X0,X1,sK4),sK2) = iProver_top
% 2.54/1.06      | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 2.54/1.06      | sK3 = k1_xboole_0 ),
% 2.54/1.06      inference(global_propositional_subsumption,
% 2.54/1.06                [status(thm)],
% 2.54/1.06                [c_2885,c_29,c_2164]) ).
% 2.54/1.06  
% 2.54/1.06  cnf(c_3391,plain,
% 2.54/1.06      ( sK3 = k1_xboole_0
% 2.54/1.06      | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 2.54/1.06      | r2_hidden(sK0(X0,X1,sK4),sK2) = iProver_top ),
% 2.54/1.06      inference(renaming,[status(thm)],[c_3390]) ).
% 2.54/1.06  
% 2.54/1.06  cnf(c_2,plain,
% 2.54/1.06      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.54/1.06      inference(cnf_transformation,[],[f44]) ).
% 2.54/1.06  
% 2.54/1.06  cnf(c_2014,plain,
% 2.54/1.06      ( m1_subset_1(X0,X1) = iProver_top | r2_hidden(X0,X1) != iProver_top ),
% 2.54/1.06      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.54/1.06  
% 2.54/1.06  cnf(c_3399,plain,
% 2.54/1.06      ( sK3 = k1_xboole_0
% 2.54/1.06      | m1_subset_1(sK0(X0,X1,sK4),sK2) = iProver_top
% 2.54/1.06      | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top ),
% 2.54/1.06      inference(superposition,[status(thm)],[c_3391,c_2014]) ).
% 2.54/1.06  
% 2.54/1.06  cnf(c_3844,plain,
% 2.54/1.06      ( sK3 = k1_xboole_0
% 2.54/1.06      | r2_hidden(sK1,k9_relat_1(sK4,k1_relat_1(sK4))) != iProver_top ),
% 2.54/1.06      inference(superposition,[status(thm)],[c_3399,c_3631]) ).
% 2.54/1.06  
% 2.54/1.06  cnf(c_3845,plain,
% 2.54/1.06      ( sK3 = k1_xboole_0 | r2_hidden(sK1,k2_relat_1(sK4)) != iProver_top ),
% 2.54/1.06      inference(light_normalisation,[status(thm)],[c_3844,c_2394]) ).
% 2.54/1.06  
% 2.54/1.06  cnf(c_3953,plain,
% 2.54/1.06      ( sK3 = k1_xboole_0 ),
% 2.54/1.06      inference(global_propositional_subsumption,
% 2.54/1.06                [status(thm)],
% 2.54/1.06                [c_3660,c_2430,c_3845]) ).
% 2.54/1.06  
% 2.54/1.06  cnf(c_13,plain,
% 2.54/1.06      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.54/1.06      inference(cnf_transformation,[],[f55]) ).
% 2.54/1.06  
% 2.54/1.06  cnf(c_8,plain,
% 2.54/1.06      ( ~ v5_relat_1(X0,X1)
% 2.54/1.06      | r2_hidden(X2,X1)
% 2.54/1.06      | ~ r2_hidden(X2,k2_relat_1(X0))
% 2.54/1.06      | ~ v1_relat_1(X0) ),
% 2.54/1.06      inference(cnf_transformation,[],[f50]) ).
% 2.54/1.06  
% 2.54/1.06  cnf(c_321,plain,
% 2.54/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.54/1.06      | r2_hidden(X3,X2)
% 2.54/1.06      | ~ r2_hidden(X3,k2_relat_1(X0))
% 2.54/1.06      | ~ v1_relat_1(X0) ),
% 2.54/1.06      inference(resolution,[status(thm)],[c_13,c_8]) ).
% 2.54/1.06  
% 2.54/1.06  cnf(c_325,plain,
% 2.54/1.06      ( ~ r2_hidden(X3,k2_relat_1(X0))
% 2.54/1.06      | r2_hidden(X3,X2)
% 2.54/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.54/1.06      inference(global_propositional_subsumption,[status(thm)],[c_321,c_12]) ).
% 2.54/1.06  
% 2.54/1.06  cnf(c_326,plain,
% 2.54/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.54/1.06      | r2_hidden(X3,X2)
% 2.54/1.06      | ~ r2_hidden(X3,k2_relat_1(X0)) ),
% 2.54/1.06      inference(renaming,[status(thm)],[c_325]) ).
% 2.54/1.06  
% 2.54/1.06  cnf(c_2001,plain,
% 2.54/1.06      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.54/1.06      | r2_hidden(X3,X2) = iProver_top
% 2.54/1.06      | r2_hidden(X3,k2_relat_1(X0)) != iProver_top ),
% 2.54/1.06      inference(predicate_to_equality,[status(thm)],[c_326]) ).
% 2.54/1.06  
% 2.54/1.06  cnf(c_2632,plain,
% 2.54/1.06      ( r2_hidden(X0,k2_relat_1(sK4)) != iProver_top
% 2.54/1.06      | r2_hidden(X0,sK3) = iProver_top ),
% 2.54/1.06      inference(superposition,[status(thm)],[c_2003,c_2001]) ).
% 2.54/1.06  
% 2.54/1.06  cnf(c_3962,plain,
% 2.54/1.06      ( r2_hidden(X0,k2_relat_1(sK4)) != iProver_top
% 2.54/1.06      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 2.54/1.06      inference(demodulation,[status(thm)],[c_3953,c_2632]) ).
% 2.54/1.06  
% 2.54/1.06  cnf(c_0,plain,
% 2.54/1.06      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.54/1.06      inference(cnf_transformation,[],[f42]) ).
% 2.54/1.06  
% 2.54/1.06  cnf(c_1,plain,
% 2.54/1.06      ( v1_xboole_0(k1_xboole_0) ),
% 2.54/1.06      inference(cnf_transformation,[],[f43]) ).
% 2.54/1.06  
% 2.54/1.06  cnf(c_310,plain,
% 2.54/1.06      ( ~ r2_hidden(X0,X1) | k1_xboole_0 != X1 ),
% 2.54/1.06      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 2.54/1.06  
% 2.54/1.06  cnf(c_311,plain,
% 2.54/1.06      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.54/1.06      inference(unflattening,[status(thm)],[c_310]) ).
% 2.54/1.06  
% 2.54/1.06  cnf(c_312,plain,
% 2.54/1.06      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.54/1.06      inference(predicate_to_equality,[status(thm)],[c_311]) ).
% 2.54/1.06  
% 2.54/1.06  cnf(c_4183,plain,
% 2.54/1.06      ( r2_hidden(X0,k2_relat_1(sK4)) != iProver_top ),
% 2.54/1.06      inference(global_propositional_subsumption,[status(thm)],[c_3962,c_312]) ).
% 2.54/1.06  
% 2.54/1.06  cnf(c_4192,plain,
% 2.54/1.06      ( $false ),
% 2.54/1.06      inference(superposition,[status(thm)],[c_2430,c_4183]) ).
% 2.54/1.06  
% 2.54/1.06  
% 2.54/1.06  % SZS output end CNFRefutation for theBenchmark.p
% 2.54/1.06  
% 2.54/1.06  ------                               Statistics
% 2.54/1.06  
% 2.54/1.06  ------ General
% 2.54/1.06  
% 2.54/1.06  abstr_ref_over_cycles:                  0
% 2.54/1.06  abstr_ref_under_cycles:                 0
% 2.54/1.06  gc_basic_clause_elim:                   0
% 2.54/1.06  forced_gc_time:                         0
% 2.54/1.06  parsing_time:                           0.012
% 2.54/1.06  unif_index_cands_time:                  0.
% 2.54/1.06  unif_index_add_time:                    0.
% 2.54/1.06  orderings_time:                         0.
% 2.54/1.06  out_proof_time:                         0.01
% 2.54/1.06  total_time:                             0.179
% 2.54/1.06  num_of_symbols:                         53
% 2.54/1.06  num_of_terms:                           2482
% 2.54/1.06  
% 2.54/1.06  ------ Preprocessing
% 2.54/1.06  
% 2.54/1.06  num_of_splits:                          0
% 2.54/1.06  num_of_split_atoms:                     0
% 2.54/1.06  num_of_reused_defs:                     0
% 2.54/1.06  num_eq_ax_congr_red:                    24
% 2.54/1.06  num_of_sem_filtered_clauses:            1
% 2.54/1.06  num_of_subtypes:                        0
% 2.54/1.06  monotx_restored_types:                  0
% 2.54/1.06  sat_num_of_epr_types:                   0
% 2.54/1.06  sat_num_of_non_cyclic_types:            0
% 2.54/1.06  sat_guarded_non_collapsed_types:        0
% 2.54/1.06  num_pure_diseq_elim:                    0
% 2.54/1.06  simp_replaced_by:                       0
% 2.54/1.06  res_preprocessed:                       114
% 2.54/1.06  prep_upred:                             0
% 2.54/1.06  prep_unflattend:                        115
% 2.54/1.06  smt_new_axioms:                         0
% 2.54/1.06  pred_elim_cands:                        3
% 2.54/1.06  pred_elim:                              4
% 2.54/1.06  pred_elim_cl:                           7
% 2.54/1.06  pred_elim_cycles:                       9
% 2.54/1.06  merged_defs:                            0
% 2.54/1.06  merged_defs_ncl:                        0
% 2.54/1.06  bin_hyper_res:                          0
% 2.54/1.06  prep_cycles:                            4
% 2.54/1.06  pred_elim_time:                         0.042
% 2.54/1.06  splitting_time:                         0.
% 2.54/1.06  sem_filter_time:                        0.
% 2.54/1.06  monotx_time:                            0.
% 2.54/1.06  subtype_inf_time:                       0.
% 2.54/1.06  
% 2.54/1.06  ------ Problem properties
% 2.54/1.06  
% 2.54/1.06  clauses:                                20
% 2.54/1.06  conjectures:                            3
% 2.54/1.06  epr:                                    2
% 2.54/1.06  horn:                                   18
% 2.54/1.06  ground:                                 5
% 2.54/1.06  unary:                                  3
% 2.54/1.06  binary:                                 7
% 2.54/1.06  lits:                                   50
% 2.54/1.06  lits_eq:                                12
% 2.54/1.06  fd_pure:                                0
% 2.54/1.06  fd_pseudo:                              0
% 2.54/1.06  fd_cond:                                0
% 2.54/1.06  fd_pseudo_cond:                         1
% 2.54/1.06  ac_symbols:                             0
% 2.54/1.06  
% 2.54/1.06  ------ Propositional Solver
% 2.54/1.06  
% 2.54/1.06  prop_solver_calls:                      31
% 2.54/1.06  prop_fast_solver_calls:                 952
% 2.54/1.06  smt_solver_calls:                       0
% 2.54/1.06  smt_fast_solver_calls:                  0
% 2.54/1.06  prop_num_of_clauses:                    1030
% 2.54/1.06  prop_preprocess_simplified:             4239
% 2.54/1.06  prop_fo_subsumed:                       10
% 2.54/1.06  prop_solver_time:                       0.
% 2.54/1.06  smt_solver_time:                        0.
% 2.54/1.06  smt_fast_solver_time:                   0.
% 2.54/1.06  prop_fast_solver_time:                  0.
% 2.54/1.06  prop_unsat_core_time:                   0.
% 2.54/1.06  
% 2.54/1.06  ------ QBF
% 2.54/1.06  
% 2.54/1.06  qbf_q_res:                              0
% 2.54/1.06  qbf_num_tautologies:                    0
% 2.54/1.06  qbf_prep_cycles:                        0
% 2.54/1.06  
% 2.54/1.06  ------ BMC1
% 2.54/1.06  
% 2.54/1.06  bmc1_current_bound:                     -1
% 2.54/1.06  bmc1_last_solved_bound:                 -1
% 2.54/1.06  bmc1_unsat_core_size:                   -1
% 2.54/1.06  bmc1_unsat_core_parents_size:           -1
% 2.54/1.06  bmc1_merge_next_fun:                    0
% 2.54/1.06  bmc1_unsat_core_clauses_time:           0.
% 2.54/1.06  
% 2.54/1.06  ------ Instantiation
% 2.54/1.06  
% 2.54/1.06  inst_num_of_clauses:                    301
% 2.54/1.06  inst_num_in_passive:                    60
% 2.54/1.06  inst_num_in_active:                     226
% 2.54/1.06  inst_num_in_unprocessed:                15
% 2.54/1.06  inst_num_of_loops:                      280
% 2.54/1.06  inst_num_of_learning_restarts:          0
% 2.54/1.06  inst_num_moves_active_passive:          48
% 2.54/1.06  inst_lit_activity:                      0
% 2.54/1.06  inst_lit_activity_moves:                0
% 2.54/1.06  inst_num_tautologies:                   0
% 2.54/1.06  inst_num_prop_implied:                  0
% 2.54/1.06  inst_num_existing_simplified:           0
% 2.54/1.06  inst_num_eq_res_simplified:             0
% 2.54/1.06  inst_num_child_elim:                    0
% 2.54/1.06  inst_num_of_dismatching_blockings:      32
% 2.54/1.06  inst_num_of_non_proper_insts:           355
% 2.54/1.06  inst_num_of_duplicates:                 0
% 2.54/1.06  inst_inst_num_from_inst_to_res:         0
% 2.54/1.06  inst_dismatching_checking_time:         0.
% 2.54/1.06  
% 2.54/1.06  ------ Resolution
% 2.54/1.06  
% 2.54/1.06  res_num_of_clauses:                     0
% 2.54/1.06  res_num_in_passive:                     0
% 2.54/1.06  res_num_in_active:                      0
% 2.54/1.06  res_num_of_loops:                       118
% 2.54/1.06  res_forward_subset_subsumed:            50
% 2.54/1.06  res_backward_subset_subsumed:           2
% 2.54/1.06  res_forward_subsumed:                   0
% 2.54/1.06  res_backward_subsumed:                  0
% 2.54/1.06  res_forward_subsumption_resolution:     0
% 2.54/1.06  res_backward_subsumption_resolution:    0
% 2.54/1.06  res_clause_to_clause_subsumption:       196
% 2.54/1.06  res_orphan_elimination:                 0
% 2.54/1.06  res_tautology_del:                      88
% 2.54/1.06  res_num_eq_res_simplified:              0
% 2.54/1.06  res_num_sel_changes:                    0
% 2.54/1.06  res_moves_from_active_to_pass:          0
% 2.54/1.06  
% 2.54/1.06  ------ Superposition
% 2.54/1.06  
% 2.54/1.06  sup_time_total:                         0.
% 2.54/1.06  sup_time_generating:                    0.
% 2.54/1.06  sup_time_sim_full:                      0.
% 2.54/1.06  sup_time_sim_immed:                     0.
% 2.54/1.06  
% 2.54/1.06  sup_num_of_clauses:                     76
% 2.54/1.06  sup_num_in_active:                      40
% 2.54/1.06  sup_num_in_passive:                     36
% 2.54/1.06  sup_num_of_loops:                       55
% 2.54/1.06  sup_fw_superposition:                   37
% 2.54/1.06  sup_bw_superposition:                   42
% 2.54/1.06  sup_immediate_simplified:               12
% 2.54/1.06  sup_given_eliminated:                   0
% 2.54/1.06  comparisons_done:                       0
% 2.54/1.06  comparisons_avoided:                    6
% 2.54/1.06  
% 2.54/1.06  ------ Simplifications
% 2.54/1.06  
% 2.54/1.06  
% 2.54/1.06  sim_fw_subset_subsumed:                 6
% 2.54/1.06  sim_bw_subset_subsumed:                 3
% 2.54/1.06  sim_fw_subsumed:                        3
% 2.54/1.06  sim_bw_subsumed:                        1
% 2.54/1.06  sim_fw_subsumption_res:                 1
% 2.54/1.06  sim_bw_subsumption_res:                 0
% 2.54/1.06  sim_tautology_del:                      1
% 2.54/1.06  sim_eq_tautology_del:                   2
% 2.54/1.06  sim_eq_res_simp:                        1
% 2.54/1.06  sim_fw_demodulated:                     0
% 2.54/1.06  sim_bw_demodulated:                     14
% 2.54/1.06  sim_light_normalised:                   2
% 2.54/1.06  sim_joinable_taut:                      0
% 2.54/1.06  sim_joinable_simp:                      0
% 2.54/1.06  sim_ac_normalised:                      0
% 2.54/1.06  sim_smt_subsumption:                    0
% 2.54/1.06  
%------------------------------------------------------------------------------
