%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:28 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 206 expanded)
%              Number of clauses        :   66 (  75 expanded)
%              Number of leaves         :   17 (  39 expanded)
%              Depth                    :   19
%              Number of atoms          :  355 ( 811 expanded)
%              Number of equality atoms :  134 ( 215 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => ( r2_hidden(k1_funct_1(X3,X2),X1)
            | k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_hidden(k1_funct_1(X3,X2),X1)
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_hidden(k1_funct_1(X3,X2),X1)
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f31])).

fof(f40,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_hidden(k1_funct_1(X3,X2),X1)
        & k1_xboole_0 != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ~ r2_hidden(k1_funct_1(sK4,sK3),sK2)
      & k1_xboole_0 != sK2
      & r2_hidden(sK3,sK1)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK3),sK2)
    & k1_xboole_0 != sK2
    & r2_hidden(sK3,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f32,f40])).

fof(f66,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

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
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f68,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f64,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f69,plain,(
    ~ r2_hidden(k1_funct_1(sK4,sK3),sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f67,plain,(
    r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_914,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_918,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1649,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_914,c_918])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_370,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK1 != X1
    | sK2 != X2
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_26])).

cnf(c_371,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_370])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_373,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_371,c_25,c_23])).

cnf(c_1650,plain,
    ( k1_relat_1(sK4) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1649,c_373])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_306,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_27])).

cnf(c_307,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_306])).

cnf(c_913,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_307])).

cnf(c_1689,plain,
    ( r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1650,c_913])).

cnf(c_30,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1068,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1278,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1068])).

cnf(c_1279,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1278])).

cnf(c_11,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1490,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1491,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1490])).

cnf(c_2302,plain,
    ( r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top
    | r2_hidden(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1689,c_30,c_1279,c_1491])).

cnf(c_2303,plain,
    ( r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2302])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_917,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1258,plain,
    ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_914,c_917])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_919,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1766,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1258,c_919])).

cnf(c_2284,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1766,c_30])).

cnf(c_9,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_922,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2512,plain,
    ( m1_subset_1(X0,sK2) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2284,c_922])).

cnf(c_2696,plain,
    ( m1_subset_1(k1_funct_1(sK4,X0),sK2) = iProver_top
    | r2_hidden(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2303,c_2512])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_923,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2714,plain,
    ( r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),sK2) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2696,c_923])).

cnf(c_22,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(sK4,sK3),sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_916,plain,
    ( r2_hidden(k1_funct_1(sK4,sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2968,plain,
    ( r2_hidden(sK3,sK1) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2714,c_916])).

cnf(c_24,negated_conjecture,
    ( r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_31,plain,
    ( r2_hidden(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3047,plain,
    ( v1_xboole_0(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2968,c_31])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_928,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_930,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1820,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_928,c_930])).

cnf(c_7,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_924,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_926,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1927,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_924,c_926])).

cnf(c_2585,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1820,c_1927])).

cnf(c_3390,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3047,c_2585])).

cnf(c_544,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1098,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_544])).

cnf(c_1099,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1098])).

cnf(c_79,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_74,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3390,c_1099,c_79,c_74,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:01:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.10/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/0.97  
% 2.10/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.10/0.97  
% 2.10/0.97  ------  iProver source info
% 2.10/0.97  
% 2.10/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.10/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.10/0.97  git: non_committed_changes: false
% 2.10/0.97  git: last_make_outside_of_git: false
% 2.10/0.97  
% 2.10/0.97  ------ 
% 2.10/0.97  
% 2.10/0.97  ------ Input Options
% 2.10/0.97  
% 2.10/0.97  --out_options                           all
% 2.10/0.97  --tptp_safe_out                         true
% 2.10/0.97  --problem_path                          ""
% 2.10/0.97  --include_path                          ""
% 2.10/0.97  --clausifier                            res/vclausify_rel
% 2.10/0.97  --clausifier_options                    --mode clausify
% 2.10/0.97  --stdin                                 false
% 2.10/0.97  --stats_out                             all
% 2.10/0.97  
% 2.10/0.97  ------ General Options
% 2.10/0.97  
% 2.10/0.97  --fof                                   false
% 2.10/0.97  --time_out_real                         305.
% 2.10/0.97  --time_out_virtual                      -1.
% 2.10/0.97  --symbol_type_check                     false
% 2.10/0.97  --clausify_out                          false
% 2.10/0.97  --sig_cnt_out                           false
% 2.10/0.97  --trig_cnt_out                          false
% 2.10/0.97  --trig_cnt_out_tolerance                1.
% 2.10/0.97  --trig_cnt_out_sk_spl                   false
% 2.10/0.97  --abstr_cl_out                          false
% 2.10/0.97  
% 2.10/0.97  ------ Global Options
% 2.10/0.97  
% 2.10/0.97  --schedule                              default
% 2.10/0.97  --add_important_lit                     false
% 2.10/0.97  --prop_solver_per_cl                    1000
% 2.10/0.97  --min_unsat_core                        false
% 2.10/0.97  --soft_assumptions                      false
% 2.10/0.97  --soft_lemma_size                       3
% 2.10/0.97  --prop_impl_unit_size                   0
% 2.10/0.97  --prop_impl_unit                        []
% 2.10/0.97  --share_sel_clauses                     true
% 2.10/0.97  --reset_solvers                         false
% 2.10/0.97  --bc_imp_inh                            [conj_cone]
% 2.10/0.97  --conj_cone_tolerance                   3.
% 2.10/0.97  --extra_neg_conj                        none
% 2.10/0.97  --large_theory_mode                     true
% 2.10/0.97  --prolific_symb_bound                   200
% 2.10/0.97  --lt_threshold                          2000
% 2.10/0.97  --clause_weak_htbl                      true
% 2.10/0.97  --gc_record_bc_elim                     false
% 2.10/0.97  
% 2.10/0.97  ------ Preprocessing Options
% 2.10/0.97  
% 2.10/0.97  --preprocessing_flag                    true
% 2.10/0.97  --time_out_prep_mult                    0.1
% 2.10/0.97  --splitting_mode                        input
% 2.10/0.97  --splitting_grd                         true
% 2.10/0.97  --splitting_cvd                         false
% 2.10/0.97  --splitting_cvd_svl                     false
% 2.10/0.97  --splitting_nvd                         32
% 2.10/0.97  --sub_typing                            true
% 2.10/0.97  --prep_gs_sim                           true
% 2.10/0.97  --prep_unflatten                        true
% 2.10/0.97  --prep_res_sim                          true
% 2.10/0.97  --prep_upred                            true
% 2.10/0.97  --prep_sem_filter                       exhaustive
% 2.10/0.97  --prep_sem_filter_out                   false
% 2.10/0.97  --pred_elim                             true
% 2.10/0.97  --res_sim_input                         true
% 2.10/0.97  --eq_ax_congr_red                       true
% 2.10/0.97  --pure_diseq_elim                       true
% 2.10/0.97  --brand_transform                       false
% 2.10/0.97  --non_eq_to_eq                          false
% 2.10/0.97  --prep_def_merge                        true
% 2.10/0.97  --prep_def_merge_prop_impl              false
% 2.10/0.97  --prep_def_merge_mbd                    true
% 2.10/0.97  --prep_def_merge_tr_red                 false
% 2.10/0.97  --prep_def_merge_tr_cl                  false
% 2.10/0.97  --smt_preprocessing                     true
% 2.10/0.97  --smt_ac_axioms                         fast
% 2.10/0.97  --preprocessed_out                      false
% 2.10/0.97  --preprocessed_stats                    false
% 2.10/0.97  
% 2.10/0.97  ------ Abstraction refinement Options
% 2.10/0.97  
% 2.10/0.97  --abstr_ref                             []
% 2.10/0.97  --abstr_ref_prep                        false
% 2.10/0.97  --abstr_ref_until_sat                   false
% 2.10/0.97  --abstr_ref_sig_restrict                funpre
% 2.10/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.10/0.97  --abstr_ref_under                       []
% 2.10/0.97  
% 2.10/0.97  ------ SAT Options
% 2.10/0.97  
% 2.10/0.97  --sat_mode                              false
% 2.10/0.97  --sat_fm_restart_options                ""
% 2.10/0.97  --sat_gr_def                            false
% 2.10/0.97  --sat_epr_types                         true
% 2.10/0.97  --sat_non_cyclic_types                  false
% 2.10/0.97  --sat_finite_models                     false
% 2.10/0.97  --sat_fm_lemmas                         false
% 2.10/0.97  --sat_fm_prep                           false
% 2.10/0.97  --sat_fm_uc_incr                        true
% 2.10/0.97  --sat_out_model                         small
% 2.10/0.97  --sat_out_clauses                       false
% 2.10/0.97  
% 2.10/0.97  ------ QBF Options
% 2.10/0.97  
% 2.10/0.97  --qbf_mode                              false
% 2.10/0.97  --qbf_elim_univ                         false
% 2.10/0.97  --qbf_dom_inst                          none
% 2.10/0.97  --qbf_dom_pre_inst                      false
% 2.10/0.97  --qbf_sk_in                             false
% 2.10/0.97  --qbf_pred_elim                         true
% 2.10/0.97  --qbf_split                             512
% 2.10/0.97  
% 2.10/0.97  ------ BMC1 Options
% 2.10/0.97  
% 2.10/0.97  --bmc1_incremental                      false
% 2.10/0.97  --bmc1_axioms                           reachable_all
% 2.10/0.97  --bmc1_min_bound                        0
% 2.10/0.97  --bmc1_max_bound                        -1
% 2.10/0.97  --bmc1_max_bound_default                -1
% 2.10/0.97  --bmc1_symbol_reachability              true
% 2.10/0.97  --bmc1_property_lemmas                  false
% 2.10/0.97  --bmc1_k_induction                      false
% 2.10/0.97  --bmc1_non_equiv_states                 false
% 2.10/0.97  --bmc1_deadlock                         false
% 2.10/0.97  --bmc1_ucm                              false
% 2.10/0.97  --bmc1_add_unsat_core                   none
% 2.10/0.97  --bmc1_unsat_core_children              false
% 2.10/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.10/0.97  --bmc1_out_stat                         full
% 2.10/0.97  --bmc1_ground_init                      false
% 2.10/0.97  --bmc1_pre_inst_next_state              false
% 2.10/0.97  --bmc1_pre_inst_state                   false
% 2.10/0.97  --bmc1_pre_inst_reach_state             false
% 2.10/0.97  --bmc1_out_unsat_core                   false
% 2.10/0.97  --bmc1_aig_witness_out                  false
% 2.10/0.97  --bmc1_verbose                          false
% 2.10/0.97  --bmc1_dump_clauses_tptp                false
% 2.10/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.10/0.97  --bmc1_dump_file                        -
% 2.10/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.10/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.10/0.97  --bmc1_ucm_extend_mode                  1
% 2.10/0.97  --bmc1_ucm_init_mode                    2
% 2.10/0.97  --bmc1_ucm_cone_mode                    none
% 2.10/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.10/0.97  --bmc1_ucm_relax_model                  4
% 2.10/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.10/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.10/0.97  --bmc1_ucm_layered_model                none
% 2.10/0.97  --bmc1_ucm_max_lemma_size               10
% 2.10/0.97  
% 2.10/0.97  ------ AIG Options
% 2.10/0.97  
% 2.10/0.97  --aig_mode                              false
% 2.10/0.97  
% 2.10/0.97  ------ Instantiation Options
% 2.10/0.97  
% 2.10/0.97  --instantiation_flag                    true
% 2.10/0.97  --inst_sos_flag                         false
% 2.10/0.97  --inst_sos_phase                        true
% 2.10/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.10/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.10/0.97  --inst_lit_sel_side                     num_symb
% 2.10/0.97  --inst_solver_per_active                1400
% 2.10/0.97  --inst_solver_calls_frac                1.
% 2.10/0.97  --inst_passive_queue_type               priority_queues
% 2.10/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.10/0.97  --inst_passive_queues_freq              [25;2]
% 2.10/0.97  --inst_dismatching                      true
% 2.10/0.97  --inst_eager_unprocessed_to_passive     true
% 2.10/0.97  --inst_prop_sim_given                   true
% 2.10/0.97  --inst_prop_sim_new                     false
% 2.10/0.97  --inst_subs_new                         false
% 2.10/0.97  --inst_eq_res_simp                      false
% 2.10/0.97  --inst_subs_given                       false
% 2.10/0.97  --inst_orphan_elimination               true
% 2.10/0.97  --inst_learning_loop_flag               true
% 2.10/0.97  --inst_learning_start                   3000
% 2.10/0.97  --inst_learning_factor                  2
% 2.10/0.97  --inst_start_prop_sim_after_learn       3
% 2.10/0.97  --inst_sel_renew                        solver
% 2.10/0.97  --inst_lit_activity_flag                true
% 2.10/0.97  --inst_restr_to_given                   false
% 2.10/0.97  --inst_activity_threshold               500
% 2.10/0.97  --inst_out_proof                        true
% 2.10/0.97  
% 2.10/0.97  ------ Resolution Options
% 2.10/0.97  
% 2.10/0.97  --resolution_flag                       true
% 2.10/0.97  --res_lit_sel                           adaptive
% 2.10/0.97  --res_lit_sel_side                      none
% 2.10/0.97  --res_ordering                          kbo
% 2.10/0.97  --res_to_prop_solver                    active
% 2.10/0.97  --res_prop_simpl_new                    false
% 2.10/0.97  --res_prop_simpl_given                  true
% 2.10/0.97  --res_passive_queue_type                priority_queues
% 2.10/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.10/0.97  --res_passive_queues_freq               [15;5]
% 2.10/0.97  --res_forward_subs                      full
% 2.10/0.97  --res_backward_subs                     full
% 2.10/0.97  --res_forward_subs_resolution           true
% 2.10/0.97  --res_backward_subs_resolution          true
% 2.10/0.97  --res_orphan_elimination                true
% 2.10/0.97  --res_time_limit                        2.
% 2.10/0.97  --res_out_proof                         true
% 2.10/0.97  
% 2.10/0.97  ------ Superposition Options
% 2.10/0.97  
% 2.10/0.97  --superposition_flag                    true
% 2.10/0.97  --sup_passive_queue_type                priority_queues
% 2.10/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.10/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.10/0.97  --demod_completeness_check              fast
% 2.10/0.97  --demod_use_ground                      true
% 2.10/0.97  --sup_to_prop_solver                    passive
% 2.10/0.97  --sup_prop_simpl_new                    true
% 2.10/0.97  --sup_prop_simpl_given                  true
% 2.10/0.97  --sup_fun_splitting                     false
% 2.10/0.97  --sup_smt_interval                      50000
% 2.10/0.97  
% 2.10/0.97  ------ Superposition Simplification Setup
% 2.10/0.97  
% 2.10/0.97  --sup_indices_passive                   []
% 2.10/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.10/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/0.97  --sup_full_bw                           [BwDemod]
% 2.10/0.97  --sup_immed_triv                        [TrivRules]
% 2.10/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.10/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/0.97  --sup_immed_bw_main                     []
% 2.10/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.10/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.10/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.10/0.97  
% 2.10/0.97  ------ Combination Options
% 2.10/0.97  
% 2.10/0.97  --comb_res_mult                         3
% 2.10/0.97  --comb_sup_mult                         2
% 2.10/0.97  --comb_inst_mult                        10
% 2.10/0.97  
% 2.10/0.97  ------ Debug Options
% 2.10/0.97  
% 2.10/0.97  --dbg_backtrace                         false
% 2.10/0.97  --dbg_dump_prop_clauses                 false
% 2.10/0.97  --dbg_dump_prop_clauses_file            -
% 2.10/0.97  --dbg_out_stat                          false
% 2.10/0.97  ------ Parsing...
% 2.10/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.10/0.97  
% 2.10/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.10/0.97  
% 2.10/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.10/0.97  
% 2.10/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.10/0.97  ------ Proving...
% 2.10/0.97  ------ Problem Properties 
% 2.10/0.97  
% 2.10/0.97  
% 2.10/0.97  clauses                                 22
% 2.10/0.97  conjectures                             4
% 2.10/0.97  EPR                                     8
% 2.10/0.97  Horn                                    19
% 2.10/0.97  unary                                   8
% 2.10/0.97  binary                                  6
% 2.10/0.97  lits                                    45
% 2.10/0.97  lits eq                                 10
% 2.10/0.97  fd_pure                                 0
% 2.10/0.97  fd_pseudo                               0
% 2.10/0.97  fd_cond                                 0
% 2.10/0.97  fd_pseudo_cond                          1
% 2.10/0.97  AC symbols                              0
% 2.10/0.97  
% 2.10/0.97  ------ Schedule dynamic 5 is on 
% 2.10/0.97  
% 2.10/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.10/0.97  
% 2.10/0.97  
% 2.10/0.97  ------ 
% 2.10/0.97  Current options:
% 2.10/0.97  ------ 
% 2.10/0.97  
% 2.10/0.97  ------ Input Options
% 2.10/0.97  
% 2.10/0.97  --out_options                           all
% 2.10/0.97  --tptp_safe_out                         true
% 2.10/0.97  --problem_path                          ""
% 2.10/0.97  --include_path                          ""
% 2.10/0.97  --clausifier                            res/vclausify_rel
% 2.10/0.97  --clausifier_options                    --mode clausify
% 2.10/0.97  --stdin                                 false
% 2.10/0.97  --stats_out                             all
% 2.10/0.97  
% 2.10/0.97  ------ General Options
% 2.10/0.97  
% 2.10/0.97  --fof                                   false
% 2.10/0.97  --time_out_real                         305.
% 2.10/0.97  --time_out_virtual                      -1.
% 2.10/0.97  --symbol_type_check                     false
% 2.10/0.97  --clausify_out                          false
% 2.10/0.97  --sig_cnt_out                           false
% 2.10/0.97  --trig_cnt_out                          false
% 2.10/0.97  --trig_cnt_out_tolerance                1.
% 2.10/0.97  --trig_cnt_out_sk_spl                   false
% 2.10/0.97  --abstr_cl_out                          false
% 2.10/0.97  
% 2.10/0.97  ------ Global Options
% 2.10/0.97  
% 2.10/0.97  --schedule                              default
% 2.10/0.97  --add_important_lit                     false
% 2.10/0.97  --prop_solver_per_cl                    1000
% 2.10/0.97  --min_unsat_core                        false
% 2.10/0.97  --soft_assumptions                      false
% 2.10/0.97  --soft_lemma_size                       3
% 2.10/0.97  --prop_impl_unit_size                   0
% 2.10/0.97  --prop_impl_unit                        []
% 2.10/0.97  --share_sel_clauses                     true
% 2.10/0.97  --reset_solvers                         false
% 2.10/0.97  --bc_imp_inh                            [conj_cone]
% 2.10/0.97  --conj_cone_tolerance                   3.
% 2.10/0.97  --extra_neg_conj                        none
% 2.10/0.97  --large_theory_mode                     true
% 2.10/0.97  --prolific_symb_bound                   200
% 2.10/0.97  --lt_threshold                          2000
% 2.10/0.97  --clause_weak_htbl                      true
% 2.10/0.97  --gc_record_bc_elim                     false
% 2.10/0.97  
% 2.10/0.97  ------ Preprocessing Options
% 2.10/0.97  
% 2.10/0.97  --preprocessing_flag                    true
% 2.10/0.97  --time_out_prep_mult                    0.1
% 2.10/0.97  --splitting_mode                        input
% 2.10/0.97  --splitting_grd                         true
% 2.10/0.97  --splitting_cvd                         false
% 2.10/0.97  --splitting_cvd_svl                     false
% 2.10/0.97  --splitting_nvd                         32
% 2.10/0.97  --sub_typing                            true
% 2.10/0.97  --prep_gs_sim                           true
% 2.10/0.97  --prep_unflatten                        true
% 2.10/0.97  --prep_res_sim                          true
% 2.10/0.97  --prep_upred                            true
% 2.10/0.97  --prep_sem_filter                       exhaustive
% 2.10/0.97  --prep_sem_filter_out                   false
% 2.10/0.97  --pred_elim                             true
% 2.10/0.97  --res_sim_input                         true
% 2.10/0.97  --eq_ax_congr_red                       true
% 2.10/0.97  --pure_diseq_elim                       true
% 2.10/0.97  --brand_transform                       false
% 2.10/0.97  --non_eq_to_eq                          false
% 2.10/0.97  --prep_def_merge                        true
% 2.10/0.97  --prep_def_merge_prop_impl              false
% 2.10/0.97  --prep_def_merge_mbd                    true
% 2.10/0.97  --prep_def_merge_tr_red                 false
% 2.10/0.97  --prep_def_merge_tr_cl                  false
% 2.10/0.97  --smt_preprocessing                     true
% 2.10/0.97  --smt_ac_axioms                         fast
% 2.10/0.97  --preprocessed_out                      false
% 2.10/0.97  --preprocessed_stats                    false
% 2.10/0.97  
% 2.10/0.97  ------ Abstraction refinement Options
% 2.10/0.97  
% 2.10/0.97  --abstr_ref                             []
% 2.10/0.97  --abstr_ref_prep                        false
% 2.10/0.97  --abstr_ref_until_sat                   false
% 2.10/0.97  --abstr_ref_sig_restrict                funpre
% 2.10/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.10/0.97  --abstr_ref_under                       []
% 2.10/0.97  
% 2.10/0.97  ------ SAT Options
% 2.10/0.97  
% 2.10/0.97  --sat_mode                              false
% 2.10/0.97  --sat_fm_restart_options                ""
% 2.10/0.97  --sat_gr_def                            false
% 2.10/0.97  --sat_epr_types                         true
% 2.10/0.97  --sat_non_cyclic_types                  false
% 2.10/0.97  --sat_finite_models                     false
% 2.10/0.97  --sat_fm_lemmas                         false
% 2.10/0.97  --sat_fm_prep                           false
% 2.10/0.97  --sat_fm_uc_incr                        true
% 2.10/0.97  --sat_out_model                         small
% 2.10/0.97  --sat_out_clauses                       false
% 2.10/0.97  
% 2.10/0.97  ------ QBF Options
% 2.10/0.97  
% 2.10/0.97  --qbf_mode                              false
% 2.10/0.97  --qbf_elim_univ                         false
% 2.10/0.97  --qbf_dom_inst                          none
% 2.10/0.97  --qbf_dom_pre_inst                      false
% 2.10/0.97  --qbf_sk_in                             false
% 2.10/0.97  --qbf_pred_elim                         true
% 2.10/0.97  --qbf_split                             512
% 2.10/0.97  
% 2.10/0.97  ------ BMC1 Options
% 2.10/0.97  
% 2.10/0.97  --bmc1_incremental                      false
% 2.10/0.97  --bmc1_axioms                           reachable_all
% 2.10/0.97  --bmc1_min_bound                        0
% 2.10/0.97  --bmc1_max_bound                        -1
% 2.10/0.97  --bmc1_max_bound_default                -1
% 2.10/0.97  --bmc1_symbol_reachability              true
% 2.10/0.97  --bmc1_property_lemmas                  false
% 2.10/0.97  --bmc1_k_induction                      false
% 2.10/0.97  --bmc1_non_equiv_states                 false
% 2.10/0.97  --bmc1_deadlock                         false
% 2.10/0.97  --bmc1_ucm                              false
% 2.10/0.97  --bmc1_add_unsat_core                   none
% 2.10/0.97  --bmc1_unsat_core_children              false
% 2.10/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.10/0.97  --bmc1_out_stat                         full
% 2.10/0.97  --bmc1_ground_init                      false
% 2.10/0.97  --bmc1_pre_inst_next_state              false
% 2.10/0.97  --bmc1_pre_inst_state                   false
% 2.10/0.97  --bmc1_pre_inst_reach_state             false
% 2.10/0.97  --bmc1_out_unsat_core                   false
% 2.10/0.97  --bmc1_aig_witness_out                  false
% 2.10/0.97  --bmc1_verbose                          false
% 2.10/0.97  --bmc1_dump_clauses_tptp                false
% 2.10/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.10/0.97  --bmc1_dump_file                        -
% 2.10/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.10/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.10/0.97  --bmc1_ucm_extend_mode                  1
% 2.10/0.97  --bmc1_ucm_init_mode                    2
% 2.10/0.97  --bmc1_ucm_cone_mode                    none
% 2.10/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.10/0.97  --bmc1_ucm_relax_model                  4
% 2.10/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.10/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.10/0.97  --bmc1_ucm_layered_model                none
% 2.10/0.97  --bmc1_ucm_max_lemma_size               10
% 2.10/0.97  
% 2.10/0.97  ------ AIG Options
% 2.10/0.97  
% 2.10/0.97  --aig_mode                              false
% 2.10/0.97  
% 2.10/0.97  ------ Instantiation Options
% 2.10/0.97  
% 2.10/0.97  --instantiation_flag                    true
% 2.10/0.97  --inst_sos_flag                         false
% 2.10/0.97  --inst_sos_phase                        true
% 2.10/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.10/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.10/0.97  --inst_lit_sel_side                     none
% 2.10/0.97  --inst_solver_per_active                1400
% 2.10/0.97  --inst_solver_calls_frac                1.
% 2.10/0.97  --inst_passive_queue_type               priority_queues
% 2.10/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.10/0.97  --inst_passive_queues_freq              [25;2]
% 2.10/0.97  --inst_dismatching                      true
% 2.10/0.97  --inst_eager_unprocessed_to_passive     true
% 2.10/0.97  --inst_prop_sim_given                   true
% 2.10/0.97  --inst_prop_sim_new                     false
% 2.10/0.97  --inst_subs_new                         false
% 2.10/0.97  --inst_eq_res_simp                      false
% 2.10/0.97  --inst_subs_given                       false
% 2.10/0.97  --inst_orphan_elimination               true
% 2.10/0.97  --inst_learning_loop_flag               true
% 2.10/0.97  --inst_learning_start                   3000
% 2.10/0.97  --inst_learning_factor                  2
% 2.10/0.97  --inst_start_prop_sim_after_learn       3
% 2.10/0.97  --inst_sel_renew                        solver
% 2.10/0.97  --inst_lit_activity_flag                true
% 2.10/0.97  --inst_restr_to_given                   false
% 2.10/0.97  --inst_activity_threshold               500
% 2.10/0.97  --inst_out_proof                        true
% 2.10/0.97  
% 2.10/0.97  ------ Resolution Options
% 2.10/0.97  
% 2.10/0.97  --resolution_flag                       false
% 2.10/0.97  --res_lit_sel                           adaptive
% 2.10/0.97  --res_lit_sel_side                      none
% 2.10/0.97  --res_ordering                          kbo
% 2.10/0.97  --res_to_prop_solver                    active
% 2.10/0.97  --res_prop_simpl_new                    false
% 2.10/0.97  --res_prop_simpl_given                  true
% 2.10/0.97  --res_passive_queue_type                priority_queues
% 2.10/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.10/0.97  --res_passive_queues_freq               [15;5]
% 2.10/0.97  --res_forward_subs                      full
% 2.10/0.97  --res_backward_subs                     full
% 2.10/0.97  --res_forward_subs_resolution           true
% 2.10/0.97  --res_backward_subs_resolution          true
% 2.10/0.97  --res_orphan_elimination                true
% 2.10/0.97  --res_time_limit                        2.
% 2.10/0.97  --res_out_proof                         true
% 2.10/0.97  
% 2.10/0.97  ------ Superposition Options
% 2.10/0.97  
% 2.10/0.97  --superposition_flag                    true
% 2.10/0.97  --sup_passive_queue_type                priority_queues
% 2.10/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.10/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.10/0.97  --demod_completeness_check              fast
% 2.10/0.97  --demod_use_ground                      true
% 2.10/0.97  --sup_to_prop_solver                    passive
% 2.10/0.97  --sup_prop_simpl_new                    true
% 2.10/0.97  --sup_prop_simpl_given                  true
% 2.10/0.97  --sup_fun_splitting                     false
% 2.10/0.97  --sup_smt_interval                      50000
% 2.10/0.97  
% 2.10/0.97  ------ Superposition Simplification Setup
% 2.10/0.97  
% 2.10/0.97  --sup_indices_passive                   []
% 2.10/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.10/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/0.97  --sup_full_bw                           [BwDemod]
% 2.10/0.97  --sup_immed_triv                        [TrivRules]
% 2.10/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.10/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/0.97  --sup_immed_bw_main                     []
% 2.10/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.10/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.10/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.10/0.97  
% 2.10/0.97  ------ Combination Options
% 2.10/0.97  
% 2.10/0.97  --comb_res_mult                         3
% 2.10/0.97  --comb_sup_mult                         2
% 2.10/0.97  --comb_inst_mult                        10
% 2.10/0.97  
% 2.10/0.97  ------ Debug Options
% 2.10/0.97  
% 2.10/0.97  --dbg_backtrace                         false
% 2.10/0.97  --dbg_dump_prop_clauses                 false
% 2.10/0.97  --dbg_dump_prop_clauses_file            -
% 2.10/0.97  --dbg_out_stat                          false
% 2.10/0.97  
% 2.10/0.97  
% 2.10/0.97  
% 2.10/0.97  
% 2.10/0.97  ------ Proving...
% 2.10/0.97  
% 2.10/0.97  
% 2.10/0.97  % SZS status Theorem for theBenchmark.p
% 2.10/0.97  
% 2.10/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.10/0.97  
% 2.10/0.97  fof(f14,conjecture,(
% 2.10/0.97    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 2.10/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/0.97  
% 2.10/0.97  fof(f15,negated_conjecture,(
% 2.10/0.97    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 2.10/0.97    inference(negated_conjecture,[],[f14])).
% 2.10/0.97  
% 2.10/0.97  fof(f31,plain,(
% 2.10/0.97    ? [X0,X1,X2,X3] : (((~r2_hidden(k1_funct_1(X3,X2),X1) & k1_xboole_0 != X1) & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 2.10/0.97    inference(ennf_transformation,[],[f15])).
% 2.10/0.97  
% 2.10/0.97  fof(f32,plain,(
% 2.10/0.97    ? [X0,X1,X2,X3] : (~r2_hidden(k1_funct_1(X3,X2),X1) & k1_xboole_0 != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 2.10/0.97    inference(flattening,[],[f31])).
% 2.10/0.97  
% 2.10/0.97  fof(f40,plain,(
% 2.10/0.97    ? [X0,X1,X2,X3] : (~r2_hidden(k1_funct_1(X3,X2),X1) & k1_xboole_0 != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_hidden(k1_funct_1(sK4,sK3),sK2) & k1_xboole_0 != sK2 & r2_hidden(sK3,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 2.10/0.97    introduced(choice_axiom,[])).
% 2.10/0.97  
% 2.10/0.97  fof(f41,plain,(
% 2.10/0.97    ~r2_hidden(k1_funct_1(sK4,sK3),sK2) & k1_xboole_0 != sK2 & r2_hidden(sK3,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)),
% 2.10/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f32,f40])).
% 2.10/0.97  
% 2.10/0.97  fof(f66,plain,(
% 2.10/0.97    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.10/0.97    inference(cnf_transformation,[],[f41])).
% 2.10/0.97  
% 2.10/0.97  fof(f11,axiom,(
% 2.10/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.10/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/0.97  
% 2.10/0.97  fof(f27,plain,(
% 2.10/0.97    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/0.97    inference(ennf_transformation,[],[f11])).
% 2.10/0.97  
% 2.10/0.97  fof(f56,plain,(
% 2.10/0.97    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.10/0.97    inference(cnf_transformation,[],[f27])).
% 2.10/0.97  
% 2.10/0.97  fof(f13,axiom,(
% 2.10/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.10/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/0.97  
% 2.10/0.97  fof(f29,plain,(
% 2.10/0.97    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/0.97    inference(ennf_transformation,[],[f13])).
% 2.10/0.97  
% 2.10/0.97  fof(f30,plain,(
% 2.10/0.97    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/0.97    inference(flattening,[],[f29])).
% 2.10/0.97  
% 2.10/0.97  fof(f39,plain,(
% 2.10/0.97    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/0.97    inference(nnf_transformation,[],[f30])).
% 2.10/0.97  
% 2.10/0.97  fof(f58,plain,(
% 2.10/0.97    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.10/0.97    inference(cnf_transformation,[],[f39])).
% 2.10/0.97  
% 2.10/0.97  fof(f65,plain,(
% 2.10/0.97    v1_funct_2(sK4,sK1,sK2)),
% 2.10/0.97    inference(cnf_transformation,[],[f41])).
% 2.10/0.97  
% 2.10/0.97  fof(f68,plain,(
% 2.10/0.97    k1_xboole_0 != sK2),
% 2.10/0.97    inference(cnf_transformation,[],[f41])).
% 2.10/0.98  
% 2.10/0.98  fof(f9,axiom,(
% 2.10/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 2.10/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/0.98  
% 2.10/0.98  fof(f24,plain,(
% 2.10/0.98    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.10/0.98    inference(ennf_transformation,[],[f9])).
% 2.10/0.98  
% 2.10/0.98  fof(f25,plain,(
% 2.10/0.98    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.10/0.98    inference(flattening,[],[f24])).
% 2.10/0.98  
% 2.10/0.98  fof(f54,plain,(
% 2.10/0.98    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.10/0.98    inference(cnf_transformation,[],[f25])).
% 2.10/0.98  
% 2.10/0.98  fof(f64,plain,(
% 2.10/0.98    v1_funct_1(sK4)),
% 2.10/0.98    inference(cnf_transformation,[],[f41])).
% 2.10/0.98  
% 2.10/0.98  fof(f7,axiom,(
% 2.10/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.10/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/0.98  
% 2.10/0.98  fof(f23,plain,(
% 2.10/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.10/0.98    inference(ennf_transformation,[],[f7])).
% 2.10/0.98  
% 2.10/0.98  fof(f52,plain,(
% 2.10/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.10/0.98    inference(cnf_transformation,[],[f23])).
% 2.10/0.98  
% 2.10/0.98  fof(f8,axiom,(
% 2.10/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.10/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/0.98  
% 2.10/0.98  fof(f53,plain,(
% 2.10/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.10/0.98    inference(cnf_transformation,[],[f8])).
% 2.10/0.98  
% 2.10/0.98  fof(f12,axiom,(
% 2.10/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.10/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/0.98  
% 2.10/0.98  fof(f28,plain,(
% 2.10/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/0.98    inference(ennf_transformation,[],[f12])).
% 2.10/0.98  
% 2.10/0.98  fof(f57,plain,(
% 2.10/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.10/0.98    inference(cnf_transformation,[],[f28])).
% 2.10/0.98  
% 2.10/0.98  fof(f10,axiom,(
% 2.10/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 2.10/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/0.98  
% 2.10/0.98  fof(f26,plain,(
% 2.10/0.98    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/0.98    inference(ennf_transformation,[],[f10])).
% 2.10/0.98  
% 2.10/0.98  fof(f55,plain,(
% 2.10/0.98    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.10/0.98    inference(cnf_transformation,[],[f26])).
% 2.10/0.98  
% 2.10/0.98  fof(f6,axiom,(
% 2.10/0.98    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.10/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/0.98  
% 2.10/0.98  fof(f21,plain,(
% 2.10/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.10/0.98    inference(ennf_transformation,[],[f6])).
% 2.10/0.98  
% 2.10/0.98  fof(f22,plain,(
% 2.10/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.10/0.98    inference(flattening,[],[f21])).
% 2.10/0.98  
% 2.10/0.98  fof(f51,plain,(
% 2.10/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.10/0.98    inference(cnf_transformation,[],[f22])).
% 2.10/0.98  
% 2.10/0.98  fof(f5,axiom,(
% 2.10/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.10/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/0.98  
% 2.10/0.98  fof(f19,plain,(
% 2.10/0.98    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.10/0.98    inference(ennf_transformation,[],[f5])).
% 2.10/0.98  
% 2.10/0.98  fof(f20,plain,(
% 2.10/0.98    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.10/0.98    inference(flattening,[],[f19])).
% 2.10/0.98  
% 2.10/0.98  fof(f50,plain,(
% 2.10/0.98    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.10/0.98    inference(cnf_transformation,[],[f20])).
% 2.10/0.98  
% 2.10/0.98  fof(f69,plain,(
% 2.10/0.98    ~r2_hidden(k1_funct_1(sK4,sK3),sK2)),
% 2.10/0.98    inference(cnf_transformation,[],[f41])).
% 2.10/0.98  
% 2.10/0.98  fof(f67,plain,(
% 2.10/0.98    r2_hidden(sK3,sK1)),
% 2.10/0.98    inference(cnf_transformation,[],[f41])).
% 2.10/0.98  
% 2.10/0.98  fof(f2,axiom,(
% 2.10/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.10/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/0.98  
% 2.10/0.98  fof(f18,plain,(
% 2.10/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.10/0.98    inference(ennf_transformation,[],[f2])).
% 2.10/0.98  
% 2.10/0.98  fof(f33,plain,(
% 2.10/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.10/0.98    inference(nnf_transformation,[],[f18])).
% 2.10/0.98  
% 2.10/0.98  fof(f34,plain,(
% 2.10/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.10/0.98    inference(rectify,[],[f33])).
% 2.10/0.98  
% 2.10/0.98  fof(f35,plain,(
% 2.10/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.10/0.98    introduced(choice_axiom,[])).
% 2.10/0.98  
% 2.10/0.98  fof(f36,plain,(
% 2.10/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.10/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 2.10/0.98  
% 2.10/0.98  fof(f44,plain,(
% 2.10/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.10/0.98    inference(cnf_transformation,[],[f36])).
% 2.10/0.98  
% 2.10/0.98  fof(f1,axiom,(
% 2.10/0.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.10/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/0.98  
% 2.10/0.98  fof(f16,plain,(
% 2.10/0.98    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 2.10/0.98    inference(unused_predicate_definition_removal,[],[f1])).
% 2.10/0.98  
% 2.10/0.98  fof(f17,plain,(
% 2.10/0.98    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 2.10/0.98    inference(ennf_transformation,[],[f16])).
% 2.10/0.98  
% 2.10/0.98  fof(f42,plain,(
% 2.10/0.98    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 2.10/0.98    inference(cnf_transformation,[],[f17])).
% 2.10/0.98  
% 2.10/0.98  fof(f4,axiom,(
% 2.10/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.10/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/0.98  
% 2.10/0.98  fof(f49,plain,(
% 2.10/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.10/0.98    inference(cnf_transformation,[],[f4])).
% 2.10/0.98  
% 2.10/0.98  fof(f3,axiom,(
% 2.10/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.10/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/0.98  
% 2.10/0.98  fof(f37,plain,(
% 2.10/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.10/0.98    inference(nnf_transformation,[],[f3])).
% 2.10/0.98  
% 2.10/0.98  fof(f38,plain,(
% 2.10/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.10/0.98    inference(flattening,[],[f37])).
% 2.10/0.98  
% 2.10/0.98  fof(f48,plain,(
% 2.10/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.10/0.98    inference(cnf_transformation,[],[f38])).
% 2.10/0.98  
% 2.10/0.98  cnf(c_25,negated_conjecture,
% 2.10/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.10/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_914,plain,
% 2.10/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.10/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_14,plain,
% 2.10/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.10/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.10/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_918,plain,
% 2.10/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.10/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.10/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_1649,plain,
% 2.10/0.98      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 2.10/0.98      inference(superposition,[status(thm)],[c_914,c_918]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_21,plain,
% 2.10/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.10/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.10/0.98      | k1_relset_1(X1,X2,X0) = X1
% 2.10/0.98      | k1_xboole_0 = X2 ),
% 2.10/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_26,negated_conjecture,
% 2.10/0.98      ( v1_funct_2(sK4,sK1,sK2) ),
% 2.10/0.98      inference(cnf_transformation,[],[f65]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_370,plain,
% 2.10/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.10/0.98      | k1_relset_1(X1,X2,X0) = X1
% 2.10/0.98      | sK1 != X1
% 2.10/0.98      | sK2 != X2
% 2.10/0.98      | sK4 != X0
% 2.10/0.98      | k1_xboole_0 = X2 ),
% 2.10/0.98      inference(resolution_lifted,[status(thm)],[c_21,c_26]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_371,plain,
% 2.10/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.10/0.98      | k1_relset_1(sK1,sK2,sK4) = sK1
% 2.10/0.98      | k1_xboole_0 = sK2 ),
% 2.10/0.98      inference(unflattening,[status(thm)],[c_370]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_23,negated_conjecture,
% 2.10/0.98      ( k1_xboole_0 != sK2 ),
% 2.10/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_373,plain,
% 2.10/0.98      ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
% 2.10/0.98      inference(global_propositional_subsumption,
% 2.10/0.98                [status(thm)],
% 2.10/0.98                [c_371,c_25,c_23]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_1650,plain,
% 2.10/0.98      ( k1_relat_1(sK4) = sK1 ),
% 2.10/0.98      inference(light_normalisation,[status(thm)],[c_1649,c_373]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_12,plain,
% 2.10/0.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.10/0.98      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 2.10/0.98      | ~ v1_funct_1(X1)
% 2.10/0.98      | ~ v1_relat_1(X1) ),
% 2.10/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_27,negated_conjecture,
% 2.10/0.98      ( v1_funct_1(sK4) ),
% 2.10/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_306,plain,
% 2.10/0.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.10/0.98      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 2.10/0.98      | ~ v1_relat_1(X1)
% 2.10/0.98      | sK4 != X1 ),
% 2.10/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_27]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_307,plain,
% 2.10/0.98      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 2.10/0.98      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
% 2.10/0.98      | ~ v1_relat_1(sK4) ),
% 2.10/0.98      inference(unflattening,[status(thm)],[c_306]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_913,plain,
% 2.10/0.98      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.10/0.98      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top
% 2.10/0.98      | v1_relat_1(sK4) != iProver_top ),
% 2.10/0.98      inference(predicate_to_equality,[status(thm)],[c_307]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_1689,plain,
% 2.10/0.98      ( r2_hidden(X0,sK1) != iProver_top
% 2.10/0.98      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top
% 2.10/0.98      | v1_relat_1(sK4) != iProver_top ),
% 2.10/0.98      inference(demodulation,[status(thm)],[c_1650,c_913]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_30,plain,
% 2.10/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.10/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_10,plain,
% 2.10/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.10/0.98      | ~ v1_relat_1(X1)
% 2.10/0.98      | v1_relat_1(X0) ),
% 2.10/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_1068,plain,
% 2.10/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.10/0.98      | v1_relat_1(X0)
% 2.10/0.98      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 2.10/0.98      inference(instantiation,[status(thm)],[c_10]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_1278,plain,
% 2.10/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.10/0.98      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
% 2.10/0.98      | v1_relat_1(sK4) ),
% 2.10/0.98      inference(instantiation,[status(thm)],[c_1068]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_1279,plain,
% 2.10/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.10/0.98      | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 2.10/0.98      | v1_relat_1(sK4) = iProver_top ),
% 2.10/0.98      inference(predicate_to_equality,[status(thm)],[c_1278]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_11,plain,
% 2.10/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.10/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_1490,plain,
% 2.10/0.98      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.10/0.98      inference(instantiation,[status(thm)],[c_11]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_1491,plain,
% 2.10/0.98      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 2.10/0.98      inference(predicate_to_equality,[status(thm)],[c_1490]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_2302,plain,
% 2.10/0.98      ( r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top
% 2.10/0.98      | r2_hidden(X0,sK1) != iProver_top ),
% 2.10/0.98      inference(global_propositional_subsumption,
% 2.10/0.98                [status(thm)],
% 2.10/0.98                [c_1689,c_30,c_1279,c_1491]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_2303,plain,
% 2.10/0.98      ( r2_hidden(X0,sK1) != iProver_top
% 2.10/0.98      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top ),
% 2.10/0.98      inference(renaming,[status(thm)],[c_2302]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_15,plain,
% 2.10/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.10/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.10/0.98      inference(cnf_transformation,[],[f57]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_917,plain,
% 2.10/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.10/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.10/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_1258,plain,
% 2.10/0.98      ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
% 2.10/0.98      inference(superposition,[status(thm)],[c_914,c_917]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_13,plain,
% 2.10/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.10/0.98      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 2.10/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_919,plain,
% 2.10/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.10/0.98      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 2.10/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_1766,plain,
% 2.10/0.98      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK2)) = iProver_top
% 2.10/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 2.10/0.98      inference(superposition,[status(thm)],[c_1258,c_919]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_2284,plain,
% 2.10/0.98      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK2)) = iProver_top ),
% 2.10/0.98      inference(global_propositional_subsumption,
% 2.10/0.98                [status(thm)],
% 2.10/0.98                [c_1766,c_30]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_9,plain,
% 2.10/0.98      ( m1_subset_1(X0,X1)
% 2.10/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.10/0.98      | ~ r2_hidden(X0,X2) ),
% 2.10/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_922,plain,
% 2.10/0.98      ( m1_subset_1(X0,X1) = iProver_top
% 2.10/0.98      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 2.10/0.98      | r2_hidden(X0,X2) != iProver_top ),
% 2.10/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_2512,plain,
% 2.10/0.98      ( m1_subset_1(X0,sK2) = iProver_top
% 2.10/0.98      | r2_hidden(X0,k2_relat_1(sK4)) != iProver_top ),
% 2.10/0.98      inference(superposition,[status(thm)],[c_2284,c_922]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_2696,plain,
% 2.10/0.98      ( m1_subset_1(k1_funct_1(sK4,X0),sK2) = iProver_top
% 2.10/0.98      | r2_hidden(X0,sK1) != iProver_top ),
% 2.10/0.98      inference(superposition,[status(thm)],[c_2303,c_2512]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_8,plain,
% 2.10/0.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.10/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_923,plain,
% 2.10/0.98      ( m1_subset_1(X0,X1) != iProver_top
% 2.10/0.98      | r2_hidden(X0,X1) = iProver_top
% 2.10/0.98      | v1_xboole_0(X1) = iProver_top ),
% 2.10/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_2714,plain,
% 2.10/0.98      ( r2_hidden(X0,sK1) != iProver_top
% 2.10/0.98      | r2_hidden(k1_funct_1(sK4,X0),sK2) = iProver_top
% 2.10/0.98      | v1_xboole_0(sK2) = iProver_top ),
% 2.10/0.98      inference(superposition,[status(thm)],[c_2696,c_923]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_22,negated_conjecture,
% 2.10/0.98      ( ~ r2_hidden(k1_funct_1(sK4,sK3),sK2) ),
% 2.10/0.98      inference(cnf_transformation,[],[f69]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_916,plain,
% 2.10/0.98      ( r2_hidden(k1_funct_1(sK4,sK3),sK2) != iProver_top ),
% 2.10/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_2968,plain,
% 2.10/0.98      ( r2_hidden(sK3,sK1) != iProver_top
% 2.10/0.98      | v1_xboole_0(sK2) = iProver_top ),
% 2.10/0.98      inference(superposition,[status(thm)],[c_2714,c_916]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_24,negated_conjecture,
% 2.10/0.98      ( r2_hidden(sK3,sK1) ),
% 2.10/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_31,plain,
% 2.10/0.98      ( r2_hidden(sK3,sK1) = iProver_top ),
% 2.10/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_3047,plain,
% 2.10/0.98      ( v1_xboole_0(sK2) = iProver_top ),
% 2.10/0.98      inference(global_propositional_subsumption,
% 2.10/0.98                [status(thm)],
% 2.10/0.98                [c_2968,c_31]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_2,plain,
% 2.10/0.98      ( r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0) ),
% 2.10/0.98      inference(cnf_transformation,[],[f44]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_928,plain,
% 2.10/0.98      ( r1_tarski(X0,X1) = iProver_top
% 2.10/0.98      | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
% 2.10/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_0,plain,
% 2.10/0.98      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.10/0.98      inference(cnf_transformation,[],[f42]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_930,plain,
% 2.10/0.98      ( r2_hidden(X0,X1) != iProver_top
% 2.10/0.98      | v1_xboole_0(X1) != iProver_top ),
% 2.10/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_1820,plain,
% 2.10/0.98      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 2.10/0.98      inference(superposition,[status(thm)],[c_928,c_930]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_7,plain,
% 2.10/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 2.10/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_924,plain,
% 2.10/0.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.10/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_4,plain,
% 2.10/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.10/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_926,plain,
% 2.10/0.98      ( X0 = X1
% 2.10/0.98      | r1_tarski(X0,X1) != iProver_top
% 2.10/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 2.10/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_1927,plain,
% 2.10/0.98      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.10/0.98      inference(superposition,[status(thm)],[c_924,c_926]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_2585,plain,
% 2.10/0.98      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.10/0.98      inference(superposition,[status(thm)],[c_1820,c_1927]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_3390,plain,
% 2.10/0.98      ( sK2 = k1_xboole_0 ),
% 2.10/0.98      inference(superposition,[status(thm)],[c_3047,c_2585]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_544,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_1098,plain,
% 2.10/0.98      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 2.10/0.98      inference(instantiation,[status(thm)],[c_544]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_1099,plain,
% 2.10/0.98      ( sK2 != k1_xboole_0
% 2.10/0.98      | k1_xboole_0 = sK2
% 2.10/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 2.10/0.98      inference(instantiation,[status(thm)],[c_1098]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_79,plain,
% 2.10/0.98      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 2.10/0.98      | k1_xboole_0 = k1_xboole_0 ),
% 2.10/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(c_74,plain,
% 2.10/0.98      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 2.10/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 2.10/0.98  
% 2.10/0.98  cnf(contradiction,plain,
% 2.10/0.98      ( $false ),
% 2.10/0.98      inference(minisat,[status(thm)],[c_3390,c_1099,c_79,c_74,c_23]) ).
% 2.10/0.98  
% 2.10/0.98  
% 2.10/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.10/0.98  
% 2.10/0.98  ------                               Statistics
% 2.10/0.98  
% 2.10/0.98  ------ General
% 2.10/0.98  
% 2.10/0.98  abstr_ref_over_cycles:                  0
% 2.10/0.98  abstr_ref_under_cycles:                 0
% 2.10/0.98  gc_basic_clause_elim:                   0
% 2.10/0.98  forced_gc_time:                         0
% 2.10/0.98  parsing_time:                           0.009
% 2.10/0.98  unif_index_cands_time:                  0.
% 2.10/0.98  unif_index_add_time:                    0.
% 2.10/0.98  orderings_time:                         0.
% 2.10/0.98  out_proof_time:                         0.01
% 2.10/0.98  total_time:                             0.126
% 2.10/0.98  num_of_symbols:                         51
% 2.10/0.98  num_of_terms:                           2846
% 2.10/0.98  
% 2.10/0.98  ------ Preprocessing
% 2.10/0.98  
% 2.10/0.98  num_of_splits:                          0
% 2.10/0.98  num_of_split_atoms:                     0
% 2.10/0.98  num_of_reused_defs:                     0
% 2.10/0.98  num_eq_ax_congr_red:                    25
% 2.10/0.98  num_of_sem_filtered_clauses:            1
% 2.10/0.98  num_of_subtypes:                        0
% 2.10/0.98  monotx_restored_types:                  0
% 2.10/0.98  sat_num_of_epr_types:                   0
% 2.10/0.98  sat_num_of_non_cyclic_types:            0
% 2.10/0.98  sat_guarded_non_collapsed_types:        0
% 2.10/0.98  num_pure_diseq_elim:                    0
% 2.10/0.98  simp_replaced_by:                       0
% 2.10/0.98  res_preprocessed:                       118
% 2.10/0.98  prep_upred:                             0
% 2.10/0.98  prep_unflattend:                        28
% 2.10/0.98  smt_new_axioms:                         0
% 2.10/0.98  pred_elim_cands:                        5
% 2.10/0.98  pred_elim:                              2
% 2.10/0.98  pred_elim_cl:                           5
% 2.10/0.98  pred_elim_cycles:                       5
% 2.10/0.98  merged_defs:                            0
% 2.10/0.98  merged_defs_ncl:                        0
% 2.10/0.98  bin_hyper_res:                          0
% 2.10/0.98  prep_cycles:                            4
% 2.10/0.98  pred_elim_time:                         0.003
% 2.10/0.98  splitting_time:                         0.
% 2.10/0.98  sem_filter_time:                        0.
% 2.10/0.98  monotx_time:                            0.
% 2.10/0.98  subtype_inf_time:                       0.
% 2.10/0.98  
% 2.10/0.98  ------ Problem properties
% 2.10/0.98  
% 2.10/0.98  clauses:                                22
% 2.10/0.98  conjectures:                            4
% 2.10/0.98  epr:                                    8
% 2.10/0.98  horn:                                   19
% 2.10/0.98  ground:                                 7
% 2.10/0.98  unary:                                  8
% 2.10/0.98  binary:                                 6
% 2.10/0.98  lits:                                   45
% 2.10/0.98  lits_eq:                                10
% 2.10/0.98  fd_pure:                                0
% 2.10/0.98  fd_pseudo:                              0
% 2.10/0.98  fd_cond:                                0
% 2.10/0.98  fd_pseudo_cond:                         1
% 2.10/0.98  ac_symbols:                             0
% 2.10/0.98  
% 2.10/0.98  ------ Propositional Solver
% 2.10/0.98  
% 2.10/0.98  prop_solver_calls:                      28
% 2.10/0.98  prop_fast_solver_calls:                 667
% 2.10/0.98  smt_solver_calls:                       0
% 2.10/0.98  smt_fast_solver_calls:                  0
% 2.10/0.98  prop_num_of_clauses:                    1174
% 2.10/0.98  prop_preprocess_simplified:             4345
% 2.10/0.98  prop_fo_subsumed:                       12
% 2.10/0.98  prop_solver_time:                       0.
% 2.10/0.98  smt_solver_time:                        0.
% 2.10/0.98  smt_fast_solver_time:                   0.
% 2.10/0.98  prop_fast_solver_time:                  0.
% 2.10/0.98  prop_unsat_core_time:                   0.
% 2.10/0.98  
% 2.10/0.98  ------ QBF
% 2.10/0.98  
% 2.10/0.98  qbf_q_res:                              0
% 2.10/0.98  qbf_num_tautologies:                    0
% 2.10/0.98  qbf_prep_cycles:                        0
% 2.10/0.98  
% 2.10/0.98  ------ BMC1
% 2.10/0.98  
% 2.10/0.98  bmc1_current_bound:                     -1
% 2.10/0.98  bmc1_last_solved_bound:                 -1
% 2.10/0.98  bmc1_unsat_core_size:                   -1
% 2.10/0.98  bmc1_unsat_core_parents_size:           -1
% 2.10/0.98  bmc1_merge_next_fun:                    0
% 2.10/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.10/0.98  
% 2.10/0.98  ------ Instantiation
% 2.10/0.98  
% 2.10/0.98  inst_num_of_clauses:                    393
% 2.10/0.98  inst_num_in_passive:                    108
% 2.10/0.98  inst_num_in_active:                     182
% 2.10/0.98  inst_num_in_unprocessed:                103
% 2.10/0.98  inst_num_of_loops:                      250
% 2.10/0.98  inst_num_of_learning_restarts:          0
% 2.10/0.98  inst_num_moves_active_passive:          65
% 2.10/0.98  inst_lit_activity:                      0
% 2.10/0.98  inst_lit_activity_moves:                0
% 2.10/0.98  inst_num_tautologies:                   0
% 2.10/0.98  inst_num_prop_implied:                  0
% 2.10/0.98  inst_num_existing_simplified:           0
% 2.10/0.98  inst_num_eq_res_simplified:             0
% 2.10/0.98  inst_num_child_elim:                    0
% 2.10/0.98  inst_num_of_dismatching_blockings:      103
% 2.10/0.98  inst_num_of_non_proper_insts:           349
% 2.10/0.98  inst_num_of_duplicates:                 0
% 2.10/0.98  inst_inst_num_from_inst_to_res:         0
% 2.10/0.98  inst_dismatching_checking_time:         0.
% 2.10/0.98  
% 2.10/0.98  ------ Resolution
% 2.10/0.98  
% 2.10/0.98  res_num_of_clauses:                     0
% 2.10/0.98  res_num_in_passive:                     0
% 2.10/0.98  res_num_in_active:                      0
% 2.10/0.98  res_num_of_loops:                       122
% 2.10/0.98  res_forward_subset_subsumed:            51
% 2.10/0.98  res_backward_subset_subsumed:           8
% 2.10/0.98  res_forward_subsumed:                   0
% 2.10/0.98  res_backward_subsumed:                  0
% 2.10/0.98  res_forward_subsumption_resolution:     0
% 2.10/0.98  res_backward_subsumption_resolution:    0
% 2.10/0.98  res_clause_to_clause_subsumption:       133
% 2.10/0.98  res_orphan_elimination:                 0
% 2.10/0.98  res_tautology_del:                      52
% 2.10/0.98  res_num_eq_res_simplified:              0
% 2.10/0.98  res_num_sel_changes:                    0
% 2.10/0.98  res_moves_from_active_to_pass:          0
% 2.10/0.98  
% 2.10/0.98  ------ Superposition
% 2.10/0.98  
% 2.10/0.98  sup_time_total:                         0.
% 2.10/0.98  sup_time_generating:                    0.
% 2.10/0.98  sup_time_sim_full:                      0.
% 2.10/0.98  sup_time_sim_immed:                     0.
% 2.10/0.98  
% 2.10/0.98  sup_num_of_clauses:                     59
% 2.10/0.98  sup_num_in_active:                      48
% 2.10/0.98  sup_num_in_passive:                     11
% 2.10/0.98  sup_num_of_loops:                       49
% 2.10/0.98  sup_fw_superposition:                   30
% 2.10/0.98  sup_bw_superposition:                   22
% 2.10/0.98  sup_immediate_simplified:               4
% 2.10/0.98  sup_given_eliminated:                   0
% 2.10/0.98  comparisons_done:                       0
% 2.10/0.98  comparisons_avoided:                    0
% 2.10/0.98  
% 2.10/0.98  ------ Simplifications
% 2.10/0.98  
% 2.10/0.98  
% 2.10/0.98  sim_fw_subset_subsumed:                 2
% 2.10/0.98  sim_bw_subset_subsumed:                 0
% 2.10/0.98  sim_fw_subsumed:                        1
% 2.10/0.98  sim_bw_subsumed:                        0
% 2.10/0.98  sim_fw_subsumption_res:                 0
% 2.10/0.98  sim_bw_subsumption_res:                 0
% 2.10/0.98  sim_tautology_del:                      7
% 2.10/0.98  sim_eq_tautology_del:                   3
% 2.10/0.98  sim_eq_res_simp:                        0
% 2.10/0.98  sim_fw_demodulated:                     0
% 2.10/0.98  sim_bw_demodulated:                     2
% 2.10/0.98  sim_light_normalised:                   1
% 2.10/0.98  sim_joinable_taut:                      0
% 2.10/0.98  sim_joinable_simp:                      0
% 2.10/0.98  sim_ac_normalised:                      0
% 2.10/0.98  sim_smt_subsumption:                    0
% 2.10/0.98  
%------------------------------------------------------------------------------
