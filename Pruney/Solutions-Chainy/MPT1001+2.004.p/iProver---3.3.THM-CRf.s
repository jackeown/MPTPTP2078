%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:20 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :  134 (1646 expanded)
%              Number of clauses        :   76 ( 505 expanded)
%              Number of leaves         :   16 ( 312 expanded)
%              Depth                    :   30
%              Number of atoms          :  371 (6670 expanded)
%              Number of equality atoms :  184 (3240 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ! [X2] :
            ~ ( k10_relat_1(X1,k1_tarski(X2)) = k1_xboole_0
              & r2_hidden(X2,X0) )
       => r1_tarski(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_relat_1(X1))
      | ? [X2] :
          ( k10_relat_1(X1,k1_tarski(X2)) = k1_xboole_0
          & r2_hidden(X2,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_relat_1(X1))
      | ? [X2] :
          ( k10_relat_1(X1,k1_tarski(X2)) = k1_xboole_0
          & r2_hidden(X2,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k10_relat_1(X1,k1_tarski(X2)) = k1_xboole_0
          & r2_hidden(X2,X0) )
     => ( k10_relat_1(X1,k1_tarski(sK0(X0,X1))) = k1_xboole_0
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_relat_1(X1))
      | ( k10_relat_1(X1,k1_tarski(sK0(X0,X1))) = k1_xboole_0
        & r2_hidden(sK0(X0,X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f33])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_relat_1(X1))
      | k10_relat_1(X1,k1_tarski(sK0(X0,X1))) = k1_xboole_0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3))
              & r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3))
                & r2_hidden(X3,X1) )
        <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f15,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3))
                & r2_hidden(X3,X1) )
        <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f16,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( ! [X3] :
              ~ ( k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3))
                & r2_hidden(X3,X1) )
        <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X3))
            | ~ r2_hidden(X3,X1) )
      <~> k2_relset_1(X0,X1,X2) = X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ? [X3] :
            ( k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3))
            & r2_hidden(X3,X1) ) )
      & ( k2_relset_1(X0,X1,X2) = X1
        | ! [X3] :
            ( k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X3))
            | ~ r2_hidden(X3,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f36,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ? [X3] :
            ( k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3))
            & r2_hidden(X3,X1) ) )
      & ( k2_relset_1(X0,X1,X2) = X1
        | ! [X3] :
            ( k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X3))
            | ~ r2_hidden(X3,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f37,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ? [X3] :
            ( k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3))
            & r2_hidden(X3,X1) ) )
      & ( k2_relset_1(X0,X1,X2) = X1
        | ! [X4] :
            ( k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X4))
            | ~ r2_hidden(X4,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(rectify,[],[f36])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3))
          & r2_hidden(X3,X1) )
     => ( k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(sK4))
        & r2_hidden(sK4,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_relset_1(X0,X1,X2) != X1
          | ? [X3] :
              ( k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3))
              & r2_hidden(X3,X1) ) )
        & ( k2_relset_1(X0,X1,X2) = X1
          | ! [X4] :
              ( k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X4))
              | ~ r2_hidden(X4,X1) ) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( k2_relset_1(sK1,sK2,sK3) != sK2
        | ? [X3] :
            ( k1_xboole_0 = k8_relset_1(sK1,sK2,sK3,k1_tarski(X3))
            & r2_hidden(X3,sK2) ) )
      & ( k2_relset_1(sK1,sK2,sK3) = sK2
        | ! [X4] :
            ( k1_xboole_0 != k8_relset_1(sK1,sK2,sK3,k1_tarski(X4))
            | ~ r2_hidden(X4,sK2) ) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ( k2_relset_1(sK1,sK2,sK3) != sK2
      | ( k1_xboole_0 = k8_relset_1(sK1,sK2,sK3,k1_tarski(sK4))
        & r2_hidden(sK4,sK2) ) )
    & ( k2_relset_1(sK1,sK2,sK3) = sK2
      | ! [X4] :
          ( k1_xboole_0 != k8_relset_1(sK1,sK2,sK3,k1_tarski(X4))
          | ~ r2_hidden(X4,sK2) ) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f37,f39,f38])).

fof(f59,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f60,plain,(
    ! [X4] :
      ( k2_relset_1(sK1,sK2,sK3) = sK2
      | k1_xboole_0 != k8_relset_1(sK1,sK2,sK3,k1_tarski(X4))
      | ~ r2_hidden(X4,sK2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_relat_1(X1))
      | r2_hidden(sK0(X0,X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f62,plain,
    ( k2_relset_1(sK1,sK2,sK3) != sK2
    | k1_xboole_0 = k8_relset_1(sK1,sK2,sK3,k1_tarski(sK4)) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k10_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k10_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( k10_relat_1(X1,X0) = k1_xboole_0
          | ~ r1_xboole_0(k2_relat_1(X1),X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k10_relat_1(X1,X0) != k1_xboole_0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_relat_1(X1),X0)
      | k10_relat_1(X1,X0) != k1_xboole_0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f61,plain,
    ( k2_relset_1(sK1,sK2,sK3) != sK2
    | r2_hidden(sK4,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f18])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f4])).

cnf(c_12,plain,
    ( r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k1_tarski(sK0(X0,X1))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1255,plain,
    ( k10_relat_1(X0,k1_tarski(sK0(X1,X0))) = k1_xboole_0
    | r1_tarski(X1,k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1250,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1252,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1671,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1250,c_1252])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1253,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2306,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1671,c_1253])).

cnf(c_22,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2716,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2306,c_22])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1258,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2721,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2716,c_1258])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1261,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2823,plain,
    ( k2_relat_1(sK3) = sK2
    | r1_tarski(sK2,k2_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2721,c_1261])).

cnf(c_3012,plain,
    ( k10_relat_1(sK3,k1_tarski(sK0(sK2,sK3))) = k1_xboole_0
    | k2_relat_1(sK3) = sK2
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1255,c_2823])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1400,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_3039,plain,
    ( ~ v1_relat_1(sK3)
    | k10_relat_1(sK3,k1_tarski(sK0(sK2,sK3))) = k1_xboole_0
    | k2_relat_1(sK3) = sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3012])).

cnf(c_3315,plain,
    ( k2_relat_1(sK3) = sK2
    | k10_relat_1(sK3,k1_tarski(sK0(sK2,sK3))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3012,c_21,c_1400,c_3039])).

cnf(c_3316,plain,
    ( k10_relat_1(sK3,k1_tarski(sK0(sK2,sK3))) = k1_xboole_0
    | k2_relat_1(sK3) = sK2 ),
    inference(renaming,[status(thm)],[c_3315])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1251,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2292,plain,
    ( k8_relset_1(sK1,sK2,sK3,X0) = k10_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1250,c_1251])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_170,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k1_tarski(X0),X1) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_20,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | k2_relset_1(sK1,sK2,sK3) = sK2
    | k1_xboole_0 != k8_relset_1(sK1,sK2,sK3,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_403,plain,
    ( ~ r1_tarski(k1_tarski(X0),X1)
    | X2 != X0
    | k8_relset_1(sK1,sK2,sK3,k1_tarski(X2)) != k1_xboole_0
    | k2_relset_1(sK1,sK2,sK3) = sK2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_170,c_20])).

cnf(c_404,plain,
    ( ~ r1_tarski(k1_tarski(X0),sK2)
    | k8_relset_1(sK1,sK2,sK3,k1_tarski(X0)) != k1_xboole_0
    | k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(unflattening,[status(thm)],[c_403])).

cnf(c_1246,plain,
    ( k8_relset_1(sK1,sK2,sK3,k1_tarski(X0)) != k1_xboole_0
    | k2_relset_1(sK1,sK2,sK3) = sK2
    | r1_tarski(k1_tarski(X0),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_404])).

cnf(c_1846,plain,
    ( k8_relset_1(sK1,sK2,sK3,k1_tarski(X0)) != k1_xboole_0
    | k2_relat_1(sK3) = sK2
    | r1_tarski(k1_tarski(X0),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1671,c_1246])).

cnf(c_2606,plain,
    ( k10_relat_1(sK3,k1_tarski(X0)) != k1_xboole_0
    | k2_relat_1(sK3) = sK2
    | r1_tarski(k1_tarski(X0),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2292,c_1846])).

cnf(c_3320,plain,
    ( k2_relat_1(sK3) = sK2
    | r1_tarski(k1_tarski(sK0(sK2,sK3)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3316,c_2606])).

cnf(c_2824,plain,
    ( ~ r1_tarski(sK2,k2_relat_1(sK3))
    | k2_relat_1(sK3) = sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2823])).

cnf(c_13,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_418,plain,
    ( r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k8_relset_1(sK1,sK2,sK3,k1_tarski(X2)) != k1_xboole_0
    | k2_relset_1(sK1,sK2,sK3) = sK2
    | sK0(X0,X1) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_419,plain,
    ( r1_tarski(sK2,k2_relat_1(X0))
    | ~ v1_relat_1(X0)
    | k8_relset_1(sK1,sK2,sK3,k1_tarski(sK0(sK2,X0))) != k1_xboole_0
    | k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(unflattening,[status(thm)],[c_418])).

cnf(c_1245,plain,
    ( k8_relset_1(sK1,sK2,sK3,k1_tarski(sK0(sK2,X0))) != k1_xboole_0
    | k2_relset_1(sK1,sK2,sK3) = sK2
    | r1_tarski(sK2,k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_419])).

cnf(c_1845,plain,
    ( k8_relset_1(sK1,sK2,sK3,k1_tarski(sK0(sK2,X0))) != k1_xboole_0
    | k2_relat_1(sK3) = sK2
    | r1_tarski(sK2,k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1671,c_1245])).

cnf(c_2607,plain,
    ( k10_relat_1(sK3,k1_tarski(sK0(sK2,X0))) != k1_xboole_0
    | k2_relat_1(sK3) = sK2
    | r1_tarski(sK2,k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2292,c_1845])).

cnf(c_3321,plain,
    ( k2_relat_1(sK3) = sK2
    | r1_tarski(sK2,k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3316,c_2607])).

cnf(c_3340,plain,
    ( r1_tarski(sK2,k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) = sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3321])).

cnf(c_3342,plain,
    ( k2_relat_1(sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3320,c_21,c_1400,c_2824,c_3340])).

cnf(c_18,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) != sK2
    | k1_xboole_0 = k8_relset_1(sK1,sK2,sK3,k1_tarski(sK4)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1848,plain,
    ( k8_relset_1(sK1,sK2,sK3,k1_tarski(sK4)) = k1_xboole_0
    | k2_relat_1(sK3) != sK2 ),
    inference(demodulation,[status(thm)],[c_1671,c_18])).

cnf(c_2605,plain,
    ( k10_relat_1(sK3,k1_tarski(sK4)) = k1_xboole_0
    | k2_relat_1(sK3) != sK2 ),
    inference(demodulation,[status(thm)],[c_2292,c_1848])).

cnf(c_3349,plain,
    ( k10_relat_1(sK3,k1_tarski(sK4)) = k1_xboole_0
    | sK2 != sK2 ),
    inference(demodulation,[status(thm)],[c_3342,c_2605])).

cnf(c_3357,plain,
    ( k10_relat_1(sK3,k1_tarski(sK4)) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_3349])).

cnf(c_11,plain,
    ( r1_xboole_0(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1256,plain,
    ( k10_relat_1(X0,X1) != k1_xboole_0
    | r1_xboole_0(k2_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3587,plain,
    ( r1_xboole_0(k2_relat_1(sK3),k1_tarski(sK4)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3357,c_1256])).

cnf(c_3588,plain,
    ( r1_xboole_0(sK2,k1_tarski(sK4)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3587,c_3342])).

cnf(c_1401,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1400])).

cnf(c_3692,plain,
    ( r1_xboole_0(sK2,k1_tarski(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3588,c_22,c_1401])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1262,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3697,plain,
    ( r1_xboole_0(k1_tarski(sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3692,c_1262])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_172,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_tarski(X0),X1) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_19,negated_conjecture,
    ( r2_hidden(sK4,sK2)
    | k2_relset_1(sK1,sK2,sK3) != sK2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_393,plain,
    ( r1_tarski(k1_tarski(X0),X1)
    | k2_relset_1(sK1,sK2,sK3) != sK2
    | sK4 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_172,c_19])).

cnf(c_394,plain,
    ( r1_tarski(k1_tarski(sK4),sK2)
    | k2_relset_1(sK1,sK2,sK3) != sK2 ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_1247,plain,
    ( k2_relset_1(sK1,sK2,sK3) != sK2
    | r1_tarski(k1_tarski(sK4),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_394])).

cnf(c_1847,plain,
    ( k2_relat_1(sK3) != sK2
    | r1_tarski(k1_tarski(sK4),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1671,c_1247])).

cnf(c_3350,plain,
    ( sK2 != sK2
    | r1_tarski(k1_tarski(sK4),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3342,c_1847])).

cnf(c_3354,plain,
    ( r1_tarski(k1_tarski(sK4),sK2) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3350])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_292,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X0,X1)
    | k1_tarski(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_5])).

cnf(c_293,plain,
    ( ~ r1_tarski(k1_tarski(X0),X1)
    | ~ r1_xboole_0(k1_tarski(X0),X1) ),
    inference(unflattening,[status(thm)],[c_292])).

cnf(c_1249,plain,
    ( r1_tarski(k1_tarski(X0),X1) != iProver_top
    | r1_xboole_0(k1_tarski(X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_293])).

cnf(c_3593,plain,
    ( r1_xboole_0(k1_tarski(sK4),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3354,c_1249])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3697,c_3593])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:06:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.56/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/0.99  
% 2.56/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.56/0.99  
% 2.56/0.99  ------  iProver source info
% 2.56/0.99  
% 2.56/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.56/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.56/0.99  git: non_committed_changes: false
% 2.56/0.99  git: last_make_outside_of_git: false
% 2.56/0.99  
% 2.56/0.99  ------ 
% 2.56/0.99  
% 2.56/0.99  ------ Input Options
% 2.56/0.99  
% 2.56/0.99  --out_options                           all
% 2.56/0.99  --tptp_safe_out                         true
% 2.56/0.99  --problem_path                          ""
% 2.56/0.99  --include_path                          ""
% 2.56/0.99  --clausifier                            res/vclausify_rel
% 2.56/0.99  --clausifier_options                    --mode clausify
% 2.56/0.99  --stdin                                 false
% 2.56/0.99  --stats_out                             all
% 2.56/0.99  
% 2.56/0.99  ------ General Options
% 2.56/0.99  
% 2.56/0.99  --fof                                   false
% 2.56/0.99  --time_out_real                         305.
% 2.56/0.99  --time_out_virtual                      -1.
% 2.56/0.99  --symbol_type_check                     false
% 2.56/0.99  --clausify_out                          false
% 2.56/0.99  --sig_cnt_out                           false
% 2.56/0.99  --trig_cnt_out                          false
% 2.56/0.99  --trig_cnt_out_tolerance                1.
% 2.56/0.99  --trig_cnt_out_sk_spl                   false
% 2.56/0.99  --abstr_cl_out                          false
% 2.56/0.99  
% 2.56/0.99  ------ Global Options
% 2.56/0.99  
% 2.56/0.99  --schedule                              default
% 2.56/0.99  --add_important_lit                     false
% 2.56/0.99  --prop_solver_per_cl                    1000
% 2.56/0.99  --min_unsat_core                        false
% 2.56/0.99  --soft_assumptions                      false
% 2.56/0.99  --soft_lemma_size                       3
% 2.56/0.99  --prop_impl_unit_size                   0
% 2.56/0.99  --prop_impl_unit                        []
% 2.56/0.99  --share_sel_clauses                     true
% 2.56/0.99  --reset_solvers                         false
% 2.56/0.99  --bc_imp_inh                            [conj_cone]
% 2.56/0.99  --conj_cone_tolerance                   3.
% 2.56/0.99  --extra_neg_conj                        none
% 2.56/0.99  --large_theory_mode                     true
% 2.56/0.99  --prolific_symb_bound                   200
% 2.56/0.99  --lt_threshold                          2000
% 2.56/0.99  --clause_weak_htbl                      true
% 2.56/0.99  --gc_record_bc_elim                     false
% 2.56/0.99  
% 2.56/0.99  ------ Preprocessing Options
% 2.56/0.99  
% 2.56/0.99  --preprocessing_flag                    true
% 2.56/0.99  --time_out_prep_mult                    0.1
% 2.56/0.99  --splitting_mode                        input
% 2.56/0.99  --splitting_grd                         true
% 2.56/0.99  --splitting_cvd                         false
% 2.56/0.99  --splitting_cvd_svl                     false
% 2.56/0.99  --splitting_nvd                         32
% 2.56/0.99  --sub_typing                            true
% 2.56/0.99  --prep_gs_sim                           true
% 2.56/0.99  --prep_unflatten                        true
% 2.56/0.99  --prep_res_sim                          true
% 2.56/0.99  --prep_upred                            true
% 2.56/0.99  --prep_sem_filter                       exhaustive
% 2.56/0.99  --prep_sem_filter_out                   false
% 2.56/0.99  --pred_elim                             true
% 2.56/0.99  --res_sim_input                         true
% 2.56/0.99  --eq_ax_congr_red                       true
% 2.56/0.99  --pure_diseq_elim                       true
% 2.56/0.99  --brand_transform                       false
% 2.56/0.99  --non_eq_to_eq                          false
% 2.56/0.99  --prep_def_merge                        true
% 2.56/0.99  --prep_def_merge_prop_impl              false
% 2.56/0.99  --prep_def_merge_mbd                    true
% 2.56/0.99  --prep_def_merge_tr_red                 false
% 2.56/0.99  --prep_def_merge_tr_cl                  false
% 2.56/0.99  --smt_preprocessing                     true
% 2.56/0.99  --smt_ac_axioms                         fast
% 2.56/0.99  --preprocessed_out                      false
% 2.56/0.99  --preprocessed_stats                    false
% 2.56/0.99  
% 2.56/0.99  ------ Abstraction refinement Options
% 2.56/0.99  
% 2.56/0.99  --abstr_ref                             []
% 2.56/0.99  --abstr_ref_prep                        false
% 2.56/0.99  --abstr_ref_until_sat                   false
% 2.56/0.99  --abstr_ref_sig_restrict                funpre
% 2.56/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.56/0.99  --abstr_ref_under                       []
% 2.56/0.99  
% 2.56/0.99  ------ SAT Options
% 2.56/0.99  
% 2.56/0.99  --sat_mode                              false
% 2.56/0.99  --sat_fm_restart_options                ""
% 2.56/0.99  --sat_gr_def                            false
% 2.56/0.99  --sat_epr_types                         true
% 2.56/0.99  --sat_non_cyclic_types                  false
% 2.56/0.99  --sat_finite_models                     false
% 2.56/0.99  --sat_fm_lemmas                         false
% 2.56/0.99  --sat_fm_prep                           false
% 2.56/0.99  --sat_fm_uc_incr                        true
% 2.56/0.99  --sat_out_model                         small
% 2.56/0.99  --sat_out_clauses                       false
% 2.56/0.99  
% 2.56/0.99  ------ QBF Options
% 2.56/0.99  
% 2.56/0.99  --qbf_mode                              false
% 2.56/0.99  --qbf_elim_univ                         false
% 2.56/0.99  --qbf_dom_inst                          none
% 2.56/0.99  --qbf_dom_pre_inst                      false
% 2.56/0.99  --qbf_sk_in                             false
% 2.56/0.99  --qbf_pred_elim                         true
% 2.56/0.99  --qbf_split                             512
% 2.56/0.99  
% 2.56/0.99  ------ BMC1 Options
% 2.56/0.99  
% 2.56/0.99  --bmc1_incremental                      false
% 2.56/0.99  --bmc1_axioms                           reachable_all
% 2.56/0.99  --bmc1_min_bound                        0
% 2.56/0.99  --bmc1_max_bound                        -1
% 2.56/0.99  --bmc1_max_bound_default                -1
% 2.56/0.99  --bmc1_symbol_reachability              true
% 2.56/0.99  --bmc1_property_lemmas                  false
% 2.56/0.99  --bmc1_k_induction                      false
% 2.56/0.99  --bmc1_non_equiv_states                 false
% 2.56/0.99  --bmc1_deadlock                         false
% 2.56/0.99  --bmc1_ucm                              false
% 2.56/0.99  --bmc1_add_unsat_core                   none
% 2.56/0.99  --bmc1_unsat_core_children              false
% 2.56/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.56/0.99  --bmc1_out_stat                         full
% 2.56/0.99  --bmc1_ground_init                      false
% 2.56/0.99  --bmc1_pre_inst_next_state              false
% 2.56/0.99  --bmc1_pre_inst_state                   false
% 2.56/0.99  --bmc1_pre_inst_reach_state             false
% 2.56/0.99  --bmc1_out_unsat_core                   false
% 2.56/0.99  --bmc1_aig_witness_out                  false
% 2.56/0.99  --bmc1_verbose                          false
% 2.56/0.99  --bmc1_dump_clauses_tptp                false
% 2.56/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.56/0.99  --bmc1_dump_file                        -
% 2.56/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.56/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.56/0.99  --bmc1_ucm_extend_mode                  1
% 2.56/0.99  --bmc1_ucm_init_mode                    2
% 2.56/0.99  --bmc1_ucm_cone_mode                    none
% 2.56/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.56/0.99  --bmc1_ucm_relax_model                  4
% 2.56/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.56/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.56/0.99  --bmc1_ucm_layered_model                none
% 2.56/0.99  --bmc1_ucm_max_lemma_size               10
% 2.56/0.99  
% 2.56/0.99  ------ AIG Options
% 2.56/0.99  
% 2.56/0.99  --aig_mode                              false
% 2.56/0.99  
% 2.56/0.99  ------ Instantiation Options
% 2.56/0.99  
% 2.56/0.99  --instantiation_flag                    true
% 2.56/0.99  --inst_sos_flag                         false
% 2.56/0.99  --inst_sos_phase                        true
% 2.56/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.56/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.56/0.99  --inst_lit_sel_side                     num_symb
% 2.56/0.99  --inst_solver_per_active                1400
% 2.56/0.99  --inst_solver_calls_frac                1.
% 2.56/0.99  --inst_passive_queue_type               priority_queues
% 2.56/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.56/0.99  --inst_passive_queues_freq              [25;2]
% 2.56/0.99  --inst_dismatching                      true
% 2.56/0.99  --inst_eager_unprocessed_to_passive     true
% 2.56/0.99  --inst_prop_sim_given                   true
% 2.56/0.99  --inst_prop_sim_new                     false
% 2.56/0.99  --inst_subs_new                         false
% 2.56/0.99  --inst_eq_res_simp                      false
% 2.56/0.99  --inst_subs_given                       false
% 2.56/0.99  --inst_orphan_elimination               true
% 2.56/0.99  --inst_learning_loop_flag               true
% 2.56/0.99  --inst_learning_start                   3000
% 2.56/0.99  --inst_learning_factor                  2
% 2.56/0.99  --inst_start_prop_sim_after_learn       3
% 2.56/0.99  --inst_sel_renew                        solver
% 2.56/0.99  --inst_lit_activity_flag                true
% 2.56/0.99  --inst_restr_to_given                   false
% 2.56/0.99  --inst_activity_threshold               500
% 2.56/0.99  --inst_out_proof                        true
% 2.56/0.99  
% 2.56/0.99  ------ Resolution Options
% 2.56/0.99  
% 2.56/0.99  --resolution_flag                       true
% 2.56/0.99  --res_lit_sel                           adaptive
% 2.56/0.99  --res_lit_sel_side                      none
% 2.56/0.99  --res_ordering                          kbo
% 2.56/0.99  --res_to_prop_solver                    active
% 2.56/0.99  --res_prop_simpl_new                    false
% 2.56/0.99  --res_prop_simpl_given                  true
% 2.56/0.99  --res_passive_queue_type                priority_queues
% 2.56/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.56/0.99  --res_passive_queues_freq               [15;5]
% 2.56/0.99  --res_forward_subs                      full
% 2.56/0.99  --res_backward_subs                     full
% 2.56/0.99  --res_forward_subs_resolution           true
% 2.56/0.99  --res_backward_subs_resolution          true
% 2.56/0.99  --res_orphan_elimination                true
% 2.56/0.99  --res_time_limit                        2.
% 2.56/0.99  --res_out_proof                         true
% 2.56/0.99  
% 2.56/0.99  ------ Superposition Options
% 2.56/0.99  
% 2.56/0.99  --superposition_flag                    true
% 2.56/0.99  --sup_passive_queue_type                priority_queues
% 2.56/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.56/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.56/0.99  --demod_completeness_check              fast
% 2.56/0.99  --demod_use_ground                      true
% 2.56/0.99  --sup_to_prop_solver                    passive
% 2.56/0.99  --sup_prop_simpl_new                    true
% 2.56/0.99  --sup_prop_simpl_given                  true
% 2.56/0.99  --sup_fun_splitting                     false
% 2.56/0.99  --sup_smt_interval                      50000
% 2.56/0.99  
% 2.56/0.99  ------ Superposition Simplification Setup
% 2.56/0.99  
% 2.56/0.99  --sup_indices_passive                   []
% 2.56/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.56/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/0.99  --sup_full_bw                           [BwDemod]
% 2.56/0.99  --sup_immed_triv                        [TrivRules]
% 2.56/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.56/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/0.99  --sup_immed_bw_main                     []
% 2.56/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.56/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.56/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.56/0.99  
% 2.56/0.99  ------ Combination Options
% 2.56/0.99  
% 2.56/0.99  --comb_res_mult                         3
% 2.56/0.99  --comb_sup_mult                         2
% 2.56/0.99  --comb_inst_mult                        10
% 2.56/0.99  
% 2.56/0.99  ------ Debug Options
% 2.56/0.99  
% 2.56/0.99  --dbg_backtrace                         false
% 2.56/0.99  --dbg_dump_prop_clauses                 false
% 2.56/0.99  --dbg_dump_prop_clauses_file            -
% 2.56/0.99  --dbg_out_stat                          false
% 2.56/0.99  ------ Parsing...
% 2.56/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.56/0.99  
% 2.56/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.56/0.99  
% 2.56/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.56/0.99  
% 2.56/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.56/0.99  ------ Proving...
% 2.56/0.99  ------ Problem Properties 
% 2.56/0.99  
% 2.56/0.99  
% 2.56/0.99  clauses                                 19
% 2.56/0.99  conjectures                             2
% 2.56/0.99  EPR                                     3
% 2.56/0.99  Horn                                    16
% 2.56/0.99  unary                                   2
% 2.56/0.99  binary                                  10
% 2.56/0.99  lits                                    44
% 2.56/0.99  lits eq                                 13
% 2.56/0.99  fd_pure                                 0
% 2.56/0.99  fd_pseudo                               0
% 2.56/0.99  fd_cond                                 0
% 2.56/0.99  fd_pseudo_cond                          1
% 2.56/0.99  AC symbols                              0
% 2.56/0.99  
% 2.56/0.99  ------ Schedule dynamic 5 is on 
% 2.56/0.99  
% 2.56/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.56/0.99  
% 2.56/0.99  
% 2.56/0.99  ------ 
% 2.56/0.99  Current options:
% 2.56/0.99  ------ 
% 2.56/0.99  
% 2.56/0.99  ------ Input Options
% 2.56/0.99  
% 2.56/0.99  --out_options                           all
% 2.56/0.99  --tptp_safe_out                         true
% 2.56/0.99  --problem_path                          ""
% 2.56/0.99  --include_path                          ""
% 2.56/0.99  --clausifier                            res/vclausify_rel
% 2.56/0.99  --clausifier_options                    --mode clausify
% 2.56/0.99  --stdin                                 false
% 2.56/0.99  --stats_out                             all
% 2.56/0.99  
% 2.56/0.99  ------ General Options
% 2.56/0.99  
% 2.56/0.99  --fof                                   false
% 2.56/0.99  --time_out_real                         305.
% 2.56/0.99  --time_out_virtual                      -1.
% 2.56/0.99  --symbol_type_check                     false
% 2.56/0.99  --clausify_out                          false
% 2.56/0.99  --sig_cnt_out                           false
% 2.56/0.99  --trig_cnt_out                          false
% 2.56/0.99  --trig_cnt_out_tolerance                1.
% 2.56/0.99  --trig_cnt_out_sk_spl                   false
% 2.56/0.99  --abstr_cl_out                          false
% 2.56/0.99  
% 2.56/0.99  ------ Global Options
% 2.56/0.99  
% 2.56/0.99  --schedule                              default
% 2.56/0.99  --add_important_lit                     false
% 2.56/0.99  --prop_solver_per_cl                    1000
% 2.56/0.99  --min_unsat_core                        false
% 2.56/0.99  --soft_assumptions                      false
% 2.56/0.99  --soft_lemma_size                       3
% 2.56/0.99  --prop_impl_unit_size                   0
% 2.56/0.99  --prop_impl_unit                        []
% 2.56/0.99  --share_sel_clauses                     true
% 2.56/0.99  --reset_solvers                         false
% 2.56/0.99  --bc_imp_inh                            [conj_cone]
% 2.56/0.99  --conj_cone_tolerance                   3.
% 2.56/0.99  --extra_neg_conj                        none
% 2.56/0.99  --large_theory_mode                     true
% 2.56/0.99  --prolific_symb_bound                   200
% 2.56/0.99  --lt_threshold                          2000
% 2.56/0.99  --clause_weak_htbl                      true
% 2.56/0.99  --gc_record_bc_elim                     false
% 2.56/0.99  
% 2.56/0.99  ------ Preprocessing Options
% 2.56/0.99  
% 2.56/0.99  --preprocessing_flag                    true
% 2.56/0.99  --time_out_prep_mult                    0.1
% 2.56/0.99  --splitting_mode                        input
% 2.56/0.99  --splitting_grd                         true
% 2.56/0.99  --splitting_cvd                         false
% 2.56/0.99  --splitting_cvd_svl                     false
% 2.56/0.99  --splitting_nvd                         32
% 2.56/0.99  --sub_typing                            true
% 2.56/0.99  --prep_gs_sim                           true
% 2.56/0.99  --prep_unflatten                        true
% 2.56/0.99  --prep_res_sim                          true
% 2.56/0.99  --prep_upred                            true
% 2.56/0.99  --prep_sem_filter                       exhaustive
% 2.56/0.99  --prep_sem_filter_out                   false
% 2.56/0.99  --pred_elim                             true
% 2.56/0.99  --res_sim_input                         true
% 2.56/0.99  --eq_ax_congr_red                       true
% 2.56/0.99  --pure_diseq_elim                       true
% 2.56/0.99  --brand_transform                       false
% 2.56/0.99  --non_eq_to_eq                          false
% 2.56/0.99  --prep_def_merge                        true
% 2.56/0.99  --prep_def_merge_prop_impl              false
% 2.56/0.99  --prep_def_merge_mbd                    true
% 2.56/0.99  --prep_def_merge_tr_red                 false
% 2.56/0.99  --prep_def_merge_tr_cl                  false
% 2.56/0.99  --smt_preprocessing                     true
% 2.56/0.99  --smt_ac_axioms                         fast
% 2.56/0.99  --preprocessed_out                      false
% 2.56/0.99  --preprocessed_stats                    false
% 2.56/0.99  
% 2.56/0.99  ------ Abstraction refinement Options
% 2.56/0.99  
% 2.56/0.99  --abstr_ref                             []
% 2.56/0.99  --abstr_ref_prep                        false
% 2.56/0.99  --abstr_ref_until_sat                   false
% 2.56/0.99  --abstr_ref_sig_restrict                funpre
% 2.56/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.56/0.99  --abstr_ref_under                       []
% 2.56/0.99  
% 2.56/0.99  ------ SAT Options
% 2.56/0.99  
% 2.56/0.99  --sat_mode                              false
% 2.56/0.99  --sat_fm_restart_options                ""
% 2.56/0.99  --sat_gr_def                            false
% 2.56/0.99  --sat_epr_types                         true
% 2.56/0.99  --sat_non_cyclic_types                  false
% 2.56/0.99  --sat_finite_models                     false
% 2.56/0.99  --sat_fm_lemmas                         false
% 2.56/0.99  --sat_fm_prep                           false
% 2.56/0.99  --sat_fm_uc_incr                        true
% 2.56/0.99  --sat_out_model                         small
% 2.56/0.99  --sat_out_clauses                       false
% 2.56/0.99  
% 2.56/0.99  ------ QBF Options
% 2.56/0.99  
% 2.56/0.99  --qbf_mode                              false
% 2.56/0.99  --qbf_elim_univ                         false
% 2.56/0.99  --qbf_dom_inst                          none
% 2.56/0.99  --qbf_dom_pre_inst                      false
% 2.56/0.99  --qbf_sk_in                             false
% 2.56/0.99  --qbf_pred_elim                         true
% 2.56/0.99  --qbf_split                             512
% 2.56/0.99  
% 2.56/0.99  ------ BMC1 Options
% 2.56/0.99  
% 2.56/0.99  --bmc1_incremental                      false
% 2.56/0.99  --bmc1_axioms                           reachable_all
% 2.56/0.99  --bmc1_min_bound                        0
% 2.56/0.99  --bmc1_max_bound                        -1
% 2.56/0.99  --bmc1_max_bound_default                -1
% 2.56/0.99  --bmc1_symbol_reachability              true
% 2.56/0.99  --bmc1_property_lemmas                  false
% 2.56/0.99  --bmc1_k_induction                      false
% 2.56/0.99  --bmc1_non_equiv_states                 false
% 2.56/0.99  --bmc1_deadlock                         false
% 2.56/0.99  --bmc1_ucm                              false
% 2.56/0.99  --bmc1_add_unsat_core                   none
% 2.56/0.99  --bmc1_unsat_core_children              false
% 2.56/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.56/0.99  --bmc1_out_stat                         full
% 2.56/0.99  --bmc1_ground_init                      false
% 2.56/0.99  --bmc1_pre_inst_next_state              false
% 2.56/0.99  --bmc1_pre_inst_state                   false
% 2.56/0.99  --bmc1_pre_inst_reach_state             false
% 2.56/0.99  --bmc1_out_unsat_core                   false
% 2.56/0.99  --bmc1_aig_witness_out                  false
% 2.56/0.99  --bmc1_verbose                          false
% 2.56/0.99  --bmc1_dump_clauses_tptp                false
% 2.56/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.56/0.99  --bmc1_dump_file                        -
% 2.56/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.56/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.56/0.99  --bmc1_ucm_extend_mode                  1
% 2.56/0.99  --bmc1_ucm_init_mode                    2
% 2.56/0.99  --bmc1_ucm_cone_mode                    none
% 2.56/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.56/0.99  --bmc1_ucm_relax_model                  4
% 2.56/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.56/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.56/0.99  --bmc1_ucm_layered_model                none
% 2.56/0.99  --bmc1_ucm_max_lemma_size               10
% 2.56/0.99  
% 2.56/0.99  ------ AIG Options
% 2.56/0.99  
% 2.56/0.99  --aig_mode                              false
% 2.56/0.99  
% 2.56/0.99  ------ Instantiation Options
% 2.56/0.99  
% 2.56/0.99  --instantiation_flag                    true
% 2.56/0.99  --inst_sos_flag                         false
% 2.56/0.99  --inst_sos_phase                        true
% 2.56/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.56/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.56/0.99  --inst_lit_sel_side                     none
% 2.56/0.99  --inst_solver_per_active                1400
% 2.56/0.99  --inst_solver_calls_frac                1.
% 2.56/0.99  --inst_passive_queue_type               priority_queues
% 2.56/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.56/0.99  --inst_passive_queues_freq              [25;2]
% 2.56/0.99  --inst_dismatching                      true
% 2.56/0.99  --inst_eager_unprocessed_to_passive     true
% 2.56/0.99  --inst_prop_sim_given                   true
% 2.56/0.99  --inst_prop_sim_new                     false
% 2.56/0.99  --inst_subs_new                         false
% 2.56/0.99  --inst_eq_res_simp                      false
% 2.56/0.99  --inst_subs_given                       false
% 2.56/0.99  --inst_orphan_elimination               true
% 2.56/0.99  --inst_learning_loop_flag               true
% 2.56/0.99  --inst_learning_start                   3000
% 2.56/0.99  --inst_learning_factor                  2
% 2.56/0.99  --inst_start_prop_sim_after_learn       3
% 2.56/0.99  --inst_sel_renew                        solver
% 2.56/0.99  --inst_lit_activity_flag                true
% 2.56/0.99  --inst_restr_to_given                   false
% 2.56/0.99  --inst_activity_threshold               500
% 2.56/0.99  --inst_out_proof                        true
% 2.56/0.99  
% 2.56/0.99  ------ Resolution Options
% 2.56/0.99  
% 2.56/0.99  --resolution_flag                       false
% 2.56/0.99  --res_lit_sel                           adaptive
% 2.56/0.99  --res_lit_sel_side                      none
% 2.56/0.99  --res_ordering                          kbo
% 2.56/0.99  --res_to_prop_solver                    active
% 2.56/0.99  --res_prop_simpl_new                    false
% 2.56/0.99  --res_prop_simpl_given                  true
% 2.56/0.99  --res_passive_queue_type                priority_queues
% 2.56/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.56/0.99  --res_passive_queues_freq               [15;5]
% 2.56/0.99  --res_forward_subs                      full
% 2.56/0.99  --res_backward_subs                     full
% 2.56/0.99  --res_forward_subs_resolution           true
% 2.56/0.99  --res_backward_subs_resolution          true
% 2.56/0.99  --res_orphan_elimination                true
% 2.56/0.99  --res_time_limit                        2.
% 2.56/0.99  --res_out_proof                         true
% 2.56/0.99  
% 2.56/0.99  ------ Superposition Options
% 2.56/0.99  
% 2.56/0.99  --superposition_flag                    true
% 2.56/0.99  --sup_passive_queue_type                priority_queues
% 2.56/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.56/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.56/0.99  --demod_completeness_check              fast
% 2.56/0.99  --demod_use_ground                      true
% 2.56/0.99  --sup_to_prop_solver                    passive
% 2.56/0.99  --sup_prop_simpl_new                    true
% 2.56/0.99  --sup_prop_simpl_given                  true
% 2.56/0.99  --sup_fun_splitting                     false
% 2.56/0.99  --sup_smt_interval                      50000
% 2.56/0.99  
% 2.56/0.99  ------ Superposition Simplification Setup
% 2.56/0.99  
% 2.56/0.99  --sup_indices_passive                   []
% 2.56/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.56/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/0.99  --sup_full_bw                           [BwDemod]
% 2.56/0.99  --sup_immed_triv                        [TrivRules]
% 2.56/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.56/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/0.99  --sup_immed_bw_main                     []
% 2.56/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.56/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.56/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.56/0.99  
% 2.56/0.99  ------ Combination Options
% 2.56/0.99  
% 2.56/0.99  --comb_res_mult                         3
% 2.56/0.99  --comb_sup_mult                         2
% 2.56/0.99  --comb_inst_mult                        10
% 2.56/0.99  
% 2.56/0.99  ------ Debug Options
% 2.56/0.99  
% 2.56/0.99  --dbg_backtrace                         false
% 2.56/0.99  --dbg_dump_prop_clauses                 false
% 2.56/0.99  --dbg_dump_prop_clauses_file            -
% 2.56/0.99  --dbg_out_stat                          false
% 2.56/0.99  
% 2.56/0.99  
% 2.56/0.99  
% 2.56/0.99  
% 2.56/0.99  ------ Proving...
% 2.56/0.99  
% 2.56/0.99  
% 2.56/0.99  % SZS status Theorem for theBenchmark.p
% 2.56/0.99  
% 2.56/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.56/0.99  
% 2.56/0.99  fof(f8,axiom,(
% 2.56/0.99    ! [X0,X1] : (v1_relat_1(X1) => (! [X2] : ~(k10_relat_1(X1,k1_tarski(X2)) = k1_xboole_0 & r2_hidden(X2,X0)) => r1_tarski(X0,k2_relat_1(X1))))),
% 2.56/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.99  
% 2.56/0.99  fof(f21,plain,(
% 2.56/0.99    ! [X0,X1] : ((r1_tarski(X0,k2_relat_1(X1)) | ? [X2] : (k10_relat_1(X1,k1_tarski(X2)) = k1_xboole_0 & r2_hidden(X2,X0))) | ~v1_relat_1(X1))),
% 2.56/0.99    inference(ennf_transformation,[],[f8])).
% 2.56/0.99  
% 2.56/0.99  fof(f22,plain,(
% 2.56/0.99    ! [X0,X1] : (r1_tarski(X0,k2_relat_1(X1)) | ? [X2] : (k10_relat_1(X1,k1_tarski(X2)) = k1_xboole_0 & r2_hidden(X2,X0)) | ~v1_relat_1(X1))),
% 2.56/0.99    inference(flattening,[],[f21])).
% 2.56/0.99  
% 2.56/0.99  fof(f33,plain,(
% 2.56/0.99    ! [X1,X0] : (? [X2] : (k10_relat_1(X1,k1_tarski(X2)) = k1_xboole_0 & r2_hidden(X2,X0)) => (k10_relat_1(X1,k1_tarski(sK0(X0,X1))) = k1_xboole_0 & r2_hidden(sK0(X0,X1),X0)))),
% 2.56/0.99    introduced(choice_axiom,[])).
% 2.56/0.99  
% 2.56/0.99  fof(f34,plain,(
% 2.56/0.99    ! [X0,X1] : (r1_tarski(X0,k2_relat_1(X1)) | (k10_relat_1(X1,k1_tarski(sK0(X0,X1))) = k1_xboole_0 & r2_hidden(sK0(X0,X1),X0)) | ~v1_relat_1(X1))),
% 2.56/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f33])).
% 2.56/0.99  
% 2.56/0.99  fof(f54,plain,(
% 2.56/0.99    ( ! [X0,X1] : (r1_tarski(X0,k2_relat_1(X1)) | k10_relat_1(X1,k1_tarski(sK0(X0,X1))) = k1_xboole_0 | ~v1_relat_1(X1)) )),
% 2.56/0.99    inference(cnf_transformation,[],[f34])).
% 2.56/0.99  
% 2.56/0.99  fof(f13,conjecture,(
% 2.56/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3)) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 2.56/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.99  
% 2.56/0.99  fof(f14,negated_conjecture,(
% 2.56/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3)) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 2.56/0.99    inference(negated_conjecture,[],[f13])).
% 2.56/0.99  
% 2.56/0.99  fof(f15,plain,(
% 2.56/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (! [X3] : ~(k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3)) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 2.56/0.99    inference(pure_predicate_removal,[],[f14])).
% 2.56/0.99  
% 2.56/0.99  fof(f16,plain,(
% 2.56/0.99    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (! [X3] : ~(k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3)) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 2.56/0.99    inference(pure_predicate_removal,[],[f15])).
% 2.56/0.99  
% 2.56/0.99  fof(f27,plain,(
% 2.56/0.99    ? [X0,X1,X2] : ((! [X3] : (k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X3)) | ~r2_hidden(X3,X1)) <~> k2_relset_1(X0,X1,X2) = X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.56/0.99    inference(ennf_transformation,[],[f16])).
% 2.56/0.99  
% 2.56/0.99  fof(f35,plain,(
% 2.56/0.99    ? [X0,X1,X2] : (((k2_relset_1(X0,X1,X2) != X1 | ? [X3] : (k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3)) & r2_hidden(X3,X1))) & (k2_relset_1(X0,X1,X2) = X1 | ! [X3] : (k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X3)) | ~r2_hidden(X3,X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.56/0.99    inference(nnf_transformation,[],[f27])).
% 2.56/0.99  
% 2.56/0.99  fof(f36,plain,(
% 2.56/0.99    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ? [X3] : (k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3)) & r2_hidden(X3,X1))) & (k2_relset_1(X0,X1,X2) = X1 | ! [X3] : (k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X3)) | ~r2_hidden(X3,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.56/0.99    inference(flattening,[],[f35])).
% 2.56/0.99  
% 2.56/0.99  fof(f37,plain,(
% 2.56/0.99    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ? [X3] : (k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3)) & r2_hidden(X3,X1))) & (k2_relset_1(X0,X1,X2) = X1 | ! [X4] : (k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X4)) | ~r2_hidden(X4,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.56/0.99    inference(rectify,[],[f36])).
% 2.56/0.99  
% 2.56/0.99  fof(f39,plain,(
% 2.56/0.99    ( ! [X2,X0,X1] : (? [X3] : (k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3)) & r2_hidden(X3,X1)) => (k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(sK4)) & r2_hidden(sK4,X1))) )),
% 2.56/0.99    introduced(choice_axiom,[])).
% 2.56/0.99  
% 2.56/0.99  fof(f38,plain,(
% 2.56/0.99    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ? [X3] : (k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3)) & r2_hidden(X3,X1))) & (k2_relset_1(X0,X1,X2) = X1 | ! [X4] : (k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X4)) | ~r2_hidden(X4,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((k2_relset_1(sK1,sK2,sK3) != sK2 | ? [X3] : (k1_xboole_0 = k8_relset_1(sK1,sK2,sK3,k1_tarski(X3)) & r2_hidden(X3,sK2))) & (k2_relset_1(sK1,sK2,sK3) = sK2 | ! [X4] : (k1_xboole_0 != k8_relset_1(sK1,sK2,sK3,k1_tarski(X4)) | ~r2_hidden(X4,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))))),
% 2.56/0.99    introduced(choice_axiom,[])).
% 2.56/0.99  
% 2.56/0.99  fof(f40,plain,(
% 2.56/0.99    (k2_relset_1(sK1,sK2,sK3) != sK2 | (k1_xboole_0 = k8_relset_1(sK1,sK2,sK3,k1_tarski(sK4)) & r2_hidden(sK4,sK2))) & (k2_relset_1(sK1,sK2,sK3) = sK2 | ! [X4] : (k1_xboole_0 != k8_relset_1(sK1,sK2,sK3,k1_tarski(X4)) | ~r2_hidden(X4,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.56/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f37,f39,f38])).
% 2.56/0.99  
% 2.56/0.99  fof(f59,plain,(
% 2.56/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.56/0.99    inference(cnf_transformation,[],[f40])).
% 2.56/0.99  
% 2.56/0.99  fof(f11,axiom,(
% 2.56/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.56/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.99  
% 2.56/0.99  fof(f25,plain,(
% 2.56/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.56/0.99    inference(ennf_transformation,[],[f11])).
% 2.56/0.99  
% 2.56/0.99  fof(f57,plain,(
% 2.56/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.56/0.99    inference(cnf_transformation,[],[f25])).
% 2.56/0.99  
% 2.56/0.99  fof(f10,axiom,(
% 2.56/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 2.56/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.99  
% 2.56/0.99  fof(f24,plain,(
% 2.56/0.99    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.56/0.99    inference(ennf_transformation,[],[f10])).
% 2.56/0.99  
% 2.56/0.99  fof(f56,plain,(
% 2.56/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.56/0.99    inference(cnf_transformation,[],[f24])).
% 2.56/0.99  
% 2.56/0.99  fof(f6,axiom,(
% 2.56/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.56/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.99  
% 2.56/0.99  fof(f31,plain,(
% 2.56/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.56/0.99    inference(nnf_transformation,[],[f6])).
% 2.56/0.99  
% 2.56/0.99  fof(f49,plain,(
% 2.56/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.56/0.99    inference(cnf_transformation,[],[f31])).
% 2.56/0.99  
% 2.56/0.99  fof(f2,axiom,(
% 2.56/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.56/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.99  
% 2.56/0.99  fof(f28,plain,(
% 2.56/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.56/0.99    inference(nnf_transformation,[],[f2])).
% 2.56/0.99  
% 2.56/0.99  fof(f29,plain,(
% 2.56/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.56/0.99    inference(flattening,[],[f28])).
% 2.56/0.99  
% 2.56/0.99  fof(f44,plain,(
% 2.56/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.56/0.99    inference(cnf_transformation,[],[f29])).
% 2.56/0.99  
% 2.56/0.99  fof(f9,axiom,(
% 2.56/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.56/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.99  
% 2.56/0.99  fof(f23,plain,(
% 2.56/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.56/0.99    inference(ennf_transformation,[],[f9])).
% 2.56/0.99  
% 2.56/0.99  fof(f55,plain,(
% 2.56/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.56/0.99    inference(cnf_transformation,[],[f23])).
% 2.56/0.99  
% 2.56/0.99  fof(f12,axiom,(
% 2.56/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 2.56/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.99  
% 2.56/0.99  fof(f26,plain,(
% 2.56/0.99    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.56/0.99    inference(ennf_transformation,[],[f12])).
% 2.56/0.99  
% 2.56/0.99  fof(f58,plain,(
% 2.56/0.99    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.56/0.99    inference(cnf_transformation,[],[f26])).
% 2.56/0.99  
% 2.56/0.99  fof(f5,axiom,(
% 2.56/0.99    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.56/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.99  
% 2.56/0.99  fof(f30,plain,(
% 2.56/0.99    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.56/0.99    inference(nnf_transformation,[],[f5])).
% 2.56/0.99  
% 2.56/0.99  fof(f47,plain,(
% 2.56/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 2.56/0.99    inference(cnf_transformation,[],[f30])).
% 2.56/0.99  
% 2.56/0.99  fof(f60,plain,(
% 2.56/0.99    ( ! [X4] : (k2_relset_1(sK1,sK2,sK3) = sK2 | k1_xboole_0 != k8_relset_1(sK1,sK2,sK3,k1_tarski(X4)) | ~r2_hidden(X4,sK2)) )),
% 2.56/0.99    inference(cnf_transformation,[],[f40])).
% 2.56/0.99  
% 2.56/0.99  fof(f53,plain,(
% 2.56/0.99    ( ! [X0,X1] : (r1_tarski(X0,k2_relat_1(X1)) | r2_hidden(sK0(X0,X1),X0) | ~v1_relat_1(X1)) )),
% 2.56/0.99    inference(cnf_transformation,[],[f34])).
% 2.56/0.99  
% 2.56/0.99  fof(f62,plain,(
% 2.56/0.99    k2_relset_1(sK1,sK2,sK3) != sK2 | k1_xboole_0 = k8_relset_1(sK1,sK2,sK3,k1_tarski(sK4))),
% 2.56/0.99    inference(cnf_transformation,[],[f40])).
% 2.56/0.99  
% 2.56/0.99  fof(f7,axiom,(
% 2.56/0.99    ! [X0,X1] : (v1_relat_1(X1) => (k10_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 2.56/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.99  
% 2.56/0.99  fof(f20,plain,(
% 2.56/0.99    ! [X0,X1] : ((k10_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.56/0.99    inference(ennf_transformation,[],[f7])).
% 2.56/0.99  
% 2.56/0.99  fof(f32,plain,(
% 2.56/0.99    ! [X0,X1] : (((k10_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k2_relat_1(X1),X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k10_relat_1(X1,X0) != k1_xboole_0)) | ~v1_relat_1(X1))),
% 2.56/0.99    inference(nnf_transformation,[],[f20])).
% 2.56/0.99  
% 2.56/0.99  fof(f51,plain,(
% 2.56/0.99    ( ! [X0,X1] : (r1_xboole_0(k2_relat_1(X1),X0) | k10_relat_1(X1,X0) != k1_xboole_0 | ~v1_relat_1(X1)) )),
% 2.56/0.99    inference(cnf_transformation,[],[f32])).
% 2.56/0.99  
% 2.56/0.99  fof(f1,axiom,(
% 2.56/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.56/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.99  
% 2.56/0.99  fof(f17,plain,(
% 2.56/0.99    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.56/0.99    inference(ennf_transformation,[],[f1])).
% 2.56/0.99  
% 2.56/0.99  fof(f41,plain,(
% 2.56/0.99    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 2.56/0.99    inference(cnf_transformation,[],[f17])).
% 2.56/0.99  
% 2.56/0.99  fof(f48,plain,(
% 2.56/0.99    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.56/0.99    inference(cnf_transformation,[],[f30])).
% 2.56/0.99  
% 2.56/0.99  fof(f61,plain,(
% 2.56/0.99    k2_relset_1(sK1,sK2,sK3) != sK2 | r2_hidden(sK4,sK2)),
% 2.56/0.99    inference(cnf_transformation,[],[f40])).
% 2.56/0.99  
% 2.56/0.99  fof(f3,axiom,(
% 2.56/0.99    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 2.56/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.99  
% 2.56/0.99  fof(f18,plain,(
% 2.56/0.99    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 2.56/0.99    inference(ennf_transformation,[],[f3])).
% 2.56/0.99  
% 2.56/0.99  fof(f19,plain,(
% 2.56/0.99    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 2.56/0.99    inference(flattening,[],[f18])).
% 2.56/0.99  
% 2.56/0.99  fof(f45,plain,(
% 2.56/0.99    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 2.56/0.99    inference(cnf_transformation,[],[f19])).
% 2.56/0.99  
% 2.56/0.99  fof(f4,axiom,(
% 2.56/0.99    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 2.56/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.99  
% 2.56/0.99  fof(f46,plain,(
% 2.56/0.99    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 2.56/0.99    inference(cnf_transformation,[],[f4])).
% 2.56/0.99  
% 2.56/0.99  cnf(c_12,plain,
% 2.56/0.99      ( r1_tarski(X0,k2_relat_1(X1))
% 2.56/0.99      | ~ v1_relat_1(X1)
% 2.56/0.99      | k10_relat_1(X1,k1_tarski(sK0(X0,X1))) = k1_xboole_0 ),
% 2.56/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_1255,plain,
% 2.56/0.99      ( k10_relat_1(X0,k1_tarski(sK0(X1,X0))) = k1_xboole_0
% 2.56/0.99      | r1_tarski(X1,k2_relat_1(X0)) = iProver_top
% 2.56/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.56/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_21,negated_conjecture,
% 2.56/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.56/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_1250,plain,
% 2.56/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.56/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_16,plain,
% 2.56/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.56/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_1252,plain,
% 2.56/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.56/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.56/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_1671,plain,
% 2.56/0.99      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 2.56/0.99      inference(superposition,[status(thm)],[c_1250,c_1252]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_15,plain,
% 2.56/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/0.99      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 2.56/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_1253,plain,
% 2.56/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.56/0.99      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 2.56/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_2306,plain,
% 2.56/0.99      ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top
% 2.56/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 2.56/0.99      inference(superposition,[status(thm)],[c_1671,c_1253]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_22,plain,
% 2.56/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.56/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_2716,plain,
% 2.56/0.99      ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top ),
% 2.56/0.99      inference(global_propositional_subsumption,
% 2.56/0.99                [status(thm)],
% 2.56/0.99                [c_2306,c_22]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_9,plain,
% 2.56/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.56/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_1258,plain,
% 2.56/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.56/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 2.56/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_2721,plain,
% 2.56/0.99      ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
% 2.56/0.99      inference(superposition,[status(thm)],[c_2716,c_1258]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_1,plain,
% 2.56/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.56/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_1261,plain,
% 2.56/0.99      ( X0 = X1
% 2.56/0.99      | r1_tarski(X1,X0) != iProver_top
% 2.56/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 2.56/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_2823,plain,
% 2.56/0.99      ( k2_relat_1(sK3) = sK2
% 2.56/0.99      | r1_tarski(sK2,k2_relat_1(sK3)) != iProver_top ),
% 2.56/0.99      inference(superposition,[status(thm)],[c_2721,c_1261]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_3012,plain,
% 2.56/0.99      ( k10_relat_1(sK3,k1_tarski(sK0(sK2,sK3))) = k1_xboole_0
% 2.56/0.99      | k2_relat_1(sK3) = sK2
% 2.56/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.56/0.99      inference(superposition,[status(thm)],[c_1255,c_2823]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_14,plain,
% 2.56/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/0.99      | v1_relat_1(X0) ),
% 2.56/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_1400,plain,
% 2.56/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.56/0.99      | v1_relat_1(sK3) ),
% 2.56/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_3039,plain,
% 2.56/0.99      ( ~ v1_relat_1(sK3)
% 2.56/0.99      | k10_relat_1(sK3,k1_tarski(sK0(sK2,sK3))) = k1_xboole_0
% 2.56/0.99      | k2_relat_1(sK3) = sK2 ),
% 2.56/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3012]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_3315,plain,
% 2.56/0.99      ( k2_relat_1(sK3) = sK2
% 2.56/0.99      | k10_relat_1(sK3,k1_tarski(sK0(sK2,sK3))) = k1_xboole_0 ),
% 2.56/0.99      inference(global_propositional_subsumption,
% 2.56/0.99                [status(thm)],
% 2.56/0.99                [c_3012,c_21,c_1400,c_3039]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_3316,plain,
% 2.56/0.99      ( k10_relat_1(sK3,k1_tarski(sK0(sK2,sK3))) = k1_xboole_0
% 2.56/0.99      | k2_relat_1(sK3) = sK2 ),
% 2.56/0.99      inference(renaming,[status(thm)],[c_3315]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_17,plain,
% 2.56/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/0.99      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 2.56/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_1251,plain,
% 2.56/0.99      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 2.56/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.56/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_2292,plain,
% 2.56/0.99      ( k8_relset_1(sK1,sK2,sK3,X0) = k10_relat_1(sK3,X0) ),
% 2.56/0.99      inference(superposition,[status(thm)],[c_1250,c_1251]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_7,plain,
% 2.56/0.99      ( r2_hidden(X0,X1) | ~ r1_tarski(k1_tarski(X0),X1) ),
% 2.56/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_170,plain,
% 2.56/0.99      ( r2_hidden(X0,X1) | ~ r1_tarski(k1_tarski(X0),X1) ),
% 2.56/0.99      inference(prop_impl,[status(thm)],[c_7]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_20,negated_conjecture,
% 2.56/0.99      ( ~ r2_hidden(X0,sK2)
% 2.56/0.99      | k2_relset_1(sK1,sK2,sK3) = sK2
% 2.56/0.99      | k1_xboole_0 != k8_relset_1(sK1,sK2,sK3,k1_tarski(X0)) ),
% 2.56/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_403,plain,
% 2.56/0.99      ( ~ r1_tarski(k1_tarski(X0),X1)
% 2.56/0.99      | X2 != X0
% 2.56/0.99      | k8_relset_1(sK1,sK2,sK3,k1_tarski(X2)) != k1_xboole_0
% 2.56/0.99      | k2_relset_1(sK1,sK2,sK3) = sK2
% 2.56/0.99      | sK2 != X1 ),
% 2.56/0.99      inference(resolution_lifted,[status(thm)],[c_170,c_20]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_404,plain,
% 2.56/0.99      ( ~ r1_tarski(k1_tarski(X0),sK2)
% 2.56/0.99      | k8_relset_1(sK1,sK2,sK3,k1_tarski(X0)) != k1_xboole_0
% 2.56/0.99      | k2_relset_1(sK1,sK2,sK3) = sK2 ),
% 2.56/0.99      inference(unflattening,[status(thm)],[c_403]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_1246,plain,
% 2.56/0.99      ( k8_relset_1(sK1,sK2,sK3,k1_tarski(X0)) != k1_xboole_0
% 2.56/0.99      | k2_relset_1(sK1,sK2,sK3) = sK2
% 2.56/0.99      | r1_tarski(k1_tarski(X0),sK2) != iProver_top ),
% 2.56/0.99      inference(predicate_to_equality,[status(thm)],[c_404]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_1846,plain,
% 2.56/0.99      ( k8_relset_1(sK1,sK2,sK3,k1_tarski(X0)) != k1_xboole_0
% 2.56/0.99      | k2_relat_1(sK3) = sK2
% 2.56/0.99      | r1_tarski(k1_tarski(X0),sK2) != iProver_top ),
% 2.56/0.99      inference(demodulation,[status(thm)],[c_1671,c_1246]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_2606,plain,
% 2.56/0.99      ( k10_relat_1(sK3,k1_tarski(X0)) != k1_xboole_0
% 2.56/0.99      | k2_relat_1(sK3) = sK2
% 2.56/0.99      | r1_tarski(k1_tarski(X0),sK2) != iProver_top ),
% 2.56/0.99      inference(demodulation,[status(thm)],[c_2292,c_1846]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_3320,plain,
% 2.56/0.99      ( k2_relat_1(sK3) = sK2
% 2.56/0.99      | r1_tarski(k1_tarski(sK0(sK2,sK3)),sK2) != iProver_top ),
% 2.56/0.99      inference(superposition,[status(thm)],[c_3316,c_2606]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_2824,plain,
% 2.56/0.99      ( ~ r1_tarski(sK2,k2_relat_1(sK3)) | k2_relat_1(sK3) = sK2 ),
% 2.56/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2823]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_13,plain,
% 2.56/0.99      ( r2_hidden(sK0(X0,X1),X0)
% 2.56/0.99      | r1_tarski(X0,k2_relat_1(X1))
% 2.56/0.99      | ~ v1_relat_1(X1) ),
% 2.56/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_418,plain,
% 2.56/0.99      ( r1_tarski(X0,k2_relat_1(X1))
% 2.56/0.99      | ~ v1_relat_1(X1)
% 2.56/0.99      | k8_relset_1(sK1,sK2,sK3,k1_tarski(X2)) != k1_xboole_0
% 2.56/0.99      | k2_relset_1(sK1,sK2,sK3) = sK2
% 2.56/0.99      | sK0(X0,X1) != X2
% 2.56/0.99      | sK2 != X0 ),
% 2.56/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_419,plain,
% 2.56/0.99      ( r1_tarski(sK2,k2_relat_1(X0))
% 2.56/0.99      | ~ v1_relat_1(X0)
% 2.56/0.99      | k8_relset_1(sK1,sK2,sK3,k1_tarski(sK0(sK2,X0))) != k1_xboole_0
% 2.56/0.99      | k2_relset_1(sK1,sK2,sK3) = sK2 ),
% 2.56/0.99      inference(unflattening,[status(thm)],[c_418]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_1245,plain,
% 2.56/0.99      ( k8_relset_1(sK1,sK2,sK3,k1_tarski(sK0(sK2,X0))) != k1_xboole_0
% 2.56/0.99      | k2_relset_1(sK1,sK2,sK3) = sK2
% 2.56/0.99      | r1_tarski(sK2,k2_relat_1(X0)) = iProver_top
% 2.56/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.56/0.99      inference(predicate_to_equality,[status(thm)],[c_419]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_1845,plain,
% 2.56/0.99      ( k8_relset_1(sK1,sK2,sK3,k1_tarski(sK0(sK2,X0))) != k1_xboole_0
% 2.56/0.99      | k2_relat_1(sK3) = sK2
% 2.56/0.99      | r1_tarski(sK2,k2_relat_1(X0)) = iProver_top
% 2.56/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.56/0.99      inference(demodulation,[status(thm)],[c_1671,c_1245]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_2607,plain,
% 2.56/0.99      ( k10_relat_1(sK3,k1_tarski(sK0(sK2,X0))) != k1_xboole_0
% 2.56/0.99      | k2_relat_1(sK3) = sK2
% 2.56/0.99      | r1_tarski(sK2,k2_relat_1(X0)) = iProver_top
% 2.56/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.56/0.99      inference(demodulation,[status(thm)],[c_2292,c_1845]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_3321,plain,
% 2.56/0.99      ( k2_relat_1(sK3) = sK2
% 2.56/0.99      | r1_tarski(sK2,k2_relat_1(sK3)) = iProver_top
% 2.56/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.56/0.99      inference(superposition,[status(thm)],[c_3316,c_2607]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_3340,plain,
% 2.56/0.99      ( r1_tarski(sK2,k2_relat_1(sK3))
% 2.56/0.99      | ~ v1_relat_1(sK3)
% 2.56/0.99      | k2_relat_1(sK3) = sK2 ),
% 2.56/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3321]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_3342,plain,
% 2.56/0.99      ( k2_relat_1(sK3) = sK2 ),
% 2.56/0.99      inference(global_propositional_subsumption,
% 2.56/0.99                [status(thm)],
% 2.56/0.99                [c_3320,c_21,c_1400,c_2824,c_3340]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_18,negated_conjecture,
% 2.56/0.99      ( k2_relset_1(sK1,sK2,sK3) != sK2
% 2.56/0.99      | k1_xboole_0 = k8_relset_1(sK1,sK2,sK3,k1_tarski(sK4)) ),
% 2.56/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_1848,plain,
% 2.56/0.99      ( k8_relset_1(sK1,sK2,sK3,k1_tarski(sK4)) = k1_xboole_0
% 2.56/0.99      | k2_relat_1(sK3) != sK2 ),
% 2.56/0.99      inference(demodulation,[status(thm)],[c_1671,c_18]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_2605,plain,
% 2.56/0.99      ( k10_relat_1(sK3,k1_tarski(sK4)) = k1_xboole_0
% 2.56/0.99      | k2_relat_1(sK3) != sK2 ),
% 2.56/0.99      inference(demodulation,[status(thm)],[c_2292,c_1848]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_3349,plain,
% 2.56/0.99      ( k10_relat_1(sK3,k1_tarski(sK4)) = k1_xboole_0 | sK2 != sK2 ),
% 2.56/0.99      inference(demodulation,[status(thm)],[c_3342,c_2605]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_3357,plain,
% 2.56/0.99      ( k10_relat_1(sK3,k1_tarski(sK4)) = k1_xboole_0 ),
% 2.56/0.99      inference(equality_resolution_simp,[status(thm)],[c_3349]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_11,plain,
% 2.56/0.99      ( r1_xboole_0(k2_relat_1(X0),X1)
% 2.56/0.99      | ~ v1_relat_1(X0)
% 2.56/0.99      | k10_relat_1(X0,X1) != k1_xboole_0 ),
% 2.56/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_1256,plain,
% 2.56/0.99      ( k10_relat_1(X0,X1) != k1_xboole_0
% 2.56/0.99      | r1_xboole_0(k2_relat_1(X0),X1) = iProver_top
% 2.56/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.56/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_3587,plain,
% 2.56/0.99      ( r1_xboole_0(k2_relat_1(sK3),k1_tarski(sK4)) = iProver_top
% 2.56/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.56/0.99      inference(superposition,[status(thm)],[c_3357,c_1256]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_3588,plain,
% 2.56/0.99      ( r1_xboole_0(sK2,k1_tarski(sK4)) = iProver_top
% 2.56/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.56/0.99      inference(light_normalisation,[status(thm)],[c_3587,c_3342]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_1401,plain,
% 2.56/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.56/0.99      | v1_relat_1(sK3) = iProver_top ),
% 2.56/0.99      inference(predicate_to_equality,[status(thm)],[c_1400]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_3692,plain,
% 2.56/0.99      ( r1_xboole_0(sK2,k1_tarski(sK4)) = iProver_top ),
% 2.56/0.99      inference(global_propositional_subsumption,
% 2.56/0.99                [status(thm)],
% 2.56/0.99                [c_3588,c_22,c_1401]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_0,plain,
% 2.56/0.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 2.56/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_1262,plain,
% 2.56/0.99      ( r1_xboole_0(X0,X1) != iProver_top
% 2.56/0.99      | r1_xboole_0(X1,X0) = iProver_top ),
% 2.56/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_3697,plain,
% 2.56/0.99      ( r1_xboole_0(k1_tarski(sK4),sK2) = iProver_top ),
% 2.56/0.99      inference(superposition,[status(thm)],[c_3692,c_1262]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_6,plain,
% 2.56/0.99      ( ~ r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1) ),
% 2.56/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_172,plain,
% 2.56/0.99      ( ~ r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1) ),
% 2.56/0.99      inference(prop_impl,[status(thm)],[c_6]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_19,negated_conjecture,
% 2.56/0.99      ( r2_hidden(sK4,sK2) | k2_relset_1(sK1,sK2,sK3) != sK2 ),
% 2.56/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_393,plain,
% 2.56/0.99      ( r1_tarski(k1_tarski(X0),X1)
% 2.56/0.99      | k2_relset_1(sK1,sK2,sK3) != sK2
% 2.56/0.99      | sK4 != X0
% 2.56/0.99      | sK2 != X1 ),
% 2.56/0.99      inference(resolution_lifted,[status(thm)],[c_172,c_19]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_394,plain,
% 2.56/0.99      ( r1_tarski(k1_tarski(sK4),sK2) | k2_relset_1(sK1,sK2,sK3) != sK2 ),
% 2.56/0.99      inference(unflattening,[status(thm)],[c_393]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_1247,plain,
% 2.56/0.99      ( k2_relset_1(sK1,sK2,sK3) != sK2
% 2.56/0.99      | r1_tarski(k1_tarski(sK4),sK2) = iProver_top ),
% 2.56/0.99      inference(predicate_to_equality,[status(thm)],[c_394]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_1847,plain,
% 2.56/0.99      ( k2_relat_1(sK3) != sK2
% 2.56/0.99      | r1_tarski(k1_tarski(sK4),sK2) = iProver_top ),
% 2.56/0.99      inference(demodulation,[status(thm)],[c_1671,c_1247]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_3350,plain,
% 2.56/0.99      ( sK2 != sK2 | r1_tarski(k1_tarski(sK4),sK2) = iProver_top ),
% 2.56/0.99      inference(demodulation,[status(thm)],[c_3342,c_1847]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_3354,plain,
% 2.56/0.99      ( r1_tarski(k1_tarski(sK4),sK2) = iProver_top ),
% 2.56/0.99      inference(equality_resolution_simp,[status(thm)],[c_3350]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_4,plain,
% 2.56/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X0,X1) | v1_xboole_0(X0) ),
% 2.56/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_5,plain,
% 2.56/0.99      ( ~ v1_xboole_0(k1_tarski(X0)) ),
% 2.56/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_292,plain,
% 2.56/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X0,X1) | k1_tarski(X2) != X0 ),
% 2.56/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_5]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_293,plain,
% 2.56/0.99      ( ~ r1_tarski(k1_tarski(X0),X1) | ~ r1_xboole_0(k1_tarski(X0),X1) ),
% 2.56/0.99      inference(unflattening,[status(thm)],[c_292]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_1249,plain,
% 2.56/0.99      ( r1_tarski(k1_tarski(X0),X1) != iProver_top
% 2.56/0.99      | r1_xboole_0(k1_tarski(X0),X1) != iProver_top ),
% 2.56/0.99      inference(predicate_to_equality,[status(thm)],[c_293]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_3593,plain,
% 2.56/0.99      ( r1_xboole_0(k1_tarski(sK4),sK2) != iProver_top ),
% 2.56/0.99      inference(superposition,[status(thm)],[c_3354,c_1249]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(contradiction,plain,
% 2.56/0.99      ( $false ),
% 2.56/0.99      inference(minisat,[status(thm)],[c_3697,c_3593]) ).
% 2.56/0.99  
% 2.56/0.99  
% 2.56/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.56/0.99  
% 2.56/0.99  ------                               Statistics
% 2.56/0.99  
% 2.56/0.99  ------ General
% 2.56/0.99  
% 2.56/0.99  abstr_ref_over_cycles:                  0
% 2.56/0.99  abstr_ref_under_cycles:                 0
% 2.56/0.99  gc_basic_clause_elim:                   0
% 2.56/0.99  forced_gc_time:                         0
% 2.56/0.99  parsing_time:                           0.008
% 2.56/0.99  unif_index_cands_time:                  0.
% 2.56/0.99  unif_index_add_time:                    0.
% 2.56/0.99  orderings_time:                         0.
% 2.56/0.99  out_proof_time:                         0.008
% 2.56/0.99  total_time:                             0.134
% 2.56/0.99  num_of_symbols:                         50
% 2.56/0.99  num_of_terms:                           3294
% 2.56/0.99  
% 2.56/0.99  ------ Preprocessing
% 2.56/0.99  
% 2.56/0.99  num_of_splits:                          0
% 2.56/0.99  num_of_split_atoms:                     0
% 2.56/0.99  num_of_reused_defs:                     0
% 2.56/0.99  num_eq_ax_congr_red:                    16
% 2.56/0.99  num_of_sem_filtered_clauses:            1
% 2.56/0.99  num_of_subtypes:                        0
% 2.56/0.99  monotx_restored_types:                  0
% 2.56/0.99  sat_num_of_epr_types:                   0
% 2.56/0.99  sat_num_of_non_cyclic_types:            0
% 2.56/0.99  sat_guarded_non_collapsed_types:        0
% 2.56/0.99  num_pure_diseq_elim:                    0
% 2.56/0.99  simp_replaced_by:                       0
% 2.56/0.99  res_preprocessed:                       103
% 2.56/0.99  prep_upred:                             0
% 2.56/0.99  prep_unflattend:                        16
% 2.56/0.99  smt_new_axioms:                         0
% 2.56/0.99  pred_elim_cands:                        4
% 2.56/0.99  pred_elim:                              2
% 2.56/0.99  pred_elim_cl:                           2
% 2.56/0.99  pred_elim_cycles:                       5
% 2.56/0.99  merged_defs:                            10
% 2.56/0.99  merged_defs_ncl:                        0
% 2.56/0.99  bin_hyper_res:                          10
% 2.56/0.99  prep_cycles:                            4
% 2.56/0.99  pred_elim_time:                         0.006
% 2.56/0.99  splitting_time:                         0.
% 2.56/0.99  sem_filter_time:                        0.
% 2.56/0.99  monotx_time:                            0.
% 2.56/0.99  subtype_inf_time:                       0.
% 2.56/0.99  
% 2.56/0.99  ------ Problem properties
% 2.56/0.99  
% 2.56/0.99  clauses:                                19
% 2.56/0.99  conjectures:                            2
% 2.56/0.99  epr:                                    3
% 2.56/0.99  horn:                                   16
% 2.56/0.99  ground:                                 3
% 2.56/0.99  unary:                                  2
% 2.56/0.99  binary:                                 10
% 2.56/0.99  lits:                                   44
% 2.56/0.99  lits_eq:                                13
% 2.56/0.99  fd_pure:                                0
% 2.56/0.99  fd_pseudo:                              0
% 2.56/0.99  fd_cond:                                0
% 2.56/0.99  fd_pseudo_cond:                         1
% 2.56/0.99  ac_symbols:                             0
% 2.56/0.99  
% 2.56/0.99  ------ Propositional Solver
% 2.56/0.99  
% 2.56/0.99  prop_solver_calls:                      28
% 2.56/0.99  prop_fast_solver_calls:                 654
% 2.56/0.99  smt_solver_calls:                       0
% 2.56/0.99  smt_fast_solver_calls:                  0
% 2.56/0.99  prop_num_of_clauses:                    1269
% 2.56/0.99  prop_preprocess_simplified:             4472
% 2.56/0.99  prop_fo_subsumed:                       4
% 2.56/0.99  prop_solver_time:                       0.
% 2.56/0.99  smt_solver_time:                        0.
% 2.56/0.99  smt_fast_solver_time:                   0.
% 2.56/0.99  prop_fast_solver_time:                  0.
% 2.56/0.99  prop_unsat_core_time:                   0.
% 2.56/0.99  
% 2.56/0.99  ------ QBF
% 2.56/0.99  
% 2.56/0.99  qbf_q_res:                              0
% 2.56/0.99  qbf_num_tautologies:                    0
% 2.56/0.99  qbf_prep_cycles:                        0
% 2.56/0.99  
% 2.56/0.99  ------ BMC1
% 2.56/0.99  
% 2.56/0.99  bmc1_current_bound:                     -1
% 2.56/0.99  bmc1_last_solved_bound:                 -1
% 2.56/0.99  bmc1_unsat_core_size:                   -1
% 2.56/0.99  bmc1_unsat_core_parents_size:           -1
% 2.56/0.99  bmc1_merge_next_fun:                    0
% 2.56/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.56/0.99  
% 2.56/0.99  ------ Instantiation
% 2.56/0.99  
% 2.56/0.99  inst_num_of_clauses:                    382
% 2.56/0.99  inst_num_in_passive:                    44
% 2.56/0.99  inst_num_in_active:                     220
% 2.56/0.99  inst_num_in_unprocessed:                119
% 2.56/0.99  inst_num_of_loops:                      230
% 2.56/0.99  inst_num_of_learning_restarts:          0
% 2.56/0.99  inst_num_moves_active_passive:          7
% 2.56/0.99  inst_lit_activity:                      0
% 2.56/0.99  inst_lit_activity_moves:                0
% 2.56/0.99  inst_num_tautologies:                   0
% 2.56/0.99  inst_num_prop_implied:                  0
% 2.56/0.99  inst_num_existing_simplified:           0
% 2.56/0.99  inst_num_eq_res_simplified:             0
% 2.56/0.99  inst_num_child_elim:                    0
% 2.56/0.99  inst_num_of_dismatching_blockings:      123
% 2.56/0.99  inst_num_of_non_proper_insts:           464
% 2.56/0.99  inst_num_of_duplicates:                 0
% 2.56/0.99  inst_inst_num_from_inst_to_res:         0
% 2.56/0.99  inst_dismatching_checking_time:         0.
% 2.56/0.99  
% 2.56/0.99  ------ Resolution
% 2.56/0.99  
% 2.56/0.99  res_num_of_clauses:                     0
% 2.56/0.99  res_num_in_passive:                     0
% 2.56/0.99  res_num_in_active:                      0
% 2.56/0.99  res_num_of_loops:                       107
% 2.56/0.99  res_forward_subset_subsumed:            49
% 2.56/0.99  res_backward_subset_subsumed:           2
% 2.56/0.99  res_forward_subsumed:                   0
% 2.56/0.99  res_backward_subsumed:                  0
% 2.56/0.99  res_forward_subsumption_resolution:     0
% 2.56/0.99  res_backward_subsumption_resolution:    0
% 2.56/0.99  res_clause_to_clause_subsumption:       219
% 2.56/0.99  res_orphan_elimination:                 0
% 2.56/0.99  res_tautology_del:                      43
% 2.56/0.99  res_num_eq_res_simplified:              0
% 2.56/0.99  res_num_sel_changes:                    0
% 2.56/0.99  res_moves_from_active_to_pass:          0
% 2.56/0.99  
% 2.56/0.99  ------ Superposition
% 2.56/0.99  
% 2.56/0.99  sup_time_total:                         0.
% 2.56/0.99  sup_time_generating:                    0.
% 2.56/0.99  sup_time_sim_full:                      0.
% 2.56/0.99  sup_time_sim_immed:                     0.
% 2.56/0.99  
% 2.56/0.99  sup_num_of_clauses:                     48
% 2.56/0.99  sup_num_in_active:                      30
% 2.56/0.99  sup_num_in_passive:                     18
% 2.56/0.99  sup_num_of_loops:                       44
% 2.56/0.99  sup_fw_superposition:                   18
% 2.56/0.99  sup_bw_superposition:                   22
% 2.56/0.99  sup_immediate_simplified:               3
% 2.56/0.99  sup_given_eliminated:                   0
% 2.56/0.99  comparisons_done:                       0
% 2.56/0.99  comparisons_avoided:                    3
% 2.56/0.99  
% 2.56/0.99  ------ Simplifications
% 2.56/0.99  
% 2.56/0.99  
% 2.56/0.99  sim_fw_subset_subsumed:                 1
% 2.56/0.99  sim_bw_subset_subsumed:                 3
% 2.56/0.99  sim_fw_subsumed:                        1
% 2.56/0.99  sim_bw_subsumed:                        0
% 2.56/0.99  sim_fw_subsumption_res:                 0
% 2.56/0.99  sim_bw_subsumption_res:                 0
% 2.56/0.99  sim_tautology_del:                      1
% 2.56/0.99  sim_eq_tautology_del:                   3
% 2.56/0.99  sim_eq_res_simp:                        2
% 2.56/0.99  sim_fw_demodulated:                     0
% 2.56/0.99  sim_bw_demodulated:                     14
% 2.56/0.99  sim_light_normalised:                   1
% 2.56/0.99  sim_joinable_taut:                      0
% 2.56/0.99  sim_joinable_simp:                      0
% 2.56/0.99  sim_ac_normalised:                      0
% 2.56/0.99  sim_smt_subsumption:                    0
% 2.56/0.99  
%------------------------------------------------------------------------------
