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
% DateTime   : Thu Dec  3 12:00:59 EST 2020

% Result     : Theorem 11.52s
% Output     : CNFRefutation 11.52s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 364 expanded)
%              Number of clauses        :   89 ( 132 expanded)
%              Number of leaves         :   20 (  84 expanded)
%              Depth                    :   16
%              Number of atoms          :  417 (1487 expanded)
%              Number of equality atoms :  165 ( 508 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f32])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f68,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f47])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f37,plain,(
    ! [X2,X0,X3] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) = X3
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK4(X3)) = X3
        & r2_hidden(sK4(X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
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
   => ( k2_relset_1(sK1,sK2,sK3) != sK2
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK3,X4) = X3
              & r2_hidden(X4,sK1) )
          | ~ r2_hidden(X3,sK2) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( k2_relset_1(sK1,sK2,sK3) != sK2
    & ! [X3] :
        ( ( k1_funct_1(sK3,sK4(X3)) = X3
          & r2_hidden(sK4(X3),sK1) )
        | ~ r2_hidden(X3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f25,f37,f36])).

fof(f64,plain,(
    ! [X3] :
      ( k1_funct_1(sK3,sK4(X3)) = X3
      | ~ r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f62,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f65,plain,(
    k2_relset_1(sK1,sK2,sK3) != sK2 ),
    inference(cnf_transformation,[],[f38])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f22])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f63,plain,(
    ! [X3] :
      ( r2_hidden(sK4(X3),sK1)
      | ~ r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f67,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f69,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f46])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

cnf(c_549,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1185,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_549])).

cnf(c_30648,plain,
    ( k1_relat_1(X0) != X1
    | sK2 != X1
    | sK2 = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1185])).

cnf(c_30649,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | sK2 = k1_relat_1(k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_30648])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_27917,plain,
    ( k2_zfmisc_1(k2_relset_1(sK1,sK2,sK3),k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_999,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_22,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | k1_funct_1(sK3,sK4(X0)) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_989,plain,
    ( k1_funct_1(sK3,sK4(X0)) = X0
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1958,plain,
    ( k1_funct_1(sK3,sK4(sK0(sK2,X0))) = sK0(sK2,X0)
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_999,c_989])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_987,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_990,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2062,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_987,c_990])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_991,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2117,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2062,c_991])).

cnf(c_29,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2405,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2117,c_29])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_994,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2410,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2405,c_994])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_997,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2917,plain,
    ( k2_relat_1(sK3) = sK2
    | r1_tarski(sK2,k2_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2410,c_997])).

cnf(c_21,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) != sK2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2096,plain,
    ( k2_relat_1(sK3) != sK2 ),
    inference(demodulation,[status(thm)],[c_2062,c_21])).

cnf(c_20172,plain,
    ( r1_tarski(sK2,k2_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2917,c_2096])).

cnf(c_20178,plain,
    ( k1_funct_1(sK3,sK4(sK0(sK2,k2_relat_1(sK3)))) = sK0(sK2,k2_relat_1(sK3)) ),
    inference(superposition,[status(thm)],[c_1958,c_20172])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_320,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | sK3 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_25])).

cnf(c_321,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ r2_hidden(X0,sK1)
    | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK1,sK2,sK3))
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_320])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_325,plain,
    ( r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK1,sK2,sK3))
    | ~ r2_hidden(X0,sK1)
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_321,c_26,c_24])).

cnf(c_326,plain,
    ( ~ r2_hidden(X0,sK1)
    | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK1,sK2,sK3))
    | k1_xboole_0 = sK2 ),
    inference(renaming,[status(thm)],[c_325])).

cnf(c_986,plain,
    ( k1_xboole_0 = sK2
    | r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK1,sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_326])).

cnf(c_2095,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2062,c_986])).

cnf(c_20947,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK0(sK2,k2_relat_1(sK3)),k2_relat_1(sK3)) = iProver_top
    | r2_hidden(sK4(sK0(sK2,k2_relat_1(sK3))),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_20178,c_2095])).

cnf(c_23,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | r2_hidden(sK4(X0),sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_7642,plain,
    ( ~ r2_hidden(sK0(sK2,X0),sK2)
    | r2_hidden(sK4(sK0(sK2,X0)),sK1) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_17409,plain,
    ( ~ r2_hidden(sK0(sK2,k2_relat_1(sK3)),sK2)
    | r2_hidden(sK4(sK0(sK2,k2_relat_1(sK3))),sK1) ),
    inference(instantiation,[status(thm)],[c_7642])).

cnf(c_17410,plain,
    ( r2_hidden(sK0(sK2,k2_relat_1(sK3)),sK2) != iProver_top
    | r2_hidden(sK4(sK0(sK2,k2_relat_1(sK3))),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17409])).

cnf(c_553,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_10731,plain,
    ( k2_zfmisc_1(k2_relset_1(sK1,sK2,sK3),X0) != X1
    | k1_zfmisc_1(k2_zfmisc_1(k2_relset_1(sK1,sK2,sK3),X0)) = k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_553])).

cnf(c_10732,plain,
    ( k2_zfmisc_1(k2_relset_1(sK1,sK2,sK3),k1_xboole_0) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k2_relset_1(sK1,sK2,sK3),k1_xboole_0)) = k1_zfmisc_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_10731])).

cnf(c_3876,plain,
    ( r2_hidden(sK0(X0,k2_relat_1(sK3)),X0)
    | r1_tarski(X0,k2_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_8976,plain,
    ( r2_hidden(sK0(sK2,k2_relat_1(sK3)),sK2)
    | r1_tarski(sK2,k2_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_3876])).

cnf(c_8977,plain,
    ( r2_hidden(sK0(sK2,k2_relat_1(sK3)),sK2) = iProver_top
    | r1_tarski(sK2,k2_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8976])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_3877,plain,
    ( ~ r2_hidden(sK0(X0,k2_relat_1(sK3)),k2_relat_1(sK3))
    | r1_tarski(X0,k2_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_8144,plain,
    ( ~ r2_hidden(sK0(sK2,k2_relat_1(sK3)),k2_relat_1(sK3))
    | r1_tarski(sK2,k2_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_3877])).

cnf(c_8147,plain,
    ( r2_hidden(sK0(sK2,k2_relat_1(sK3)),k2_relat_1(sK3)) != iProver_top
    | r1_tarski(sK2,k2_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8144])).

cnf(c_554,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1158,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_554])).

cnf(c_1247,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X3))
    | X2 != X0
    | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1158])).

cnf(c_2301,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_relset_1(sK1,sK2,sK3),X3)))
    | X2 != X0
    | k1_zfmisc_1(k2_zfmisc_1(k2_relset_1(sK1,sK2,sK3),X3)) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1247])).

cnf(c_2303,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_relset_1(sK1,sK2,sK3),k1_xboole_0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_zfmisc_1(k2_zfmisc_1(k2_relset_1(sK1,sK2,sK3),k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2301])).

cnf(c_17,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_12,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_345,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_17,c_12])).

cnf(c_1580,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_relset_1(sK1,sK2,sK3),X1)))
    | r1_tarski(k1_relat_1(X0),k2_relset_1(sK1,sK2,sK3))
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_345])).

cnf(c_1586,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_relset_1(sK1,sK2,sK3),k1_xboole_0)))
    | r1_tarski(k1_relat_1(k1_xboole_0),k2_relset_1(sK1,sK2,sK3))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1580])).

cnf(c_550,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_1273,plain,
    ( ~ r1_tarski(X0,k2_relset_1(sK1,sK2,sK3))
    | r1_tarski(sK2,k2_relset_1(sK1,sK2,sK3))
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_550])).

cnf(c_1579,plain,
    ( ~ r1_tarski(k1_relat_1(X0),k2_relset_1(sK1,sK2,sK3))
    | r1_tarski(sK2,k2_relset_1(sK1,sK2,sK3))
    | sK2 != k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1273])).

cnf(c_1582,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),k2_relset_1(sK1,sK2,sK3))
    | r1_tarski(sK2,k2_relset_1(sK1,sK2,sK3))
    | sK2 != k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1579])).

cnf(c_1196,plain,
    ( X0 != X1
    | X0 = k2_zfmisc_1(X2,X3)
    | k2_zfmisc_1(X2,X3) != X1 ),
    inference(instantiation,[status(thm)],[c_549])).

cnf(c_1197,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1196])).

cnf(c_1166,plain,
    ( ~ m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK2))
    | r1_tarski(k2_relset_1(sK1,sK2,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1146,plain,
    ( m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1133,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),sK2)
    | ~ r1_tarski(sK2,k2_relset_1(sK1,sK2,sK3))
    | k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_556,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1122,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2))
    | X0 != k2_zfmisc_1(X1,X2) ),
    inference(instantiation,[status(thm)],[c_556])).

cnf(c_1124,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | v1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1122])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_69,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_7,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_67,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_8,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_66,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_64,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_13,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_52,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_15,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_30649,c_27917,c_20947,c_17410,c_10732,c_8977,c_8147,c_2917,c_2303,c_2096,c_1586,c_1582,c_1197,c_1166,c_1146,c_1133,c_1124,c_69,c_67,c_66,c_64,c_52,c_15,c_21,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:14:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 11.52/2.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.52/2.01  
% 11.52/2.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.52/2.01  
% 11.52/2.01  ------  iProver source info
% 11.52/2.01  
% 11.52/2.01  git: date: 2020-06-30 10:37:57 +0100
% 11.52/2.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.52/2.01  git: non_committed_changes: false
% 11.52/2.01  git: last_make_outside_of_git: false
% 11.52/2.01  
% 11.52/2.01  ------ 
% 11.52/2.01  
% 11.52/2.01  ------ Input Options
% 11.52/2.01  
% 11.52/2.01  --out_options                           all
% 11.52/2.01  --tptp_safe_out                         true
% 11.52/2.01  --problem_path                          ""
% 11.52/2.01  --include_path                          ""
% 11.52/2.01  --clausifier                            res/vclausify_rel
% 11.52/2.01  --clausifier_options                    --mode clausify
% 11.52/2.01  --stdin                                 false
% 11.52/2.01  --stats_out                             all
% 11.52/2.01  
% 11.52/2.01  ------ General Options
% 11.52/2.01  
% 11.52/2.01  --fof                                   false
% 11.52/2.01  --time_out_real                         305.
% 11.52/2.01  --time_out_virtual                      -1.
% 11.52/2.01  --symbol_type_check                     false
% 11.52/2.01  --clausify_out                          false
% 11.52/2.01  --sig_cnt_out                           false
% 11.52/2.01  --trig_cnt_out                          false
% 11.52/2.01  --trig_cnt_out_tolerance                1.
% 11.52/2.01  --trig_cnt_out_sk_spl                   false
% 11.52/2.01  --abstr_cl_out                          false
% 11.52/2.01  
% 11.52/2.01  ------ Global Options
% 11.52/2.01  
% 11.52/2.01  --schedule                              default
% 11.52/2.01  --add_important_lit                     false
% 11.52/2.01  --prop_solver_per_cl                    1000
% 11.52/2.01  --min_unsat_core                        false
% 11.52/2.01  --soft_assumptions                      false
% 11.52/2.01  --soft_lemma_size                       3
% 11.52/2.01  --prop_impl_unit_size                   0
% 11.52/2.01  --prop_impl_unit                        []
% 11.52/2.01  --share_sel_clauses                     true
% 11.52/2.01  --reset_solvers                         false
% 11.52/2.01  --bc_imp_inh                            [conj_cone]
% 11.52/2.01  --conj_cone_tolerance                   3.
% 11.52/2.01  --extra_neg_conj                        none
% 11.52/2.01  --large_theory_mode                     true
% 11.52/2.01  --prolific_symb_bound                   200
% 11.52/2.01  --lt_threshold                          2000
% 11.52/2.01  --clause_weak_htbl                      true
% 11.52/2.01  --gc_record_bc_elim                     false
% 11.52/2.01  
% 11.52/2.01  ------ Preprocessing Options
% 11.52/2.01  
% 11.52/2.01  --preprocessing_flag                    true
% 11.52/2.01  --time_out_prep_mult                    0.1
% 11.52/2.01  --splitting_mode                        input
% 11.52/2.01  --splitting_grd                         true
% 11.52/2.01  --splitting_cvd                         false
% 11.52/2.01  --splitting_cvd_svl                     false
% 11.52/2.01  --splitting_nvd                         32
% 11.52/2.01  --sub_typing                            true
% 11.52/2.01  --prep_gs_sim                           true
% 11.52/2.01  --prep_unflatten                        true
% 11.52/2.01  --prep_res_sim                          true
% 11.52/2.01  --prep_upred                            true
% 11.52/2.01  --prep_sem_filter                       exhaustive
% 11.52/2.01  --prep_sem_filter_out                   false
% 11.52/2.01  --pred_elim                             true
% 11.52/2.01  --res_sim_input                         true
% 11.52/2.01  --eq_ax_congr_red                       true
% 11.52/2.01  --pure_diseq_elim                       true
% 11.52/2.01  --brand_transform                       false
% 11.52/2.01  --non_eq_to_eq                          false
% 11.52/2.01  --prep_def_merge                        true
% 11.52/2.01  --prep_def_merge_prop_impl              false
% 11.52/2.01  --prep_def_merge_mbd                    true
% 11.52/2.01  --prep_def_merge_tr_red                 false
% 11.52/2.01  --prep_def_merge_tr_cl                  false
% 11.52/2.01  --smt_preprocessing                     true
% 11.52/2.01  --smt_ac_axioms                         fast
% 11.52/2.01  --preprocessed_out                      false
% 11.52/2.01  --preprocessed_stats                    false
% 11.52/2.01  
% 11.52/2.01  ------ Abstraction refinement Options
% 11.52/2.01  
% 11.52/2.01  --abstr_ref                             []
% 11.52/2.01  --abstr_ref_prep                        false
% 11.52/2.01  --abstr_ref_until_sat                   false
% 11.52/2.01  --abstr_ref_sig_restrict                funpre
% 11.52/2.01  --abstr_ref_af_restrict_to_split_sk     false
% 11.52/2.01  --abstr_ref_under                       []
% 11.52/2.01  
% 11.52/2.01  ------ SAT Options
% 11.52/2.01  
% 11.52/2.01  --sat_mode                              false
% 11.52/2.01  --sat_fm_restart_options                ""
% 11.52/2.01  --sat_gr_def                            false
% 11.52/2.01  --sat_epr_types                         true
% 11.52/2.01  --sat_non_cyclic_types                  false
% 11.52/2.01  --sat_finite_models                     false
% 11.52/2.01  --sat_fm_lemmas                         false
% 11.52/2.01  --sat_fm_prep                           false
% 11.52/2.01  --sat_fm_uc_incr                        true
% 11.52/2.01  --sat_out_model                         small
% 11.52/2.01  --sat_out_clauses                       false
% 11.52/2.01  
% 11.52/2.01  ------ QBF Options
% 11.52/2.01  
% 11.52/2.01  --qbf_mode                              false
% 11.52/2.01  --qbf_elim_univ                         false
% 11.52/2.01  --qbf_dom_inst                          none
% 11.52/2.01  --qbf_dom_pre_inst                      false
% 11.52/2.01  --qbf_sk_in                             false
% 11.52/2.01  --qbf_pred_elim                         true
% 11.52/2.01  --qbf_split                             512
% 11.52/2.01  
% 11.52/2.01  ------ BMC1 Options
% 11.52/2.01  
% 11.52/2.01  --bmc1_incremental                      false
% 11.52/2.01  --bmc1_axioms                           reachable_all
% 11.52/2.01  --bmc1_min_bound                        0
% 11.52/2.01  --bmc1_max_bound                        -1
% 11.52/2.01  --bmc1_max_bound_default                -1
% 11.52/2.01  --bmc1_symbol_reachability              true
% 11.52/2.01  --bmc1_property_lemmas                  false
% 11.52/2.01  --bmc1_k_induction                      false
% 11.52/2.01  --bmc1_non_equiv_states                 false
% 11.52/2.01  --bmc1_deadlock                         false
% 11.52/2.01  --bmc1_ucm                              false
% 11.52/2.01  --bmc1_add_unsat_core                   none
% 11.52/2.01  --bmc1_unsat_core_children              false
% 11.52/2.01  --bmc1_unsat_core_extrapolate_axioms    false
% 11.52/2.01  --bmc1_out_stat                         full
% 11.52/2.01  --bmc1_ground_init                      false
% 11.52/2.01  --bmc1_pre_inst_next_state              false
% 11.52/2.01  --bmc1_pre_inst_state                   false
% 11.52/2.01  --bmc1_pre_inst_reach_state             false
% 11.52/2.01  --bmc1_out_unsat_core                   false
% 11.52/2.01  --bmc1_aig_witness_out                  false
% 11.52/2.01  --bmc1_verbose                          false
% 11.52/2.01  --bmc1_dump_clauses_tptp                false
% 11.52/2.01  --bmc1_dump_unsat_core_tptp             false
% 11.52/2.01  --bmc1_dump_file                        -
% 11.52/2.01  --bmc1_ucm_expand_uc_limit              128
% 11.52/2.01  --bmc1_ucm_n_expand_iterations          6
% 11.52/2.01  --bmc1_ucm_extend_mode                  1
% 11.52/2.01  --bmc1_ucm_init_mode                    2
% 11.52/2.01  --bmc1_ucm_cone_mode                    none
% 11.52/2.01  --bmc1_ucm_reduced_relation_type        0
% 11.52/2.01  --bmc1_ucm_relax_model                  4
% 11.52/2.01  --bmc1_ucm_full_tr_after_sat            true
% 11.52/2.01  --bmc1_ucm_expand_neg_assumptions       false
% 11.52/2.01  --bmc1_ucm_layered_model                none
% 11.52/2.01  --bmc1_ucm_max_lemma_size               10
% 11.52/2.01  
% 11.52/2.01  ------ AIG Options
% 11.52/2.01  
% 11.52/2.01  --aig_mode                              false
% 11.52/2.01  
% 11.52/2.01  ------ Instantiation Options
% 11.52/2.01  
% 11.52/2.01  --instantiation_flag                    true
% 11.52/2.01  --inst_sos_flag                         false
% 11.52/2.01  --inst_sos_phase                        true
% 11.52/2.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.52/2.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.52/2.01  --inst_lit_sel_side                     num_symb
% 11.52/2.01  --inst_solver_per_active                1400
% 11.52/2.01  --inst_solver_calls_frac                1.
% 11.52/2.01  --inst_passive_queue_type               priority_queues
% 11.52/2.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.52/2.01  --inst_passive_queues_freq              [25;2]
% 11.52/2.01  --inst_dismatching                      true
% 11.52/2.01  --inst_eager_unprocessed_to_passive     true
% 11.52/2.01  --inst_prop_sim_given                   true
% 11.52/2.01  --inst_prop_sim_new                     false
% 11.52/2.01  --inst_subs_new                         false
% 11.52/2.01  --inst_eq_res_simp                      false
% 11.52/2.01  --inst_subs_given                       false
% 11.52/2.01  --inst_orphan_elimination               true
% 11.52/2.01  --inst_learning_loop_flag               true
% 11.52/2.01  --inst_learning_start                   3000
% 11.52/2.01  --inst_learning_factor                  2
% 11.52/2.01  --inst_start_prop_sim_after_learn       3
% 11.52/2.01  --inst_sel_renew                        solver
% 11.52/2.01  --inst_lit_activity_flag                true
% 11.52/2.01  --inst_restr_to_given                   false
% 11.52/2.01  --inst_activity_threshold               500
% 11.52/2.01  --inst_out_proof                        true
% 11.52/2.01  
% 11.52/2.01  ------ Resolution Options
% 11.52/2.01  
% 11.52/2.01  --resolution_flag                       true
% 11.52/2.01  --res_lit_sel                           adaptive
% 11.52/2.01  --res_lit_sel_side                      none
% 11.52/2.01  --res_ordering                          kbo
% 11.52/2.01  --res_to_prop_solver                    active
% 11.52/2.01  --res_prop_simpl_new                    false
% 11.52/2.01  --res_prop_simpl_given                  true
% 11.52/2.01  --res_passive_queue_type                priority_queues
% 11.52/2.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.52/2.01  --res_passive_queues_freq               [15;5]
% 11.52/2.01  --res_forward_subs                      full
% 11.52/2.01  --res_backward_subs                     full
% 11.52/2.01  --res_forward_subs_resolution           true
% 11.52/2.01  --res_backward_subs_resolution          true
% 11.52/2.01  --res_orphan_elimination                true
% 11.52/2.01  --res_time_limit                        2.
% 11.52/2.01  --res_out_proof                         true
% 11.52/2.01  
% 11.52/2.01  ------ Superposition Options
% 11.52/2.01  
% 11.52/2.01  --superposition_flag                    true
% 11.52/2.01  --sup_passive_queue_type                priority_queues
% 11.52/2.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.52/2.01  --sup_passive_queues_freq               [8;1;4]
% 11.52/2.01  --demod_completeness_check              fast
% 11.52/2.01  --demod_use_ground                      true
% 11.52/2.01  --sup_to_prop_solver                    passive
% 11.52/2.01  --sup_prop_simpl_new                    true
% 11.52/2.01  --sup_prop_simpl_given                  true
% 11.52/2.01  --sup_fun_splitting                     false
% 11.52/2.01  --sup_smt_interval                      50000
% 11.52/2.01  
% 11.52/2.01  ------ Superposition Simplification Setup
% 11.52/2.01  
% 11.52/2.01  --sup_indices_passive                   []
% 11.52/2.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.52/2.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.52/2.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.52/2.01  --sup_full_triv                         [TrivRules;PropSubs]
% 11.52/2.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.52/2.01  --sup_full_bw                           [BwDemod]
% 11.52/2.01  --sup_immed_triv                        [TrivRules]
% 11.52/2.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.52/2.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.52/2.01  --sup_immed_bw_main                     []
% 11.52/2.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.52/2.01  --sup_input_triv                        [Unflattening;TrivRules]
% 11.52/2.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.52/2.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.52/2.01  
% 11.52/2.01  ------ Combination Options
% 11.52/2.01  
% 11.52/2.01  --comb_res_mult                         3
% 11.52/2.01  --comb_sup_mult                         2
% 11.52/2.01  --comb_inst_mult                        10
% 11.52/2.01  
% 11.52/2.01  ------ Debug Options
% 11.52/2.01  
% 11.52/2.01  --dbg_backtrace                         false
% 11.52/2.01  --dbg_dump_prop_clauses                 false
% 11.52/2.01  --dbg_dump_prop_clauses_file            -
% 11.52/2.01  --dbg_out_stat                          false
% 11.52/2.01  ------ Parsing...
% 11.52/2.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.52/2.01  
% 11.52/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 11.52/2.01  
% 11.52/2.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.52/2.01  
% 11.52/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.52/2.01  ------ Proving...
% 11.52/2.01  ------ Problem Properties 
% 11.52/2.01  
% 11.52/2.01  
% 11.52/2.01  clauses                                 22
% 11.52/2.01  conjectures                             4
% 11.52/2.01  EPR                                     4
% 11.52/2.01  Horn                                    19
% 11.52/2.01  unary                                   8
% 11.52/2.01  binary                                  9
% 11.52/2.01  lits                                    41
% 11.52/2.01  lits eq                                 12
% 11.52/2.01  fd_pure                                 0
% 11.52/2.01  fd_pseudo                               0
% 11.52/2.01  fd_cond                                 1
% 11.52/2.01  fd_pseudo_cond                          1
% 11.52/2.01  AC symbols                              0
% 11.52/2.01  
% 11.52/2.01  ------ Schedule dynamic 5 is on 
% 11.52/2.01  
% 11.52/2.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.52/2.01  
% 11.52/2.01  
% 11.52/2.01  ------ 
% 11.52/2.01  Current options:
% 11.52/2.01  ------ 
% 11.52/2.01  
% 11.52/2.01  ------ Input Options
% 11.52/2.01  
% 11.52/2.01  --out_options                           all
% 11.52/2.01  --tptp_safe_out                         true
% 11.52/2.01  --problem_path                          ""
% 11.52/2.01  --include_path                          ""
% 11.52/2.01  --clausifier                            res/vclausify_rel
% 11.52/2.01  --clausifier_options                    --mode clausify
% 11.52/2.01  --stdin                                 false
% 11.52/2.01  --stats_out                             all
% 11.52/2.01  
% 11.52/2.01  ------ General Options
% 11.52/2.01  
% 11.52/2.01  --fof                                   false
% 11.52/2.01  --time_out_real                         305.
% 11.52/2.01  --time_out_virtual                      -1.
% 11.52/2.01  --symbol_type_check                     false
% 11.52/2.01  --clausify_out                          false
% 11.52/2.01  --sig_cnt_out                           false
% 11.52/2.01  --trig_cnt_out                          false
% 11.52/2.01  --trig_cnt_out_tolerance                1.
% 11.52/2.01  --trig_cnt_out_sk_spl                   false
% 11.52/2.01  --abstr_cl_out                          false
% 11.52/2.01  
% 11.52/2.01  ------ Global Options
% 11.52/2.01  
% 11.52/2.01  --schedule                              default
% 11.52/2.01  --add_important_lit                     false
% 11.52/2.01  --prop_solver_per_cl                    1000
% 11.52/2.01  --min_unsat_core                        false
% 11.52/2.01  --soft_assumptions                      false
% 11.52/2.01  --soft_lemma_size                       3
% 11.52/2.01  --prop_impl_unit_size                   0
% 11.52/2.01  --prop_impl_unit                        []
% 11.52/2.01  --share_sel_clauses                     true
% 11.52/2.01  --reset_solvers                         false
% 11.52/2.01  --bc_imp_inh                            [conj_cone]
% 11.52/2.01  --conj_cone_tolerance                   3.
% 11.52/2.01  --extra_neg_conj                        none
% 11.52/2.01  --large_theory_mode                     true
% 11.52/2.01  --prolific_symb_bound                   200
% 11.52/2.01  --lt_threshold                          2000
% 11.52/2.01  --clause_weak_htbl                      true
% 11.52/2.01  --gc_record_bc_elim                     false
% 11.52/2.01  
% 11.52/2.01  ------ Preprocessing Options
% 11.52/2.01  
% 11.52/2.01  --preprocessing_flag                    true
% 11.52/2.01  --time_out_prep_mult                    0.1
% 11.52/2.01  --splitting_mode                        input
% 11.52/2.01  --splitting_grd                         true
% 11.52/2.01  --splitting_cvd                         false
% 11.52/2.01  --splitting_cvd_svl                     false
% 11.52/2.01  --splitting_nvd                         32
% 11.52/2.01  --sub_typing                            true
% 11.52/2.01  --prep_gs_sim                           true
% 11.52/2.01  --prep_unflatten                        true
% 11.52/2.01  --prep_res_sim                          true
% 11.52/2.01  --prep_upred                            true
% 11.52/2.01  --prep_sem_filter                       exhaustive
% 11.52/2.01  --prep_sem_filter_out                   false
% 11.52/2.01  --pred_elim                             true
% 11.52/2.01  --res_sim_input                         true
% 11.52/2.01  --eq_ax_congr_red                       true
% 11.52/2.01  --pure_diseq_elim                       true
% 11.52/2.01  --brand_transform                       false
% 11.52/2.01  --non_eq_to_eq                          false
% 11.52/2.01  --prep_def_merge                        true
% 11.52/2.01  --prep_def_merge_prop_impl              false
% 11.52/2.01  --prep_def_merge_mbd                    true
% 11.52/2.01  --prep_def_merge_tr_red                 false
% 11.52/2.01  --prep_def_merge_tr_cl                  false
% 11.52/2.01  --smt_preprocessing                     true
% 11.52/2.01  --smt_ac_axioms                         fast
% 11.52/2.01  --preprocessed_out                      false
% 11.52/2.01  --preprocessed_stats                    false
% 11.52/2.01  
% 11.52/2.01  ------ Abstraction refinement Options
% 11.52/2.01  
% 11.52/2.01  --abstr_ref                             []
% 11.52/2.01  --abstr_ref_prep                        false
% 11.52/2.01  --abstr_ref_until_sat                   false
% 11.52/2.01  --abstr_ref_sig_restrict                funpre
% 11.52/2.01  --abstr_ref_af_restrict_to_split_sk     false
% 11.52/2.01  --abstr_ref_under                       []
% 11.52/2.01  
% 11.52/2.01  ------ SAT Options
% 11.52/2.01  
% 11.52/2.01  --sat_mode                              false
% 11.52/2.01  --sat_fm_restart_options                ""
% 11.52/2.01  --sat_gr_def                            false
% 11.52/2.01  --sat_epr_types                         true
% 11.52/2.01  --sat_non_cyclic_types                  false
% 11.52/2.01  --sat_finite_models                     false
% 11.52/2.01  --sat_fm_lemmas                         false
% 11.52/2.01  --sat_fm_prep                           false
% 11.52/2.01  --sat_fm_uc_incr                        true
% 11.52/2.01  --sat_out_model                         small
% 11.52/2.01  --sat_out_clauses                       false
% 11.52/2.01  
% 11.52/2.01  ------ QBF Options
% 11.52/2.01  
% 11.52/2.01  --qbf_mode                              false
% 11.52/2.01  --qbf_elim_univ                         false
% 11.52/2.01  --qbf_dom_inst                          none
% 11.52/2.01  --qbf_dom_pre_inst                      false
% 11.52/2.01  --qbf_sk_in                             false
% 11.52/2.01  --qbf_pred_elim                         true
% 11.52/2.01  --qbf_split                             512
% 11.52/2.01  
% 11.52/2.01  ------ BMC1 Options
% 11.52/2.01  
% 11.52/2.01  --bmc1_incremental                      false
% 11.52/2.01  --bmc1_axioms                           reachable_all
% 11.52/2.01  --bmc1_min_bound                        0
% 11.52/2.01  --bmc1_max_bound                        -1
% 11.52/2.01  --bmc1_max_bound_default                -1
% 11.52/2.01  --bmc1_symbol_reachability              true
% 11.52/2.01  --bmc1_property_lemmas                  false
% 11.52/2.01  --bmc1_k_induction                      false
% 11.52/2.01  --bmc1_non_equiv_states                 false
% 11.52/2.01  --bmc1_deadlock                         false
% 11.52/2.01  --bmc1_ucm                              false
% 11.52/2.01  --bmc1_add_unsat_core                   none
% 11.52/2.01  --bmc1_unsat_core_children              false
% 11.52/2.01  --bmc1_unsat_core_extrapolate_axioms    false
% 11.52/2.01  --bmc1_out_stat                         full
% 11.52/2.01  --bmc1_ground_init                      false
% 11.52/2.01  --bmc1_pre_inst_next_state              false
% 11.52/2.01  --bmc1_pre_inst_state                   false
% 11.52/2.01  --bmc1_pre_inst_reach_state             false
% 11.52/2.01  --bmc1_out_unsat_core                   false
% 11.52/2.01  --bmc1_aig_witness_out                  false
% 11.52/2.01  --bmc1_verbose                          false
% 11.52/2.01  --bmc1_dump_clauses_tptp                false
% 11.52/2.01  --bmc1_dump_unsat_core_tptp             false
% 11.52/2.01  --bmc1_dump_file                        -
% 11.52/2.01  --bmc1_ucm_expand_uc_limit              128
% 11.52/2.01  --bmc1_ucm_n_expand_iterations          6
% 11.52/2.01  --bmc1_ucm_extend_mode                  1
% 11.52/2.01  --bmc1_ucm_init_mode                    2
% 11.52/2.01  --bmc1_ucm_cone_mode                    none
% 11.52/2.01  --bmc1_ucm_reduced_relation_type        0
% 11.52/2.01  --bmc1_ucm_relax_model                  4
% 11.52/2.01  --bmc1_ucm_full_tr_after_sat            true
% 11.52/2.01  --bmc1_ucm_expand_neg_assumptions       false
% 11.52/2.01  --bmc1_ucm_layered_model                none
% 11.52/2.01  --bmc1_ucm_max_lemma_size               10
% 11.52/2.01  
% 11.52/2.01  ------ AIG Options
% 11.52/2.01  
% 11.52/2.01  --aig_mode                              false
% 11.52/2.01  
% 11.52/2.01  ------ Instantiation Options
% 11.52/2.01  
% 11.52/2.01  --instantiation_flag                    true
% 11.52/2.01  --inst_sos_flag                         false
% 11.52/2.01  --inst_sos_phase                        true
% 11.52/2.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.52/2.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.52/2.01  --inst_lit_sel_side                     none
% 11.52/2.01  --inst_solver_per_active                1400
% 11.52/2.01  --inst_solver_calls_frac                1.
% 11.52/2.01  --inst_passive_queue_type               priority_queues
% 11.52/2.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.52/2.01  --inst_passive_queues_freq              [25;2]
% 11.52/2.01  --inst_dismatching                      true
% 11.52/2.01  --inst_eager_unprocessed_to_passive     true
% 11.52/2.01  --inst_prop_sim_given                   true
% 11.52/2.01  --inst_prop_sim_new                     false
% 11.52/2.01  --inst_subs_new                         false
% 11.52/2.01  --inst_eq_res_simp                      false
% 11.52/2.01  --inst_subs_given                       false
% 11.52/2.01  --inst_orphan_elimination               true
% 11.52/2.01  --inst_learning_loop_flag               true
% 11.52/2.01  --inst_learning_start                   3000
% 11.52/2.01  --inst_learning_factor                  2
% 11.52/2.01  --inst_start_prop_sim_after_learn       3
% 11.52/2.01  --inst_sel_renew                        solver
% 11.52/2.01  --inst_lit_activity_flag                true
% 11.52/2.01  --inst_restr_to_given                   false
% 11.52/2.01  --inst_activity_threshold               500
% 11.52/2.01  --inst_out_proof                        true
% 11.52/2.01  
% 11.52/2.01  ------ Resolution Options
% 11.52/2.01  
% 11.52/2.01  --resolution_flag                       false
% 11.52/2.01  --res_lit_sel                           adaptive
% 11.52/2.01  --res_lit_sel_side                      none
% 11.52/2.01  --res_ordering                          kbo
% 11.52/2.01  --res_to_prop_solver                    active
% 11.52/2.01  --res_prop_simpl_new                    false
% 11.52/2.01  --res_prop_simpl_given                  true
% 11.52/2.01  --res_passive_queue_type                priority_queues
% 11.52/2.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.52/2.01  --res_passive_queues_freq               [15;5]
% 11.52/2.01  --res_forward_subs                      full
% 11.52/2.01  --res_backward_subs                     full
% 11.52/2.01  --res_forward_subs_resolution           true
% 11.52/2.01  --res_backward_subs_resolution          true
% 11.52/2.01  --res_orphan_elimination                true
% 11.52/2.01  --res_time_limit                        2.
% 11.52/2.01  --res_out_proof                         true
% 11.52/2.01  
% 11.52/2.01  ------ Superposition Options
% 11.52/2.01  
% 11.52/2.01  --superposition_flag                    true
% 11.52/2.01  --sup_passive_queue_type                priority_queues
% 11.52/2.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.52/2.01  --sup_passive_queues_freq               [8;1;4]
% 11.52/2.01  --demod_completeness_check              fast
% 11.52/2.01  --demod_use_ground                      true
% 11.52/2.01  --sup_to_prop_solver                    passive
% 11.52/2.01  --sup_prop_simpl_new                    true
% 11.52/2.01  --sup_prop_simpl_given                  true
% 11.52/2.01  --sup_fun_splitting                     false
% 11.52/2.01  --sup_smt_interval                      50000
% 11.52/2.01  
% 11.52/2.01  ------ Superposition Simplification Setup
% 11.52/2.01  
% 11.52/2.01  --sup_indices_passive                   []
% 11.52/2.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.52/2.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.52/2.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.52/2.01  --sup_full_triv                         [TrivRules;PropSubs]
% 11.52/2.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.52/2.01  --sup_full_bw                           [BwDemod]
% 11.52/2.01  --sup_immed_triv                        [TrivRules]
% 11.52/2.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.52/2.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.52/2.01  --sup_immed_bw_main                     []
% 11.52/2.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.52/2.01  --sup_input_triv                        [Unflattening;TrivRules]
% 11.52/2.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.52/2.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.52/2.01  
% 11.52/2.01  ------ Combination Options
% 11.52/2.01  
% 11.52/2.01  --comb_res_mult                         3
% 11.52/2.01  --comb_sup_mult                         2
% 11.52/2.01  --comb_inst_mult                        10
% 11.52/2.01  
% 11.52/2.01  ------ Debug Options
% 11.52/2.01  
% 11.52/2.01  --dbg_backtrace                         false
% 11.52/2.01  --dbg_dump_prop_clauses                 false
% 11.52/2.01  --dbg_dump_prop_clauses_file            -
% 11.52/2.01  --dbg_out_stat                          false
% 11.52/2.01  
% 11.52/2.01  
% 11.52/2.01  
% 11.52/2.01  
% 11.52/2.01  ------ Proving...
% 11.52/2.01  
% 11.52/2.01  
% 11.52/2.01  % SZS status Theorem for theBenchmark.p
% 11.52/2.01  
% 11.52/2.01  % SZS output start CNFRefutation for theBenchmark.p
% 11.52/2.01  
% 11.52/2.01  fof(f3,axiom,(
% 11.52/2.01    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 11.52/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.01  
% 11.52/2.01  fof(f32,plain,(
% 11.52/2.01    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 11.52/2.01    inference(nnf_transformation,[],[f3])).
% 11.52/2.01  
% 11.52/2.01  fof(f33,plain,(
% 11.52/2.01    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 11.52/2.01    inference(flattening,[],[f32])).
% 11.52/2.01  
% 11.52/2.01  fof(f47,plain,(
% 11.52/2.01    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 11.52/2.01    inference(cnf_transformation,[],[f33])).
% 11.52/2.01  
% 11.52/2.01  fof(f68,plain,(
% 11.52/2.01    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 11.52/2.01    inference(equality_resolution,[],[f47])).
% 11.52/2.01  
% 11.52/2.01  fof(f1,axiom,(
% 11.52/2.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 11.52/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.01  
% 11.52/2.01  fof(f16,plain,(
% 11.52/2.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 11.52/2.01    inference(ennf_transformation,[],[f1])).
% 11.52/2.01  
% 11.52/2.01  fof(f26,plain,(
% 11.52/2.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 11.52/2.01    inference(nnf_transformation,[],[f16])).
% 11.52/2.01  
% 11.52/2.01  fof(f27,plain,(
% 11.52/2.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.52/2.01    inference(rectify,[],[f26])).
% 11.52/2.01  
% 11.52/2.01  fof(f28,plain,(
% 11.52/2.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 11.52/2.01    introduced(choice_axiom,[])).
% 11.52/2.01  
% 11.52/2.01  fof(f29,plain,(
% 11.52/2.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.52/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 11.52/2.01  
% 11.52/2.01  fof(f40,plain,(
% 11.52/2.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 11.52/2.01    inference(cnf_transformation,[],[f29])).
% 11.52/2.01  
% 11.52/2.01  fof(f13,conjecture,(
% 11.52/2.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 11.52/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.01  
% 11.52/2.01  fof(f14,negated_conjecture,(
% 11.52/2.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 11.52/2.01    inference(negated_conjecture,[],[f13])).
% 11.52/2.01  
% 11.52/2.01  fof(f24,plain,(
% 11.52/2.01    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 11.52/2.01    inference(ennf_transformation,[],[f14])).
% 11.52/2.01  
% 11.52/2.01  fof(f25,plain,(
% 11.52/2.01    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 11.52/2.01    inference(flattening,[],[f24])).
% 11.52/2.01  
% 11.52/2.01  fof(f37,plain,(
% 11.52/2.01    ( ! [X2,X0] : (! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) => (k1_funct_1(X2,sK4(X3)) = X3 & r2_hidden(sK4(X3),X0)))) )),
% 11.52/2.01    introduced(choice_axiom,[])).
% 11.52/2.01  
% 11.52/2.01  fof(f36,plain,(
% 11.52/2.01    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (k2_relset_1(sK1,sK2,sK3) != sK2 & ! [X3] : (? [X4] : (k1_funct_1(sK3,X4) = X3 & r2_hidden(X4,sK1)) | ~r2_hidden(X3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 11.52/2.01    introduced(choice_axiom,[])).
% 11.52/2.01  
% 11.52/2.01  fof(f38,plain,(
% 11.52/2.01    k2_relset_1(sK1,sK2,sK3) != sK2 & ! [X3] : ((k1_funct_1(sK3,sK4(X3)) = X3 & r2_hidden(sK4(X3),sK1)) | ~r2_hidden(X3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 11.52/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f25,f37,f36])).
% 11.52/2.01  
% 11.52/2.01  fof(f64,plain,(
% 11.52/2.01    ( ! [X3] : (k1_funct_1(sK3,sK4(X3)) = X3 | ~r2_hidden(X3,sK2)) )),
% 11.52/2.01    inference(cnf_transformation,[],[f38])).
% 11.52/2.01  
% 11.52/2.01  fof(f62,plain,(
% 11.52/2.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 11.52/2.01    inference(cnf_transformation,[],[f38])).
% 11.52/2.01  
% 11.52/2.01  fof(f11,axiom,(
% 11.52/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 11.52/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.01  
% 11.52/2.01  fof(f21,plain,(
% 11.52/2.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.52/2.01    inference(ennf_transformation,[],[f11])).
% 11.52/2.01  
% 11.52/2.01  fof(f58,plain,(
% 11.52/2.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.52/2.01    inference(cnf_transformation,[],[f21])).
% 11.52/2.01  
% 11.52/2.01  fof(f10,axiom,(
% 11.52/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 11.52/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.01  
% 11.52/2.01  fof(f20,plain,(
% 11.52/2.01    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.52/2.01    inference(ennf_transformation,[],[f10])).
% 11.52/2.01  
% 11.52/2.01  fof(f57,plain,(
% 11.52/2.01    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.52/2.01    inference(cnf_transformation,[],[f20])).
% 11.52/2.01  
% 11.52/2.01  fof(f4,axiom,(
% 11.52/2.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.52/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.01  
% 11.52/2.01  fof(f34,plain,(
% 11.52/2.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.52/2.01    inference(nnf_transformation,[],[f4])).
% 11.52/2.01  
% 11.52/2.01  fof(f48,plain,(
% 11.52/2.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.52/2.01    inference(cnf_transformation,[],[f34])).
% 11.52/2.01  
% 11.52/2.01  fof(f2,axiom,(
% 11.52/2.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.52/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.01  
% 11.52/2.01  fof(f30,plain,(
% 11.52/2.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.52/2.01    inference(nnf_transformation,[],[f2])).
% 11.52/2.01  
% 11.52/2.01  fof(f31,plain,(
% 11.52/2.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.52/2.01    inference(flattening,[],[f30])).
% 11.52/2.01  
% 11.52/2.01  fof(f44,plain,(
% 11.52/2.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.52/2.01    inference(cnf_transformation,[],[f31])).
% 11.52/2.01  
% 11.52/2.01  fof(f65,plain,(
% 11.52/2.01    k2_relset_1(sK1,sK2,sK3) != sK2),
% 11.52/2.01    inference(cnf_transformation,[],[f38])).
% 11.52/2.01  
% 11.52/2.01  fof(f12,axiom,(
% 11.52/2.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 11.52/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.01  
% 11.52/2.01  fof(f22,plain,(
% 11.52/2.01    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 11.52/2.01    inference(ennf_transformation,[],[f12])).
% 11.52/2.01  
% 11.52/2.01  fof(f23,plain,(
% 11.52/2.01    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 11.52/2.01    inference(flattening,[],[f22])).
% 11.52/2.01  
% 11.52/2.01  fof(f59,plain,(
% 11.52/2.01    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 11.52/2.01    inference(cnf_transformation,[],[f23])).
% 11.52/2.01  
% 11.52/2.01  fof(f61,plain,(
% 11.52/2.01    v1_funct_2(sK3,sK1,sK2)),
% 11.52/2.01    inference(cnf_transformation,[],[f38])).
% 11.52/2.01  
% 11.52/2.01  fof(f60,plain,(
% 11.52/2.01    v1_funct_1(sK3)),
% 11.52/2.01    inference(cnf_transformation,[],[f38])).
% 11.52/2.01  
% 11.52/2.01  fof(f63,plain,(
% 11.52/2.01    ( ! [X3] : (r2_hidden(sK4(X3),sK1) | ~r2_hidden(X3,sK2)) )),
% 11.52/2.01    inference(cnf_transformation,[],[f38])).
% 11.52/2.01  
% 11.52/2.01  fof(f41,plain,(
% 11.52/2.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 11.52/2.01    inference(cnf_transformation,[],[f29])).
% 11.52/2.01  
% 11.52/2.01  fof(f9,axiom,(
% 11.52/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 11.52/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.01  
% 11.52/2.01  fof(f15,plain,(
% 11.52/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 11.52/2.01    inference(pure_predicate_removal,[],[f9])).
% 11.52/2.01  
% 11.52/2.01  fof(f19,plain,(
% 11.52/2.01    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.52/2.01    inference(ennf_transformation,[],[f15])).
% 11.52/2.01  
% 11.52/2.01  fof(f56,plain,(
% 11.52/2.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.52/2.01    inference(cnf_transformation,[],[f19])).
% 11.52/2.01  
% 11.52/2.01  fof(f5,axiom,(
% 11.52/2.01    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 11.52/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.01  
% 11.52/2.01  fof(f17,plain,(
% 11.52/2.01    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.52/2.01    inference(ennf_transformation,[],[f5])).
% 11.52/2.01  
% 11.52/2.01  fof(f35,plain,(
% 11.52/2.01    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.52/2.01    inference(nnf_transformation,[],[f17])).
% 11.52/2.01  
% 11.52/2.01  fof(f50,plain,(
% 11.52/2.01    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.52/2.01    inference(cnf_transformation,[],[f35])).
% 11.52/2.01  
% 11.52/2.01  fof(f42,plain,(
% 11.52/2.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.52/2.01    inference(cnf_transformation,[],[f31])).
% 11.52/2.01  
% 11.52/2.01  fof(f67,plain,(
% 11.52/2.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.52/2.01    inference(equality_resolution,[],[f42])).
% 11.52/2.01  
% 11.52/2.01  fof(f46,plain,(
% 11.52/2.01    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 11.52/2.01    inference(cnf_transformation,[],[f33])).
% 11.52/2.01  
% 11.52/2.01  fof(f69,plain,(
% 11.52/2.01    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 11.52/2.01    inference(equality_resolution,[],[f46])).
% 11.52/2.01  
% 11.52/2.01  fof(f45,plain,(
% 11.52/2.01    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0) )),
% 11.52/2.01    inference(cnf_transformation,[],[f33])).
% 11.52/2.01  
% 11.52/2.01  fof(f49,plain,(
% 11.52/2.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.52/2.01    inference(cnf_transformation,[],[f34])).
% 11.52/2.01  
% 11.52/2.01  fof(f6,axiom,(
% 11.52/2.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 11.52/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.01  
% 11.52/2.01  fof(f52,plain,(
% 11.52/2.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 11.52/2.01    inference(cnf_transformation,[],[f6])).
% 11.52/2.01  
% 11.52/2.01  fof(f7,axiom,(
% 11.52/2.01    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 11.52/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.52/2.01  
% 11.52/2.01  fof(f53,plain,(
% 11.52/2.01    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 11.52/2.01    inference(cnf_transformation,[],[f7])).
% 11.52/2.01  
% 11.52/2.01  cnf(c_549,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_1185,plain,
% 11.52/2.01      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 11.52/2.01      inference(instantiation,[status(thm)],[c_549]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_30648,plain,
% 11.52/2.01      ( k1_relat_1(X0) != X1 | sK2 != X1 | sK2 = k1_relat_1(X0) ),
% 11.52/2.01      inference(instantiation,[status(thm)],[c_1185]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_30649,plain,
% 11.52/2.01      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 11.52/2.01      | sK2 = k1_relat_1(k1_xboole_0)
% 11.52/2.01      | sK2 != k1_xboole_0 ),
% 11.52/2.01      inference(instantiation,[status(thm)],[c_30648]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_6,plain,
% 11.52/2.01      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 11.52/2.01      inference(cnf_transformation,[],[f68]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_27917,plain,
% 11.52/2.01      ( k2_zfmisc_1(k2_relset_1(sK1,sK2,sK3),k1_xboole_0) = k1_xboole_0 ),
% 11.52/2.01      inference(instantiation,[status(thm)],[c_6]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_1,plain,
% 11.52/2.01      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 11.52/2.01      inference(cnf_transformation,[],[f40]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_999,plain,
% 11.52/2.01      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 11.52/2.01      | r1_tarski(X0,X1) = iProver_top ),
% 11.52/2.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_22,negated_conjecture,
% 11.52/2.01      ( ~ r2_hidden(X0,sK2) | k1_funct_1(sK3,sK4(X0)) = X0 ),
% 11.52/2.01      inference(cnf_transformation,[],[f64]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_989,plain,
% 11.52/2.01      ( k1_funct_1(sK3,sK4(X0)) = X0 | r2_hidden(X0,sK2) != iProver_top ),
% 11.52/2.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_1958,plain,
% 11.52/2.01      ( k1_funct_1(sK3,sK4(sK0(sK2,X0))) = sK0(sK2,X0)
% 11.52/2.01      | r1_tarski(sK2,X0) = iProver_top ),
% 11.52/2.01      inference(superposition,[status(thm)],[c_999,c_989]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_24,negated_conjecture,
% 11.52/2.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 11.52/2.01      inference(cnf_transformation,[],[f62]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_987,plain,
% 11.52/2.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 11.52/2.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_19,plain,
% 11.52/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.52/2.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 11.52/2.01      inference(cnf_transformation,[],[f58]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_990,plain,
% 11.52/2.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 11.52/2.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.52/2.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_2062,plain,
% 11.52/2.01      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 11.52/2.01      inference(superposition,[status(thm)],[c_987,c_990]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_18,plain,
% 11.52/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.52/2.01      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 11.52/2.01      inference(cnf_transformation,[],[f57]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_991,plain,
% 11.52/2.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.52/2.01      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 11.52/2.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_2117,plain,
% 11.52/2.01      ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top
% 11.52/2.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 11.52/2.01      inference(superposition,[status(thm)],[c_2062,c_991]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_29,plain,
% 11.52/2.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 11.52/2.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_2405,plain,
% 11.52/2.01      ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top ),
% 11.52/2.01      inference(global_propositional_subsumption,
% 11.52/2.01                [status(thm)],
% 11.52/2.01                [c_2117,c_29]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_10,plain,
% 11.52/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.52/2.01      inference(cnf_transformation,[],[f48]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_994,plain,
% 11.52/2.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.52/2.01      | r1_tarski(X0,X1) = iProver_top ),
% 11.52/2.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_2410,plain,
% 11.52/2.01      ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
% 11.52/2.01      inference(superposition,[status(thm)],[c_2405,c_994]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_3,plain,
% 11.52/2.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 11.52/2.01      inference(cnf_transformation,[],[f44]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_997,plain,
% 11.52/2.01      ( X0 = X1
% 11.52/2.01      | r1_tarski(X0,X1) != iProver_top
% 11.52/2.01      | r1_tarski(X1,X0) != iProver_top ),
% 11.52/2.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_2917,plain,
% 11.52/2.01      ( k2_relat_1(sK3) = sK2
% 11.52/2.01      | r1_tarski(sK2,k2_relat_1(sK3)) != iProver_top ),
% 11.52/2.01      inference(superposition,[status(thm)],[c_2410,c_997]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_21,negated_conjecture,
% 11.52/2.01      ( k2_relset_1(sK1,sK2,sK3) != sK2 ),
% 11.52/2.01      inference(cnf_transformation,[],[f65]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_2096,plain,
% 11.52/2.01      ( k2_relat_1(sK3) != sK2 ),
% 11.52/2.01      inference(demodulation,[status(thm)],[c_2062,c_21]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_20172,plain,
% 11.52/2.01      ( r1_tarski(sK2,k2_relat_1(sK3)) != iProver_top ),
% 11.52/2.01      inference(global_propositional_subsumption,
% 11.52/2.01                [status(thm)],
% 11.52/2.01                [c_2917,c_2096]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_20178,plain,
% 11.52/2.01      ( k1_funct_1(sK3,sK4(sK0(sK2,k2_relat_1(sK3)))) = sK0(sK2,k2_relat_1(sK3)) ),
% 11.52/2.01      inference(superposition,[status(thm)],[c_1958,c_20172]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_20,plain,
% 11.52/2.01      ( ~ v1_funct_2(X0,X1,X2)
% 11.52/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.52/2.01      | ~ r2_hidden(X3,X1)
% 11.52/2.01      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 11.52/2.01      | ~ v1_funct_1(X0)
% 11.52/2.01      | k1_xboole_0 = X2 ),
% 11.52/2.01      inference(cnf_transformation,[],[f59]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_25,negated_conjecture,
% 11.52/2.01      ( v1_funct_2(sK3,sK1,sK2) ),
% 11.52/2.01      inference(cnf_transformation,[],[f61]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_320,plain,
% 11.52/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.52/2.01      | ~ r2_hidden(X3,X1)
% 11.52/2.01      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 11.52/2.01      | ~ v1_funct_1(X0)
% 11.52/2.01      | sK3 != X0
% 11.52/2.01      | sK2 != X2
% 11.52/2.01      | sK1 != X1
% 11.52/2.01      | k1_xboole_0 = X2 ),
% 11.52/2.01      inference(resolution_lifted,[status(thm)],[c_20,c_25]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_321,plain,
% 11.52/2.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 11.52/2.01      | ~ r2_hidden(X0,sK1)
% 11.52/2.01      | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK1,sK2,sK3))
% 11.52/2.01      | ~ v1_funct_1(sK3)
% 11.52/2.01      | k1_xboole_0 = sK2 ),
% 11.52/2.01      inference(unflattening,[status(thm)],[c_320]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_26,negated_conjecture,
% 11.52/2.01      ( v1_funct_1(sK3) ),
% 11.52/2.01      inference(cnf_transformation,[],[f60]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_325,plain,
% 11.52/2.01      ( r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK1,sK2,sK3))
% 11.52/2.01      | ~ r2_hidden(X0,sK1)
% 11.52/2.01      | k1_xboole_0 = sK2 ),
% 11.52/2.01      inference(global_propositional_subsumption,
% 11.52/2.01                [status(thm)],
% 11.52/2.01                [c_321,c_26,c_24]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_326,plain,
% 11.52/2.01      ( ~ r2_hidden(X0,sK1)
% 11.52/2.01      | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK1,sK2,sK3))
% 11.52/2.01      | k1_xboole_0 = sK2 ),
% 11.52/2.01      inference(renaming,[status(thm)],[c_325]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_986,plain,
% 11.52/2.01      ( k1_xboole_0 = sK2
% 11.52/2.01      | r2_hidden(X0,sK1) != iProver_top
% 11.52/2.01      | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK1,sK2,sK3)) = iProver_top ),
% 11.52/2.01      inference(predicate_to_equality,[status(thm)],[c_326]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_2095,plain,
% 11.52/2.01      ( sK2 = k1_xboole_0
% 11.52/2.01      | r2_hidden(X0,sK1) != iProver_top
% 11.52/2.01      | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) = iProver_top ),
% 11.52/2.01      inference(demodulation,[status(thm)],[c_2062,c_986]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_20947,plain,
% 11.52/2.01      ( sK2 = k1_xboole_0
% 11.52/2.01      | r2_hidden(sK0(sK2,k2_relat_1(sK3)),k2_relat_1(sK3)) = iProver_top
% 11.52/2.01      | r2_hidden(sK4(sK0(sK2,k2_relat_1(sK3))),sK1) != iProver_top ),
% 11.52/2.01      inference(superposition,[status(thm)],[c_20178,c_2095]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_23,negated_conjecture,
% 11.52/2.01      ( ~ r2_hidden(X0,sK2) | r2_hidden(sK4(X0),sK1) ),
% 11.52/2.01      inference(cnf_transformation,[],[f63]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_7642,plain,
% 11.52/2.01      ( ~ r2_hidden(sK0(sK2,X0),sK2) | r2_hidden(sK4(sK0(sK2,X0)),sK1) ),
% 11.52/2.01      inference(instantiation,[status(thm)],[c_23]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_17409,plain,
% 11.52/2.01      ( ~ r2_hidden(sK0(sK2,k2_relat_1(sK3)),sK2)
% 11.52/2.01      | r2_hidden(sK4(sK0(sK2,k2_relat_1(sK3))),sK1) ),
% 11.52/2.01      inference(instantiation,[status(thm)],[c_7642]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_17410,plain,
% 11.52/2.01      ( r2_hidden(sK0(sK2,k2_relat_1(sK3)),sK2) != iProver_top
% 11.52/2.01      | r2_hidden(sK4(sK0(sK2,k2_relat_1(sK3))),sK1) = iProver_top ),
% 11.52/2.01      inference(predicate_to_equality,[status(thm)],[c_17409]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_553,plain,
% 11.52/2.01      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 11.52/2.01      theory(equality) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_10731,plain,
% 11.52/2.01      ( k2_zfmisc_1(k2_relset_1(sK1,sK2,sK3),X0) != X1
% 11.52/2.01      | k1_zfmisc_1(k2_zfmisc_1(k2_relset_1(sK1,sK2,sK3),X0)) = k1_zfmisc_1(X1) ),
% 11.52/2.01      inference(instantiation,[status(thm)],[c_553]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_10732,plain,
% 11.52/2.01      ( k2_zfmisc_1(k2_relset_1(sK1,sK2,sK3),k1_xboole_0) != k1_xboole_0
% 11.52/2.01      | k1_zfmisc_1(k2_zfmisc_1(k2_relset_1(sK1,sK2,sK3),k1_xboole_0)) = k1_zfmisc_1(k1_xboole_0) ),
% 11.52/2.01      inference(instantiation,[status(thm)],[c_10731]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_3876,plain,
% 11.52/2.01      ( r2_hidden(sK0(X0,k2_relat_1(sK3)),X0)
% 11.52/2.01      | r1_tarski(X0,k2_relat_1(sK3)) ),
% 11.52/2.01      inference(instantiation,[status(thm)],[c_1]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_8976,plain,
% 11.52/2.01      ( r2_hidden(sK0(sK2,k2_relat_1(sK3)),sK2)
% 11.52/2.01      | r1_tarski(sK2,k2_relat_1(sK3)) ),
% 11.52/2.01      inference(instantiation,[status(thm)],[c_3876]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_8977,plain,
% 11.52/2.01      ( r2_hidden(sK0(sK2,k2_relat_1(sK3)),sK2) = iProver_top
% 11.52/2.01      | r1_tarski(sK2,k2_relat_1(sK3)) = iProver_top ),
% 11.52/2.01      inference(predicate_to_equality,[status(thm)],[c_8976]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_0,plain,
% 11.52/2.01      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 11.52/2.01      inference(cnf_transformation,[],[f41]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_3877,plain,
% 11.52/2.01      ( ~ r2_hidden(sK0(X0,k2_relat_1(sK3)),k2_relat_1(sK3))
% 11.52/2.01      | r1_tarski(X0,k2_relat_1(sK3)) ),
% 11.52/2.01      inference(instantiation,[status(thm)],[c_0]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_8144,plain,
% 11.52/2.01      ( ~ r2_hidden(sK0(sK2,k2_relat_1(sK3)),k2_relat_1(sK3))
% 11.52/2.01      | r1_tarski(sK2,k2_relat_1(sK3)) ),
% 11.52/2.01      inference(instantiation,[status(thm)],[c_3877]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_8147,plain,
% 11.52/2.01      ( r2_hidden(sK0(sK2,k2_relat_1(sK3)),k2_relat_1(sK3)) != iProver_top
% 11.52/2.01      | r1_tarski(sK2,k2_relat_1(sK3)) = iProver_top ),
% 11.52/2.01      inference(predicate_to_equality,[status(thm)],[c_8144]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_554,plain,
% 11.52/2.01      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.52/2.01      theory(equality) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_1158,plain,
% 11.52/2.01      ( m1_subset_1(X0,X1)
% 11.52/2.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 11.52/2.01      | X0 != X2
% 11.52/2.01      | X1 != k1_zfmisc_1(X3) ),
% 11.52/2.01      inference(instantiation,[status(thm)],[c_554]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_1247,plain,
% 11.52/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.52/2.01      | m1_subset_1(X2,k1_zfmisc_1(X3))
% 11.52/2.01      | X2 != X0
% 11.52/2.01      | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
% 11.52/2.01      inference(instantiation,[status(thm)],[c_1158]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_2301,plain,
% 11.52/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.52/2.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_relset_1(sK1,sK2,sK3),X3)))
% 11.52/2.01      | X2 != X0
% 11.52/2.01      | k1_zfmisc_1(k2_zfmisc_1(k2_relset_1(sK1,sK2,sK3),X3)) != k1_zfmisc_1(X1) ),
% 11.52/2.01      inference(instantiation,[status(thm)],[c_1247]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_2303,plain,
% 11.52/2.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_relset_1(sK1,sK2,sK3),k1_xboole_0)))
% 11.52/2.01      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 11.52/2.01      | k1_zfmisc_1(k2_zfmisc_1(k2_relset_1(sK1,sK2,sK3),k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
% 11.52/2.01      | k1_xboole_0 != k1_xboole_0 ),
% 11.52/2.01      inference(instantiation,[status(thm)],[c_2301]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_17,plain,
% 11.52/2.01      ( v4_relat_1(X0,X1)
% 11.52/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 11.52/2.01      inference(cnf_transformation,[],[f56]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_12,plain,
% 11.52/2.01      ( ~ v4_relat_1(X0,X1)
% 11.52/2.01      | r1_tarski(k1_relat_1(X0),X1)
% 11.52/2.01      | ~ v1_relat_1(X0) ),
% 11.52/2.01      inference(cnf_transformation,[],[f50]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_345,plain,
% 11.52/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.52/2.01      | r1_tarski(k1_relat_1(X0),X1)
% 11.52/2.01      | ~ v1_relat_1(X0) ),
% 11.52/2.01      inference(resolution,[status(thm)],[c_17,c_12]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_1580,plain,
% 11.52/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_relset_1(sK1,sK2,sK3),X1)))
% 11.52/2.01      | r1_tarski(k1_relat_1(X0),k2_relset_1(sK1,sK2,sK3))
% 11.52/2.01      | ~ v1_relat_1(X0) ),
% 11.52/2.01      inference(instantiation,[status(thm)],[c_345]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_1586,plain,
% 11.52/2.01      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_relset_1(sK1,sK2,sK3),k1_xboole_0)))
% 11.52/2.01      | r1_tarski(k1_relat_1(k1_xboole_0),k2_relset_1(sK1,sK2,sK3))
% 11.52/2.01      | ~ v1_relat_1(k1_xboole_0) ),
% 11.52/2.01      inference(instantiation,[status(thm)],[c_1580]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_550,plain,
% 11.52/2.01      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 11.52/2.01      theory(equality) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_1273,plain,
% 11.52/2.01      ( ~ r1_tarski(X0,k2_relset_1(sK1,sK2,sK3))
% 11.52/2.01      | r1_tarski(sK2,k2_relset_1(sK1,sK2,sK3))
% 11.52/2.01      | sK2 != X0 ),
% 11.52/2.01      inference(instantiation,[status(thm)],[c_550]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_1579,plain,
% 11.52/2.01      ( ~ r1_tarski(k1_relat_1(X0),k2_relset_1(sK1,sK2,sK3))
% 11.52/2.01      | r1_tarski(sK2,k2_relset_1(sK1,sK2,sK3))
% 11.52/2.01      | sK2 != k1_relat_1(X0) ),
% 11.52/2.01      inference(instantiation,[status(thm)],[c_1273]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_1582,plain,
% 11.52/2.01      ( ~ r1_tarski(k1_relat_1(k1_xboole_0),k2_relset_1(sK1,sK2,sK3))
% 11.52/2.01      | r1_tarski(sK2,k2_relset_1(sK1,sK2,sK3))
% 11.52/2.01      | sK2 != k1_relat_1(k1_xboole_0) ),
% 11.52/2.01      inference(instantiation,[status(thm)],[c_1579]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_1196,plain,
% 11.52/2.01      ( X0 != X1 | X0 = k2_zfmisc_1(X2,X3) | k2_zfmisc_1(X2,X3) != X1 ),
% 11.52/2.01      inference(instantiation,[status(thm)],[c_549]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_1197,plain,
% 11.52/2.01      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 11.52/2.01      | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 11.52/2.01      | k1_xboole_0 != k1_xboole_0 ),
% 11.52/2.01      inference(instantiation,[status(thm)],[c_1196]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_1166,plain,
% 11.52/2.01      ( ~ m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK2))
% 11.52/2.01      | r1_tarski(k2_relset_1(sK1,sK2,sK3),sK2) ),
% 11.52/2.01      inference(instantiation,[status(thm)],[c_10]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_1146,plain,
% 11.52/2.01      ( m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK2))
% 11.52/2.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 11.52/2.01      inference(instantiation,[status(thm)],[c_18]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_1133,plain,
% 11.52/2.01      ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),sK2)
% 11.52/2.01      | ~ r1_tarski(sK2,k2_relset_1(sK1,sK2,sK3))
% 11.52/2.01      | k2_relset_1(sK1,sK2,sK3) = sK2 ),
% 11.52/2.01      inference(instantiation,[status(thm)],[c_3]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_556,plain,
% 11.52/2.01      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 11.52/2.01      theory(equality) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_1122,plain,
% 11.52/2.01      ( v1_relat_1(X0)
% 11.52/2.01      | ~ v1_relat_1(k2_zfmisc_1(X1,X2))
% 11.52/2.01      | X0 != k2_zfmisc_1(X1,X2) ),
% 11.52/2.01      inference(instantiation,[status(thm)],[c_556]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_1124,plain,
% 11.52/2.01      ( ~ v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 11.52/2.01      | v1_relat_1(k1_xboole_0)
% 11.52/2.01      | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
% 11.52/2.01      inference(instantiation,[status(thm)],[c_1122]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_5,plain,
% 11.52/2.01      ( r1_tarski(X0,X0) ),
% 11.52/2.01      inference(cnf_transformation,[],[f67]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_69,plain,
% 11.52/2.01      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 11.52/2.01      inference(instantiation,[status(thm)],[c_5]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_7,plain,
% 11.52/2.01      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.52/2.01      inference(cnf_transformation,[],[f69]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_67,plain,
% 11.52/2.01      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 11.52/2.01      inference(instantiation,[status(thm)],[c_7]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_8,plain,
% 11.52/2.01      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 11.52/2.01      | k1_xboole_0 = X1
% 11.52/2.01      | k1_xboole_0 = X0 ),
% 11.52/2.01      inference(cnf_transformation,[],[f45]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_66,plain,
% 11.52/2.01      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 11.52/2.01      | k1_xboole_0 = k1_xboole_0 ),
% 11.52/2.01      inference(instantiation,[status(thm)],[c_8]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_9,plain,
% 11.52/2.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.52/2.01      inference(cnf_transformation,[],[f49]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_64,plain,
% 11.52/2.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 11.52/2.01      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 11.52/2.01      inference(instantiation,[status(thm)],[c_9]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_13,plain,
% 11.52/2.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 11.52/2.01      inference(cnf_transformation,[],[f52]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_52,plain,
% 11.52/2.01      ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
% 11.52/2.01      inference(instantiation,[status(thm)],[c_13]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(c_15,plain,
% 11.52/2.01      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 11.52/2.01      inference(cnf_transformation,[],[f53]) ).
% 11.52/2.01  
% 11.52/2.01  cnf(contradiction,plain,
% 11.52/2.01      ( $false ),
% 11.52/2.01      inference(minisat,
% 11.52/2.01                [status(thm)],
% 11.52/2.01                [c_30649,c_27917,c_20947,c_17410,c_10732,c_8977,c_8147,
% 11.52/2.01                 c_2917,c_2303,c_2096,c_1586,c_1582,c_1197,c_1166,c_1146,
% 11.52/2.01                 c_1133,c_1124,c_69,c_67,c_66,c_64,c_52,c_15,c_21,c_24]) ).
% 11.52/2.01  
% 11.52/2.01  
% 11.52/2.01  % SZS output end CNFRefutation for theBenchmark.p
% 11.52/2.01  
% 11.52/2.01  ------                               Statistics
% 11.52/2.01  
% 11.52/2.01  ------ General
% 11.52/2.01  
% 11.52/2.01  abstr_ref_over_cycles:                  0
% 11.52/2.01  abstr_ref_under_cycles:                 0
% 11.52/2.01  gc_basic_clause_elim:                   0
% 11.52/2.01  forced_gc_time:                         0
% 11.52/2.01  parsing_time:                           0.006
% 11.52/2.01  unif_index_cands_time:                  0.
% 11.52/2.01  unif_index_add_time:                    0.
% 11.52/2.01  orderings_time:                         0.
% 11.52/2.01  out_proof_time:                         0.019
% 11.52/2.01  total_time:                             1.037
% 11.52/2.01  num_of_symbols:                         50
% 11.52/2.01  num_of_terms:                           28490
% 11.52/2.01  
% 11.52/2.01  ------ Preprocessing
% 11.52/2.01  
% 11.52/2.01  num_of_splits:                          0
% 11.52/2.01  num_of_split_atoms:                     0
% 11.52/2.01  num_of_reused_defs:                     0
% 11.52/2.01  num_eq_ax_congr_red:                    14
% 11.52/2.01  num_of_sem_filtered_clauses:            1
% 11.52/2.01  num_of_subtypes:                        0
% 11.52/2.01  monotx_restored_types:                  0
% 11.52/2.01  sat_num_of_epr_types:                   0
% 11.52/2.01  sat_num_of_non_cyclic_types:            0
% 11.52/2.01  sat_guarded_non_collapsed_types:        0
% 11.52/2.01  num_pure_diseq_elim:                    0
% 11.52/2.01  simp_replaced_by:                       0
% 11.52/2.01  res_preprocessed:                       117
% 11.52/2.01  prep_upred:                             0
% 11.52/2.01  prep_unflattend:                        7
% 11.52/2.01  smt_new_axioms:                         0
% 11.52/2.01  pred_elim_cands:                        4
% 11.52/2.01  pred_elim:                              3
% 11.52/2.01  pred_elim_cl:                           4
% 11.52/2.01  pred_elim_cycles:                       6
% 11.52/2.01  merged_defs:                            8
% 11.52/2.01  merged_defs_ncl:                        0
% 11.52/2.01  bin_hyper_res:                          8
% 11.52/2.01  prep_cycles:                            4
% 11.52/2.01  pred_elim_time:                         0.002
% 11.52/2.01  splitting_time:                         0.
% 11.52/2.01  sem_filter_time:                        0.
% 11.52/2.01  monotx_time:                            0.
% 11.52/2.01  subtype_inf_time:                       0.
% 11.52/2.01  
% 11.52/2.01  ------ Problem properties
% 11.52/2.01  
% 11.52/2.01  clauses:                                22
% 11.52/2.01  conjectures:                            4
% 11.52/2.01  epr:                                    4
% 11.52/2.01  horn:                                   19
% 11.52/2.01  ground:                                 4
% 11.52/2.01  unary:                                  8
% 11.52/2.01  binary:                                 9
% 11.52/2.01  lits:                                   41
% 11.52/2.01  lits_eq:                                12
% 11.52/2.01  fd_pure:                                0
% 11.52/2.01  fd_pseudo:                              0
% 11.52/2.01  fd_cond:                                1
% 11.52/2.01  fd_pseudo_cond:                         1
% 11.52/2.01  ac_symbols:                             0
% 11.52/2.01  
% 11.52/2.01  ------ Propositional Solver
% 11.52/2.01  
% 11.52/2.01  prop_solver_calls:                      32
% 11.52/2.01  prop_fast_solver_calls:                 1245
% 11.52/2.01  smt_solver_calls:                       0
% 11.52/2.01  smt_fast_solver_calls:                  0
% 11.52/2.01  prop_num_of_clauses:                    10602
% 11.52/2.01  prop_preprocess_simplified:             20318
% 11.52/2.01  prop_fo_subsumed:                       6
% 11.52/2.01  prop_solver_time:                       0.
% 11.52/2.01  smt_solver_time:                        0.
% 11.52/2.01  smt_fast_solver_time:                   0.
% 11.52/2.01  prop_fast_solver_time:                  0.
% 11.52/2.01  prop_unsat_core_time:                   0.001
% 11.52/2.01  
% 11.52/2.01  ------ QBF
% 11.52/2.01  
% 11.52/2.01  qbf_q_res:                              0
% 11.52/2.01  qbf_num_tautologies:                    0
% 11.52/2.01  qbf_prep_cycles:                        0
% 11.52/2.01  
% 11.52/2.01  ------ BMC1
% 11.52/2.01  
% 11.52/2.01  bmc1_current_bound:                     -1
% 11.52/2.01  bmc1_last_solved_bound:                 -1
% 11.52/2.01  bmc1_unsat_core_size:                   -1
% 11.52/2.01  bmc1_unsat_core_parents_size:           -1
% 11.52/2.01  bmc1_merge_next_fun:                    0
% 11.52/2.01  bmc1_unsat_core_clauses_time:           0.
% 11.52/2.01  
% 11.52/2.01  ------ Instantiation
% 11.52/2.01  
% 11.52/2.01  inst_num_of_clauses:                    2581
% 11.52/2.01  inst_num_in_passive:                    1529
% 11.52/2.01  inst_num_in_active:                     1010
% 11.52/2.01  inst_num_in_unprocessed:                42
% 11.52/2.01  inst_num_of_loops:                      1433
% 11.52/2.01  inst_num_of_learning_restarts:          0
% 11.52/2.01  inst_num_moves_active_passive:          417
% 11.52/2.01  inst_lit_activity:                      0
% 11.52/2.01  inst_lit_activity_moves:                0
% 11.52/2.01  inst_num_tautologies:                   0
% 11.52/2.01  inst_num_prop_implied:                  0
% 11.52/2.01  inst_num_existing_simplified:           0
% 11.52/2.01  inst_num_eq_res_simplified:             0
% 11.52/2.01  inst_num_child_elim:                    0
% 11.52/2.01  inst_num_of_dismatching_blockings:      1627
% 11.52/2.01  inst_num_of_non_proper_insts:           3078
% 11.52/2.01  inst_num_of_duplicates:                 0
% 11.52/2.01  inst_inst_num_from_inst_to_res:         0
% 11.52/2.01  inst_dismatching_checking_time:         0.
% 11.52/2.01  
% 11.52/2.01  ------ Resolution
% 11.52/2.01  
% 11.52/2.01  res_num_of_clauses:                     0
% 11.52/2.01  res_num_in_passive:                     0
% 11.52/2.01  res_num_in_active:                      0
% 11.52/2.01  res_num_of_loops:                       121
% 11.52/2.01  res_forward_subset_subsumed:            210
% 11.52/2.01  res_backward_subset_subsumed:           8
% 11.52/2.01  res_forward_subsumed:                   0
% 11.52/2.01  res_backward_subsumed:                  0
% 11.52/2.01  res_forward_subsumption_resolution:     0
% 11.52/2.01  res_backward_subsumption_resolution:    0
% 11.52/2.01  res_clause_to_clause_subsumption:       24714
% 11.52/2.01  res_orphan_elimination:                 0
% 11.52/2.01  res_tautology_del:                      290
% 11.52/2.01  res_num_eq_res_simplified:              0
% 11.52/2.01  res_num_sel_changes:                    0
% 11.52/2.01  res_moves_from_active_to_pass:          0
% 11.52/2.01  
% 11.52/2.01  ------ Superposition
% 11.52/2.01  
% 11.52/2.01  sup_time_total:                         0.
% 11.52/2.01  sup_time_generating:                    0.
% 11.52/2.01  sup_time_sim_full:                      0.
% 11.52/2.01  sup_time_sim_immed:                     0.
% 11.52/2.01  
% 11.52/2.01  sup_num_of_clauses:                     861
% 11.52/2.01  sup_num_in_active:                      283
% 11.52/2.01  sup_num_in_passive:                     578
% 11.52/2.01  sup_num_of_loops:                       286
% 11.52/2.01  sup_fw_superposition:                   744
% 11.52/2.01  sup_bw_superposition:                   226
% 11.52/2.01  sup_immediate_simplified:               172
% 11.52/2.01  sup_given_eliminated:                   0
% 11.52/2.01  comparisons_done:                       0
% 11.52/2.01  comparisons_avoided:                    8
% 11.52/2.01  
% 11.52/2.01  ------ Simplifications
% 11.52/2.01  
% 11.52/2.01  
% 11.52/2.01  sim_fw_subset_subsumed:                 2
% 11.52/2.01  sim_bw_subset_subsumed:                 4
% 11.52/2.01  sim_fw_subsumed:                        10
% 11.52/2.01  sim_bw_subsumed:                        0
% 11.52/2.01  sim_fw_subsumption_res:                 0
% 11.52/2.01  sim_bw_subsumption_res:                 0
% 11.52/2.01  sim_tautology_del:                      4
% 11.52/2.01  sim_eq_tautology_del:                   73
% 11.52/2.01  sim_eq_res_simp:                        0
% 11.52/2.01  sim_fw_demodulated:                     149
% 11.52/2.01  sim_bw_demodulated:                     4
% 11.52/2.01  sim_light_normalised:                   14
% 11.52/2.01  sim_joinable_taut:                      0
% 11.52/2.01  sim_joinable_simp:                      0
% 11.52/2.01  sim_ac_normalised:                      0
% 11.52/2.01  sim_smt_subsumption:                    0
% 11.52/2.01  
%------------------------------------------------------------------------------
