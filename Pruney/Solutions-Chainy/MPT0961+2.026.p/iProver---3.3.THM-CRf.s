%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:59 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :  144 (1881 expanded)
%              Number of clauses        :   94 ( 802 expanded)
%              Number of leaves         :   18 ( 363 expanded)
%              Depth                    :   28
%              Number of atoms          :  422 (5696 expanded)
%              Number of equality atoms :  221 (1682 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          & v1_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f22,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f31,plain,
    ( ? [X0] :
        ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          | ~ v1_funct_1(X0) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
        | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
        | ~ v1_funct_1(sK2) )
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
      | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
      | ~ v1_funct_1(sK2) )
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f31])).

fof(f51,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

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

fof(f20,plain,(
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
    inference(flattening,[],[f20])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f53,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f33,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f28])).

fof(f42,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f50])).

fof(f55,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f54])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f57,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f48])).

cnf(c_4,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_696,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_702,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_696,c_3])).

cnf(c_5,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_695,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1019,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_702,c_695])).

cnf(c_8,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ r1_tarski(k1_relat_1(X0),X2)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_232,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ r1_tarski(k1_relat_1(X0),X2)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_20])).

cnf(c_233,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),X0)
    | ~ r1_tarski(k1_relat_1(sK2),X1)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ),
    inference(unflattening,[status(thm)],[c_232])).

cnf(c_692,plain,
    ( r1_tarski(k2_relat_1(sK2),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK2),X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_233])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_694,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1122,plain,
    ( r1_tarski(k2_relat_1(sK2),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK2),X1) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_692,c_694])).

cnf(c_1249,plain,
    ( r1_tarski(k1_relat_1(sK2),X0) != iProver_top
    | v1_xboole_0(k2_relat_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1019,c_1122])).

cnf(c_15,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_18,negated_conjecture,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_111,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_19])).

cnf(c_112,negated_conjecture,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    inference(renaming,[status(thm)],[c_111])).

cnf(c_375,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k1_relset_1(X1,X2,X0) != X1
    | k2_relat_1(sK2) != X2
    | k1_relat_1(sK2) != X1
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_112])).

cnf(c_376,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k1_relat_1(sK2)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_375])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_384,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_376,c_7])).

cnf(c_688,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_384])).

cnf(c_817,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_692,c_688])).

cnf(c_1144,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1019,c_817])).

cnf(c_1289,plain,
    ( k2_relat_1(sK2) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1144,c_1019])).

cnf(c_1505,plain,
    ( r1_tarski(k1_relat_1(sK2),X0) != iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1249,c_1289])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_697,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1509,plain,
    ( r1_tarski(k1_relat_1(sK2),X0) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1505,c_697])).

cnf(c_1513,plain,
    ( v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1019,c_1509])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_11,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_297,plain,
    ( ~ v1_xboole_0(X0)
    | X1 != X0
    | sK1(X1) != X2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_11])).

cnf(c_298,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_297])).

cnf(c_691,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_298])).

cnf(c_1847,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1513,c_691])).

cnf(c_12,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_332,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k2_relat_1(sK2) != k1_xboole_0
    | k1_relat_1(sK2) != X0
    | sK2 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_112])).

cnf(c_333,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)))
    | k2_relat_1(sK2) != k1_xboole_0
    | sK2 != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_332])).

cnf(c_690,plain,
    ( k2_relat_1(sK2) != k1_xboole_0
    | sK2 != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_333])).

cnf(c_1294,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | sK2 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1289,c_690])).

cnf(c_1311,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1294])).

cnf(c_480,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_806,plain,
    ( sK2 != X0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_480])).

cnf(c_841,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_806])).

cnf(c_479,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_842,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_479])).

cnf(c_903,plain,
    ( ~ v1_xboole_0(sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_298])).

cnf(c_904,plain,
    ( k1_xboole_0 = sK2
    | v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_903])).

cnf(c_1720,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1311,c_841,c_842,c_904,c_1513])).

cnf(c_1860,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1847,c_1720])).

cnf(c_14,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_359,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_relat_1(sK2) != X1
    | k1_relat_1(sK2) != k1_xboole_0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_112])).

cnf(c_360,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2))))
    | k1_relset_1(k1_xboole_0,k2_relat_1(sK2),sK2) != k1_xboole_0
    | k1_relat_1(sK2) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_359])).

cnf(c_689,plain,
    ( k1_relset_1(k1_xboole_0,k2_relat_1(sK2),sK2) != k1_xboole_0
    | k1_relat_1(sK2) != k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_360])).

cnf(c_1295,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) != k1_xboole_0
    | k1_relat_1(sK2) != k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1289,c_689])).

cnf(c_1867,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1847,c_1295])).

cnf(c_1907,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1860,c_1867])).

cnf(c_59,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_61,plain,
    ( m1_subset_1(k2_subset_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_59])).

cnf(c_62,plain,
    ( k2_subset_1(k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_63,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_300,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_298])).

cnf(c_1065,plain,
    ( X0 != X1
    | X0 = k2_subset_1(X2)
    | k2_subset_1(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_480])).

cnf(c_1066,plain,
    ( k2_subset_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k2_subset_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1065])).

cnf(c_483,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_834,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k2_subset_1(X2),k1_zfmisc_1(X2))
    | X1 != k1_zfmisc_1(X2)
    | X0 != k2_subset_1(X2) ),
    inference(instantiation,[status(thm)],[c_483])).

cnf(c_892,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_subset_1(X2),k1_zfmisc_1(X2))
    | X0 != k2_subset_1(X2)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X2) ),
    inference(instantiation,[status(thm)],[c_834])).

cnf(c_1083,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_subset_1(X3),k1_zfmisc_1(X3))
    | X0 != k2_subset_1(X3)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_892])).

cnf(c_1084,plain,
    ( X0 != k2_subset_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(X1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top
    | m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1083])).

cnf(c_1086,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 != k2_subset_1(k1_xboole_0)
    | m1_subset_1(k2_subset_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1084])).

cnf(c_482,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_1520,plain,
    ( k2_zfmisc_1(X0,X1) != X2
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(X2) ),
    inference(instantiation,[status(thm)],[c_482])).

cnf(c_1521,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = k1_zfmisc_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1520])).

cnf(c_1123,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_702,c_694])).

cnf(c_1848,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1123,c_691])).

cnf(c_1856,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1848])).

cnf(c_2009,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_697,c_1848])).

cnf(c_2304,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1860,c_2009])).

cnf(c_2307,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2304,c_702])).

cnf(c_693,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1002,plain,
    ( k1_relset_1(X0,X1,k2_zfmisc_1(X0,X1)) = k1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(superposition,[status(thm)],[c_702,c_693])).

cnf(c_2082,plain,
    ( k1_relat_1(k2_zfmisc_1(X0,k1_xboole_0)) = k1_relset_1(X0,k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2009,c_1002])).

cnf(c_2089,plain,
    ( k1_relset_1(X0,k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_2082,c_2009])).

cnf(c_2308,plain,
    ( k1_relset_1(X0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2307,c_2089])).

cnf(c_2318,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2308])).

cnf(c_2516,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1907,c_61,c_62,c_2,c_63,c_300,c_1066,c_1086,c_1521,c_1856,c_2318])).

cnf(c_2520,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2516,c_2307])).

cnf(c_2521,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2520,c_2009])).

cnf(c_2523,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2521,c_702])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:01:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.10/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.00  
% 2.10/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.10/1.00  
% 2.10/1.00  ------  iProver source info
% 2.10/1.00  
% 2.10/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.10/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.10/1.00  git: non_committed_changes: false
% 2.10/1.00  git: last_make_outside_of_git: false
% 2.10/1.00  
% 2.10/1.00  ------ 
% 2.10/1.00  
% 2.10/1.00  ------ Input Options
% 2.10/1.00  
% 2.10/1.00  --out_options                           all
% 2.10/1.00  --tptp_safe_out                         true
% 2.10/1.00  --problem_path                          ""
% 2.10/1.00  --include_path                          ""
% 2.10/1.00  --clausifier                            res/vclausify_rel
% 2.10/1.00  --clausifier_options                    --mode clausify
% 2.10/1.00  --stdin                                 false
% 2.10/1.00  --stats_out                             all
% 2.10/1.00  
% 2.10/1.00  ------ General Options
% 2.10/1.00  
% 2.10/1.00  --fof                                   false
% 2.10/1.00  --time_out_real                         305.
% 2.10/1.00  --time_out_virtual                      -1.
% 2.10/1.00  --symbol_type_check                     false
% 2.10/1.00  --clausify_out                          false
% 2.10/1.00  --sig_cnt_out                           false
% 2.10/1.00  --trig_cnt_out                          false
% 2.10/1.00  --trig_cnt_out_tolerance                1.
% 2.10/1.00  --trig_cnt_out_sk_spl                   false
% 2.10/1.00  --abstr_cl_out                          false
% 2.10/1.00  
% 2.10/1.00  ------ Global Options
% 2.10/1.00  
% 2.10/1.00  --schedule                              default
% 2.10/1.00  --add_important_lit                     false
% 2.10/1.00  --prop_solver_per_cl                    1000
% 2.10/1.00  --min_unsat_core                        false
% 2.10/1.00  --soft_assumptions                      false
% 2.10/1.00  --soft_lemma_size                       3
% 2.10/1.00  --prop_impl_unit_size                   0
% 2.10/1.00  --prop_impl_unit                        []
% 2.10/1.00  --share_sel_clauses                     true
% 2.10/1.00  --reset_solvers                         false
% 2.10/1.00  --bc_imp_inh                            [conj_cone]
% 2.10/1.00  --conj_cone_tolerance                   3.
% 2.10/1.00  --extra_neg_conj                        none
% 2.10/1.00  --large_theory_mode                     true
% 2.10/1.00  --prolific_symb_bound                   200
% 2.10/1.00  --lt_threshold                          2000
% 2.10/1.00  --clause_weak_htbl                      true
% 2.10/1.00  --gc_record_bc_elim                     false
% 2.10/1.00  
% 2.10/1.00  ------ Preprocessing Options
% 2.10/1.00  
% 2.10/1.00  --preprocessing_flag                    true
% 2.10/1.00  --time_out_prep_mult                    0.1
% 2.10/1.00  --splitting_mode                        input
% 2.10/1.00  --splitting_grd                         true
% 2.10/1.00  --splitting_cvd                         false
% 2.10/1.00  --splitting_cvd_svl                     false
% 2.10/1.00  --splitting_nvd                         32
% 2.10/1.00  --sub_typing                            true
% 2.10/1.00  --prep_gs_sim                           true
% 2.10/1.00  --prep_unflatten                        true
% 2.10/1.00  --prep_res_sim                          true
% 2.10/1.00  --prep_upred                            true
% 2.10/1.00  --prep_sem_filter                       exhaustive
% 2.10/1.00  --prep_sem_filter_out                   false
% 2.10/1.00  --pred_elim                             true
% 2.10/1.00  --res_sim_input                         true
% 2.10/1.00  --eq_ax_congr_red                       true
% 2.10/1.00  --pure_diseq_elim                       true
% 2.10/1.00  --brand_transform                       false
% 2.10/1.00  --non_eq_to_eq                          false
% 2.10/1.00  --prep_def_merge                        true
% 2.10/1.00  --prep_def_merge_prop_impl              false
% 2.10/1.00  --prep_def_merge_mbd                    true
% 2.10/1.00  --prep_def_merge_tr_red                 false
% 2.10/1.00  --prep_def_merge_tr_cl                  false
% 2.10/1.00  --smt_preprocessing                     true
% 2.10/1.00  --smt_ac_axioms                         fast
% 2.10/1.00  --preprocessed_out                      false
% 2.10/1.00  --preprocessed_stats                    false
% 2.10/1.00  
% 2.10/1.00  ------ Abstraction refinement Options
% 2.10/1.00  
% 2.10/1.00  --abstr_ref                             []
% 2.10/1.00  --abstr_ref_prep                        false
% 2.10/1.00  --abstr_ref_until_sat                   false
% 2.10/1.00  --abstr_ref_sig_restrict                funpre
% 2.10/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.10/1.00  --abstr_ref_under                       []
% 2.10/1.00  
% 2.10/1.00  ------ SAT Options
% 2.10/1.00  
% 2.10/1.00  --sat_mode                              false
% 2.10/1.00  --sat_fm_restart_options                ""
% 2.10/1.00  --sat_gr_def                            false
% 2.10/1.00  --sat_epr_types                         true
% 2.10/1.00  --sat_non_cyclic_types                  false
% 2.10/1.00  --sat_finite_models                     false
% 2.10/1.00  --sat_fm_lemmas                         false
% 2.10/1.00  --sat_fm_prep                           false
% 2.10/1.00  --sat_fm_uc_incr                        true
% 2.10/1.00  --sat_out_model                         small
% 2.10/1.00  --sat_out_clauses                       false
% 2.10/1.00  
% 2.10/1.00  ------ QBF Options
% 2.10/1.00  
% 2.10/1.00  --qbf_mode                              false
% 2.10/1.00  --qbf_elim_univ                         false
% 2.10/1.00  --qbf_dom_inst                          none
% 2.10/1.00  --qbf_dom_pre_inst                      false
% 2.10/1.00  --qbf_sk_in                             false
% 2.10/1.00  --qbf_pred_elim                         true
% 2.10/1.00  --qbf_split                             512
% 2.10/1.00  
% 2.10/1.00  ------ BMC1 Options
% 2.10/1.00  
% 2.10/1.00  --bmc1_incremental                      false
% 2.10/1.00  --bmc1_axioms                           reachable_all
% 2.10/1.00  --bmc1_min_bound                        0
% 2.10/1.00  --bmc1_max_bound                        -1
% 2.10/1.00  --bmc1_max_bound_default                -1
% 2.10/1.00  --bmc1_symbol_reachability              true
% 2.10/1.00  --bmc1_property_lemmas                  false
% 2.10/1.00  --bmc1_k_induction                      false
% 2.10/1.00  --bmc1_non_equiv_states                 false
% 2.10/1.00  --bmc1_deadlock                         false
% 2.10/1.00  --bmc1_ucm                              false
% 2.10/1.00  --bmc1_add_unsat_core                   none
% 2.10/1.00  --bmc1_unsat_core_children              false
% 2.10/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.10/1.00  --bmc1_out_stat                         full
% 2.10/1.00  --bmc1_ground_init                      false
% 2.10/1.00  --bmc1_pre_inst_next_state              false
% 2.10/1.00  --bmc1_pre_inst_state                   false
% 2.10/1.00  --bmc1_pre_inst_reach_state             false
% 2.10/1.00  --bmc1_out_unsat_core                   false
% 2.10/1.00  --bmc1_aig_witness_out                  false
% 2.10/1.00  --bmc1_verbose                          false
% 2.10/1.00  --bmc1_dump_clauses_tptp                false
% 2.10/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.10/1.00  --bmc1_dump_file                        -
% 2.10/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.10/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.10/1.00  --bmc1_ucm_extend_mode                  1
% 2.10/1.00  --bmc1_ucm_init_mode                    2
% 2.10/1.00  --bmc1_ucm_cone_mode                    none
% 2.10/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.10/1.00  --bmc1_ucm_relax_model                  4
% 2.10/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.10/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.10/1.00  --bmc1_ucm_layered_model                none
% 2.10/1.00  --bmc1_ucm_max_lemma_size               10
% 2.10/1.00  
% 2.10/1.00  ------ AIG Options
% 2.10/1.00  
% 2.10/1.00  --aig_mode                              false
% 2.10/1.00  
% 2.10/1.00  ------ Instantiation Options
% 2.10/1.00  
% 2.10/1.00  --instantiation_flag                    true
% 2.10/1.00  --inst_sos_flag                         false
% 2.10/1.00  --inst_sos_phase                        true
% 2.10/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.10/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.10/1.00  --inst_lit_sel_side                     num_symb
% 2.10/1.00  --inst_solver_per_active                1400
% 2.10/1.00  --inst_solver_calls_frac                1.
% 2.10/1.00  --inst_passive_queue_type               priority_queues
% 2.10/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.10/1.00  --inst_passive_queues_freq              [25;2]
% 2.10/1.00  --inst_dismatching                      true
% 2.10/1.00  --inst_eager_unprocessed_to_passive     true
% 2.10/1.00  --inst_prop_sim_given                   true
% 2.10/1.00  --inst_prop_sim_new                     false
% 2.10/1.00  --inst_subs_new                         false
% 2.10/1.00  --inst_eq_res_simp                      false
% 2.10/1.00  --inst_subs_given                       false
% 2.10/1.00  --inst_orphan_elimination               true
% 2.10/1.00  --inst_learning_loop_flag               true
% 2.10/1.00  --inst_learning_start                   3000
% 2.10/1.00  --inst_learning_factor                  2
% 2.10/1.00  --inst_start_prop_sim_after_learn       3
% 2.10/1.00  --inst_sel_renew                        solver
% 2.10/1.00  --inst_lit_activity_flag                true
% 2.10/1.00  --inst_restr_to_given                   false
% 2.10/1.00  --inst_activity_threshold               500
% 2.10/1.00  --inst_out_proof                        true
% 2.10/1.00  
% 2.10/1.00  ------ Resolution Options
% 2.10/1.00  
% 2.10/1.00  --resolution_flag                       true
% 2.10/1.00  --res_lit_sel                           adaptive
% 2.10/1.00  --res_lit_sel_side                      none
% 2.10/1.00  --res_ordering                          kbo
% 2.10/1.00  --res_to_prop_solver                    active
% 2.10/1.00  --res_prop_simpl_new                    false
% 2.10/1.00  --res_prop_simpl_given                  true
% 2.10/1.00  --res_passive_queue_type                priority_queues
% 2.10/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.10/1.00  --res_passive_queues_freq               [15;5]
% 2.10/1.00  --res_forward_subs                      full
% 2.10/1.00  --res_backward_subs                     full
% 2.10/1.00  --res_forward_subs_resolution           true
% 2.10/1.00  --res_backward_subs_resolution          true
% 2.10/1.00  --res_orphan_elimination                true
% 2.10/1.00  --res_time_limit                        2.
% 2.10/1.00  --res_out_proof                         true
% 2.10/1.00  
% 2.10/1.00  ------ Superposition Options
% 2.10/1.00  
% 2.10/1.00  --superposition_flag                    true
% 2.10/1.00  --sup_passive_queue_type                priority_queues
% 2.10/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.10/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.10/1.00  --demod_completeness_check              fast
% 2.10/1.00  --demod_use_ground                      true
% 2.10/1.00  --sup_to_prop_solver                    passive
% 2.10/1.00  --sup_prop_simpl_new                    true
% 2.10/1.00  --sup_prop_simpl_given                  true
% 2.10/1.00  --sup_fun_splitting                     false
% 2.10/1.00  --sup_smt_interval                      50000
% 2.10/1.00  
% 2.10/1.00  ------ Superposition Simplification Setup
% 2.10/1.00  
% 2.10/1.00  --sup_indices_passive                   []
% 2.10/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.10/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/1.00  --sup_full_bw                           [BwDemod]
% 2.10/1.00  --sup_immed_triv                        [TrivRules]
% 2.10/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.10/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/1.00  --sup_immed_bw_main                     []
% 2.10/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.10/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.10/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.10/1.00  
% 2.10/1.00  ------ Combination Options
% 2.10/1.00  
% 2.10/1.00  --comb_res_mult                         3
% 2.10/1.00  --comb_sup_mult                         2
% 2.10/1.00  --comb_inst_mult                        10
% 2.10/1.00  
% 2.10/1.00  ------ Debug Options
% 2.10/1.00  
% 2.10/1.00  --dbg_backtrace                         false
% 2.10/1.00  --dbg_dump_prop_clauses                 false
% 2.10/1.00  --dbg_dump_prop_clauses_file            -
% 2.10/1.00  --dbg_out_stat                          false
% 2.10/1.00  ------ Parsing...
% 2.10/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.10/1.00  
% 2.10/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.10/1.00  
% 2.10/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.10/1.00  
% 2.10/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.10/1.00  ------ Proving...
% 2.10/1.00  ------ Problem Properties 
% 2.10/1.00  
% 2.10/1.00  
% 2.10/1.00  clauses                                 15
% 2.10/1.00  conjectures                             0
% 2.10/1.00  EPR                                     2
% 2.10/1.00  Horn                                    15
% 2.10/1.00  unary                                   3
% 2.10/1.00  binary                                  8
% 2.10/1.00  lits                                    34
% 2.10/1.00  lits eq                                 17
% 2.10/1.00  fd_pure                                 0
% 2.10/1.00  fd_pseudo                               0
% 2.10/1.00  fd_cond                                 5
% 2.10/1.00  fd_pseudo_cond                          0
% 2.10/1.00  AC symbols                              0
% 2.10/1.00  
% 2.10/1.00  ------ Schedule dynamic 5 is on 
% 2.10/1.00  
% 2.10/1.00  ------ no conjectures: strip conj schedule 
% 2.10/1.00  
% 2.10/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 2.10/1.00  
% 2.10/1.00  
% 2.10/1.00  ------ 
% 2.10/1.00  Current options:
% 2.10/1.00  ------ 
% 2.10/1.00  
% 2.10/1.00  ------ Input Options
% 2.10/1.00  
% 2.10/1.00  --out_options                           all
% 2.10/1.00  --tptp_safe_out                         true
% 2.10/1.00  --problem_path                          ""
% 2.10/1.00  --include_path                          ""
% 2.10/1.00  --clausifier                            res/vclausify_rel
% 2.10/1.00  --clausifier_options                    --mode clausify
% 2.10/1.00  --stdin                                 false
% 2.10/1.00  --stats_out                             all
% 2.10/1.00  
% 2.10/1.00  ------ General Options
% 2.10/1.00  
% 2.10/1.00  --fof                                   false
% 2.10/1.00  --time_out_real                         305.
% 2.10/1.00  --time_out_virtual                      -1.
% 2.10/1.00  --symbol_type_check                     false
% 2.10/1.00  --clausify_out                          false
% 2.10/1.00  --sig_cnt_out                           false
% 2.10/1.00  --trig_cnt_out                          false
% 2.10/1.00  --trig_cnt_out_tolerance                1.
% 2.10/1.00  --trig_cnt_out_sk_spl                   false
% 2.10/1.00  --abstr_cl_out                          false
% 2.10/1.00  
% 2.10/1.00  ------ Global Options
% 2.10/1.00  
% 2.10/1.00  --schedule                              default
% 2.10/1.00  --add_important_lit                     false
% 2.10/1.00  --prop_solver_per_cl                    1000
% 2.10/1.00  --min_unsat_core                        false
% 2.10/1.00  --soft_assumptions                      false
% 2.10/1.00  --soft_lemma_size                       3
% 2.10/1.00  --prop_impl_unit_size                   0
% 2.10/1.00  --prop_impl_unit                        []
% 2.10/1.00  --share_sel_clauses                     true
% 2.10/1.00  --reset_solvers                         false
% 2.10/1.00  --bc_imp_inh                            [conj_cone]
% 2.10/1.00  --conj_cone_tolerance                   3.
% 2.10/1.00  --extra_neg_conj                        none
% 2.10/1.00  --large_theory_mode                     true
% 2.10/1.00  --prolific_symb_bound                   200
% 2.10/1.00  --lt_threshold                          2000
% 2.10/1.00  --clause_weak_htbl                      true
% 2.10/1.00  --gc_record_bc_elim                     false
% 2.10/1.00  
% 2.10/1.00  ------ Preprocessing Options
% 2.10/1.00  
% 2.10/1.00  --preprocessing_flag                    true
% 2.10/1.00  --time_out_prep_mult                    0.1
% 2.10/1.00  --splitting_mode                        input
% 2.10/1.00  --splitting_grd                         true
% 2.10/1.00  --splitting_cvd                         false
% 2.10/1.00  --splitting_cvd_svl                     false
% 2.10/1.00  --splitting_nvd                         32
% 2.10/1.00  --sub_typing                            true
% 2.10/1.00  --prep_gs_sim                           true
% 2.10/1.00  --prep_unflatten                        true
% 2.10/1.00  --prep_res_sim                          true
% 2.10/1.00  --prep_upred                            true
% 2.10/1.00  --prep_sem_filter                       exhaustive
% 2.10/1.00  --prep_sem_filter_out                   false
% 2.10/1.00  --pred_elim                             true
% 2.10/1.00  --res_sim_input                         true
% 2.10/1.00  --eq_ax_congr_red                       true
% 2.10/1.00  --pure_diseq_elim                       true
% 2.10/1.00  --brand_transform                       false
% 2.10/1.00  --non_eq_to_eq                          false
% 2.10/1.00  --prep_def_merge                        true
% 2.10/1.00  --prep_def_merge_prop_impl              false
% 2.10/1.00  --prep_def_merge_mbd                    true
% 2.10/1.00  --prep_def_merge_tr_red                 false
% 2.10/1.00  --prep_def_merge_tr_cl                  false
% 2.10/1.00  --smt_preprocessing                     true
% 2.10/1.00  --smt_ac_axioms                         fast
% 2.10/1.00  --preprocessed_out                      false
% 2.10/1.00  --preprocessed_stats                    false
% 2.10/1.00  
% 2.10/1.00  ------ Abstraction refinement Options
% 2.10/1.00  
% 2.10/1.00  --abstr_ref                             []
% 2.10/1.00  --abstr_ref_prep                        false
% 2.10/1.00  --abstr_ref_until_sat                   false
% 2.10/1.00  --abstr_ref_sig_restrict                funpre
% 2.10/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.10/1.00  --abstr_ref_under                       []
% 2.10/1.00  
% 2.10/1.00  ------ SAT Options
% 2.10/1.00  
% 2.10/1.00  --sat_mode                              false
% 2.10/1.00  --sat_fm_restart_options                ""
% 2.10/1.00  --sat_gr_def                            false
% 2.10/1.00  --sat_epr_types                         true
% 2.10/1.00  --sat_non_cyclic_types                  false
% 2.10/1.00  --sat_finite_models                     false
% 2.10/1.00  --sat_fm_lemmas                         false
% 2.10/1.00  --sat_fm_prep                           false
% 2.10/1.00  --sat_fm_uc_incr                        true
% 2.10/1.00  --sat_out_model                         small
% 2.10/1.00  --sat_out_clauses                       false
% 2.10/1.00  
% 2.10/1.00  ------ QBF Options
% 2.10/1.00  
% 2.10/1.00  --qbf_mode                              false
% 2.10/1.00  --qbf_elim_univ                         false
% 2.10/1.00  --qbf_dom_inst                          none
% 2.10/1.00  --qbf_dom_pre_inst                      false
% 2.10/1.00  --qbf_sk_in                             false
% 2.10/1.00  --qbf_pred_elim                         true
% 2.10/1.00  --qbf_split                             512
% 2.10/1.00  
% 2.10/1.00  ------ BMC1 Options
% 2.10/1.00  
% 2.10/1.00  --bmc1_incremental                      false
% 2.10/1.00  --bmc1_axioms                           reachable_all
% 2.10/1.00  --bmc1_min_bound                        0
% 2.10/1.00  --bmc1_max_bound                        -1
% 2.10/1.00  --bmc1_max_bound_default                -1
% 2.10/1.00  --bmc1_symbol_reachability              true
% 2.10/1.00  --bmc1_property_lemmas                  false
% 2.10/1.00  --bmc1_k_induction                      false
% 2.10/1.00  --bmc1_non_equiv_states                 false
% 2.10/1.00  --bmc1_deadlock                         false
% 2.10/1.00  --bmc1_ucm                              false
% 2.10/1.00  --bmc1_add_unsat_core                   none
% 2.10/1.00  --bmc1_unsat_core_children              false
% 2.10/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.10/1.00  --bmc1_out_stat                         full
% 2.10/1.00  --bmc1_ground_init                      false
% 2.10/1.00  --bmc1_pre_inst_next_state              false
% 2.10/1.00  --bmc1_pre_inst_state                   false
% 2.10/1.00  --bmc1_pre_inst_reach_state             false
% 2.10/1.00  --bmc1_out_unsat_core                   false
% 2.10/1.00  --bmc1_aig_witness_out                  false
% 2.10/1.00  --bmc1_verbose                          false
% 2.10/1.00  --bmc1_dump_clauses_tptp                false
% 2.10/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.10/1.00  --bmc1_dump_file                        -
% 2.10/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.10/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.10/1.00  --bmc1_ucm_extend_mode                  1
% 2.10/1.00  --bmc1_ucm_init_mode                    2
% 2.10/1.00  --bmc1_ucm_cone_mode                    none
% 2.10/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.10/1.00  --bmc1_ucm_relax_model                  4
% 2.10/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.10/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.10/1.00  --bmc1_ucm_layered_model                none
% 2.10/1.00  --bmc1_ucm_max_lemma_size               10
% 2.10/1.00  
% 2.10/1.00  ------ AIG Options
% 2.10/1.00  
% 2.10/1.00  --aig_mode                              false
% 2.10/1.00  
% 2.10/1.00  ------ Instantiation Options
% 2.10/1.00  
% 2.10/1.00  --instantiation_flag                    true
% 2.10/1.00  --inst_sos_flag                         false
% 2.10/1.00  --inst_sos_phase                        true
% 2.10/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.10/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.10/1.00  --inst_lit_sel_side                     none
% 2.10/1.00  --inst_solver_per_active                1400
% 2.10/1.00  --inst_solver_calls_frac                1.
% 2.10/1.00  --inst_passive_queue_type               priority_queues
% 2.10/1.00  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 2.10/1.00  --inst_passive_queues_freq              [25;2]
% 2.10/1.00  --inst_dismatching                      true
% 2.10/1.00  --inst_eager_unprocessed_to_passive     true
% 2.10/1.00  --inst_prop_sim_given                   true
% 2.10/1.00  --inst_prop_sim_new                     false
% 2.10/1.00  --inst_subs_new                         false
% 2.10/1.00  --inst_eq_res_simp                      false
% 2.10/1.00  --inst_subs_given                       false
% 2.10/1.00  --inst_orphan_elimination               true
% 2.10/1.00  --inst_learning_loop_flag               true
% 2.10/1.00  --inst_learning_start                   3000
% 2.10/1.00  --inst_learning_factor                  2
% 2.10/1.00  --inst_start_prop_sim_after_learn       3
% 2.10/1.00  --inst_sel_renew                        solver
% 2.10/1.00  --inst_lit_activity_flag                true
% 2.10/1.00  --inst_restr_to_given                   false
% 2.10/1.00  --inst_activity_threshold               500
% 2.10/1.00  --inst_out_proof                        true
% 2.10/1.00  
% 2.10/1.00  ------ Resolution Options
% 2.10/1.00  
% 2.10/1.00  --resolution_flag                       false
% 2.10/1.00  --res_lit_sel                           adaptive
% 2.10/1.00  --res_lit_sel_side                      none
% 2.10/1.00  --res_ordering                          kbo
% 2.10/1.00  --res_to_prop_solver                    active
% 2.10/1.00  --res_prop_simpl_new                    false
% 2.10/1.00  --res_prop_simpl_given                  true
% 2.10/1.00  --res_passive_queue_type                priority_queues
% 2.10/1.00  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 2.10/1.00  --res_passive_queues_freq               [15;5]
% 2.10/1.00  --res_forward_subs                      full
% 2.10/1.00  --res_backward_subs                     full
% 2.10/1.00  --res_forward_subs_resolution           true
% 2.10/1.00  --res_backward_subs_resolution          true
% 2.10/1.00  --res_orphan_elimination                true
% 2.10/1.00  --res_time_limit                        2.
% 2.10/1.00  --res_out_proof                         true
% 2.10/1.00  
% 2.10/1.00  ------ Superposition Options
% 2.10/1.00  
% 2.10/1.00  --superposition_flag                    true
% 2.10/1.00  --sup_passive_queue_type                priority_queues
% 2.10/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.10/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.10/1.00  --demod_completeness_check              fast
% 2.10/1.00  --demod_use_ground                      true
% 2.10/1.00  --sup_to_prop_solver                    passive
% 2.10/1.00  --sup_prop_simpl_new                    true
% 2.10/1.00  --sup_prop_simpl_given                  true
% 2.10/1.00  --sup_fun_splitting                     false
% 2.10/1.00  --sup_smt_interval                      50000
% 2.10/1.00  
% 2.10/1.00  ------ Superposition Simplification Setup
% 2.10/1.00  
% 2.10/1.00  --sup_indices_passive                   []
% 2.10/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.10/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/1.00  --sup_full_bw                           [BwDemod]
% 2.10/1.00  --sup_immed_triv                        [TrivRules]
% 2.10/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.10/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/1.00  --sup_immed_bw_main                     []
% 2.10/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.10/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.10/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.10/1.00  
% 2.10/1.00  ------ Combination Options
% 2.10/1.00  
% 2.10/1.00  --comb_res_mult                         3
% 2.10/1.00  --comb_sup_mult                         2
% 2.10/1.00  --comb_inst_mult                        10
% 2.10/1.00  
% 2.10/1.00  ------ Debug Options
% 2.10/1.00  
% 2.10/1.00  --dbg_backtrace                         false
% 2.10/1.00  --dbg_dump_prop_clauses                 false
% 2.10/1.00  --dbg_dump_prop_clauses_file            -
% 2.10/1.00  --dbg_out_stat                          false
% 2.10/1.00  
% 2.10/1.00  
% 2.10/1.00  
% 2.10/1.00  
% 2.10/1.00  ------ Proving...
% 2.10/1.00  
% 2.10/1.00  
% 2.10/1.00  % SZS status Theorem for theBenchmark.p
% 2.10/1.00  
% 2.10/1.00   Resolution empty clause
% 2.10/1.00  
% 2.10/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.10/1.00  
% 2.10/1.00  fof(f4,axiom,(
% 2.10/1.00    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.00  
% 2.10/1.00  fof(f37,plain,(
% 2.10/1.00    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.10/1.00    inference(cnf_transformation,[],[f4])).
% 2.10/1.00  
% 2.10/1.00  fof(f3,axiom,(
% 2.10/1.00    ! [X0] : k2_subset_1(X0) = X0),
% 2.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.00  
% 2.10/1.00  fof(f36,plain,(
% 2.10/1.00    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.10/1.00    inference(cnf_transformation,[],[f3])).
% 2.10/1.00  
% 2.10/1.00  fof(f5,axiom,(
% 2.10/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.00  
% 2.10/1.00  fof(f13,plain,(
% 2.10/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 2.10/1.00    inference(unused_predicate_definition_removal,[],[f5])).
% 2.10/1.00  
% 2.10/1.00  fof(f14,plain,(
% 2.10/1.00    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 2.10/1.00    inference(ennf_transformation,[],[f13])).
% 2.10/1.00  
% 2.10/1.00  fof(f38,plain,(
% 2.10/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.10/1.00    inference(cnf_transformation,[],[f14])).
% 2.10/1.00  
% 2.10/1.00  fof(f8,axiom,(
% 2.10/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.00  
% 2.10/1.00  fof(f17,plain,(
% 2.10/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 2.10/1.00    inference(ennf_transformation,[],[f8])).
% 2.10/1.00  
% 2.10/1.00  fof(f18,plain,(
% 2.10/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 2.10/1.00    inference(flattening,[],[f17])).
% 2.10/1.00  
% 2.10/1.00  fof(f41,plain,(
% 2.10/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 2.10/1.00    inference(cnf_transformation,[],[f18])).
% 2.10/1.00  
% 2.10/1.00  fof(f11,conjecture,(
% 2.10/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.00  
% 2.10/1.00  fof(f12,negated_conjecture,(
% 2.10/1.00    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.10/1.00    inference(negated_conjecture,[],[f11])).
% 2.10/1.00  
% 2.10/1.00  fof(f22,plain,(
% 2.10/1.00    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 2.10/1.00    inference(ennf_transformation,[],[f12])).
% 2.10/1.00  
% 2.10/1.00  fof(f23,plain,(
% 2.10/1.00    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 2.10/1.00    inference(flattening,[],[f22])).
% 2.10/1.00  
% 2.10/1.00  fof(f31,plain,(
% 2.10/1.00    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0)) => ((~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 2.10/1.00    introduced(choice_axiom,[])).
% 2.10/1.00  
% 2.10/1.00  fof(f32,plain,(
% 2.10/1.00    (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 2.10/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f31])).
% 2.10/1.00  
% 2.10/1.00  fof(f51,plain,(
% 2.10/1.00    v1_relat_1(sK2)),
% 2.10/1.00    inference(cnf_transformation,[],[f32])).
% 2.10/1.00  
% 2.10/1.00  fof(f6,axiom,(
% 2.10/1.00    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 2.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.00  
% 2.10/1.00  fof(f15,plain,(
% 2.10/1.00    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 2.10/1.00    inference(ennf_transformation,[],[f6])).
% 2.10/1.00  
% 2.10/1.00  fof(f39,plain,(
% 2.10/1.00    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 2.10/1.00    inference(cnf_transformation,[],[f15])).
% 2.10/1.00  
% 2.10/1.00  fof(f10,axiom,(
% 2.10/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.00  
% 2.10/1.00  fof(f20,plain,(
% 2.10/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/1.00    inference(ennf_transformation,[],[f10])).
% 2.10/1.00  
% 2.10/1.00  fof(f21,plain,(
% 2.10/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/1.00    inference(flattening,[],[f20])).
% 2.10/1.00  
% 2.10/1.00  fof(f30,plain,(
% 2.10/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/1.00    inference(nnf_transformation,[],[f21])).
% 2.10/1.00  
% 2.10/1.00  fof(f47,plain,(
% 2.10/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.10/1.00    inference(cnf_transformation,[],[f30])).
% 2.10/1.00  
% 2.10/1.00  fof(f53,plain,(
% 2.10/1.00    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2)),
% 2.10/1.00    inference(cnf_transformation,[],[f32])).
% 2.10/1.00  
% 2.10/1.00  fof(f52,plain,(
% 2.10/1.00    v1_funct_1(sK2)),
% 2.10/1.00    inference(cnf_transformation,[],[f32])).
% 2.10/1.00  
% 2.10/1.00  fof(f7,axiom,(
% 2.10/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.00  
% 2.10/1.00  fof(f16,plain,(
% 2.10/1.00    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/1.00    inference(ennf_transformation,[],[f7])).
% 2.10/1.00  
% 2.10/1.00  fof(f40,plain,(
% 2.10/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.10/1.00    inference(cnf_transformation,[],[f16])).
% 2.10/1.00  
% 2.10/1.00  fof(f2,axiom,(
% 2.10/1.00    v1_xboole_0(k1_xboole_0)),
% 2.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.00  
% 2.10/1.00  fof(f35,plain,(
% 2.10/1.00    v1_xboole_0(k1_xboole_0)),
% 2.10/1.00    inference(cnf_transformation,[],[f2])).
% 2.10/1.00  
% 2.10/1.00  fof(f1,axiom,(
% 2.10/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.00  
% 2.10/1.00  fof(f24,plain,(
% 2.10/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.10/1.00    inference(nnf_transformation,[],[f1])).
% 2.10/1.00  
% 2.10/1.00  fof(f25,plain,(
% 2.10/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.10/1.00    inference(rectify,[],[f24])).
% 2.10/1.00  
% 2.10/1.00  fof(f26,plain,(
% 2.10/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.10/1.00    introduced(choice_axiom,[])).
% 2.10/1.00  
% 2.10/1.00  fof(f27,plain,(
% 2.10/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.10/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 2.10/1.00  
% 2.10/1.00  fof(f33,plain,(
% 2.10/1.00    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.10/1.00    inference(cnf_transformation,[],[f27])).
% 2.10/1.00  
% 2.10/1.00  fof(f9,axiom,(
% 2.10/1.00    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.00  
% 2.10/1.00  fof(f19,plain,(
% 2.10/1.00    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.10/1.00    inference(ennf_transformation,[],[f9])).
% 2.10/1.00  
% 2.10/1.00  fof(f28,plain,(
% 2.10/1.00    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)))),
% 2.10/1.00    introduced(choice_axiom,[])).
% 2.10/1.00  
% 2.10/1.00  fof(f29,plain,(
% 2.10/1.00    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)) | k1_xboole_0 = X0)),
% 2.10/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f28])).
% 2.10/1.00  
% 2.10/1.00  fof(f42,plain,(
% 2.10/1.00    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 2.10/1.00    inference(cnf_transformation,[],[f29])).
% 2.10/1.00  
% 2.10/1.00  fof(f50,plain,(
% 2.10/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.10/1.00    inference(cnf_transformation,[],[f30])).
% 2.10/1.00  
% 2.10/1.00  fof(f54,plain,(
% 2.10/1.00    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.10/1.00    inference(equality_resolution,[],[f50])).
% 2.10/1.00  
% 2.10/1.00  fof(f55,plain,(
% 2.10/1.00    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.10/1.00    inference(equality_resolution,[],[f54])).
% 2.10/1.00  
% 2.10/1.00  fof(f48,plain,(
% 2.10/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.10/1.00    inference(cnf_transformation,[],[f30])).
% 2.10/1.00  
% 2.10/1.00  fof(f57,plain,(
% 2.10/1.00    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.10/1.00    inference(equality_resolution,[],[f48])).
% 2.10/1.00  
% 2.10/1.00  cnf(c_4,plain,
% 2.10/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 2.10/1.00      inference(cnf_transformation,[],[f37]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_696,plain,
% 2.10/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.10/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_3,plain,
% 2.10/1.00      ( k2_subset_1(X0) = X0 ),
% 2.10/1.00      inference(cnf_transformation,[],[f36]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_702,plain,
% 2.10/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.10/1.00      inference(light_normalisation,[status(thm)],[c_696,c_3]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_5,plain,
% 2.10/1.00      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.10/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_695,plain,
% 2.10/1.00      ( r1_tarski(X0,X1) = iProver_top
% 2.10/1.00      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 2.10/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1019,plain,
% 2.10/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 2.10/1.00      inference(superposition,[status(thm)],[c_702,c_695]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_8,plain,
% 2.10/1.00      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 2.10/1.00      | ~ r1_tarski(k1_relat_1(X0),X2)
% 2.10/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.10/1.00      | ~ v1_relat_1(X0) ),
% 2.10/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_20,negated_conjecture,
% 2.10/1.00      ( v1_relat_1(sK2) ),
% 2.10/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_232,plain,
% 2.10/1.00      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 2.10/1.00      | ~ r1_tarski(k1_relat_1(X0),X2)
% 2.10/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.10/1.00      | sK2 != X0 ),
% 2.10/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_20]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_233,plain,
% 2.10/1.00      ( ~ r1_tarski(k2_relat_1(sK2),X0)
% 2.10/1.00      | ~ r1_tarski(k1_relat_1(sK2),X1)
% 2.10/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ),
% 2.10/1.00      inference(unflattening,[status(thm)],[c_232]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_692,plain,
% 2.10/1.00      ( r1_tarski(k2_relat_1(sK2),X0) != iProver_top
% 2.10/1.00      | r1_tarski(k1_relat_1(sK2),X1) != iProver_top
% 2.10/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top ),
% 2.10/1.00      inference(predicate_to_equality,[status(thm)],[c_233]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_6,plain,
% 2.10/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.10/1.00      | ~ v1_xboole_0(X2)
% 2.10/1.00      | v1_xboole_0(X0) ),
% 2.10/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_694,plain,
% 2.10/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.10/1.00      | v1_xboole_0(X2) != iProver_top
% 2.10/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.10/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1122,plain,
% 2.10/1.00      ( r1_tarski(k2_relat_1(sK2),X0) != iProver_top
% 2.10/1.00      | r1_tarski(k1_relat_1(sK2),X1) != iProver_top
% 2.10/1.00      | v1_xboole_0(X0) != iProver_top
% 2.10/1.00      | v1_xboole_0(sK2) = iProver_top ),
% 2.10/1.00      inference(superposition,[status(thm)],[c_692,c_694]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1249,plain,
% 2.10/1.00      ( r1_tarski(k1_relat_1(sK2),X0) != iProver_top
% 2.10/1.00      | v1_xboole_0(k2_relat_1(sK2)) != iProver_top
% 2.10/1.00      | v1_xboole_0(sK2) = iProver_top ),
% 2.10/1.00      inference(superposition,[status(thm)],[c_1019,c_1122]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_15,plain,
% 2.10/1.00      ( v1_funct_2(X0,X1,X2)
% 2.10/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.10/1.00      | k1_relset_1(X1,X2,X0) != X1
% 2.10/1.00      | k1_xboole_0 = X2 ),
% 2.10/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_18,negated_conjecture,
% 2.10/1.00      ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
% 2.10/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 2.10/1.00      | ~ v1_funct_1(sK2) ),
% 2.10/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_19,negated_conjecture,
% 2.10/1.00      ( v1_funct_1(sK2) ),
% 2.10/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_111,plain,
% 2.10/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 2.10/1.00      | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
% 2.10/1.00      inference(global_propositional_subsumption,[status(thm)],[c_18,c_19]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_112,negated_conjecture,
% 2.10/1.00      ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
% 2.10/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
% 2.10/1.00      inference(renaming,[status(thm)],[c_111]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_375,plain,
% 2.10/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.10/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 2.10/1.00      | k1_relset_1(X1,X2,X0) != X1
% 2.10/1.00      | k2_relat_1(sK2) != X2
% 2.10/1.00      | k1_relat_1(sK2) != X1
% 2.10/1.00      | sK2 != X0
% 2.10/1.00      | k1_xboole_0 = X2 ),
% 2.10/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_112]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_376,plain,
% 2.10/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 2.10/1.00      | k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k1_relat_1(sK2)
% 2.10/1.00      | k1_xboole_0 = k2_relat_1(sK2) ),
% 2.10/1.00      inference(unflattening,[status(thm)],[c_375]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_7,plain,
% 2.10/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.10/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.10/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_384,plain,
% 2.10/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 2.10/1.00      | k1_xboole_0 = k2_relat_1(sK2) ),
% 2.10/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_376,c_7]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_688,plain,
% 2.10/1.00      ( k1_xboole_0 = k2_relat_1(sK2)
% 2.10/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top ),
% 2.10/1.00      inference(predicate_to_equality,[status(thm)],[c_384]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_817,plain,
% 2.10/1.00      ( k2_relat_1(sK2) = k1_xboole_0
% 2.10/1.00      | r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.10/1.00      | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top ),
% 2.10/1.00      inference(superposition,[status(thm)],[c_692,c_688]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1144,plain,
% 2.10/1.00      ( k2_relat_1(sK2) = k1_xboole_0
% 2.10/1.00      | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top ),
% 2.10/1.00      inference(superposition,[status(thm)],[c_1019,c_817]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1289,plain,
% 2.10/1.00      ( k2_relat_1(sK2) = k1_xboole_0 ),
% 2.10/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_1144,c_1019]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1505,plain,
% 2.10/1.00      ( r1_tarski(k1_relat_1(sK2),X0) != iProver_top
% 2.10/1.00      | v1_xboole_0(sK2) = iProver_top
% 2.10/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.10/1.00      inference(light_normalisation,[status(thm)],[c_1249,c_1289]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_2,plain,
% 2.10/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 2.10/1.00      inference(cnf_transformation,[],[f35]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_697,plain,
% 2.10/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.10/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1509,plain,
% 2.10/1.00      ( r1_tarski(k1_relat_1(sK2),X0) != iProver_top
% 2.10/1.00      | v1_xboole_0(sK2) = iProver_top ),
% 2.10/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_1505,c_697]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1513,plain,
% 2.10/1.00      ( v1_xboole_0(sK2) = iProver_top ),
% 2.10/1.00      inference(superposition,[status(thm)],[c_1019,c_1509]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1,plain,
% 2.10/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.10/1.00      inference(cnf_transformation,[],[f33]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_11,plain,
% 2.10/1.00      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 2.10/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_297,plain,
% 2.10/1.00      ( ~ v1_xboole_0(X0) | X1 != X0 | sK1(X1) != X2 | k1_xboole_0 = X1 ),
% 2.10/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_11]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_298,plain,
% 2.10/1.00      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.10/1.00      inference(unflattening,[status(thm)],[c_297]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_691,plain,
% 2.10/1.00      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.10/1.00      inference(predicate_to_equality,[status(thm)],[c_298]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1847,plain,
% 2.10/1.00      ( sK2 = k1_xboole_0 ),
% 2.10/1.00      inference(superposition,[status(thm)],[c_1513,c_691]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_12,plain,
% 2.10/1.00      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 2.10/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 2.10/1.00      | k1_xboole_0 = X0 ),
% 2.10/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_332,plain,
% 2.10/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 2.10/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 2.10/1.00      | k2_relat_1(sK2) != k1_xboole_0
% 2.10/1.00      | k1_relat_1(sK2) != X0
% 2.10/1.00      | sK2 != k1_xboole_0
% 2.10/1.00      | k1_xboole_0 = X0 ),
% 2.10/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_112]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_333,plain,
% 2.10/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 2.10/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)))
% 2.10/1.00      | k2_relat_1(sK2) != k1_xboole_0
% 2.10/1.00      | sK2 != k1_xboole_0
% 2.10/1.00      | k1_xboole_0 = k1_relat_1(sK2) ),
% 2.10/1.00      inference(unflattening,[status(thm)],[c_332]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_690,plain,
% 2.10/1.00      ( k2_relat_1(sK2) != k1_xboole_0
% 2.10/1.00      | sK2 != k1_xboole_0
% 2.10/1.00      | k1_xboole_0 = k1_relat_1(sK2)
% 2.10/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.10/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) != iProver_top ),
% 2.10/1.00      inference(predicate_to_equality,[status(thm)],[c_333]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1294,plain,
% 2.10/1.00      ( k1_relat_1(sK2) = k1_xboole_0
% 2.10/1.00      | sK2 != k1_xboole_0
% 2.10/1.00      | k1_xboole_0 != k1_xboole_0
% 2.10/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) != iProver_top
% 2.10/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) != iProver_top ),
% 2.10/1.00      inference(demodulation,[status(thm)],[c_1289,c_690]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1311,plain,
% 2.10/1.00      ( k1_relat_1(sK2) = k1_xboole_0
% 2.10/1.00      | sK2 != k1_xboole_0
% 2.10/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) != iProver_top
% 2.10/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) != iProver_top ),
% 2.10/1.00      inference(equality_resolution_simp,[status(thm)],[c_1294]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_480,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_806,plain,
% 2.10/1.00      ( sK2 != X0 | sK2 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 2.10/1.00      inference(instantiation,[status(thm)],[c_480]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_841,plain,
% 2.10/1.00      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 2.10/1.00      inference(instantiation,[status(thm)],[c_806]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_479,plain,( X0 = X0 ),theory(equality) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_842,plain,
% 2.10/1.00      ( sK2 = sK2 ),
% 2.10/1.00      inference(instantiation,[status(thm)],[c_479]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_903,plain,
% 2.10/1.00      ( ~ v1_xboole_0(sK2) | k1_xboole_0 = sK2 ),
% 2.10/1.00      inference(instantiation,[status(thm)],[c_298]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_904,plain,
% 2.10/1.00      ( k1_xboole_0 = sK2 | v1_xboole_0(sK2) != iProver_top ),
% 2.10/1.00      inference(predicate_to_equality,[status(thm)],[c_903]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1720,plain,
% 2.10/1.00      ( k1_relat_1(sK2) = k1_xboole_0
% 2.10/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) != iProver_top
% 2.10/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) != iProver_top ),
% 2.10/1.00      inference(global_propositional_subsumption,
% 2.10/1.00                [status(thm)],
% 2.10/1.00                [c_1311,c_841,c_842,c_904,c_1513]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1860,plain,
% 2.10/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
% 2.10/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) != iProver_top ),
% 2.10/1.00      inference(demodulation,[status(thm)],[c_1847,c_1720]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_14,plain,
% 2.10/1.00      ( v1_funct_2(X0,k1_xboole_0,X1)
% 2.10/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.10/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 2.10/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_359,plain,
% 2.10/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.10/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 2.10/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 2.10/1.00      | k2_relat_1(sK2) != X1
% 2.10/1.00      | k1_relat_1(sK2) != k1_xboole_0
% 2.10/1.00      | sK2 != X0 ),
% 2.10/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_112]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_360,plain,
% 2.10/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 2.10/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2))))
% 2.10/1.00      | k1_relset_1(k1_xboole_0,k2_relat_1(sK2),sK2) != k1_xboole_0
% 2.10/1.00      | k1_relat_1(sK2) != k1_xboole_0 ),
% 2.10/1.00      inference(unflattening,[status(thm)],[c_359]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_689,plain,
% 2.10/1.00      ( k1_relset_1(k1_xboole_0,k2_relat_1(sK2),sK2) != k1_xboole_0
% 2.10/1.00      | k1_relat_1(sK2) != k1_xboole_0
% 2.10/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.10/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2)))) != iProver_top ),
% 2.10/1.00      inference(predicate_to_equality,[status(thm)],[c_360]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1295,plain,
% 2.10/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) != k1_xboole_0
% 2.10/1.00      | k1_relat_1(sK2) != k1_xboole_0
% 2.10/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) != iProver_top
% 2.10/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 2.10/1.00      inference(demodulation,[status(thm)],[c_1289,c_689]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1867,plain,
% 2.10/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.10/1.00      | k1_relat_1(k1_xboole_0) != k1_xboole_0
% 2.10/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) != iProver_top
% 2.10/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 2.10/1.00      inference(demodulation,[status(thm)],[c_1847,c_1295]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1907,plain,
% 2.10/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.10/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) != iProver_top
% 2.10/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 2.10/1.00      inference(backward_subsumption_resolution,[status(thm)],[c_1860,c_1867]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_59,plain,
% 2.10/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.10/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_61,plain,
% 2.10/1.00      ( m1_subset_1(k2_subset_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.10/1.00      inference(instantiation,[status(thm)],[c_59]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_62,plain,
% 2.10/1.00      ( k2_subset_1(k1_xboole_0) = k1_xboole_0 ),
% 2.10/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_63,plain,
% 2.10/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.10/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_300,plain,
% 2.10/1.00      ( ~ v1_xboole_0(k1_xboole_0) | k1_xboole_0 = k1_xboole_0 ),
% 2.10/1.00      inference(instantiation,[status(thm)],[c_298]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1065,plain,
% 2.10/1.00      ( X0 != X1 | X0 = k2_subset_1(X2) | k2_subset_1(X2) != X1 ),
% 2.10/1.00      inference(instantiation,[status(thm)],[c_480]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1066,plain,
% 2.10/1.00      ( k2_subset_1(k1_xboole_0) != k1_xboole_0
% 2.10/1.00      | k1_xboole_0 = k2_subset_1(k1_xboole_0)
% 2.10/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 2.10/1.00      inference(instantiation,[status(thm)],[c_1065]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_483,plain,
% 2.10/1.00      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.10/1.00      theory(equality) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_834,plain,
% 2.10/1.00      ( m1_subset_1(X0,X1)
% 2.10/1.00      | ~ m1_subset_1(k2_subset_1(X2),k1_zfmisc_1(X2))
% 2.10/1.00      | X1 != k1_zfmisc_1(X2)
% 2.10/1.00      | X0 != k2_subset_1(X2) ),
% 2.10/1.00      inference(instantiation,[status(thm)],[c_483]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_892,plain,
% 2.10/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.10/1.00      | ~ m1_subset_1(k2_subset_1(X2),k1_zfmisc_1(X2))
% 2.10/1.00      | X0 != k2_subset_1(X2)
% 2.10/1.00      | k1_zfmisc_1(X1) != k1_zfmisc_1(X2) ),
% 2.10/1.00      inference(instantiation,[status(thm)],[c_834]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1083,plain,
% 2.10/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.10/1.00      | ~ m1_subset_1(k2_subset_1(X3),k1_zfmisc_1(X3))
% 2.10/1.00      | X0 != k2_subset_1(X3)
% 2.10/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(X3) ),
% 2.10/1.00      inference(instantiation,[status(thm)],[c_892]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1084,plain,
% 2.10/1.00      ( X0 != k2_subset_1(X1)
% 2.10/1.00      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(X1)
% 2.10/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top
% 2.10/1.00      | m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) != iProver_top ),
% 2.10/1.00      inference(predicate_to_equality,[status(thm)],[c_1083]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1086,plain,
% 2.10/1.00      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
% 2.10/1.00      | k1_xboole_0 != k2_subset_1(k1_xboole_0)
% 2.10/1.00      | m1_subset_1(k2_subset_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.10/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 2.10/1.00      inference(instantiation,[status(thm)],[c_1084]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_482,plain,
% 2.10/1.00      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 2.10/1.00      theory(equality) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1520,plain,
% 2.10/1.00      ( k2_zfmisc_1(X0,X1) != X2
% 2.10/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(X2) ),
% 2.10/1.00      inference(instantiation,[status(thm)],[c_482]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1521,plain,
% 2.10/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.10/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = k1_zfmisc_1(k1_xboole_0) ),
% 2.10/1.00      inference(instantiation,[status(thm)],[c_1520]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1123,plain,
% 2.10/1.00      ( v1_xboole_0(X0) != iProver_top
% 2.10/1.00      | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
% 2.10/1.00      inference(superposition,[status(thm)],[c_702,c_694]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1848,plain,
% 2.10/1.00      ( k2_zfmisc_1(X0,X1) = k1_xboole_0 | v1_xboole_0(X1) != iProver_top ),
% 2.10/1.00      inference(superposition,[status(thm)],[c_1123,c_691]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1856,plain,
% 2.10/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
% 2.10/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.10/1.00      inference(instantiation,[status(thm)],[c_1848]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_2009,plain,
% 2.10/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.10/1.00      inference(superposition,[status(thm)],[c_697,c_1848]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_2304,plain,
% 2.10/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
% 2.10/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.10/1.00      inference(demodulation,[status(thm)],[c_1860,c_2009]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_2307,plain,
% 2.10/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.10/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_2304,c_702]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_693,plain,
% 2.10/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.10/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.10/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1002,plain,
% 2.10/1.00      ( k1_relset_1(X0,X1,k2_zfmisc_1(X0,X1)) = k1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.10/1.00      inference(superposition,[status(thm)],[c_702,c_693]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_2082,plain,
% 2.10/1.00      ( k1_relat_1(k2_zfmisc_1(X0,k1_xboole_0)) = k1_relset_1(X0,k1_xboole_0,k1_xboole_0) ),
% 2.10/1.00      inference(superposition,[status(thm)],[c_2009,c_1002]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_2089,plain,
% 2.10/1.00      ( k1_relset_1(X0,k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 2.10/1.00      inference(light_normalisation,[status(thm)],[c_2082,c_2009]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_2308,plain,
% 2.10/1.00      ( k1_relset_1(X0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.10/1.00      inference(demodulation,[status(thm)],[c_2307,c_2089]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_2318,plain,
% 2.10/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.10/1.00      inference(instantiation,[status(thm)],[c_2308]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_2516,plain,
% 2.10/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) != iProver_top ),
% 2.10/1.00      inference(global_propositional_subsumption,
% 2.10/1.00                [status(thm)],
% 2.10/1.00                [c_1907,c_61,c_62,c_2,c_63,c_300,c_1066,c_1086,c_1521,c_1856,
% 2.10/1.00                 c_2318]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_2520,plain,
% 2.10/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 2.10/1.00      inference(light_normalisation,[status(thm)],[c_2516,c_2307]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_2521,plain,
% 2.10/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.10/1.00      inference(demodulation,[status(thm)],[c_2520,c_2009]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_2523,plain,
% 2.10/1.00      ( $false ),
% 2.10/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_2521,c_702]) ).
% 2.10/1.00  
% 2.10/1.00  
% 2.10/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.10/1.00  
% 2.10/1.00  ------                               Statistics
% 2.10/1.00  
% 2.10/1.00  ------ General
% 2.10/1.00  
% 2.10/1.00  abstr_ref_over_cycles:                  0
% 2.10/1.00  abstr_ref_under_cycles:                 0
% 2.10/1.00  gc_basic_clause_elim:                   0
% 2.10/1.00  forced_gc_time:                         0
% 2.10/1.00  parsing_time:                           0.008
% 2.10/1.00  unif_index_cands_time:                  0.
% 2.10/1.00  unif_index_add_time:                    0.
% 2.10/1.00  orderings_time:                         0.
% 2.10/1.00  out_proof_time:                         0.011
% 2.10/1.00  total_time:                             0.111
% 2.10/1.00  num_of_symbols:                         49
% 2.10/1.00  num_of_terms:                           2407
% 2.10/1.00  
% 2.10/1.00  ------ Preprocessing
% 2.10/1.00  
% 2.10/1.00  num_of_splits:                          0
% 2.10/1.00  num_of_split_atoms:                     0
% 2.10/1.00  num_of_reused_defs:                     0
% 2.10/1.00  num_eq_ax_congr_red:                    17
% 2.10/1.00  num_of_sem_filtered_clauses:            2
% 2.10/1.00  num_of_subtypes:                        0
% 2.10/1.00  monotx_restored_types:                  0
% 2.10/1.00  sat_num_of_epr_types:                   0
% 2.10/1.00  sat_num_of_non_cyclic_types:            0
% 2.10/1.00  sat_guarded_non_collapsed_types:        0
% 2.10/1.00  num_pure_diseq_elim:                    0
% 2.10/1.00  simp_replaced_by:                       0
% 2.10/1.00  res_preprocessed:                       89
% 2.10/1.00  prep_upred:                             0
% 2.10/1.00  prep_unflattend:                        39
% 2.10/1.00  smt_new_axioms:                         0
% 2.10/1.00  pred_elim_cands:                        3
% 2.10/1.00  pred_elim:                              3
% 2.10/1.00  pred_elim_cl:                           5
% 2.10/1.00  pred_elim_cycles:                       5
% 2.10/1.00  merged_defs:                            0
% 2.10/1.00  merged_defs_ncl:                        0
% 2.10/1.00  bin_hyper_res:                          0
% 2.10/1.00  prep_cycles:                            4
% 2.10/1.00  pred_elim_time:                         0.004
% 2.10/1.00  splitting_time:                         0.
% 2.10/1.00  sem_filter_time:                        0.
% 2.10/1.00  monotx_time:                            0.
% 2.10/1.00  subtype_inf_time:                       0.
% 2.10/1.00  
% 2.10/1.00  ------ Problem properties
% 2.10/1.00  
% 2.10/1.00  clauses:                                15
% 2.10/1.00  conjectures:                            0
% 2.10/1.00  epr:                                    2
% 2.10/1.00  horn:                                   15
% 2.10/1.00  ground:                                 4
% 2.10/1.00  unary:                                  3
% 2.10/1.00  binary:                                 8
% 2.10/1.00  lits:                                   34
% 2.10/1.00  lits_eq:                                17
% 2.10/1.00  fd_pure:                                0
% 2.10/1.00  fd_pseudo:                              0
% 2.10/1.00  fd_cond:                                5
% 2.10/1.00  fd_pseudo_cond:                         0
% 2.10/1.00  ac_symbols:                             0
% 2.10/1.00  
% 2.10/1.00  ------ Propositional Solver
% 2.10/1.00  
% 2.10/1.00  prop_solver_calls:                      28
% 2.10/1.00  prop_fast_solver_calls:                 583
% 2.10/1.00  smt_solver_calls:                       0
% 2.10/1.00  smt_fast_solver_calls:                  0
% 2.10/1.00  prop_num_of_clauses:                    919
% 2.10/1.00  prop_preprocess_simplified:             3137
% 2.10/1.00  prop_fo_subsumed:                       8
% 2.10/1.00  prop_solver_time:                       0.
% 2.10/1.00  smt_solver_time:                        0.
% 2.10/1.00  smt_fast_solver_time:                   0.
% 2.10/1.00  prop_fast_solver_time:                  0.
% 2.10/1.00  prop_unsat_core_time:                   0.
% 2.10/1.00  
% 2.10/1.00  ------ QBF
% 2.10/1.00  
% 2.10/1.00  qbf_q_res:                              0
% 2.10/1.00  qbf_num_tautologies:                    0
% 2.10/1.00  qbf_prep_cycles:                        0
% 2.10/1.00  
% 2.10/1.00  ------ BMC1
% 2.10/1.00  
% 2.10/1.00  bmc1_current_bound:                     -1
% 2.10/1.00  bmc1_last_solved_bound:                 -1
% 2.10/1.00  bmc1_unsat_core_size:                   -1
% 2.10/1.00  bmc1_unsat_core_parents_size:           -1
% 2.10/1.00  bmc1_merge_next_fun:                    0
% 2.10/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.10/1.00  
% 2.10/1.00  ------ Instantiation
% 2.10/1.00  
% 2.10/1.00  inst_num_of_clauses:                    336
% 2.10/1.00  inst_num_in_passive:                    42
% 2.10/1.00  inst_num_in_active:                     196
% 2.10/1.00  inst_num_in_unprocessed:                98
% 2.10/1.00  inst_num_of_loops:                      220
% 2.10/1.00  inst_num_of_learning_restarts:          0
% 2.10/1.00  inst_num_moves_active_passive:          21
% 2.10/1.00  inst_lit_activity:                      0
% 2.10/1.00  inst_lit_activity_moves:                0
% 2.10/1.00  inst_num_tautologies:                   0
% 2.10/1.00  inst_num_prop_implied:                  0
% 2.10/1.00  inst_num_existing_simplified:           0
% 2.10/1.00  inst_num_eq_res_simplified:             0
% 2.10/1.00  inst_num_child_elim:                    0
% 2.10/1.00  inst_num_of_dismatching_blockings:      69
% 2.10/1.00  inst_num_of_non_proper_insts:           275
% 2.10/1.00  inst_num_of_duplicates:                 0
% 2.10/1.00  inst_inst_num_from_inst_to_res:         0
% 2.10/1.00  inst_dismatching_checking_time:         0.
% 2.10/1.00  
% 2.10/1.00  ------ Resolution
% 2.10/1.00  
% 2.10/1.00  res_num_of_clauses:                     0
% 2.10/1.00  res_num_in_passive:                     0
% 2.10/1.00  res_num_in_active:                      0
% 2.10/1.00  res_num_of_loops:                       93
% 2.10/1.00  res_forward_subset_subsumed:            20
% 2.10/1.00  res_backward_subset_subsumed:           2
% 2.10/1.00  res_forward_subsumed:                   0
% 2.10/1.00  res_backward_subsumed:                  0
% 2.10/1.00  res_forward_subsumption_resolution:     1
% 2.10/1.00  res_backward_subsumption_resolution:    2
% 2.10/1.00  res_clause_to_clause_subsumption:       154
% 2.10/1.00  res_orphan_elimination:                 0
% 2.10/1.00  res_tautology_del:                      56
% 2.10/1.00  res_num_eq_res_simplified:              0
% 2.10/1.00  res_num_sel_changes:                    0
% 2.10/1.00  res_moves_from_active_to_pass:          0
% 2.10/1.00  
% 2.10/1.00  ------ Superposition
% 2.10/1.00  
% 2.10/1.00  sup_time_total:                         0.
% 2.10/1.00  sup_time_generating:                    0.
% 2.10/1.00  sup_time_sim_full:                      0.
% 2.10/1.00  sup_time_sim_immed:                     0.
% 2.10/1.00  
% 2.10/1.00  sup_num_of_clauses:                     30
% 2.10/1.00  sup_num_in_active:                      21
% 2.10/1.00  sup_num_in_passive:                     9
% 2.10/1.00  sup_num_of_loops:                       42
% 2.10/1.00  sup_fw_superposition:                   23
% 2.10/1.00  sup_bw_superposition:                   16
% 2.10/1.00  sup_immediate_simplified:               8
% 2.10/1.00  sup_given_eliminated:                   0
% 2.10/1.00  comparisons_done:                       0
% 2.10/1.00  comparisons_avoided:                    0
% 2.10/1.00  
% 2.10/1.00  ------ Simplifications
% 2.10/1.00  
% 2.10/1.00  
% 2.10/1.00  sim_fw_subset_subsumed:                 3
% 2.10/1.00  sim_bw_subset_subsumed:                 2
% 2.10/1.00  sim_fw_subsumed:                        2
% 2.10/1.00  sim_bw_subsumed:                        0
% 2.10/1.00  sim_fw_subsumption_res:                 4
% 2.10/1.00  sim_bw_subsumption_res:                 1
% 2.10/1.00  sim_tautology_del:                      2
% 2.10/1.00  sim_eq_tautology_del:                   2
% 2.10/1.00  sim_eq_res_simp:                        1
% 2.10/1.00  sim_fw_demodulated:                     2
% 2.10/1.00  sim_bw_demodulated:                     20
% 2.10/1.00  sim_light_normalised:                   8
% 2.10/1.00  sim_joinable_taut:                      0
% 2.10/1.00  sim_joinable_simp:                      0
% 2.10/1.00  sim_ac_normalised:                      0
% 2.10/1.00  sim_smt_subsumption:                    0
% 2.10/1.00  
%------------------------------------------------------------------------------
