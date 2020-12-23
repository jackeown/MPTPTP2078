%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:54 EST 2020

% Result     : Theorem 1.50s
% Output     : CNFRefutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 614 expanded)
%              Number of clauses        :   75 ( 165 expanded)
%              Number of leaves         :   17 ( 139 expanded)
%              Depth                    :   18
%              Number of atoms          :  364 (2129 expanded)
%              Number of equality atoms :  155 ( 681 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | k1_xboole_0 != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,X1) = k1_xboole_0
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(k1_funct_1(sK3,sK1),sK2)
      & k1_xboole_0 != sK2
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
      & v1_funct_2(sK3,k1_tarski(sK1),sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK1),sK2)
    & k1_xboole_0 != sK2
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
    & v1_funct_2(sK3,k1_tarski(sK1),sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f28])).

fof(f45,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f47,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f32,f33])).

fof(f51,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f31,f50])).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(definition_unfolding,[],[f47,f51])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <=> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
        | ~ r2_hidden(X1,X3)
        | X0 != X2 )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
        | ~ r2_hidden(X1,X3)
        | X0 != X2 )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(flattening,[],[f25])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3)) ) ),
    inference(definition_unfolding,[],[f36,f51])).

fof(f49,plain,(
    ~ r2_hidden(k1_funct_1(sK3,sK1),sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3)) ) ),
    inference(definition_unfolding,[],[f35,f51])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f14,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f23])).

fof(f30,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f19])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f46,plain,(
    v1_funct_2(sK3,k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f57,plain,(
    v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
    inference(definition_unfolding,[],[f46,f51])).

fof(f48,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f34,f50])).

cnf(c_6,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_16,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_277,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,X0) = k1_xboole_0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_16])).

cnf(c_278,plain,
    ( r2_hidden(X0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_277])).

cnf(c_749,plain,
    ( k1_funct_1(sK3,X0) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_278])).

cnf(c_279,plain,
    ( k1_funct_1(sK3,X0) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_278])).

cnf(c_508,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_844,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_508])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_225,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_14])).

cnf(c_226,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_225])).

cnf(c_845,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_226])).

cnf(c_846,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_845])).

cnf(c_1042,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
    | k1_funct_1(sK3,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_749,c_279,c_844,c_846])).

cnf(c_1043,plain,
    ( k1_funct_1(sK3,X0) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1042])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_244,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_16])).

cnf(c_245,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_244])).

cnf(c_751,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_245])).

cnf(c_246,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_245])).

cnf(c_915,plain,
    ( r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_751,c_246,c_844,c_846])).

cnf(c_916,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_915])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_210,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(X2)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_14])).

cnf(c_211,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(X1) ),
    inference(unflattening,[status(thm)],[c_210])).

cnf(c_753,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(X0)
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_211])).

cnf(c_927,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_753])).

cnf(c_3,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(k2_enumset1(X3,X3,X3,X3),X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_757,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(k2_enumset1(X3,X3,X3,X3),X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1207,plain,
    ( r2_hidden(X0,sK2) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_927,c_757])).

cnf(c_1582,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_916,c_1207])).

cnf(c_12,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(sK3,sK1),sK2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_755,plain,
    ( r2_hidden(k1_funct_1(sK3,sK1),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1590,plain,
    ( r2_hidden(sK1,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1582,c_755])).

cnf(c_1643,plain,
    ( k1_funct_1(sK3,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1043,c_1590])).

cnf(c_1704,plain,
    ( r2_hidden(k1_xboole_0,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1643,c_755])).

cnf(c_509,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1572,plain,
    ( X0 != X1
    | X0 = sK0(k2_enumset1(sK1,sK1,sK1,sK1))
    | sK0(k2_enumset1(sK1,sK1,sK1,sK1)) != X1 ),
    inference(instantiation,[status(thm)],[c_509])).

cnf(c_1573,plain,
    ( sK0(k2_enumset1(sK1,sK1,sK1,sK1)) != sK1
    | sK1 = sK0(k2_enumset1(sK1,sK1,sK1,sK1))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1572])).

cnf(c_4,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3))
    | X2 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_756,plain,
    ( X0 = X1
    | r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1208,plain,
    ( sK1 = X0
    | r2_hidden(k4_tarski(X0,X1),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_927,c_756])).

cnf(c_1316,plain,
    ( sK1 = X0
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_916,c_1208])).

cnf(c_1444,plain,
    ( k1_funct_1(sK3,X0) = k1_xboole_0
    | sK1 = X0 ),
    inference(superposition,[status(thm)],[c_1043,c_1316])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_760,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_15,negated_conjecture,
    ( v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_189,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k2_enumset1(sK1,sK1,sK1,sK1) != X1
    | sK2 != X2
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_15])).

cnf(c_190,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
    | ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
    | r2_hidden(k1_funct_1(sK3,X0),sK2)
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_189])).

cnf(c_13,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_194,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
    | r2_hidden(k1_funct_1(sK3,X0),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_190,c_16,c_14,c_13])).

cnf(c_754,plain,
    ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_194])).

cnf(c_1140,plain,
    ( r2_hidden(k1_funct_1(sK3,sK0(k2_enumset1(sK1,sK1,sK1,sK1))),sK2) = iProver_top
    | v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_760,c_754])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_179,plain,
    ( r2_hidden(sK0(X0),X0)
    | k2_enumset1(X1,X1,X1,X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_180,plain,
    ( r2_hidden(sK0(k2_enumset1(X0,X0,X0,X1)),k2_enumset1(X0,X0,X0,X1)) ),
    inference(unflattening,[status(thm)],[c_179])).

cnf(c_181,plain,
    ( r2_hidden(sK0(k2_enumset1(X0,X0,X0,X1)),k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_180])).

cnf(c_183,plain,
    ( r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_181])).

cnf(c_849,plain,
    ( r2_hidden(k1_funct_1(sK3,sK0(k2_enumset1(sK1,sK1,sK1,sK1))),sK2)
    | ~ r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_194])).

cnf(c_852,plain,
    ( r2_hidden(k1_funct_1(sK3,sK0(k2_enumset1(sK1,sK1,sK1,sK1))),sK2) = iProver_top
    | r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_849])).

cnf(c_1308,plain,
    ( r2_hidden(k1_funct_1(sK3,sK0(k2_enumset1(sK1,sK1,sK1,sK1))),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1140,c_183,c_852])).

cnf(c_1458,plain,
    ( sK0(k2_enumset1(sK1,sK1,sK1,sK1)) = sK1
    | r2_hidden(k1_xboole_0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1444,c_1308])).

cnf(c_511,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_871,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(X2),X2)
    | X1 != X2
    | X0 != sK0(X2) ),
    inference(instantiation,[status(thm)],[c_511])).

cnf(c_1117,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1))
    | X1 != k2_enumset1(sK1,sK1,sK1,sK1)
    | X0 != sK0(k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_871])).

cnf(c_1255,plain,
    ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1))
    | X0 != sK0(k2_enumset1(sK1,sK1,sK1,sK1))
    | k2_enumset1(sK1,sK1,sK1,sK1) != k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_1117])).

cnf(c_1258,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1))
    | r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1))
    | k2_enumset1(sK1,sK1,sK1,sK1) != k2_enumset1(sK1,sK1,sK1,sK1)
    | sK1 != sK0(k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_1255])).

cnf(c_529,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_508])).

cnf(c_512,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | k2_enumset1(X0,X2,X4,X6) = k2_enumset1(X1,X3,X5,X7) ),
    theory(equality)).

cnf(c_521,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k2_enumset1(sK1,sK1,sK1,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_512])).

cnf(c_192,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
    | r2_hidden(k1_funct_1(sK3,sK1),sK2)
    | ~ r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_190])).

cnf(c_182,plain,
    ( r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_180])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1704,c_1573,c_1458,c_1258,c_529,c_521,c_192,c_182,c_12,c_13,c_14,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n012.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 12:02:07 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 1.50/0.94  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.50/0.94  
% 1.50/0.94  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.50/0.94  
% 1.50/0.94  ------  iProver source info
% 1.50/0.94  
% 1.50/0.94  git: date: 2020-06-30 10:37:57 +0100
% 1.50/0.94  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.50/0.94  git: non_committed_changes: false
% 1.50/0.94  git: last_make_outside_of_git: false
% 1.50/0.94  
% 1.50/0.94  ------ 
% 1.50/0.94  
% 1.50/0.94  ------ Input Options
% 1.50/0.94  
% 1.50/0.94  --out_options                           all
% 1.50/0.94  --tptp_safe_out                         true
% 1.50/0.94  --problem_path                          ""
% 1.50/0.94  --include_path                          ""
% 1.50/0.94  --clausifier                            res/vclausify_rel
% 1.50/0.94  --clausifier_options                    --mode clausify
% 1.50/0.94  --stdin                                 false
% 1.50/0.94  --stats_out                             all
% 1.50/0.94  
% 1.50/0.94  ------ General Options
% 1.50/0.94  
% 1.50/0.94  --fof                                   false
% 1.50/0.94  --time_out_real                         305.
% 1.50/0.94  --time_out_virtual                      -1.
% 1.50/0.94  --symbol_type_check                     false
% 1.50/0.94  --clausify_out                          false
% 1.50/0.94  --sig_cnt_out                           false
% 1.50/0.95  --trig_cnt_out                          false
% 1.50/0.95  --trig_cnt_out_tolerance                1.
% 1.50/0.95  --trig_cnt_out_sk_spl                   false
% 1.50/0.95  --abstr_cl_out                          false
% 1.50/0.95  
% 1.50/0.95  ------ Global Options
% 1.50/0.95  
% 1.50/0.95  --schedule                              default
% 1.50/0.95  --add_important_lit                     false
% 1.50/0.95  --prop_solver_per_cl                    1000
% 1.50/0.95  --min_unsat_core                        false
% 1.50/0.95  --soft_assumptions                      false
% 1.50/0.95  --soft_lemma_size                       3
% 1.50/0.95  --prop_impl_unit_size                   0
% 1.50/0.95  --prop_impl_unit                        []
% 1.50/0.95  --share_sel_clauses                     true
% 1.50/0.95  --reset_solvers                         false
% 1.50/0.95  --bc_imp_inh                            [conj_cone]
% 1.50/0.95  --conj_cone_tolerance                   3.
% 1.50/0.95  --extra_neg_conj                        none
% 1.50/0.95  --large_theory_mode                     true
% 1.50/0.95  --prolific_symb_bound                   200
% 1.50/0.95  --lt_threshold                          2000
% 1.50/0.95  --clause_weak_htbl                      true
% 1.50/0.95  --gc_record_bc_elim                     false
% 1.50/0.95  
% 1.50/0.95  ------ Preprocessing Options
% 1.50/0.95  
% 1.50/0.95  --preprocessing_flag                    true
% 1.50/0.95  --time_out_prep_mult                    0.1
% 1.50/0.95  --splitting_mode                        input
% 1.50/0.95  --splitting_grd                         true
% 1.50/0.95  --splitting_cvd                         false
% 1.50/0.95  --splitting_cvd_svl                     false
% 1.50/0.95  --splitting_nvd                         32
% 1.50/0.95  --sub_typing                            true
% 1.50/0.95  --prep_gs_sim                           true
% 1.50/0.95  --prep_unflatten                        true
% 1.50/0.95  --prep_res_sim                          true
% 1.50/0.95  --prep_upred                            true
% 1.50/0.95  --prep_sem_filter                       exhaustive
% 1.50/0.95  --prep_sem_filter_out                   false
% 1.50/0.95  --pred_elim                             true
% 1.50/0.95  --res_sim_input                         true
% 1.50/0.95  --eq_ax_congr_red                       true
% 1.50/0.95  --pure_diseq_elim                       true
% 1.50/0.95  --brand_transform                       false
% 1.50/0.95  --non_eq_to_eq                          false
% 1.50/0.95  --prep_def_merge                        true
% 1.50/0.95  --prep_def_merge_prop_impl              false
% 1.50/0.95  --prep_def_merge_mbd                    true
% 1.50/0.95  --prep_def_merge_tr_red                 false
% 1.50/0.95  --prep_def_merge_tr_cl                  false
% 1.50/0.95  --smt_preprocessing                     true
% 1.50/0.95  --smt_ac_axioms                         fast
% 1.50/0.95  --preprocessed_out                      false
% 1.50/0.95  --preprocessed_stats                    false
% 1.50/0.95  
% 1.50/0.95  ------ Abstraction refinement Options
% 1.50/0.95  
% 1.50/0.95  --abstr_ref                             []
% 1.50/0.95  --abstr_ref_prep                        false
% 1.50/0.95  --abstr_ref_until_sat                   false
% 1.50/0.95  --abstr_ref_sig_restrict                funpre
% 1.50/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 1.50/0.95  --abstr_ref_under                       []
% 1.50/0.95  
% 1.50/0.95  ------ SAT Options
% 1.50/0.95  
% 1.50/0.95  --sat_mode                              false
% 1.50/0.95  --sat_fm_restart_options                ""
% 1.50/0.95  --sat_gr_def                            false
% 1.50/0.95  --sat_epr_types                         true
% 1.50/0.95  --sat_non_cyclic_types                  false
% 1.50/0.95  --sat_finite_models                     false
% 1.50/0.95  --sat_fm_lemmas                         false
% 1.50/0.95  --sat_fm_prep                           false
% 1.50/0.95  --sat_fm_uc_incr                        true
% 1.50/0.95  --sat_out_model                         small
% 1.50/0.95  --sat_out_clauses                       false
% 1.50/0.95  
% 1.50/0.95  ------ QBF Options
% 1.50/0.95  
% 1.50/0.95  --qbf_mode                              false
% 1.50/0.95  --qbf_elim_univ                         false
% 1.50/0.95  --qbf_dom_inst                          none
% 1.50/0.95  --qbf_dom_pre_inst                      false
% 1.50/0.95  --qbf_sk_in                             false
% 1.50/0.95  --qbf_pred_elim                         true
% 1.50/0.95  --qbf_split                             512
% 1.50/0.95  
% 1.50/0.95  ------ BMC1 Options
% 1.50/0.95  
% 1.50/0.95  --bmc1_incremental                      false
% 1.50/0.95  --bmc1_axioms                           reachable_all
% 1.50/0.95  --bmc1_min_bound                        0
% 1.50/0.95  --bmc1_max_bound                        -1
% 1.50/0.95  --bmc1_max_bound_default                -1
% 1.50/0.95  --bmc1_symbol_reachability              true
% 1.50/0.95  --bmc1_property_lemmas                  false
% 1.50/0.95  --bmc1_k_induction                      false
% 1.50/0.95  --bmc1_non_equiv_states                 false
% 1.50/0.95  --bmc1_deadlock                         false
% 1.50/0.95  --bmc1_ucm                              false
% 1.50/0.95  --bmc1_add_unsat_core                   none
% 1.50/0.95  --bmc1_unsat_core_children              false
% 1.50/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 1.50/0.95  --bmc1_out_stat                         full
% 1.50/0.95  --bmc1_ground_init                      false
% 1.50/0.95  --bmc1_pre_inst_next_state              false
% 1.50/0.95  --bmc1_pre_inst_state                   false
% 1.50/0.95  --bmc1_pre_inst_reach_state             false
% 1.50/0.95  --bmc1_out_unsat_core                   false
% 1.50/0.95  --bmc1_aig_witness_out                  false
% 1.50/0.95  --bmc1_verbose                          false
% 1.50/0.95  --bmc1_dump_clauses_tptp                false
% 1.50/0.95  --bmc1_dump_unsat_core_tptp             false
% 1.50/0.95  --bmc1_dump_file                        -
% 1.50/0.95  --bmc1_ucm_expand_uc_limit              128
% 1.50/0.95  --bmc1_ucm_n_expand_iterations          6
% 1.50/0.95  --bmc1_ucm_extend_mode                  1
% 1.50/0.95  --bmc1_ucm_init_mode                    2
% 1.50/0.95  --bmc1_ucm_cone_mode                    none
% 1.50/0.95  --bmc1_ucm_reduced_relation_type        0
% 1.50/0.95  --bmc1_ucm_relax_model                  4
% 1.50/0.95  --bmc1_ucm_full_tr_after_sat            true
% 1.50/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 1.50/0.95  --bmc1_ucm_layered_model                none
% 1.50/0.95  --bmc1_ucm_max_lemma_size               10
% 1.50/0.95  
% 1.50/0.95  ------ AIG Options
% 1.50/0.95  
% 1.50/0.95  --aig_mode                              false
% 1.50/0.95  
% 1.50/0.95  ------ Instantiation Options
% 1.50/0.95  
% 1.50/0.95  --instantiation_flag                    true
% 1.50/0.95  --inst_sos_flag                         false
% 1.50/0.95  --inst_sos_phase                        true
% 1.50/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.50/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.50/0.95  --inst_lit_sel_side                     num_symb
% 1.50/0.95  --inst_solver_per_active                1400
% 1.50/0.95  --inst_solver_calls_frac                1.
% 1.50/0.95  --inst_passive_queue_type               priority_queues
% 1.50/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.50/0.95  --inst_passive_queues_freq              [25;2]
% 1.50/0.95  --inst_dismatching                      true
% 1.50/0.95  --inst_eager_unprocessed_to_passive     true
% 1.50/0.95  --inst_prop_sim_given                   true
% 1.50/0.95  --inst_prop_sim_new                     false
% 1.50/0.95  --inst_subs_new                         false
% 1.50/0.95  --inst_eq_res_simp                      false
% 1.50/0.95  --inst_subs_given                       false
% 1.50/0.95  --inst_orphan_elimination               true
% 1.50/0.95  --inst_learning_loop_flag               true
% 1.50/0.95  --inst_learning_start                   3000
% 1.50/0.95  --inst_learning_factor                  2
% 1.50/0.95  --inst_start_prop_sim_after_learn       3
% 1.50/0.95  --inst_sel_renew                        solver
% 1.50/0.95  --inst_lit_activity_flag                true
% 1.50/0.95  --inst_restr_to_given                   false
% 1.50/0.95  --inst_activity_threshold               500
% 1.50/0.95  --inst_out_proof                        true
% 1.50/0.95  
% 1.50/0.95  ------ Resolution Options
% 1.50/0.95  
% 1.50/0.95  --resolution_flag                       true
% 1.50/0.95  --res_lit_sel                           adaptive
% 1.50/0.95  --res_lit_sel_side                      none
% 1.50/0.95  --res_ordering                          kbo
% 1.50/0.95  --res_to_prop_solver                    active
% 1.50/0.95  --res_prop_simpl_new                    false
% 1.50/0.95  --res_prop_simpl_given                  true
% 1.50/0.95  --res_passive_queue_type                priority_queues
% 1.50/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.50/0.95  --res_passive_queues_freq               [15;5]
% 1.50/0.95  --res_forward_subs                      full
% 1.50/0.95  --res_backward_subs                     full
% 1.50/0.95  --res_forward_subs_resolution           true
% 1.50/0.95  --res_backward_subs_resolution          true
% 1.50/0.95  --res_orphan_elimination                true
% 1.50/0.95  --res_time_limit                        2.
% 1.50/0.95  --res_out_proof                         true
% 1.50/0.95  
% 1.50/0.95  ------ Superposition Options
% 1.50/0.95  
% 1.50/0.95  --superposition_flag                    true
% 1.50/0.95  --sup_passive_queue_type                priority_queues
% 1.50/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.50/0.95  --sup_passive_queues_freq               [8;1;4]
% 1.50/0.95  --demod_completeness_check              fast
% 1.50/0.95  --demod_use_ground                      true
% 1.50/0.95  --sup_to_prop_solver                    passive
% 1.50/0.95  --sup_prop_simpl_new                    true
% 1.50/0.95  --sup_prop_simpl_given                  true
% 1.50/0.95  --sup_fun_splitting                     false
% 1.50/0.95  --sup_smt_interval                      50000
% 1.50/0.95  
% 1.50/0.95  ------ Superposition Simplification Setup
% 1.50/0.95  
% 1.50/0.95  --sup_indices_passive                   []
% 1.50/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.50/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.50/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.50/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 1.50/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.50/0.95  --sup_full_bw                           [BwDemod]
% 1.50/0.95  --sup_immed_triv                        [TrivRules]
% 1.50/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.50/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.50/0.95  --sup_immed_bw_main                     []
% 1.50/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.50/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 1.50/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.50/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.50/0.95  
% 1.50/0.95  ------ Combination Options
% 1.50/0.95  
% 1.50/0.95  --comb_res_mult                         3
% 1.50/0.95  --comb_sup_mult                         2
% 1.50/0.95  --comb_inst_mult                        10
% 1.50/0.95  
% 1.50/0.95  ------ Debug Options
% 1.50/0.95  
% 1.50/0.95  --dbg_backtrace                         false
% 1.50/0.95  --dbg_dump_prop_clauses                 false
% 1.50/0.95  --dbg_dump_prop_clauses_file            -
% 1.50/0.95  --dbg_out_stat                          false
% 1.50/0.95  ------ Parsing...
% 1.50/0.95  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.50/0.95  
% 1.50/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.50/0.95  
% 1.50/0.95  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.50/0.95  
% 1.50/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.50/0.95  ------ Proving...
% 1.50/0.95  ------ Problem Properties 
% 1.50/0.95  
% 1.50/0.95  
% 1.50/0.95  clauses                                 13
% 1.50/0.95  conjectures                             2
% 1.50/0.95  EPR                                     1
% 1.50/0.95  Horn                                    11
% 1.50/0.95  unary                                   3
% 1.50/0.95  binary                                  6
% 1.50/0.95  lits                                    28
% 1.50/0.95  lits eq                                 6
% 1.50/0.95  fd_pure                                 0
% 1.50/0.95  fd_pseudo                               0
% 1.50/0.95  fd_cond                                 0
% 1.50/0.95  fd_pseudo_cond                          2
% 1.50/0.95  AC symbols                              0
% 1.50/0.95  
% 1.50/0.95  ------ Schedule dynamic 5 is on 
% 1.50/0.95  
% 1.50/0.95  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.50/0.95  
% 1.50/0.95  
% 1.50/0.95  ------ 
% 1.50/0.95  Current options:
% 1.50/0.95  ------ 
% 1.50/0.95  
% 1.50/0.95  ------ Input Options
% 1.50/0.95  
% 1.50/0.95  --out_options                           all
% 1.50/0.95  --tptp_safe_out                         true
% 1.50/0.95  --problem_path                          ""
% 1.50/0.95  --include_path                          ""
% 1.50/0.95  --clausifier                            res/vclausify_rel
% 1.50/0.95  --clausifier_options                    --mode clausify
% 1.50/0.95  --stdin                                 false
% 1.50/0.95  --stats_out                             all
% 1.50/0.95  
% 1.50/0.95  ------ General Options
% 1.50/0.95  
% 1.50/0.95  --fof                                   false
% 1.50/0.95  --time_out_real                         305.
% 1.50/0.95  --time_out_virtual                      -1.
% 1.50/0.95  --symbol_type_check                     false
% 1.50/0.95  --clausify_out                          false
% 1.50/0.95  --sig_cnt_out                           false
% 1.50/0.95  --trig_cnt_out                          false
% 1.50/0.95  --trig_cnt_out_tolerance                1.
% 1.50/0.95  --trig_cnt_out_sk_spl                   false
% 1.50/0.95  --abstr_cl_out                          false
% 1.50/0.95  
% 1.50/0.95  ------ Global Options
% 1.50/0.95  
% 1.50/0.95  --schedule                              default
% 1.50/0.95  --add_important_lit                     false
% 1.50/0.95  --prop_solver_per_cl                    1000
% 1.50/0.95  --min_unsat_core                        false
% 1.50/0.95  --soft_assumptions                      false
% 1.50/0.95  --soft_lemma_size                       3
% 1.50/0.95  --prop_impl_unit_size                   0
% 1.50/0.95  --prop_impl_unit                        []
% 1.50/0.95  --share_sel_clauses                     true
% 1.50/0.95  --reset_solvers                         false
% 1.50/0.95  --bc_imp_inh                            [conj_cone]
% 1.50/0.95  --conj_cone_tolerance                   3.
% 1.50/0.95  --extra_neg_conj                        none
% 1.50/0.95  --large_theory_mode                     true
% 1.50/0.95  --prolific_symb_bound                   200
% 1.50/0.95  --lt_threshold                          2000
% 1.50/0.95  --clause_weak_htbl                      true
% 1.50/0.95  --gc_record_bc_elim                     false
% 1.50/0.95  
% 1.50/0.95  ------ Preprocessing Options
% 1.50/0.95  
% 1.50/0.95  --preprocessing_flag                    true
% 1.50/0.95  --time_out_prep_mult                    0.1
% 1.50/0.95  --splitting_mode                        input
% 1.50/0.95  --splitting_grd                         true
% 1.50/0.95  --splitting_cvd                         false
% 1.50/0.95  --splitting_cvd_svl                     false
% 1.50/0.95  --splitting_nvd                         32
% 1.50/0.95  --sub_typing                            true
% 1.50/0.95  --prep_gs_sim                           true
% 1.50/0.95  --prep_unflatten                        true
% 1.50/0.95  --prep_res_sim                          true
% 1.50/0.95  --prep_upred                            true
% 1.50/0.95  --prep_sem_filter                       exhaustive
% 1.50/0.95  --prep_sem_filter_out                   false
% 1.50/0.95  --pred_elim                             true
% 1.50/0.95  --res_sim_input                         true
% 1.50/0.95  --eq_ax_congr_red                       true
% 1.50/0.95  --pure_diseq_elim                       true
% 1.50/0.95  --brand_transform                       false
% 1.50/0.95  --non_eq_to_eq                          false
% 1.50/0.95  --prep_def_merge                        true
% 1.50/0.95  --prep_def_merge_prop_impl              false
% 1.50/0.95  --prep_def_merge_mbd                    true
% 1.50/0.95  --prep_def_merge_tr_red                 false
% 1.50/0.95  --prep_def_merge_tr_cl                  false
% 1.50/0.95  --smt_preprocessing                     true
% 1.50/0.95  --smt_ac_axioms                         fast
% 1.50/0.95  --preprocessed_out                      false
% 1.50/0.95  --preprocessed_stats                    false
% 1.50/0.95  
% 1.50/0.95  ------ Abstraction refinement Options
% 1.50/0.95  
% 1.50/0.95  --abstr_ref                             []
% 1.50/0.95  --abstr_ref_prep                        false
% 1.50/0.95  --abstr_ref_until_sat                   false
% 1.50/0.95  --abstr_ref_sig_restrict                funpre
% 1.50/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 1.50/0.95  --abstr_ref_under                       []
% 1.50/0.95  
% 1.50/0.95  ------ SAT Options
% 1.50/0.95  
% 1.50/0.95  --sat_mode                              false
% 1.50/0.95  --sat_fm_restart_options                ""
% 1.50/0.95  --sat_gr_def                            false
% 1.50/0.95  --sat_epr_types                         true
% 1.50/0.95  --sat_non_cyclic_types                  false
% 1.50/0.95  --sat_finite_models                     false
% 1.50/0.95  --sat_fm_lemmas                         false
% 1.50/0.95  --sat_fm_prep                           false
% 1.50/0.95  --sat_fm_uc_incr                        true
% 1.50/0.95  --sat_out_model                         small
% 1.50/0.95  --sat_out_clauses                       false
% 1.50/0.95  
% 1.50/0.95  ------ QBF Options
% 1.50/0.95  
% 1.50/0.95  --qbf_mode                              false
% 1.50/0.95  --qbf_elim_univ                         false
% 1.50/0.95  --qbf_dom_inst                          none
% 1.50/0.95  --qbf_dom_pre_inst                      false
% 1.50/0.95  --qbf_sk_in                             false
% 1.50/0.95  --qbf_pred_elim                         true
% 1.50/0.95  --qbf_split                             512
% 1.50/0.95  
% 1.50/0.95  ------ BMC1 Options
% 1.50/0.95  
% 1.50/0.95  --bmc1_incremental                      false
% 1.50/0.95  --bmc1_axioms                           reachable_all
% 1.50/0.95  --bmc1_min_bound                        0
% 1.50/0.95  --bmc1_max_bound                        -1
% 1.50/0.95  --bmc1_max_bound_default                -1
% 1.50/0.95  --bmc1_symbol_reachability              true
% 1.50/0.95  --bmc1_property_lemmas                  false
% 1.50/0.95  --bmc1_k_induction                      false
% 1.50/0.95  --bmc1_non_equiv_states                 false
% 1.50/0.95  --bmc1_deadlock                         false
% 1.50/0.95  --bmc1_ucm                              false
% 1.50/0.95  --bmc1_add_unsat_core                   none
% 1.50/0.95  --bmc1_unsat_core_children              false
% 1.50/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 1.50/0.95  --bmc1_out_stat                         full
% 1.50/0.95  --bmc1_ground_init                      false
% 1.50/0.95  --bmc1_pre_inst_next_state              false
% 1.50/0.95  --bmc1_pre_inst_state                   false
% 1.50/0.95  --bmc1_pre_inst_reach_state             false
% 1.50/0.95  --bmc1_out_unsat_core                   false
% 1.50/0.95  --bmc1_aig_witness_out                  false
% 1.50/0.95  --bmc1_verbose                          false
% 1.50/0.95  --bmc1_dump_clauses_tptp                false
% 1.50/0.95  --bmc1_dump_unsat_core_tptp             false
% 1.50/0.95  --bmc1_dump_file                        -
% 1.50/0.95  --bmc1_ucm_expand_uc_limit              128
% 1.50/0.95  --bmc1_ucm_n_expand_iterations          6
% 1.50/0.95  --bmc1_ucm_extend_mode                  1
% 1.50/0.95  --bmc1_ucm_init_mode                    2
% 1.50/0.95  --bmc1_ucm_cone_mode                    none
% 1.50/0.95  --bmc1_ucm_reduced_relation_type        0
% 1.50/0.95  --bmc1_ucm_relax_model                  4
% 1.50/0.95  --bmc1_ucm_full_tr_after_sat            true
% 1.50/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 1.50/0.95  --bmc1_ucm_layered_model                none
% 1.50/0.95  --bmc1_ucm_max_lemma_size               10
% 1.50/0.95  
% 1.50/0.95  ------ AIG Options
% 1.50/0.95  
% 1.50/0.95  --aig_mode                              false
% 1.50/0.95  
% 1.50/0.95  ------ Instantiation Options
% 1.50/0.95  
% 1.50/0.95  --instantiation_flag                    true
% 1.50/0.95  --inst_sos_flag                         false
% 1.50/0.95  --inst_sos_phase                        true
% 1.50/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.50/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.50/0.95  --inst_lit_sel_side                     none
% 1.50/0.95  --inst_solver_per_active                1400
% 1.50/0.95  --inst_solver_calls_frac                1.
% 1.50/0.95  --inst_passive_queue_type               priority_queues
% 1.50/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.50/0.95  --inst_passive_queues_freq              [25;2]
% 1.50/0.95  --inst_dismatching                      true
% 1.50/0.95  --inst_eager_unprocessed_to_passive     true
% 1.50/0.95  --inst_prop_sim_given                   true
% 1.50/0.95  --inst_prop_sim_new                     false
% 1.50/0.95  --inst_subs_new                         false
% 1.50/0.95  --inst_eq_res_simp                      false
% 1.50/0.95  --inst_subs_given                       false
% 1.50/0.95  --inst_orphan_elimination               true
% 1.50/0.95  --inst_learning_loop_flag               true
% 1.50/0.95  --inst_learning_start                   3000
% 1.50/0.95  --inst_learning_factor                  2
% 1.50/0.95  --inst_start_prop_sim_after_learn       3
% 1.50/0.95  --inst_sel_renew                        solver
% 1.50/0.95  --inst_lit_activity_flag                true
% 1.50/0.95  --inst_restr_to_given                   false
% 1.50/0.95  --inst_activity_threshold               500
% 1.50/0.95  --inst_out_proof                        true
% 1.50/0.95  
% 1.50/0.95  ------ Resolution Options
% 1.50/0.95  
% 1.50/0.95  --resolution_flag                       false
% 1.50/0.95  --res_lit_sel                           adaptive
% 1.50/0.95  --res_lit_sel_side                      none
% 1.50/0.95  --res_ordering                          kbo
% 1.50/0.95  --res_to_prop_solver                    active
% 1.50/0.95  --res_prop_simpl_new                    false
% 1.50/0.95  --res_prop_simpl_given                  true
% 1.50/0.95  --res_passive_queue_type                priority_queues
% 1.50/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.50/0.95  --res_passive_queues_freq               [15;5]
% 1.50/0.95  --res_forward_subs                      full
% 1.50/0.95  --res_backward_subs                     full
% 1.50/0.95  --res_forward_subs_resolution           true
% 1.50/0.95  --res_backward_subs_resolution          true
% 1.50/0.95  --res_orphan_elimination                true
% 1.50/0.95  --res_time_limit                        2.
% 1.50/0.95  --res_out_proof                         true
% 1.50/0.95  
% 1.50/0.95  ------ Superposition Options
% 1.50/0.95  
% 1.50/0.95  --superposition_flag                    true
% 1.50/0.95  --sup_passive_queue_type                priority_queues
% 1.50/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.50/0.95  --sup_passive_queues_freq               [8;1;4]
% 1.50/0.95  --demod_completeness_check              fast
% 1.50/0.95  --demod_use_ground                      true
% 1.50/0.95  --sup_to_prop_solver                    passive
% 1.50/0.95  --sup_prop_simpl_new                    true
% 1.50/0.95  --sup_prop_simpl_given                  true
% 1.50/0.95  --sup_fun_splitting                     false
% 1.50/0.95  --sup_smt_interval                      50000
% 1.50/0.95  
% 1.50/0.95  ------ Superposition Simplification Setup
% 1.50/0.95  
% 1.50/0.95  --sup_indices_passive                   []
% 1.50/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.50/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.50/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.50/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 1.50/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.50/0.95  --sup_full_bw                           [BwDemod]
% 1.50/0.95  --sup_immed_triv                        [TrivRules]
% 1.50/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.50/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.50/0.95  --sup_immed_bw_main                     []
% 1.50/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.50/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 1.50/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.50/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.50/0.95  
% 1.50/0.95  ------ Combination Options
% 1.50/0.95  
% 1.50/0.95  --comb_res_mult                         3
% 1.50/0.95  --comb_sup_mult                         2
% 1.50/0.95  --comb_inst_mult                        10
% 1.50/0.95  
% 1.50/0.95  ------ Debug Options
% 1.50/0.95  
% 1.50/0.95  --dbg_backtrace                         false
% 1.50/0.95  --dbg_dump_prop_clauses                 false
% 1.50/0.95  --dbg_dump_prop_clauses_file            -
% 1.50/0.95  --dbg_out_stat                          false
% 1.50/0.95  
% 1.50/0.95  
% 1.50/0.95  
% 1.50/0.95  
% 1.50/0.95  ------ Proving...
% 1.50/0.95  
% 1.50/0.95  
% 1.50/0.95  % SZS status Theorem for theBenchmark.p
% 1.50/0.95  
% 1.50/0.95  % SZS output start CNFRefutation for theBenchmark.p
% 1.50/0.95  
% 1.50/0.95  fof(f8,axiom,(
% 1.50/0.95    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 1.50/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.50/0.95  
% 1.50/0.95  fof(f16,plain,(
% 1.50/0.95    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.50/0.95    inference(ennf_transformation,[],[f8])).
% 1.50/0.95  
% 1.50/0.95  fof(f17,plain,(
% 1.50/0.95    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.50/0.95    inference(flattening,[],[f16])).
% 1.50/0.95  
% 1.50/0.95  fof(f27,plain,(
% 1.50/0.95    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.50/0.95    inference(nnf_transformation,[],[f17])).
% 1.50/0.95  
% 1.50/0.95  fof(f42,plain,(
% 1.50/0.95    ( ! [X2,X0,X1] : (k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2 | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.50/0.95    inference(cnf_transformation,[],[f27])).
% 1.50/0.95  
% 1.50/0.95  fof(f59,plain,(
% 1.50/0.95    ( ! [X0,X1] : (k1_funct_1(X0,X1) = k1_xboole_0 | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.50/0.95    inference(equality_resolution,[],[f42])).
% 1.50/0.95  
% 1.50/0.95  fof(f11,conjecture,(
% 1.50/0.95    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 1.50/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.50/0.95  
% 1.50/0.95  fof(f12,negated_conjecture,(
% 1.50/0.95    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 1.50/0.95    inference(negated_conjecture,[],[f11])).
% 1.50/0.95  
% 1.50/0.95  fof(f21,plain,(
% 1.50/0.95    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 1.50/0.95    inference(ennf_transformation,[],[f12])).
% 1.50/0.95  
% 1.50/0.95  fof(f22,plain,(
% 1.50/0.95    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 1.50/0.95    inference(flattening,[],[f21])).
% 1.50/0.95  
% 1.50/0.95  fof(f28,plain,(
% 1.50/0.95    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK3,sK1),sK2) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3))),
% 1.50/0.95    introduced(choice_axiom,[])).
% 1.50/0.95  
% 1.50/0.95  fof(f29,plain,(
% 1.50/0.95    ~r2_hidden(k1_funct_1(sK3,sK1),sK2) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3)),
% 1.50/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f28])).
% 1.50/0.95  
% 1.50/0.95  fof(f45,plain,(
% 1.50/0.95    v1_funct_1(sK3)),
% 1.50/0.95    inference(cnf_transformation,[],[f29])).
% 1.50/0.95  
% 1.50/0.95  fof(f9,axiom,(
% 1.50/0.95    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.50/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.50/0.95  
% 1.50/0.95  fof(f18,plain,(
% 1.50/0.95    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.95    inference(ennf_transformation,[],[f9])).
% 1.50/0.95  
% 1.50/0.95  fof(f43,plain,(
% 1.50/0.95    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.50/0.95    inference(cnf_transformation,[],[f18])).
% 1.50/0.95  
% 1.50/0.95  fof(f47,plain,(
% 1.50/0.95    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 1.50/0.95    inference(cnf_transformation,[],[f29])).
% 1.50/0.95  
% 1.50/0.95  fof(f2,axiom,(
% 1.50/0.95    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.50/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.50/0.95  
% 1.50/0.95  fof(f31,plain,(
% 1.50/0.95    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.50/0.95    inference(cnf_transformation,[],[f2])).
% 1.50/0.95  
% 1.50/0.95  fof(f3,axiom,(
% 1.50/0.95    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.50/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.50/0.95  
% 1.50/0.95  fof(f32,plain,(
% 1.50/0.95    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.50/0.95    inference(cnf_transformation,[],[f3])).
% 1.50/0.95  
% 1.50/0.95  fof(f4,axiom,(
% 1.50/0.95    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.50/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.50/0.95  
% 1.50/0.95  fof(f33,plain,(
% 1.50/0.95    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.50/0.95    inference(cnf_transformation,[],[f4])).
% 1.50/0.95  
% 1.50/0.95  fof(f50,plain,(
% 1.50/0.95    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.50/0.95    inference(definition_unfolding,[],[f32,f33])).
% 1.50/0.95  
% 1.50/0.95  fof(f51,plain,(
% 1.50/0.95    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.50/0.95    inference(definition_unfolding,[],[f31,f50])).
% 1.50/0.95  
% 1.50/0.95  fof(f56,plain,(
% 1.50/0.95    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))),
% 1.50/0.95    inference(definition_unfolding,[],[f47,f51])).
% 1.50/0.95  
% 1.50/0.95  fof(f39,plain,(
% 1.50/0.95    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2 | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.50/0.95    inference(cnf_transformation,[],[f27])).
% 1.50/0.95  
% 1.50/0.95  fof(f61,plain,(
% 1.50/0.95    ( ! [X0,X1] : (r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.50/0.95    inference(equality_resolution,[],[f39])).
% 1.50/0.95  
% 1.50/0.95  fof(f7,axiom,(
% 1.50/0.95    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.50/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.50/0.95  
% 1.50/0.95  fof(f15,plain,(
% 1.50/0.95    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.50/0.95    inference(ennf_transformation,[],[f7])).
% 1.50/0.95  
% 1.50/0.95  fof(f38,plain,(
% 1.50/0.95    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.50/0.95    inference(cnf_transformation,[],[f15])).
% 1.50/0.95  
% 1.50/0.95  fof(f6,axiom,(
% 1.50/0.95    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <=> (r2_hidden(X1,X3) & X0 = X2))),
% 1.50/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.50/0.95  
% 1.50/0.95  fof(f25,plain,(
% 1.50/0.95    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | (~r2_hidden(X1,X3) | X0 != X2)) & ((r2_hidden(X1,X3) & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 1.50/0.95    inference(nnf_transformation,[],[f6])).
% 1.50/0.95  
% 1.50/0.95  fof(f26,plain,(
% 1.50/0.95    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | ~r2_hidden(X1,X3) | X0 != X2) & ((r2_hidden(X1,X3) & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 1.50/0.95    inference(flattening,[],[f25])).
% 1.50/0.95  
% 1.50/0.95  fof(f36,plain,(
% 1.50/0.95    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))) )),
% 1.50/0.95    inference(cnf_transformation,[],[f26])).
% 1.50/0.95  
% 1.50/0.95  fof(f54,plain,(
% 1.50/0.95    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3))) )),
% 1.50/0.95    inference(definition_unfolding,[],[f36,f51])).
% 1.50/0.95  
% 1.50/0.95  fof(f49,plain,(
% 1.50/0.95    ~r2_hidden(k1_funct_1(sK3,sK1),sK2)),
% 1.50/0.95    inference(cnf_transformation,[],[f29])).
% 1.50/0.95  
% 1.50/0.95  fof(f35,plain,(
% 1.50/0.95    ( ! [X2,X0,X3,X1] : (X0 = X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))) )),
% 1.50/0.95    inference(cnf_transformation,[],[f26])).
% 1.50/0.95  
% 1.50/0.95  fof(f55,plain,(
% 1.50/0.95    ( ! [X2,X0,X3,X1] : (X0 = X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3))) )),
% 1.50/0.95    inference(definition_unfolding,[],[f35,f51])).
% 1.50/0.95  
% 1.50/0.95  fof(f1,axiom,(
% 1.50/0.95    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.50/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.50/0.95  
% 1.50/0.95  fof(f13,plain,(
% 1.50/0.95    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 1.50/0.95    inference(unused_predicate_definition_removal,[],[f1])).
% 1.50/0.95  
% 1.50/0.95  fof(f14,plain,(
% 1.50/0.95    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 1.50/0.95    inference(ennf_transformation,[],[f13])).
% 1.50/0.95  
% 1.50/0.95  fof(f23,plain,(
% 1.50/0.95    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.50/0.95    introduced(choice_axiom,[])).
% 1.50/0.95  
% 1.50/0.95  fof(f24,plain,(
% 1.50/0.95    ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0))),
% 1.50/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f23])).
% 1.50/0.95  
% 1.50/0.95  fof(f30,plain,(
% 1.50/0.95    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 1.50/0.95    inference(cnf_transformation,[],[f24])).
% 1.50/0.95  
% 1.50/0.95  fof(f10,axiom,(
% 1.50/0.95    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 1.50/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.50/0.95  
% 1.50/0.95  fof(f19,plain,(
% 1.50/0.95    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.50/0.95    inference(ennf_transformation,[],[f10])).
% 1.50/0.95  
% 1.50/0.95  fof(f20,plain,(
% 1.50/0.95    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.50/0.95    inference(flattening,[],[f19])).
% 1.50/0.95  
% 1.50/0.95  fof(f44,plain,(
% 1.50/0.95    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.50/0.95    inference(cnf_transformation,[],[f20])).
% 1.50/0.95  
% 1.50/0.95  fof(f46,plain,(
% 1.50/0.95    v1_funct_2(sK3,k1_tarski(sK1),sK2)),
% 1.50/0.95    inference(cnf_transformation,[],[f29])).
% 1.50/0.95  
% 1.50/0.95  fof(f57,plain,(
% 1.50/0.95    v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2)),
% 1.50/0.95    inference(definition_unfolding,[],[f46,f51])).
% 1.50/0.95  
% 1.50/0.95  fof(f48,plain,(
% 1.50/0.95    k1_xboole_0 != sK2),
% 1.50/0.95    inference(cnf_transformation,[],[f29])).
% 1.50/0.95  
% 1.50/0.95  fof(f5,axiom,(
% 1.50/0.95    ! [X0,X1] : ~v1_xboole_0(k2_tarski(X0,X1))),
% 1.50/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.50/0.95  
% 1.50/0.95  fof(f34,plain,(
% 1.50/0.95    ( ! [X0,X1] : (~v1_xboole_0(k2_tarski(X0,X1))) )),
% 1.50/0.95    inference(cnf_transformation,[],[f5])).
% 1.50/0.95  
% 1.50/0.95  fof(f52,plain,(
% 1.50/0.95    ( ! [X0,X1] : (~v1_xboole_0(k2_enumset1(X0,X0,X0,X1))) )),
% 1.50/0.95    inference(definition_unfolding,[],[f34,f50])).
% 1.50/0.95  
% 1.50/0.95  cnf(c_6,plain,
% 1.50/0.95      ( r2_hidden(X0,k1_relat_1(X1))
% 1.50/0.95      | ~ v1_relat_1(X1)
% 1.50/0.95      | ~ v1_funct_1(X1)
% 1.50/0.95      | k1_funct_1(X1,X0) = k1_xboole_0 ),
% 1.50/0.95      inference(cnf_transformation,[],[f59]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_16,negated_conjecture,
% 1.50/0.95      ( v1_funct_1(sK3) ),
% 1.50/0.95      inference(cnf_transformation,[],[f45]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_277,plain,
% 1.50/0.95      ( r2_hidden(X0,k1_relat_1(X1))
% 1.50/0.95      | ~ v1_relat_1(X1)
% 1.50/0.95      | k1_funct_1(X1,X0) = k1_xboole_0
% 1.50/0.95      | sK3 != X1 ),
% 1.50/0.95      inference(resolution_lifted,[status(thm)],[c_6,c_16]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_278,plain,
% 1.50/0.95      ( r2_hidden(X0,k1_relat_1(sK3))
% 1.50/0.95      | ~ v1_relat_1(sK3)
% 1.50/0.95      | k1_funct_1(sK3,X0) = k1_xboole_0 ),
% 1.50/0.95      inference(unflattening,[status(thm)],[c_277]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_749,plain,
% 1.50/0.95      ( k1_funct_1(sK3,X0) = k1_xboole_0
% 1.50/0.95      | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
% 1.50/0.95      | v1_relat_1(sK3) != iProver_top ),
% 1.50/0.95      inference(predicate_to_equality,[status(thm)],[c_278]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_279,plain,
% 1.50/0.95      ( k1_funct_1(sK3,X0) = k1_xboole_0
% 1.50/0.95      | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
% 1.50/0.95      | v1_relat_1(sK3) != iProver_top ),
% 1.50/0.95      inference(predicate_to_equality,[status(thm)],[c_278]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_508,plain,( X0 = X0 ),theory(equality) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_844,plain,
% 1.50/0.95      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
% 1.50/0.95      inference(instantiation,[status(thm)],[c_508]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_10,plain,
% 1.50/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.50/0.95      | v1_relat_1(X0) ),
% 1.50/0.95      inference(cnf_transformation,[],[f43]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_14,negated_conjecture,
% 1.50/0.95      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
% 1.50/0.95      inference(cnf_transformation,[],[f56]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_225,plain,
% 1.50/0.95      ( v1_relat_1(X0)
% 1.50/0.95      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.50/0.95      | sK3 != X0 ),
% 1.50/0.95      inference(resolution_lifted,[status(thm)],[c_10,c_14]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_226,plain,
% 1.50/0.95      ( v1_relat_1(sK3)
% 1.50/0.95      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.50/0.95      inference(unflattening,[status(thm)],[c_225]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_845,plain,
% 1.50/0.95      ( v1_relat_1(sK3)
% 1.50/0.95      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
% 1.50/0.95      inference(instantiation,[status(thm)],[c_226]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_846,plain,
% 1.50/0.95      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
% 1.50/0.95      | v1_relat_1(sK3) = iProver_top ),
% 1.50/0.95      inference(predicate_to_equality,[status(thm)],[c_845]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_1042,plain,
% 1.50/0.95      ( r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
% 1.50/0.95      | k1_funct_1(sK3,X0) = k1_xboole_0 ),
% 1.50/0.95      inference(global_propositional_subsumption,
% 1.50/0.95                [status(thm)],
% 1.50/0.95                [c_749,c_279,c_844,c_846]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_1043,plain,
% 1.50/0.95      ( k1_funct_1(sK3,X0) = k1_xboole_0
% 1.50/0.95      | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top ),
% 1.50/0.95      inference(renaming,[status(thm)],[c_1042]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_9,plain,
% 1.50/0.95      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 1.50/0.95      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 1.50/0.95      | ~ v1_relat_1(X1)
% 1.50/0.95      | ~ v1_funct_1(X1) ),
% 1.50/0.95      inference(cnf_transformation,[],[f61]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_244,plain,
% 1.50/0.95      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 1.50/0.95      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 1.50/0.95      | ~ v1_relat_1(X1)
% 1.50/0.95      | sK3 != X1 ),
% 1.50/0.95      inference(resolution_lifted,[status(thm)],[c_9,c_16]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_245,plain,
% 1.50/0.95      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 1.50/0.95      | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3)
% 1.50/0.95      | ~ v1_relat_1(sK3) ),
% 1.50/0.95      inference(unflattening,[status(thm)],[c_244]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_751,plain,
% 1.50/0.95      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 1.50/0.95      | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) = iProver_top
% 1.50/0.95      | v1_relat_1(sK3) != iProver_top ),
% 1.50/0.95      inference(predicate_to_equality,[status(thm)],[c_245]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_246,plain,
% 1.50/0.95      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 1.50/0.95      | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) = iProver_top
% 1.50/0.95      | v1_relat_1(sK3) != iProver_top ),
% 1.50/0.95      inference(predicate_to_equality,[status(thm)],[c_245]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_915,plain,
% 1.50/0.95      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) = iProver_top
% 1.50/0.95      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
% 1.50/0.95      inference(global_propositional_subsumption,
% 1.50/0.95                [status(thm)],
% 1.50/0.95                [c_751,c_246,c_844,c_846]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_916,plain,
% 1.50/0.95      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 1.50/0.95      | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) = iProver_top ),
% 1.50/0.95      inference(renaming,[status(thm)],[c_915]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_5,plain,
% 1.50/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.50/0.95      | ~ r2_hidden(X2,X0)
% 1.50/0.95      | r2_hidden(X2,X1) ),
% 1.50/0.95      inference(cnf_transformation,[],[f38]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_210,plain,
% 1.50/0.95      ( ~ r2_hidden(X0,X1)
% 1.50/0.95      | r2_hidden(X0,X2)
% 1.50/0.95      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(X2)
% 1.50/0.95      | sK3 != X1 ),
% 1.50/0.95      inference(resolution_lifted,[status(thm)],[c_5,c_14]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_211,plain,
% 1.50/0.95      ( r2_hidden(X0,X1)
% 1.50/0.95      | ~ r2_hidden(X0,sK3)
% 1.50/0.95      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(X1) ),
% 1.50/0.95      inference(unflattening,[status(thm)],[c_210]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_753,plain,
% 1.50/0.95      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(X0)
% 1.50/0.95      | r2_hidden(X1,X0) = iProver_top
% 1.50/0.95      | r2_hidden(X1,sK3) != iProver_top ),
% 1.50/0.95      inference(predicate_to_equality,[status(thm)],[c_211]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_927,plain,
% 1.50/0.95      ( r2_hidden(X0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) = iProver_top
% 1.50/0.95      | r2_hidden(X0,sK3) != iProver_top ),
% 1.50/0.95      inference(equality_resolution,[status(thm)],[c_753]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_3,plain,
% 1.50/0.95      ( r2_hidden(X0,X1)
% 1.50/0.95      | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(k2_enumset1(X3,X3,X3,X3),X1)) ),
% 1.50/0.95      inference(cnf_transformation,[],[f54]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_757,plain,
% 1.50/0.95      ( r2_hidden(X0,X1) = iProver_top
% 1.50/0.95      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(k2_enumset1(X3,X3,X3,X3),X1)) != iProver_top ),
% 1.50/0.95      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_1207,plain,
% 1.50/0.95      ( r2_hidden(X0,sK2) = iProver_top
% 1.50/0.95      | r2_hidden(k4_tarski(X1,X0),sK3) != iProver_top ),
% 1.50/0.95      inference(superposition,[status(thm)],[c_927,c_757]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_1582,plain,
% 1.50/0.95      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 1.50/0.95      | r2_hidden(k1_funct_1(sK3,X0),sK2) = iProver_top ),
% 1.50/0.95      inference(superposition,[status(thm)],[c_916,c_1207]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_12,negated_conjecture,
% 1.50/0.95      ( ~ r2_hidden(k1_funct_1(sK3,sK1),sK2) ),
% 1.50/0.95      inference(cnf_transformation,[],[f49]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_755,plain,
% 1.50/0.95      ( r2_hidden(k1_funct_1(sK3,sK1),sK2) != iProver_top ),
% 1.50/0.95      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_1590,plain,
% 1.50/0.95      ( r2_hidden(sK1,k1_relat_1(sK3)) != iProver_top ),
% 1.50/0.95      inference(superposition,[status(thm)],[c_1582,c_755]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_1643,plain,
% 1.50/0.95      ( k1_funct_1(sK3,sK1) = k1_xboole_0 ),
% 1.50/0.95      inference(superposition,[status(thm)],[c_1043,c_1590]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_1704,plain,
% 1.50/0.95      ( r2_hidden(k1_xboole_0,sK2) != iProver_top ),
% 1.50/0.95      inference(demodulation,[status(thm)],[c_1643,c_755]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_509,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_1572,plain,
% 1.50/0.95      ( X0 != X1
% 1.50/0.95      | X0 = sK0(k2_enumset1(sK1,sK1,sK1,sK1))
% 1.50/0.95      | sK0(k2_enumset1(sK1,sK1,sK1,sK1)) != X1 ),
% 1.50/0.95      inference(instantiation,[status(thm)],[c_509]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_1573,plain,
% 1.50/0.95      ( sK0(k2_enumset1(sK1,sK1,sK1,sK1)) != sK1
% 1.50/0.95      | sK1 = sK0(k2_enumset1(sK1,sK1,sK1,sK1))
% 1.50/0.95      | sK1 != sK1 ),
% 1.50/0.95      inference(instantiation,[status(thm)],[c_1572]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_4,plain,
% 1.50/0.95      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3))
% 1.50/0.95      | X2 = X0 ),
% 1.50/0.95      inference(cnf_transformation,[],[f55]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_756,plain,
% 1.50/0.95      ( X0 = X1
% 1.50/0.95      | r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),X3)) != iProver_top ),
% 1.50/0.95      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_1208,plain,
% 1.50/0.95      ( sK1 = X0 | r2_hidden(k4_tarski(X0,X1),sK3) != iProver_top ),
% 1.50/0.95      inference(superposition,[status(thm)],[c_927,c_756]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_1316,plain,
% 1.50/0.95      ( sK1 = X0 | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
% 1.50/0.95      inference(superposition,[status(thm)],[c_916,c_1208]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_1444,plain,
% 1.50/0.95      ( k1_funct_1(sK3,X0) = k1_xboole_0 | sK1 = X0 ),
% 1.50/0.95      inference(superposition,[status(thm)],[c_1043,c_1316]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_0,plain,
% 1.50/0.95      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 1.50/0.95      inference(cnf_transformation,[],[f30]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_760,plain,
% 1.50/0.95      ( r2_hidden(sK0(X0),X0) = iProver_top
% 1.50/0.95      | v1_xboole_0(X0) = iProver_top ),
% 1.50/0.95      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_11,plain,
% 1.50/0.95      ( ~ v1_funct_2(X0,X1,X2)
% 1.50/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.50/0.95      | ~ r2_hidden(X3,X1)
% 1.50/0.95      | r2_hidden(k1_funct_1(X0,X3),X2)
% 1.50/0.95      | ~ v1_funct_1(X0)
% 1.50/0.95      | k1_xboole_0 = X2 ),
% 1.50/0.95      inference(cnf_transformation,[],[f44]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_15,negated_conjecture,
% 1.50/0.95      ( v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
% 1.50/0.95      inference(cnf_transformation,[],[f57]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_189,plain,
% 1.50/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.50/0.95      | ~ r2_hidden(X3,X1)
% 1.50/0.95      | r2_hidden(k1_funct_1(X0,X3),X2)
% 1.50/0.95      | ~ v1_funct_1(X0)
% 1.50/0.95      | k2_enumset1(sK1,sK1,sK1,sK1) != X1
% 1.50/0.95      | sK2 != X2
% 1.50/0.95      | sK3 != X0
% 1.50/0.95      | k1_xboole_0 = X2 ),
% 1.50/0.95      inference(resolution_lifted,[status(thm)],[c_11,c_15]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_190,plain,
% 1.50/0.95      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
% 1.50/0.95      | ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
% 1.50/0.95      | r2_hidden(k1_funct_1(sK3,X0),sK2)
% 1.50/0.95      | ~ v1_funct_1(sK3)
% 1.50/0.95      | k1_xboole_0 = sK2 ),
% 1.50/0.95      inference(unflattening,[status(thm)],[c_189]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_13,negated_conjecture,
% 1.50/0.95      ( k1_xboole_0 != sK2 ),
% 1.50/0.95      inference(cnf_transformation,[],[f48]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_194,plain,
% 1.50/0.95      ( ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
% 1.50/0.95      | r2_hidden(k1_funct_1(sK3,X0),sK2) ),
% 1.50/0.95      inference(global_propositional_subsumption,
% 1.50/0.95                [status(thm)],
% 1.50/0.95                [c_190,c_16,c_14,c_13]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_754,plain,
% 1.50/0.95      ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
% 1.50/0.95      | r2_hidden(k1_funct_1(sK3,X0),sK2) = iProver_top ),
% 1.50/0.95      inference(predicate_to_equality,[status(thm)],[c_194]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_1140,plain,
% 1.50/0.95      ( r2_hidden(k1_funct_1(sK3,sK0(k2_enumset1(sK1,sK1,sK1,sK1))),sK2) = iProver_top
% 1.50/0.95      | v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top ),
% 1.50/0.95      inference(superposition,[status(thm)],[c_760,c_754]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_1,plain,
% 1.50/0.95      ( ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X1)) ),
% 1.50/0.95      inference(cnf_transformation,[],[f52]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_179,plain,
% 1.50/0.95      ( r2_hidden(sK0(X0),X0) | k2_enumset1(X1,X1,X1,X2) != X0 ),
% 1.50/0.95      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_180,plain,
% 1.50/0.95      ( r2_hidden(sK0(k2_enumset1(X0,X0,X0,X1)),k2_enumset1(X0,X0,X0,X1)) ),
% 1.50/0.95      inference(unflattening,[status(thm)],[c_179]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_181,plain,
% 1.50/0.95      ( r2_hidden(sK0(k2_enumset1(X0,X0,X0,X1)),k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
% 1.50/0.95      inference(predicate_to_equality,[status(thm)],[c_180]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_183,plain,
% 1.50/0.95      ( r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top ),
% 1.50/0.95      inference(instantiation,[status(thm)],[c_181]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_849,plain,
% 1.50/0.95      ( r2_hidden(k1_funct_1(sK3,sK0(k2_enumset1(sK1,sK1,sK1,sK1))),sK2)
% 1.50/0.95      | ~ r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) ),
% 1.50/0.95      inference(instantiation,[status(thm)],[c_194]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_852,plain,
% 1.50/0.95      ( r2_hidden(k1_funct_1(sK3,sK0(k2_enumset1(sK1,sK1,sK1,sK1))),sK2) = iProver_top
% 1.50/0.95      | r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top ),
% 1.50/0.95      inference(predicate_to_equality,[status(thm)],[c_849]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_1308,plain,
% 1.50/0.95      ( r2_hidden(k1_funct_1(sK3,sK0(k2_enumset1(sK1,sK1,sK1,sK1))),sK2) = iProver_top ),
% 1.50/0.95      inference(global_propositional_subsumption,
% 1.50/0.95                [status(thm)],
% 1.50/0.95                [c_1140,c_183,c_852]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_1458,plain,
% 1.50/0.95      ( sK0(k2_enumset1(sK1,sK1,sK1,sK1)) = sK1
% 1.50/0.95      | r2_hidden(k1_xboole_0,sK2) = iProver_top ),
% 1.50/0.95      inference(superposition,[status(thm)],[c_1444,c_1308]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_511,plain,
% 1.50/0.95      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.50/0.95      theory(equality) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_871,plain,
% 1.50/0.95      ( r2_hidden(X0,X1)
% 1.50/0.95      | ~ r2_hidden(sK0(X2),X2)
% 1.50/0.95      | X1 != X2
% 1.50/0.95      | X0 != sK0(X2) ),
% 1.50/0.95      inference(instantiation,[status(thm)],[c_511]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_1117,plain,
% 1.50/0.95      ( r2_hidden(X0,X1)
% 1.50/0.95      | ~ r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1))
% 1.50/0.95      | X1 != k2_enumset1(sK1,sK1,sK1,sK1)
% 1.50/0.95      | X0 != sK0(k2_enumset1(sK1,sK1,sK1,sK1)) ),
% 1.50/0.95      inference(instantiation,[status(thm)],[c_871]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_1255,plain,
% 1.50/0.95      ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
% 1.50/0.95      | ~ r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1))
% 1.50/0.95      | X0 != sK0(k2_enumset1(sK1,sK1,sK1,sK1))
% 1.50/0.95      | k2_enumset1(sK1,sK1,sK1,sK1) != k2_enumset1(sK1,sK1,sK1,sK1) ),
% 1.50/0.95      inference(instantiation,[status(thm)],[c_1117]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_1258,plain,
% 1.50/0.95      ( ~ r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1))
% 1.50/0.95      | r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1))
% 1.50/0.95      | k2_enumset1(sK1,sK1,sK1,sK1) != k2_enumset1(sK1,sK1,sK1,sK1)
% 1.50/0.95      | sK1 != sK0(k2_enumset1(sK1,sK1,sK1,sK1)) ),
% 1.50/0.95      inference(instantiation,[status(thm)],[c_1255]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_529,plain,
% 1.50/0.95      ( sK1 = sK1 ),
% 1.50/0.95      inference(instantiation,[status(thm)],[c_508]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_512,plain,
% 1.50/0.95      ( X0 != X1
% 1.50/0.95      | X2 != X3
% 1.50/0.95      | X4 != X5
% 1.50/0.95      | X6 != X7
% 1.50/0.95      | k2_enumset1(X0,X2,X4,X6) = k2_enumset1(X1,X3,X5,X7) ),
% 1.50/0.95      theory(equality) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_521,plain,
% 1.50/0.95      ( k2_enumset1(sK1,sK1,sK1,sK1) = k2_enumset1(sK1,sK1,sK1,sK1)
% 1.50/0.95      | sK1 != sK1 ),
% 1.50/0.95      inference(instantiation,[status(thm)],[c_512]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_192,plain,
% 1.50/0.95      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
% 1.50/0.95      | r2_hidden(k1_funct_1(sK3,sK1),sK2)
% 1.50/0.95      | ~ r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1))
% 1.50/0.95      | ~ v1_funct_1(sK3)
% 1.50/0.95      | k1_xboole_0 = sK2 ),
% 1.50/0.95      inference(instantiation,[status(thm)],[c_190]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(c_182,plain,
% 1.50/0.95      ( r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) ),
% 1.50/0.95      inference(instantiation,[status(thm)],[c_180]) ).
% 1.50/0.95  
% 1.50/0.95  cnf(contradiction,plain,
% 1.50/0.95      ( $false ),
% 1.50/0.95      inference(minisat,
% 1.50/0.95                [status(thm)],
% 1.50/0.95                [c_1704,c_1573,c_1458,c_1258,c_529,c_521,c_192,c_182,
% 1.50/0.95                 c_12,c_13,c_14,c_16]) ).
% 1.50/0.95  
% 1.50/0.95  
% 1.50/0.95  % SZS output end CNFRefutation for theBenchmark.p
% 1.50/0.95  
% 1.50/0.95  ------                               Statistics
% 1.50/0.95  
% 1.50/0.95  ------ General
% 1.50/0.95  
% 1.50/0.95  abstr_ref_over_cycles:                  0
% 1.50/0.95  abstr_ref_under_cycles:                 0
% 1.50/0.95  gc_basic_clause_elim:                   0
% 1.50/0.95  forced_gc_time:                         0
% 1.50/0.95  parsing_time:                           0.01
% 1.50/0.95  unif_index_cands_time:                  0.
% 1.50/0.95  unif_index_add_time:                    0.
% 1.50/0.95  orderings_time:                         0.
% 1.50/0.95  out_proof_time:                         0.012
% 1.50/0.95  total_time:                             0.088
% 1.50/0.95  num_of_symbols:                         48
% 1.50/0.95  num_of_terms:                           1749
% 1.50/0.95  
% 1.50/0.95  ------ Preprocessing
% 1.50/0.95  
% 1.50/0.95  num_of_splits:                          0
% 1.50/0.95  num_of_split_atoms:                     0
% 1.50/0.95  num_of_reused_defs:                     0
% 1.50/0.95  num_eq_ax_congr_red:                    8
% 1.50/0.95  num_of_sem_filtered_clauses:            1
% 1.50/0.95  num_of_subtypes:                        0
% 1.50/0.95  monotx_restored_types:                  0
% 1.50/0.95  sat_num_of_epr_types:                   0
% 1.50/0.95  sat_num_of_non_cyclic_types:            0
% 1.50/0.95  sat_guarded_non_collapsed_types:        0
% 1.50/0.95  num_pure_diseq_elim:                    0
% 1.50/0.95  simp_replaced_by:                       0
% 1.50/0.95  res_preprocessed:                       78
% 1.50/0.95  prep_upred:                             0
% 1.50/0.95  prep_unflattend:                        10
% 1.50/0.95  smt_new_axioms:                         0
% 1.50/0.95  pred_elim_cands:                        3
% 1.50/0.95  pred_elim:                              3
% 1.50/0.95  pred_elim_cl:                           3
% 1.50/0.95  pred_elim_cycles:                       7
% 1.50/0.95  merged_defs:                            0
% 1.50/0.95  merged_defs_ncl:                        0
% 1.50/0.95  bin_hyper_res:                          0
% 1.50/0.95  prep_cycles:                            4
% 1.50/0.95  pred_elim_time:                         0.004
% 1.50/0.95  splitting_time:                         0.
% 1.50/0.95  sem_filter_time:                        0.
% 1.50/0.95  monotx_time:                            0.
% 1.50/0.95  subtype_inf_time:                       0.
% 1.50/0.95  
% 1.50/0.95  ------ Problem properties
% 1.50/0.95  
% 1.50/0.95  clauses:                                13
% 1.50/0.95  conjectures:                            2
% 1.50/0.95  epr:                                    1
% 1.50/0.95  horn:                                   11
% 1.50/0.95  ground:                                 2
% 1.50/0.95  unary:                                  3
% 1.50/0.95  binary:                                 6
% 1.50/0.95  lits:                                   28
% 1.50/0.95  lits_eq:                                6
% 1.50/0.95  fd_pure:                                0
% 1.50/0.95  fd_pseudo:                              0
% 1.50/0.95  fd_cond:                                0
% 1.50/0.95  fd_pseudo_cond:                         2
% 1.50/0.95  ac_symbols:                             0
% 1.50/0.95  
% 1.50/0.95  ------ Propositional Solver
% 1.50/0.95  
% 1.50/0.95  prop_solver_calls:                      26
% 1.50/0.95  prop_fast_solver_calls:                 473
% 1.50/0.95  smt_solver_calls:                       0
% 1.50/0.95  smt_fast_solver_calls:                  0
% 1.50/0.95  prop_num_of_clauses:                    567
% 1.50/0.95  prop_preprocess_simplified:             2722
% 1.50/0.95  prop_fo_subsumed:                       8
% 1.50/0.95  prop_solver_time:                       0.
% 1.50/0.95  smt_solver_time:                        0.
% 1.50/0.95  smt_fast_solver_time:                   0.
% 1.50/0.95  prop_fast_solver_time:                  0.
% 1.50/0.95  prop_unsat_core_time:                   0.
% 1.50/0.95  
% 1.50/0.95  ------ QBF
% 1.50/0.95  
% 1.50/0.95  qbf_q_res:                              0
% 1.50/0.95  qbf_num_tautologies:                    0
% 1.50/0.95  qbf_prep_cycles:                        0
% 1.50/0.95  
% 1.50/0.95  ------ BMC1
% 1.50/0.95  
% 1.50/0.95  bmc1_current_bound:                     -1
% 1.50/0.95  bmc1_last_solved_bound:                 -1
% 1.50/0.95  bmc1_unsat_core_size:                   -1
% 1.50/0.95  bmc1_unsat_core_parents_size:           -1
% 1.50/0.95  bmc1_merge_next_fun:                    0
% 1.50/0.95  bmc1_unsat_core_clauses_time:           0.
% 1.50/0.95  
% 1.50/0.95  ------ Instantiation
% 1.50/0.95  
% 1.50/0.95  inst_num_of_clauses:                    172
% 1.50/0.95  inst_num_in_passive:                    0
% 1.50/0.95  inst_num_in_active:                     102
% 1.50/0.95  inst_num_in_unprocessed:                70
% 1.50/0.95  inst_num_of_loops:                      120
% 1.50/0.95  inst_num_of_learning_restarts:          0
% 1.50/0.95  inst_num_moves_active_passive:          16
% 1.50/0.95  inst_lit_activity:                      0
% 1.50/0.95  inst_lit_activity_moves:                0
% 1.50/0.95  inst_num_tautologies:                   0
% 1.50/0.95  inst_num_prop_implied:                  0
% 1.50/0.95  inst_num_existing_simplified:           0
% 1.50/0.95  inst_num_eq_res_simplified:             0
% 1.50/0.95  inst_num_child_elim:                    0
% 1.50/0.95  inst_num_of_dismatching_blockings:      12
% 1.50/0.95  inst_num_of_non_proper_insts:           106
% 1.50/0.95  inst_num_of_duplicates:                 0
% 1.50/0.95  inst_inst_num_from_inst_to_res:         0
% 1.50/0.95  inst_dismatching_checking_time:         0.
% 1.50/0.95  
% 1.50/0.95  ------ Resolution
% 1.50/0.95  
% 1.50/0.95  res_num_of_clauses:                     0
% 1.50/0.95  res_num_in_passive:                     0
% 1.50/0.95  res_num_in_active:                      0
% 1.50/0.95  res_num_of_loops:                       82
% 1.50/0.95  res_forward_subset_subsumed:            59
% 1.50/0.95  res_backward_subset_subsumed:           0
% 1.50/0.95  res_forward_subsumed:                   0
% 1.50/0.95  res_backward_subsumed:                  0
% 1.50/0.95  res_forward_subsumption_resolution:     0
% 1.50/0.95  res_backward_subsumption_resolution:    0
% 1.50/0.95  res_clause_to_clause_subsumption:       24
% 1.50/0.95  res_orphan_elimination:                 0
% 1.50/0.95  res_tautology_del:                      17
% 1.50/0.95  res_num_eq_res_simplified:              0
% 1.50/0.95  res_num_sel_changes:                    0
% 1.50/0.95  res_moves_from_active_to_pass:          0
% 1.50/0.95  
% 1.50/0.95  ------ Superposition
% 1.50/0.95  
% 1.50/0.95  sup_time_total:                         0.
% 1.50/0.95  sup_time_generating:                    0.
% 1.50/0.95  sup_time_sim_full:                      0.
% 1.50/0.95  sup_time_sim_immed:                     0.
% 1.50/0.95  
% 1.50/0.95  sup_num_of_clauses:                     25
% 1.50/0.95  sup_num_in_active:                      21
% 1.50/0.95  sup_num_in_passive:                     4
% 1.50/0.95  sup_num_of_loops:                       22
% 1.50/0.95  sup_fw_superposition:                   7
% 1.50/0.95  sup_bw_superposition:                   9
% 1.50/0.95  sup_immediate_simplified:               2
% 1.50/0.95  sup_given_eliminated:                   0
% 1.50/0.95  comparisons_done:                       0
% 1.50/0.95  comparisons_avoided:                    1
% 1.50/0.95  
% 1.50/0.95  ------ Simplifications
% 1.50/0.95  
% 1.50/0.95  
% 1.50/0.95  sim_fw_subset_subsumed:                 2
% 1.50/0.95  sim_bw_subset_subsumed:                 0
% 1.50/0.95  sim_fw_subsumed:                        0
% 1.50/0.95  sim_bw_subsumed:                        0
% 1.50/0.95  sim_fw_subsumption_res:                 0
% 1.50/0.95  sim_bw_subsumption_res:                 0
% 1.50/0.95  sim_tautology_del:                      1
% 1.50/0.95  sim_eq_tautology_del:                   3
% 1.50/0.95  sim_eq_res_simp:                        0
% 1.50/0.95  sim_fw_demodulated:                     0
% 1.50/0.95  sim_bw_demodulated:                     1
% 1.50/0.95  sim_light_normalised:                   0
% 1.50/0.95  sim_joinable_taut:                      0
% 1.50/0.95  sim_joinable_simp:                      0
% 1.50/0.95  sim_ac_normalised:                      0
% 1.50/0.95  sim_smt_subsumption:                    0
% 1.50/0.95  
%------------------------------------------------------------------------------
