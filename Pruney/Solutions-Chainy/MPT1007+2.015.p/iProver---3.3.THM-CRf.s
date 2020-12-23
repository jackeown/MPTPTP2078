%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:45 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :  131 (1130 expanded)
%              Number of clauses        :   66 ( 290 expanded)
%              Number of leaves         :   17 ( 240 expanded)
%              Depth                    :   17
%              Number of atoms          :  347 (4089 expanded)
%              Number of equality atoms :  146 (1332 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | k1_xboole_0 != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_funct_1(X0,X1)
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f36,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f37,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f42,plain,
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

fof(f43,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK1),sK2)
    & k1_xboole_0 != sK2
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
    & v1_funct_2(sK3,k1_tarski(sK1),sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f37,f42])).

fof(f70,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f72,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f76,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f47,f75])).

fof(f81,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(definition_unfolding,[],[f72,f76])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f51,f76])).

fof(f74,plain,(
    ~ r2_hidden(k1_funct_1(sK3,sK1),sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 )
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X0) = X1
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X0) = X1
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2)) ) ),
    inference(definition_unfolding,[],[f66,f76])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f34])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f71,plain,(
    v1_funct_2(sK3,k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f82,plain,(
    v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
    inference(definition_unfolding,[],[f71,f76])).

fof(f73,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f43])).

fof(f18,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f22])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f40])).

fof(f68,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_xboole_0 != k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f50,f76])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_11,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_474,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,X0) = k1_xboole_0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_27])).

cnf(c_475,plain,
    ( r2_hidden(X0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_474])).

cnf(c_1408,plain,
    ( k1_funct_1(sK3,X0) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_475])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_30,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_476,plain,
    ( k1_funct_1(sK3,X0) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_475])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1562,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1563,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1562])).

cnf(c_1623,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
    | k1_funct_1(sK3,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1408,c_30,c_476,c_1563])).

cnf(c_1624,plain,
    ( k1_funct_1(sK3,X0) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1623])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_441,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_27])).

cnf(c_442,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_441])).

cnf(c_1410,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_442])).

cnf(c_443,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_442])).

cnf(c_1574,plain,
    ( r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1410,c_30,c_443,c_1563])).

cnf(c_1575,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_1574])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1425,plain,
    ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = k1_xboole_0
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2082,plain,
    ( k4_xboole_0(k2_enumset1(k4_tarski(X0,k1_funct_1(sK3,X0)),k4_tarski(X0,k1_funct_1(sK3,X0)),k4_tarski(X0,k1_funct_1(sK3,X0)),k4_tarski(X0,k1_funct_1(sK3,X0))),sK3) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1575,c_1425])).

cnf(c_3061,plain,
    ( k1_funct_1(sK3,X0) = k1_xboole_0
    | k4_xboole_0(k2_enumset1(k4_tarski(X0,k1_funct_1(sK3,X0)),k4_tarski(X0,k1_funct_1(sK3,X0)),k4_tarski(X0,k1_funct_1(sK3,X0)),k4_tarski(X0,k1_funct_1(sK3,X0))),sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1624,c_2082])).

cnf(c_23,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(sK3,sK1),sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_31,plain,
    ( r2_hidden(k1_funct_1(sK3,sK1),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1413,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1423,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2229,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1413,c_1423])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2))
    | k1_mcart_1(X0) = X1 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1416,plain,
    ( k1_mcart_1(X0) = X1
    | r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2328,plain,
    ( k1_mcart_1(X0) = sK1
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2229,c_1416])).

cnf(c_2361,plain,
    ( k1_mcart_1(k4_tarski(X0,k1_funct_1(sK3,X0))) = sK1
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1575,c_2328])).

cnf(c_2429,plain,
    ( k1_funct_1(sK3,X0) = k1_xboole_0
    | k1_mcart_1(k4_tarski(X0,k1_funct_1(sK3,X0))) = sK1 ),
    inference(superposition,[status(thm)],[c_1624,c_2361])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1418,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2327,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k1_mcart_1(X0),k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2229,c_1418])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_350,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k2_enumset1(sK1,sK1,sK1,sK1) != X1
    | sK2 != X2
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_26])).

cnf(c_351,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
    | ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
    | r2_hidden(k1_funct_1(sK3,X0),sK2)
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_350])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_355,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
    | r2_hidden(k1_funct_1(sK3,X0),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_351,c_27,c_25,c_24])).

cnf(c_1411,plain,
    ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_355])).

cnf(c_2507,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK3,k1_mcart_1(X0)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2327,c_1411])).

cnf(c_3172,plain,
    ( k1_funct_1(sK3,X0) = k1_xboole_0
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK3,sK1),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2429,c_2507])).

cnf(c_3311,plain,
    ( k1_funct_1(sK3,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3061,c_30,c_31,c_443,c_1563,c_1624,c_3172])).

cnf(c_1414,plain,
    ( r2_hidden(k1_funct_1(sK3,sK1),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3315,plain,
    ( r2_hidden(k1_xboole_0,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3311,c_1414])).

cnf(c_21,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1415,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2058,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_xboole_0
    | r2_hidden(k1_funct_1(sK3,sK0(k2_enumset1(sK1,sK1,sK1,sK1))),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1415,c_1411])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1424,plain,
    ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) != k1_xboole_0
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1990,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_1424])).

cnf(c_1,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_339,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_15])).

cnf(c_340,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_339])).

cnf(c_341,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_340])).

cnf(c_1995,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1990,c_341])).

cnf(c_3195,plain,
    ( r2_hidden(k1_funct_1(sK3,sK0(k2_enumset1(sK1,sK1,sK1,sK1))),sK2) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2058,c_1995])).

cnf(c_3322,plain,
    ( r2_hidden(k1_xboole_0,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3311,c_3195])).

cnf(c_3363,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3315,c_3322])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:18:01 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.60/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.00  
% 2.60/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.60/1.00  
% 2.60/1.00  ------  iProver source info
% 2.60/1.00  
% 2.60/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.60/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.60/1.00  git: non_committed_changes: false
% 2.60/1.00  git: last_make_outside_of_git: false
% 2.60/1.00  
% 2.60/1.00  ------ 
% 2.60/1.00  
% 2.60/1.00  ------ Input Options
% 2.60/1.00  
% 2.60/1.00  --out_options                           all
% 2.60/1.00  --tptp_safe_out                         true
% 2.60/1.00  --problem_path                          ""
% 2.60/1.00  --include_path                          ""
% 2.60/1.00  --clausifier                            res/vclausify_rel
% 2.60/1.00  --clausifier_options                    --mode clausify
% 2.60/1.00  --stdin                                 false
% 2.60/1.00  --stats_out                             all
% 2.60/1.00  
% 2.60/1.00  ------ General Options
% 2.60/1.00  
% 2.60/1.00  --fof                                   false
% 2.60/1.00  --time_out_real                         305.
% 2.60/1.00  --time_out_virtual                      -1.
% 2.60/1.00  --symbol_type_check                     false
% 2.60/1.00  --clausify_out                          false
% 2.60/1.00  --sig_cnt_out                           false
% 2.60/1.00  --trig_cnt_out                          false
% 2.60/1.00  --trig_cnt_out_tolerance                1.
% 2.60/1.00  --trig_cnt_out_sk_spl                   false
% 2.60/1.00  --abstr_cl_out                          false
% 2.60/1.00  
% 2.60/1.00  ------ Global Options
% 2.60/1.00  
% 2.60/1.00  --schedule                              default
% 2.60/1.00  --add_important_lit                     false
% 2.60/1.00  --prop_solver_per_cl                    1000
% 2.60/1.00  --min_unsat_core                        false
% 2.60/1.00  --soft_assumptions                      false
% 2.60/1.00  --soft_lemma_size                       3
% 2.60/1.00  --prop_impl_unit_size                   0
% 2.60/1.00  --prop_impl_unit                        []
% 2.60/1.00  --share_sel_clauses                     true
% 2.60/1.00  --reset_solvers                         false
% 2.60/1.00  --bc_imp_inh                            [conj_cone]
% 2.60/1.00  --conj_cone_tolerance                   3.
% 2.60/1.00  --extra_neg_conj                        none
% 2.60/1.00  --large_theory_mode                     true
% 2.60/1.00  --prolific_symb_bound                   200
% 2.60/1.00  --lt_threshold                          2000
% 2.60/1.00  --clause_weak_htbl                      true
% 2.60/1.00  --gc_record_bc_elim                     false
% 2.60/1.00  
% 2.60/1.00  ------ Preprocessing Options
% 2.60/1.00  
% 2.60/1.00  --preprocessing_flag                    true
% 2.60/1.00  --time_out_prep_mult                    0.1
% 2.60/1.00  --splitting_mode                        input
% 2.60/1.00  --splitting_grd                         true
% 2.60/1.00  --splitting_cvd                         false
% 2.60/1.00  --splitting_cvd_svl                     false
% 2.60/1.00  --splitting_nvd                         32
% 2.60/1.00  --sub_typing                            true
% 2.60/1.00  --prep_gs_sim                           true
% 2.60/1.00  --prep_unflatten                        true
% 2.60/1.00  --prep_res_sim                          true
% 2.60/1.00  --prep_upred                            true
% 2.60/1.00  --prep_sem_filter                       exhaustive
% 2.60/1.00  --prep_sem_filter_out                   false
% 2.60/1.00  --pred_elim                             true
% 2.60/1.00  --res_sim_input                         true
% 2.60/1.00  --eq_ax_congr_red                       true
% 2.60/1.00  --pure_diseq_elim                       true
% 2.60/1.00  --brand_transform                       false
% 2.60/1.00  --non_eq_to_eq                          false
% 2.60/1.00  --prep_def_merge                        true
% 2.60/1.00  --prep_def_merge_prop_impl              false
% 2.60/1.00  --prep_def_merge_mbd                    true
% 2.60/1.00  --prep_def_merge_tr_red                 false
% 2.60/1.00  --prep_def_merge_tr_cl                  false
% 2.60/1.00  --smt_preprocessing                     true
% 2.60/1.00  --smt_ac_axioms                         fast
% 2.60/1.00  --preprocessed_out                      false
% 2.60/1.00  --preprocessed_stats                    false
% 2.60/1.00  
% 2.60/1.00  ------ Abstraction refinement Options
% 2.60/1.00  
% 2.60/1.00  --abstr_ref                             []
% 2.60/1.00  --abstr_ref_prep                        false
% 2.60/1.00  --abstr_ref_until_sat                   false
% 2.60/1.00  --abstr_ref_sig_restrict                funpre
% 2.60/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.60/1.00  --abstr_ref_under                       []
% 2.60/1.00  
% 2.60/1.00  ------ SAT Options
% 2.60/1.00  
% 2.60/1.00  --sat_mode                              false
% 2.60/1.00  --sat_fm_restart_options                ""
% 2.60/1.00  --sat_gr_def                            false
% 2.60/1.00  --sat_epr_types                         true
% 2.60/1.00  --sat_non_cyclic_types                  false
% 2.60/1.00  --sat_finite_models                     false
% 2.60/1.00  --sat_fm_lemmas                         false
% 2.60/1.00  --sat_fm_prep                           false
% 2.60/1.00  --sat_fm_uc_incr                        true
% 2.60/1.00  --sat_out_model                         small
% 2.60/1.00  --sat_out_clauses                       false
% 2.60/1.00  
% 2.60/1.00  ------ QBF Options
% 2.60/1.00  
% 2.60/1.00  --qbf_mode                              false
% 2.60/1.00  --qbf_elim_univ                         false
% 2.60/1.00  --qbf_dom_inst                          none
% 2.60/1.00  --qbf_dom_pre_inst                      false
% 2.60/1.00  --qbf_sk_in                             false
% 2.60/1.00  --qbf_pred_elim                         true
% 2.60/1.00  --qbf_split                             512
% 2.60/1.00  
% 2.60/1.00  ------ BMC1 Options
% 2.60/1.00  
% 2.60/1.00  --bmc1_incremental                      false
% 2.60/1.00  --bmc1_axioms                           reachable_all
% 2.60/1.00  --bmc1_min_bound                        0
% 2.60/1.00  --bmc1_max_bound                        -1
% 2.60/1.00  --bmc1_max_bound_default                -1
% 2.60/1.00  --bmc1_symbol_reachability              true
% 2.60/1.00  --bmc1_property_lemmas                  false
% 2.60/1.00  --bmc1_k_induction                      false
% 2.60/1.00  --bmc1_non_equiv_states                 false
% 2.60/1.00  --bmc1_deadlock                         false
% 2.60/1.00  --bmc1_ucm                              false
% 2.60/1.00  --bmc1_add_unsat_core                   none
% 2.60/1.00  --bmc1_unsat_core_children              false
% 2.60/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.60/1.00  --bmc1_out_stat                         full
% 2.60/1.00  --bmc1_ground_init                      false
% 2.60/1.00  --bmc1_pre_inst_next_state              false
% 2.60/1.00  --bmc1_pre_inst_state                   false
% 2.60/1.00  --bmc1_pre_inst_reach_state             false
% 2.60/1.00  --bmc1_out_unsat_core                   false
% 2.60/1.00  --bmc1_aig_witness_out                  false
% 2.60/1.00  --bmc1_verbose                          false
% 2.60/1.00  --bmc1_dump_clauses_tptp                false
% 2.60/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.60/1.00  --bmc1_dump_file                        -
% 2.60/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.60/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.60/1.00  --bmc1_ucm_extend_mode                  1
% 2.60/1.00  --bmc1_ucm_init_mode                    2
% 2.60/1.00  --bmc1_ucm_cone_mode                    none
% 2.60/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.60/1.00  --bmc1_ucm_relax_model                  4
% 2.60/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.60/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.60/1.00  --bmc1_ucm_layered_model                none
% 2.60/1.00  --bmc1_ucm_max_lemma_size               10
% 2.60/1.00  
% 2.60/1.00  ------ AIG Options
% 2.60/1.00  
% 2.60/1.00  --aig_mode                              false
% 2.60/1.00  
% 2.60/1.00  ------ Instantiation Options
% 2.60/1.00  
% 2.60/1.00  --instantiation_flag                    true
% 2.60/1.00  --inst_sos_flag                         false
% 2.60/1.00  --inst_sos_phase                        true
% 2.60/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.60/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.60/1.00  --inst_lit_sel_side                     num_symb
% 2.60/1.00  --inst_solver_per_active                1400
% 2.60/1.00  --inst_solver_calls_frac                1.
% 2.60/1.00  --inst_passive_queue_type               priority_queues
% 2.60/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.60/1.00  --inst_passive_queues_freq              [25;2]
% 2.60/1.00  --inst_dismatching                      true
% 2.60/1.00  --inst_eager_unprocessed_to_passive     true
% 2.60/1.00  --inst_prop_sim_given                   true
% 2.60/1.00  --inst_prop_sim_new                     false
% 2.60/1.00  --inst_subs_new                         false
% 2.60/1.00  --inst_eq_res_simp                      false
% 2.60/1.00  --inst_subs_given                       false
% 2.60/1.00  --inst_orphan_elimination               true
% 2.60/1.00  --inst_learning_loop_flag               true
% 2.60/1.00  --inst_learning_start                   3000
% 2.60/1.00  --inst_learning_factor                  2
% 2.60/1.00  --inst_start_prop_sim_after_learn       3
% 2.60/1.00  --inst_sel_renew                        solver
% 2.60/1.00  --inst_lit_activity_flag                true
% 2.60/1.00  --inst_restr_to_given                   false
% 2.60/1.00  --inst_activity_threshold               500
% 2.60/1.00  --inst_out_proof                        true
% 2.60/1.00  
% 2.60/1.00  ------ Resolution Options
% 2.60/1.00  
% 2.60/1.00  --resolution_flag                       true
% 2.60/1.00  --res_lit_sel                           adaptive
% 2.60/1.00  --res_lit_sel_side                      none
% 2.60/1.00  --res_ordering                          kbo
% 2.60/1.00  --res_to_prop_solver                    active
% 2.60/1.00  --res_prop_simpl_new                    false
% 2.60/1.00  --res_prop_simpl_given                  true
% 2.60/1.00  --res_passive_queue_type                priority_queues
% 2.60/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.60/1.00  --res_passive_queues_freq               [15;5]
% 2.60/1.00  --res_forward_subs                      full
% 2.60/1.00  --res_backward_subs                     full
% 2.60/1.00  --res_forward_subs_resolution           true
% 2.60/1.00  --res_backward_subs_resolution          true
% 2.60/1.00  --res_orphan_elimination                true
% 2.60/1.00  --res_time_limit                        2.
% 2.60/1.00  --res_out_proof                         true
% 2.60/1.00  
% 2.60/1.00  ------ Superposition Options
% 2.60/1.00  
% 2.60/1.00  --superposition_flag                    true
% 2.60/1.00  --sup_passive_queue_type                priority_queues
% 2.60/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.60/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.60/1.00  --demod_completeness_check              fast
% 2.60/1.00  --demod_use_ground                      true
% 2.60/1.00  --sup_to_prop_solver                    passive
% 2.60/1.00  --sup_prop_simpl_new                    true
% 2.60/1.00  --sup_prop_simpl_given                  true
% 2.60/1.00  --sup_fun_splitting                     false
% 2.60/1.00  --sup_smt_interval                      50000
% 2.60/1.00  
% 2.60/1.00  ------ Superposition Simplification Setup
% 2.60/1.00  
% 2.60/1.00  --sup_indices_passive                   []
% 2.60/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.60/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/1.00  --sup_full_bw                           [BwDemod]
% 2.60/1.00  --sup_immed_triv                        [TrivRules]
% 2.60/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.60/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/1.00  --sup_immed_bw_main                     []
% 2.60/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.60/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.60/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.60/1.00  
% 2.60/1.00  ------ Combination Options
% 2.60/1.00  
% 2.60/1.00  --comb_res_mult                         3
% 2.60/1.00  --comb_sup_mult                         2
% 2.60/1.00  --comb_inst_mult                        10
% 2.60/1.00  
% 2.60/1.00  ------ Debug Options
% 2.60/1.00  
% 2.60/1.00  --dbg_backtrace                         false
% 2.60/1.00  --dbg_dump_prop_clauses                 false
% 2.60/1.00  --dbg_dump_prop_clauses_file            -
% 2.60/1.00  --dbg_out_stat                          false
% 2.60/1.00  ------ Parsing...
% 2.60/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.60/1.00  
% 2.60/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.60/1.00  
% 2.60/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.60/1.00  
% 2.60/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.60/1.00  ------ Proving...
% 2.60/1.00  ------ Problem Properties 
% 2.60/1.00  
% 2.60/1.00  
% 2.60/1.00  clauses                                 24
% 2.60/1.00  conjectures                             3
% 2.60/1.00  EPR                                     2
% 2.60/1.00  Horn                                    22
% 2.60/1.00  unary                                   10
% 2.60/1.00  binary                                  9
% 2.60/1.00  lits                                    44
% 2.60/1.00  lits eq                                 11
% 2.60/1.00  fd_pure                                 0
% 2.60/1.00  fd_pseudo                               0
% 2.60/1.00  fd_cond                                 1
% 2.60/1.00  fd_pseudo_cond                          2
% 2.60/1.00  AC symbols                              0
% 2.60/1.00  
% 2.60/1.00  ------ Schedule dynamic 5 is on 
% 2.60/1.00  
% 2.60/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.60/1.00  
% 2.60/1.00  
% 2.60/1.00  ------ 
% 2.60/1.00  Current options:
% 2.60/1.00  ------ 
% 2.60/1.00  
% 2.60/1.00  ------ Input Options
% 2.60/1.00  
% 2.60/1.00  --out_options                           all
% 2.60/1.00  --tptp_safe_out                         true
% 2.60/1.00  --problem_path                          ""
% 2.60/1.00  --include_path                          ""
% 2.60/1.00  --clausifier                            res/vclausify_rel
% 2.60/1.00  --clausifier_options                    --mode clausify
% 2.60/1.00  --stdin                                 false
% 2.60/1.00  --stats_out                             all
% 2.60/1.00  
% 2.60/1.00  ------ General Options
% 2.60/1.00  
% 2.60/1.00  --fof                                   false
% 2.60/1.00  --time_out_real                         305.
% 2.60/1.00  --time_out_virtual                      -1.
% 2.60/1.00  --symbol_type_check                     false
% 2.60/1.00  --clausify_out                          false
% 2.60/1.00  --sig_cnt_out                           false
% 2.60/1.00  --trig_cnt_out                          false
% 2.60/1.00  --trig_cnt_out_tolerance                1.
% 2.60/1.00  --trig_cnt_out_sk_spl                   false
% 2.60/1.00  --abstr_cl_out                          false
% 2.60/1.00  
% 2.60/1.00  ------ Global Options
% 2.60/1.00  
% 2.60/1.00  --schedule                              default
% 2.60/1.00  --add_important_lit                     false
% 2.60/1.00  --prop_solver_per_cl                    1000
% 2.60/1.00  --min_unsat_core                        false
% 2.60/1.00  --soft_assumptions                      false
% 2.60/1.00  --soft_lemma_size                       3
% 2.60/1.00  --prop_impl_unit_size                   0
% 2.60/1.00  --prop_impl_unit                        []
% 2.60/1.00  --share_sel_clauses                     true
% 2.60/1.00  --reset_solvers                         false
% 2.60/1.00  --bc_imp_inh                            [conj_cone]
% 2.60/1.00  --conj_cone_tolerance                   3.
% 2.60/1.00  --extra_neg_conj                        none
% 2.60/1.00  --large_theory_mode                     true
% 2.60/1.00  --prolific_symb_bound                   200
% 2.60/1.00  --lt_threshold                          2000
% 2.60/1.00  --clause_weak_htbl                      true
% 2.60/1.00  --gc_record_bc_elim                     false
% 2.60/1.00  
% 2.60/1.00  ------ Preprocessing Options
% 2.60/1.00  
% 2.60/1.00  --preprocessing_flag                    true
% 2.60/1.00  --time_out_prep_mult                    0.1
% 2.60/1.00  --splitting_mode                        input
% 2.60/1.00  --splitting_grd                         true
% 2.60/1.00  --splitting_cvd                         false
% 2.60/1.00  --splitting_cvd_svl                     false
% 2.60/1.00  --splitting_nvd                         32
% 2.60/1.00  --sub_typing                            true
% 2.60/1.00  --prep_gs_sim                           true
% 2.60/1.00  --prep_unflatten                        true
% 2.60/1.00  --prep_res_sim                          true
% 2.60/1.00  --prep_upred                            true
% 2.60/1.00  --prep_sem_filter                       exhaustive
% 2.60/1.00  --prep_sem_filter_out                   false
% 2.60/1.00  --pred_elim                             true
% 2.60/1.00  --res_sim_input                         true
% 2.60/1.00  --eq_ax_congr_red                       true
% 2.60/1.00  --pure_diseq_elim                       true
% 2.60/1.00  --brand_transform                       false
% 2.60/1.00  --non_eq_to_eq                          false
% 2.60/1.00  --prep_def_merge                        true
% 2.60/1.00  --prep_def_merge_prop_impl              false
% 2.60/1.00  --prep_def_merge_mbd                    true
% 2.60/1.00  --prep_def_merge_tr_red                 false
% 2.60/1.00  --prep_def_merge_tr_cl                  false
% 2.60/1.00  --smt_preprocessing                     true
% 2.60/1.00  --smt_ac_axioms                         fast
% 2.60/1.00  --preprocessed_out                      false
% 2.60/1.00  --preprocessed_stats                    false
% 2.60/1.00  
% 2.60/1.00  ------ Abstraction refinement Options
% 2.60/1.00  
% 2.60/1.00  --abstr_ref                             []
% 2.60/1.00  --abstr_ref_prep                        false
% 2.60/1.00  --abstr_ref_until_sat                   false
% 2.60/1.00  --abstr_ref_sig_restrict                funpre
% 2.60/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.60/1.00  --abstr_ref_under                       []
% 2.60/1.00  
% 2.60/1.00  ------ SAT Options
% 2.60/1.00  
% 2.60/1.00  --sat_mode                              false
% 2.60/1.00  --sat_fm_restart_options                ""
% 2.60/1.00  --sat_gr_def                            false
% 2.60/1.00  --sat_epr_types                         true
% 2.60/1.00  --sat_non_cyclic_types                  false
% 2.60/1.00  --sat_finite_models                     false
% 2.60/1.00  --sat_fm_lemmas                         false
% 2.60/1.00  --sat_fm_prep                           false
% 2.60/1.00  --sat_fm_uc_incr                        true
% 2.60/1.00  --sat_out_model                         small
% 2.60/1.00  --sat_out_clauses                       false
% 2.60/1.00  
% 2.60/1.00  ------ QBF Options
% 2.60/1.00  
% 2.60/1.00  --qbf_mode                              false
% 2.60/1.00  --qbf_elim_univ                         false
% 2.60/1.00  --qbf_dom_inst                          none
% 2.60/1.00  --qbf_dom_pre_inst                      false
% 2.60/1.00  --qbf_sk_in                             false
% 2.60/1.00  --qbf_pred_elim                         true
% 2.60/1.00  --qbf_split                             512
% 2.60/1.00  
% 2.60/1.00  ------ BMC1 Options
% 2.60/1.00  
% 2.60/1.00  --bmc1_incremental                      false
% 2.60/1.00  --bmc1_axioms                           reachable_all
% 2.60/1.00  --bmc1_min_bound                        0
% 2.60/1.00  --bmc1_max_bound                        -1
% 2.60/1.00  --bmc1_max_bound_default                -1
% 2.60/1.00  --bmc1_symbol_reachability              true
% 2.60/1.00  --bmc1_property_lemmas                  false
% 2.60/1.00  --bmc1_k_induction                      false
% 2.60/1.00  --bmc1_non_equiv_states                 false
% 2.60/1.00  --bmc1_deadlock                         false
% 2.60/1.00  --bmc1_ucm                              false
% 2.60/1.00  --bmc1_add_unsat_core                   none
% 2.60/1.00  --bmc1_unsat_core_children              false
% 2.60/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.60/1.00  --bmc1_out_stat                         full
% 2.60/1.00  --bmc1_ground_init                      false
% 2.60/1.00  --bmc1_pre_inst_next_state              false
% 2.60/1.00  --bmc1_pre_inst_state                   false
% 2.60/1.00  --bmc1_pre_inst_reach_state             false
% 2.60/1.00  --bmc1_out_unsat_core                   false
% 2.60/1.00  --bmc1_aig_witness_out                  false
% 2.60/1.00  --bmc1_verbose                          false
% 2.60/1.00  --bmc1_dump_clauses_tptp                false
% 2.60/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.60/1.00  --bmc1_dump_file                        -
% 2.60/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.60/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.60/1.00  --bmc1_ucm_extend_mode                  1
% 2.60/1.00  --bmc1_ucm_init_mode                    2
% 2.60/1.00  --bmc1_ucm_cone_mode                    none
% 2.60/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.60/1.00  --bmc1_ucm_relax_model                  4
% 2.60/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.60/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.60/1.00  --bmc1_ucm_layered_model                none
% 2.60/1.00  --bmc1_ucm_max_lemma_size               10
% 2.60/1.00  
% 2.60/1.00  ------ AIG Options
% 2.60/1.00  
% 2.60/1.00  --aig_mode                              false
% 2.60/1.00  
% 2.60/1.00  ------ Instantiation Options
% 2.60/1.00  
% 2.60/1.00  --instantiation_flag                    true
% 2.60/1.00  --inst_sos_flag                         false
% 2.60/1.00  --inst_sos_phase                        true
% 2.60/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.60/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.60/1.00  --inst_lit_sel_side                     none
% 2.60/1.00  --inst_solver_per_active                1400
% 2.60/1.00  --inst_solver_calls_frac                1.
% 2.60/1.00  --inst_passive_queue_type               priority_queues
% 2.60/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.60/1.00  --inst_passive_queues_freq              [25;2]
% 2.60/1.00  --inst_dismatching                      true
% 2.60/1.00  --inst_eager_unprocessed_to_passive     true
% 2.60/1.00  --inst_prop_sim_given                   true
% 2.60/1.00  --inst_prop_sim_new                     false
% 2.60/1.00  --inst_subs_new                         false
% 2.60/1.00  --inst_eq_res_simp                      false
% 2.60/1.00  --inst_subs_given                       false
% 2.60/1.00  --inst_orphan_elimination               true
% 2.60/1.00  --inst_learning_loop_flag               true
% 2.60/1.00  --inst_learning_start                   3000
% 2.60/1.00  --inst_learning_factor                  2
% 2.60/1.00  --inst_start_prop_sim_after_learn       3
% 2.60/1.00  --inst_sel_renew                        solver
% 2.60/1.00  --inst_lit_activity_flag                true
% 2.60/1.00  --inst_restr_to_given                   false
% 2.60/1.00  --inst_activity_threshold               500
% 2.60/1.00  --inst_out_proof                        true
% 2.60/1.00  
% 2.60/1.00  ------ Resolution Options
% 2.60/1.00  
% 2.60/1.00  --resolution_flag                       false
% 2.60/1.00  --res_lit_sel                           adaptive
% 2.60/1.00  --res_lit_sel_side                      none
% 2.60/1.00  --res_ordering                          kbo
% 2.60/1.00  --res_to_prop_solver                    active
% 2.60/1.00  --res_prop_simpl_new                    false
% 2.60/1.00  --res_prop_simpl_given                  true
% 2.60/1.00  --res_passive_queue_type                priority_queues
% 2.60/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.60/1.00  --res_passive_queues_freq               [15;5]
% 2.60/1.00  --res_forward_subs                      full
% 2.60/1.00  --res_backward_subs                     full
% 2.60/1.00  --res_forward_subs_resolution           true
% 2.60/1.00  --res_backward_subs_resolution          true
% 2.60/1.00  --res_orphan_elimination                true
% 2.60/1.00  --res_time_limit                        2.
% 2.60/1.00  --res_out_proof                         true
% 2.60/1.00  
% 2.60/1.00  ------ Superposition Options
% 2.60/1.00  
% 2.60/1.00  --superposition_flag                    true
% 2.60/1.00  --sup_passive_queue_type                priority_queues
% 2.60/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.60/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.60/1.00  --demod_completeness_check              fast
% 2.60/1.00  --demod_use_ground                      true
% 2.60/1.00  --sup_to_prop_solver                    passive
% 2.60/1.00  --sup_prop_simpl_new                    true
% 2.60/1.00  --sup_prop_simpl_given                  true
% 2.60/1.00  --sup_fun_splitting                     false
% 2.60/1.00  --sup_smt_interval                      50000
% 2.60/1.00  
% 2.60/1.00  ------ Superposition Simplification Setup
% 2.60/1.00  
% 2.60/1.00  --sup_indices_passive                   []
% 2.60/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.60/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/1.00  --sup_full_bw                           [BwDemod]
% 2.60/1.00  --sup_immed_triv                        [TrivRules]
% 2.60/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.60/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/1.00  --sup_immed_bw_main                     []
% 2.60/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.60/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.60/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.60/1.00  
% 2.60/1.00  ------ Combination Options
% 2.60/1.00  
% 2.60/1.00  --comb_res_mult                         3
% 2.60/1.00  --comb_sup_mult                         2
% 2.60/1.00  --comb_inst_mult                        10
% 2.60/1.00  
% 2.60/1.00  ------ Debug Options
% 2.60/1.00  
% 2.60/1.00  --dbg_backtrace                         false
% 2.60/1.00  --dbg_dump_prop_clauses                 false
% 2.60/1.00  --dbg_dump_prop_clauses_file            -
% 2.60/1.00  --dbg_out_stat                          false
% 2.60/1.00  
% 2.60/1.00  
% 2.60/1.00  
% 2.60/1.00  
% 2.60/1.00  ------ Proving...
% 2.60/1.00  
% 2.60/1.00  
% 2.60/1.00  % SZS status Theorem for theBenchmark.p
% 2.60/1.00  
% 2.60/1.00   Resolution empty clause
% 2.60/1.00  
% 2.60/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.60/1.00  
% 2.60/1.00  fof(f13,axiom,(
% 2.60/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f27,plain,(
% 2.60/1.00    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.60/1.00    inference(ennf_transformation,[],[f13])).
% 2.60/1.00  
% 2.60/1.00  fof(f28,plain,(
% 2.60/1.00    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.60/1.00    inference(flattening,[],[f27])).
% 2.60/1.00  
% 2.60/1.00  fof(f39,plain,(
% 2.60/1.00    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.60/1.00    inference(nnf_transformation,[],[f28])).
% 2.60/1.00  
% 2.60/1.00  fof(f61,plain,(
% 2.60/1.00    ( ! [X2,X0,X1] : (k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2 | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f39])).
% 2.60/1.00  
% 2.60/1.00  fof(f83,plain,(
% 2.60/1.00    ( ! [X0,X1] : (k1_xboole_0 = k1_funct_1(X0,X1) | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.60/1.00    inference(equality_resolution,[],[f61])).
% 2.60/1.00  
% 2.60/1.00  fof(f20,conjecture,(
% 2.60/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f21,negated_conjecture,(
% 2.60/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 2.60/1.00    inference(negated_conjecture,[],[f20])).
% 2.60/1.00  
% 2.60/1.00  fof(f36,plain,(
% 2.60/1.00    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 2.60/1.00    inference(ennf_transformation,[],[f21])).
% 2.60/1.00  
% 2.60/1.00  fof(f37,plain,(
% 2.60/1.00    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 2.60/1.00    inference(flattening,[],[f36])).
% 2.60/1.00  
% 2.60/1.00  fof(f42,plain,(
% 2.60/1.00    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK3,sK1),sK2) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3))),
% 2.60/1.00    introduced(choice_axiom,[])).
% 2.60/1.00  
% 2.60/1.00  fof(f43,plain,(
% 2.60/1.00    ~r2_hidden(k1_funct_1(sK3,sK1),sK2) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3)),
% 2.60/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f37,f42])).
% 2.60/1.00  
% 2.60/1.00  fof(f70,plain,(
% 2.60/1.00    v1_funct_1(sK3)),
% 2.60/1.00    inference(cnf_transformation,[],[f43])).
% 2.60/1.00  
% 2.60/1.00  fof(f72,plain,(
% 2.60/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 2.60/1.00    inference(cnf_transformation,[],[f43])).
% 2.60/1.00  
% 2.60/1.00  fof(f4,axiom,(
% 2.60/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f47,plain,(
% 2.60/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f4])).
% 2.60/1.00  
% 2.60/1.00  fof(f5,axiom,(
% 2.60/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f48,plain,(
% 2.60/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f5])).
% 2.60/1.00  
% 2.60/1.00  fof(f6,axiom,(
% 2.60/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f49,plain,(
% 2.60/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f6])).
% 2.60/1.00  
% 2.60/1.00  fof(f75,plain,(
% 2.60/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.60/1.00    inference(definition_unfolding,[],[f48,f49])).
% 2.60/1.00  
% 2.60/1.00  fof(f76,plain,(
% 2.60/1.00    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.60/1.00    inference(definition_unfolding,[],[f47,f75])).
% 2.60/1.00  
% 2.60/1.00  fof(f81,plain,(
% 2.60/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))),
% 2.60/1.00    inference(definition_unfolding,[],[f72,f76])).
% 2.60/1.00  
% 2.60/1.00  fof(f15,axiom,(
% 2.60/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f30,plain,(
% 2.60/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.60/1.00    inference(ennf_transformation,[],[f15])).
% 2.60/1.00  
% 2.60/1.00  fof(f63,plain,(
% 2.60/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.60/1.00    inference(cnf_transformation,[],[f30])).
% 2.60/1.00  
% 2.60/1.00  fof(f58,plain,(
% 2.60/1.00    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2 | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f39])).
% 2.60/1.00  
% 2.60/1.00  fof(f85,plain,(
% 2.60/1.00    ( ! [X0,X1] : (r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.60/1.00    inference(equality_resolution,[],[f58])).
% 2.60/1.00  
% 2.60/1.00  fof(f7,axiom,(
% 2.60/1.00    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f38,plain,(
% 2.60/1.00    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)))),
% 2.60/1.00    inference(nnf_transformation,[],[f7])).
% 2.60/1.00  
% 2.60/1.00  fof(f51,plain,(
% 2.60/1.00    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f38])).
% 2.60/1.00  
% 2.60/1.00  fof(f77,plain,(
% 2.60/1.00    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.60/1.00    inference(definition_unfolding,[],[f51,f76])).
% 2.60/1.00  
% 2.60/1.00  fof(f74,plain,(
% 2.60/1.00    ~r2_hidden(k1_funct_1(sK3,sK1),sK2)),
% 2.60/1.00    inference(cnf_transformation,[],[f43])).
% 2.60/1.00  
% 2.60/1.00  fof(f8,axiom,(
% 2.60/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f23,plain,(
% 2.60/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.60/1.00    inference(ennf_transformation,[],[f8])).
% 2.60/1.00  
% 2.60/1.00  fof(f52,plain,(
% 2.60/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.60/1.00    inference(cnf_transformation,[],[f23])).
% 2.60/1.00  
% 2.60/1.00  fof(f17,axiom,(
% 2.60/1.00    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f32,plain,(
% 2.60/1.00    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1) | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 2.60/1.00    inference(ennf_transformation,[],[f17])).
% 2.60/1.00  
% 2.60/1.00  fof(f66,plain,(
% 2.60/1.00    ( ! [X2,X0,X1] : (k1_mcart_1(X0) = X1 | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))) )),
% 2.60/1.00    inference(cnf_transformation,[],[f32])).
% 2.60/1.00  
% 2.60/1.00  fof(f80,plain,(
% 2.60/1.00    ( ! [X2,X0,X1] : (k1_mcart_1(X0) = X1 | ~r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2))) )),
% 2.60/1.00    inference(definition_unfolding,[],[f66,f76])).
% 2.60/1.00  
% 2.60/1.00  fof(f16,axiom,(
% 2.60/1.00    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f31,plain,(
% 2.60/1.00    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.60/1.00    inference(ennf_transformation,[],[f16])).
% 2.60/1.00  
% 2.60/1.00  fof(f64,plain,(
% 2.60/1.00    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 2.60/1.00    inference(cnf_transformation,[],[f31])).
% 2.60/1.00  
% 2.60/1.00  fof(f19,axiom,(
% 2.60/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f34,plain,(
% 2.60/1.00    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.60/1.00    inference(ennf_transformation,[],[f19])).
% 2.60/1.00  
% 2.60/1.00  fof(f35,plain,(
% 2.60/1.00    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.60/1.00    inference(flattening,[],[f34])).
% 2.60/1.00  
% 2.60/1.00  fof(f69,plain,(
% 2.60/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f35])).
% 2.60/1.00  
% 2.60/1.00  fof(f71,plain,(
% 2.60/1.00    v1_funct_2(sK3,k1_tarski(sK1),sK2)),
% 2.60/1.00    inference(cnf_transformation,[],[f43])).
% 2.60/1.00  
% 2.60/1.00  fof(f82,plain,(
% 2.60/1.00    v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2)),
% 2.60/1.00    inference(definition_unfolding,[],[f71,f76])).
% 2.60/1.00  
% 2.60/1.00  fof(f73,plain,(
% 2.60/1.00    k1_xboole_0 != sK2),
% 2.60/1.00    inference(cnf_transformation,[],[f43])).
% 2.60/1.00  
% 2.60/1.00  fof(f18,axiom,(
% 2.60/1.00    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f22,plain,(
% 2.60/1.00    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.60/1.00    inference(pure_predicate_removal,[],[f18])).
% 2.60/1.00  
% 2.60/1.00  fof(f33,plain,(
% 2.60/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.60/1.00    inference(ennf_transformation,[],[f22])).
% 2.60/1.00  
% 2.60/1.00  fof(f40,plain,(
% 2.60/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.60/1.00    introduced(choice_axiom,[])).
% 2.60/1.00  
% 2.60/1.00  fof(f41,plain,(
% 2.60/1.00    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 2.60/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f40])).
% 2.60/1.00  
% 2.60/1.00  fof(f68,plain,(
% 2.60/1.00    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 2.60/1.00    inference(cnf_transformation,[],[f41])).
% 2.60/1.00  
% 2.60/1.00  fof(f3,axiom,(
% 2.60/1.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f46,plain,(
% 2.60/1.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.60/1.00    inference(cnf_transformation,[],[f3])).
% 2.60/1.00  
% 2.60/1.00  fof(f50,plain,(
% 2.60/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f38])).
% 2.60/1.00  
% 2.60/1.00  fof(f78,plain,(
% 2.60/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) )),
% 2.60/1.00    inference(definition_unfolding,[],[f50,f76])).
% 2.60/1.00  
% 2.60/1.00  fof(f2,axiom,(
% 2.60/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f45,plain,(
% 2.60/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f2])).
% 2.60/1.00  
% 2.60/1.00  fof(f14,axiom,(
% 2.60/1.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f29,plain,(
% 2.60/1.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.60/1.00    inference(ennf_transformation,[],[f14])).
% 2.60/1.00  
% 2.60/1.00  fof(f62,plain,(
% 2.60/1.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f29])).
% 2.60/1.00  
% 2.60/1.00  cnf(c_11,plain,
% 2.60/1.00      ( r2_hidden(X0,k1_relat_1(X1))
% 2.60/1.00      | ~ v1_relat_1(X1)
% 2.60/1.00      | ~ v1_funct_1(X1)
% 2.60/1.00      | k1_funct_1(X1,X0) = k1_xboole_0 ),
% 2.60/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_27,negated_conjecture,
% 2.60/1.00      ( v1_funct_1(sK3) ),
% 2.60/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_474,plain,
% 2.60/1.00      ( r2_hidden(X0,k1_relat_1(X1))
% 2.60/1.00      | ~ v1_relat_1(X1)
% 2.60/1.00      | k1_funct_1(X1,X0) = k1_xboole_0
% 2.60/1.00      | sK3 != X1 ),
% 2.60/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_27]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_475,plain,
% 2.60/1.00      ( r2_hidden(X0,k1_relat_1(sK3))
% 2.60/1.00      | ~ v1_relat_1(sK3)
% 2.60/1.00      | k1_funct_1(sK3,X0) = k1_xboole_0 ),
% 2.60/1.00      inference(unflattening,[status(thm)],[c_474]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1408,plain,
% 2.60/1.00      ( k1_funct_1(sK3,X0) = k1_xboole_0
% 2.60/1.00      | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
% 2.60/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_475]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_25,negated_conjecture,
% 2.60/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
% 2.60/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_30,plain,
% 2.60/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) = iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_476,plain,
% 2.60/1.00      ( k1_funct_1(sK3,X0) = k1_xboole_0
% 2.60/1.00      | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
% 2.60/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_475]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_16,plain,
% 2.60/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.60/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1562,plain,
% 2.60/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
% 2.60/1.00      | v1_relat_1(sK3) ),
% 2.60/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1563,plain,
% 2.60/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) != iProver_top
% 2.60/1.00      | v1_relat_1(sK3) = iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_1562]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1623,plain,
% 2.60/1.00      ( r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
% 2.60/1.00      | k1_funct_1(sK3,X0) = k1_xboole_0 ),
% 2.60/1.00      inference(global_propositional_subsumption,
% 2.60/1.00                [status(thm)],
% 2.60/1.00                [c_1408,c_30,c_476,c_1563]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1624,plain,
% 2.60/1.00      ( k1_funct_1(sK3,X0) = k1_xboole_0
% 2.60/1.00      | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top ),
% 2.60/1.00      inference(renaming,[status(thm)],[c_1623]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_14,plain,
% 2.60/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.60/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 2.60/1.00      | ~ v1_relat_1(X1)
% 2.60/1.00      | ~ v1_funct_1(X1) ),
% 2.60/1.00      inference(cnf_transformation,[],[f85]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_441,plain,
% 2.60/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.60/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 2.60/1.00      | ~ v1_relat_1(X1)
% 2.60/1.00      | sK3 != X1 ),
% 2.60/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_27]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_442,plain,
% 2.60/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.60/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3)
% 2.60/1.00      | ~ v1_relat_1(sK3) ),
% 2.60/1.00      inference(unflattening,[status(thm)],[c_441]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1410,plain,
% 2.60/1.00      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.60/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) = iProver_top
% 2.60/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_442]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_443,plain,
% 2.60/1.00      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.60/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) = iProver_top
% 2.60/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_442]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1574,plain,
% 2.60/1.00      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) = iProver_top
% 2.60/1.00      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
% 2.60/1.00      inference(global_propositional_subsumption,
% 2.60/1.00                [status(thm)],
% 2.60/1.00                [c_1410,c_30,c_443,c_1563]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1575,plain,
% 2.60/1.00      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.60/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) = iProver_top ),
% 2.60/1.00      inference(renaming,[status(thm)],[c_1574]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_3,plain,
% 2.60/1.00      ( ~ r2_hidden(X0,X1)
% 2.60/1.00      | k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = k1_xboole_0 ),
% 2.60/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1425,plain,
% 2.60/1.00      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = k1_xboole_0
% 2.60/1.00      | r2_hidden(X0,X1) != iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2082,plain,
% 2.60/1.00      ( k4_xboole_0(k2_enumset1(k4_tarski(X0,k1_funct_1(sK3,X0)),k4_tarski(X0,k1_funct_1(sK3,X0)),k4_tarski(X0,k1_funct_1(sK3,X0)),k4_tarski(X0,k1_funct_1(sK3,X0))),sK3) = k1_xboole_0
% 2.60/1.00      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
% 2.60/1.00      inference(superposition,[status(thm)],[c_1575,c_1425]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_3061,plain,
% 2.60/1.00      ( k1_funct_1(sK3,X0) = k1_xboole_0
% 2.60/1.00      | k4_xboole_0(k2_enumset1(k4_tarski(X0,k1_funct_1(sK3,X0)),k4_tarski(X0,k1_funct_1(sK3,X0)),k4_tarski(X0,k1_funct_1(sK3,X0)),k4_tarski(X0,k1_funct_1(sK3,X0))),sK3) = k1_xboole_0 ),
% 2.60/1.00      inference(superposition,[status(thm)],[c_1624,c_2082]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_23,negated_conjecture,
% 2.60/1.00      ( ~ r2_hidden(k1_funct_1(sK3,sK1),sK2) ),
% 2.60/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_31,plain,
% 2.60/1.00      ( r2_hidden(k1_funct_1(sK3,sK1),sK2) != iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1413,plain,
% 2.60/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) = iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_5,plain,
% 2.60/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.60/1.00      | ~ r2_hidden(X2,X0)
% 2.60/1.00      | r2_hidden(X2,X1) ),
% 2.60/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1423,plain,
% 2.60/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.60/1.00      | r2_hidden(X2,X0) != iProver_top
% 2.60/1.00      | r2_hidden(X2,X1) = iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2229,plain,
% 2.60/1.00      ( r2_hidden(X0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) = iProver_top
% 2.60/1.00      | r2_hidden(X0,sK3) != iProver_top ),
% 2.60/1.00      inference(superposition,[status(thm)],[c_1413,c_1423]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_20,plain,
% 2.60/1.00      ( ~ r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2))
% 2.60/1.00      | k1_mcart_1(X0) = X1 ),
% 2.60/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1416,plain,
% 2.60/1.00      ( k1_mcart_1(X0) = X1
% 2.60/1.00      | r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2)) != iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2328,plain,
% 2.60/1.00      ( k1_mcart_1(X0) = sK1 | r2_hidden(X0,sK3) != iProver_top ),
% 2.60/1.00      inference(superposition,[status(thm)],[c_2229,c_1416]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2361,plain,
% 2.60/1.00      ( k1_mcart_1(k4_tarski(X0,k1_funct_1(sK3,X0))) = sK1
% 2.60/1.00      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
% 2.60/1.00      inference(superposition,[status(thm)],[c_1575,c_2328]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2429,plain,
% 2.60/1.00      ( k1_funct_1(sK3,X0) = k1_xboole_0
% 2.60/1.00      | k1_mcart_1(k4_tarski(X0,k1_funct_1(sK3,X0))) = sK1 ),
% 2.60/1.00      inference(superposition,[status(thm)],[c_1624,c_2361]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_18,plain,
% 2.60/1.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1) ),
% 2.60/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1418,plain,
% 2.60/1.00      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 2.60/1.00      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2327,plain,
% 2.60/1.00      ( r2_hidden(X0,sK3) != iProver_top
% 2.60/1.00      | r2_hidden(k1_mcart_1(X0),k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top ),
% 2.60/1.00      inference(superposition,[status(thm)],[c_2229,c_1418]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_22,plain,
% 2.60/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.60/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.60/1.00      | ~ r2_hidden(X3,X1)
% 2.60/1.00      | r2_hidden(k1_funct_1(X0,X3),X2)
% 2.60/1.00      | ~ v1_funct_1(X0)
% 2.60/1.00      | k1_xboole_0 = X2 ),
% 2.60/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_26,negated_conjecture,
% 2.60/1.00      ( v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
% 2.60/1.00      inference(cnf_transformation,[],[f82]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_350,plain,
% 2.60/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.60/1.00      | ~ r2_hidden(X3,X1)
% 2.60/1.00      | r2_hidden(k1_funct_1(X0,X3),X2)
% 2.60/1.00      | ~ v1_funct_1(X0)
% 2.60/1.00      | k2_enumset1(sK1,sK1,sK1,sK1) != X1
% 2.60/1.00      | sK2 != X2
% 2.60/1.00      | sK3 != X0
% 2.60/1.00      | k1_xboole_0 = X2 ),
% 2.60/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_26]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_351,plain,
% 2.60/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
% 2.60/1.00      | ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
% 2.60/1.00      | r2_hidden(k1_funct_1(sK3,X0),sK2)
% 2.60/1.00      | ~ v1_funct_1(sK3)
% 2.60/1.00      | k1_xboole_0 = sK2 ),
% 2.60/1.00      inference(unflattening,[status(thm)],[c_350]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_24,negated_conjecture,
% 2.60/1.00      ( k1_xboole_0 != sK2 ),
% 2.60/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_355,plain,
% 2.60/1.00      ( ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
% 2.60/1.00      | r2_hidden(k1_funct_1(sK3,X0),sK2) ),
% 2.60/1.00      inference(global_propositional_subsumption,
% 2.60/1.00                [status(thm)],
% 2.60/1.00                [c_351,c_27,c_25,c_24]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1411,plain,
% 2.60/1.00      ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
% 2.60/1.00      | r2_hidden(k1_funct_1(sK3,X0),sK2) = iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_355]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2507,plain,
% 2.60/1.00      ( r2_hidden(X0,sK3) != iProver_top
% 2.60/1.00      | r2_hidden(k1_funct_1(sK3,k1_mcart_1(X0)),sK2) = iProver_top ),
% 2.60/1.00      inference(superposition,[status(thm)],[c_2327,c_1411]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_3172,plain,
% 2.60/1.00      ( k1_funct_1(sK3,X0) = k1_xboole_0
% 2.60/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) != iProver_top
% 2.60/1.00      | r2_hidden(k1_funct_1(sK3,sK1),sK2) = iProver_top ),
% 2.60/1.00      inference(superposition,[status(thm)],[c_2429,c_2507]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_3311,plain,
% 2.60/1.00      ( k1_funct_1(sK3,X0) = k1_xboole_0 ),
% 2.60/1.00      inference(global_propositional_subsumption,
% 2.60/1.00                [status(thm)],
% 2.60/1.00                [c_3061,c_30,c_31,c_443,c_1563,c_1624,c_3172]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1414,plain,
% 2.60/1.00      ( r2_hidden(k1_funct_1(sK3,sK1),sK2) != iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_3315,plain,
% 2.60/1.00      ( r2_hidden(k1_xboole_0,sK2) != iProver_top ),
% 2.60/1.00      inference(demodulation,[status(thm)],[c_3311,c_1414]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_21,plain,
% 2.60/1.00      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 2.60/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1415,plain,
% 2.60/1.00      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2058,plain,
% 2.60/1.00      ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_xboole_0
% 2.60/1.00      | r2_hidden(k1_funct_1(sK3,sK0(k2_enumset1(sK1,sK1,sK1,sK1))),sK2) = iProver_top ),
% 2.60/1.00      inference(superposition,[status(thm)],[c_1415,c_1411]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2,plain,
% 2.60/1.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.60/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_4,plain,
% 2.60/1.00      ( r2_hidden(X0,X1)
% 2.60/1.00      | k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) != k1_xboole_0 ),
% 2.60/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1424,plain,
% 2.60/1.00      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) != k1_xboole_0
% 2.60/1.00      | r2_hidden(X0,X1) = iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1990,plain,
% 2.60/1.00      ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0
% 2.60/1.00      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 2.60/1.00      inference(superposition,[status(thm)],[c_2,c_1424]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1,plain,
% 2.60/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 2.60/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_15,plain,
% 2.60/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 2.60/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_339,plain,
% 2.60/1.00      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 2.60/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_15]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_340,plain,
% 2.60/1.00      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.60/1.00      inference(unflattening,[status(thm)],[c_339]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_341,plain,
% 2.60/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_340]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1995,plain,
% 2.60/1.00      ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0 ),
% 2.60/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1990,c_341]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_3195,plain,
% 2.60/1.00      ( r2_hidden(k1_funct_1(sK3,sK0(k2_enumset1(sK1,sK1,sK1,sK1))),sK2) = iProver_top ),
% 2.60/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_2058,c_1995]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_3322,plain,
% 2.60/1.00      ( r2_hidden(k1_xboole_0,sK2) = iProver_top ),
% 2.60/1.00      inference(demodulation,[status(thm)],[c_3311,c_3195]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_3363,plain,
% 2.60/1.00      ( $false ),
% 2.60/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_3315,c_3322]) ).
% 2.60/1.00  
% 2.60/1.00  
% 2.60/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.60/1.00  
% 2.60/1.00  ------                               Statistics
% 2.60/1.00  
% 2.60/1.00  ------ General
% 2.60/1.00  
% 2.60/1.00  abstr_ref_over_cycles:                  0
% 2.60/1.00  abstr_ref_under_cycles:                 0
% 2.60/1.00  gc_basic_clause_elim:                   0
% 2.60/1.00  forced_gc_time:                         0
% 2.60/1.00  parsing_time:                           0.01
% 2.60/1.00  unif_index_cands_time:                  0.
% 2.60/1.00  unif_index_add_time:                    0.
% 2.60/1.00  orderings_time:                         0.
% 2.60/1.00  out_proof_time:                         0.009
% 2.60/1.00  total_time:                             0.122
% 2.60/1.00  num_of_symbols:                         53
% 2.60/1.00  num_of_terms:                           2594
% 2.60/1.00  
% 2.60/1.00  ------ Preprocessing
% 2.60/1.00  
% 2.60/1.00  num_of_splits:                          0
% 2.60/1.00  num_of_split_atoms:                     0
% 2.60/1.00  num_of_reused_defs:                     0
% 2.60/1.00  num_eq_ax_congr_red:                    14
% 2.60/1.00  num_of_sem_filtered_clauses:            1
% 2.60/1.00  num_of_subtypes:                        0
% 2.60/1.00  monotx_restored_types:                  0
% 2.60/1.00  sat_num_of_epr_types:                   0
% 2.60/1.00  sat_num_of_non_cyclic_types:            0
% 2.60/1.00  sat_guarded_non_collapsed_types:        0
% 2.60/1.00  num_pure_diseq_elim:                    0
% 2.60/1.00  simp_replaced_by:                       0
% 2.60/1.00  res_preprocessed:                       126
% 2.60/1.00  prep_upred:                             0
% 2.60/1.00  prep_unflattend:                        26
% 2.60/1.00  smt_new_axioms:                         0
% 2.60/1.00  pred_elim_cands:                        3
% 2.60/1.00  pred_elim:                              4
% 2.60/1.00  pred_elim_cl:                           3
% 2.60/1.00  pred_elim_cycles:                       8
% 2.60/1.00  merged_defs:                            8
% 2.60/1.00  merged_defs_ncl:                        0
% 2.60/1.00  bin_hyper_res:                          8
% 2.60/1.00  prep_cycles:                            4
% 2.60/1.00  pred_elim_time:                         0.007
% 2.60/1.00  splitting_time:                         0.
% 2.60/1.00  sem_filter_time:                        0.
% 2.60/1.00  monotx_time:                            0.
% 2.60/1.00  subtype_inf_time:                       0.
% 2.60/1.00  
% 2.60/1.00  ------ Problem properties
% 2.60/1.00  
% 2.60/1.00  clauses:                                24
% 2.60/1.00  conjectures:                            3
% 2.60/1.00  epr:                                    2
% 2.60/1.00  horn:                                   22
% 2.60/1.00  ground:                                 5
% 2.60/1.00  unary:                                  10
% 2.60/1.00  binary:                                 9
% 2.60/1.00  lits:                                   44
% 2.60/1.00  lits_eq:                                11
% 2.60/1.00  fd_pure:                                0
% 2.60/1.00  fd_pseudo:                              0
% 2.60/1.00  fd_cond:                                1
% 2.60/1.00  fd_pseudo_cond:                         2
% 2.60/1.00  ac_symbols:                             0
% 2.60/1.00  
% 2.60/1.00  ------ Propositional Solver
% 2.60/1.00  
% 2.60/1.00  prop_solver_calls:                      28
% 2.60/1.00  prop_fast_solver_calls:                 705
% 2.60/1.00  smt_solver_calls:                       0
% 2.60/1.00  smt_fast_solver_calls:                  0
% 2.60/1.00  prop_num_of_clauses:                    956
% 2.60/1.00  prop_preprocess_simplified:             4310
% 2.60/1.00  prop_fo_subsumed:                       11
% 2.60/1.00  prop_solver_time:                       0.
% 2.60/1.00  smt_solver_time:                        0.
% 2.60/1.00  smt_fast_solver_time:                   0.
% 2.60/1.00  prop_fast_solver_time:                  0.
% 2.60/1.00  prop_unsat_core_time:                   0.
% 2.60/1.00  
% 2.60/1.00  ------ QBF
% 2.60/1.00  
% 2.60/1.00  qbf_q_res:                              0
% 2.60/1.00  qbf_num_tautologies:                    0
% 2.60/1.00  qbf_prep_cycles:                        0
% 2.60/1.00  
% 2.60/1.00  ------ BMC1
% 2.60/1.00  
% 2.60/1.00  bmc1_current_bound:                     -1
% 2.60/1.00  bmc1_last_solved_bound:                 -1
% 2.60/1.00  bmc1_unsat_core_size:                   -1
% 2.60/1.00  bmc1_unsat_core_parents_size:           -1
% 2.60/1.00  bmc1_merge_next_fun:                    0
% 2.60/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.60/1.00  
% 2.60/1.00  ------ Instantiation
% 2.60/1.00  
% 2.60/1.00  inst_num_of_clauses:                    316
% 2.60/1.00  inst_num_in_passive:                    115
% 2.60/1.00  inst_num_in_active:                     199
% 2.60/1.00  inst_num_in_unprocessed:                2
% 2.60/1.00  inst_num_of_loops:                      230
% 2.60/1.00  inst_num_of_learning_restarts:          0
% 2.60/1.00  inst_num_moves_active_passive:          28
% 2.60/1.00  inst_lit_activity:                      0
% 2.60/1.00  inst_lit_activity_moves:                0
% 2.60/1.00  inst_num_tautologies:                   0
% 2.60/1.00  inst_num_prop_implied:                  0
% 2.60/1.00  inst_num_existing_simplified:           0
% 2.60/1.00  inst_num_eq_res_simplified:             0
% 2.60/1.00  inst_num_child_elim:                    0
% 2.60/1.00  inst_num_of_dismatching_blockings:      100
% 2.60/1.00  inst_num_of_non_proper_insts:           258
% 2.60/1.00  inst_num_of_duplicates:                 0
% 2.60/1.00  inst_inst_num_from_inst_to_res:         0
% 2.60/1.00  inst_dismatching_checking_time:         0.
% 2.60/1.00  
% 2.60/1.00  ------ Resolution
% 2.60/1.00  
% 2.60/1.00  res_num_of_clauses:                     0
% 2.60/1.00  res_num_in_passive:                     0
% 2.60/1.00  res_num_in_active:                      0
% 2.60/1.00  res_num_of_loops:                       130
% 2.60/1.00  res_forward_subset_subsumed:            18
% 2.60/1.00  res_backward_subset_subsumed:           1
% 2.60/1.00  res_forward_subsumed:                   1
% 2.60/1.00  res_backward_subsumed:                  1
% 2.60/1.00  res_forward_subsumption_resolution:     3
% 2.60/1.00  res_backward_subsumption_resolution:    0
% 2.60/1.00  res_clause_to_clause_subsumption:       137
% 2.60/1.00  res_orphan_elimination:                 0
% 2.60/1.00  res_tautology_del:                      75
% 2.60/1.00  res_num_eq_res_simplified:              0
% 2.60/1.00  res_num_sel_changes:                    0
% 2.60/1.00  res_moves_from_active_to_pass:          0
% 2.60/1.00  
% 2.60/1.00  ------ Superposition
% 2.60/1.00  
% 2.60/1.00  sup_time_total:                         0.
% 2.60/1.00  sup_time_generating:                    0.
% 2.60/1.00  sup_time_sim_full:                      0.
% 2.60/1.00  sup_time_sim_immed:                     0.
% 2.60/1.00  
% 2.60/1.00  sup_num_of_clauses:                     65
% 2.60/1.00  sup_num_in_active:                      30
% 2.60/1.00  sup_num_in_passive:                     35
% 2.60/1.00  sup_num_of_loops:                       44
% 2.60/1.00  sup_fw_superposition:                   27
% 2.60/1.00  sup_bw_superposition:                   40
% 2.60/1.00  sup_immediate_simplified:               2
% 2.60/1.00  sup_given_eliminated:                   0
% 2.60/1.00  comparisons_done:                       0
% 2.60/1.00  comparisons_avoided:                    6
% 2.60/1.00  
% 2.60/1.00  ------ Simplifications
% 2.60/1.00  
% 2.60/1.00  
% 2.60/1.00  sim_fw_subset_subsumed:                 3
% 2.60/1.00  sim_bw_subset_subsumed:                 6
% 2.60/1.00  sim_fw_subsumed:                        1
% 2.60/1.00  sim_bw_subsumed:                        3
% 2.60/1.00  sim_fw_subsumption_res:                 2
% 2.60/1.00  sim_bw_subsumption_res:                 0
% 2.60/1.00  sim_tautology_del:                      0
% 2.60/1.00  sim_eq_tautology_del:                   3
% 2.60/1.00  sim_eq_res_simp:                        0
% 2.60/1.00  sim_fw_demodulated:                     0
% 2.60/1.00  sim_bw_demodulated:                     11
% 2.60/1.00  sim_light_normalised:                   1
% 2.60/1.00  sim_joinable_taut:                      0
% 2.60/1.00  sim_joinable_simp:                      0
% 2.60/1.00  sim_ac_normalised:                      0
% 2.60/1.00  sim_smt_subsumption:                    0
% 2.60/1.00  
%------------------------------------------------------------------------------
