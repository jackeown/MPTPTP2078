%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:45 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 505 expanded)
%              Number of clauses        :   65 ( 142 expanded)
%              Number of leaves         :   23 ( 115 expanded)
%              Depth                    :   19
%              Number of atoms          :  337 (1466 expanded)
%              Number of equality atoms :  125 ( 481 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,axiom,(
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

fof(f23,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f23])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f44])).

fof(f72,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f39,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f40,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f46,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(k1_funct_1(sK4,sK2),sK3)
      & k1_xboole_0 != sK3
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
      & v1_funct_2(sK4,k1_tarski(sK2),sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK2),sK3)
    & k1_xboole_0 != sK3
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
    & v1_funct_2(sK4,k1_tarski(sK2),sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f40,f46])).

fof(f76,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) ),
    inference(cnf_transformation,[],[f47])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f79,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f80,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f79])).

fof(f84,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) ),
    inference(definition_unfolding,[],[f76,f80])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 )
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X0) = X1
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X0) = X1
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2)) ) ),
    inference(definition_unfolding,[],[f70,f80])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f37])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f75,plain,(
    v1_funct_2(sK4,k1_tarski(sK2),sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f85,plain,(
    v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
    inference(definition_unfolding,[],[f75,f80])).

fof(f74,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f77,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f47])).

fof(f78,plain,(
    ~ r2_hidden(k1_funct_1(sK4,sK2),sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f7,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f41])).

fof(f54,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f42])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f81,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f53,f79])).

fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f14,axiom,(
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

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_funct_1(X0,X1) != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_funct_1(X0,X1)
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f61,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

cnf(c_21,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1341,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1339,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1354,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2266,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1339,c_1354])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2))
    | k1_mcart_1(X0) = X1 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1342,plain,
    ( k1_mcart_1(X0) = X1
    | r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2317,plain,
    ( k1_mcart_1(X0) = sK2
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2266,c_1342])).

cnf(c_2469,plain,
    ( k1_mcart_1(sK1(sK4)) = sK2
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1341,c_2317])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1344,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2316,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(k1_mcart_1(X0),k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2266,c_1344])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_295,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k1_funct_1(X2,X0),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X2)
    | k2_enumset1(sK2,sK2,sK2,sK2) != X1
    | sK3 != X3
    | sK4 != X2
    | k1_xboole_0 = X3 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_26])).

cnf(c_296,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2))
    | r2_hidden(k1_funct_1(sK4,X0),sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_295])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_300,plain,
    ( r2_hidden(k1_funct_1(sK4,X0),sK3)
    | ~ r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_296,c_27,c_25,c_24])).

cnf(c_301,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2))
    | r2_hidden(k1_funct_1(sK4,X0),sK3) ),
    inference(renaming,[status(thm)],[c_300])).

cnf(c_1336,plain,
    ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_301])).

cnf(c_2615,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(k1_funct_1(sK4,k1_mcart_1(X0)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2316,c_1336])).

cnf(c_2705,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(k1_funct_1(sK4,sK2),sK3) = iProver_top
    | r2_hidden(sK1(sK4),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2469,c_2615])).

cnf(c_23,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(sK4,sK2),sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_31,plain,
    ( r2_hidden(k1_funct_1(sK4,sK2),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3502,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK1(sK4),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2705,c_31])).

cnf(c_3508,plain,
    ( sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1341,c_3502])).

cnf(c_3,plain,
    ( m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1355,plain,
    ( m1_subset_1(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1352,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2165,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1355,c_1352])).

cnf(c_3051,plain,
    ( r2_hidden(k1_funct_1(sK4,sK0(k2_enumset1(sK2,sK2,sK2,sK2))),sK3) = iProver_top
    | v1_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2165,c_1336])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1356,plain,
    ( v1_xboole_0(k2_enumset1(X0,X0,X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3265,plain,
    ( r2_hidden(k1_funct_1(sK4,sK0(k2_enumset1(sK2,sK2,sK2,sK2))),sK3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3051,c_1356])).

cnf(c_3647,plain,
    ( r2_hidden(k1_funct_1(k1_xboole_0,sK0(k2_enumset1(sK2,sK2,sK2,sK2))),sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3508,c_3265])).

cnf(c_9,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_12,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1349,plain,
    ( k1_funct_1(X0,X1) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2900,plain,
    ( k1_funct_1(k1_xboole_0,X0) = k1_xboole_0
    | r2_hidden(X0,k1_xboole_0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_1349])).

cnf(c_10,plain,
    ( v1_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_66,plain,
    ( v1_funct_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_68,plain,
    ( v1_funct_1(k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_66])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_88,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_284,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_15])).

cnf(c_285,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_284])).

cnf(c_286,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_285])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1515,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1517,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1515])).

cnf(c_5,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1516,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1519,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1516])).

cnf(c_2941,plain,
    ( k1_funct_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2900,c_68,c_88,c_286,c_1517,c_1519])).

cnf(c_3697,plain,
    ( r2_hidden(k1_xboole_0,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3647,c_2941])).

cnf(c_1340,plain,
    ( r2_hidden(k1_funct_1(sK4,sK2),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3662,plain,
    ( r2_hidden(k1_funct_1(k1_xboole_0,sK2),sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3508,c_1340])).

cnf(c_3665,plain,
    ( r2_hidden(k1_xboole_0,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3662,c_2941])).

cnf(c_3699,plain,
    ( $false ),
    inference(backward_subsumption_resolution,[status(thm)],[c_3697,c_3665])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:06:17 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.99/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/0.99  
% 2.99/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.99/0.99  
% 2.99/0.99  ------  iProver source info
% 2.99/0.99  
% 2.99/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.99/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.99/0.99  git: non_committed_changes: false
% 2.99/0.99  git: last_make_outside_of_git: false
% 2.99/0.99  
% 2.99/0.99  ------ 
% 2.99/0.99  
% 2.99/0.99  ------ Input Options
% 2.99/0.99  
% 2.99/0.99  --out_options                           all
% 2.99/0.99  --tptp_safe_out                         true
% 2.99/0.99  --problem_path                          ""
% 2.99/0.99  --include_path                          ""
% 2.99/0.99  --clausifier                            res/vclausify_rel
% 2.99/0.99  --clausifier_options                    --mode clausify
% 2.99/0.99  --stdin                                 false
% 2.99/0.99  --stats_out                             all
% 2.99/0.99  
% 2.99/0.99  ------ General Options
% 2.99/0.99  
% 2.99/0.99  --fof                                   false
% 2.99/0.99  --time_out_real                         305.
% 2.99/0.99  --time_out_virtual                      -1.
% 2.99/0.99  --symbol_type_check                     false
% 2.99/0.99  --clausify_out                          false
% 2.99/0.99  --sig_cnt_out                           false
% 2.99/0.99  --trig_cnt_out                          false
% 2.99/0.99  --trig_cnt_out_tolerance                1.
% 2.99/0.99  --trig_cnt_out_sk_spl                   false
% 2.99/0.99  --abstr_cl_out                          false
% 2.99/0.99  
% 2.99/0.99  ------ Global Options
% 2.99/0.99  
% 2.99/0.99  --schedule                              default
% 2.99/0.99  --add_important_lit                     false
% 2.99/0.99  --prop_solver_per_cl                    1000
% 2.99/0.99  --min_unsat_core                        false
% 2.99/0.99  --soft_assumptions                      false
% 2.99/0.99  --soft_lemma_size                       3
% 2.99/0.99  --prop_impl_unit_size                   0
% 2.99/0.99  --prop_impl_unit                        []
% 2.99/0.99  --share_sel_clauses                     true
% 2.99/0.99  --reset_solvers                         false
% 2.99/0.99  --bc_imp_inh                            [conj_cone]
% 2.99/0.99  --conj_cone_tolerance                   3.
% 2.99/0.99  --extra_neg_conj                        none
% 2.99/0.99  --large_theory_mode                     true
% 2.99/0.99  --prolific_symb_bound                   200
% 2.99/0.99  --lt_threshold                          2000
% 2.99/0.99  --clause_weak_htbl                      true
% 2.99/0.99  --gc_record_bc_elim                     false
% 2.99/0.99  
% 2.99/0.99  ------ Preprocessing Options
% 2.99/0.99  
% 2.99/0.99  --preprocessing_flag                    true
% 2.99/0.99  --time_out_prep_mult                    0.1
% 2.99/0.99  --splitting_mode                        input
% 2.99/0.99  --splitting_grd                         true
% 2.99/0.99  --splitting_cvd                         false
% 2.99/0.99  --splitting_cvd_svl                     false
% 2.99/0.99  --splitting_nvd                         32
% 2.99/0.99  --sub_typing                            true
% 2.99/0.99  --prep_gs_sim                           true
% 2.99/0.99  --prep_unflatten                        true
% 2.99/0.99  --prep_res_sim                          true
% 2.99/0.99  --prep_upred                            true
% 2.99/0.99  --prep_sem_filter                       exhaustive
% 2.99/0.99  --prep_sem_filter_out                   false
% 2.99/0.99  --pred_elim                             true
% 2.99/0.99  --res_sim_input                         true
% 2.99/0.99  --eq_ax_congr_red                       true
% 2.99/0.99  --pure_diseq_elim                       true
% 2.99/0.99  --brand_transform                       false
% 2.99/0.99  --non_eq_to_eq                          false
% 2.99/0.99  --prep_def_merge                        true
% 2.99/0.99  --prep_def_merge_prop_impl              false
% 2.99/0.99  --prep_def_merge_mbd                    true
% 2.99/0.99  --prep_def_merge_tr_red                 false
% 2.99/0.99  --prep_def_merge_tr_cl                  false
% 2.99/0.99  --smt_preprocessing                     true
% 2.99/0.99  --smt_ac_axioms                         fast
% 2.99/0.99  --preprocessed_out                      false
% 2.99/0.99  --preprocessed_stats                    false
% 2.99/0.99  
% 2.99/0.99  ------ Abstraction refinement Options
% 2.99/0.99  
% 2.99/0.99  --abstr_ref                             []
% 2.99/0.99  --abstr_ref_prep                        false
% 2.99/0.99  --abstr_ref_until_sat                   false
% 2.99/0.99  --abstr_ref_sig_restrict                funpre
% 2.99/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.99/0.99  --abstr_ref_under                       []
% 2.99/0.99  
% 2.99/0.99  ------ SAT Options
% 2.99/0.99  
% 2.99/0.99  --sat_mode                              false
% 2.99/0.99  --sat_fm_restart_options                ""
% 2.99/0.99  --sat_gr_def                            false
% 2.99/0.99  --sat_epr_types                         true
% 2.99/0.99  --sat_non_cyclic_types                  false
% 2.99/0.99  --sat_finite_models                     false
% 2.99/0.99  --sat_fm_lemmas                         false
% 2.99/0.99  --sat_fm_prep                           false
% 2.99/0.99  --sat_fm_uc_incr                        true
% 2.99/0.99  --sat_out_model                         small
% 2.99/0.99  --sat_out_clauses                       false
% 2.99/0.99  
% 2.99/0.99  ------ QBF Options
% 2.99/0.99  
% 2.99/0.99  --qbf_mode                              false
% 2.99/0.99  --qbf_elim_univ                         false
% 2.99/0.99  --qbf_dom_inst                          none
% 2.99/0.99  --qbf_dom_pre_inst                      false
% 2.99/0.99  --qbf_sk_in                             false
% 2.99/0.99  --qbf_pred_elim                         true
% 2.99/0.99  --qbf_split                             512
% 2.99/0.99  
% 2.99/0.99  ------ BMC1 Options
% 2.99/0.99  
% 2.99/0.99  --bmc1_incremental                      false
% 2.99/0.99  --bmc1_axioms                           reachable_all
% 2.99/0.99  --bmc1_min_bound                        0
% 2.99/0.99  --bmc1_max_bound                        -1
% 2.99/0.99  --bmc1_max_bound_default                -1
% 2.99/0.99  --bmc1_symbol_reachability              true
% 2.99/0.99  --bmc1_property_lemmas                  false
% 2.99/0.99  --bmc1_k_induction                      false
% 2.99/0.99  --bmc1_non_equiv_states                 false
% 2.99/0.99  --bmc1_deadlock                         false
% 2.99/0.99  --bmc1_ucm                              false
% 2.99/0.99  --bmc1_add_unsat_core                   none
% 2.99/0.99  --bmc1_unsat_core_children              false
% 2.99/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.99/0.99  --bmc1_out_stat                         full
% 2.99/0.99  --bmc1_ground_init                      false
% 2.99/0.99  --bmc1_pre_inst_next_state              false
% 2.99/0.99  --bmc1_pre_inst_state                   false
% 2.99/0.99  --bmc1_pre_inst_reach_state             false
% 2.99/0.99  --bmc1_out_unsat_core                   false
% 2.99/0.99  --bmc1_aig_witness_out                  false
% 2.99/0.99  --bmc1_verbose                          false
% 2.99/0.99  --bmc1_dump_clauses_tptp                false
% 2.99/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.99/0.99  --bmc1_dump_file                        -
% 2.99/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.99/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.99/0.99  --bmc1_ucm_extend_mode                  1
% 2.99/0.99  --bmc1_ucm_init_mode                    2
% 2.99/0.99  --bmc1_ucm_cone_mode                    none
% 2.99/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.99/0.99  --bmc1_ucm_relax_model                  4
% 2.99/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.99/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.99/0.99  --bmc1_ucm_layered_model                none
% 2.99/0.99  --bmc1_ucm_max_lemma_size               10
% 2.99/0.99  
% 2.99/0.99  ------ AIG Options
% 2.99/0.99  
% 2.99/0.99  --aig_mode                              false
% 2.99/0.99  
% 2.99/0.99  ------ Instantiation Options
% 2.99/0.99  
% 2.99/0.99  --instantiation_flag                    true
% 2.99/0.99  --inst_sos_flag                         false
% 2.99/0.99  --inst_sos_phase                        true
% 2.99/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.99/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.99/0.99  --inst_lit_sel_side                     num_symb
% 2.99/0.99  --inst_solver_per_active                1400
% 2.99/0.99  --inst_solver_calls_frac                1.
% 2.99/0.99  --inst_passive_queue_type               priority_queues
% 2.99/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.99/0.99  --inst_passive_queues_freq              [25;2]
% 2.99/0.99  --inst_dismatching                      true
% 2.99/0.99  --inst_eager_unprocessed_to_passive     true
% 2.99/0.99  --inst_prop_sim_given                   true
% 2.99/0.99  --inst_prop_sim_new                     false
% 2.99/0.99  --inst_subs_new                         false
% 2.99/0.99  --inst_eq_res_simp                      false
% 2.99/0.99  --inst_subs_given                       false
% 2.99/0.99  --inst_orphan_elimination               true
% 2.99/0.99  --inst_learning_loop_flag               true
% 2.99/0.99  --inst_learning_start                   3000
% 2.99/0.99  --inst_learning_factor                  2
% 2.99/0.99  --inst_start_prop_sim_after_learn       3
% 2.99/0.99  --inst_sel_renew                        solver
% 2.99/0.99  --inst_lit_activity_flag                true
% 2.99/0.99  --inst_restr_to_given                   false
% 2.99/0.99  --inst_activity_threshold               500
% 2.99/0.99  --inst_out_proof                        true
% 2.99/0.99  
% 2.99/0.99  ------ Resolution Options
% 2.99/0.99  
% 2.99/0.99  --resolution_flag                       true
% 2.99/0.99  --res_lit_sel                           adaptive
% 2.99/0.99  --res_lit_sel_side                      none
% 2.99/0.99  --res_ordering                          kbo
% 2.99/0.99  --res_to_prop_solver                    active
% 2.99/0.99  --res_prop_simpl_new                    false
% 2.99/0.99  --res_prop_simpl_given                  true
% 2.99/0.99  --res_passive_queue_type                priority_queues
% 2.99/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.99/0.99  --res_passive_queues_freq               [15;5]
% 2.99/0.99  --res_forward_subs                      full
% 2.99/0.99  --res_backward_subs                     full
% 2.99/0.99  --res_forward_subs_resolution           true
% 2.99/0.99  --res_backward_subs_resolution          true
% 2.99/0.99  --res_orphan_elimination                true
% 2.99/0.99  --res_time_limit                        2.
% 2.99/0.99  --res_out_proof                         true
% 2.99/0.99  
% 2.99/0.99  ------ Superposition Options
% 2.99/0.99  
% 2.99/0.99  --superposition_flag                    true
% 2.99/0.99  --sup_passive_queue_type                priority_queues
% 2.99/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.99/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.99/0.99  --demod_completeness_check              fast
% 2.99/0.99  --demod_use_ground                      true
% 2.99/0.99  --sup_to_prop_solver                    passive
% 2.99/0.99  --sup_prop_simpl_new                    true
% 2.99/0.99  --sup_prop_simpl_given                  true
% 2.99/0.99  --sup_fun_splitting                     false
% 2.99/0.99  --sup_smt_interval                      50000
% 2.99/0.99  
% 2.99/0.99  ------ Superposition Simplification Setup
% 2.99/0.99  
% 2.99/0.99  --sup_indices_passive                   []
% 2.99/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.99/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.99  --sup_full_bw                           [BwDemod]
% 2.99/0.99  --sup_immed_triv                        [TrivRules]
% 2.99/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.99/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.99  --sup_immed_bw_main                     []
% 2.99/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.99/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.99/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.99/0.99  
% 2.99/0.99  ------ Combination Options
% 2.99/0.99  
% 2.99/0.99  --comb_res_mult                         3
% 2.99/0.99  --comb_sup_mult                         2
% 2.99/0.99  --comb_inst_mult                        10
% 2.99/0.99  
% 2.99/0.99  ------ Debug Options
% 2.99/0.99  
% 2.99/0.99  --dbg_backtrace                         false
% 2.99/0.99  --dbg_dump_prop_clauses                 false
% 2.99/0.99  --dbg_dump_prop_clauses_file            -
% 2.99/0.99  --dbg_out_stat                          false
% 2.99/0.99  ------ Parsing...
% 2.99/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.99/0.99  
% 2.99/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.99/0.99  
% 2.99/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.99/0.99  
% 2.99/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.99/0.99  ------ Proving...
% 2.99/0.99  ------ Problem Properties 
% 2.99/0.99  
% 2.99/0.99  
% 2.99/0.99  clauses                                 25
% 2.99/0.99  conjectures                             4
% 2.99/0.99  EPR                                     6
% 2.99/0.99  Horn                                    22
% 2.99/0.99  unary                                   11
% 2.99/0.99  binary                                  8
% 2.99/0.99  lits                                    49
% 2.99/0.99  lits eq                                 7
% 2.99/0.99  fd_pure                                 0
% 2.99/0.99  fd_pseudo                               0
% 2.99/0.99  fd_cond                                 1
% 2.99/0.99  fd_pseudo_cond                          2
% 2.99/0.99  AC symbols                              0
% 2.99/0.99  
% 2.99/0.99  ------ Schedule dynamic 5 is on 
% 2.99/0.99  
% 2.99/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.99/0.99  
% 2.99/0.99  
% 2.99/0.99  ------ 
% 2.99/0.99  Current options:
% 2.99/0.99  ------ 
% 2.99/0.99  
% 2.99/0.99  ------ Input Options
% 2.99/0.99  
% 2.99/0.99  --out_options                           all
% 2.99/0.99  --tptp_safe_out                         true
% 2.99/0.99  --problem_path                          ""
% 2.99/0.99  --include_path                          ""
% 2.99/0.99  --clausifier                            res/vclausify_rel
% 2.99/0.99  --clausifier_options                    --mode clausify
% 2.99/0.99  --stdin                                 false
% 2.99/0.99  --stats_out                             all
% 2.99/0.99  
% 2.99/0.99  ------ General Options
% 2.99/0.99  
% 2.99/0.99  --fof                                   false
% 2.99/0.99  --time_out_real                         305.
% 2.99/0.99  --time_out_virtual                      -1.
% 2.99/0.99  --symbol_type_check                     false
% 2.99/0.99  --clausify_out                          false
% 2.99/0.99  --sig_cnt_out                           false
% 2.99/0.99  --trig_cnt_out                          false
% 2.99/0.99  --trig_cnt_out_tolerance                1.
% 2.99/0.99  --trig_cnt_out_sk_spl                   false
% 2.99/0.99  --abstr_cl_out                          false
% 2.99/0.99  
% 2.99/0.99  ------ Global Options
% 2.99/0.99  
% 2.99/0.99  --schedule                              default
% 2.99/0.99  --add_important_lit                     false
% 2.99/0.99  --prop_solver_per_cl                    1000
% 2.99/0.99  --min_unsat_core                        false
% 2.99/0.99  --soft_assumptions                      false
% 2.99/0.99  --soft_lemma_size                       3
% 2.99/0.99  --prop_impl_unit_size                   0
% 2.99/0.99  --prop_impl_unit                        []
% 2.99/0.99  --share_sel_clauses                     true
% 2.99/0.99  --reset_solvers                         false
% 2.99/0.99  --bc_imp_inh                            [conj_cone]
% 2.99/0.99  --conj_cone_tolerance                   3.
% 2.99/0.99  --extra_neg_conj                        none
% 2.99/0.99  --large_theory_mode                     true
% 2.99/0.99  --prolific_symb_bound                   200
% 2.99/0.99  --lt_threshold                          2000
% 2.99/0.99  --clause_weak_htbl                      true
% 2.99/0.99  --gc_record_bc_elim                     false
% 2.99/0.99  
% 2.99/0.99  ------ Preprocessing Options
% 2.99/0.99  
% 2.99/0.99  --preprocessing_flag                    true
% 2.99/0.99  --time_out_prep_mult                    0.1
% 2.99/0.99  --splitting_mode                        input
% 2.99/0.99  --splitting_grd                         true
% 2.99/0.99  --splitting_cvd                         false
% 2.99/0.99  --splitting_cvd_svl                     false
% 2.99/0.99  --splitting_nvd                         32
% 2.99/0.99  --sub_typing                            true
% 2.99/0.99  --prep_gs_sim                           true
% 2.99/0.99  --prep_unflatten                        true
% 2.99/0.99  --prep_res_sim                          true
% 2.99/0.99  --prep_upred                            true
% 2.99/0.99  --prep_sem_filter                       exhaustive
% 2.99/0.99  --prep_sem_filter_out                   false
% 2.99/0.99  --pred_elim                             true
% 2.99/0.99  --res_sim_input                         true
% 2.99/0.99  --eq_ax_congr_red                       true
% 2.99/0.99  --pure_diseq_elim                       true
% 2.99/0.99  --brand_transform                       false
% 2.99/0.99  --non_eq_to_eq                          false
% 2.99/0.99  --prep_def_merge                        true
% 2.99/0.99  --prep_def_merge_prop_impl              false
% 2.99/0.99  --prep_def_merge_mbd                    true
% 2.99/0.99  --prep_def_merge_tr_red                 false
% 2.99/0.99  --prep_def_merge_tr_cl                  false
% 2.99/0.99  --smt_preprocessing                     true
% 2.99/0.99  --smt_ac_axioms                         fast
% 2.99/0.99  --preprocessed_out                      false
% 2.99/0.99  --preprocessed_stats                    false
% 2.99/0.99  
% 2.99/0.99  ------ Abstraction refinement Options
% 2.99/0.99  
% 2.99/0.99  --abstr_ref                             []
% 2.99/0.99  --abstr_ref_prep                        false
% 2.99/0.99  --abstr_ref_until_sat                   false
% 2.99/0.99  --abstr_ref_sig_restrict                funpre
% 2.99/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.99/0.99  --abstr_ref_under                       []
% 2.99/0.99  
% 2.99/0.99  ------ SAT Options
% 2.99/0.99  
% 2.99/0.99  --sat_mode                              false
% 2.99/0.99  --sat_fm_restart_options                ""
% 2.99/0.99  --sat_gr_def                            false
% 2.99/0.99  --sat_epr_types                         true
% 2.99/0.99  --sat_non_cyclic_types                  false
% 2.99/0.99  --sat_finite_models                     false
% 2.99/0.99  --sat_fm_lemmas                         false
% 2.99/0.99  --sat_fm_prep                           false
% 2.99/0.99  --sat_fm_uc_incr                        true
% 2.99/0.99  --sat_out_model                         small
% 2.99/0.99  --sat_out_clauses                       false
% 2.99/0.99  
% 2.99/0.99  ------ QBF Options
% 2.99/0.99  
% 2.99/0.99  --qbf_mode                              false
% 2.99/0.99  --qbf_elim_univ                         false
% 2.99/0.99  --qbf_dom_inst                          none
% 2.99/0.99  --qbf_dom_pre_inst                      false
% 2.99/0.99  --qbf_sk_in                             false
% 2.99/0.99  --qbf_pred_elim                         true
% 2.99/0.99  --qbf_split                             512
% 2.99/0.99  
% 2.99/0.99  ------ BMC1 Options
% 2.99/0.99  
% 2.99/0.99  --bmc1_incremental                      false
% 2.99/0.99  --bmc1_axioms                           reachable_all
% 2.99/0.99  --bmc1_min_bound                        0
% 2.99/0.99  --bmc1_max_bound                        -1
% 2.99/0.99  --bmc1_max_bound_default                -1
% 2.99/0.99  --bmc1_symbol_reachability              true
% 2.99/0.99  --bmc1_property_lemmas                  false
% 2.99/0.99  --bmc1_k_induction                      false
% 2.99/0.99  --bmc1_non_equiv_states                 false
% 2.99/0.99  --bmc1_deadlock                         false
% 2.99/0.99  --bmc1_ucm                              false
% 2.99/0.99  --bmc1_add_unsat_core                   none
% 2.99/0.99  --bmc1_unsat_core_children              false
% 2.99/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.99/0.99  --bmc1_out_stat                         full
% 2.99/0.99  --bmc1_ground_init                      false
% 2.99/0.99  --bmc1_pre_inst_next_state              false
% 2.99/0.99  --bmc1_pre_inst_state                   false
% 2.99/0.99  --bmc1_pre_inst_reach_state             false
% 2.99/0.99  --bmc1_out_unsat_core                   false
% 2.99/0.99  --bmc1_aig_witness_out                  false
% 2.99/0.99  --bmc1_verbose                          false
% 2.99/0.99  --bmc1_dump_clauses_tptp                false
% 2.99/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.99/0.99  --bmc1_dump_file                        -
% 2.99/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.99/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.99/0.99  --bmc1_ucm_extend_mode                  1
% 2.99/0.99  --bmc1_ucm_init_mode                    2
% 2.99/0.99  --bmc1_ucm_cone_mode                    none
% 2.99/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.99/0.99  --bmc1_ucm_relax_model                  4
% 2.99/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.99/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.99/0.99  --bmc1_ucm_layered_model                none
% 2.99/0.99  --bmc1_ucm_max_lemma_size               10
% 2.99/0.99  
% 2.99/0.99  ------ AIG Options
% 2.99/0.99  
% 2.99/0.99  --aig_mode                              false
% 2.99/0.99  
% 2.99/0.99  ------ Instantiation Options
% 2.99/0.99  
% 2.99/0.99  --instantiation_flag                    true
% 2.99/0.99  --inst_sos_flag                         false
% 2.99/0.99  --inst_sos_phase                        true
% 2.99/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.99/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.99/0.99  --inst_lit_sel_side                     none
% 2.99/0.99  --inst_solver_per_active                1400
% 2.99/0.99  --inst_solver_calls_frac                1.
% 2.99/0.99  --inst_passive_queue_type               priority_queues
% 2.99/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.99/0.99  --inst_passive_queues_freq              [25;2]
% 2.99/0.99  --inst_dismatching                      true
% 2.99/0.99  --inst_eager_unprocessed_to_passive     true
% 2.99/0.99  --inst_prop_sim_given                   true
% 2.99/0.99  --inst_prop_sim_new                     false
% 2.99/0.99  --inst_subs_new                         false
% 2.99/0.99  --inst_eq_res_simp                      false
% 2.99/0.99  --inst_subs_given                       false
% 2.99/0.99  --inst_orphan_elimination               true
% 2.99/0.99  --inst_learning_loop_flag               true
% 2.99/0.99  --inst_learning_start                   3000
% 2.99/0.99  --inst_learning_factor                  2
% 2.99/0.99  --inst_start_prop_sim_after_learn       3
% 2.99/0.99  --inst_sel_renew                        solver
% 2.99/0.99  --inst_lit_activity_flag                true
% 2.99/0.99  --inst_restr_to_given                   false
% 2.99/0.99  --inst_activity_threshold               500
% 2.99/0.99  --inst_out_proof                        true
% 2.99/0.99  
% 2.99/0.99  ------ Resolution Options
% 2.99/0.99  
% 2.99/0.99  --resolution_flag                       false
% 2.99/0.99  --res_lit_sel                           adaptive
% 2.99/0.99  --res_lit_sel_side                      none
% 2.99/0.99  --res_ordering                          kbo
% 2.99/0.99  --res_to_prop_solver                    active
% 2.99/0.99  --res_prop_simpl_new                    false
% 2.99/0.99  --res_prop_simpl_given                  true
% 2.99/0.99  --res_passive_queue_type                priority_queues
% 2.99/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.99/0.99  --res_passive_queues_freq               [15;5]
% 2.99/0.99  --res_forward_subs                      full
% 2.99/0.99  --res_backward_subs                     full
% 2.99/0.99  --res_forward_subs_resolution           true
% 2.99/0.99  --res_backward_subs_resolution          true
% 2.99/0.99  --res_orphan_elimination                true
% 2.99/0.99  --res_time_limit                        2.
% 2.99/0.99  --res_out_proof                         true
% 2.99/0.99  
% 2.99/0.99  ------ Superposition Options
% 2.99/0.99  
% 2.99/0.99  --superposition_flag                    true
% 2.99/0.99  --sup_passive_queue_type                priority_queues
% 2.99/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.99/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.99/0.99  --demod_completeness_check              fast
% 2.99/0.99  --demod_use_ground                      true
% 2.99/0.99  --sup_to_prop_solver                    passive
% 2.99/0.99  --sup_prop_simpl_new                    true
% 2.99/0.99  --sup_prop_simpl_given                  true
% 2.99/0.99  --sup_fun_splitting                     false
% 2.99/0.99  --sup_smt_interval                      50000
% 2.99/0.99  
% 2.99/0.99  ------ Superposition Simplification Setup
% 2.99/0.99  
% 2.99/0.99  --sup_indices_passive                   []
% 2.99/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.99/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.99  --sup_full_bw                           [BwDemod]
% 2.99/0.99  --sup_immed_triv                        [TrivRules]
% 2.99/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.99/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.99  --sup_immed_bw_main                     []
% 2.99/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.99/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.99/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.99/0.99  
% 2.99/0.99  ------ Combination Options
% 2.99/0.99  
% 2.99/0.99  --comb_res_mult                         3
% 2.99/0.99  --comb_sup_mult                         2
% 2.99/0.99  --comb_inst_mult                        10
% 2.99/0.99  
% 2.99/0.99  ------ Debug Options
% 2.99/0.99  
% 2.99/0.99  --dbg_backtrace                         false
% 2.99/0.99  --dbg_dump_prop_clauses                 false
% 2.99/0.99  --dbg_dump_prop_clauses_file            -
% 2.99/0.99  --dbg_out_stat                          false
% 2.99/0.99  
% 2.99/0.99  
% 2.99/0.99  
% 2.99/0.99  
% 2.99/0.99  ------ Proving...
% 2.99/0.99  
% 2.99/0.99  
% 2.99/0.99  % SZS status Theorem for theBenchmark.p
% 2.99/0.99  
% 2.99/0.99   Resolution empty clause
% 2.99/0.99  
% 2.99/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.99/0.99  
% 2.99/0.99  fof(f19,axiom,(
% 2.99/0.99    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f23,plain,(
% 2.99/0.99    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.99/0.99    inference(pure_predicate_removal,[],[f19])).
% 2.99/0.99  
% 2.99/0.99  fof(f36,plain,(
% 2.99/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.99/0.99    inference(ennf_transformation,[],[f23])).
% 2.99/0.99  
% 2.99/0.99  fof(f44,plain,(
% 2.99/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 2.99/0.99    introduced(choice_axiom,[])).
% 2.99/0.99  
% 2.99/0.99  fof(f45,plain,(
% 2.99/0.99    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 2.99/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f44])).
% 2.99/0.99  
% 2.99/0.99  fof(f72,plain,(
% 2.99/0.99    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 2.99/0.99    inference(cnf_transformation,[],[f45])).
% 2.99/0.99  
% 2.99/0.99  fof(f21,conjecture,(
% 2.99/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f22,negated_conjecture,(
% 2.99/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 2.99/0.99    inference(negated_conjecture,[],[f21])).
% 2.99/0.99  
% 2.99/0.99  fof(f39,plain,(
% 2.99/0.99    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 2.99/0.99    inference(ennf_transformation,[],[f22])).
% 2.99/0.99  
% 2.99/0.99  fof(f40,plain,(
% 2.99/0.99    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 2.99/0.99    inference(flattening,[],[f39])).
% 2.99/0.99  
% 2.99/0.99  fof(f46,plain,(
% 2.99/0.99    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK4,sK2),sK3) & k1_xboole_0 != sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK4,k1_tarski(sK2),sK3) & v1_funct_1(sK4))),
% 2.99/0.99    introduced(choice_axiom,[])).
% 2.99/0.99  
% 2.99/0.99  fof(f47,plain,(
% 2.99/0.99    ~r2_hidden(k1_funct_1(sK4,sK2),sK3) & k1_xboole_0 != sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK4,k1_tarski(sK2),sK3) & v1_funct_1(sK4)),
% 2.99/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f40,f46])).
% 2.99/0.99  
% 2.99/0.99  fof(f76,plain,(
% 2.99/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))),
% 2.99/0.99    inference(cnf_transformation,[],[f47])).
% 2.99/0.99  
% 2.99/0.99  fof(f3,axiom,(
% 2.99/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f50,plain,(
% 2.99/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f3])).
% 2.99/0.99  
% 2.99/0.99  fof(f4,axiom,(
% 2.99/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f51,plain,(
% 2.99/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f4])).
% 2.99/0.99  
% 2.99/0.99  fof(f5,axiom,(
% 2.99/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f52,plain,(
% 2.99/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f5])).
% 2.99/0.99  
% 2.99/0.99  fof(f79,plain,(
% 2.99/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.99/0.99    inference(definition_unfolding,[],[f51,f52])).
% 2.99/0.99  
% 2.99/0.99  fof(f80,plain,(
% 2.99/0.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.99/0.99    inference(definition_unfolding,[],[f50,f79])).
% 2.99/0.99  
% 2.99/0.99  fof(f84,plain,(
% 2.99/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))),
% 2.99/0.99    inference(definition_unfolding,[],[f76,f80])).
% 2.99/0.99  
% 2.99/0.99  fof(f8,axiom,(
% 2.99/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f24,plain,(
% 2.99/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.99/0.99    inference(ennf_transformation,[],[f8])).
% 2.99/0.99  
% 2.99/0.99  fof(f55,plain,(
% 2.99/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.99/0.99    inference(cnf_transformation,[],[f24])).
% 2.99/0.99  
% 2.99/0.99  fof(f18,axiom,(
% 2.99/0.99    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f35,plain,(
% 2.99/0.99    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1) | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 2.99/0.99    inference(ennf_transformation,[],[f18])).
% 2.99/0.99  
% 2.99/0.99  fof(f70,plain,(
% 2.99/0.99    ( ! [X2,X0,X1] : (k1_mcart_1(X0) = X1 | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))) )),
% 2.99/0.99    inference(cnf_transformation,[],[f35])).
% 2.99/0.99  
% 2.99/0.99  fof(f83,plain,(
% 2.99/0.99    ( ! [X2,X0,X1] : (k1_mcart_1(X0) = X1 | ~r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2))) )),
% 2.99/0.99    inference(definition_unfolding,[],[f70,f80])).
% 2.99/0.99  
% 2.99/0.99  fof(f17,axiom,(
% 2.99/0.99    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f34,plain,(
% 2.99/0.99    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.99/0.99    inference(ennf_transformation,[],[f17])).
% 2.99/0.99  
% 2.99/0.99  fof(f68,plain,(
% 2.99/0.99    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 2.99/0.99    inference(cnf_transformation,[],[f34])).
% 2.99/0.99  
% 2.99/0.99  fof(f20,axiom,(
% 2.99/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f37,plain,(
% 2.99/0.99    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.99/0.99    inference(ennf_transformation,[],[f20])).
% 2.99/0.99  
% 2.99/0.99  fof(f38,plain,(
% 2.99/0.99    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.99/0.99    inference(flattening,[],[f37])).
% 2.99/0.99  
% 2.99/0.99  fof(f73,plain,(
% 2.99/0.99    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f38])).
% 2.99/0.99  
% 2.99/0.99  fof(f75,plain,(
% 2.99/0.99    v1_funct_2(sK4,k1_tarski(sK2),sK3)),
% 2.99/0.99    inference(cnf_transformation,[],[f47])).
% 2.99/0.99  
% 2.99/0.99  fof(f85,plain,(
% 2.99/0.99    v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3)),
% 2.99/0.99    inference(definition_unfolding,[],[f75,f80])).
% 2.99/0.99  
% 2.99/0.99  fof(f74,plain,(
% 2.99/0.99    v1_funct_1(sK4)),
% 2.99/0.99    inference(cnf_transformation,[],[f47])).
% 2.99/0.99  
% 2.99/0.99  fof(f77,plain,(
% 2.99/0.99    k1_xboole_0 != sK3),
% 2.99/0.99    inference(cnf_transformation,[],[f47])).
% 2.99/0.99  
% 2.99/0.99  fof(f78,plain,(
% 2.99/0.99    ~r2_hidden(k1_funct_1(sK4,sK2),sK3)),
% 2.99/0.99    inference(cnf_transformation,[],[f47])).
% 2.99/0.99  
% 2.99/0.99  fof(f7,axiom,(
% 2.99/0.99    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f41,plain,(
% 2.99/0.99    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK0(X0),X0))),
% 2.99/0.99    introduced(choice_axiom,[])).
% 2.99/0.99  
% 2.99/0.99  fof(f42,plain,(
% 2.99/0.99    ! [X0] : m1_subset_1(sK0(X0),X0)),
% 2.99/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f41])).
% 2.99/0.99  
% 2.99/0.99  fof(f54,plain,(
% 2.99/0.99    ( ! [X0] : (m1_subset_1(sK0(X0),X0)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f42])).
% 2.99/0.99  
% 2.99/0.99  fof(f10,axiom,(
% 2.99/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f25,plain,(
% 2.99/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.99/0.99    inference(ennf_transformation,[],[f10])).
% 2.99/0.99  
% 2.99/0.99  fof(f26,plain,(
% 2.99/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.99/0.99    inference(flattening,[],[f25])).
% 2.99/0.99  
% 2.99/0.99  fof(f57,plain,(
% 2.99/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f26])).
% 2.99/0.99  
% 2.99/0.99  fof(f6,axiom,(
% 2.99/0.99    ! [X0,X1] : ~v1_xboole_0(k2_tarski(X0,X1))),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f53,plain,(
% 2.99/0.99    ( ! [X0,X1] : (~v1_xboole_0(k2_tarski(X0,X1))) )),
% 2.99/0.99    inference(cnf_transformation,[],[f6])).
% 2.99/0.99  
% 2.99/0.99  fof(f81,plain,(
% 2.99/0.99    ( ! [X0,X1] : (~v1_xboole_0(k2_enumset1(X0,X0,X0,X1))) )),
% 2.99/0.99    inference(definition_unfolding,[],[f53,f79])).
% 2.99/0.99  
% 2.99/0.99  fof(f12,axiom,(
% 2.99/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f59,plain,(
% 2.99/0.99    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.99/0.99    inference(cnf_transformation,[],[f12])).
% 2.99/0.99  
% 2.99/0.99  fof(f14,axiom,(
% 2.99/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f30,plain,(
% 2.99/0.99    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.99/0.99    inference(ennf_transformation,[],[f14])).
% 2.99/0.99  
% 2.99/0.99  fof(f31,plain,(
% 2.99/0.99    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.99/0.99    inference(flattening,[],[f30])).
% 2.99/0.99  
% 2.99/0.99  fof(f43,plain,(
% 2.99/0.99    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.99/0.99    inference(nnf_transformation,[],[f31])).
% 2.99/0.99  
% 2.99/0.99  fof(f64,plain,(
% 2.99/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2 | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f43])).
% 2.99/0.99  
% 2.99/0.99  fof(f87,plain,(
% 2.99/0.99    ( ! [X0,X1] : (k1_xboole_0 = k1_funct_1(X0,X1) | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.99/0.99    inference(equality_resolution,[],[f64])).
% 2.99/0.99  
% 2.99/0.99  fof(f13,axiom,(
% 2.99/0.99    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f29,plain,(
% 2.99/0.99    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 2.99/0.99    inference(ennf_transformation,[],[f13])).
% 2.99/0.99  
% 2.99/0.99  fof(f61,plain,(
% 2.99/0.99    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f29])).
% 2.99/0.99  
% 2.99/0.99  fof(f1,axiom,(
% 2.99/0.99    v1_xboole_0(k1_xboole_0)),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f48,plain,(
% 2.99/0.99    v1_xboole_0(k1_xboole_0)),
% 2.99/0.99    inference(cnf_transformation,[],[f1])).
% 2.99/0.99  
% 2.99/0.99  fof(f2,axiom,(
% 2.99/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f49,plain,(
% 2.99/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f2])).
% 2.99/0.99  
% 2.99/0.99  fof(f15,axiom,(
% 2.99/0.99    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f32,plain,(
% 2.99/0.99    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.99/0.99    inference(ennf_transformation,[],[f15])).
% 2.99/0.99  
% 2.99/0.99  fof(f66,plain,(
% 2.99/0.99    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f32])).
% 2.99/0.99  
% 2.99/0.99  fof(f16,axiom,(
% 2.99/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f33,plain,(
% 2.99/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.99/0.99    inference(ennf_transformation,[],[f16])).
% 2.99/0.99  
% 2.99/0.99  fof(f67,plain,(
% 2.99/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.99/0.99    inference(cnf_transformation,[],[f33])).
% 2.99/0.99  
% 2.99/0.99  fof(f9,axiom,(
% 2.99/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f56,plain,(
% 2.99/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.99/0.99    inference(cnf_transformation,[],[f9])).
% 2.99/0.99  
% 2.99/0.99  cnf(c_21,plain,
% 2.99/0.99      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 2.99/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1341,plain,
% 2.99/0.99      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_25,negated_conjecture,
% 2.99/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) ),
% 2.99/0.99      inference(cnf_transformation,[],[f84]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1339,plain,
% 2.99/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_4,plain,
% 2.99/0.99      ( ~ r2_hidden(X0,X1)
% 2.99/0.99      | r2_hidden(X0,X2)
% 2.99/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 2.99/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1354,plain,
% 2.99/0.99      ( r2_hidden(X0,X1) != iProver_top
% 2.99/0.99      | r2_hidden(X0,X2) = iProver_top
% 2.99/0.99      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2266,plain,
% 2.99/0.99      ( r2_hidden(X0,k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) = iProver_top
% 2.99/0.99      | r2_hidden(X0,sK4) != iProver_top ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_1339,c_1354]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_20,plain,
% 2.99/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2))
% 2.99/0.99      | k1_mcart_1(X0) = X1 ),
% 2.99/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1342,plain,
% 2.99/0.99      ( k1_mcart_1(X0) = X1
% 2.99/0.99      | r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2)) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2317,plain,
% 2.99/0.99      ( k1_mcart_1(X0) = sK2 | r2_hidden(X0,sK4) != iProver_top ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_2266,c_1342]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2469,plain,
% 2.99/0.99      ( k1_mcart_1(sK1(sK4)) = sK2 | sK4 = k1_xboole_0 ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_1341,c_2317]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_18,plain,
% 2.99/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1) ),
% 2.99/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1344,plain,
% 2.99/0.99      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 2.99/0.99      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2316,plain,
% 2.99/0.99      ( r2_hidden(X0,sK4) != iProver_top
% 2.99/0.99      | r2_hidden(k1_mcart_1(X0),k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_2266,c_1344]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_22,plain,
% 2.99/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.99/0.99      | ~ r2_hidden(X3,X1)
% 2.99/0.99      | r2_hidden(k1_funct_1(X0,X3),X2)
% 2.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.99/0.99      | ~ v1_funct_1(X0)
% 2.99/0.99      | k1_xboole_0 = X2 ),
% 2.99/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_26,negated_conjecture,
% 2.99/0.99      ( v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
% 2.99/0.99      inference(cnf_transformation,[],[f85]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_295,plain,
% 2.99/0.99      ( ~ r2_hidden(X0,X1)
% 2.99/0.99      | r2_hidden(k1_funct_1(X2,X0),X3)
% 2.99/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.99/0.99      | ~ v1_funct_1(X2)
% 2.99/0.99      | k2_enumset1(sK2,sK2,sK2,sK2) != X1
% 2.99/0.99      | sK3 != X3
% 2.99/0.99      | sK4 != X2
% 2.99/0.99      | k1_xboole_0 = X3 ),
% 2.99/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_26]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_296,plain,
% 2.99/0.99      ( ~ r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2))
% 2.99/0.99      | r2_hidden(k1_funct_1(sK4,X0),sK3)
% 2.99/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))
% 2.99/0.99      | ~ v1_funct_1(sK4)
% 2.99/0.99      | k1_xboole_0 = sK3 ),
% 2.99/0.99      inference(unflattening,[status(thm)],[c_295]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_27,negated_conjecture,
% 2.99/0.99      ( v1_funct_1(sK4) ),
% 2.99/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_24,negated_conjecture,
% 2.99/0.99      ( k1_xboole_0 != sK3 ),
% 2.99/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_300,plain,
% 2.99/0.99      ( r2_hidden(k1_funct_1(sK4,X0),sK3)
% 2.99/0.99      | ~ r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 2.99/0.99      inference(global_propositional_subsumption,
% 2.99/0.99                [status(thm)],
% 2.99/0.99                [c_296,c_27,c_25,c_24]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_301,plain,
% 2.99/0.99      ( ~ r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2))
% 2.99/0.99      | r2_hidden(k1_funct_1(sK4,X0),sK3) ),
% 2.99/0.99      inference(renaming,[status(thm)],[c_300]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1336,plain,
% 2.99/0.99      ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
% 2.99/0.99      | r2_hidden(k1_funct_1(sK4,X0),sK3) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_301]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2615,plain,
% 2.99/0.99      ( r2_hidden(X0,sK4) != iProver_top
% 2.99/0.99      | r2_hidden(k1_funct_1(sK4,k1_mcart_1(X0)),sK3) = iProver_top ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_2316,c_1336]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2705,plain,
% 2.99/0.99      ( sK4 = k1_xboole_0
% 2.99/0.99      | r2_hidden(k1_funct_1(sK4,sK2),sK3) = iProver_top
% 2.99/0.99      | r2_hidden(sK1(sK4),sK4) != iProver_top ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_2469,c_2615]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_23,negated_conjecture,
% 2.99/0.99      ( ~ r2_hidden(k1_funct_1(sK4,sK2),sK3) ),
% 2.99/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_31,plain,
% 2.99/0.99      ( r2_hidden(k1_funct_1(sK4,sK2),sK3) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_3502,plain,
% 2.99/0.99      ( sK4 = k1_xboole_0 | r2_hidden(sK1(sK4),sK4) != iProver_top ),
% 2.99/0.99      inference(global_propositional_subsumption,[status(thm)],[c_2705,c_31]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_3508,plain,
% 2.99/0.99      ( sK4 = k1_xboole_0 ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_1341,c_3502]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_3,plain,
% 2.99/0.99      ( m1_subset_1(sK0(X0),X0) ),
% 2.99/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1355,plain,
% 2.99/0.99      ( m1_subset_1(sK0(X0),X0) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_6,plain,
% 2.99/0.99      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 2.99/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1352,plain,
% 2.99/0.99      ( r2_hidden(X0,X1) = iProver_top
% 2.99/0.99      | m1_subset_1(X0,X1) != iProver_top
% 2.99/0.99      | v1_xboole_0(X1) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2165,plain,
% 2.99/0.99      ( r2_hidden(sK0(X0),X0) = iProver_top | v1_xboole_0(X0) = iProver_top ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_1355,c_1352]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_3051,plain,
% 2.99/0.99      ( r2_hidden(k1_funct_1(sK4,sK0(k2_enumset1(sK2,sK2,sK2,sK2))),sK3) = iProver_top
% 2.99/0.99      | v1_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_2165,c_1336]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2,plain,
% 2.99/0.99      ( ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X1)) ),
% 2.99/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1356,plain,
% 2.99/0.99      ( v1_xboole_0(k2_enumset1(X0,X0,X0,X1)) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_3265,plain,
% 2.99/0.99      ( r2_hidden(k1_funct_1(sK4,sK0(k2_enumset1(sK2,sK2,sK2,sK2))),sK3) = iProver_top ),
% 2.99/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_3051,c_1356]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_3647,plain,
% 2.99/0.99      ( r2_hidden(k1_funct_1(k1_xboole_0,sK0(k2_enumset1(sK2,sK2,sK2,sK2))),sK3) = iProver_top ),
% 2.99/0.99      inference(demodulation,[status(thm)],[c_3508,c_3265]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_9,plain,
% 2.99/0.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.99/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_12,plain,
% 2.99/0.99      ( r2_hidden(X0,k1_relat_1(X1))
% 2.99/0.99      | ~ v1_relat_1(X1)
% 2.99/0.99      | ~ v1_funct_1(X1)
% 2.99/0.99      | k1_funct_1(X1,X0) = k1_xboole_0 ),
% 2.99/0.99      inference(cnf_transformation,[],[f87]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1349,plain,
% 2.99/0.99      ( k1_funct_1(X0,X1) = k1_xboole_0
% 2.99/0.99      | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
% 2.99/0.99      | v1_relat_1(X0) != iProver_top
% 2.99/0.99      | v1_funct_1(X0) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2900,plain,
% 2.99/0.99      ( k1_funct_1(k1_xboole_0,X0) = k1_xboole_0
% 2.99/0.99      | r2_hidden(X0,k1_xboole_0) = iProver_top
% 2.99/0.99      | v1_relat_1(k1_xboole_0) != iProver_top
% 2.99/0.99      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_9,c_1349]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_10,plain,
% 2.99/0.99      ( v1_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 2.99/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_66,plain,
% 2.99/0.99      ( v1_funct_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_68,plain,
% 2.99/0.99      ( v1_funct_1(k1_xboole_0) = iProver_top
% 2.99/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_66]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_0,plain,
% 2.99/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.99/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_88,plain,
% 2.99/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1,plain,
% 2.99/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 2.99/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_15,plain,
% 2.99/0.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 2.99/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_284,plain,
% 2.99/0.99      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 2.99/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_15]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_285,plain,
% 2.99/0.99      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.99/0.99      inference(unflattening,[status(thm)],[c_284]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_286,plain,
% 2.99/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_285]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_16,plain,
% 2.99/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.99/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1515,plain,
% 2.99/0.99      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.99/0.99      | v1_relat_1(k1_xboole_0) ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1517,plain,
% 2.99/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.99/0.99      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_1515]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_5,plain,
% 2.99/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.99/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1516,plain,
% 2.99/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1519,plain,
% 2.99/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_1516]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2941,plain,
% 2.99/0.99      ( k1_funct_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.99/0.99      inference(global_propositional_subsumption,
% 2.99/0.99                [status(thm)],
% 2.99/0.99                [c_2900,c_68,c_88,c_286,c_1517,c_1519]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_3697,plain,
% 2.99/0.99      ( r2_hidden(k1_xboole_0,sK3) = iProver_top ),
% 2.99/0.99      inference(demodulation,[status(thm)],[c_3647,c_2941]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1340,plain,
% 2.99/0.99      ( r2_hidden(k1_funct_1(sK4,sK2),sK3) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_3662,plain,
% 2.99/0.99      ( r2_hidden(k1_funct_1(k1_xboole_0,sK2),sK3) != iProver_top ),
% 2.99/0.99      inference(demodulation,[status(thm)],[c_3508,c_1340]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_3665,plain,
% 2.99/0.99      ( r2_hidden(k1_xboole_0,sK3) != iProver_top ),
% 2.99/0.99      inference(demodulation,[status(thm)],[c_3662,c_2941]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_3699,plain,
% 2.99/0.99      ( $false ),
% 2.99/0.99      inference(backward_subsumption_resolution,[status(thm)],[c_3697,c_3665]) ).
% 2.99/0.99  
% 2.99/0.99  
% 2.99/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.99/0.99  
% 2.99/0.99  ------                               Statistics
% 2.99/0.99  
% 2.99/0.99  ------ General
% 2.99/0.99  
% 2.99/0.99  abstr_ref_over_cycles:                  0
% 2.99/0.99  abstr_ref_under_cycles:                 0
% 2.99/0.99  gc_basic_clause_elim:                   0
% 2.99/0.99  forced_gc_time:                         0
% 2.99/0.99  parsing_time:                           0.009
% 2.99/0.99  unif_index_cands_time:                  0.
% 2.99/0.99  unif_index_add_time:                    0.
% 2.99/0.99  orderings_time:                         0.
% 2.99/0.99  out_proof_time:                         0.014
% 2.99/0.99  total_time:                             0.153
% 2.99/0.99  num_of_symbols:                         53
% 2.99/0.99  num_of_terms:                           3049
% 2.99/0.99  
% 2.99/0.99  ------ Preprocessing
% 2.99/0.99  
% 2.99/0.99  num_of_splits:                          0
% 2.99/0.99  num_of_split_atoms:                     0
% 2.99/0.99  num_of_reused_defs:                     0
% 2.99/0.99  num_eq_ax_congr_red:                    19
% 2.99/0.99  num_of_sem_filtered_clauses:            1
% 2.99/0.99  num_of_subtypes:                        0
% 2.99/0.99  monotx_restored_types:                  0
% 2.99/0.99  sat_num_of_epr_types:                   0
% 2.99/0.99  sat_num_of_non_cyclic_types:            0
% 2.99/0.99  sat_guarded_non_collapsed_types:        0
% 2.99/0.99  num_pure_diseq_elim:                    0
% 2.99/0.99  simp_replaced_by:                       0
% 2.99/0.99  res_preprocessed:                       129
% 2.99/0.99  prep_upred:                             0
% 2.99/0.99  prep_unflattend:                        29
% 2.99/0.99  smt_new_axioms:                         0
% 2.99/0.99  pred_elim_cands:                        5
% 2.99/0.99  pred_elim:                              2
% 2.99/0.99  pred_elim_cl:                           2
% 2.99/0.99  pred_elim_cycles:                       8
% 2.99/0.99  merged_defs:                            0
% 2.99/0.99  merged_defs_ncl:                        0
% 2.99/0.99  bin_hyper_res:                          0
% 2.99/0.99  prep_cycles:                            4
% 2.99/0.99  pred_elim_time:                         0.008
% 2.99/0.99  splitting_time:                         0.
% 2.99/0.99  sem_filter_time:                        0.
% 2.99/0.99  monotx_time:                            0.
% 2.99/0.99  subtype_inf_time:                       0.
% 2.99/0.99  
% 2.99/0.99  ------ Problem properties
% 2.99/0.99  
% 2.99/0.99  clauses:                                25
% 2.99/0.99  conjectures:                            4
% 2.99/0.99  epr:                                    6
% 2.99/0.99  horn:                                   22
% 2.99/0.99  ground:                                 7
% 2.99/0.99  unary:                                  11
% 2.99/0.99  binary:                                 8
% 2.99/0.99  lits:                                   49
% 2.99/0.99  lits_eq:                                7
% 2.99/0.99  fd_pure:                                0
% 2.99/0.99  fd_pseudo:                              0
% 2.99/0.99  fd_cond:                                1
% 2.99/0.99  fd_pseudo_cond:                         2
% 2.99/0.99  ac_symbols:                             0
% 2.99/0.99  
% 2.99/0.99  ------ Propositional Solver
% 2.99/0.99  
% 2.99/0.99  prop_solver_calls:                      28
% 2.99/0.99  prop_fast_solver_calls:                 765
% 2.99/0.99  smt_solver_calls:                       0
% 2.99/0.99  smt_fast_solver_calls:                  0
% 2.99/0.99  prop_num_of_clauses:                    1064
% 2.99/0.99  prop_preprocess_simplified:             4658
% 2.99/0.99  prop_fo_subsumed:                       9
% 2.99/0.99  prop_solver_time:                       0.
% 2.99/0.99  smt_solver_time:                        0.
% 2.99/0.99  smt_fast_solver_time:                   0.
% 2.99/0.99  prop_fast_solver_time:                  0.
% 2.99/0.99  prop_unsat_core_time:                   0.
% 2.99/0.99  
% 2.99/0.99  ------ QBF
% 2.99/0.99  
% 2.99/0.99  qbf_q_res:                              0
% 2.99/0.99  qbf_num_tautologies:                    0
% 2.99/0.99  qbf_prep_cycles:                        0
% 2.99/0.99  
% 2.99/0.99  ------ BMC1
% 2.99/0.99  
% 2.99/0.99  bmc1_current_bound:                     -1
% 2.99/0.99  bmc1_last_solved_bound:                 -1
% 2.99/0.99  bmc1_unsat_core_size:                   -1
% 2.99/0.99  bmc1_unsat_core_parents_size:           -1
% 2.99/0.99  bmc1_merge_next_fun:                    0
% 2.99/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.99/0.99  
% 2.99/0.99  ------ Instantiation
% 2.99/0.99  
% 2.99/0.99  inst_num_of_clauses:                    324
% 2.99/0.99  inst_num_in_passive:                    108
% 2.99/0.99  inst_num_in_active:                     210
% 2.99/0.99  inst_num_in_unprocessed:                6
% 2.99/0.99  inst_num_of_loops:                      240
% 2.99/0.99  inst_num_of_learning_restarts:          0
% 2.99/0.99  inst_num_moves_active_passive:          27
% 2.99/0.99  inst_lit_activity:                      0
% 2.99/0.99  inst_lit_activity_moves:                0
% 2.99/0.99  inst_num_tautologies:                   0
% 2.99/0.99  inst_num_prop_implied:                  0
% 2.99/0.99  inst_num_existing_simplified:           0
% 2.99/0.99  inst_num_eq_res_simplified:             0
% 2.99/0.99  inst_num_child_elim:                    0
% 2.99/0.99  inst_num_of_dismatching_blockings:      102
% 2.99/0.99  inst_num_of_non_proper_insts:           262
% 2.99/0.99  inst_num_of_duplicates:                 0
% 2.99/0.99  inst_inst_num_from_inst_to_res:         0
% 2.99/0.99  inst_dismatching_checking_time:         0.
% 2.99/0.99  
% 2.99/0.99  ------ Resolution
% 2.99/0.99  
% 2.99/0.99  res_num_of_clauses:                     0
% 2.99/0.99  res_num_in_passive:                     0
% 2.99/0.99  res_num_in_active:                      0
% 2.99/0.99  res_num_of_loops:                       133
% 2.99/0.99  res_forward_subset_subsumed:            23
% 2.99/0.99  res_backward_subset_subsumed:           0
% 2.99/0.99  res_forward_subsumed:                   0
% 2.99/0.99  res_backward_subsumed:                  0
% 2.99/0.99  res_forward_subsumption_resolution:     0
% 2.99/0.99  res_backward_subsumption_resolution:    0
% 2.99/0.99  res_clause_to_clause_subsumption:       142
% 2.99/0.99  res_orphan_elimination:                 0
% 2.99/0.99  res_tautology_del:                      54
% 2.99/0.99  res_num_eq_res_simplified:              0
% 2.99/0.99  res_num_sel_changes:                    0
% 2.99/0.99  res_moves_from_active_to_pass:          0
% 2.99/0.99  
% 2.99/0.99  ------ Superposition
% 2.99/0.99  
% 2.99/0.99  sup_time_total:                         0.
% 2.99/0.99  sup_time_generating:                    0.
% 2.99/0.99  sup_time_sim_full:                      0.
% 2.99/0.99  sup_time_sim_immed:                     0.
% 2.99/0.99  
% 2.99/0.99  sup_num_of_clauses:                     55
% 2.99/0.99  sup_num_in_active:                      26
% 2.99/0.99  sup_num_in_passive:                     29
% 2.99/0.99  sup_num_of_loops:                       47
% 2.99/0.99  sup_fw_superposition:                   31
% 2.99/0.99  sup_bw_superposition:                   31
% 2.99/0.99  sup_immediate_simplified:               7
% 2.99/0.99  sup_given_eliminated:                   0
% 2.99/0.99  comparisons_done:                       0
% 2.99/0.99  comparisons_avoided:                    3
% 2.99/0.99  
% 2.99/0.99  ------ Simplifications
% 2.99/0.99  
% 2.99/0.99  
% 2.99/0.99  sim_fw_subset_subsumed:                 10
% 2.99/0.99  sim_bw_subset_subsumed:                 3
% 2.99/0.99  sim_fw_subsumed:                        5
% 2.99/0.99  sim_bw_subsumed:                        3
% 2.99/0.99  sim_fw_subsumption_res:                 1
% 2.99/0.99  sim_bw_subsumption_res:                 1
% 2.99/0.99  sim_tautology_del:                      0
% 2.99/0.99  sim_eq_tautology_del:                   3
% 2.99/0.99  sim_eq_res_simp:                        0
% 2.99/0.99  sim_fw_demodulated:                     4
% 2.99/0.99  sim_bw_demodulated:                     20
% 2.99/0.99  sim_light_normalised:                   3
% 2.99/0.99  sim_joinable_taut:                      0
% 2.99/0.99  sim_joinable_simp:                      0
% 2.99/0.99  sim_ac_normalised:                      0
% 2.99/0.99  sim_smt_subsumption:                    0
% 2.99/0.99  
%------------------------------------------------------------------------------
