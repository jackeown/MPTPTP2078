%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:43 EST 2020

% Result     : Theorem 1.25s
% Output     : CNFRefutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :  185 ( 781 expanded)
%              Number of clauses        :   98 ( 225 expanded)
%              Number of leaves         :   27 ( 179 expanded)
%              Depth                    :   24
%              Number of atoms          :  481 (2245 expanded)
%              Number of equality atoms :  178 ( 745 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
     => r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f32,f49])).

fof(f69,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f43,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f44,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f52,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(k1_funct_1(sK5,sK3),sK4)
      & k1_xboole_0 != sK4
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4)))
      & v1_funct_2(sK5,k1_tarski(sK3),sK4)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ~ r2_hidden(k1_funct_1(sK5,sK3),sK4)
    & k1_xboole_0 != sK4
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4)))
    & v1_funct_2(sK5,k1_tarski(sK3),sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f44,f52])).

fof(f85,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) ),
    inference(cnf_transformation,[],[f53])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f88,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f89,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f56,f88])).

fof(f94,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) ),
    inference(definition_unfolding,[],[f85,f89])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <=> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
        | ~ r2_hidden(X1,X3)
        | X0 != X2 )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
        | ~ r2_hidden(X1,X3)
        | X0 != X2 )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(flattening,[],[f45])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3)) ) ),
    inference(definition_unfolding,[],[f60,f89])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f87,plain,(
    ~ r2_hidden(k1_funct_1(sK5,sK3),sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f83,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f53])).

fof(f8,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f47])).

fof(f63,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f48])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f41])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f84,plain,(
    v1_funct_2(sK5,k1_tarski(sK3),sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f95,plain,(
    v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(definition_unfolding,[],[f84,f89])).

fof(f86,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f53])).

fof(f6,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f90,plain,(
    ! [X0] : ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(definition_unfolding,[],[f59,f89])).

fof(f14,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f17,axiom,(
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

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_funct_1(X0,X1) != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_funct_1(X0,X1)
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f73,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f19,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f15,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f11,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_12,plain,
    ( r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
    | ~ v1_relat_1(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2192,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_464,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(X2)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_28])).

cnf(c_465,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,sK5)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(X1) ),
    inference(unflattening,[status(thm)],[c_464])).

cnf(c_2179,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(X0)
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_465])).

cnf(c_2420,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2179])).

cnf(c_5,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3))
    | X2 = X0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2196,plain,
    ( X0 = X1
    | r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3058,plain,
    ( sK3 = X0
    | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2420,c_2196])).

cnf(c_3276,plain,
    ( sK1(sK5) = sK3
    | sK5 = k1_xboole_0
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2192,c_3058])).

cnf(c_1726,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2376,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_1726])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_510,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_28])).

cnf(c_511,plain,
    ( v1_relat_1(sK5)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_510])).

cnf(c_2377,plain,
    ( v1_relat_1(sK5)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_511])).

cnf(c_3277,plain,
    ( ~ v1_relat_1(sK5)
    | sK1(sK5) = sK3
    | sK5 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3276])).

cnf(c_3350,plain,
    ( sK5 = k1_xboole_0
    | sK1(sK5) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3276,c_2376,c_2377,c_3277])).

cnf(c_3351,plain,
    ( sK1(sK5) = sK3
    | sK5 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3350])).

cnf(c_3354,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(k4_tarski(sK3,sK2(sK5)),sK5) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3351,c_2192])).

cnf(c_2378,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2377])).

cnf(c_3411,plain,
    ( r2_hidden(k4_tarski(sK3,sK2(sK5)),sK5) = iProver_top
    | sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3354,c_2376,c_2378])).

cnf(c_3412,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(k4_tarski(sK3,sK2(sK5)),sK5) = iProver_top ),
    inference(renaming,[status(thm)],[c_3411])).

cnf(c_11,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2193,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3533,plain,
    ( r2_hidden(X0,k1_relat_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top
    | v1_relat_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2420,c_2193])).

cnf(c_3959,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK3,k1_relat_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top
    | v1_relat_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3412,c_3533])).

cnf(c_26,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(sK5,sK3),sK4) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_34,plain,
    ( r2_hidden(k1_funct_1(sK5,sK3),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_24,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_21,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X2),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_325,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_24,c_21])).

cnf(c_329,plain,
    ( ~ v1_funct_1(X0)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_325,c_23])).

cnf(c_330,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_329])).

cnf(c_489,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X3,X2))
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_330,c_28])).

cnf(c_490,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | r2_hidden(k1_funct_1(sK5,X0),X1)
    | ~ v1_funct_1(sK5)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X2,X1)) ),
    inference(unflattening,[status(thm)],[c_489])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_494,plain,
    ( r2_hidden(k1_funct_1(sK5,X0),X1)
    | ~ r2_hidden(X0,k1_relat_1(sK5))
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X2,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_490,c_30])).

cnf(c_495,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | r2_hidden(k1_funct_1(sK5,X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X2,X1)) ),
    inference(renaming,[status(thm)],[c_494])).

cnf(c_2592,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | r2_hidden(k1_funct_1(sK5,X0),sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_495])).

cnf(c_2622,plain,
    ( r2_hidden(k1_funct_1(sK5,sK3),sK4)
    | ~ r2_hidden(sK3,k1_relat_1(sK5))
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_2592])).

cnf(c_2623,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
    | r2_hidden(k1_funct_1(sK5,sK3),sK4) = iProver_top
    | r2_hidden(sK3,k1_relat_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2622])).

cnf(c_3534,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK3,k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3412,c_2193])).

cnf(c_4107,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3959,c_34,c_2376,c_2378,c_2623,c_3534])).

cnf(c_6,plain,
    ( m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_430,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | X1 != X2
    | sK0(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_8])).

cnf(c_431,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_430])).

cnf(c_2182,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_431])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_353,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k2_enumset1(sK3,sK3,sK3,sK3) != X1
    | sK4 != X2
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_29])).

cnf(c_354,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
    | ~ r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3))
    | r2_hidden(k1_funct_1(sK5,X0),sK4)
    | ~ v1_funct_1(sK5)
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_353])).

cnf(c_27,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_358,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3))
    | r2_hidden(k1_funct_1(sK5,X0),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_354,c_30,c_28,c_27])).

cnf(c_2184,plain,
    ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_358])).

cnf(c_3521,plain,
    ( r2_hidden(k1_funct_1(sK5,sK0(k2_enumset1(sK3,sK3,sK3,sK3))),sK4) = iProver_top
    | v1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2182,c_2184])).

cnf(c_2380,plain,
    ( r2_hidden(sK0(k2_enumset1(X0,X0,X0,X0)),k2_enumset1(X0,X0,X0,X0))
    | v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(instantiation,[status(thm)],[c_431])).

cnf(c_2936,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
    | v1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_2380])).

cnf(c_2938,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top
    | v1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2936])).

cnf(c_2937,plain,
    ( r2_hidden(k1_funct_1(sK5,sK0(k2_enumset1(sK3,sK3,sK3,sK3))),sK4)
    | ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_358])).

cnf(c_2940,plain,
    ( r2_hidden(k1_funct_1(sK5,sK0(k2_enumset1(sK3,sK3,sK3,sK3))),sK4) = iProver_top
    | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2937])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2961,plain,
    ( ~ v1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2962,plain,
    ( v1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2961])).

cnf(c_3817,plain,
    ( r2_hidden(k1_funct_1(sK5,sK0(k2_enumset1(sK3,sK3,sK3,sK3))),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3521,c_2938,c_2940,c_2962])).

cnf(c_4112,plain,
    ( r2_hidden(k1_funct_1(k1_xboole_0,sK0(k2_enumset1(sK3,sK3,sK3,sK3))),sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4107,c_3817])).

cnf(c_14,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_18,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2190,plain,
    ( k1_funct_1(X0,X1) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3637,plain,
    ( k1_funct_1(k1_xboole_0,X0) = k1_xboole_0
    | r2_hidden(X0,k1_xboole_0) = iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_2190])).

cnf(c_16,plain,
    ( v1_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_60,plain,
    ( v1_funct_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_62,plain,
    ( v1_funct_1(k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_60])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_97,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_314,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_22])).

cnf(c_315,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_314])).

cnf(c_316,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_315])).

cnf(c_15,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_9,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2195,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2777,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_2195])).

cnf(c_3727,plain,
    ( k1_funct_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3637,c_62,c_97,c_316,c_2777])).

cnf(c_4170,plain,
    ( r2_hidden(k1_xboole_0,sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4112,c_3727])).

cnf(c_2177,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | r2_hidden(X2,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_495])).

cnf(c_2466,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),sK4) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2177])).

cnf(c_2188,plain,
    ( r2_hidden(k1_funct_1(sK5,sK3),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2634,plain,
    ( r2_hidden(sK3,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2466,c_2188])).

cnf(c_3640,plain,
    ( k1_funct_1(sK5,sK3) = k1_xboole_0
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2190,c_2634])).

cnf(c_31,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3732,plain,
    ( k1_funct_1(sK5,sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3640,c_31,c_2376,c_2378])).

cnf(c_3735,plain,
    ( r2_hidden(k1_xboole_0,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3732,c_2188])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4170,c_3735])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:56:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 1.25/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.25/1.02  
% 1.25/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.25/1.02  
% 1.25/1.02  ------  iProver source info
% 1.25/1.02  
% 1.25/1.02  git: date: 2020-06-30 10:37:57 +0100
% 1.25/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.25/1.02  git: non_committed_changes: false
% 1.25/1.02  git: last_make_outside_of_git: false
% 1.25/1.02  
% 1.25/1.02  ------ 
% 1.25/1.02  
% 1.25/1.02  ------ Input Options
% 1.25/1.02  
% 1.25/1.02  --out_options                           all
% 1.25/1.02  --tptp_safe_out                         true
% 1.25/1.02  --problem_path                          ""
% 1.25/1.02  --include_path                          ""
% 1.25/1.02  --clausifier                            res/vclausify_rel
% 1.25/1.02  --clausifier_options                    --mode clausify
% 1.25/1.02  --stdin                                 false
% 1.25/1.02  --stats_out                             all
% 1.25/1.02  
% 1.25/1.02  ------ General Options
% 1.25/1.02  
% 1.25/1.02  --fof                                   false
% 1.25/1.02  --time_out_real                         305.
% 1.25/1.02  --time_out_virtual                      -1.
% 1.25/1.02  --symbol_type_check                     false
% 1.25/1.02  --clausify_out                          false
% 1.25/1.02  --sig_cnt_out                           false
% 1.25/1.02  --trig_cnt_out                          false
% 1.25/1.02  --trig_cnt_out_tolerance                1.
% 1.25/1.02  --trig_cnt_out_sk_spl                   false
% 1.25/1.02  --abstr_cl_out                          false
% 1.25/1.02  
% 1.25/1.02  ------ Global Options
% 1.25/1.02  
% 1.25/1.02  --schedule                              default
% 1.25/1.02  --add_important_lit                     false
% 1.25/1.02  --prop_solver_per_cl                    1000
% 1.25/1.02  --min_unsat_core                        false
% 1.25/1.02  --soft_assumptions                      false
% 1.25/1.02  --soft_lemma_size                       3
% 1.25/1.02  --prop_impl_unit_size                   0
% 1.25/1.02  --prop_impl_unit                        []
% 1.25/1.02  --share_sel_clauses                     true
% 1.25/1.02  --reset_solvers                         false
% 1.25/1.02  --bc_imp_inh                            [conj_cone]
% 1.25/1.02  --conj_cone_tolerance                   3.
% 1.25/1.02  --extra_neg_conj                        none
% 1.25/1.02  --large_theory_mode                     true
% 1.25/1.02  --prolific_symb_bound                   200
% 1.25/1.02  --lt_threshold                          2000
% 1.25/1.02  --clause_weak_htbl                      true
% 1.25/1.02  --gc_record_bc_elim                     false
% 1.25/1.02  
% 1.25/1.02  ------ Preprocessing Options
% 1.25/1.02  
% 1.25/1.02  --preprocessing_flag                    true
% 1.25/1.02  --time_out_prep_mult                    0.1
% 1.25/1.02  --splitting_mode                        input
% 1.25/1.02  --splitting_grd                         true
% 1.25/1.02  --splitting_cvd                         false
% 1.25/1.02  --splitting_cvd_svl                     false
% 1.25/1.02  --splitting_nvd                         32
% 1.25/1.02  --sub_typing                            true
% 1.25/1.02  --prep_gs_sim                           true
% 1.25/1.02  --prep_unflatten                        true
% 1.25/1.02  --prep_res_sim                          true
% 1.25/1.02  --prep_upred                            true
% 1.25/1.02  --prep_sem_filter                       exhaustive
% 1.25/1.02  --prep_sem_filter_out                   false
% 1.25/1.02  --pred_elim                             true
% 1.25/1.02  --res_sim_input                         true
% 1.25/1.02  --eq_ax_congr_red                       true
% 1.25/1.02  --pure_diseq_elim                       true
% 1.25/1.02  --brand_transform                       false
% 1.25/1.02  --non_eq_to_eq                          false
% 1.25/1.02  --prep_def_merge                        true
% 1.25/1.02  --prep_def_merge_prop_impl              false
% 1.25/1.02  --prep_def_merge_mbd                    true
% 1.25/1.02  --prep_def_merge_tr_red                 false
% 1.25/1.02  --prep_def_merge_tr_cl                  false
% 1.25/1.02  --smt_preprocessing                     true
% 1.25/1.02  --smt_ac_axioms                         fast
% 1.25/1.02  --preprocessed_out                      false
% 1.25/1.02  --preprocessed_stats                    false
% 1.25/1.02  
% 1.25/1.02  ------ Abstraction refinement Options
% 1.25/1.02  
% 1.25/1.02  --abstr_ref                             []
% 1.25/1.02  --abstr_ref_prep                        false
% 1.25/1.02  --abstr_ref_until_sat                   false
% 1.25/1.02  --abstr_ref_sig_restrict                funpre
% 1.25/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.25/1.02  --abstr_ref_under                       []
% 1.25/1.02  
% 1.25/1.02  ------ SAT Options
% 1.25/1.02  
% 1.25/1.02  --sat_mode                              false
% 1.25/1.02  --sat_fm_restart_options                ""
% 1.25/1.02  --sat_gr_def                            false
% 1.25/1.02  --sat_epr_types                         true
% 1.25/1.02  --sat_non_cyclic_types                  false
% 1.25/1.02  --sat_finite_models                     false
% 1.25/1.02  --sat_fm_lemmas                         false
% 1.25/1.02  --sat_fm_prep                           false
% 1.25/1.02  --sat_fm_uc_incr                        true
% 1.25/1.02  --sat_out_model                         small
% 1.25/1.02  --sat_out_clauses                       false
% 1.25/1.02  
% 1.25/1.02  ------ QBF Options
% 1.25/1.02  
% 1.25/1.02  --qbf_mode                              false
% 1.25/1.02  --qbf_elim_univ                         false
% 1.25/1.02  --qbf_dom_inst                          none
% 1.25/1.02  --qbf_dom_pre_inst                      false
% 1.25/1.02  --qbf_sk_in                             false
% 1.25/1.02  --qbf_pred_elim                         true
% 1.25/1.02  --qbf_split                             512
% 1.25/1.02  
% 1.25/1.02  ------ BMC1 Options
% 1.25/1.02  
% 1.25/1.02  --bmc1_incremental                      false
% 1.25/1.02  --bmc1_axioms                           reachable_all
% 1.25/1.02  --bmc1_min_bound                        0
% 1.25/1.02  --bmc1_max_bound                        -1
% 1.25/1.02  --bmc1_max_bound_default                -1
% 1.25/1.02  --bmc1_symbol_reachability              true
% 1.25/1.02  --bmc1_property_lemmas                  false
% 1.25/1.02  --bmc1_k_induction                      false
% 1.25/1.02  --bmc1_non_equiv_states                 false
% 1.25/1.02  --bmc1_deadlock                         false
% 1.25/1.02  --bmc1_ucm                              false
% 1.25/1.02  --bmc1_add_unsat_core                   none
% 1.25/1.02  --bmc1_unsat_core_children              false
% 1.25/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.25/1.02  --bmc1_out_stat                         full
% 1.25/1.02  --bmc1_ground_init                      false
% 1.25/1.02  --bmc1_pre_inst_next_state              false
% 1.25/1.02  --bmc1_pre_inst_state                   false
% 1.25/1.02  --bmc1_pre_inst_reach_state             false
% 1.25/1.02  --bmc1_out_unsat_core                   false
% 1.25/1.02  --bmc1_aig_witness_out                  false
% 1.25/1.02  --bmc1_verbose                          false
% 1.25/1.02  --bmc1_dump_clauses_tptp                false
% 1.25/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.25/1.02  --bmc1_dump_file                        -
% 1.25/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.25/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.25/1.02  --bmc1_ucm_extend_mode                  1
% 1.25/1.02  --bmc1_ucm_init_mode                    2
% 1.25/1.02  --bmc1_ucm_cone_mode                    none
% 1.25/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.25/1.02  --bmc1_ucm_relax_model                  4
% 1.25/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.25/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.25/1.02  --bmc1_ucm_layered_model                none
% 1.25/1.02  --bmc1_ucm_max_lemma_size               10
% 1.25/1.02  
% 1.25/1.02  ------ AIG Options
% 1.25/1.02  
% 1.25/1.02  --aig_mode                              false
% 1.25/1.02  
% 1.25/1.02  ------ Instantiation Options
% 1.25/1.02  
% 1.25/1.02  --instantiation_flag                    true
% 1.25/1.02  --inst_sos_flag                         false
% 1.25/1.02  --inst_sos_phase                        true
% 1.25/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.25/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.25/1.02  --inst_lit_sel_side                     num_symb
% 1.25/1.02  --inst_solver_per_active                1400
% 1.25/1.02  --inst_solver_calls_frac                1.
% 1.25/1.02  --inst_passive_queue_type               priority_queues
% 1.25/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.25/1.02  --inst_passive_queues_freq              [25;2]
% 1.25/1.02  --inst_dismatching                      true
% 1.25/1.02  --inst_eager_unprocessed_to_passive     true
% 1.25/1.02  --inst_prop_sim_given                   true
% 1.25/1.02  --inst_prop_sim_new                     false
% 1.25/1.02  --inst_subs_new                         false
% 1.25/1.02  --inst_eq_res_simp                      false
% 1.25/1.02  --inst_subs_given                       false
% 1.25/1.02  --inst_orphan_elimination               true
% 1.25/1.02  --inst_learning_loop_flag               true
% 1.25/1.02  --inst_learning_start                   3000
% 1.25/1.02  --inst_learning_factor                  2
% 1.25/1.02  --inst_start_prop_sim_after_learn       3
% 1.25/1.02  --inst_sel_renew                        solver
% 1.25/1.02  --inst_lit_activity_flag                true
% 1.25/1.02  --inst_restr_to_given                   false
% 1.25/1.02  --inst_activity_threshold               500
% 1.25/1.02  --inst_out_proof                        true
% 1.25/1.02  
% 1.25/1.02  ------ Resolution Options
% 1.25/1.02  
% 1.25/1.02  --resolution_flag                       true
% 1.25/1.02  --res_lit_sel                           adaptive
% 1.25/1.02  --res_lit_sel_side                      none
% 1.25/1.02  --res_ordering                          kbo
% 1.25/1.02  --res_to_prop_solver                    active
% 1.25/1.02  --res_prop_simpl_new                    false
% 1.25/1.02  --res_prop_simpl_given                  true
% 1.25/1.02  --res_passive_queue_type                priority_queues
% 1.25/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.25/1.02  --res_passive_queues_freq               [15;5]
% 1.25/1.02  --res_forward_subs                      full
% 1.25/1.02  --res_backward_subs                     full
% 1.25/1.02  --res_forward_subs_resolution           true
% 1.25/1.02  --res_backward_subs_resolution          true
% 1.25/1.02  --res_orphan_elimination                true
% 1.25/1.02  --res_time_limit                        2.
% 1.25/1.02  --res_out_proof                         true
% 1.25/1.02  
% 1.25/1.02  ------ Superposition Options
% 1.25/1.02  
% 1.25/1.02  --superposition_flag                    true
% 1.25/1.02  --sup_passive_queue_type                priority_queues
% 1.25/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.25/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.25/1.02  --demod_completeness_check              fast
% 1.25/1.02  --demod_use_ground                      true
% 1.25/1.02  --sup_to_prop_solver                    passive
% 1.25/1.02  --sup_prop_simpl_new                    true
% 1.25/1.02  --sup_prop_simpl_given                  true
% 1.25/1.02  --sup_fun_splitting                     false
% 1.25/1.02  --sup_smt_interval                      50000
% 1.25/1.02  
% 1.25/1.02  ------ Superposition Simplification Setup
% 1.25/1.02  
% 1.25/1.02  --sup_indices_passive                   []
% 1.25/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.25/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.25/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.25/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.25/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.25/1.02  --sup_full_bw                           [BwDemod]
% 1.25/1.02  --sup_immed_triv                        [TrivRules]
% 1.25/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.25/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.25/1.02  --sup_immed_bw_main                     []
% 1.25/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.25/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.25/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.25/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.25/1.03  
% 1.25/1.03  ------ Combination Options
% 1.25/1.03  
% 1.25/1.03  --comb_res_mult                         3
% 1.25/1.03  --comb_sup_mult                         2
% 1.25/1.03  --comb_inst_mult                        10
% 1.25/1.03  
% 1.25/1.03  ------ Debug Options
% 1.25/1.03  
% 1.25/1.03  --dbg_backtrace                         false
% 1.25/1.03  --dbg_dump_prop_clauses                 false
% 1.25/1.03  --dbg_dump_prop_clauses_file            -
% 1.25/1.03  --dbg_out_stat                          false
% 1.25/1.03  ------ Parsing...
% 1.25/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.25/1.03  
% 1.25/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.25/1.03  
% 1.25/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.25/1.03  
% 1.25/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.25/1.03  ------ Proving...
% 1.25/1.03  ------ Problem Properties 
% 1.25/1.03  
% 1.25/1.03  
% 1.25/1.03  clauses                                 29
% 1.25/1.03  conjectures                             3
% 1.25/1.03  EPR                                     5
% 1.25/1.03  Horn                                    25
% 1.25/1.03  unary                                   11
% 1.25/1.03  binary                                  9
% 1.25/1.03  lits                                    59
% 1.25/1.03  lits eq                                 11
% 1.25/1.03  fd_pure                                 0
% 1.25/1.03  fd_pseudo                               0
% 1.25/1.03  fd_cond                                 1
% 1.25/1.03  fd_pseudo_cond                          2
% 1.25/1.03  AC symbols                              0
% 1.25/1.03  
% 1.25/1.03  ------ Schedule dynamic 5 is on 
% 1.25/1.03  
% 1.25/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.25/1.03  
% 1.25/1.03  
% 1.25/1.03  ------ 
% 1.25/1.03  Current options:
% 1.25/1.03  ------ 
% 1.25/1.03  
% 1.25/1.03  ------ Input Options
% 1.25/1.03  
% 1.25/1.03  --out_options                           all
% 1.25/1.03  --tptp_safe_out                         true
% 1.25/1.03  --problem_path                          ""
% 1.25/1.03  --include_path                          ""
% 1.25/1.03  --clausifier                            res/vclausify_rel
% 1.25/1.03  --clausifier_options                    --mode clausify
% 1.25/1.03  --stdin                                 false
% 1.25/1.03  --stats_out                             all
% 1.25/1.03  
% 1.25/1.03  ------ General Options
% 1.25/1.03  
% 1.25/1.03  --fof                                   false
% 1.25/1.03  --time_out_real                         305.
% 1.25/1.03  --time_out_virtual                      -1.
% 1.25/1.03  --symbol_type_check                     false
% 1.25/1.03  --clausify_out                          false
% 1.25/1.03  --sig_cnt_out                           false
% 1.25/1.03  --trig_cnt_out                          false
% 1.25/1.03  --trig_cnt_out_tolerance                1.
% 1.25/1.03  --trig_cnt_out_sk_spl                   false
% 1.25/1.03  --abstr_cl_out                          false
% 1.25/1.03  
% 1.25/1.03  ------ Global Options
% 1.25/1.03  
% 1.25/1.03  --schedule                              default
% 1.25/1.03  --add_important_lit                     false
% 1.25/1.03  --prop_solver_per_cl                    1000
% 1.25/1.03  --min_unsat_core                        false
% 1.25/1.03  --soft_assumptions                      false
% 1.25/1.03  --soft_lemma_size                       3
% 1.25/1.03  --prop_impl_unit_size                   0
% 1.25/1.03  --prop_impl_unit                        []
% 1.25/1.03  --share_sel_clauses                     true
% 1.25/1.03  --reset_solvers                         false
% 1.25/1.03  --bc_imp_inh                            [conj_cone]
% 1.25/1.03  --conj_cone_tolerance                   3.
% 1.25/1.03  --extra_neg_conj                        none
% 1.25/1.03  --large_theory_mode                     true
% 1.25/1.03  --prolific_symb_bound                   200
% 1.25/1.03  --lt_threshold                          2000
% 1.25/1.03  --clause_weak_htbl                      true
% 1.25/1.03  --gc_record_bc_elim                     false
% 1.25/1.03  
% 1.25/1.03  ------ Preprocessing Options
% 1.25/1.03  
% 1.25/1.03  --preprocessing_flag                    true
% 1.25/1.03  --time_out_prep_mult                    0.1
% 1.25/1.03  --splitting_mode                        input
% 1.25/1.03  --splitting_grd                         true
% 1.25/1.03  --splitting_cvd                         false
% 1.25/1.03  --splitting_cvd_svl                     false
% 1.25/1.03  --splitting_nvd                         32
% 1.25/1.03  --sub_typing                            true
% 1.25/1.03  --prep_gs_sim                           true
% 1.25/1.03  --prep_unflatten                        true
% 1.25/1.03  --prep_res_sim                          true
% 1.25/1.03  --prep_upred                            true
% 1.25/1.03  --prep_sem_filter                       exhaustive
% 1.25/1.03  --prep_sem_filter_out                   false
% 1.25/1.03  --pred_elim                             true
% 1.25/1.03  --res_sim_input                         true
% 1.25/1.03  --eq_ax_congr_red                       true
% 1.25/1.03  --pure_diseq_elim                       true
% 1.25/1.03  --brand_transform                       false
% 1.25/1.03  --non_eq_to_eq                          false
% 1.25/1.03  --prep_def_merge                        true
% 1.25/1.03  --prep_def_merge_prop_impl              false
% 1.25/1.03  --prep_def_merge_mbd                    true
% 1.25/1.03  --prep_def_merge_tr_red                 false
% 1.25/1.03  --prep_def_merge_tr_cl                  false
% 1.25/1.03  --smt_preprocessing                     true
% 1.25/1.03  --smt_ac_axioms                         fast
% 1.25/1.03  --preprocessed_out                      false
% 1.25/1.03  --preprocessed_stats                    false
% 1.25/1.03  
% 1.25/1.03  ------ Abstraction refinement Options
% 1.25/1.03  
% 1.25/1.03  --abstr_ref                             []
% 1.25/1.03  --abstr_ref_prep                        false
% 1.25/1.03  --abstr_ref_until_sat                   false
% 1.25/1.03  --abstr_ref_sig_restrict                funpre
% 1.25/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.25/1.03  --abstr_ref_under                       []
% 1.25/1.03  
% 1.25/1.03  ------ SAT Options
% 1.25/1.03  
% 1.25/1.03  --sat_mode                              false
% 1.25/1.03  --sat_fm_restart_options                ""
% 1.25/1.03  --sat_gr_def                            false
% 1.25/1.03  --sat_epr_types                         true
% 1.25/1.03  --sat_non_cyclic_types                  false
% 1.25/1.03  --sat_finite_models                     false
% 1.25/1.03  --sat_fm_lemmas                         false
% 1.25/1.03  --sat_fm_prep                           false
% 1.25/1.03  --sat_fm_uc_incr                        true
% 1.25/1.03  --sat_out_model                         small
% 1.25/1.03  --sat_out_clauses                       false
% 1.25/1.03  
% 1.25/1.03  ------ QBF Options
% 1.25/1.03  
% 1.25/1.03  --qbf_mode                              false
% 1.25/1.03  --qbf_elim_univ                         false
% 1.25/1.03  --qbf_dom_inst                          none
% 1.25/1.03  --qbf_dom_pre_inst                      false
% 1.25/1.03  --qbf_sk_in                             false
% 1.25/1.03  --qbf_pred_elim                         true
% 1.25/1.03  --qbf_split                             512
% 1.25/1.03  
% 1.25/1.03  ------ BMC1 Options
% 1.25/1.03  
% 1.25/1.03  --bmc1_incremental                      false
% 1.25/1.03  --bmc1_axioms                           reachable_all
% 1.25/1.03  --bmc1_min_bound                        0
% 1.25/1.03  --bmc1_max_bound                        -1
% 1.25/1.03  --bmc1_max_bound_default                -1
% 1.25/1.03  --bmc1_symbol_reachability              true
% 1.25/1.03  --bmc1_property_lemmas                  false
% 1.25/1.03  --bmc1_k_induction                      false
% 1.25/1.03  --bmc1_non_equiv_states                 false
% 1.25/1.03  --bmc1_deadlock                         false
% 1.25/1.03  --bmc1_ucm                              false
% 1.25/1.03  --bmc1_add_unsat_core                   none
% 1.25/1.03  --bmc1_unsat_core_children              false
% 1.25/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.25/1.03  --bmc1_out_stat                         full
% 1.25/1.03  --bmc1_ground_init                      false
% 1.25/1.03  --bmc1_pre_inst_next_state              false
% 1.25/1.03  --bmc1_pre_inst_state                   false
% 1.25/1.03  --bmc1_pre_inst_reach_state             false
% 1.25/1.03  --bmc1_out_unsat_core                   false
% 1.25/1.03  --bmc1_aig_witness_out                  false
% 1.25/1.03  --bmc1_verbose                          false
% 1.25/1.03  --bmc1_dump_clauses_tptp                false
% 1.25/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.25/1.03  --bmc1_dump_file                        -
% 1.25/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.25/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.25/1.03  --bmc1_ucm_extend_mode                  1
% 1.25/1.03  --bmc1_ucm_init_mode                    2
% 1.25/1.03  --bmc1_ucm_cone_mode                    none
% 1.25/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.25/1.03  --bmc1_ucm_relax_model                  4
% 1.25/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.25/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.25/1.03  --bmc1_ucm_layered_model                none
% 1.25/1.03  --bmc1_ucm_max_lemma_size               10
% 1.25/1.03  
% 1.25/1.03  ------ AIG Options
% 1.25/1.03  
% 1.25/1.03  --aig_mode                              false
% 1.25/1.03  
% 1.25/1.03  ------ Instantiation Options
% 1.25/1.03  
% 1.25/1.03  --instantiation_flag                    true
% 1.25/1.03  --inst_sos_flag                         false
% 1.25/1.03  --inst_sos_phase                        true
% 1.25/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.25/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.25/1.03  --inst_lit_sel_side                     none
% 1.25/1.03  --inst_solver_per_active                1400
% 1.25/1.03  --inst_solver_calls_frac                1.
% 1.25/1.03  --inst_passive_queue_type               priority_queues
% 1.25/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.25/1.03  --inst_passive_queues_freq              [25;2]
% 1.25/1.03  --inst_dismatching                      true
% 1.25/1.03  --inst_eager_unprocessed_to_passive     true
% 1.25/1.03  --inst_prop_sim_given                   true
% 1.25/1.03  --inst_prop_sim_new                     false
% 1.25/1.03  --inst_subs_new                         false
% 1.25/1.03  --inst_eq_res_simp                      false
% 1.25/1.03  --inst_subs_given                       false
% 1.25/1.03  --inst_orphan_elimination               true
% 1.25/1.03  --inst_learning_loop_flag               true
% 1.25/1.03  --inst_learning_start                   3000
% 1.25/1.03  --inst_learning_factor                  2
% 1.25/1.03  --inst_start_prop_sim_after_learn       3
% 1.25/1.03  --inst_sel_renew                        solver
% 1.25/1.03  --inst_lit_activity_flag                true
% 1.25/1.03  --inst_restr_to_given                   false
% 1.25/1.03  --inst_activity_threshold               500
% 1.25/1.03  --inst_out_proof                        true
% 1.25/1.03  
% 1.25/1.03  ------ Resolution Options
% 1.25/1.03  
% 1.25/1.03  --resolution_flag                       false
% 1.25/1.03  --res_lit_sel                           adaptive
% 1.25/1.03  --res_lit_sel_side                      none
% 1.25/1.03  --res_ordering                          kbo
% 1.25/1.03  --res_to_prop_solver                    active
% 1.25/1.03  --res_prop_simpl_new                    false
% 1.25/1.03  --res_prop_simpl_given                  true
% 1.25/1.03  --res_passive_queue_type                priority_queues
% 1.25/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.25/1.03  --res_passive_queues_freq               [15;5]
% 1.25/1.03  --res_forward_subs                      full
% 1.25/1.03  --res_backward_subs                     full
% 1.25/1.03  --res_forward_subs_resolution           true
% 1.25/1.03  --res_backward_subs_resolution          true
% 1.25/1.03  --res_orphan_elimination                true
% 1.25/1.03  --res_time_limit                        2.
% 1.25/1.03  --res_out_proof                         true
% 1.25/1.03  
% 1.25/1.03  ------ Superposition Options
% 1.25/1.03  
% 1.25/1.03  --superposition_flag                    true
% 1.25/1.03  --sup_passive_queue_type                priority_queues
% 1.25/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.25/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.25/1.03  --demod_completeness_check              fast
% 1.25/1.03  --demod_use_ground                      true
% 1.25/1.03  --sup_to_prop_solver                    passive
% 1.25/1.03  --sup_prop_simpl_new                    true
% 1.25/1.03  --sup_prop_simpl_given                  true
% 1.25/1.03  --sup_fun_splitting                     false
% 1.25/1.03  --sup_smt_interval                      50000
% 1.25/1.03  
% 1.25/1.03  ------ Superposition Simplification Setup
% 1.25/1.03  
% 1.25/1.03  --sup_indices_passive                   []
% 1.25/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.25/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.25/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.25/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.25/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.25/1.03  --sup_full_bw                           [BwDemod]
% 1.25/1.03  --sup_immed_triv                        [TrivRules]
% 1.25/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.25/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.25/1.03  --sup_immed_bw_main                     []
% 1.25/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.25/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.25/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.25/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.25/1.03  
% 1.25/1.03  ------ Combination Options
% 1.25/1.03  
% 1.25/1.03  --comb_res_mult                         3
% 1.25/1.03  --comb_sup_mult                         2
% 1.25/1.03  --comb_inst_mult                        10
% 1.25/1.03  
% 1.25/1.03  ------ Debug Options
% 1.25/1.03  
% 1.25/1.03  --dbg_backtrace                         false
% 1.25/1.03  --dbg_dump_prop_clauses                 false
% 1.25/1.03  --dbg_dump_prop_clauses_file            -
% 1.25/1.03  --dbg_out_stat                          false
% 1.25/1.03  
% 1.25/1.03  
% 1.25/1.03  
% 1.25/1.03  
% 1.25/1.03  ------ Proving...
% 1.25/1.03  
% 1.25/1.03  
% 1.25/1.03  % SZS status Theorem for theBenchmark.p
% 1.25/1.03  
% 1.25/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 1.25/1.03  
% 1.25/1.03  fof(f13,axiom,(
% 1.25/1.03    ! [X0] : (v1_relat_1(X0) => (! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) => k1_xboole_0 = X0))),
% 1.25/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.25/1.03  
% 1.25/1.03  fof(f31,plain,(
% 1.25/1.03    ! [X0] : ((k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)) | ~v1_relat_1(X0))),
% 1.25/1.03    inference(ennf_transformation,[],[f13])).
% 1.25/1.03  
% 1.25/1.03  fof(f32,plain,(
% 1.25/1.03    ! [X0] : (k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) | ~v1_relat_1(X0))),
% 1.25/1.03    inference(flattening,[],[f31])).
% 1.25/1.03  
% 1.25/1.03  fof(f49,plain,(
% 1.25/1.03    ! [X0] : (? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) => r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0))),
% 1.25/1.03    introduced(choice_axiom,[])).
% 1.25/1.03  
% 1.25/1.03  fof(f50,plain,(
% 1.25/1.03    ! [X0] : (k1_xboole_0 = X0 | r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) | ~v1_relat_1(X0))),
% 1.25/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f32,f49])).
% 1.25/1.03  
% 1.25/1.03  fof(f69,plain,(
% 1.25/1.03    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) | ~v1_relat_1(X0)) )),
% 1.25/1.03    inference(cnf_transformation,[],[f50])).
% 1.25/1.03  
% 1.25/1.03  fof(f9,axiom,(
% 1.25/1.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.25/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.25/1.03  
% 1.25/1.03  fof(f26,plain,(
% 1.25/1.03    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.25/1.03    inference(ennf_transformation,[],[f9])).
% 1.25/1.03  
% 1.25/1.03  fof(f64,plain,(
% 1.25/1.03    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.25/1.03    inference(cnf_transformation,[],[f26])).
% 1.25/1.03  
% 1.25/1.03  fof(f23,conjecture,(
% 1.25/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 1.25/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.25/1.03  
% 1.25/1.03  fof(f24,negated_conjecture,(
% 1.25/1.03    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 1.25/1.03    inference(negated_conjecture,[],[f23])).
% 1.25/1.03  
% 1.25/1.03  fof(f43,plain,(
% 1.25/1.03    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 1.25/1.03    inference(ennf_transformation,[],[f24])).
% 1.25/1.03  
% 1.25/1.03  fof(f44,plain,(
% 1.25/1.03    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 1.25/1.03    inference(flattening,[],[f43])).
% 1.25/1.03  
% 1.25/1.03  fof(f52,plain,(
% 1.25/1.03    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK5,sK3),sK4) & k1_xboole_0 != sK4 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) & v1_funct_2(sK5,k1_tarski(sK3),sK4) & v1_funct_1(sK5))),
% 1.25/1.03    introduced(choice_axiom,[])).
% 1.25/1.03  
% 1.25/1.03  fof(f53,plain,(
% 1.25/1.03    ~r2_hidden(k1_funct_1(sK5,sK3),sK4) & k1_xboole_0 != sK4 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) & v1_funct_2(sK5,k1_tarski(sK3),sK4) & v1_funct_1(sK5)),
% 1.25/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f44,f52])).
% 1.25/1.03  
% 1.25/1.03  fof(f85,plain,(
% 1.25/1.03    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4)))),
% 1.25/1.03    inference(cnf_transformation,[],[f53])).
% 1.25/1.03  
% 1.25/1.03  fof(f3,axiom,(
% 1.25/1.03    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.25/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.25/1.03  
% 1.25/1.03  fof(f56,plain,(
% 1.25/1.03    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.25/1.03    inference(cnf_transformation,[],[f3])).
% 1.25/1.03  
% 1.25/1.03  fof(f4,axiom,(
% 1.25/1.03    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.25/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.25/1.03  
% 1.25/1.03  fof(f57,plain,(
% 1.25/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.25/1.03    inference(cnf_transformation,[],[f4])).
% 1.25/1.03  
% 1.25/1.03  fof(f5,axiom,(
% 1.25/1.03    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.25/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.25/1.03  
% 1.25/1.03  fof(f58,plain,(
% 1.25/1.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.25/1.03    inference(cnf_transformation,[],[f5])).
% 1.25/1.03  
% 1.25/1.03  fof(f88,plain,(
% 1.25/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.25/1.03    inference(definition_unfolding,[],[f57,f58])).
% 1.25/1.03  
% 1.25/1.03  fof(f89,plain,(
% 1.25/1.03    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.25/1.03    inference(definition_unfolding,[],[f56,f88])).
% 1.25/1.03  
% 1.25/1.03  fof(f94,plain,(
% 1.25/1.03    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))),
% 1.25/1.03    inference(definition_unfolding,[],[f85,f89])).
% 1.25/1.03  
% 1.25/1.03  fof(f7,axiom,(
% 1.25/1.03    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <=> (r2_hidden(X1,X3) & X0 = X2))),
% 1.25/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.25/1.03  
% 1.25/1.03  fof(f45,plain,(
% 1.25/1.03    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | (~r2_hidden(X1,X3) | X0 != X2)) & ((r2_hidden(X1,X3) & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 1.25/1.03    inference(nnf_transformation,[],[f7])).
% 1.25/1.03  
% 1.25/1.03  fof(f46,plain,(
% 1.25/1.03    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | ~r2_hidden(X1,X3) | X0 != X2) & ((r2_hidden(X1,X3) & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 1.25/1.03    inference(flattening,[],[f45])).
% 1.25/1.03  
% 1.25/1.03  fof(f60,plain,(
% 1.25/1.03    ( ! [X2,X0,X3,X1] : (X0 = X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))) )),
% 1.25/1.03    inference(cnf_transformation,[],[f46])).
% 1.25/1.03  
% 1.25/1.03  fof(f93,plain,(
% 1.25/1.03    ( ! [X2,X0,X3,X1] : (X0 = X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3))) )),
% 1.25/1.03    inference(definition_unfolding,[],[f60,f89])).
% 1.25/1.03  
% 1.25/1.03  fof(f20,axiom,(
% 1.25/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.25/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.25/1.03  
% 1.25/1.03  fof(f39,plain,(
% 1.25/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.25/1.03    inference(ennf_transformation,[],[f20])).
% 1.25/1.03  
% 1.25/1.03  fof(f80,plain,(
% 1.25/1.03    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.25/1.03    inference(cnf_transformation,[],[f39])).
% 1.25/1.03  
% 1.25/1.03  fof(f12,axiom,(
% 1.25/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.25/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.25/1.03  
% 1.25/1.03  fof(f29,plain,(
% 1.25/1.03    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 1.25/1.03    inference(ennf_transformation,[],[f12])).
% 1.25/1.03  
% 1.25/1.03  fof(f30,plain,(
% 1.25/1.03    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 1.25/1.03    inference(flattening,[],[f29])).
% 1.25/1.03  
% 1.25/1.03  fof(f67,plain,(
% 1.25/1.03    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 1.25/1.03    inference(cnf_transformation,[],[f30])).
% 1.25/1.03  
% 1.25/1.03  fof(f87,plain,(
% 1.25/1.03    ~r2_hidden(k1_funct_1(sK5,sK3),sK4)),
% 1.25/1.03    inference(cnf_transformation,[],[f53])).
% 1.25/1.03  
% 1.25/1.03  fof(f21,axiom,(
% 1.25/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.25/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.25/1.03  
% 1.25/1.03  fof(f25,plain,(
% 1.25/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.25/1.03    inference(pure_predicate_removal,[],[f21])).
% 1.25/1.03  
% 1.25/1.03  fof(f40,plain,(
% 1.25/1.03    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.25/1.03    inference(ennf_transformation,[],[f25])).
% 1.25/1.03  
% 1.25/1.03  fof(f81,plain,(
% 1.25/1.03    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.25/1.03    inference(cnf_transformation,[],[f40])).
% 1.25/1.03  
% 1.25/1.03  fof(f18,axiom,(
% 1.25/1.03    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 1.25/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.25/1.03  
% 1.25/1.03  fof(f36,plain,(
% 1.25/1.03    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.25/1.03    inference(ennf_transformation,[],[f18])).
% 1.25/1.03  
% 1.25/1.03  fof(f37,plain,(
% 1.25/1.03    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.25/1.03    inference(flattening,[],[f36])).
% 1.25/1.03  
% 1.25/1.03  fof(f78,plain,(
% 1.25/1.03    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.25/1.03    inference(cnf_transformation,[],[f37])).
% 1.25/1.03  
% 1.25/1.03  fof(f83,plain,(
% 1.25/1.03    v1_funct_1(sK5)),
% 1.25/1.03    inference(cnf_transformation,[],[f53])).
% 1.25/1.03  
% 1.25/1.03  fof(f8,axiom,(
% 1.25/1.03    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 1.25/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.25/1.03  
% 1.25/1.03  fof(f47,plain,(
% 1.25/1.03    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK0(X0),X0))),
% 1.25/1.03    introduced(choice_axiom,[])).
% 1.25/1.03  
% 1.25/1.03  fof(f48,plain,(
% 1.25/1.03    ! [X0] : m1_subset_1(sK0(X0),X0)),
% 1.25/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f47])).
% 1.25/1.03  
% 1.25/1.03  fof(f63,plain,(
% 1.25/1.03    ( ! [X0] : (m1_subset_1(sK0(X0),X0)) )),
% 1.25/1.03    inference(cnf_transformation,[],[f48])).
% 1.25/1.03  
% 1.25/1.03  fof(f10,axiom,(
% 1.25/1.03    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.25/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.25/1.03  
% 1.25/1.03  fof(f27,plain,(
% 1.25/1.03    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.25/1.03    inference(ennf_transformation,[],[f10])).
% 1.25/1.03  
% 1.25/1.03  fof(f28,plain,(
% 1.25/1.03    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.25/1.03    inference(flattening,[],[f27])).
% 1.25/1.03  
% 1.25/1.03  fof(f65,plain,(
% 1.25/1.03    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.25/1.03    inference(cnf_transformation,[],[f28])).
% 1.25/1.03  
% 1.25/1.03  fof(f22,axiom,(
% 1.25/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 1.25/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.25/1.03  
% 1.25/1.03  fof(f41,plain,(
% 1.25/1.03    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.25/1.03    inference(ennf_transformation,[],[f22])).
% 1.25/1.03  
% 1.25/1.03  fof(f42,plain,(
% 1.25/1.03    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.25/1.03    inference(flattening,[],[f41])).
% 1.25/1.03  
% 1.25/1.03  fof(f82,plain,(
% 1.25/1.03    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.25/1.03    inference(cnf_transformation,[],[f42])).
% 1.25/1.03  
% 1.25/1.03  fof(f84,plain,(
% 1.25/1.03    v1_funct_2(sK5,k1_tarski(sK3),sK4)),
% 1.25/1.03    inference(cnf_transformation,[],[f53])).
% 1.25/1.03  
% 1.25/1.03  fof(f95,plain,(
% 1.25/1.03    v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4)),
% 1.25/1.03    inference(definition_unfolding,[],[f84,f89])).
% 1.25/1.03  
% 1.25/1.03  fof(f86,plain,(
% 1.25/1.03    k1_xboole_0 != sK4),
% 1.25/1.03    inference(cnf_transformation,[],[f53])).
% 1.25/1.03  
% 1.25/1.03  fof(f6,axiom,(
% 1.25/1.03    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 1.25/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.25/1.03  
% 1.25/1.03  fof(f59,plain,(
% 1.25/1.03    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 1.25/1.03    inference(cnf_transformation,[],[f6])).
% 1.25/1.03  
% 1.25/1.03  fof(f90,plain,(
% 1.25/1.03    ( ! [X0] : (~v1_xboole_0(k2_enumset1(X0,X0,X0,X0))) )),
% 1.25/1.03    inference(definition_unfolding,[],[f59,f89])).
% 1.25/1.03  
% 1.25/1.03  fof(f14,axiom,(
% 1.25/1.03    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.25/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.25/1.03  
% 1.25/1.03  fof(f70,plain,(
% 1.25/1.03    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.25/1.03    inference(cnf_transformation,[],[f14])).
% 1.25/1.03  
% 1.25/1.03  fof(f17,axiom,(
% 1.25/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 1.25/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.25/1.03  
% 1.25/1.03  fof(f34,plain,(
% 1.25/1.03    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.25/1.03    inference(ennf_transformation,[],[f17])).
% 1.25/1.03  
% 1.25/1.03  fof(f35,plain,(
% 1.25/1.03    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.25/1.03    inference(flattening,[],[f34])).
% 1.25/1.03  
% 1.25/1.03  fof(f51,plain,(
% 1.25/1.03    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.25/1.03    inference(nnf_transformation,[],[f35])).
% 1.25/1.03  
% 1.25/1.03  fof(f76,plain,(
% 1.25/1.03    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2 | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.25/1.03    inference(cnf_transformation,[],[f51])).
% 1.25/1.03  
% 1.25/1.03  fof(f98,plain,(
% 1.25/1.03    ( ! [X0,X1] : (k1_xboole_0 = k1_funct_1(X0,X1) | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.25/1.03    inference(equality_resolution,[],[f76])).
% 1.25/1.03  
% 1.25/1.03  fof(f16,axiom,(
% 1.25/1.03    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 1.25/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.25/1.03  
% 1.25/1.03  fof(f33,plain,(
% 1.25/1.03    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 1.25/1.03    inference(ennf_transformation,[],[f16])).
% 1.25/1.03  
% 1.25/1.03  fof(f73,plain,(
% 1.25/1.03    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 1.25/1.03    inference(cnf_transformation,[],[f33])).
% 1.25/1.03  
% 1.25/1.03  fof(f1,axiom,(
% 1.25/1.03    v1_xboole_0(k1_xboole_0)),
% 1.25/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.25/1.03  
% 1.25/1.03  fof(f54,plain,(
% 1.25/1.03    v1_xboole_0(k1_xboole_0)),
% 1.25/1.03    inference(cnf_transformation,[],[f1])).
% 1.25/1.03  
% 1.25/1.03  fof(f2,axiom,(
% 1.25/1.03    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.25/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.25/1.03  
% 1.25/1.03  fof(f55,plain,(
% 1.25/1.03    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.25/1.03    inference(cnf_transformation,[],[f2])).
% 1.25/1.03  
% 1.25/1.03  fof(f19,axiom,(
% 1.25/1.03    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.25/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.25/1.03  
% 1.25/1.03  fof(f38,plain,(
% 1.25/1.03    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.25/1.03    inference(ennf_transformation,[],[f19])).
% 1.25/1.03  
% 1.25/1.03  fof(f79,plain,(
% 1.25/1.03    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.25/1.03    inference(cnf_transformation,[],[f38])).
% 1.25/1.03  
% 1.25/1.03  fof(f15,axiom,(
% 1.25/1.03    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.25/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.25/1.03  
% 1.25/1.03  fof(f72,plain,(
% 1.25/1.03    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.25/1.03    inference(cnf_transformation,[],[f15])).
% 1.25/1.03  
% 1.25/1.03  fof(f11,axiom,(
% 1.25/1.03    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.25/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.25/1.03  
% 1.25/1.03  fof(f66,plain,(
% 1.25/1.03    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.25/1.03    inference(cnf_transformation,[],[f11])).
% 1.25/1.03  
% 1.25/1.03  cnf(c_12,plain,
% 1.25/1.03      ( r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
% 1.25/1.03      | ~ v1_relat_1(X0)
% 1.25/1.03      | k1_xboole_0 = X0 ),
% 1.25/1.03      inference(cnf_transformation,[],[f69]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_2192,plain,
% 1.25/1.03      ( k1_xboole_0 = X0
% 1.25/1.03      | r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) = iProver_top
% 1.25/1.03      | v1_relat_1(X0) != iProver_top ),
% 1.25/1.03      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_7,plain,
% 1.25/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.25/1.03      | ~ r2_hidden(X2,X0)
% 1.25/1.03      | r2_hidden(X2,X1) ),
% 1.25/1.03      inference(cnf_transformation,[],[f64]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_28,negated_conjecture,
% 1.25/1.03      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) ),
% 1.25/1.03      inference(cnf_transformation,[],[f94]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_464,plain,
% 1.25/1.03      ( ~ r2_hidden(X0,X1)
% 1.25/1.03      | r2_hidden(X0,X2)
% 1.25/1.03      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(X2)
% 1.25/1.03      | sK5 != X1 ),
% 1.25/1.03      inference(resolution_lifted,[status(thm)],[c_7,c_28]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_465,plain,
% 1.25/1.03      ( r2_hidden(X0,X1)
% 1.25/1.03      | ~ r2_hidden(X0,sK5)
% 1.25/1.03      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(X1) ),
% 1.25/1.03      inference(unflattening,[status(thm)],[c_464]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_2179,plain,
% 1.25/1.03      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(X0)
% 1.25/1.03      | r2_hidden(X1,X0) = iProver_top
% 1.25/1.03      | r2_hidden(X1,sK5) != iProver_top ),
% 1.25/1.03      inference(predicate_to_equality,[status(thm)],[c_465]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_2420,plain,
% 1.25/1.03      ( r2_hidden(X0,k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) = iProver_top
% 1.25/1.03      | r2_hidden(X0,sK5) != iProver_top ),
% 1.25/1.03      inference(equality_resolution,[status(thm)],[c_2179]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_5,plain,
% 1.25/1.03      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3))
% 1.25/1.03      | X2 = X0 ),
% 1.25/1.03      inference(cnf_transformation,[],[f93]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_2196,plain,
% 1.25/1.03      ( X0 = X1
% 1.25/1.03      | r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),X3)) != iProver_top ),
% 1.25/1.03      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_3058,plain,
% 1.25/1.03      ( sK3 = X0 | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top ),
% 1.25/1.03      inference(superposition,[status(thm)],[c_2420,c_2196]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_3276,plain,
% 1.25/1.03      ( sK1(sK5) = sK3
% 1.25/1.03      | sK5 = k1_xboole_0
% 1.25/1.03      | v1_relat_1(sK5) != iProver_top ),
% 1.25/1.03      inference(superposition,[status(thm)],[c_2192,c_3058]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_1726,plain,( X0 = X0 ),theory(equality) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_2376,plain,
% 1.25/1.03      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) ),
% 1.25/1.03      inference(instantiation,[status(thm)],[c_1726]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_23,plain,
% 1.25/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.25/1.03      | v1_relat_1(X0) ),
% 1.25/1.03      inference(cnf_transformation,[],[f80]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_510,plain,
% 1.25/1.03      ( v1_relat_1(X0)
% 1.25/1.03      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.25/1.03      | sK5 != X0 ),
% 1.25/1.03      inference(resolution_lifted,[status(thm)],[c_23,c_28]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_511,plain,
% 1.25/1.03      ( v1_relat_1(sK5)
% 1.25/1.03      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.25/1.03      inference(unflattening,[status(thm)],[c_510]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_2377,plain,
% 1.25/1.03      ( v1_relat_1(sK5)
% 1.25/1.03      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) ),
% 1.25/1.03      inference(instantiation,[status(thm)],[c_511]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_3277,plain,
% 1.25/1.03      ( ~ v1_relat_1(sK5) | sK1(sK5) = sK3 | sK5 = k1_xboole_0 ),
% 1.25/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_3276]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_3350,plain,
% 1.25/1.03      ( sK5 = k1_xboole_0 | sK1(sK5) = sK3 ),
% 1.25/1.03      inference(global_propositional_subsumption,
% 1.25/1.03                [status(thm)],
% 1.25/1.03                [c_3276,c_2376,c_2377,c_3277]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_3351,plain,
% 1.25/1.03      ( sK1(sK5) = sK3 | sK5 = k1_xboole_0 ),
% 1.25/1.03      inference(renaming,[status(thm)],[c_3350]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_3354,plain,
% 1.25/1.03      ( sK5 = k1_xboole_0
% 1.25/1.03      | r2_hidden(k4_tarski(sK3,sK2(sK5)),sK5) = iProver_top
% 1.25/1.03      | v1_relat_1(sK5) != iProver_top ),
% 1.25/1.03      inference(superposition,[status(thm)],[c_3351,c_2192]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_2378,plain,
% 1.25/1.03      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
% 1.25/1.03      | v1_relat_1(sK5) = iProver_top ),
% 1.25/1.03      inference(predicate_to_equality,[status(thm)],[c_2377]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_3411,plain,
% 1.25/1.03      ( r2_hidden(k4_tarski(sK3,sK2(sK5)),sK5) = iProver_top
% 1.25/1.03      | sK5 = k1_xboole_0 ),
% 1.25/1.03      inference(global_propositional_subsumption,
% 1.25/1.03                [status(thm)],
% 1.25/1.03                [c_3354,c_2376,c_2378]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_3412,plain,
% 1.25/1.03      ( sK5 = k1_xboole_0
% 1.25/1.03      | r2_hidden(k4_tarski(sK3,sK2(sK5)),sK5) = iProver_top ),
% 1.25/1.03      inference(renaming,[status(thm)],[c_3411]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_11,plain,
% 1.25/1.03      ( r2_hidden(X0,k1_relat_1(X1))
% 1.25/1.03      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 1.25/1.03      | ~ v1_relat_1(X1) ),
% 1.25/1.03      inference(cnf_transformation,[],[f67]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_2193,plain,
% 1.25/1.03      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 1.25/1.03      | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top
% 1.25/1.03      | v1_relat_1(X1) != iProver_top ),
% 1.25/1.03      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_3533,plain,
% 1.25/1.03      ( r2_hidden(X0,k1_relat_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top
% 1.25/1.03      | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top
% 1.25/1.03      | v1_relat_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != iProver_top ),
% 1.25/1.03      inference(superposition,[status(thm)],[c_2420,c_2193]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_3959,plain,
% 1.25/1.03      ( sK5 = k1_xboole_0
% 1.25/1.03      | r2_hidden(sK3,k1_relat_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top
% 1.25/1.03      | v1_relat_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != iProver_top ),
% 1.25/1.03      inference(superposition,[status(thm)],[c_3412,c_3533]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_26,negated_conjecture,
% 1.25/1.03      ( ~ r2_hidden(k1_funct_1(sK5,sK3),sK4) ),
% 1.25/1.03      inference(cnf_transformation,[],[f87]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_34,plain,
% 1.25/1.03      ( r2_hidden(k1_funct_1(sK5,sK3),sK4) != iProver_top ),
% 1.25/1.03      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_24,plain,
% 1.25/1.03      ( v5_relat_1(X0,X1)
% 1.25/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 1.25/1.03      inference(cnf_transformation,[],[f81]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_21,plain,
% 1.25/1.03      ( ~ v5_relat_1(X0,X1)
% 1.25/1.03      | ~ r2_hidden(X2,k1_relat_1(X0))
% 1.25/1.03      | r2_hidden(k1_funct_1(X0,X2),X1)
% 1.25/1.03      | ~ v1_funct_1(X0)
% 1.25/1.03      | ~ v1_relat_1(X0) ),
% 1.25/1.03      inference(cnf_transformation,[],[f78]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_325,plain,
% 1.25/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.25/1.03      | ~ r2_hidden(X3,k1_relat_1(X0))
% 1.25/1.03      | r2_hidden(k1_funct_1(X0,X3),X2)
% 1.25/1.03      | ~ v1_funct_1(X0)
% 1.25/1.03      | ~ v1_relat_1(X0) ),
% 1.25/1.03      inference(resolution,[status(thm)],[c_24,c_21]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_329,plain,
% 1.25/1.03      ( ~ v1_funct_1(X0)
% 1.25/1.03      | r2_hidden(k1_funct_1(X0,X3),X2)
% 1.25/1.03      | ~ r2_hidden(X3,k1_relat_1(X0))
% 1.25/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.25/1.03      inference(global_propositional_subsumption,
% 1.25/1.03                [status(thm)],
% 1.25/1.03                [c_325,c_23]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_330,plain,
% 1.25/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.25/1.03      | ~ r2_hidden(X3,k1_relat_1(X0))
% 1.25/1.03      | r2_hidden(k1_funct_1(X0,X3),X2)
% 1.25/1.03      | ~ v1_funct_1(X0) ),
% 1.25/1.03      inference(renaming,[status(thm)],[c_329]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_489,plain,
% 1.25/1.03      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 1.25/1.03      | r2_hidden(k1_funct_1(X1,X0),X2)
% 1.25/1.03      | ~ v1_funct_1(X1)
% 1.25/1.03      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X3,X2))
% 1.25/1.03      | sK5 != X1 ),
% 1.25/1.03      inference(resolution_lifted,[status(thm)],[c_330,c_28]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_490,plain,
% 1.25/1.03      ( ~ r2_hidden(X0,k1_relat_1(sK5))
% 1.25/1.03      | r2_hidden(k1_funct_1(sK5,X0),X1)
% 1.25/1.03      | ~ v1_funct_1(sK5)
% 1.25/1.03      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X2,X1)) ),
% 1.25/1.03      inference(unflattening,[status(thm)],[c_489]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_30,negated_conjecture,
% 1.25/1.03      ( v1_funct_1(sK5) ),
% 1.25/1.03      inference(cnf_transformation,[],[f83]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_494,plain,
% 1.25/1.03      ( r2_hidden(k1_funct_1(sK5,X0),X1)
% 1.25/1.03      | ~ r2_hidden(X0,k1_relat_1(sK5))
% 1.25/1.03      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X2,X1)) ),
% 1.25/1.03      inference(global_propositional_subsumption,
% 1.25/1.03                [status(thm)],
% 1.25/1.03                [c_490,c_30]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_495,plain,
% 1.25/1.03      ( ~ r2_hidden(X0,k1_relat_1(sK5))
% 1.25/1.03      | r2_hidden(k1_funct_1(sK5,X0),X1)
% 1.25/1.03      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X2,X1)) ),
% 1.25/1.03      inference(renaming,[status(thm)],[c_494]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_2592,plain,
% 1.25/1.03      ( ~ r2_hidden(X0,k1_relat_1(sK5))
% 1.25/1.03      | r2_hidden(k1_funct_1(sK5,X0),sK4)
% 1.25/1.03      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) ),
% 1.25/1.03      inference(instantiation,[status(thm)],[c_495]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_2622,plain,
% 1.25/1.03      ( r2_hidden(k1_funct_1(sK5,sK3),sK4)
% 1.25/1.03      | ~ r2_hidden(sK3,k1_relat_1(sK5))
% 1.25/1.03      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) ),
% 1.25/1.03      inference(instantiation,[status(thm)],[c_2592]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_2623,plain,
% 1.25/1.03      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
% 1.25/1.03      | r2_hidden(k1_funct_1(sK5,sK3),sK4) = iProver_top
% 1.25/1.03      | r2_hidden(sK3,k1_relat_1(sK5)) != iProver_top ),
% 1.25/1.03      inference(predicate_to_equality,[status(thm)],[c_2622]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_3534,plain,
% 1.25/1.03      ( sK5 = k1_xboole_0
% 1.25/1.03      | r2_hidden(sK3,k1_relat_1(sK5)) = iProver_top
% 1.25/1.03      | v1_relat_1(sK5) != iProver_top ),
% 1.25/1.03      inference(superposition,[status(thm)],[c_3412,c_2193]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_4107,plain,
% 1.25/1.03      ( sK5 = k1_xboole_0 ),
% 1.25/1.03      inference(global_propositional_subsumption,
% 1.25/1.03                [status(thm)],
% 1.25/1.03                [c_3959,c_34,c_2376,c_2378,c_2623,c_3534]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_6,plain,
% 1.25/1.03      ( m1_subset_1(sK0(X0),X0) ),
% 1.25/1.03      inference(cnf_transformation,[],[f63]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_8,plain,
% 1.25/1.03      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 1.25/1.03      inference(cnf_transformation,[],[f65]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_430,plain,
% 1.25/1.03      ( r2_hidden(X0,X1) | v1_xboole_0(X1) | X1 != X2 | sK0(X2) != X0 ),
% 1.25/1.03      inference(resolution_lifted,[status(thm)],[c_6,c_8]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_431,plain,
% 1.25/1.03      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 1.25/1.03      inference(unflattening,[status(thm)],[c_430]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_2182,plain,
% 1.25/1.03      ( r2_hidden(sK0(X0),X0) = iProver_top
% 1.25/1.03      | v1_xboole_0(X0) = iProver_top ),
% 1.25/1.03      inference(predicate_to_equality,[status(thm)],[c_431]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_25,plain,
% 1.25/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 1.25/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.25/1.03      | ~ r2_hidden(X3,X1)
% 1.25/1.03      | r2_hidden(k1_funct_1(X0,X3),X2)
% 1.25/1.03      | ~ v1_funct_1(X0)
% 1.25/1.03      | k1_xboole_0 = X2 ),
% 1.25/1.03      inference(cnf_transformation,[],[f82]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_29,negated_conjecture,
% 1.25/1.03      ( v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
% 1.25/1.03      inference(cnf_transformation,[],[f95]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_353,plain,
% 1.25/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.25/1.03      | ~ r2_hidden(X3,X1)
% 1.25/1.03      | r2_hidden(k1_funct_1(X0,X3),X2)
% 1.25/1.03      | ~ v1_funct_1(X0)
% 1.25/1.03      | k2_enumset1(sK3,sK3,sK3,sK3) != X1
% 1.25/1.03      | sK4 != X2
% 1.25/1.03      | sK5 != X0
% 1.25/1.03      | k1_xboole_0 = X2 ),
% 1.25/1.03      inference(resolution_lifted,[status(thm)],[c_25,c_29]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_354,plain,
% 1.25/1.03      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
% 1.25/1.03      | ~ r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3))
% 1.25/1.03      | r2_hidden(k1_funct_1(sK5,X0),sK4)
% 1.25/1.03      | ~ v1_funct_1(sK5)
% 1.25/1.03      | k1_xboole_0 = sK4 ),
% 1.25/1.03      inference(unflattening,[status(thm)],[c_353]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_27,negated_conjecture,
% 1.25/1.03      ( k1_xboole_0 != sK4 ),
% 1.25/1.03      inference(cnf_transformation,[],[f86]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_358,plain,
% 1.25/1.03      ( ~ r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3))
% 1.25/1.03      | r2_hidden(k1_funct_1(sK5,X0),sK4) ),
% 1.25/1.03      inference(global_propositional_subsumption,
% 1.25/1.03                [status(thm)],
% 1.25/1.03                [c_354,c_30,c_28,c_27]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_2184,plain,
% 1.25/1.03      ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
% 1.25/1.03      | r2_hidden(k1_funct_1(sK5,X0),sK4) = iProver_top ),
% 1.25/1.03      inference(predicate_to_equality,[status(thm)],[c_358]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_3521,plain,
% 1.25/1.03      ( r2_hidden(k1_funct_1(sK5,sK0(k2_enumset1(sK3,sK3,sK3,sK3))),sK4) = iProver_top
% 1.25/1.03      | v1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top ),
% 1.25/1.03      inference(superposition,[status(thm)],[c_2182,c_2184]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_2380,plain,
% 1.25/1.03      ( r2_hidden(sK0(k2_enumset1(X0,X0,X0,X0)),k2_enumset1(X0,X0,X0,X0))
% 1.25/1.03      | v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
% 1.25/1.03      inference(instantiation,[status(thm)],[c_431]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_2936,plain,
% 1.25/1.03      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
% 1.25/1.03      | v1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 1.25/1.03      inference(instantiation,[status(thm)],[c_2380]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_2938,plain,
% 1.25/1.03      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top
% 1.25/1.03      | v1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top ),
% 1.25/1.03      inference(predicate_to_equality,[status(thm)],[c_2936]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_2937,plain,
% 1.25/1.03      ( r2_hidden(k1_funct_1(sK5,sK0(k2_enumset1(sK3,sK3,sK3,sK3))),sK4)
% 1.25/1.03      | ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 1.25/1.03      inference(instantiation,[status(thm)],[c_358]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_2940,plain,
% 1.25/1.03      ( r2_hidden(k1_funct_1(sK5,sK0(k2_enumset1(sK3,sK3,sK3,sK3))),sK4) = iProver_top
% 1.25/1.03      | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
% 1.25/1.03      inference(predicate_to_equality,[status(thm)],[c_2937]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_2,plain,
% 1.25/1.03      ( ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
% 1.25/1.03      inference(cnf_transformation,[],[f90]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_2961,plain,
% 1.25/1.03      ( ~ v1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 1.25/1.03      inference(instantiation,[status(thm)],[c_2]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_2962,plain,
% 1.25/1.03      ( v1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
% 1.25/1.03      inference(predicate_to_equality,[status(thm)],[c_2961]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_3817,plain,
% 1.25/1.03      ( r2_hidden(k1_funct_1(sK5,sK0(k2_enumset1(sK3,sK3,sK3,sK3))),sK4) = iProver_top ),
% 1.25/1.03      inference(global_propositional_subsumption,
% 1.25/1.03                [status(thm)],
% 1.25/1.03                [c_3521,c_2938,c_2940,c_2962]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_4112,plain,
% 1.25/1.03      ( r2_hidden(k1_funct_1(k1_xboole_0,sK0(k2_enumset1(sK3,sK3,sK3,sK3))),sK4) = iProver_top ),
% 1.25/1.03      inference(demodulation,[status(thm)],[c_4107,c_3817]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_14,plain,
% 1.25/1.03      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 1.25/1.03      inference(cnf_transformation,[],[f70]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_18,plain,
% 1.25/1.03      ( r2_hidden(X0,k1_relat_1(X1))
% 1.25/1.03      | ~ v1_funct_1(X1)
% 1.25/1.03      | ~ v1_relat_1(X1)
% 1.25/1.03      | k1_funct_1(X1,X0) = k1_xboole_0 ),
% 1.25/1.03      inference(cnf_transformation,[],[f98]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_2190,plain,
% 1.25/1.03      ( k1_funct_1(X0,X1) = k1_xboole_0
% 1.25/1.03      | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
% 1.25/1.03      | v1_funct_1(X0) != iProver_top
% 1.25/1.03      | v1_relat_1(X0) != iProver_top ),
% 1.25/1.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_3637,plain,
% 1.25/1.03      ( k1_funct_1(k1_xboole_0,X0) = k1_xboole_0
% 1.25/1.03      | r2_hidden(X0,k1_xboole_0) = iProver_top
% 1.25/1.03      | v1_funct_1(k1_xboole_0) != iProver_top
% 1.25/1.03      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 1.25/1.03      inference(superposition,[status(thm)],[c_14,c_2190]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_16,plain,
% 1.25/1.03      ( v1_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 1.25/1.03      inference(cnf_transformation,[],[f73]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_60,plain,
% 1.25/1.03      ( v1_funct_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 1.25/1.03      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_62,plain,
% 1.25/1.03      ( v1_funct_1(k1_xboole_0) = iProver_top
% 1.25/1.03      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 1.25/1.03      inference(instantiation,[status(thm)],[c_60]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_0,plain,
% 1.25/1.03      ( v1_xboole_0(k1_xboole_0) ),
% 1.25/1.03      inference(cnf_transformation,[],[f54]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_97,plain,
% 1.25/1.03      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 1.25/1.03      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_1,plain,
% 1.25/1.03      ( r1_tarski(k1_xboole_0,X0) ),
% 1.25/1.03      inference(cnf_transformation,[],[f55]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_22,plain,
% 1.25/1.03      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 1.25/1.03      inference(cnf_transformation,[],[f79]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_314,plain,
% 1.25/1.03      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 1.25/1.03      inference(resolution_lifted,[status(thm)],[c_1,c_22]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_315,plain,
% 1.25/1.03      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 1.25/1.03      inference(unflattening,[status(thm)],[c_314]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_316,plain,
% 1.25/1.03      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 1.25/1.03      inference(predicate_to_equality,[status(thm)],[c_315]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_15,plain,
% 1.25/1.03      ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 1.25/1.03      inference(cnf_transformation,[],[f72]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_9,plain,
% 1.25/1.03      ( v1_relat_1(k6_relat_1(X0)) ),
% 1.25/1.03      inference(cnf_transformation,[],[f66]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_2195,plain,
% 1.25/1.03      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 1.25/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_2777,plain,
% 1.25/1.03      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 1.25/1.03      inference(superposition,[status(thm)],[c_15,c_2195]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_3727,plain,
% 1.25/1.03      ( k1_funct_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 1.25/1.03      inference(global_propositional_subsumption,
% 1.25/1.03                [status(thm)],
% 1.25/1.03                [c_3637,c_62,c_97,c_316,c_2777]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_4170,plain,
% 1.25/1.03      ( r2_hidden(k1_xboole_0,sK4) = iProver_top ),
% 1.25/1.03      inference(demodulation,[status(thm)],[c_4112,c_3727]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_2177,plain,
% 1.25/1.03      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.25/1.03      | r2_hidden(X2,k1_relat_1(sK5)) != iProver_top
% 1.25/1.03      | r2_hidden(k1_funct_1(sK5,X2),X1) = iProver_top ),
% 1.25/1.03      inference(predicate_to_equality,[status(thm)],[c_495]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_2466,plain,
% 1.25/1.03      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 1.25/1.03      | r2_hidden(k1_funct_1(sK5,X0),sK4) = iProver_top ),
% 1.25/1.03      inference(equality_resolution,[status(thm)],[c_2177]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_2188,plain,
% 1.25/1.03      ( r2_hidden(k1_funct_1(sK5,sK3),sK4) != iProver_top ),
% 1.25/1.03      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_2634,plain,
% 1.25/1.03      ( r2_hidden(sK3,k1_relat_1(sK5)) != iProver_top ),
% 1.25/1.03      inference(superposition,[status(thm)],[c_2466,c_2188]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_3640,plain,
% 1.25/1.03      ( k1_funct_1(sK5,sK3) = k1_xboole_0
% 1.25/1.03      | v1_funct_1(sK5) != iProver_top
% 1.25/1.03      | v1_relat_1(sK5) != iProver_top ),
% 1.25/1.03      inference(superposition,[status(thm)],[c_2190,c_2634]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_31,plain,
% 1.25/1.03      ( v1_funct_1(sK5) = iProver_top ),
% 1.25/1.03      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_3732,plain,
% 1.25/1.03      ( k1_funct_1(sK5,sK3) = k1_xboole_0 ),
% 1.25/1.03      inference(global_propositional_subsumption,
% 1.25/1.03                [status(thm)],
% 1.25/1.03                [c_3640,c_31,c_2376,c_2378]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(c_3735,plain,
% 1.25/1.03      ( r2_hidden(k1_xboole_0,sK4) != iProver_top ),
% 1.25/1.03      inference(demodulation,[status(thm)],[c_3732,c_2188]) ).
% 1.25/1.03  
% 1.25/1.03  cnf(contradiction,plain,
% 1.25/1.03      ( $false ),
% 1.25/1.03      inference(minisat,[status(thm)],[c_4170,c_3735]) ).
% 1.25/1.03  
% 1.25/1.03  
% 1.25/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 1.25/1.03  
% 1.25/1.03  ------                               Statistics
% 1.25/1.03  
% 1.25/1.03  ------ General
% 1.25/1.03  
% 1.25/1.03  abstr_ref_over_cycles:                  0
% 1.25/1.03  abstr_ref_under_cycles:                 0
% 1.25/1.03  gc_basic_clause_elim:                   0
% 1.25/1.03  forced_gc_time:                         0
% 1.25/1.03  parsing_time:                           0.015
% 1.25/1.03  unif_index_cands_time:                  0.
% 1.25/1.03  unif_index_add_time:                    0.
% 1.25/1.03  orderings_time:                         0.
% 1.25/1.03  out_proof_time:                         0.012
% 1.25/1.03  total_time:                             0.162
% 1.25/1.03  num_of_symbols:                         54
% 1.25/1.03  num_of_terms:                           4130
% 1.25/1.03  
% 1.25/1.03  ------ Preprocessing
% 1.25/1.03  
% 1.25/1.03  num_of_splits:                          0
% 1.25/1.03  num_of_split_atoms:                     0
% 1.25/1.03  num_of_reused_defs:                     0
% 1.25/1.03  num_eq_ax_congr_red:                    10
% 1.25/1.03  num_of_sem_filtered_clauses:            1
% 1.25/1.03  num_of_subtypes:                        0
% 1.25/1.03  monotx_restored_types:                  0
% 1.25/1.03  sat_num_of_epr_types:                   0
% 1.25/1.03  sat_num_of_non_cyclic_types:            0
% 1.25/1.03  sat_guarded_non_collapsed_types:        0
% 1.25/1.03  num_pure_diseq_elim:                    0
% 1.25/1.03  simp_replaced_by:                       0
% 1.25/1.03  res_preprocessed:                       148
% 1.25/1.03  prep_upred:                             0
% 1.25/1.03  prep_unflattend:                        77
% 1.25/1.03  smt_new_axioms:                         0
% 1.25/1.03  pred_elim_cands:                        4
% 1.25/1.03  pred_elim:                              4
% 1.25/1.03  pred_elim_cl:                           1
% 1.25/1.03  pred_elim_cycles:                       11
% 1.25/1.03  merged_defs:                            0
% 1.25/1.03  merged_defs_ncl:                        0
% 1.25/1.03  bin_hyper_res:                          0
% 1.25/1.03  prep_cycles:                            4
% 1.25/1.03  pred_elim_time:                         0.023
% 1.25/1.03  splitting_time:                         0.
% 1.25/1.03  sem_filter_time:                        0.
% 1.25/1.03  monotx_time:                            0.001
% 1.25/1.03  subtype_inf_time:                       0.
% 1.25/1.03  
% 1.25/1.03  ------ Problem properties
% 1.25/1.03  
% 1.25/1.03  clauses:                                29
% 1.25/1.03  conjectures:                            3
% 1.25/1.03  epr:                                    5
% 1.25/1.03  horn:                                   25
% 1.25/1.03  ground:                                 8
% 1.25/1.03  unary:                                  11
% 1.25/1.03  binary:                                 9
% 1.25/1.03  lits:                                   59
% 1.25/1.03  lits_eq:                                11
% 1.25/1.03  fd_pure:                                0
% 1.25/1.03  fd_pseudo:                              0
% 1.25/1.03  fd_cond:                                1
% 1.25/1.03  fd_pseudo_cond:                         2
% 1.25/1.03  ac_symbols:                             0
% 1.25/1.03  
% 1.25/1.03  ------ Propositional Solver
% 1.25/1.03  
% 1.25/1.03  prop_solver_calls:                      27
% 1.25/1.03  prop_fast_solver_calls:                 1002
% 1.25/1.03  smt_solver_calls:                       0
% 1.25/1.03  smt_fast_solver_calls:                  0
% 1.25/1.03  prop_num_of_clauses:                    1187
% 1.25/1.03  prop_preprocess_simplified:             5316
% 1.25/1.03  prop_fo_subsumed:                       24
% 1.25/1.03  prop_solver_time:                       0.
% 1.25/1.03  smt_solver_time:                        0.
% 1.25/1.03  smt_fast_solver_time:                   0.
% 1.25/1.03  prop_fast_solver_time:                  0.
% 1.25/1.03  prop_unsat_core_time:                   0.
% 1.25/1.03  
% 1.25/1.03  ------ QBF
% 1.25/1.03  
% 1.25/1.03  qbf_q_res:                              0
% 1.25/1.03  qbf_num_tautologies:                    0
% 1.25/1.03  qbf_prep_cycles:                        0
% 1.25/1.03  
% 1.25/1.03  ------ BMC1
% 1.25/1.03  
% 1.25/1.03  bmc1_current_bound:                     -1
% 1.25/1.03  bmc1_last_solved_bound:                 -1
% 1.25/1.03  bmc1_unsat_core_size:                   -1
% 1.25/1.03  bmc1_unsat_core_parents_size:           -1
% 1.25/1.03  bmc1_merge_next_fun:                    0
% 1.25/1.03  bmc1_unsat_core_clauses_time:           0.
% 1.25/1.03  
% 1.25/1.03  ------ Instantiation
% 1.25/1.03  
% 1.25/1.03  inst_num_of_clauses:                    294
% 1.25/1.03  inst_num_in_passive:                    69
% 1.25/1.03  inst_num_in_active:                     196
% 1.25/1.03  inst_num_in_unprocessed:                29
% 1.25/1.03  inst_num_of_loops:                      230
% 1.25/1.03  inst_num_of_learning_restarts:          0
% 1.25/1.03  inst_num_moves_active_passive:          31
% 1.25/1.03  inst_lit_activity:                      0
% 1.25/1.03  inst_lit_activity_moves:                0
% 1.25/1.03  inst_num_tautologies:                   0
% 1.25/1.03  inst_num_prop_implied:                  0
% 1.25/1.03  inst_num_existing_simplified:           0
% 1.25/1.03  inst_num_eq_res_simplified:             0
% 1.25/1.03  inst_num_child_elim:                    0
% 1.25/1.03  inst_num_of_dismatching_blockings:      93
% 1.25/1.03  inst_num_of_non_proper_insts:           230
% 1.25/1.03  inst_num_of_duplicates:                 0
% 1.25/1.03  inst_inst_num_from_inst_to_res:         0
% 1.25/1.03  inst_dismatching_checking_time:         0.
% 1.25/1.03  
% 1.25/1.03  ------ Resolution
% 1.25/1.03  
% 1.25/1.03  res_num_of_clauses:                     0
% 1.25/1.03  res_num_in_passive:                     0
% 1.25/1.03  res_num_in_active:                      0
% 1.25/1.03  res_num_of_loops:                       152
% 1.25/1.03  res_forward_subset_subsumed:            47
% 1.25/1.03  res_backward_subset_subsumed:           0
% 1.25/1.03  res_forward_subsumed:                   0
% 1.25/1.03  res_backward_subsumed:                  0
% 1.25/1.03  res_forward_subsumption_resolution:     0
% 1.25/1.03  res_backward_subsumption_resolution:    0
% 1.25/1.03  res_clause_to_clause_subsumption:       123
% 1.25/1.03  res_orphan_elimination:                 0
% 1.25/1.03  res_tautology_del:                      14
% 1.25/1.03  res_num_eq_res_simplified:              0
% 1.25/1.03  res_num_sel_changes:                    0
% 1.25/1.03  res_moves_from_active_to_pass:          0
% 1.25/1.03  
% 1.25/1.03  ------ Superposition
% 1.25/1.03  
% 1.25/1.03  sup_time_total:                         0.
% 1.25/1.03  sup_time_generating:                    0.
% 1.25/1.03  sup_time_sim_full:                      0.
% 1.25/1.03  sup_time_sim_immed:                     0.
% 1.25/1.03  
% 1.25/1.03  sup_num_of_clauses:                     38
% 1.25/1.03  sup_num_in_active:                      23
% 1.25/1.03  sup_num_in_passive:                     15
% 1.25/1.03  sup_num_of_loops:                       44
% 1.25/1.03  sup_fw_superposition:                   20
% 1.25/1.03  sup_bw_superposition:                   17
% 1.25/1.03  sup_immediate_simplified:               19
% 1.25/1.03  sup_given_eliminated:                   0
% 1.25/1.03  comparisons_done:                       0
% 1.25/1.03  comparisons_avoided:                    3
% 1.25/1.03  
% 1.25/1.03  ------ Simplifications
% 1.25/1.03  
% 1.25/1.03  
% 1.25/1.03  sim_fw_subset_subsumed:                 3
% 1.25/1.03  sim_bw_subset_subsumed:                 6
% 1.25/1.03  sim_fw_subsumed:                        9
% 1.25/1.03  sim_bw_subsumed:                        3
% 1.25/1.03  sim_fw_subsumption_res:                 0
% 1.25/1.03  sim_bw_subsumption_res:                 0
% 1.25/1.03  sim_tautology_del:                      1
% 1.25/1.03  sim_eq_tautology_del:                   4
% 1.25/1.03  sim_eq_res_simp:                        0
% 1.25/1.03  sim_fw_demodulated:                     4
% 1.25/1.03  sim_bw_demodulated:                     19
% 1.25/1.03  sim_light_normalised:                   4
% 1.25/1.03  sim_joinable_taut:                      0
% 1.25/1.03  sim_joinable_simp:                      0
% 1.25/1.03  sim_ac_normalised:                      0
% 1.25/1.03  sim_smt_subsumption:                    0
% 1.25/1.03  
%------------------------------------------------------------------------------
