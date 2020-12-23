%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:48 EST 2020

% Result     : Theorem 2.95s
% Output     : CNFRefutation 2.95s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 678 expanded)
%              Number of clauses        :   89 ( 195 expanded)
%              Number of leaves         :   23 ( 152 expanded)
%              Depth                    :   23
%              Number of atoms          :  449 (2080 expanded)
%              Number of equality atoms :  176 ( 649 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | k1_xboole_0 != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_funct_1(X0,X1)
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f40,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f41,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f41,f52])).

fof(f82,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f53])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f84,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) ),
    inference(cnf_transformation,[],[f53])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f87,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f88,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f54,f87])).

fof(f91,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) ),
    inference(definition_unfolding,[],[f84,f88])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k2_relat_1(X1))
          & r2_hidden(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f46,plain,(
    ! [X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
     => r2_hidden(sK1(X1),k2_relat_1(X1)) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X1),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f46])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X1),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f64,f88])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k1_xboole_0 = k11_relat_1(X1,X0) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X1))
      | k1_xboole_0 = k11_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f86,plain,(
    ~ r2_hidden(k1_funct_1(sK5,sK3),sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f42])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f93,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f60])).

fof(f6,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f44])).

fof(f62,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f38])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f83,plain,(
    v1_funct_2(sK5,k1_tarski(sK3),sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f92,plain,(
    v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(definition_unfolding,[],[f83,f88])).

fof(f85,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f53])).

fof(f4,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f89,plain,(
    ! [X0] : ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(definition_unfolding,[],[f57,f88])).

cnf(c_13,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_428,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,X0) = k1_xboole_0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_29])).

cnf(c_429,plain,
    ( r2_hidden(X0,k1_relat_1(sK5))
    | ~ v1_relat_1(sK5)
    | k1_funct_1(sK5,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_428])).

cnf(c_1607,plain,
    ( k1_funct_1(sK5,X0) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_429])).

cnf(c_430,plain,
    ( k1_funct_1(sK5,X0) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_429])).

cnf(c_1224,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1786,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_1224])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_521,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_27])).

cnf(c_522,plain,
    ( v1_relat_1(sK5)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_521])).

cnf(c_1788,plain,
    ( v1_relat_1(sK5)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_522])).

cnf(c_1789,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1788])).

cnf(c_2093,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) = iProver_top
    | k1_funct_1(sK5,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1607,c_430,c_1786,c_1789])).

cnf(c_2094,plain,
    ( k1_funct_1(sK5,X0) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2093])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(sK1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1617,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(sK1(X1),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3156,plain,
    ( k1_funct_1(sK5,X0) = k1_xboole_0
    | r2_hidden(sK1(sK5),k2_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2094,c_1617])).

cnf(c_20,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_12,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_311,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_20,c_12])).

cnf(c_315,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_311,c_20,c_18,c_12])).

cnf(c_512,plain,
    ( k7_relat_1(X0,X1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_315,c_27])).

cnf(c_513,plain,
    ( k7_relat_1(sK5,X0) = sK5
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_512])).

cnf(c_1805,plain,
    ( k7_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3)) = sK5 ),
    inference(equality_resolution,[status(thm)],[c_513])).

cnf(c_1602,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_522])).

cnf(c_1813,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1602,c_1786,c_1789])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1618,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2639,plain,
    ( k2_relat_1(k7_relat_1(sK5,X0)) = k9_relat_1(sK5,X0) ),
    inference(superposition,[status(thm)],[c_1813,c_1618])).

cnf(c_2817,plain,
    ( k9_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3)) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1805,c_2639])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1619,plain,
    ( k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2691,plain,
    ( k9_relat_1(sK5,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK5,X0) ),
    inference(superposition,[status(thm)],[c_1813,c_1619])).

cnf(c_2867,plain,
    ( k11_relat_1(sK5,sK3) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_2817,c_2691])).

cnf(c_10,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k11_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1616,plain,
    ( k11_relat_1(X0,X1) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_19,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_17,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X2),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_331,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_19,c_17])).

cnf(c_335,plain,
    ( ~ v1_funct_1(X0)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_331,c_18])).

cnf(c_336,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_335])).

cnf(c_380,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_336,c_29])).

cnf(c_381,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r2_hidden(X2,k1_relat_1(sK5))
    | r2_hidden(k1_funct_1(sK5,X2),X1) ),
    inference(unflattening,[status(thm)],[c_380])).

cnf(c_533,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | r2_hidden(k1_funct_1(sK5,X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X2,X1))
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_381])).

cnf(c_859,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | r2_hidden(k1_funct_1(sK5,X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X2,X1)) ),
    inference(equality_resolution_simp,[status(thm)],[c_533])).

cnf(c_1601,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | r2_hidden(X2,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_859])).

cnf(c_1900,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),sK4) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1601])).

cnf(c_25,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(sK5,sK3),sK4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1611,plain,
    ( r2_hidden(k1_funct_1(sK5,sK3),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2263,plain,
    ( r2_hidden(sK3,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1900,c_1611])).

cnf(c_2697,plain,
    ( k11_relat_1(sK5,sK3) = k1_xboole_0
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1616,c_2263])).

cnf(c_2982,plain,
    ( k11_relat_1(sK5,sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2697,c_1786,c_1789])).

cnf(c_2985,plain,
    ( k2_relat_1(sK5) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2867,c_2982])).

cnf(c_3167,plain,
    ( k1_funct_1(sK5,X0) = k1_xboole_0
    | r2_hidden(sK1(sK5),k1_xboole_0) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3156,c_2985])).

cnf(c_3288,plain,
    ( r2_hidden(sK1(sK5),k1_xboole_0) = iProver_top
    | k1_funct_1(sK5,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3167,c_1786,c_1789])).

cnf(c_3289,plain,
    ( k1_funct_1(sK5,X0) = k1_xboole_0
    | r2_hidden(sK1(sK5),k1_xboole_0) = iProver_top ),
    inference(renaming,[status(thm)],[c_3288])).

cnf(c_1,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1620,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2287,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_1620])).

cnf(c_3296,plain,
    ( k1_funct_1(sK5,X0) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3289,c_2287])).

cnf(c_5,plain,
    ( m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_460,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | X1 != X2
    | sK0(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_6])).

cnf(c_461,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_460])).

cnf(c_1606,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_461])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_359,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k2_enumset1(sK3,sK3,sK3,sK3) != X1
    | sK4 != X2
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_28])).

cnf(c_360,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
    | ~ r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3))
    | r2_hidden(k1_funct_1(sK5,X0),sK4)
    | ~ v1_funct_1(sK5)
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_359])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_364,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3))
    | r2_hidden(k1_funct_1(sK5,X0),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_360,c_29,c_27,c_26])).

cnf(c_1610,plain,
    ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_364])).

cnf(c_2283,plain,
    ( r2_hidden(k1_funct_1(sK5,sK0(k2_enumset1(sK3,sK3,sK3,sK3))),sK4) = iProver_top
    | v1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1606,c_1610])).

cnf(c_1794,plain,
    ( r2_hidden(sK0(k2_enumset1(X0,X0,X0,X0)),k2_enumset1(X0,X0,X0,X0))
    | v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(instantiation,[status(thm)],[c_461])).

cnf(c_2254,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
    | v1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_1794])).

cnf(c_2256,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top
    | v1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2254])).

cnf(c_2255,plain,
    ( r2_hidden(k1_funct_1(sK5,sK0(k2_enumset1(sK3,sK3,sK3,sK3))),sK4)
    | ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_364])).

cnf(c_2258,plain,
    ( r2_hidden(k1_funct_1(sK5,sK0(k2_enumset1(sK3,sK3,sK3,sK3))),sK4) = iProver_top
    | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2255])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2268,plain,
    ( ~ v1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2269,plain,
    ( v1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2268])).

cnf(c_2481,plain,
    ( r2_hidden(k1_funct_1(sK5,sK0(k2_enumset1(sK3,sK3,sK3,sK3))),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2283,c_2256,c_2258,c_2269])).

cnf(c_3305,plain,
    ( r2_hidden(k1_xboole_0,sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3296,c_2481])).

cnf(c_2267,plain,
    ( k1_funct_1(sK5,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2094,c_2263])).

cnf(c_2380,plain,
    ( r2_hidden(k1_xboole_0,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2267,c_1611])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3305,c_2380])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:38:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.95/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.02  
% 2.95/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.95/1.02  
% 2.95/1.02  ------  iProver source info
% 2.95/1.02  
% 2.95/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.95/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.95/1.02  git: non_committed_changes: false
% 2.95/1.02  git: last_make_outside_of_git: false
% 2.95/1.02  
% 2.95/1.02  ------ 
% 2.95/1.02  
% 2.95/1.02  ------ Input Options
% 2.95/1.02  
% 2.95/1.02  --out_options                           all
% 2.95/1.02  --tptp_safe_out                         true
% 2.95/1.02  --problem_path                          ""
% 2.95/1.02  --include_path                          ""
% 2.95/1.02  --clausifier                            res/vclausify_rel
% 2.95/1.02  --clausifier_options                    --mode clausify
% 2.95/1.02  --stdin                                 false
% 2.95/1.02  --stats_out                             all
% 2.95/1.02  
% 2.95/1.02  ------ General Options
% 2.95/1.02  
% 2.95/1.02  --fof                                   false
% 2.95/1.02  --time_out_real                         305.
% 2.95/1.02  --time_out_virtual                      -1.
% 2.95/1.02  --symbol_type_check                     false
% 2.95/1.02  --clausify_out                          false
% 2.95/1.02  --sig_cnt_out                           false
% 2.95/1.02  --trig_cnt_out                          false
% 2.95/1.02  --trig_cnt_out_tolerance                1.
% 2.95/1.02  --trig_cnt_out_sk_spl                   false
% 2.95/1.02  --abstr_cl_out                          false
% 2.95/1.02  
% 2.95/1.02  ------ Global Options
% 2.95/1.02  
% 2.95/1.02  --schedule                              default
% 2.95/1.02  --add_important_lit                     false
% 2.95/1.02  --prop_solver_per_cl                    1000
% 2.95/1.02  --min_unsat_core                        false
% 2.95/1.02  --soft_assumptions                      false
% 2.95/1.02  --soft_lemma_size                       3
% 2.95/1.02  --prop_impl_unit_size                   0
% 2.95/1.02  --prop_impl_unit                        []
% 2.95/1.02  --share_sel_clauses                     true
% 2.95/1.02  --reset_solvers                         false
% 2.95/1.02  --bc_imp_inh                            [conj_cone]
% 2.95/1.02  --conj_cone_tolerance                   3.
% 2.95/1.02  --extra_neg_conj                        none
% 2.95/1.02  --large_theory_mode                     true
% 2.95/1.02  --prolific_symb_bound                   200
% 2.95/1.02  --lt_threshold                          2000
% 2.95/1.02  --clause_weak_htbl                      true
% 2.95/1.02  --gc_record_bc_elim                     false
% 2.95/1.02  
% 2.95/1.02  ------ Preprocessing Options
% 2.95/1.02  
% 2.95/1.02  --preprocessing_flag                    true
% 2.95/1.02  --time_out_prep_mult                    0.1
% 2.95/1.02  --splitting_mode                        input
% 2.95/1.02  --splitting_grd                         true
% 2.95/1.02  --splitting_cvd                         false
% 2.95/1.02  --splitting_cvd_svl                     false
% 2.95/1.02  --splitting_nvd                         32
% 2.95/1.02  --sub_typing                            true
% 2.95/1.02  --prep_gs_sim                           true
% 2.95/1.02  --prep_unflatten                        true
% 2.95/1.02  --prep_res_sim                          true
% 2.95/1.02  --prep_upred                            true
% 2.95/1.02  --prep_sem_filter                       exhaustive
% 2.95/1.02  --prep_sem_filter_out                   false
% 2.95/1.02  --pred_elim                             true
% 2.95/1.02  --res_sim_input                         true
% 2.95/1.02  --eq_ax_congr_red                       true
% 2.95/1.02  --pure_diseq_elim                       true
% 2.95/1.02  --brand_transform                       false
% 2.95/1.02  --non_eq_to_eq                          false
% 2.95/1.02  --prep_def_merge                        true
% 2.95/1.02  --prep_def_merge_prop_impl              false
% 2.95/1.02  --prep_def_merge_mbd                    true
% 2.95/1.02  --prep_def_merge_tr_red                 false
% 2.95/1.02  --prep_def_merge_tr_cl                  false
% 2.95/1.02  --smt_preprocessing                     true
% 2.95/1.02  --smt_ac_axioms                         fast
% 2.95/1.02  --preprocessed_out                      false
% 2.95/1.02  --preprocessed_stats                    false
% 2.95/1.02  
% 2.95/1.02  ------ Abstraction refinement Options
% 2.95/1.02  
% 2.95/1.02  --abstr_ref                             []
% 2.95/1.02  --abstr_ref_prep                        false
% 2.95/1.02  --abstr_ref_until_sat                   false
% 2.95/1.02  --abstr_ref_sig_restrict                funpre
% 2.95/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.95/1.02  --abstr_ref_under                       []
% 2.95/1.02  
% 2.95/1.02  ------ SAT Options
% 2.95/1.02  
% 2.95/1.02  --sat_mode                              false
% 2.95/1.02  --sat_fm_restart_options                ""
% 2.95/1.02  --sat_gr_def                            false
% 2.95/1.02  --sat_epr_types                         true
% 2.95/1.02  --sat_non_cyclic_types                  false
% 2.95/1.02  --sat_finite_models                     false
% 2.95/1.02  --sat_fm_lemmas                         false
% 2.95/1.02  --sat_fm_prep                           false
% 2.95/1.02  --sat_fm_uc_incr                        true
% 2.95/1.02  --sat_out_model                         small
% 2.95/1.02  --sat_out_clauses                       false
% 2.95/1.02  
% 2.95/1.02  ------ QBF Options
% 2.95/1.02  
% 2.95/1.02  --qbf_mode                              false
% 2.95/1.02  --qbf_elim_univ                         false
% 2.95/1.02  --qbf_dom_inst                          none
% 2.95/1.02  --qbf_dom_pre_inst                      false
% 2.95/1.02  --qbf_sk_in                             false
% 2.95/1.02  --qbf_pred_elim                         true
% 2.95/1.02  --qbf_split                             512
% 2.95/1.02  
% 2.95/1.02  ------ BMC1 Options
% 2.95/1.02  
% 2.95/1.02  --bmc1_incremental                      false
% 2.95/1.02  --bmc1_axioms                           reachable_all
% 2.95/1.02  --bmc1_min_bound                        0
% 2.95/1.02  --bmc1_max_bound                        -1
% 2.95/1.02  --bmc1_max_bound_default                -1
% 2.95/1.02  --bmc1_symbol_reachability              true
% 2.95/1.02  --bmc1_property_lemmas                  false
% 2.95/1.02  --bmc1_k_induction                      false
% 2.95/1.02  --bmc1_non_equiv_states                 false
% 2.95/1.02  --bmc1_deadlock                         false
% 2.95/1.02  --bmc1_ucm                              false
% 2.95/1.02  --bmc1_add_unsat_core                   none
% 2.95/1.02  --bmc1_unsat_core_children              false
% 2.95/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.95/1.02  --bmc1_out_stat                         full
% 2.95/1.02  --bmc1_ground_init                      false
% 2.95/1.02  --bmc1_pre_inst_next_state              false
% 2.95/1.02  --bmc1_pre_inst_state                   false
% 2.95/1.02  --bmc1_pre_inst_reach_state             false
% 2.95/1.02  --bmc1_out_unsat_core                   false
% 2.95/1.02  --bmc1_aig_witness_out                  false
% 2.95/1.02  --bmc1_verbose                          false
% 2.95/1.02  --bmc1_dump_clauses_tptp                false
% 2.95/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.95/1.02  --bmc1_dump_file                        -
% 2.95/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.95/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.95/1.02  --bmc1_ucm_extend_mode                  1
% 2.95/1.02  --bmc1_ucm_init_mode                    2
% 2.95/1.02  --bmc1_ucm_cone_mode                    none
% 2.95/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.95/1.02  --bmc1_ucm_relax_model                  4
% 2.95/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.95/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.95/1.02  --bmc1_ucm_layered_model                none
% 2.95/1.02  --bmc1_ucm_max_lemma_size               10
% 2.95/1.02  
% 2.95/1.02  ------ AIG Options
% 2.95/1.02  
% 2.95/1.02  --aig_mode                              false
% 2.95/1.02  
% 2.95/1.02  ------ Instantiation Options
% 2.95/1.02  
% 2.95/1.02  --instantiation_flag                    true
% 2.95/1.02  --inst_sos_flag                         false
% 2.95/1.02  --inst_sos_phase                        true
% 2.95/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.95/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.95/1.02  --inst_lit_sel_side                     num_symb
% 2.95/1.02  --inst_solver_per_active                1400
% 2.95/1.02  --inst_solver_calls_frac                1.
% 2.95/1.02  --inst_passive_queue_type               priority_queues
% 2.95/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.95/1.02  --inst_passive_queues_freq              [25;2]
% 2.95/1.02  --inst_dismatching                      true
% 2.95/1.02  --inst_eager_unprocessed_to_passive     true
% 2.95/1.02  --inst_prop_sim_given                   true
% 2.95/1.02  --inst_prop_sim_new                     false
% 2.95/1.02  --inst_subs_new                         false
% 2.95/1.02  --inst_eq_res_simp                      false
% 2.95/1.02  --inst_subs_given                       false
% 2.95/1.02  --inst_orphan_elimination               true
% 2.95/1.02  --inst_learning_loop_flag               true
% 2.95/1.02  --inst_learning_start                   3000
% 2.95/1.02  --inst_learning_factor                  2
% 2.95/1.02  --inst_start_prop_sim_after_learn       3
% 2.95/1.02  --inst_sel_renew                        solver
% 2.95/1.02  --inst_lit_activity_flag                true
% 2.95/1.02  --inst_restr_to_given                   false
% 2.95/1.02  --inst_activity_threshold               500
% 2.95/1.02  --inst_out_proof                        true
% 2.95/1.02  
% 2.95/1.02  ------ Resolution Options
% 2.95/1.02  
% 2.95/1.02  --resolution_flag                       true
% 2.95/1.02  --res_lit_sel                           adaptive
% 2.95/1.02  --res_lit_sel_side                      none
% 2.95/1.02  --res_ordering                          kbo
% 2.95/1.02  --res_to_prop_solver                    active
% 2.95/1.02  --res_prop_simpl_new                    false
% 2.95/1.02  --res_prop_simpl_given                  true
% 2.95/1.02  --res_passive_queue_type                priority_queues
% 2.95/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.95/1.02  --res_passive_queues_freq               [15;5]
% 2.95/1.02  --res_forward_subs                      full
% 2.95/1.02  --res_backward_subs                     full
% 2.95/1.02  --res_forward_subs_resolution           true
% 2.95/1.02  --res_backward_subs_resolution          true
% 2.95/1.02  --res_orphan_elimination                true
% 2.95/1.02  --res_time_limit                        2.
% 2.95/1.02  --res_out_proof                         true
% 2.95/1.02  
% 2.95/1.02  ------ Superposition Options
% 2.95/1.02  
% 2.95/1.02  --superposition_flag                    true
% 2.95/1.02  --sup_passive_queue_type                priority_queues
% 2.95/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.95/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.95/1.02  --demod_completeness_check              fast
% 2.95/1.02  --demod_use_ground                      true
% 2.95/1.02  --sup_to_prop_solver                    passive
% 2.95/1.02  --sup_prop_simpl_new                    true
% 2.95/1.02  --sup_prop_simpl_given                  true
% 2.95/1.02  --sup_fun_splitting                     false
% 2.95/1.02  --sup_smt_interval                      50000
% 2.95/1.02  
% 2.95/1.02  ------ Superposition Simplification Setup
% 2.95/1.02  
% 2.95/1.02  --sup_indices_passive                   []
% 2.95/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.95/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.95/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.95/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.95/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.95/1.02  --sup_full_bw                           [BwDemod]
% 2.95/1.02  --sup_immed_triv                        [TrivRules]
% 2.95/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.95/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.95/1.02  --sup_immed_bw_main                     []
% 2.95/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.95/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.95/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.95/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.95/1.02  
% 2.95/1.02  ------ Combination Options
% 2.95/1.02  
% 2.95/1.02  --comb_res_mult                         3
% 2.95/1.02  --comb_sup_mult                         2
% 2.95/1.02  --comb_inst_mult                        10
% 2.95/1.02  
% 2.95/1.02  ------ Debug Options
% 2.95/1.02  
% 2.95/1.02  --dbg_backtrace                         false
% 2.95/1.02  --dbg_dump_prop_clauses                 false
% 2.95/1.02  --dbg_dump_prop_clauses_file            -
% 2.95/1.02  --dbg_out_stat                          false
% 2.95/1.02  ------ Parsing...
% 2.95/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.95/1.02  
% 2.95/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.95/1.02  
% 2.95/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.95/1.02  
% 2.95/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.95/1.02  ------ Proving...
% 2.95/1.02  ------ Problem Properties 
% 2.95/1.02  
% 2.95/1.02  
% 2.95/1.02  clauses                                 27
% 2.95/1.02  conjectures                             2
% 2.95/1.02  EPR                                     1
% 2.95/1.02  Horn                                    21
% 2.95/1.02  unary                                   8
% 2.95/1.02  binary                                  8
% 2.95/1.02  lits                                    58
% 2.95/1.02  lits eq                                 23
% 2.95/1.02  fd_pure                                 0
% 2.95/1.02  fd_pseudo                               0
% 2.95/1.02  fd_cond                                 4
% 2.95/1.02  fd_pseudo_cond                          1
% 2.95/1.02  AC symbols                              0
% 2.95/1.02  
% 2.95/1.02  ------ Schedule dynamic 5 is on 
% 2.95/1.02  
% 2.95/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.95/1.02  
% 2.95/1.02  
% 2.95/1.02  ------ 
% 2.95/1.02  Current options:
% 2.95/1.02  ------ 
% 2.95/1.02  
% 2.95/1.02  ------ Input Options
% 2.95/1.02  
% 2.95/1.02  --out_options                           all
% 2.95/1.02  --tptp_safe_out                         true
% 2.95/1.02  --problem_path                          ""
% 2.95/1.02  --include_path                          ""
% 2.95/1.02  --clausifier                            res/vclausify_rel
% 2.95/1.02  --clausifier_options                    --mode clausify
% 2.95/1.02  --stdin                                 false
% 2.95/1.02  --stats_out                             all
% 2.95/1.02  
% 2.95/1.02  ------ General Options
% 2.95/1.02  
% 2.95/1.02  --fof                                   false
% 2.95/1.02  --time_out_real                         305.
% 2.95/1.02  --time_out_virtual                      -1.
% 2.95/1.02  --symbol_type_check                     false
% 2.95/1.02  --clausify_out                          false
% 2.95/1.02  --sig_cnt_out                           false
% 2.95/1.02  --trig_cnt_out                          false
% 2.95/1.02  --trig_cnt_out_tolerance                1.
% 2.95/1.02  --trig_cnt_out_sk_spl                   false
% 2.95/1.02  --abstr_cl_out                          false
% 2.95/1.02  
% 2.95/1.02  ------ Global Options
% 2.95/1.02  
% 2.95/1.02  --schedule                              default
% 2.95/1.02  --add_important_lit                     false
% 2.95/1.02  --prop_solver_per_cl                    1000
% 2.95/1.02  --min_unsat_core                        false
% 2.95/1.02  --soft_assumptions                      false
% 2.95/1.02  --soft_lemma_size                       3
% 2.95/1.02  --prop_impl_unit_size                   0
% 2.95/1.02  --prop_impl_unit                        []
% 2.95/1.02  --share_sel_clauses                     true
% 2.95/1.02  --reset_solvers                         false
% 2.95/1.02  --bc_imp_inh                            [conj_cone]
% 2.95/1.02  --conj_cone_tolerance                   3.
% 2.95/1.02  --extra_neg_conj                        none
% 2.95/1.02  --large_theory_mode                     true
% 2.95/1.02  --prolific_symb_bound                   200
% 2.95/1.02  --lt_threshold                          2000
% 2.95/1.02  --clause_weak_htbl                      true
% 2.95/1.02  --gc_record_bc_elim                     false
% 2.95/1.02  
% 2.95/1.02  ------ Preprocessing Options
% 2.95/1.02  
% 2.95/1.02  --preprocessing_flag                    true
% 2.95/1.02  --time_out_prep_mult                    0.1
% 2.95/1.02  --splitting_mode                        input
% 2.95/1.02  --splitting_grd                         true
% 2.95/1.02  --splitting_cvd                         false
% 2.95/1.02  --splitting_cvd_svl                     false
% 2.95/1.02  --splitting_nvd                         32
% 2.95/1.02  --sub_typing                            true
% 2.95/1.02  --prep_gs_sim                           true
% 2.95/1.02  --prep_unflatten                        true
% 2.95/1.02  --prep_res_sim                          true
% 2.95/1.02  --prep_upred                            true
% 2.95/1.02  --prep_sem_filter                       exhaustive
% 2.95/1.02  --prep_sem_filter_out                   false
% 2.95/1.02  --pred_elim                             true
% 2.95/1.02  --res_sim_input                         true
% 2.95/1.02  --eq_ax_congr_red                       true
% 2.95/1.02  --pure_diseq_elim                       true
% 2.95/1.02  --brand_transform                       false
% 2.95/1.02  --non_eq_to_eq                          false
% 2.95/1.02  --prep_def_merge                        true
% 2.95/1.02  --prep_def_merge_prop_impl              false
% 2.95/1.02  --prep_def_merge_mbd                    true
% 2.95/1.02  --prep_def_merge_tr_red                 false
% 2.95/1.02  --prep_def_merge_tr_cl                  false
% 2.95/1.02  --smt_preprocessing                     true
% 2.95/1.02  --smt_ac_axioms                         fast
% 2.95/1.02  --preprocessed_out                      false
% 2.95/1.02  --preprocessed_stats                    false
% 2.95/1.02  
% 2.95/1.02  ------ Abstraction refinement Options
% 2.95/1.02  
% 2.95/1.02  --abstr_ref                             []
% 2.95/1.02  --abstr_ref_prep                        false
% 2.95/1.02  --abstr_ref_until_sat                   false
% 2.95/1.02  --abstr_ref_sig_restrict                funpre
% 2.95/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.95/1.02  --abstr_ref_under                       []
% 2.95/1.02  
% 2.95/1.02  ------ SAT Options
% 2.95/1.02  
% 2.95/1.02  --sat_mode                              false
% 2.95/1.02  --sat_fm_restart_options                ""
% 2.95/1.02  --sat_gr_def                            false
% 2.95/1.02  --sat_epr_types                         true
% 2.95/1.02  --sat_non_cyclic_types                  false
% 2.95/1.02  --sat_finite_models                     false
% 2.95/1.02  --sat_fm_lemmas                         false
% 2.95/1.02  --sat_fm_prep                           false
% 2.95/1.02  --sat_fm_uc_incr                        true
% 2.95/1.02  --sat_out_model                         small
% 2.95/1.02  --sat_out_clauses                       false
% 2.95/1.02  
% 2.95/1.02  ------ QBF Options
% 2.95/1.02  
% 2.95/1.02  --qbf_mode                              false
% 2.95/1.02  --qbf_elim_univ                         false
% 2.95/1.02  --qbf_dom_inst                          none
% 2.95/1.02  --qbf_dom_pre_inst                      false
% 2.95/1.02  --qbf_sk_in                             false
% 2.95/1.02  --qbf_pred_elim                         true
% 2.95/1.02  --qbf_split                             512
% 2.95/1.02  
% 2.95/1.02  ------ BMC1 Options
% 2.95/1.02  
% 2.95/1.02  --bmc1_incremental                      false
% 2.95/1.02  --bmc1_axioms                           reachable_all
% 2.95/1.02  --bmc1_min_bound                        0
% 2.95/1.02  --bmc1_max_bound                        -1
% 2.95/1.02  --bmc1_max_bound_default                -1
% 2.95/1.02  --bmc1_symbol_reachability              true
% 2.95/1.02  --bmc1_property_lemmas                  false
% 2.95/1.02  --bmc1_k_induction                      false
% 2.95/1.02  --bmc1_non_equiv_states                 false
% 2.95/1.02  --bmc1_deadlock                         false
% 2.95/1.02  --bmc1_ucm                              false
% 2.95/1.02  --bmc1_add_unsat_core                   none
% 2.95/1.02  --bmc1_unsat_core_children              false
% 2.95/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.95/1.02  --bmc1_out_stat                         full
% 2.95/1.02  --bmc1_ground_init                      false
% 2.95/1.02  --bmc1_pre_inst_next_state              false
% 2.95/1.02  --bmc1_pre_inst_state                   false
% 2.95/1.02  --bmc1_pre_inst_reach_state             false
% 2.95/1.02  --bmc1_out_unsat_core                   false
% 2.95/1.02  --bmc1_aig_witness_out                  false
% 2.95/1.02  --bmc1_verbose                          false
% 2.95/1.02  --bmc1_dump_clauses_tptp                false
% 2.95/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.95/1.02  --bmc1_dump_file                        -
% 2.95/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.95/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.95/1.02  --bmc1_ucm_extend_mode                  1
% 2.95/1.02  --bmc1_ucm_init_mode                    2
% 2.95/1.02  --bmc1_ucm_cone_mode                    none
% 2.95/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.95/1.02  --bmc1_ucm_relax_model                  4
% 2.95/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.95/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.95/1.02  --bmc1_ucm_layered_model                none
% 2.95/1.02  --bmc1_ucm_max_lemma_size               10
% 2.95/1.02  
% 2.95/1.02  ------ AIG Options
% 2.95/1.02  
% 2.95/1.02  --aig_mode                              false
% 2.95/1.02  
% 2.95/1.02  ------ Instantiation Options
% 2.95/1.02  
% 2.95/1.02  --instantiation_flag                    true
% 2.95/1.02  --inst_sos_flag                         false
% 2.95/1.02  --inst_sos_phase                        true
% 2.95/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.95/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.95/1.02  --inst_lit_sel_side                     none
% 2.95/1.02  --inst_solver_per_active                1400
% 2.95/1.02  --inst_solver_calls_frac                1.
% 2.95/1.02  --inst_passive_queue_type               priority_queues
% 2.95/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.95/1.02  --inst_passive_queues_freq              [25;2]
% 2.95/1.02  --inst_dismatching                      true
% 2.95/1.02  --inst_eager_unprocessed_to_passive     true
% 2.95/1.02  --inst_prop_sim_given                   true
% 2.95/1.02  --inst_prop_sim_new                     false
% 2.95/1.02  --inst_subs_new                         false
% 2.95/1.02  --inst_eq_res_simp                      false
% 2.95/1.02  --inst_subs_given                       false
% 2.95/1.02  --inst_orphan_elimination               true
% 2.95/1.02  --inst_learning_loop_flag               true
% 2.95/1.02  --inst_learning_start                   3000
% 2.95/1.02  --inst_learning_factor                  2
% 2.95/1.02  --inst_start_prop_sim_after_learn       3
% 2.95/1.02  --inst_sel_renew                        solver
% 2.95/1.02  --inst_lit_activity_flag                true
% 2.95/1.02  --inst_restr_to_given                   false
% 2.95/1.02  --inst_activity_threshold               500
% 2.95/1.02  --inst_out_proof                        true
% 2.95/1.02  
% 2.95/1.02  ------ Resolution Options
% 2.95/1.02  
% 2.95/1.02  --resolution_flag                       false
% 2.95/1.02  --res_lit_sel                           adaptive
% 2.95/1.02  --res_lit_sel_side                      none
% 2.95/1.02  --res_ordering                          kbo
% 2.95/1.02  --res_to_prop_solver                    active
% 2.95/1.02  --res_prop_simpl_new                    false
% 2.95/1.02  --res_prop_simpl_given                  true
% 2.95/1.02  --res_passive_queue_type                priority_queues
% 2.95/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.95/1.02  --res_passive_queues_freq               [15;5]
% 2.95/1.02  --res_forward_subs                      full
% 2.95/1.02  --res_backward_subs                     full
% 2.95/1.02  --res_forward_subs_resolution           true
% 2.95/1.02  --res_backward_subs_resolution          true
% 2.95/1.02  --res_orphan_elimination                true
% 2.95/1.02  --res_time_limit                        2.
% 2.95/1.02  --res_out_proof                         true
% 2.95/1.02  
% 2.95/1.02  ------ Superposition Options
% 2.95/1.02  
% 2.95/1.02  --superposition_flag                    true
% 2.95/1.02  --sup_passive_queue_type                priority_queues
% 2.95/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.95/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.95/1.02  --demod_completeness_check              fast
% 2.95/1.02  --demod_use_ground                      true
% 2.95/1.02  --sup_to_prop_solver                    passive
% 2.95/1.02  --sup_prop_simpl_new                    true
% 2.95/1.02  --sup_prop_simpl_given                  true
% 2.95/1.02  --sup_fun_splitting                     false
% 2.95/1.02  --sup_smt_interval                      50000
% 2.95/1.02  
% 2.95/1.02  ------ Superposition Simplification Setup
% 2.95/1.02  
% 2.95/1.02  --sup_indices_passive                   []
% 2.95/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.95/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.95/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.95/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.95/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.95/1.02  --sup_full_bw                           [BwDemod]
% 2.95/1.02  --sup_immed_triv                        [TrivRules]
% 2.95/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.95/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.95/1.02  --sup_immed_bw_main                     []
% 2.95/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.95/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.95/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.95/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.95/1.02  
% 2.95/1.02  ------ Combination Options
% 2.95/1.02  
% 2.95/1.02  --comb_res_mult                         3
% 2.95/1.02  --comb_sup_mult                         2
% 2.95/1.02  --comb_inst_mult                        10
% 2.95/1.02  
% 2.95/1.02  ------ Debug Options
% 2.95/1.02  
% 2.95/1.02  --dbg_backtrace                         false
% 2.95/1.02  --dbg_dump_prop_clauses                 false
% 2.95/1.02  --dbg_dump_prop_clauses_file            -
% 2.95/1.02  --dbg_out_stat                          false
% 2.95/1.02  
% 2.95/1.02  
% 2.95/1.02  
% 2.95/1.02  
% 2.95/1.02  ------ Proving...
% 2.95/1.02  
% 2.95/1.02  
% 2.95/1.02  % SZS status Theorem for theBenchmark.p
% 2.95/1.02  
% 2.95/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.95/1.02  
% 2.95/1.02  fof(f14,axiom,(
% 2.95/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 2.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.02  
% 2.95/1.02  fof(f31,plain,(
% 2.95/1.02    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.95/1.02    inference(ennf_transformation,[],[f14])).
% 2.95/1.02  
% 2.95/1.02  fof(f32,plain,(
% 2.95/1.02    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.95/1.02    inference(flattening,[],[f31])).
% 2.95/1.02  
% 2.95/1.02  fof(f49,plain,(
% 2.95/1.02    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.95/1.02    inference(nnf_transformation,[],[f32])).
% 2.95/1.02  
% 2.95/1.02  fof(f73,plain,(
% 2.95/1.02    ( ! [X2,X0,X1] : (k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2 | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.95/1.02    inference(cnf_transformation,[],[f49])).
% 2.95/1.02  
% 2.95/1.02  fof(f95,plain,(
% 2.95/1.02    ( ! [X0,X1] : (k1_xboole_0 = k1_funct_1(X0,X1) | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.95/1.02    inference(equality_resolution,[],[f73])).
% 2.95/1.02  
% 2.95/1.02  fof(f20,conjecture,(
% 2.95/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 2.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.02  
% 2.95/1.02  fof(f21,negated_conjecture,(
% 2.95/1.02    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 2.95/1.02    inference(negated_conjecture,[],[f20])).
% 2.95/1.02  
% 2.95/1.02  fof(f40,plain,(
% 2.95/1.02    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 2.95/1.02    inference(ennf_transformation,[],[f21])).
% 2.95/1.02  
% 2.95/1.02  fof(f41,plain,(
% 2.95/1.02    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 2.95/1.02    inference(flattening,[],[f40])).
% 2.95/1.02  
% 2.95/1.02  fof(f52,plain,(
% 2.95/1.02    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK5,sK3),sK4) & k1_xboole_0 != sK4 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) & v1_funct_2(sK5,k1_tarski(sK3),sK4) & v1_funct_1(sK5))),
% 2.95/1.02    introduced(choice_axiom,[])).
% 2.95/1.02  
% 2.95/1.02  fof(f53,plain,(
% 2.95/1.02    ~r2_hidden(k1_funct_1(sK5,sK3),sK4) & k1_xboole_0 != sK4 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) & v1_funct_2(sK5,k1_tarski(sK3),sK4) & v1_funct_1(sK5)),
% 2.95/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f41,f52])).
% 2.95/1.02  
% 2.95/1.02  fof(f82,plain,(
% 2.95/1.02    v1_funct_1(sK5)),
% 2.95/1.02    inference(cnf_transformation,[],[f53])).
% 2.95/1.02  
% 2.95/1.02  fof(f16,axiom,(
% 2.95/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.02  
% 2.95/1.02  fof(f35,plain,(
% 2.95/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.95/1.02    inference(ennf_transformation,[],[f16])).
% 2.95/1.02  
% 2.95/1.02  fof(f75,plain,(
% 2.95/1.02    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.95/1.02    inference(cnf_transformation,[],[f35])).
% 2.95/1.02  
% 2.95/1.02  fof(f84,plain,(
% 2.95/1.02    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4)))),
% 2.95/1.02    inference(cnf_transformation,[],[f53])).
% 2.95/1.02  
% 2.95/1.02  fof(f1,axiom,(
% 2.95/1.02    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.02  
% 2.95/1.02  fof(f54,plain,(
% 2.95/1.02    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.95/1.02    inference(cnf_transformation,[],[f1])).
% 2.95/1.02  
% 2.95/1.02  fof(f2,axiom,(
% 2.95/1.02    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.02  
% 2.95/1.02  fof(f55,plain,(
% 2.95/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.95/1.02    inference(cnf_transformation,[],[f2])).
% 2.95/1.02  
% 2.95/1.02  fof(f3,axiom,(
% 2.95/1.02    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.02  
% 2.95/1.02  fof(f56,plain,(
% 2.95/1.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.95/1.02    inference(cnf_transformation,[],[f3])).
% 2.95/1.02  
% 2.95/1.02  fof(f87,plain,(
% 2.95/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.95/1.02    inference(definition_unfolding,[],[f55,f56])).
% 2.95/1.02  
% 2.95/1.02  fof(f88,plain,(
% 2.95/1.02    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.95/1.02    inference(definition_unfolding,[],[f54,f87])).
% 2.95/1.02  
% 2.95/1.02  fof(f91,plain,(
% 2.95/1.02    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))),
% 2.95/1.02    inference(definition_unfolding,[],[f84,f88])).
% 2.95/1.02  
% 2.95/1.02  fof(f11,axiom,(
% 2.95/1.02    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k2_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X1))))),
% 2.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.02  
% 2.95/1.02  fof(f26,plain,(
% 2.95/1.02    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.95/1.02    inference(ennf_transformation,[],[f11])).
% 2.95/1.02  
% 2.95/1.02  fof(f27,plain,(
% 2.95/1.02    ! [X0,X1] : (? [X2] : r2_hidden(X2,k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.95/1.02    inference(flattening,[],[f26])).
% 2.95/1.02  
% 2.95/1.02  fof(f46,plain,(
% 2.95/1.02    ! [X1] : (? [X2] : r2_hidden(X2,k2_relat_1(X1)) => r2_hidden(sK1(X1),k2_relat_1(X1)))),
% 2.95/1.02    introduced(choice_axiom,[])).
% 2.95/1.02  
% 2.95/1.02  fof(f47,plain,(
% 2.95/1.02    ! [X0,X1] : (r2_hidden(sK1(X1),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.95/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f46])).
% 2.95/1.02  
% 2.95/1.02  fof(f66,plain,(
% 2.95/1.02    ( ! [X0,X1] : (r2_hidden(sK1(X1),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.95/1.02    inference(cnf_transformation,[],[f47])).
% 2.95/1.02  
% 2.95/1.02  fof(f17,axiom,(
% 2.95/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.02  
% 2.95/1.02  fof(f36,plain,(
% 2.95/1.02    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.95/1.02    inference(ennf_transformation,[],[f17])).
% 2.95/1.02  
% 2.95/1.02  fof(f76,plain,(
% 2.95/1.02    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.95/1.02    inference(cnf_transformation,[],[f36])).
% 2.95/1.02  
% 2.95/1.02  fof(f13,axiom,(
% 2.95/1.02    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.02  
% 2.95/1.02  fof(f29,plain,(
% 2.95/1.02    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.95/1.02    inference(ennf_transformation,[],[f13])).
% 2.95/1.02  
% 2.95/1.02  fof(f30,plain,(
% 2.95/1.02    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.95/1.02    inference(flattening,[],[f29])).
% 2.95/1.02  
% 2.95/1.02  fof(f69,plain,(
% 2.95/1.02    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.95/1.02    inference(cnf_transformation,[],[f30])).
% 2.95/1.02  
% 2.95/1.02  fof(f10,axiom,(
% 2.95/1.02    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 2.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.02  
% 2.95/1.02  fof(f25,plain,(
% 2.95/1.02    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 2.95/1.02    inference(ennf_transformation,[],[f10])).
% 2.95/1.02  
% 2.95/1.02  fof(f65,plain,(
% 2.95/1.02    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 2.95/1.02    inference(cnf_transformation,[],[f25])).
% 2.95/1.02  
% 2.95/1.02  fof(f9,axiom,(
% 2.95/1.02    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 2.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.02  
% 2.95/1.02  fof(f24,plain,(
% 2.95/1.02    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 2.95/1.02    inference(ennf_transformation,[],[f9])).
% 2.95/1.02  
% 2.95/1.02  fof(f64,plain,(
% 2.95/1.02    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 2.95/1.02    inference(cnf_transformation,[],[f24])).
% 2.95/1.02  
% 2.95/1.02  fof(f90,plain,(
% 2.95/1.02    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 2.95/1.02    inference(definition_unfolding,[],[f64,f88])).
% 2.95/1.02  
% 2.95/1.02  fof(f12,axiom,(
% 2.95/1.02    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 2.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.02  
% 2.95/1.02  fof(f28,plain,(
% 2.95/1.02    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 2.95/1.02    inference(ennf_transformation,[],[f12])).
% 2.95/1.02  
% 2.95/1.02  fof(f48,plain,(
% 2.95/1.02    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 2.95/1.02    inference(nnf_transformation,[],[f28])).
% 2.95/1.02  
% 2.95/1.02  fof(f68,plain,(
% 2.95/1.02    ( ! [X0,X1] : (r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.95/1.02    inference(cnf_transformation,[],[f48])).
% 2.95/1.02  
% 2.95/1.02  fof(f77,plain,(
% 2.95/1.02    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.95/1.02    inference(cnf_transformation,[],[f36])).
% 2.95/1.02  
% 2.95/1.02  fof(f15,axiom,(
% 2.95/1.02    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 2.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.02  
% 2.95/1.02  fof(f33,plain,(
% 2.95/1.02    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.95/1.02    inference(ennf_transformation,[],[f15])).
% 2.95/1.02  
% 2.95/1.02  fof(f34,plain,(
% 2.95/1.02    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.95/1.02    inference(flattening,[],[f33])).
% 2.95/1.02  
% 2.95/1.02  fof(f74,plain,(
% 2.95/1.02    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.95/1.02    inference(cnf_transformation,[],[f34])).
% 2.95/1.02  
% 2.95/1.02  fof(f86,plain,(
% 2.95/1.02    ~r2_hidden(k1_funct_1(sK5,sK3),sK4)),
% 2.95/1.02    inference(cnf_transformation,[],[f53])).
% 2.95/1.02  
% 2.95/1.02  fof(f5,axiom,(
% 2.95/1.02    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.02  
% 2.95/1.02  fof(f42,plain,(
% 2.95/1.02    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.95/1.02    inference(nnf_transformation,[],[f5])).
% 2.95/1.02  
% 2.95/1.02  fof(f43,plain,(
% 2.95/1.02    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.95/1.02    inference(flattening,[],[f42])).
% 2.95/1.02  
% 2.95/1.02  fof(f60,plain,(
% 2.95/1.02    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 2.95/1.02    inference(cnf_transformation,[],[f43])).
% 2.95/1.02  
% 2.95/1.02  fof(f93,plain,(
% 2.95/1.02    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 2.95/1.02    inference(equality_resolution,[],[f60])).
% 2.95/1.02  
% 2.95/1.02  fof(f6,axiom,(
% 2.95/1.02    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 2.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.02  
% 2.95/1.02  fof(f61,plain,(
% 2.95/1.02    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 2.95/1.02    inference(cnf_transformation,[],[f6])).
% 2.95/1.02  
% 2.95/1.02  fof(f7,axiom,(
% 2.95/1.02    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 2.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.02  
% 2.95/1.02  fof(f44,plain,(
% 2.95/1.02    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK0(X0),X0))),
% 2.95/1.02    introduced(choice_axiom,[])).
% 2.95/1.02  
% 2.95/1.02  fof(f45,plain,(
% 2.95/1.02    ! [X0] : m1_subset_1(sK0(X0),X0)),
% 2.95/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f44])).
% 2.95/1.02  
% 2.95/1.02  fof(f62,plain,(
% 2.95/1.02    ( ! [X0] : (m1_subset_1(sK0(X0),X0)) )),
% 2.95/1.02    inference(cnf_transformation,[],[f45])).
% 2.95/1.02  
% 2.95/1.02  fof(f8,axiom,(
% 2.95/1.02    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.02  
% 2.95/1.02  fof(f22,plain,(
% 2.95/1.02    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.95/1.02    inference(ennf_transformation,[],[f8])).
% 2.95/1.02  
% 2.95/1.02  fof(f23,plain,(
% 2.95/1.02    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.95/1.02    inference(flattening,[],[f22])).
% 2.95/1.02  
% 2.95/1.02  fof(f63,plain,(
% 2.95/1.02    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.95/1.02    inference(cnf_transformation,[],[f23])).
% 2.95/1.02  
% 2.95/1.02  fof(f19,axiom,(
% 2.95/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 2.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.02  
% 2.95/1.02  fof(f38,plain,(
% 2.95/1.02    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.95/1.02    inference(ennf_transformation,[],[f19])).
% 2.95/1.02  
% 2.95/1.02  fof(f39,plain,(
% 2.95/1.02    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.95/1.02    inference(flattening,[],[f38])).
% 2.95/1.02  
% 2.95/1.02  fof(f81,plain,(
% 2.95/1.02    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.95/1.02    inference(cnf_transformation,[],[f39])).
% 2.95/1.02  
% 2.95/1.02  fof(f83,plain,(
% 2.95/1.02    v1_funct_2(sK5,k1_tarski(sK3),sK4)),
% 2.95/1.02    inference(cnf_transformation,[],[f53])).
% 2.95/1.02  
% 2.95/1.02  fof(f92,plain,(
% 2.95/1.02    v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4)),
% 2.95/1.02    inference(definition_unfolding,[],[f83,f88])).
% 2.95/1.02  
% 2.95/1.02  fof(f85,plain,(
% 2.95/1.02    k1_xboole_0 != sK4),
% 2.95/1.02    inference(cnf_transformation,[],[f53])).
% 2.95/1.02  
% 2.95/1.02  fof(f4,axiom,(
% 2.95/1.02    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 2.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.02  
% 2.95/1.02  fof(f57,plain,(
% 2.95/1.02    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 2.95/1.02    inference(cnf_transformation,[],[f4])).
% 2.95/1.02  
% 2.95/1.02  fof(f89,plain,(
% 2.95/1.02    ( ! [X0] : (~v1_xboole_0(k2_enumset1(X0,X0,X0,X0))) )),
% 2.95/1.02    inference(definition_unfolding,[],[f57,f88])).
% 2.95/1.02  
% 2.95/1.02  cnf(c_13,plain,
% 2.95/1.02      ( r2_hidden(X0,k1_relat_1(X1))
% 2.95/1.02      | ~ v1_funct_1(X1)
% 2.95/1.02      | ~ v1_relat_1(X1)
% 2.95/1.02      | k1_funct_1(X1,X0) = k1_xboole_0 ),
% 2.95/1.02      inference(cnf_transformation,[],[f95]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_29,negated_conjecture,
% 2.95/1.02      ( v1_funct_1(sK5) ),
% 2.95/1.02      inference(cnf_transformation,[],[f82]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_428,plain,
% 2.95/1.02      ( r2_hidden(X0,k1_relat_1(X1))
% 2.95/1.02      | ~ v1_relat_1(X1)
% 2.95/1.02      | k1_funct_1(X1,X0) = k1_xboole_0
% 2.95/1.02      | sK5 != X1 ),
% 2.95/1.02      inference(resolution_lifted,[status(thm)],[c_13,c_29]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_429,plain,
% 2.95/1.02      ( r2_hidden(X0,k1_relat_1(sK5))
% 2.95/1.02      | ~ v1_relat_1(sK5)
% 2.95/1.02      | k1_funct_1(sK5,X0) = k1_xboole_0 ),
% 2.95/1.02      inference(unflattening,[status(thm)],[c_428]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_1607,plain,
% 2.95/1.02      ( k1_funct_1(sK5,X0) = k1_xboole_0
% 2.95/1.02      | r2_hidden(X0,k1_relat_1(sK5)) = iProver_top
% 2.95/1.02      | v1_relat_1(sK5) != iProver_top ),
% 2.95/1.02      inference(predicate_to_equality,[status(thm)],[c_429]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_430,plain,
% 2.95/1.02      ( k1_funct_1(sK5,X0) = k1_xboole_0
% 2.95/1.02      | r2_hidden(X0,k1_relat_1(sK5)) = iProver_top
% 2.95/1.02      | v1_relat_1(sK5) != iProver_top ),
% 2.95/1.02      inference(predicate_to_equality,[status(thm)],[c_429]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_1224,plain,( X0 = X0 ),theory(equality) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_1786,plain,
% 2.95/1.02      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) ),
% 2.95/1.02      inference(instantiation,[status(thm)],[c_1224]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_18,plain,
% 2.95/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.95/1.02      | v1_relat_1(X0) ),
% 2.95/1.02      inference(cnf_transformation,[],[f75]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_27,negated_conjecture,
% 2.95/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) ),
% 2.95/1.02      inference(cnf_transformation,[],[f91]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_521,plain,
% 2.95/1.02      ( v1_relat_1(X0)
% 2.95/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.95/1.02      | sK5 != X0 ),
% 2.95/1.02      inference(resolution_lifted,[status(thm)],[c_18,c_27]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_522,plain,
% 2.95/1.02      ( v1_relat_1(sK5)
% 2.95/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.95/1.02      inference(unflattening,[status(thm)],[c_521]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_1788,plain,
% 2.95/1.02      ( v1_relat_1(sK5)
% 2.95/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) ),
% 2.95/1.02      inference(instantiation,[status(thm)],[c_522]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_1789,plain,
% 2.95/1.02      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
% 2.95/1.02      | v1_relat_1(sK5) = iProver_top ),
% 2.95/1.02      inference(predicate_to_equality,[status(thm)],[c_1788]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_2093,plain,
% 2.95/1.02      ( r2_hidden(X0,k1_relat_1(sK5)) = iProver_top
% 2.95/1.02      | k1_funct_1(sK5,X0) = k1_xboole_0 ),
% 2.95/1.02      inference(global_propositional_subsumption,
% 2.95/1.02                [status(thm)],
% 2.95/1.02                [c_1607,c_430,c_1786,c_1789]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_2094,plain,
% 2.95/1.02      ( k1_funct_1(sK5,X0) = k1_xboole_0
% 2.95/1.02      | r2_hidden(X0,k1_relat_1(sK5)) = iProver_top ),
% 2.95/1.02      inference(renaming,[status(thm)],[c_2093]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_9,plain,
% 2.95/1.02      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.95/1.02      | r2_hidden(sK1(X1),k2_relat_1(X1))
% 2.95/1.02      | ~ v1_relat_1(X1) ),
% 2.95/1.02      inference(cnf_transformation,[],[f66]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_1617,plain,
% 2.95/1.02      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 2.95/1.02      | r2_hidden(sK1(X1),k2_relat_1(X1)) = iProver_top
% 2.95/1.02      | v1_relat_1(X1) != iProver_top ),
% 2.95/1.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_3156,plain,
% 2.95/1.02      ( k1_funct_1(sK5,X0) = k1_xboole_0
% 2.95/1.02      | r2_hidden(sK1(sK5),k2_relat_1(sK5)) = iProver_top
% 2.95/1.02      | v1_relat_1(sK5) != iProver_top ),
% 2.95/1.02      inference(superposition,[status(thm)],[c_2094,c_1617]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_20,plain,
% 2.95/1.02      ( v4_relat_1(X0,X1)
% 2.95/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.95/1.02      inference(cnf_transformation,[],[f76]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_12,plain,
% 2.95/1.02      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.95/1.02      inference(cnf_transformation,[],[f69]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_311,plain,
% 2.95/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.95/1.02      | ~ v1_relat_1(X0)
% 2.95/1.02      | k7_relat_1(X0,X1) = X0 ),
% 2.95/1.02      inference(resolution,[status(thm)],[c_20,c_12]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_315,plain,
% 2.95/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.95/1.02      | k7_relat_1(X0,X1) = X0 ),
% 2.95/1.02      inference(global_propositional_subsumption,
% 2.95/1.02                [status(thm)],
% 2.95/1.02                [c_311,c_20,c_18,c_12]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_512,plain,
% 2.95/1.02      ( k7_relat_1(X0,X1) = X0
% 2.95/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.95/1.02      | sK5 != X0 ),
% 2.95/1.02      inference(resolution_lifted,[status(thm)],[c_315,c_27]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_513,plain,
% 2.95/1.02      ( k7_relat_1(sK5,X0) = sK5
% 2.95/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.95/1.02      inference(unflattening,[status(thm)],[c_512]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_1805,plain,
% 2.95/1.02      ( k7_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3)) = sK5 ),
% 2.95/1.02      inference(equality_resolution,[status(thm)],[c_513]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_1602,plain,
% 2.95/1.02      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.95/1.02      | v1_relat_1(sK5) = iProver_top ),
% 2.95/1.02      inference(predicate_to_equality,[status(thm)],[c_522]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_1813,plain,
% 2.95/1.02      ( v1_relat_1(sK5) = iProver_top ),
% 2.95/1.02      inference(global_propositional_subsumption,
% 2.95/1.02                [status(thm)],
% 2.95/1.02                [c_1602,c_1786,c_1789]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_8,plain,
% 2.95/1.02      ( ~ v1_relat_1(X0)
% 2.95/1.02      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.95/1.02      inference(cnf_transformation,[],[f65]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_1618,plain,
% 2.95/1.02      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 2.95/1.02      | v1_relat_1(X0) != iProver_top ),
% 2.95/1.02      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_2639,plain,
% 2.95/1.02      ( k2_relat_1(k7_relat_1(sK5,X0)) = k9_relat_1(sK5,X0) ),
% 2.95/1.02      inference(superposition,[status(thm)],[c_1813,c_1618]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_2817,plain,
% 2.95/1.02      ( k9_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3)) = k2_relat_1(sK5) ),
% 2.95/1.02      inference(superposition,[status(thm)],[c_1805,c_2639]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_7,plain,
% 2.95/1.02      ( ~ v1_relat_1(X0)
% 2.95/1.02      | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
% 2.95/1.02      inference(cnf_transformation,[],[f90]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_1619,plain,
% 2.95/1.02      ( k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1)
% 2.95/1.02      | v1_relat_1(X0) != iProver_top ),
% 2.95/1.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_2691,plain,
% 2.95/1.02      ( k9_relat_1(sK5,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK5,X0) ),
% 2.95/1.02      inference(superposition,[status(thm)],[c_1813,c_1619]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_2867,plain,
% 2.95/1.02      ( k11_relat_1(sK5,sK3) = k2_relat_1(sK5) ),
% 2.95/1.02      inference(superposition,[status(thm)],[c_2817,c_2691]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_10,plain,
% 2.95/1.02      ( r2_hidden(X0,k1_relat_1(X1))
% 2.95/1.02      | ~ v1_relat_1(X1)
% 2.95/1.02      | k11_relat_1(X1,X0) = k1_xboole_0 ),
% 2.95/1.02      inference(cnf_transformation,[],[f68]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_1616,plain,
% 2.95/1.02      ( k11_relat_1(X0,X1) = k1_xboole_0
% 2.95/1.02      | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
% 2.95/1.02      | v1_relat_1(X0) != iProver_top ),
% 2.95/1.02      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_19,plain,
% 2.95/1.02      ( v5_relat_1(X0,X1)
% 2.95/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.95/1.02      inference(cnf_transformation,[],[f77]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_17,plain,
% 2.95/1.02      ( ~ v5_relat_1(X0,X1)
% 2.95/1.02      | ~ r2_hidden(X2,k1_relat_1(X0))
% 2.95/1.02      | r2_hidden(k1_funct_1(X0,X2),X1)
% 2.95/1.02      | ~ v1_funct_1(X0)
% 2.95/1.02      | ~ v1_relat_1(X0) ),
% 2.95/1.02      inference(cnf_transformation,[],[f74]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_331,plain,
% 2.95/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.95/1.02      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.95/1.02      | r2_hidden(k1_funct_1(X0,X3),X2)
% 2.95/1.02      | ~ v1_funct_1(X0)
% 2.95/1.02      | ~ v1_relat_1(X0) ),
% 2.95/1.02      inference(resolution,[status(thm)],[c_19,c_17]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_335,plain,
% 2.95/1.02      ( ~ v1_funct_1(X0)
% 2.95/1.02      | r2_hidden(k1_funct_1(X0,X3),X2)
% 2.95/1.02      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.95/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.95/1.02      inference(global_propositional_subsumption,
% 2.95/1.02                [status(thm)],
% 2.95/1.02                [c_331,c_18]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_336,plain,
% 2.95/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.95/1.02      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.95/1.02      | r2_hidden(k1_funct_1(X0,X3),X2)
% 2.95/1.02      | ~ v1_funct_1(X0) ),
% 2.95/1.02      inference(renaming,[status(thm)],[c_335]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_380,plain,
% 2.95/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.95/1.02      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.95/1.02      | r2_hidden(k1_funct_1(X0,X3),X2)
% 2.95/1.02      | sK5 != X0 ),
% 2.95/1.02      inference(resolution_lifted,[status(thm)],[c_336,c_29]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_381,plain,
% 2.95/1.02      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.95/1.02      | ~ r2_hidden(X2,k1_relat_1(sK5))
% 2.95/1.02      | r2_hidden(k1_funct_1(sK5,X2),X1) ),
% 2.95/1.02      inference(unflattening,[status(thm)],[c_380]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_533,plain,
% 2.95/1.02      ( ~ r2_hidden(X0,k1_relat_1(sK5))
% 2.95/1.02      | r2_hidden(k1_funct_1(sK5,X0),X1)
% 2.95/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X2,X1))
% 2.95/1.02      | sK5 != sK5 ),
% 2.95/1.02      inference(resolution_lifted,[status(thm)],[c_27,c_381]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_859,plain,
% 2.95/1.02      ( ~ r2_hidden(X0,k1_relat_1(sK5))
% 2.95/1.02      | r2_hidden(k1_funct_1(sK5,X0),X1)
% 2.95/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X2,X1)) ),
% 2.95/1.02      inference(equality_resolution_simp,[status(thm)],[c_533]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_1601,plain,
% 2.95/1.02      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.95/1.02      | r2_hidden(X2,k1_relat_1(sK5)) != iProver_top
% 2.95/1.02      | r2_hidden(k1_funct_1(sK5,X2),X1) = iProver_top ),
% 2.95/1.02      inference(predicate_to_equality,[status(thm)],[c_859]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_1900,plain,
% 2.95/1.02      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 2.95/1.02      | r2_hidden(k1_funct_1(sK5,X0),sK4) = iProver_top ),
% 2.95/1.02      inference(equality_resolution,[status(thm)],[c_1601]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_25,negated_conjecture,
% 2.95/1.02      ( ~ r2_hidden(k1_funct_1(sK5,sK3),sK4) ),
% 2.95/1.02      inference(cnf_transformation,[],[f86]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_1611,plain,
% 2.95/1.02      ( r2_hidden(k1_funct_1(sK5,sK3),sK4) != iProver_top ),
% 2.95/1.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_2263,plain,
% 2.95/1.02      ( r2_hidden(sK3,k1_relat_1(sK5)) != iProver_top ),
% 2.95/1.02      inference(superposition,[status(thm)],[c_1900,c_1611]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_2697,plain,
% 2.95/1.02      ( k11_relat_1(sK5,sK3) = k1_xboole_0
% 2.95/1.02      | v1_relat_1(sK5) != iProver_top ),
% 2.95/1.02      inference(superposition,[status(thm)],[c_1616,c_2263]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_2982,plain,
% 2.95/1.02      ( k11_relat_1(sK5,sK3) = k1_xboole_0 ),
% 2.95/1.02      inference(global_propositional_subsumption,
% 2.95/1.02                [status(thm)],
% 2.95/1.02                [c_2697,c_1786,c_1789]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_2985,plain,
% 2.95/1.02      ( k2_relat_1(sK5) = k1_xboole_0 ),
% 2.95/1.02      inference(light_normalisation,[status(thm)],[c_2867,c_2982]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_3167,plain,
% 2.95/1.02      ( k1_funct_1(sK5,X0) = k1_xboole_0
% 2.95/1.02      | r2_hidden(sK1(sK5),k1_xboole_0) = iProver_top
% 2.95/1.02      | v1_relat_1(sK5) != iProver_top ),
% 2.95/1.02      inference(light_normalisation,[status(thm)],[c_3156,c_2985]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_3288,plain,
% 2.95/1.02      ( r2_hidden(sK1(sK5),k1_xboole_0) = iProver_top
% 2.95/1.02      | k1_funct_1(sK5,X0) = k1_xboole_0 ),
% 2.95/1.02      inference(global_propositional_subsumption,
% 2.95/1.02                [status(thm)],
% 2.95/1.02                [c_3167,c_1786,c_1789]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_3289,plain,
% 2.95/1.02      ( k1_funct_1(sK5,X0) = k1_xboole_0
% 2.95/1.02      | r2_hidden(sK1(sK5),k1_xboole_0) = iProver_top ),
% 2.95/1.02      inference(renaming,[status(thm)],[c_3288]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_1,plain,
% 2.95/1.02      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.95/1.02      inference(cnf_transformation,[],[f93]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_4,plain,
% 2.95/1.02      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 2.95/1.02      inference(cnf_transformation,[],[f61]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_1620,plain,
% 2.95/1.02      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 2.95/1.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_2287,plain,
% 2.95/1.02      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.95/1.02      inference(superposition,[status(thm)],[c_1,c_1620]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_3296,plain,
% 2.95/1.02      ( k1_funct_1(sK5,X0) = k1_xboole_0 ),
% 2.95/1.02      inference(forward_subsumption_resolution,
% 2.95/1.02                [status(thm)],
% 2.95/1.02                [c_3289,c_2287]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_5,plain,
% 2.95/1.02      ( m1_subset_1(sK0(X0),X0) ),
% 2.95/1.02      inference(cnf_transformation,[],[f62]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_6,plain,
% 2.95/1.02      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.95/1.02      inference(cnf_transformation,[],[f63]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_460,plain,
% 2.95/1.02      ( r2_hidden(X0,X1) | v1_xboole_0(X1) | X1 != X2 | sK0(X2) != X0 ),
% 2.95/1.02      inference(resolution_lifted,[status(thm)],[c_5,c_6]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_461,plain,
% 2.95/1.02      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.95/1.02      inference(unflattening,[status(thm)],[c_460]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_1606,plain,
% 2.95/1.02      ( r2_hidden(sK0(X0),X0) = iProver_top
% 2.95/1.02      | v1_xboole_0(X0) = iProver_top ),
% 2.95/1.02      inference(predicate_to_equality,[status(thm)],[c_461]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_24,plain,
% 2.95/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.95/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.95/1.02      | ~ r2_hidden(X3,X1)
% 2.95/1.02      | r2_hidden(k1_funct_1(X0,X3),X2)
% 2.95/1.02      | ~ v1_funct_1(X0)
% 2.95/1.02      | k1_xboole_0 = X2 ),
% 2.95/1.02      inference(cnf_transformation,[],[f81]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_28,negated_conjecture,
% 2.95/1.02      ( v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
% 2.95/1.02      inference(cnf_transformation,[],[f92]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_359,plain,
% 2.95/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.95/1.02      | ~ r2_hidden(X3,X1)
% 2.95/1.02      | r2_hidden(k1_funct_1(X0,X3),X2)
% 2.95/1.02      | ~ v1_funct_1(X0)
% 2.95/1.02      | k2_enumset1(sK3,sK3,sK3,sK3) != X1
% 2.95/1.02      | sK4 != X2
% 2.95/1.02      | sK5 != X0
% 2.95/1.02      | k1_xboole_0 = X2 ),
% 2.95/1.02      inference(resolution_lifted,[status(thm)],[c_24,c_28]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_360,plain,
% 2.95/1.02      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
% 2.95/1.02      | ~ r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3))
% 2.95/1.02      | r2_hidden(k1_funct_1(sK5,X0),sK4)
% 2.95/1.02      | ~ v1_funct_1(sK5)
% 2.95/1.02      | k1_xboole_0 = sK4 ),
% 2.95/1.02      inference(unflattening,[status(thm)],[c_359]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_26,negated_conjecture,
% 2.95/1.02      ( k1_xboole_0 != sK4 ),
% 2.95/1.02      inference(cnf_transformation,[],[f85]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_364,plain,
% 2.95/1.02      ( ~ r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3))
% 2.95/1.02      | r2_hidden(k1_funct_1(sK5,X0),sK4) ),
% 2.95/1.02      inference(global_propositional_subsumption,
% 2.95/1.02                [status(thm)],
% 2.95/1.02                [c_360,c_29,c_27,c_26]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_1610,plain,
% 2.95/1.02      ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
% 2.95/1.02      | r2_hidden(k1_funct_1(sK5,X0),sK4) = iProver_top ),
% 2.95/1.02      inference(predicate_to_equality,[status(thm)],[c_364]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_2283,plain,
% 2.95/1.02      ( r2_hidden(k1_funct_1(sK5,sK0(k2_enumset1(sK3,sK3,sK3,sK3))),sK4) = iProver_top
% 2.95/1.02      | v1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top ),
% 2.95/1.02      inference(superposition,[status(thm)],[c_1606,c_1610]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_1794,plain,
% 2.95/1.02      ( r2_hidden(sK0(k2_enumset1(X0,X0,X0,X0)),k2_enumset1(X0,X0,X0,X0))
% 2.95/1.02      | v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
% 2.95/1.02      inference(instantiation,[status(thm)],[c_461]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_2254,plain,
% 2.95/1.02      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
% 2.95/1.02      | v1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 2.95/1.02      inference(instantiation,[status(thm)],[c_1794]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_2256,plain,
% 2.95/1.02      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top
% 2.95/1.02      | v1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top ),
% 2.95/1.02      inference(predicate_to_equality,[status(thm)],[c_2254]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_2255,plain,
% 2.95/1.02      ( r2_hidden(k1_funct_1(sK5,sK0(k2_enumset1(sK3,sK3,sK3,sK3))),sK4)
% 2.95/1.02      | ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 2.95/1.02      inference(instantiation,[status(thm)],[c_364]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_2258,plain,
% 2.95/1.02      ( r2_hidden(k1_funct_1(sK5,sK0(k2_enumset1(sK3,sK3,sK3,sK3))),sK4) = iProver_top
% 2.95/1.02      | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
% 2.95/1.02      inference(predicate_to_equality,[status(thm)],[c_2255]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_0,plain,
% 2.95/1.02      ( ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
% 2.95/1.02      inference(cnf_transformation,[],[f89]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_2268,plain,
% 2.95/1.02      ( ~ v1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 2.95/1.02      inference(instantiation,[status(thm)],[c_0]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_2269,plain,
% 2.95/1.02      ( v1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
% 2.95/1.02      inference(predicate_to_equality,[status(thm)],[c_2268]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_2481,plain,
% 2.95/1.02      ( r2_hidden(k1_funct_1(sK5,sK0(k2_enumset1(sK3,sK3,sK3,sK3))),sK4) = iProver_top ),
% 2.95/1.02      inference(global_propositional_subsumption,
% 2.95/1.02                [status(thm)],
% 2.95/1.02                [c_2283,c_2256,c_2258,c_2269]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_3305,plain,
% 2.95/1.02      ( r2_hidden(k1_xboole_0,sK4) = iProver_top ),
% 2.95/1.02      inference(demodulation,[status(thm)],[c_3296,c_2481]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_2267,plain,
% 2.95/1.02      ( k1_funct_1(sK5,sK3) = k1_xboole_0 ),
% 2.95/1.02      inference(superposition,[status(thm)],[c_2094,c_2263]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(c_2380,plain,
% 2.95/1.02      ( r2_hidden(k1_xboole_0,sK4) != iProver_top ),
% 2.95/1.02      inference(demodulation,[status(thm)],[c_2267,c_1611]) ).
% 2.95/1.02  
% 2.95/1.02  cnf(contradiction,plain,
% 2.95/1.02      ( $false ),
% 2.95/1.02      inference(minisat,[status(thm)],[c_3305,c_2380]) ).
% 2.95/1.02  
% 2.95/1.02  
% 2.95/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.95/1.02  
% 2.95/1.02  ------                               Statistics
% 2.95/1.02  
% 2.95/1.02  ------ General
% 2.95/1.02  
% 2.95/1.02  abstr_ref_over_cycles:                  0
% 2.95/1.02  abstr_ref_under_cycles:                 0
% 2.95/1.02  gc_basic_clause_elim:                   0
% 2.95/1.02  forced_gc_time:                         0
% 2.95/1.02  parsing_time:                           0.011
% 2.95/1.02  unif_index_cands_time:                  0.
% 2.95/1.02  unif_index_add_time:                    0.
% 2.95/1.02  orderings_time:                         0.
% 2.95/1.02  out_proof_time:                         0.011
% 2.95/1.02  total_time:                             0.161
% 2.95/1.02  num_of_symbols:                         57
% 2.95/1.02  num_of_terms:                           2583
% 2.95/1.02  
% 2.95/1.02  ------ Preprocessing
% 2.95/1.02  
% 2.95/1.02  num_of_splits:                          0
% 2.95/1.02  num_of_split_atoms:                     0
% 2.95/1.02  num_of_reused_defs:                     0
% 2.95/1.02  num_eq_ax_congr_red:                    38
% 2.95/1.02  num_of_sem_filtered_clauses:            1
% 2.95/1.02  num_of_subtypes:                        0
% 2.95/1.02  monotx_restored_types:                  0
% 2.95/1.02  sat_num_of_epr_types:                   0
% 2.95/1.02  sat_num_of_non_cyclic_types:            0
% 2.95/1.02  sat_guarded_non_collapsed_types:        0
% 2.95/1.02  num_pure_diseq_elim:                    0
% 2.95/1.02  simp_replaced_by:                       0
% 2.95/1.02  res_preprocessed:                       141
% 2.95/1.02  prep_upred:                             0
% 2.95/1.02  prep_unflattend:                        41
% 2.95/1.02  smt_new_axioms:                         0
% 2.95/1.02  pred_elim_cands:                        3
% 2.95/1.02  pred_elim:                              5
% 2.95/1.02  pred_elim_cl:                           2
% 2.95/1.02  pred_elim_cycles:                       10
% 2.95/1.02  merged_defs:                            0
% 2.95/1.02  merged_defs_ncl:                        0
% 2.95/1.02  bin_hyper_res:                          0
% 2.95/1.02  prep_cycles:                            4
% 2.95/1.02  pred_elim_time:                         0.021
% 2.95/1.02  splitting_time:                         0.
% 2.95/1.02  sem_filter_time:                        0.
% 2.95/1.02  monotx_time:                            0.
% 2.95/1.02  subtype_inf_time:                       0.
% 2.95/1.02  
% 2.95/1.02  ------ Problem properties
% 2.95/1.02  
% 2.95/1.02  clauses:                                27
% 2.95/1.02  conjectures:                            2
% 2.95/1.02  epr:                                    1
% 2.95/1.02  horn:                                   21
% 2.95/1.02  ground:                                 3
% 2.95/1.02  unary:                                  8
% 2.95/1.02  binary:                                 8
% 2.95/1.02  lits:                                   58
% 2.95/1.02  lits_eq:                                23
% 2.95/1.02  fd_pure:                                0
% 2.95/1.02  fd_pseudo:                              0
% 2.95/1.02  fd_cond:                                4
% 2.95/1.02  fd_pseudo_cond:                         1
% 2.95/1.02  ac_symbols:                             0
% 2.95/1.02  
% 2.95/1.02  ------ Propositional Solver
% 2.95/1.02  
% 2.95/1.02  prop_solver_calls:                      27
% 2.95/1.02  prop_fast_solver_calls:                 900
% 2.95/1.02  smt_solver_calls:                       0
% 2.95/1.02  smt_fast_solver_calls:                  0
% 2.95/1.02  prop_num_of_clauses:                    985
% 2.95/1.02  prop_preprocess_simplified:             4919
% 2.95/1.02  prop_fo_subsumed:                       12
% 2.95/1.02  prop_solver_time:                       0.
% 2.95/1.02  smt_solver_time:                        0.
% 2.95/1.02  smt_fast_solver_time:                   0.
% 2.95/1.02  prop_fast_solver_time:                  0.
% 2.95/1.02  prop_unsat_core_time:                   0.
% 2.95/1.02  
% 2.95/1.02  ------ QBF
% 2.95/1.02  
% 2.95/1.02  qbf_q_res:                              0
% 2.95/1.02  qbf_num_tautologies:                    0
% 2.95/1.02  qbf_prep_cycles:                        0
% 2.95/1.02  
% 2.95/1.02  ------ BMC1
% 2.95/1.02  
% 2.95/1.02  bmc1_current_bound:                     -1
% 2.95/1.02  bmc1_last_solved_bound:                 -1
% 2.95/1.02  bmc1_unsat_core_size:                   -1
% 2.95/1.02  bmc1_unsat_core_parents_size:           -1
% 2.95/1.02  bmc1_merge_next_fun:                    0
% 2.95/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.95/1.02  
% 2.95/1.02  ------ Instantiation
% 2.95/1.02  
% 2.95/1.02  inst_num_of_clauses:                    353
% 2.95/1.02  inst_num_in_passive:                    111
% 2.95/1.02  inst_num_in_active:                     211
% 2.95/1.02  inst_num_in_unprocessed:                31
% 2.95/1.02  inst_num_of_loops:                      250
% 2.95/1.02  inst_num_of_learning_restarts:          0
% 2.95/1.02  inst_num_moves_active_passive:          36
% 2.95/1.02  inst_lit_activity:                      0
% 2.95/1.02  inst_lit_activity_moves:                0
% 2.95/1.02  inst_num_tautologies:                   0
% 2.95/1.02  inst_num_prop_implied:                  0
% 2.95/1.02  inst_num_existing_simplified:           0
% 2.95/1.02  inst_num_eq_res_simplified:             0
% 2.95/1.02  inst_num_child_elim:                    0
% 2.95/1.02  inst_num_of_dismatching_blockings:      39
% 2.95/1.02  inst_num_of_non_proper_insts:           250
% 2.95/1.02  inst_num_of_duplicates:                 0
% 2.95/1.02  inst_inst_num_from_inst_to_res:         0
% 2.95/1.02  inst_dismatching_checking_time:         0.
% 2.95/1.02  
% 2.95/1.02  ------ Resolution
% 2.95/1.02  
% 2.95/1.02  res_num_of_clauses:                     0
% 2.95/1.02  res_num_in_passive:                     0
% 2.95/1.02  res_num_in_active:                      0
% 2.95/1.02  res_num_of_loops:                       145
% 2.95/1.02  res_forward_subset_subsumed:            50
% 2.95/1.02  res_backward_subset_subsumed:           0
% 2.95/1.02  res_forward_subsumed:                   0
% 2.95/1.02  res_backward_subsumed:                  0
% 2.95/1.02  res_forward_subsumption_resolution:     0
% 2.95/1.02  res_backward_subsumption_resolution:    0
% 2.95/1.02  res_clause_to_clause_subsumption:       79
% 2.95/1.02  res_orphan_elimination:                 0
% 2.95/1.02  res_tautology_del:                      31
% 2.95/1.02  res_num_eq_res_simplified:              1
% 2.95/1.02  res_num_sel_changes:                    0
% 2.95/1.02  res_moves_from_active_to_pass:          0
% 2.95/1.02  
% 2.95/1.02  ------ Superposition
% 2.95/1.02  
% 2.95/1.02  sup_time_total:                         0.
% 2.95/1.02  sup_time_generating:                    0.
% 2.95/1.02  sup_time_sim_full:                      0.
% 2.95/1.02  sup_time_sim_immed:                     0.
% 2.95/1.02  
% 2.95/1.02  sup_num_of_clauses:                     52
% 2.95/1.02  sup_num_in_active:                      35
% 2.95/1.02  sup_num_in_passive:                     17
% 2.95/1.02  sup_num_of_loops:                       48
% 2.95/1.02  sup_fw_superposition:                   23
% 2.95/1.02  sup_bw_superposition:                   17
% 2.95/1.02  sup_immediate_simplified:               11
% 2.95/1.02  sup_given_eliminated:                   0
% 2.95/1.02  comparisons_done:                       0
% 2.95/1.02  comparisons_avoided:                    0
% 2.95/1.02  
% 2.95/1.02  ------ Simplifications
% 2.95/1.02  
% 2.95/1.02  
% 2.95/1.02  sim_fw_subset_subsumed:                 5
% 2.95/1.02  sim_bw_subset_subsumed:                 2
% 2.95/1.02  sim_fw_subsumed:                        2
% 2.95/1.02  sim_bw_subsumed:                        3
% 2.95/1.02  sim_fw_subsumption_res:                 2
% 2.95/1.02  sim_bw_subsumption_res:                 0
% 2.95/1.02  sim_tautology_del:                      0
% 2.95/1.02  sim_eq_tautology_del:                   3
% 2.95/1.02  sim_eq_res_simp:                        0
% 2.95/1.02  sim_fw_demodulated:                     0
% 2.95/1.02  sim_bw_demodulated:                     12
% 2.95/1.02  sim_light_normalised:                   4
% 2.95/1.02  sim_joinable_taut:                      0
% 2.95/1.02  sim_joinable_simp:                      0
% 2.95/1.02  sim_ac_normalised:                      0
% 2.95/1.02  sim_smt_subsumption:                    0
% 2.95/1.02  
%------------------------------------------------------------------------------
