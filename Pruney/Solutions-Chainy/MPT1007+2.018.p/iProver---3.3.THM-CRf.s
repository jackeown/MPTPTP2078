%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:45 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :  172 (1446 expanded)
%              Number of clauses        :   93 ( 434 expanded)
%              Number of leaves         :   24 ( 330 expanded)
%              Depth                    :   25
%              Number of atoms          :  446 (4026 expanded)
%              Number of equality atoms :  185 (1344 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f45])).

fof(f57,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f43,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f44,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f49,plain,
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

fof(f50,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK1),sK2)
    & k1_xboole_0 != sK2
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
    & v1_funct_2(sK3,k1_tarski(sK1),sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f44,f49])).

fof(f81,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) ),
    inference(cnf_transformation,[],[f50])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f84,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f85,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f53,f84])).

fof(f88,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(definition_unfolding,[],[f81,f85])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f60,f85])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k1_xboole_0 = k11_relat_1(X1,X0) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X1))
      | k1_xboole_0 = k11_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f17,axiom,(
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
    inference(ennf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f79,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f83,plain,(
    ~ r2_hidden(k1_funct_1(sK3,sK1),sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f68,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f21,axiom,(
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
    inference(ennf_transformation,[],[f21])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f41])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f80,plain,(
    v1_funct_2(sK3,k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f89,plain,(
    v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
    inference(definition_unfolding,[],[f80,f85])).

fof(f82,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f50])).

fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

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

fof(f48,plain,(
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

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_funct_1(X0,X1) != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_funct_1(X0,X1)
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f14,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f18,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f86,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f56,f84])).

cnf(c_3,plain,
    ( m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_511,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | X1 != X2
    | sK0(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_4])).

cnf(c_512,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_511])).

cnf(c_2057,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_512])).

cnf(c_23,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_10,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_319,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_23,c_10])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_323,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_319,c_23,c_21,c_10])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_561,plain,
    ( k7_relat_1(X0,X1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_323,c_27])).

cnf(c_562,plain,
    ( k7_relat_1(sK3,X0) = sK3
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_561])).

cnf(c_2243,plain,
    ( k7_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) = sK3 ),
    inference(equality_resolution,[status(thm)],[c_562])).

cnf(c_570,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_27])).

cnf(c_571,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_570])).

cnf(c_2053,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_571])).

cnf(c_1675,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2227,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_1675])).

cnf(c_2229,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_571])).

cnf(c_2230,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2229])).

cnf(c_2267,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2053,c_2227,c_2230])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2068,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2726,plain,
    ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_2267,c_2068])).

cnf(c_2811,plain,
    ( k9_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2243,c_2726])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2069,plain,
    ( k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3106,plain,
    ( k9_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_2267,c_2069])).

cnf(c_3269,plain,
    ( k11_relat_1(sK3,sK1) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2811,c_3106])).

cnf(c_8,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k11_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2067,plain,
    ( k11_relat_1(X0,X1) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_22,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_19,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X2),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_339,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(resolution,[status(thm)],[c_22,c_19])).

cnf(c_353,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_339,c_21])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_431,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_353,c_29])).

cnf(c_432,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,X0),X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(unflattening,[status(thm)],[c_431])).

cnf(c_582,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X1))
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_432])).

cnf(c_1118,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X1)) ),
    inference(equality_resolution_simp,[status(thm)],[c_582])).

cnf(c_2052,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | r2_hidden(X2,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1118])).

cnf(c_2329,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),sK2) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2052])).

cnf(c_25,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(sK3,sK1),sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2063,plain,
    ( r2_hidden(k1_funct_1(sK3,sK1),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2592,plain,
    ( r2_hidden(sK1,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2329,c_2063])).

cnf(c_3191,plain,
    ( k11_relat_1(sK3,sK1) = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2067,c_2592])).

cnf(c_3339,plain,
    ( k11_relat_1(sK3,sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3191,c_2227,c_2230])).

cnf(c_3343,plain,
    ( k2_relat_1(sK3) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3269,c_3339])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2065,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3346,plain,
    ( sK3 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3343,c_2065])).

cnf(c_2351,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != k1_xboole_0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2359,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1675])).

cnf(c_1676,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2531,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_1676])).

cnf(c_2802,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2531])).

cnf(c_2803,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_2802])).

cnf(c_3504,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3346,c_2227,c_2229,c_2351,c_2359,c_2803,c_3343])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_366,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k1_funct_1(X2,X0),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X2)
    | k2_enumset1(sK1,sK1,sK1,sK1) != X1
    | sK2 != X3
    | sK3 != X2
    | k1_xboole_0 = X3 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_28])).

cnf(c_367,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
    | r2_hidden(k1_funct_1(sK3,X0),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_366])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_371,plain,
    ( r2_hidden(k1_funct_1(sK3,X0),sK2)
    | ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_367,c_29,c_27,c_26])).

cnf(c_372,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
    | r2_hidden(k1_funct_1(sK3,X0),sK2) ),
    inference(renaming,[status(thm)],[c_371])).

cnf(c_2061,plain,
    ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_372])).

cnf(c_3525,plain,
    ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
    | r2_hidden(k1_funct_1(k1_xboole_0,X0),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3504,c_2061])).

cnf(c_16,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_479,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,X0) = k1_xboole_0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_29])).

cnf(c_480,plain,
    ( r2_hidden(X0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_479])).

cnf(c_2058,plain,
    ( k1_funct_1(sK3,X0) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_480])).

cnf(c_481,plain,
    ( k1_funct_1(sK3,X0) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_480])).

cnf(c_2470,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
    | k1_funct_1(sK3,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2058,c_481,c_2227,c_2230])).

cnf(c_2471,plain,
    ( k1_funct_1(sK3,X0) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2470])).

cnf(c_3520,plain,
    ( k1_funct_1(k1_xboole_0,X0) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3504,c_2471])).

cnf(c_12,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_3551,plain,
    ( k1_funct_1(k1_xboole_0,X0) = k1_xboole_0
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3520,c_12])).

cnf(c_1,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_308,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_20])).

cnf(c_309,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_308])).

cnf(c_310,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_309])).

cnf(c_3837,plain,
    ( k1_funct_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3551,c_310])).

cnf(c_3994,plain,
    ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
    | r2_hidden(k1_xboole_0,sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3525,c_3837])).

cnf(c_2596,plain,
    ( k1_funct_1(sK3,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2471,c_2592])).

cnf(c_2649,plain,
    ( r2_hidden(k1_xboole_0,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2596,c_2063])).

cnf(c_3997,plain,
    ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3994,c_2649])).

cnf(c_4001,plain,
    ( v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2057,c_3997])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2641,plain,
    ( ~ v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2642,plain,
    ( v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2641])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4001,c_2642])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 21:01:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.62/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/0.99  
% 2.62/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.62/0.99  
% 2.62/0.99  ------  iProver source info
% 2.62/0.99  
% 2.62/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.62/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.62/0.99  git: non_committed_changes: false
% 2.62/0.99  git: last_make_outside_of_git: false
% 2.62/0.99  
% 2.62/0.99  ------ 
% 2.62/0.99  
% 2.62/0.99  ------ Input Options
% 2.62/0.99  
% 2.62/0.99  --out_options                           all
% 2.62/0.99  --tptp_safe_out                         true
% 2.62/0.99  --problem_path                          ""
% 2.62/0.99  --include_path                          ""
% 2.62/0.99  --clausifier                            res/vclausify_rel
% 2.62/0.99  --clausifier_options                    --mode clausify
% 2.62/0.99  --stdin                                 false
% 2.62/0.99  --stats_out                             all
% 2.62/0.99  
% 2.62/0.99  ------ General Options
% 2.62/0.99  
% 2.62/0.99  --fof                                   false
% 2.62/0.99  --time_out_real                         305.
% 2.62/0.99  --time_out_virtual                      -1.
% 2.62/0.99  --symbol_type_check                     false
% 2.62/0.99  --clausify_out                          false
% 2.62/0.99  --sig_cnt_out                           false
% 2.62/0.99  --trig_cnt_out                          false
% 2.62/0.99  --trig_cnt_out_tolerance                1.
% 2.62/0.99  --trig_cnt_out_sk_spl                   false
% 2.62/0.99  --abstr_cl_out                          false
% 2.62/0.99  
% 2.62/0.99  ------ Global Options
% 2.62/0.99  
% 2.62/0.99  --schedule                              default
% 2.62/0.99  --add_important_lit                     false
% 2.62/0.99  --prop_solver_per_cl                    1000
% 2.62/0.99  --min_unsat_core                        false
% 2.62/0.99  --soft_assumptions                      false
% 2.62/0.99  --soft_lemma_size                       3
% 2.62/0.99  --prop_impl_unit_size                   0
% 2.62/0.99  --prop_impl_unit                        []
% 2.62/0.99  --share_sel_clauses                     true
% 2.62/0.99  --reset_solvers                         false
% 2.62/0.99  --bc_imp_inh                            [conj_cone]
% 2.62/0.99  --conj_cone_tolerance                   3.
% 2.62/0.99  --extra_neg_conj                        none
% 2.62/0.99  --large_theory_mode                     true
% 2.62/0.99  --prolific_symb_bound                   200
% 2.62/0.99  --lt_threshold                          2000
% 2.62/0.99  --clause_weak_htbl                      true
% 2.62/0.99  --gc_record_bc_elim                     false
% 2.62/0.99  
% 2.62/0.99  ------ Preprocessing Options
% 2.62/0.99  
% 2.62/0.99  --preprocessing_flag                    true
% 2.62/0.99  --time_out_prep_mult                    0.1
% 2.62/0.99  --splitting_mode                        input
% 2.62/0.99  --splitting_grd                         true
% 2.62/0.99  --splitting_cvd                         false
% 2.62/0.99  --splitting_cvd_svl                     false
% 2.62/0.99  --splitting_nvd                         32
% 2.62/0.99  --sub_typing                            true
% 2.62/0.99  --prep_gs_sim                           true
% 2.62/0.99  --prep_unflatten                        true
% 2.62/0.99  --prep_res_sim                          true
% 2.62/0.99  --prep_upred                            true
% 2.62/0.99  --prep_sem_filter                       exhaustive
% 2.62/0.99  --prep_sem_filter_out                   false
% 2.62/0.99  --pred_elim                             true
% 2.62/0.99  --res_sim_input                         true
% 2.62/0.99  --eq_ax_congr_red                       true
% 2.62/0.99  --pure_diseq_elim                       true
% 2.62/0.99  --brand_transform                       false
% 2.62/0.99  --non_eq_to_eq                          false
% 2.62/0.99  --prep_def_merge                        true
% 2.62/0.99  --prep_def_merge_prop_impl              false
% 2.62/0.99  --prep_def_merge_mbd                    true
% 2.62/0.99  --prep_def_merge_tr_red                 false
% 2.62/0.99  --prep_def_merge_tr_cl                  false
% 2.62/0.99  --smt_preprocessing                     true
% 2.62/0.99  --smt_ac_axioms                         fast
% 2.62/0.99  --preprocessed_out                      false
% 2.62/0.99  --preprocessed_stats                    false
% 2.62/0.99  
% 2.62/0.99  ------ Abstraction refinement Options
% 2.62/0.99  
% 2.62/0.99  --abstr_ref                             []
% 2.62/0.99  --abstr_ref_prep                        false
% 2.62/0.99  --abstr_ref_until_sat                   false
% 2.62/0.99  --abstr_ref_sig_restrict                funpre
% 2.62/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.62/0.99  --abstr_ref_under                       []
% 2.62/0.99  
% 2.62/0.99  ------ SAT Options
% 2.62/0.99  
% 2.62/0.99  --sat_mode                              false
% 2.62/0.99  --sat_fm_restart_options                ""
% 2.62/0.99  --sat_gr_def                            false
% 2.62/0.99  --sat_epr_types                         true
% 2.62/0.99  --sat_non_cyclic_types                  false
% 2.62/0.99  --sat_finite_models                     false
% 2.62/0.99  --sat_fm_lemmas                         false
% 2.62/0.99  --sat_fm_prep                           false
% 2.62/0.99  --sat_fm_uc_incr                        true
% 2.62/0.99  --sat_out_model                         small
% 2.62/0.99  --sat_out_clauses                       false
% 2.62/0.99  
% 2.62/0.99  ------ QBF Options
% 2.62/0.99  
% 2.62/0.99  --qbf_mode                              false
% 2.62/0.99  --qbf_elim_univ                         false
% 2.62/0.99  --qbf_dom_inst                          none
% 2.62/0.99  --qbf_dom_pre_inst                      false
% 2.62/0.99  --qbf_sk_in                             false
% 2.62/0.99  --qbf_pred_elim                         true
% 2.62/0.99  --qbf_split                             512
% 2.62/0.99  
% 2.62/0.99  ------ BMC1 Options
% 2.62/0.99  
% 2.62/0.99  --bmc1_incremental                      false
% 2.62/0.99  --bmc1_axioms                           reachable_all
% 2.62/0.99  --bmc1_min_bound                        0
% 2.62/0.99  --bmc1_max_bound                        -1
% 2.62/0.99  --bmc1_max_bound_default                -1
% 2.62/0.99  --bmc1_symbol_reachability              true
% 2.62/0.99  --bmc1_property_lemmas                  false
% 2.62/0.99  --bmc1_k_induction                      false
% 2.62/0.99  --bmc1_non_equiv_states                 false
% 2.62/0.99  --bmc1_deadlock                         false
% 2.62/0.99  --bmc1_ucm                              false
% 2.62/0.99  --bmc1_add_unsat_core                   none
% 2.62/0.99  --bmc1_unsat_core_children              false
% 2.62/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.62/0.99  --bmc1_out_stat                         full
% 2.62/0.99  --bmc1_ground_init                      false
% 2.62/0.99  --bmc1_pre_inst_next_state              false
% 2.62/0.99  --bmc1_pre_inst_state                   false
% 2.62/0.99  --bmc1_pre_inst_reach_state             false
% 2.62/0.99  --bmc1_out_unsat_core                   false
% 2.62/0.99  --bmc1_aig_witness_out                  false
% 2.62/0.99  --bmc1_verbose                          false
% 2.62/0.99  --bmc1_dump_clauses_tptp                false
% 2.62/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.62/0.99  --bmc1_dump_file                        -
% 2.62/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.62/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.62/0.99  --bmc1_ucm_extend_mode                  1
% 2.62/0.99  --bmc1_ucm_init_mode                    2
% 2.62/0.99  --bmc1_ucm_cone_mode                    none
% 2.62/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.62/0.99  --bmc1_ucm_relax_model                  4
% 2.62/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.62/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.62/0.99  --bmc1_ucm_layered_model                none
% 2.62/0.99  --bmc1_ucm_max_lemma_size               10
% 2.62/0.99  
% 2.62/0.99  ------ AIG Options
% 2.62/0.99  
% 2.62/0.99  --aig_mode                              false
% 2.62/0.99  
% 2.62/0.99  ------ Instantiation Options
% 2.62/0.99  
% 2.62/0.99  --instantiation_flag                    true
% 2.62/0.99  --inst_sos_flag                         false
% 2.62/0.99  --inst_sos_phase                        true
% 2.62/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.62/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.62/0.99  --inst_lit_sel_side                     num_symb
% 2.62/0.99  --inst_solver_per_active                1400
% 2.62/0.99  --inst_solver_calls_frac                1.
% 2.62/0.99  --inst_passive_queue_type               priority_queues
% 2.62/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.62/0.99  --inst_passive_queues_freq              [25;2]
% 2.62/0.99  --inst_dismatching                      true
% 2.62/0.99  --inst_eager_unprocessed_to_passive     true
% 2.62/0.99  --inst_prop_sim_given                   true
% 2.62/0.99  --inst_prop_sim_new                     false
% 2.62/0.99  --inst_subs_new                         false
% 2.62/0.99  --inst_eq_res_simp                      false
% 2.62/0.99  --inst_subs_given                       false
% 2.62/0.99  --inst_orphan_elimination               true
% 2.62/0.99  --inst_learning_loop_flag               true
% 2.62/0.99  --inst_learning_start                   3000
% 2.62/0.99  --inst_learning_factor                  2
% 2.62/0.99  --inst_start_prop_sim_after_learn       3
% 2.62/0.99  --inst_sel_renew                        solver
% 2.62/0.99  --inst_lit_activity_flag                true
% 2.62/0.99  --inst_restr_to_given                   false
% 2.62/0.99  --inst_activity_threshold               500
% 2.62/0.99  --inst_out_proof                        true
% 2.62/0.99  
% 2.62/0.99  ------ Resolution Options
% 2.62/0.99  
% 2.62/0.99  --resolution_flag                       true
% 2.62/0.99  --res_lit_sel                           adaptive
% 2.62/0.99  --res_lit_sel_side                      none
% 2.62/0.99  --res_ordering                          kbo
% 2.62/0.99  --res_to_prop_solver                    active
% 2.62/0.99  --res_prop_simpl_new                    false
% 2.62/0.99  --res_prop_simpl_given                  true
% 2.62/0.99  --res_passive_queue_type                priority_queues
% 2.62/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.62/0.99  --res_passive_queues_freq               [15;5]
% 2.62/0.99  --res_forward_subs                      full
% 2.62/0.99  --res_backward_subs                     full
% 2.62/0.99  --res_forward_subs_resolution           true
% 2.62/0.99  --res_backward_subs_resolution          true
% 2.62/0.99  --res_orphan_elimination                true
% 2.62/0.99  --res_time_limit                        2.
% 2.62/0.99  --res_out_proof                         true
% 2.62/0.99  
% 2.62/0.99  ------ Superposition Options
% 2.62/0.99  
% 2.62/0.99  --superposition_flag                    true
% 2.62/0.99  --sup_passive_queue_type                priority_queues
% 2.62/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.62/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.62/0.99  --demod_completeness_check              fast
% 2.62/0.99  --demod_use_ground                      true
% 2.62/0.99  --sup_to_prop_solver                    passive
% 2.62/0.99  --sup_prop_simpl_new                    true
% 2.62/0.99  --sup_prop_simpl_given                  true
% 2.62/0.99  --sup_fun_splitting                     false
% 2.62/0.99  --sup_smt_interval                      50000
% 2.62/0.99  
% 2.62/0.99  ------ Superposition Simplification Setup
% 2.62/0.99  
% 2.62/0.99  --sup_indices_passive                   []
% 2.62/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.62/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/0.99  --sup_full_bw                           [BwDemod]
% 2.62/0.99  --sup_immed_triv                        [TrivRules]
% 2.62/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.62/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/0.99  --sup_immed_bw_main                     []
% 2.62/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.62/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.62/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.62/0.99  
% 2.62/0.99  ------ Combination Options
% 2.62/0.99  
% 2.62/0.99  --comb_res_mult                         3
% 2.62/0.99  --comb_sup_mult                         2
% 2.62/0.99  --comb_inst_mult                        10
% 2.62/0.99  
% 2.62/0.99  ------ Debug Options
% 2.62/0.99  
% 2.62/0.99  --dbg_backtrace                         false
% 2.62/0.99  --dbg_dump_prop_clauses                 false
% 2.62/0.99  --dbg_dump_prop_clauses_file            -
% 2.62/0.99  --dbg_out_stat                          false
% 2.62/0.99  ------ Parsing...
% 2.62/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.62/0.99  
% 2.62/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.62/0.99  
% 2.62/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.62/0.99  
% 2.62/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.62/0.99  ------ Proving...
% 2.62/0.99  ------ Problem Properties 
% 2.62/0.99  
% 2.62/0.99  
% 2.62/0.99  clauses                                 26
% 2.62/0.99  conjectures                             2
% 2.62/0.99  EPR                                     4
% 2.62/0.99  Horn                                    22
% 2.62/0.99  unary                                   9
% 2.62/0.99  binary                                  8
% 2.62/0.99  lits                                    53
% 2.62/0.99  lits eq                                 19
% 2.62/0.99  fd_pure                                 0
% 2.62/0.99  fd_pseudo                               0
% 2.62/0.99  fd_cond                                 2
% 2.62/0.99  fd_pseudo_cond                          1
% 2.62/0.99  AC symbols                              0
% 2.62/0.99  
% 2.62/0.99  ------ Schedule dynamic 5 is on 
% 2.62/0.99  
% 2.62/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.62/0.99  
% 2.62/0.99  
% 2.62/0.99  ------ 
% 2.62/0.99  Current options:
% 2.62/0.99  ------ 
% 2.62/0.99  
% 2.62/0.99  ------ Input Options
% 2.62/0.99  
% 2.62/0.99  --out_options                           all
% 2.62/0.99  --tptp_safe_out                         true
% 2.62/0.99  --problem_path                          ""
% 2.62/0.99  --include_path                          ""
% 2.62/0.99  --clausifier                            res/vclausify_rel
% 2.62/0.99  --clausifier_options                    --mode clausify
% 2.62/0.99  --stdin                                 false
% 2.62/0.99  --stats_out                             all
% 2.62/0.99  
% 2.62/0.99  ------ General Options
% 2.62/0.99  
% 2.62/0.99  --fof                                   false
% 2.62/0.99  --time_out_real                         305.
% 2.62/0.99  --time_out_virtual                      -1.
% 2.62/0.99  --symbol_type_check                     false
% 2.62/0.99  --clausify_out                          false
% 2.62/0.99  --sig_cnt_out                           false
% 2.62/0.99  --trig_cnt_out                          false
% 2.62/0.99  --trig_cnt_out_tolerance                1.
% 2.62/0.99  --trig_cnt_out_sk_spl                   false
% 2.62/0.99  --abstr_cl_out                          false
% 2.62/0.99  
% 2.62/0.99  ------ Global Options
% 2.62/0.99  
% 2.62/0.99  --schedule                              default
% 2.62/0.99  --add_important_lit                     false
% 2.62/0.99  --prop_solver_per_cl                    1000
% 2.62/0.99  --min_unsat_core                        false
% 2.62/0.99  --soft_assumptions                      false
% 2.62/0.99  --soft_lemma_size                       3
% 2.62/0.99  --prop_impl_unit_size                   0
% 2.62/0.99  --prop_impl_unit                        []
% 2.62/0.99  --share_sel_clauses                     true
% 2.62/0.99  --reset_solvers                         false
% 2.62/0.99  --bc_imp_inh                            [conj_cone]
% 2.62/0.99  --conj_cone_tolerance                   3.
% 2.62/0.99  --extra_neg_conj                        none
% 2.62/0.99  --large_theory_mode                     true
% 2.62/0.99  --prolific_symb_bound                   200
% 2.62/0.99  --lt_threshold                          2000
% 2.62/0.99  --clause_weak_htbl                      true
% 2.62/0.99  --gc_record_bc_elim                     false
% 2.62/0.99  
% 2.62/0.99  ------ Preprocessing Options
% 2.62/0.99  
% 2.62/0.99  --preprocessing_flag                    true
% 2.62/0.99  --time_out_prep_mult                    0.1
% 2.62/0.99  --splitting_mode                        input
% 2.62/0.99  --splitting_grd                         true
% 2.62/0.99  --splitting_cvd                         false
% 2.62/0.99  --splitting_cvd_svl                     false
% 2.62/0.99  --splitting_nvd                         32
% 2.62/0.99  --sub_typing                            true
% 2.62/0.99  --prep_gs_sim                           true
% 2.62/0.99  --prep_unflatten                        true
% 2.62/0.99  --prep_res_sim                          true
% 2.62/0.99  --prep_upred                            true
% 2.62/0.99  --prep_sem_filter                       exhaustive
% 2.62/0.99  --prep_sem_filter_out                   false
% 2.62/0.99  --pred_elim                             true
% 2.62/0.99  --res_sim_input                         true
% 2.62/0.99  --eq_ax_congr_red                       true
% 2.62/0.99  --pure_diseq_elim                       true
% 2.62/0.99  --brand_transform                       false
% 2.62/0.99  --non_eq_to_eq                          false
% 2.62/0.99  --prep_def_merge                        true
% 2.62/0.99  --prep_def_merge_prop_impl              false
% 2.62/0.99  --prep_def_merge_mbd                    true
% 2.62/0.99  --prep_def_merge_tr_red                 false
% 2.62/0.99  --prep_def_merge_tr_cl                  false
% 2.62/0.99  --smt_preprocessing                     true
% 2.62/0.99  --smt_ac_axioms                         fast
% 2.62/0.99  --preprocessed_out                      false
% 2.62/0.99  --preprocessed_stats                    false
% 2.62/0.99  
% 2.62/0.99  ------ Abstraction refinement Options
% 2.62/0.99  
% 2.62/0.99  --abstr_ref                             []
% 2.62/0.99  --abstr_ref_prep                        false
% 2.62/0.99  --abstr_ref_until_sat                   false
% 2.62/0.99  --abstr_ref_sig_restrict                funpre
% 2.62/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.62/0.99  --abstr_ref_under                       []
% 2.62/0.99  
% 2.62/0.99  ------ SAT Options
% 2.62/0.99  
% 2.62/0.99  --sat_mode                              false
% 2.62/0.99  --sat_fm_restart_options                ""
% 2.62/0.99  --sat_gr_def                            false
% 2.62/0.99  --sat_epr_types                         true
% 2.62/0.99  --sat_non_cyclic_types                  false
% 2.62/0.99  --sat_finite_models                     false
% 2.62/0.99  --sat_fm_lemmas                         false
% 2.62/0.99  --sat_fm_prep                           false
% 2.62/0.99  --sat_fm_uc_incr                        true
% 2.62/0.99  --sat_out_model                         small
% 2.62/0.99  --sat_out_clauses                       false
% 2.62/0.99  
% 2.62/0.99  ------ QBF Options
% 2.62/0.99  
% 2.62/0.99  --qbf_mode                              false
% 2.62/0.99  --qbf_elim_univ                         false
% 2.62/0.99  --qbf_dom_inst                          none
% 2.62/0.99  --qbf_dom_pre_inst                      false
% 2.62/0.99  --qbf_sk_in                             false
% 2.62/0.99  --qbf_pred_elim                         true
% 2.62/0.99  --qbf_split                             512
% 2.62/0.99  
% 2.62/0.99  ------ BMC1 Options
% 2.62/0.99  
% 2.62/0.99  --bmc1_incremental                      false
% 2.62/0.99  --bmc1_axioms                           reachable_all
% 2.62/0.99  --bmc1_min_bound                        0
% 2.62/0.99  --bmc1_max_bound                        -1
% 2.62/0.99  --bmc1_max_bound_default                -1
% 2.62/0.99  --bmc1_symbol_reachability              true
% 2.62/0.99  --bmc1_property_lemmas                  false
% 2.62/0.99  --bmc1_k_induction                      false
% 2.62/0.99  --bmc1_non_equiv_states                 false
% 2.62/0.99  --bmc1_deadlock                         false
% 2.62/0.99  --bmc1_ucm                              false
% 2.62/0.99  --bmc1_add_unsat_core                   none
% 2.62/0.99  --bmc1_unsat_core_children              false
% 2.62/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.62/0.99  --bmc1_out_stat                         full
% 2.62/0.99  --bmc1_ground_init                      false
% 2.62/0.99  --bmc1_pre_inst_next_state              false
% 2.62/0.99  --bmc1_pre_inst_state                   false
% 2.62/0.99  --bmc1_pre_inst_reach_state             false
% 2.62/0.99  --bmc1_out_unsat_core                   false
% 2.62/0.99  --bmc1_aig_witness_out                  false
% 2.62/0.99  --bmc1_verbose                          false
% 2.62/0.99  --bmc1_dump_clauses_tptp                false
% 2.62/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.62/0.99  --bmc1_dump_file                        -
% 2.62/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.62/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.62/0.99  --bmc1_ucm_extend_mode                  1
% 2.62/0.99  --bmc1_ucm_init_mode                    2
% 2.62/0.99  --bmc1_ucm_cone_mode                    none
% 2.62/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.62/0.99  --bmc1_ucm_relax_model                  4
% 2.62/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.62/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.62/0.99  --bmc1_ucm_layered_model                none
% 2.62/0.99  --bmc1_ucm_max_lemma_size               10
% 2.62/0.99  
% 2.62/0.99  ------ AIG Options
% 2.62/0.99  
% 2.62/0.99  --aig_mode                              false
% 2.62/0.99  
% 2.62/0.99  ------ Instantiation Options
% 2.62/0.99  
% 2.62/0.99  --instantiation_flag                    true
% 2.62/0.99  --inst_sos_flag                         false
% 2.62/0.99  --inst_sos_phase                        true
% 2.62/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.62/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.62/0.99  --inst_lit_sel_side                     none
% 2.62/0.99  --inst_solver_per_active                1400
% 2.62/0.99  --inst_solver_calls_frac                1.
% 2.62/0.99  --inst_passive_queue_type               priority_queues
% 2.62/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.62/0.99  --inst_passive_queues_freq              [25;2]
% 2.62/0.99  --inst_dismatching                      true
% 2.62/0.99  --inst_eager_unprocessed_to_passive     true
% 2.62/0.99  --inst_prop_sim_given                   true
% 2.62/0.99  --inst_prop_sim_new                     false
% 2.62/0.99  --inst_subs_new                         false
% 2.62/0.99  --inst_eq_res_simp                      false
% 2.62/0.99  --inst_subs_given                       false
% 2.62/0.99  --inst_orphan_elimination               true
% 2.62/0.99  --inst_learning_loop_flag               true
% 2.62/0.99  --inst_learning_start                   3000
% 2.62/0.99  --inst_learning_factor                  2
% 2.62/0.99  --inst_start_prop_sim_after_learn       3
% 2.62/0.99  --inst_sel_renew                        solver
% 2.62/0.99  --inst_lit_activity_flag                true
% 2.62/0.99  --inst_restr_to_given                   false
% 2.62/0.99  --inst_activity_threshold               500
% 2.62/0.99  --inst_out_proof                        true
% 2.62/0.99  
% 2.62/0.99  ------ Resolution Options
% 2.62/0.99  
% 2.62/0.99  --resolution_flag                       false
% 2.62/0.99  --res_lit_sel                           adaptive
% 2.62/0.99  --res_lit_sel_side                      none
% 2.62/0.99  --res_ordering                          kbo
% 2.62/0.99  --res_to_prop_solver                    active
% 2.62/0.99  --res_prop_simpl_new                    false
% 2.62/0.99  --res_prop_simpl_given                  true
% 2.62/0.99  --res_passive_queue_type                priority_queues
% 2.62/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.62/0.99  --res_passive_queues_freq               [15;5]
% 2.62/0.99  --res_forward_subs                      full
% 2.62/0.99  --res_backward_subs                     full
% 2.62/0.99  --res_forward_subs_resolution           true
% 2.62/0.99  --res_backward_subs_resolution          true
% 2.62/0.99  --res_orphan_elimination                true
% 2.62/0.99  --res_time_limit                        2.
% 2.62/0.99  --res_out_proof                         true
% 2.62/0.99  
% 2.62/0.99  ------ Superposition Options
% 2.62/0.99  
% 2.62/0.99  --superposition_flag                    true
% 2.62/0.99  --sup_passive_queue_type                priority_queues
% 2.62/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.62/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.62/0.99  --demod_completeness_check              fast
% 2.62/0.99  --demod_use_ground                      true
% 2.62/0.99  --sup_to_prop_solver                    passive
% 2.62/0.99  --sup_prop_simpl_new                    true
% 2.62/0.99  --sup_prop_simpl_given                  true
% 2.62/0.99  --sup_fun_splitting                     false
% 2.62/0.99  --sup_smt_interval                      50000
% 2.62/0.99  
% 2.62/0.99  ------ Superposition Simplification Setup
% 2.62/0.99  
% 2.62/0.99  --sup_indices_passive                   []
% 2.62/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.62/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/0.99  --sup_full_bw                           [BwDemod]
% 2.62/0.99  --sup_immed_triv                        [TrivRules]
% 2.62/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.62/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/0.99  --sup_immed_bw_main                     []
% 2.62/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.62/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.62/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.62/0.99  
% 2.62/0.99  ------ Combination Options
% 2.62/0.99  
% 2.62/0.99  --comb_res_mult                         3
% 2.62/0.99  --comb_sup_mult                         2
% 2.62/0.99  --comb_inst_mult                        10
% 2.62/0.99  
% 2.62/0.99  ------ Debug Options
% 2.62/0.99  
% 2.62/0.99  --dbg_backtrace                         false
% 2.62/0.99  --dbg_dump_prop_clauses                 false
% 2.62/0.99  --dbg_dump_prop_clauses_file            -
% 2.62/0.99  --dbg_out_stat                          false
% 2.62/0.99  
% 2.62/0.99  
% 2.62/0.99  
% 2.62/0.99  
% 2.62/0.99  ------ Proving...
% 2.62/0.99  
% 2.62/0.99  
% 2.62/0.99  % SZS status Theorem for theBenchmark.p
% 2.62/0.99  
% 2.62/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.62/0.99  
% 2.62/0.99  fof(f7,axiom,(
% 2.62/0.99    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 2.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f45,plain,(
% 2.62/0.99    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK0(X0),X0))),
% 2.62/0.99    introduced(choice_axiom,[])).
% 2.62/0.99  
% 2.62/0.99  fof(f46,plain,(
% 2.62/0.99    ! [X0] : m1_subset_1(sK0(X0),X0)),
% 2.62/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f45])).
% 2.62/0.99  
% 2.62/0.99  fof(f57,plain,(
% 2.62/0.99    ( ! [X0] : (m1_subset_1(sK0(X0),X0)) )),
% 2.62/0.99    inference(cnf_transformation,[],[f46])).
% 2.62/0.99  
% 2.62/0.99  fof(f8,axiom,(
% 2.62/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f24,plain,(
% 2.62/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.62/0.99    inference(ennf_transformation,[],[f8])).
% 2.62/0.99  
% 2.62/0.99  fof(f25,plain,(
% 2.62/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.62/0.99    inference(flattening,[],[f24])).
% 2.62/0.99  
% 2.62/0.99  fof(f58,plain,(
% 2.62/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.62/0.99    inference(cnf_transformation,[],[f25])).
% 2.62/0.99  
% 2.62/0.99  fof(f20,axiom,(
% 2.62/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f40,plain,(
% 2.62/0.99    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.62/0.99    inference(ennf_transformation,[],[f20])).
% 2.62/0.99  
% 2.62/0.99  fof(f76,plain,(
% 2.62/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.62/0.99    inference(cnf_transformation,[],[f40])).
% 2.62/0.99  
% 2.62/0.99  fof(f13,axiom,(
% 2.62/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f30,plain,(
% 2.62/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.62/0.99    inference(ennf_transformation,[],[f13])).
% 2.62/0.99  
% 2.62/0.99  fof(f31,plain,(
% 2.62/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.62/0.99    inference(flattening,[],[f30])).
% 2.62/0.99  
% 2.62/0.99  fof(f64,plain,(
% 2.62/0.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.62/0.99    inference(cnf_transformation,[],[f31])).
% 2.62/0.99  
% 2.62/0.99  fof(f19,axiom,(
% 2.62/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f39,plain,(
% 2.62/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.62/0.99    inference(ennf_transformation,[],[f19])).
% 2.62/0.99  
% 2.62/0.99  fof(f75,plain,(
% 2.62/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.62/0.99    inference(cnf_transformation,[],[f39])).
% 2.62/0.99  
% 2.62/0.99  fof(f22,conjecture,(
% 2.62/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 2.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f23,negated_conjecture,(
% 2.62/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 2.62/0.99    inference(negated_conjecture,[],[f22])).
% 2.62/0.99  
% 2.62/0.99  fof(f43,plain,(
% 2.62/0.99    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 2.62/0.99    inference(ennf_transformation,[],[f23])).
% 2.62/0.99  
% 2.62/0.99  fof(f44,plain,(
% 2.62/0.99    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 2.62/0.99    inference(flattening,[],[f43])).
% 2.62/0.99  
% 2.62/0.99  fof(f49,plain,(
% 2.62/0.99    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK3,sK1),sK2) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3))),
% 2.62/0.99    introduced(choice_axiom,[])).
% 2.62/0.99  
% 2.62/0.99  fof(f50,plain,(
% 2.62/0.99    ~r2_hidden(k1_funct_1(sK3,sK1),sK2) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3)),
% 2.62/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f44,f49])).
% 2.62/0.99  
% 2.62/0.99  fof(f81,plain,(
% 2.62/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 2.62/0.99    inference(cnf_transformation,[],[f50])).
% 2.62/0.99  
% 2.62/0.99  fof(f3,axiom,(
% 2.62/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f53,plain,(
% 2.62/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.62/0.99    inference(cnf_transformation,[],[f3])).
% 2.62/0.99  
% 2.62/0.99  fof(f4,axiom,(
% 2.62/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f54,plain,(
% 2.62/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.62/0.99    inference(cnf_transformation,[],[f4])).
% 2.62/0.99  
% 2.62/0.99  fof(f5,axiom,(
% 2.62/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f55,plain,(
% 2.62/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.62/0.99    inference(cnf_transformation,[],[f5])).
% 2.62/0.99  
% 2.62/0.99  fof(f84,plain,(
% 2.62/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.62/0.99    inference(definition_unfolding,[],[f54,f55])).
% 2.62/0.99  
% 2.62/0.99  fof(f85,plain,(
% 2.62/0.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.62/0.99    inference(definition_unfolding,[],[f53,f84])).
% 2.62/0.99  
% 2.62/0.99  fof(f88,plain,(
% 2.62/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))),
% 2.62/0.99    inference(definition_unfolding,[],[f81,f85])).
% 2.62/0.99  
% 2.62/0.99  fof(f11,axiom,(
% 2.62/0.99    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 2.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f28,plain,(
% 2.62/0.99    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 2.62/0.99    inference(ennf_transformation,[],[f11])).
% 2.62/0.99  
% 2.62/0.99  fof(f61,plain,(
% 2.62/0.99    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 2.62/0.99    inference(cnf_transformation,[],[f28])).
% 2.62/0.99  
% 2.62/0.99  fof(f10,axiom,(
% 2.62/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 2.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f27,plain,(
% 2.62/0.99    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 2.62/0.99    inference(ennf_transformation,[],[f10])).
% 2.62/0.99  
% 2.62/0.99  fof(f60,plain,(
% 2.62/0.99    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 2.62/0.99    inference(cnf_transformation,[],[f27])).
% 2.62/0.99  
% 2.62/0.99  fof(f87,plain,(
% 2.62/0.99    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 2.62/0.99    inference(definition_unfolding,[],[f60,f85])).
% 2.62/0.99  
% 2.62/0.99  fof(f12,axiom,(
% 2.62/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 2.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f29,plain,(
% 2.62/0.99    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 2.62/0.99    inference(ennf_transformation,[],[f12])).
% 2.62/0.99  
% 2.62/0.99  fof(f47,plain,(
% 2.62/0.99    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 2.62/0.99    inference(nnf_transformation,[],[f29])).
% 2.62/0.99  
% 2.62/0.99  fof(f63,plain,(
% 2.62/0.99    ( ! [X0,X1] : (r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.62/0.99    inference(cnf_transformation,[],[f47])).
% 2.62/0.99  
% 2.62/0.99  fof(f77,plain,(
% 2.62/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.62/0.99    inference(cnf_transformation,[],[f40])).
% 2.62/0.99  
% 2.62/0.99  fof(f17,axiom,(
% 2.62/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 2.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f36,plain,(
% 2.62/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.62/0.99    inference(ennf_transformation,[],[f17])).
% 2.62/0.99  
% 2.62/0.99  fof(f37,plain,(
% 2.62/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.62/0.99    inference(flattening,[],[f36])).
% 2.62/0.99  
% 2.62/0.99  fof(f73,plain,(
% 2.62/0.99    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.62/0.99    inference(cnf_transformation,[],[f37])).
% 2.62/0.99  
% 2.62/0.99  fof(f79,plain,(
% 2.62/0.99    v1_funct_1(sK3)),
% 2.62/0.99    inference(cnf_transformation,[],[f50])).
% 2.62/0.99  
% 2.62/0.99  fof(f83,plain,(
% 2.62/0.99    ~r2_hidden(k1_funct_1(sK3,sK1),sK2)),
% 2.62/0.99    inference(cnf_transformation,[],[f50])).
% 2.62/0.99  
% 2.62/0.99  fof(f15,axiom,(
% 2.62/0.99    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f32,plain,(
% 2.62/0.99    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.62/0.99    inference(ennf_transformation,[],[f15])).
% 2.62/0.99  
% 2.62/0.99  fof(f33,plain,(
% 2.62/0.99    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.62/0.99    inference(flattening,[],[f32])).
% 2.62/0.99  
% 2.62/0.99  fof(f68,plain,(
% 2.62/0.99    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.62/0.99    inference(cnf_transformation,[],[f33])).
% 2.62/0.99  
% 2.62/0.99  fof(f21,axiom,(
% 2.62/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 2.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f41,plain,(
% 2.62/0.99    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.62/0.99    inference(ennf_transformation,[],[f21])).
% 2.62/0.99  
% 2.62/0.99  fof(f42,plain,(
% 2.62/0.99    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.62/0.99    inference(flattening,[],[f41])).
% 2.62/0.99  
% 2.62/0.99  fof(f78,plain,(
% 2.62/0.99    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.62/0.99    inference(cnf_transformation,[],[f42])).
% 2.62/0.99  
% 2.62/0.99  fof(f80,plain,(
% 2.62/0.99    v1_funct_2(sK3,k1_tarski(sK1),sK2)),
% 2.62/0.99    inference(cnf_transformation,[],[f50])).
% 2.62/0.99  
% 2.62/0.99  fof(f89,plain,(
% 2.62/0.99    v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2)),
% 2.62/0.99    inference(definition_unfolding,[],[f80,f85])).
% 2.62/0.99  
% 2.62/0.99  fof(f82,plain,(
% 2.62/0.99    k1_xboole_0 != sK2),
% 2.62/0.99    inference(cnf_transformation,[],[f50])).
% 2.62/0.99  
% 2.62/0.99  fof(f16,axiom,(
% 2.62/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 2.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f34,plain,(
% 2.62/0.99    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.62/0.99    inference(ennf_transformation,[],[f16])).
% 2.62/0.99  
% 2.62/0.99  fof(f35,plain,(
% 2.62/0.99    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.62/0.99    inference(flattening,[],[f34])).
% 2.62/0.99  
% 2.62/0.99  fof(f48,plain,(
% 2.62/0.99    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.62/0.99    inference(nnf_transformation,[],[f35])).
% 2.62/0.99  
% 2.62/0.99  fof(f71,plain,(
% 2.62/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2 | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.62/0.99    inference(cnf_transformation,[],[f48])).
% 2.62/0.99  
% 2.62/0.99  fof(f91,plain,(
% 2.62/0.99    ( ! [X0,X1] : (k1_xboole_0 = k1_funct_1(X0,X1) | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.62/0.99    inference(equality_resolution,[],[f71])).
% 2.62/0.99  
% 2.62/0.99  fof(f14,axiom,(
% 2.62/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f65,plain,(
% 2.62/0.99    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.62/0.99    inference(cnf_transformation,[],[f14])).
% 2.62/0.99  
% 2.62/0.99  fof(f2,axiom,(
% 2.62/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f52,plain,(
% 2.62/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.62/0.99    inference(cnf_transformation,[],[f2])).
% 2.62/0.99  
% 2.62/0.99  fof(f18,axiom,(
% 2.62/0.99    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f38,plain,(
% 2.62/0.99    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.62/0.99    inference(ennf_transformation,[],[f18])).
% 2.62/0.99  
% 2.62/0.99  fof(f74,plain,(
% 2.62/0.99    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.62/0.99    inference(cnf_transformation,[],[f38])).
% 2.62/0.99  
% 2.62/0.99  fof(f6,axiom,(
% 2.62/0.99    ! [X0,X1] : ~v1_xboole_0(k2_tarski(X0,X1))),
% 2.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f56,plain,(
% 2.62/0.99    ( ! [X0,X1] : (~v1_xboole_0(k2_tarski(X0,X1))) )),
% 2.62/0.99    inference(cnf_transformation,[],[f6])).
% 2.62/0.99  
% 2.62/0.99  fof(f86,plain,(
% 2.62/0.99    ( ! [X0,X1] : (~v1_xboole_0(k2_enumset1(X0,X0,X0,X1))) )),
% 2.62/0.99    inference(definition_unfolding,[],[f56,f84])).
% 2.62/0.99  
% 2.62/0.99  cnf(c_3,plain,
% 2.62/0.99      ( m1_subset_1(sK0(X0),X0) ),
% 2.62/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_4,plain,
% 2.62/0.99      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 2.62/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_511,plain,
% 2.62/0.99      ( r2_hidden(X0,X1) | v1_xboole_0(X1) | X1 != X2 | sK0(X2) != X0 ),
% 2.62/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_4]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_512,plain,
% 2.62/0.99      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.62/0.99      inference(unflattening,[status(thm)],[c_511]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2057,plain,
% 2.62/0.99      ( r2_hidden(sK0(X0),X0) = iProver_top
% 2.62/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.62/0.99      inference(predicate_to_equality,[status(thm)],[c_512]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_23,plain,
% 2.62/0.99      ( v4_relat_1(X0,X1)
% 2.62/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.62/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_10,plain,
% 2.62/0.99      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.62/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_319,plain,
% 2.62/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.62/0.99      | ~ v1_relat_1(X0)
% 2.62/0.99      | k7_relat_1(X0,X1) = X0 ),
% 2.62/0.99      inference(resolution,[status(thm)],[c_23,c_10]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_21,plain,
% 2.62/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.62/0.99      | v1_relat_1(X0) ),
% 2.62/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_323,plain,
% 2.62/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.62/0.99      | k7_relat_1(X0,X1) = X0 ),
% 2.62/0.99      inference(global_propositional_subsumption,
% 2.62/0.99                [status(thm)],
% 2.62/0.99                [c_319,c_23,c_21,c_10]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_27,negated_conjecture,
% 2.62/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
% 2.62/0.99      inference(cnf_transformation,[],[f88]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_561,plain,
% 2.62/0.99      ( k7_relat_1(X0,X1) = X0
% 2.62/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.62/0.99      | sK3 != X0 ),
% 2.62/0.99      inference(resolution_lifted,[status(thm)],[c_323,c_27]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_562,plain,
% 2.62/0.99      ( k7_relat_1(sK3,X0) = sK3
% 2.62/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.62/0.99      inference(unflattening,[status(thm)],[c_561]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2243,plain,
% 2.62/0.99      ( k7_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) = sK3 ),
% 2.62/0.99      inference(equality_resolution,[status(thm)],[c_562]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_570,plain,
% 2.62/0.99      ( v1_relat_1(X0)
% 2.62/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.62/0.99      | sK3 != X0 ),
% 2.62/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_27]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_571,plain,
% 2.62/0.99      ( v1_relat_1(sK3)
% 2.62/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.62/0.99      inference(unflattening,[status(thm)],[c_570]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2053,plain,
% 2.62/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.62/0.99      | v1_relat_1(sK3) = iProver_top ),
% 2.62/0.99      inference(predicate_to_equality,[status(thm)],[c_571]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1675,plain,( X0 = X0 ),theory(equality) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2227,plain,
% 2.62/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
% 2.62/0.99      inference(instantiation,[status(thm)],[c_1675]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2229,plain,
% 2.62/0.99      ( v1_relat_1(sK3)
% 2.62/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
% 2.62/0.99      inference(instantiation,[status(thm)],[c_571]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2230,plain,
% 2.62/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
% 2.62/0.99      | v1_relat_1(sK3) = iProver_top ),
% 2.62/0.99      inference(predicate_to_equality,[status(thm)],[c_2229]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2267,plain,
% 2.62/0.99      ( v1_relat_1(sK3) = iProver_top ),
% 2.62/0.99      inference(global_propositional_subsumption,
% 2.62/0.99                [status(thm)],
% 2.62/0.99                [c_2053,c_2227,c_2230]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_7,plain,
% 2.62/0.99      ( ~ v1_relat_1(X0)
% 2.62/0.99      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.62/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2068,plain,
% 2.62/0.99      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 2.62/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.62/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2726,plain,
% 2.62/0.99      ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
% 2.62/0.99      inference(superposition,[status(thm)],[c_2267,c_2068]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2811,plain,
% 2.62/0.99      ( k9_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) = k2_relat_1(sK3) ),
% 2.62/0.99      inference(superposition,[status(thm)],[c_2243,c_2726]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_6,plain,
% 2.62/0.99      ( ~ v1_relat_1(X0)
% 2.62/0.99      | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
% 2.62/0.99      inference(cnf_transformation,[],[f87]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2069,plain,
% 2.62/0.99      ( k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1)
% 2.62/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.62/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_3106,plain,
% 2.62/0.99      ( k9_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK3,X0) ),
% 2.62/0.99      inference(superposition,[status(thm)],[c_2267,c_2069]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_3269,plain,
% 2.62/0.99      ( k11_relat_1(sK3,sK1) = k2_relat_1(sK3) ),
% 2.62/0.99      inference(superposition,[status(thm)],[c_2811,c_3106]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_8,plain,
% 2.62/0.99      ( r2_hidden(X0,k1_relat_1(X1))
% 2.62/0.99      | ~ v1_relat_1(X1)
% 2.62/0.99      | k11_relat_1(X1,X0) = k1_xboole_0 ),
% 2.62/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2067,plain,
% 2.62/0.99      ( k11_relat_1(X0,X1) = k1_xboole_0
% 2.62/0.99      | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
% 2.62/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.62/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_22,plain,
% 2.62/0.99      ( v5_relat_1(X0,X1)
% 2.62/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.62/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_19,plain,
% 2.62/0.99      ( ~ v5_relat_1(X0,X1)
% 2.62/0.99      | ~ r2_hidden(X2,k1_relat_1(X0))
% 2.62/0.99      | r2_hidden(k1_funct_1(X0,X2),X1)
% 2.62/0.99      | ~ v1_funct_1(X0)
% 2.62/0.99      | ~ v1_relat_1(X0) ),
% 2.62/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_339,plain,
% 2.62/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.62/0.99      | r2_hidden(k1_funct_1(X1,X0),X2)
% 2.62/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 2.62/0.99      | ~ v1_funct_1(X1)
% 2.62/0.99      | ~ v1_relat_1(X1) ),
% 2.62/0.99      inference(resolution,[status(thm)],[c_22,c_19]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_353,plain,
% 2.62/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.62/0.99      | r2_hidden(k1_funct_1(X1,X0),X2)
% 2.62/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 2.62/0.99      | ~ v1_funct_1(X1) ),
% 2.62/0.99      inference(forward_subsumption_resolution,
% 2.62/0.99                [status(thm)],
% 2.62/0.99                [c_339,c_21]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_29,negated_conjecture,
% 2.62/0.99      ( v1_funct_1(sK3) ),
% 2.62/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_431,plain,
% 2.62/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.62/0.99      | r2_hidden(k1_funct_1(X1,X0),X2)
% 2.62/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 2.62/0.99      | sK3 != X1 ),
% 2.62/0.99      inference(resolution_lifted,[status(thm)],[c_353,c_29]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_432,plain,
% 2.62/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.62/0.99      | r2_hidden(k1_funct_1(sK3,X0),X1)
% 2.62/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.62/0.99      inference(unflattening,[status(thm)],[c_431]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_582,plain,
% 2.62/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.62/0.99      | r2_hidden(k1_funct_1(sK3,X0),X1)
% 2.62/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X1))
% 2.62/0.99      | sK3 != sK3 ),
% 2.62/0.99      inference(resolution_lifted,[status(thm)],[c_27,c_432]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1118,plain,
% 2.62/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.62/0.99      | r2_hidden(k1_funct_1(sK3,X0),X1)
% 2.62/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X1)) ),
% 2.62/0.99      inference(equality_resolution_simp,[status(thm)],[c_582]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2052,plain,
% 2.62/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.62/0.99      | r2_hidden(X2,k1_relat_1(sK3)) != iProver_top
% 2.62/0.99      | r2_hidden(k1_funct_1(sK3,X2),X1) = iProver_top ),
% 2.62/0.99      inference(predicate_to_equality,[status(thm)],[c_1118]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2329,plain,
% 2.62/0.99      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.62/0.99      | r2_hidden(k1_funct_1(sK3,X0),sK2) = iProver_top ),
% 2.62/0.99      inference(equality_resolution,[status(thm)],[c_2052]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_25,negated_conjecture,
% 2.62/0.99      ( ~ r2_hidden(k1_funct_1(sK3,sK1),sK2) ),
% 2.62/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2063,plain,
% 2.62/0.99      ( r2_hidden(k1_funct_1(sK3,sK1),sK2) != iProver_top ),
% 2.62/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2592,plain,
% 2.62/0.99      ( r2_hidden(sK1,k1_relat_1(sK3)) != iProver_top ),
% 2.62/0.99      inference(superposition,[status(thm)],[c_2329,c_2063]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_3191,plain,
% 2.62/0.99      ( k11_relat_1(sK3,sK1) = k1_xboole_0
% 2.62/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.62/0.99      inference(superposition,[status(thm)],[c_2067,c_2592]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_3339,plain,
% 2.62/0.99      ( k11_relat_1(sK3,sK1) = k1_xboole_0 ),
% 2.62/0.99      inference(global_propositional_subsumption,
% 2.62/0.99                [status(thm)],
% 2.62/0.99                [c_3191,c_2227,c_2230]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_3343,plain,
% 2.62/0.99      ( k2_relat_1(sK3) = k1_xboole_0 ),
% 2.62/0.99      inference(light_normalisation,[status(thm)],[c_3269,c_3339]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_13,plain,
% 2.62/0.99      ( ~ v1_relat_1(X0)
% 2.62/0.99      | k2_relat_1(X0) != k1_xboole_0
% 2.62/0.99      | k1_xboole_0 = X0 ),
% 2.62/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2065,plain,
% 2.62/0.99      ( k2_relat_1(X0) != k1_xboole_0
% 2.62/0.99      | k1_xboole_0 = X0
% 2.62/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.62/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_3346,plain,
% 2.62/0.99      ( sK3 = k1_xboole_0 | v1_relat_1(sK3) != iProver_top ),
% 2.62/0.99      inference(superposition,[status(thm)],[c_3343,c_2065]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2351,plain,
% 2.62/0.99      ( ~ v1_relat_1(sK3)
% 2.62/0.99      | k2_relat_1(sK3) != k1_xboole_0
% 2.62/0.99      | k1_xboole_0 = sK3 ),
% 2.62/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2359,plain,
% 2.62/0.99      ( sK3 = sK3 ),
% 2.62/0.99      inference(instantiation,[status(thm)],[c_1675]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1676,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2531,plain,
% 2.62/0.99      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 2.62/0.99      inference(instantiation,[status(thm)],[c_1676]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2802,plain,
% 2.62/0.99      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 2.62/0.99      inference(instantiation,[status(thm)],[c_2531]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2803,plain,
% 2.62/0.99      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 2.62/0.99      inference(instantiation,[status(thm)],[c_2802]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_3504,plain,
% 2.62/0.99      ( sK3 = k1_xboole_0 ),
% 2.62/0.99      inference(global_propositional_subsumption,
% 2.62/0.99                [status(thm)],
% 2.62/0.99                [c_3346,c_2227,c_2229,c_2351,c_2359,c_2803,c_3343]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_24,plain,
% 2.62/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.62/0.99      | ~ r2_hidden(X3,X1)
% 2.62/0.99      | r2_hidden(k1_funct_1(X0,X3),X2)
% 2.62/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.62/0.99      | ~ v1_funct_1(X0)
% 2.62/0.99      | k1_xboole_0 = X2 ),
% 2.62/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_28,negated_conjecture,
% 2.62/0.99      ( v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
% 2.62/0.99      inference(cnf_transformation,[],[f89]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_366,plain,
% 2.62/0.99      ( ~ r2_hidden(X0,X1)
% 2.62/0.99      | r2_hidden(k1_funct_1(X2,X0),X3)
% 2.62/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.62/0.99      | ~ v1_funct_1(X2)
% 2.62/0.99      | k2_enumset1(sK1,sK1,sK1,sK1) != X1
% 2.62/0.99      | sK2 != X3
% 2.62/0.99      | sK3 != X2
% 2.62/0.99      | k1_xboole_0 = X3 ),
% 2.62/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_28]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_367,plain,
% 2.62/0.99      ( ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
% 2.62/0.99      | r2_hidden(k1_funct_1(sK3,X0),sK2)
% 2.62/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
% 2.62/0.99      | ~ v1_funct_1(sK3)
% 2.62/0.99      | k1_xboole_0 = sK2 ),
% 2.62/0.99      inference(unflattening,[status(thm)],[c_366]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_26,negated_conjecture,
% 2.62/0.99      ( k1_xboole_0 != sK2 ),
% 2.62/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_371,plain,
% 2.62/0.99      ( r2_hidden(k1_funct_1(sK3,X0),sK2)
% 2.62/0.99      | ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
% 2.62/0.99      inference(global_propositional_subsumption,
% 2.62/0.99                [status(thm)],
% 2.62/0.99                [c_367,c_29,c_27,c_26]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_372,plain,
% 2.62/0.99      ( ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
% 2.62/0.99      | r2_hidden(k1_funct_1(sK3,X0),sK2) ),
% 2.62/0.99      inference(renaming,[status(thm)],[c_371]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2061,plain,
% 2.62/0.99      ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
% 2.62/0.99      | r2_hidden(k1_funct_1(sK3,X0),sK2) = iProver_top ),
% 2.62/0.99      inference(predicate_to_equality,[status(thm)],[c_372]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_3525,plain,
% 2.62/0.99      ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
% 2.62/0.99      | r2_hidden(k1_funct_1(k1_xboole_0,X0),sK2) = iProver_top ),
% 2.62/0.99      inference(demodulation,[status(thm)],[c_3504,c_2061]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_16,plain,
% 2.62/0.99      ( r2_hidden(X0,k1_relat_1(X1))
% 2.62/0.99      | ~ v1_funct_1(X1)
% 2.62/0.99      | ~ v1_relat_1(X1)
% 2.62/0.99      | k1_funct_1(X1,X0) = k1_xboole_0 ),
% 2.62/0.99      inference(cnf_transformation,[],[f91]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_479,plain,
% 2.62/0.99      ( r2_hidden(X0,k1_relat_1(X1))
% 2.62/0.99      | ~ v1_relat_1(X1)
% 2.62/0.99      | k1_funct_1(X1,X0) = k1_xboole_0
% 2.62/0.99      | sK3 != X1 ),
% 2.62/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_29]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_480,plain,
% 2.62/0.99      ( r2_hidden(X0,k1_relat_1(sK3))
% 2.62/0.99      | ~ v1_relat_1(sK3)
% 2.62/0.99      | k1_funct_1(sK3,X0) = k1_xboole_0 ),
% 2.62/0.99      inference(unflattening,[status(thm)],[c_479]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2058,plain,
% 2.62/0.99      ( k1_funct_1(sK3,X0) = k1_xboole_0
% 2.62/0.99      | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
% 2.62/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.62/0.99      inference(predicate_to_equality,[status(thm)],[c_480]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_481,plain,
% 2.62/0.99      ( k1_funct_1(sK3,X0) = k1_xboole_0
% 2.62/0.99      | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
% 2.62/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.62/0.99      inference(predicate_to_equality,[status(thm)],[c_480]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2470,plain,
% 2.62/0.99      ( r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
% 2.62/0.99      | k1_funct_1(sK3,X0) = k1_xboole_0 ),
% 2.62/0.99      inference(global_propositional_subsumption,
% 2.62/0.99                [status(thm)],
% 2.62/0.99                [c_2058,c_481,c_2227,c_2230]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2471,plain,
% 2.62/0.99      ( k1_funct_1(sK3,X0) = k1_xboole_0
% 2.62/0.99      | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top ),
% 2.62/0.99      inference(renaming,[status(thm)],[c_2470]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_3520,plain,
% 2.62/0.99      ( k1_funct_1(k1_xboole_0,X0) = k1_xboole_0
% 2.62/0.99      | r2_hidden(X0,k1_relat_1(k1_xboole_0)) = iProver_top ),
% 2.62/0.99      inference(demodulation,[status(thm)],[c_3504,c_2471]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_12,plain,
% 2.62/0.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.62/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_3551,plain,
% 2.62/0.99      ( k1_funct_1(k1_xboole_0,X0) = k1_xboole_0
% 2.62/0.99      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 2.62/0.99      inference(light_normalisation,[status(thm)],[c_3520,c_12]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1,plain,
% 2.62/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 2.62/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_20,plain,
% 2.62/0.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 2.62/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_308,plain,
% 2.62/0.99      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 2.62/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_20]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_309,plain,
% 2.62/0.99      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.62/0.99      inference(unflattening,[status(thm)],[c_308]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_310,plain,
% 2.62/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.62/0.99      inference(predicate_to_equality,[status(thm)],[c_309]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_3837,plain,
% 2.62/0.99      ( k1_funct_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.62/0.99      inference(global_propositional_subsumption,
% 2.62/0.99                [status(thm)],
% 2.62/0.99                [c_3551,c_310]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_3994,plain,
% 2.62/0.99      ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
% 2.62/0.99      | r2_hidden(k1_xboole_0,sK2) = iProver_top ),
% 2.62/0.99      inference(light_normalisation,[status(thm)],[c_3525,c_3837]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2596,plain,
% 2.62/0.99      ( k1_funct_1(sK3,sK1) = k1_xboole_0 ),
% 2.62/0.99      inference(superposition,[status(thm)],[c_2471,c_2592]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2649,plain,
% 2.62/0.99      ( r2_hidden(k1_xboole_0,sK2) != iProver_top ),
% 2.62/0.99      inference(demodulation,[status(thm)],[c_2596,c_2063]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_3997,plain,
% 2.62/0.99      ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top ),
% 2.62/0.99      inference(forward_subsumption_resolution,
% 2.62/0.99                [status(thm)],
% 2.62/0.99                [c_3994,c_2649]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_4001,plain,
% 2.62/0.99      ( v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top ),
% 2.62/0.99      inference(superposition,[status(thm)],[c_2057,c_3997]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2,plain,
% 2.62/0.99      ( ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X1)) ),
% 2.62/0.99      inference(cnf_transformation,[],[f86]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2641,plain,
% 2.62/0.99      ( ~ v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1)) ),
% 2.62/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2642,plain,
% 2.62/0.99      ( v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top ),
% 2.62/0.99      inference(predicate_to_equality,[status(thm)],[c_2641]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(contradiction,plain,
% 2.62/0.99      ( $false ),
% 2.62/0.99      inference(minisat,[status(thm)],[c_4001,c_2642]) ).
% 2.62/0.99  
% 2.62/0.99  
% 2.62/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.62/0.99  
% 2.62/0.99  ------                               Statistics
% 2.62/0.99  
% 2.62/0.99  ------ General
% 2.62/0.99  
% 2.62/0.99  abstr_ref_over_cycles:                  0
% 2.62/0.99  abstr_ref_under_cycles:                 0
% 2.62/0.99  gc_basic_clause_elim:                   0
% 2.62/0.99  forced_gc_time:                         0
% 2.62/0.99  parsing_time:                           0.014
% 2.62/0.99  unif_index_cands_time:                  0.
% 2.62/0.99  unif_index_add_time:                    0.
% 2.62/0.99  orderings_time:                         0.
% 2.62/0.99  out_proof_time:                         0.027
% 2.62/0.99  total_time:                             0.191
% 2.62/0.99  num_of_symbols:                         55
% 2.62/0.99  num_of_terms:                           2793
% 2.62/0.99  
% 2.62/0.99  ------ Preprocessing
% 2.62/0.99  
% 2.62/0.99  num_of_splits:                          0
% 2.62/0.99  num_of_split_atoms:                     0
% 2.62/0.99  num_of_reused_defs:                     0
% 2.62/0.99  num_eq_ax_congr_red:                    23
% 2.62/0.99  num_of_sem_filtered_clauses:            1
% 2.62/0.99  num_of_subtypes:                        0
% 2.62/0.99  monotx_restored_types:                  0
% 2.62/0.99  sat_num_of_epr_types:                   0
% 2.62/0.99  sat_num_of_non_cyclic_types:            0
% 2.62/0.99  sat_guarded_non_collapsed_types:        0
% 2.62/0.99  num_pure_diseq_elim:                    0
% 2.62/0.99  simp_replaced_by:                       0
% 2.62/0.99  res_preprocessed:                       138
% 2.62/0.99  prep_upred:                             0
% 2.62/0.99  prep_unflattend:                        63
% 2.62/0.99  smt_new_axioms:                         0
% 2.62/0.99  pred_elim_cands:                        3
% 2.62/0.99  pred_elim:                              6
% 2.62/0.99  pred_elim_cl:                           3
% 2.62/0.99  pred_elim_cycles:                       11
% 2.62/0.99  merged_defs:                            0
% 2.62/0.99  merged_defs_ncl:                        0
% 2.62/0.99  bin_hyper_res:                          0
% 2.62/0.99  prep_cycles:                            4
% 2.62/0.99  pred_elim_time:                         0.034
% 2.62/0.99  splitting_time:                         0.
% 2.62/0.99  sem_filter_time:                        0.
% 2.62/0.99  monotx_time:                            0.001
% 2.62/0.99  subtype_inf_time:                       0.
% 2.62/0.99  
% 2.62/0.99  ------ Problem properties
% 2.62/0.99  
% 2.62/0.99  clauses:                                26
% 2.62/0.99  conjectures:                            2
% 2.62/0.99  epr:                                    4
% 2.62/0.99  horn:                                   22
% 2.62/0.99  ground:                                 6
% 2.62/0.99  unary:                                  9
% 2.62/0.99  binary:                                 8
% 2.62/0.99  lits:                                   53
% 2.62/0.99  lits_eq:                                19
% 2.62/0.99  fd_pure:                                0
% 2.62/0.99  fd_pseudo:                              0
% 2.62/0.99  fd_cond:                                2
% 2.62/0.99  fd_pseudo_cond:                         1
% 2.62/0.99  ac_symbols:                             0
% 2.62/0.99  
% 2.62/0.99  ------ Propositional Solver
% 2.62/0.99  
% 2.62/0.99  prop_solver_calls:                      28
% 2.62/0.99  prop_fast_solver_calls:                 941
% 2.62/0.99  smt_solver_calls:                       0
% 2.62/0.99  smt_fast_solver_calls:                  0
% 2.62/0.99  prop_num_of_clauses:                    1101
% 2.62/0.99  prop_preprocess_simplified:             5195
% 2.62/0.99  prop_fo_subsumed:                       14
% 2.62/0.99  prop_solver_time:                       0.
% 2.62/0.99  smt_solver_time:                        0.
% 2.62/0.99  smt_fast_solver_time:                   0.
% 2.62/0.99  prop_fast_solver_time:                  0.
% 2.62/0.99  prop_unsat_core_time:                   0.
% 2.62/0.99  
% 2.62/0.99  ------ QBF
% 2.62/0.99  
% 2.62/0.99  qbf_q_res:                              0
% 2.62/0.99  qbf_num_tautologies:                    0
% 2.62/0.99  qbf_prep_cycles:                        0
% 2.62/0.99  
% 2.62/0.99  ------ BMC1
% 2.62/0.99  
% 2.62/0.99  bmc1_current_bound:                     -1
% 2.62/0.99  bmc1_last_solved_bound:                 -1
% 2.62/0.99  bmc1_unsat_core_size:                   -1
% 2.62/0.99  bmc1_unsat_core_parents_size:           -1
% 2.62/0.99  bmc1_merge_next_fun:                    0
% 2.62/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.62/0.99  
% 2.62/0.99  ------ Instantiation
% 2.62/0.99  
% 2.62/0.99  inst_num_of_clauses:                    387
% 2.62/0.99  inst_num_in_passive:                    163
% 2.62/0.99  inst_num_in_active:                     206
% 2.62/0.99  inst_num_in_unprocessed:                18
% 2.62/0.99  inst_num_of_loops:                      260
% 2.62/0.99  inst_num_of_learning_restarts:          0
% 2.62/0.99  inst_num_moves_active_passive:          51
% 2.62/0.99  inst_lit_activity:                      0
% 2.62/0.99  inst_lit_activity_moves:                0
% 2.62/0.99  inst_num_tautologies:                   0
% 2.62/0.99  inst_num_prop_implied:                  0
% 2.62/0.99  inst_num_existing_simplified:           0
% 2.62/0.99  inst_num_eq_res_simplified:             0
% 2.62/0.99  inst_num_child_elim:                    0
% 2.62/0.99  inst_num_of_dismatching_blockings:      63
% 2.62/0.99  inst_num_of_non_proper_insts:           271
% 2.62/0.99  inst_num_of_duplicates:                 0
% 2.62/0.99  inst_inst_num_from_inst_to_res:         0
% 2.62/0.99  inst_dismatching_checking_time:         0.
% 2.62/0.99  
% 2.62/0.99  ------ Resolution
% 2.62/0.99  
% 2.62/0.99  res_num_of_clauses:                     0
% 2.62/0.99  res_num_in_passive:                     0
% 2.62/0.99  res_num_in_active:                      0
% 2.62/0.99  res_num_of_loops:                       142
% 2.62/0.99  res_forward_subset_subsumed:            46
% 2.62/0.99  res_backward_subset_subsumed:           0
% 2.62/0.99  res_forward_subsumed:                   0
% 2.62/0.99  res_backward_subsumed:                  0
% 2.62/0.99  res_forward_subsumption_resolution:     1
% 2.62/0.99  res_backward_subsumption_resolution:    0
% 2.62/0.99  res_clause_to_clause_subsumption:       97
% 2.62/0.99  res_orphan_elimination:                 0
% 2.62/0.99  res_tautology_del:                      32
% 2.62/0.99  res_num_eq_res_simplified:              1
% 2.62/0.99  res_num_sel_changes:                    0
% 2.62/0.99  res_moves_from_active_to_pass:          0
% 2.62/0.99  
% 2.62/0.99  ------ Superposition
% 2.62/0.99  
% 2.62/0.99  sup_time_total:                         0.
% 2.62/0.99  sup_time_generating:                    0.
% 2.62/0.99  sup_time_sim_full:                      0.
% 2.62/0.99  sup_time_sim_immed:                     0.
% 2.62/0.99  
% 2.62/0.99  sup_num_of_clauses:                     39
% 2.62/0.99  sup_num_in_active:                      29
% 2.62/0.99  sup_num_in_passive:                     10
% 2.62/0.99  sup_num_of_loops:                       51
% 2.62/0.99  sup_fw_superposition:                   22
% 2.62/0.99  sup_bw_superposition:                   14
% 2.62/0.99  sup_immediate_simplified:               15
% 2.62/0.99  sup_given_eliminated:                   0
% 2.62/0.99  comparisons_done:                       0
% 2.62/0.99  comparisons_avoided:                    0
% 2.62/0.99  
% 2.62/0.99  ------ Simplifications
% 2.62/0.99  
% 2.62/0.99  
% 2.62/0.99  sim_fw_subset_subsumed:                 3
% 2.62/0.99  sim_bw_subset_subsumed:                 0
% 2.62/0.99  sim_fw_subsumed:                        8
% 2.62/0.99  sim_bw_subsumed:                        0
% 2.62/0.99  sim_fw_subsumption_res:                 1
% 2.62/0.99  sim_bw_subsumption_res:                 0
% 2.62/0.99  sim_tautology_del:                      0
% 2.62/0.99  sim_eq_tautology_del:                   2
% 2.62/0.99  sim_eq_res_simp:                        1
% 2.62/0.99  sim_fw_demodulated:                     1
% 2.62/0.99  sim_bw_demodulated:                     23
% 2.62/0.99  sim_light_normalised:                   14
% 2.62/0.99  sim_joinable_taut:                      0
% 2.62/0.99  sim_joinable_simp:                      0
% 2.62/0.99  sim_ac_normalised:                      0
% 2.62/0.99  sim_smt_subsumption:                    0
% 2.62/0.99  
%------------------------------------------------------------------------------
