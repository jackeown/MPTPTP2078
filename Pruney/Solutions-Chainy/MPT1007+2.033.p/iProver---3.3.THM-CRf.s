%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:48 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :  179 (1118 expanded)
%              Number of clauses        :   97 ( 321 expanded)
%              Number of leaves         :   23 ( 253 expanded)
%              Depth                    :   25
%              Number of atoms          :  472 (3092 expanded)
%              Number of equality atoms :  192 (1022 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

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

fof(f41,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f42,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f47,plain,
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

fof(f48,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK1),sK2)
    & k1_xboole_0 != sK2
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
    & v1_funct_2(sK3,k1_tarski(sK1),sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f42,f47])).

fof(f80,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) ),
    inference(cnf_transformation,[],[f48])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f83,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f84,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f52,f83])).

fof(f87,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(definition_unfolding,[],[f80,f84])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f56,f84])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k1_xboole_0 = k11_relat_1(X1,X0) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X1))
      | k1_xboole_0 = k11_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f78,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f82,plain,(
    ~ r2_hidden(k1_funct_1(sK3,sK1),sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f64,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f43])).

fof(f50,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f39])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f79,plain,(
    v1_funct_2(sK3,k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f88,plain,(
    v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
    inference(definition_unfolding,[],[f79,f84])).

fof(f81,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f48])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f85,plain,(
    ! [X0] : ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(definition_unfolding,[],[f55,f84])).

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
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | k1_xboole_0 != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_funct_1(X0,X1)
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f16,axiom,(
    ! [X0] :
      ( v5_ordinal1(k1_xboole_0)
      & v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f72,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f23])).

fof(f70,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f23])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f17,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_396,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_28])).

cnf(c_397,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_1426,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_397])).

cnf(c_1121,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1567,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_1121])).

cnf(c_1569,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_397])).

cnf(c_1570,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1569])).

cnf(c_1601,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1426,c_1567,c_1570])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1436,plain,
    ( k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2448,plain,
    ( k9_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1601,c_1436])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_8,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_334,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_24,c_8])).

cnf(c_338,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_334,c_24,c_22,c_8])).

cnf(c_375,plain,
    ( k7_relat_1(X0,X1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_338,c_28])).

cnf(c_376,plain,
    ( k7_relat_1(sK3,X0) = sK3
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_375])).

cnf(c_1583,plain,
    ( k7_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) = sK3 ),
    inference(equality_resolution,[status(thm)],[c_376])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1435,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2061,plain,
    ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1601,c_1435])).

cnf(c_2190,plain,
    ( k9_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1583,c_2061])).

cnf(c_2639,plain,
    ( k11_relat_1(sK3,sK1) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2448,c_2190])).

cnf(c_6,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k11_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1434,plain,
    ( k11_relat_1(X0,X1) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_17,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X2),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_384,plain,
    ( v5_relat_1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X1))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_28])).

cnf(c_385,plain,
    ( v5_relat_1(sK3,X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X0)) ),
    inference(unflattening,[status(thm)],[c_384])).

cnf(c_434,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | X3 != X2
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X4,X3))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_385])).

cnf(c_435,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,X0),X1)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X1)) ),
    inference(unflattening,[status(thm)],[c_434])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_439,plain,
    ( r2_hidden(k1_funct_1(sK3,X0),X1)
    | ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_435,c_30])).

cnf(c_440,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,X0),X1)
    | ~ v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X1)) ),
    inference(renaming,[status(thm)],[c_439])).

cnf(c_453,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X1)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_440,c_397])).

cnf(c_1425,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | r2_hidden(X2,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_453])).

cnf(c_1865,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),sK2) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1425])).

cnf(c_26,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(sK3,sK1),sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1429,plain,
    ( r2_hidden(k1_funct_1(sK3,sK1),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1937,plain,
    ( r2_hidden(sK1,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1865,c_1429])).

cnf(c_2518,plain,
    ( k11_relat_1(sK3,sK1) = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1434,c_1937])).

cnf(c_2727,plain,
    ( k11_relat_1(sK3,sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2518,c_1567,c_1570])).

cnf(c_2731,plain,
    ( k2_relat_1(sK3) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2639,c_2727])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1432,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2191,plain,
    ( k7_relat_1(sK3,X0) = k1_xboole_0
    | k9_relat_1(sK3,X0) != k1_xboole_0
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2061,c_1432])).

cnf(c_2244,plain,
    ( k7_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) = k1_xboole_0
    | k2_relat_1(sK3) != k1_xboole_0
    | v1_relat_1(k7_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2190,c_2191])).

cnf(c_2245,plain,
    ( k7_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) = k1_xboole_0
    | k2_relat_1(sK3) != k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2244,c_1583])).

cnf(c_2246,plain,
    ( k2_relat_1(sK3) != k1_xboole_0
    | sK3 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2245,c_1583])).

cnf(c_2247,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2246])).

cnf(c_2249,plain,
    ( sK3 = k1_xboole_0
    | k2_relat_1(sK3) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2246,c_1567,c_1569,c_2247])).

cnf(c_2250,plain,
    ( k2_relat_1(sK3) != k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2249])).

cnf(c_2733,plain,
    ( sK3 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2731,c_2250])).

cnf(c_2737,plain,
    ( sK3 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_2733])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1437,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_354,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k2_enumset1(sK1,sK1,sK1,sK1) != X1
    | sK2 != X2
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_29])).

cnf(c_355,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
    | ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
    | r2_hidden(k1_funct_1(sK3,X0),sK2)
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_354])).

cnf(c_27,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_359,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
    | r2_hidden(k1_funct_1(sK3,X0),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_355,c_30,c_28,c_27])).

cnf(c_1427,plain,
    ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_359])).

cnf(c_1794,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_xboole_0
    | r2_hidden(k1_funct_1(sK3,sK0(k2_enumset1(sK1,sK1,sK1,sK1))),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1437,c_1427])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_317,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_3])).

cnf(c_1872,plain,
    ( r2_hidden(k1_funct_1(sK3,sK0(k2_enumset1(sK1,sK1,sK1,sK1))),sK2) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1794,c_317])).

cnf(c_2813,plain,
    ( r2_hidden(k1_funct_1(k1_xboole_0,sK0(k2_enumset1(sK1,sK1,sK1,sK1))),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2737,c_1872])).

cnf(c_13,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_18,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_489,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,X0) = k1_xboole_0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_18])).

cnf(c_490,plain,
    ( r2_hidden(X0,k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | k1_funct_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_489])).

cnf(c_20,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_467,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_18])).

cnf(c_468,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
    | r2_hidden(k4_tarski(X0,k1_funct_1(k1_xboole_0,X0)),k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_467])).

cnf(c_472,plain,
    ( r2_hidden(k4_tarski(X0,k1_funct_1(k1_xboole_0,X0)),k1_xboole_0)
    | ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_468,c_20])).

cnf(c_473,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
    | r2_hidden(k4_tarski(X0,k1_funct_1(k1_xboole_0,X0)),k1_xboole_0) ),
    inference(renaming,[status(thm)],[c_472])).

cnf(c_2,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_21,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_323,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_21])).

cnf(c_324,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_323])).

cnf(c_482,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_473,c_324])).

cnf(c_494,plain,
    ( k1_funct_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_490,c_20,c_482])).

cnf(c_2847,plain,
    ( r2_hidden(k1_xboole_0,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2813,c_494])).

cnf(c_533,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,X0) = k1_xboole_0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_30])).

cnf(c_534,plain,
    ( r2_hidden(X0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_533])).

cnf(c_1421,plain,
    ( k1_funct_1(sK3,X0) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_534])).

cnf(c_535,plain,
    ( k1_funct_1(sK3,X0) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_534])).

cnf(c_1797,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
    | k1_funct_1(sK3,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1421,c_535,c_1567,c_1570])).

cnf(c_1798,plain,
    ( k1_funct_1(sK3,X0) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1797])).

cnf(c_1941,plain,
    ( k1_funct_1(sK3,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1798,c_1937])).

cnf(c_1986,plain,
    ( r2_hidden(k1_xboole_0,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1941,c_1429])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2847,c_1986])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:29:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.19/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/0.98  
% 2.19/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.19/0.98  
% 2.19/0.98  ------  iProver source info
% 2.19/0.98  
% 2.19/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.19/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.19/0.98  git: non_committed_changes: false
% 2.19/0.98  git: last_make_outside_of_git: false
% 2.19/0.98  
% 2.19/0.98  ------ 
% 2.19/0.98  
% 2.19/0.98  ------ Input Options
% 2.19/0.98  
% 2.19/0.98  --out_options                           all
% 2.19/0.98  --tptp_safe_out                         true
% 2.19/0.98  --problem_path                          ""
% 2.19/0.98  --include_path                          ""
% 2.19/0.98  --clausifier                            res/vclausify_rel
% 2.19/0.98  --clausifier_options                    --mode clausify
% 2.19/0.98  --stdin                                 false
% 2.19/0.98  --stats_out                             all
% 2.19/0.98  
% 2.19/0.98  ------ General Options
% 2.19/0.98  
% 2.19/0.98  --fof                                   false
% 2.19/0.98  --time_out_real                         305.
% 2.19/0.98  --time_out_virtual                      -1.
% 2.19/0.98  --symbol_type_check                     false
% 2.19/0.98  --clausify_out                          false
% 2.19/0.98  --sig_cnt_out                           false
% 2.19/0.98  --trig_cnt_out                          false
% 2.19/0.98  --trig_cnt_out_tolerance                1.
% 2.19/0.98  --trig_cnt_out_sk_spl                   false
% 2.19/0.98  --abstr_cl_out                          false
% 2.19/0.98  
% 2.19/0.98  ------ Global Options
% 2.19/0.98  
% 2.19/0.98  --schedule                              default
% 2.19/0.98  --add_important_lit                     false
% 2.19/0.98  --prop_solver_per_cl                    1000
% 2.19/0.98  --min_unsat_core                        false
% 2.19/0.98  --soft_assumptions                      false
% 2.19/0.98  --soft_lemma_size                       3
% 2.19/0.98  --prop_impl_unit_size                   0
% 2.19/0.98  --prop_impl_unit                        []
% 2.19/0.98  --share_sel_clauses                     true
% 2.19/0.98  --reset_solvers                         false
% 2.19/0.98  --bc_imp_inh                            [conj_cone]
% 2.19/0.98  --conj_cone_tolerance                   3.
% 2.19/0.98  --extra_neg_conj                        none
% 2.19/0.98  --large_theory_mode                     true
% 2.19/0.98  --prolific_symb_bound                   200
% 2.19/0.98  --lt_threshold                          2000
% 2.19/0.98  --clause_weak_htbl                      true
% 2.19/0.98  --gc_record_bc_elim                     false
% 2.19/0.98  
% 2.19/0.98  ------ Preprocessing Options
% 2.19/0.98  
% 2.19/0.98  --preprocessing_flag                    true
% 2.19/0.98  --time_out_prep_mult                    0.1
% 2.19/0.98  --splitting_mode                        input
% 2.19/0.98  --splitting_grd                         true
% 2.19/0.98  --splitting_cvd                         false
% 2.19/0.98  --splitting_cvd_svl                     false
% 2.19/0.98  --splitting_nvd                         32
% 2.19/0.98  --sub_typing                            true
% 2.19/0.98  --prep_gs_sim                           true
% 2.19/0.98  --prep_unflatten                        true
% 2.19/0.98  --prep_res_sim                          true
% 2.19/0.98  --prep_upred                            true
% 2.19/0.98  --prep_sem_filter                       exhaustive
% 2.19/0.98  --prep_sem_filter_out                   false
% 2.19/0.98  --pred_elim                             true
% 2.19/0.98  --res_sim_input                         true
% 2.19/0.98  --eq_ax_congr_red                       true
% 2.19/0.98  --pure_diseq_elim                       true
% 2.19/0.98  --brand_transform                       false
% 2.19/0.98  --non_eq_to_eq                          false
% 2.19/0.98  --prep_def_merge                        true
% 2.19/0.98  --prep_def_merge_prop_impl              false
% 2.19/0.98  --prep_def_merge_mbd                    true
% 2.19/0.98  --prep_def_merge_tr_red                 false
% 2.19/0.98  --prep_def_merge_tr_cl                  false
% 2.19/0.98  --smt_preprocessing                     true
% 2.19/0.98  --smt_ac_axioms                         fast
% 2.19/0.98  --preprocessed_out                      false
% 2.19/0.98  --preprocessed_stats                    false
% 2.19/0.98  
% 2.19/0.98  ------ Abstraction refinement Options
% 2.19/0.98  
% 2.19/0.98  --abstr_ref                             []
% 2.19/0.98  --abstr_ref_prep                        false
% 2.19/0.98  --abstr_ref_until_sat                   false
% 2.19/0.98  --abstr_ref_sig_restrict                funpre
% 2.19/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.19/0.98  --abstr_ref_under                       []
% 2.19/0.98  
% 2.19/0.98  ------ SAT Options
% 2.19/0.98  
% 2.19/0.98  --sat_mode                              false
% 2.19/0.98  --sat_fm_restart_options                ""
% 2.19/0.98  --sat_gr_def                            false
% 2.19/0.98  --sat_epr_types                         true
% 2.19/0.98  --sat_non_cyclic_types                  false
% 2.19/0.98  --sat_finite_models                     false
% 2.19/0.98  --sat_fm_lemmas                         false
% 2.19/0.98  --sat_fm_prep                           false
% 2.19/0.98  --sat_fm_uc_incr                        true
% 2.19/0.98  --sat_out_model                         small
% 2.19/0.98  --sat_out_clauses                       false
% 2.19/0.98  
% 2.19/0.98  ------ QBF Options
% 2.19/0.98  
% 2.19/0.98  --qbf_mode                              false
% 2.19/0.98  --qbf_elim_univ                         false
% 2.19/0.98  --qbf_dom_inst                          none
% 2.19/0.98  --qbf_dom_pre_inst                      false
% 2.19/0.98  --qbf_sk_in                             false
% 2.19/0.98  --qbf_pred_elim                         true
% 2.19/0.98  --qbf_split                             512
% 2.19/0.98  
% 2.19/0.98  ------ BMC1 Options
% 2.19/0.98  
% 2.19/0.98  --bmc1_incremental                      false
% 2.19/0.98  --bmc1_axioms                           reachable_all
% 2.19/0.98  --bmc1_min_bound                        0
% 2.19/0.98  --bmc1_max_bound                        -1
% 2.19/0.98  --bmc1_max_bound_default                -1
% 2.19/0.98  --bmc1_symbol_reachability              true
% 2.19/0.98  --bmc1_property_lemmas                  false
% 2.19/0.98  --bmc1_k_induction                      false
% 2.19/0.98  --bmc1_non_equiv_states                 false
% 2.19/0.98  --bmc1_deadlock                         false
% 2.19/0.98  --bmc1_ucm                              false
% 2.19/0.98  --bmc1_add_unsat_core                   none
% 2.19/0.98  --bmc1_unsat_core_children              false
% 2.19/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.19/0.98  --bmc1_out_stat                         full
% 2.19/0.98  --bmc1_ground_init                      false
% 2.19/0.98  --bmc1_pre_inst_next_state              false
% 2.19/0.98  --bmc1_pre_inst_state                   false
% 2.19/0.98  --bmc1_pre_inst_reach_state             false
% 2.19/0.98  --bmc1_out_unsat_core                   false
% 2.19/0.98  --bmc1_aig_witness_out                  false
% 2.19/0.98  --bmc1_verbose                          false
% 2.19/0.98  --bmc1_dump_clauses_tptp                false
% 2.19/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.19/0.98  --bmc1_dump_file                        -
% 2.19/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.19/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.19/0.98  --bmc1_ucm_extend_mode                  1
% 2.19/0.98  --bmc1_ucm_init_mode                    2
% 2.19/0.98  --bmc1_ucm_cone_mode                    none
% 2.19/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.19/0.98  --bmc1_ucm_relax_model                  4
% 2.19/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.19/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.19/0.98  --bmc1_ucm_layered_model                none
% 2.19/0.98  --bmc1_ucm_max_lemma_size               10
% 2.19/0.98  
% 2.19/0.98  ------ AIG Options
% 2.19/0.98  
% 2.19/0.98  --aig_mode                              false
% 2.19/0.98  
% 2.19/0.98  ------ Instantiation Options
% 2.19/0.98  
% 2.19/0.98  --instantiation_flag                    true
% 2.19/0.98  --inst_sos_flag                         false
% 2.19/0.98  --inst_sos_phase                        true
% 2.19/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.19/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.19/0.98  --inst_lit_sel_side                     num_symb
% 2.19/0.98  --inst_solver_per_active                1400
% 2.19/0.98  --inst_solver_calls_frac                1.
% 2.19/0.98  --inst_passive_queue_type               priority_queues
% 2.19/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.19/0.98  --inst_passive_queues_freq              [25;2]
% 2.19/0.98  --inst_dismatching                      true
% 2.19/0.98  --inst_eager_unprocessed_to_passive     true
% 2.19/0.98  --inst_prop_sim_given                   true
% 2.19/0.98  --inst_prop_sim_new                     false
% 2.19/0.98  --inst_subs_new                         false
% 2.19/0.98  --inst_eq_res_simp                      false
% 2.19/0.98  --inst_subs_given                       false
% 2.19/0.98  --inst_orphan_elimination               true
% 2.19/0.98  --inst_learning_loop_flag               true
% 2.19/0.98  --inst_learning_start                   3000
% 2.19/0.98  --inst_learning_factor                  2
% 2.19/0.98  --inst_start_prop_sim_after_learn       3
% 2.19/0.98  --inst_sel_renew                        solver
% 2.19/0.98  --inst_lit_activity_flag                true
% 2.19/0.98  --inst_restr_to_given                   false
% 2.19/0.98  --inst_activity_threshold               500
% 2.19/0.98  --inst_out_proof                        true
% 2.19/0.98  
% 2.19/0.98  ------ Resolution Options
% 2.19/0.98  
% 2.19/0.98  --resolution_flag                       true
% 2.19/0.98  --res_lit_sel                           adaptive
% 2.19/0.98  --res_lit_sel_side                      none
% 2.19/0.98  --res_ordering                          kbo
% 2.19/0.98  --res_to_prop_solver                    active
% 2.19/0.98  --res_prop_simpl_new                    false
% 2.19/0.98  --res_prop_simpl_given                  true
% 2.19/0.98  --res_passive_queue_type                priority_queues
% 2.19/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.19/0.98  --res_passive_queues_freq               [15;5]
% 2.19/0.98  --res_forward_subs                      full
% 2.19/0.98  --res_backward_subs                     full
% 2.19/0.98  --res_forward_subs_resolution           true
% 2.19/0.98  --res_backward_subs_resolution          true
% 2.19/0.98  --res_orphan_elimination                true
% 2.19/0.98  --res_time_limit                        2.
% 2.19/0.98  --res_out_proof                         true
% 2.19/0.98  
% 2.19/0.98  ------ Superposition Options
% 2.19/0.98  
% 2.19/0.98  --superposition_flag                    true
% 2.19/0.98  --sup_passive_queue_type                priority_queues
% 2.19/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.19/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.19/0.98  --demod_completeness_check              fast
% 2.19/0.98  --demod_use_ground                      true
% 2.19/0.98  --sup_to_prop_solver                    passive
% 2.19/0.98  --sup_prop_simpl_new                    true
% 2.19/0.98  --sup_prop_simpl_given                  true
% 2.19/0.98  --sup_fun_splitting                     false
% 2.19/0.98  --sup_smt_interval                      50000
% 2.19/0.98  
% 2.19/0.98  ------ Superposition Simplification Setup
% 2.19/0.98  
% 2.19/0.98  --sup_indices_passive                   []
% 2.19/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.19/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/0.98  --sup_full_bw                           [BwDemod]
% 2.19/0.98  --sup_immed_triv                        [TrivRules]
% 2.19/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.19/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/0.98  --sup_immed_bw_main                     []
% 2.19/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.19/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/0.98  
% 2.19/0.98  ------ Combination Options
% 2.19/0.98  
% 2.19/0.98  --comb_res_mult                         3
% 2.19/0.98  --comb_sup_mult                         2
% 2.19/0.98  --comb_inst_mult                        10
% 2.19/0.98  
% 2.19/0.98  ------ Debug Options
% 2.19/0.98  
% 2.19/0.98  --dbg_backtrace                         false
% 2.19/0.98  --dbg_dump_prop_clauses                 false
% 2.19/0.98  --dbg_dump_prop_clauses_file            -
% 2.19/0.98  --dbg_out_stat                          false
% 2.19/0.98  ------ Parsing...
% 2.19/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.19/0.98  
% 2.19/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.19/0.98  
% 2.19/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.19/0.98  
% 2.19/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.19/0.98  ------ Proving...
% 2.19/0.98  ------ Problem Properties 
% 2.19/0.98  
% 2.19/0.98  
% 2.19/0.98  clauses                                 23
% 2.19/0.98  conjectures                             2
% 2.19/0.98  EPR                                     3
% 2.19/0.98  Horn                                    20
% 2.19/0.98  unary                                   9
% 2.19/0.98  binary                                  6
% 2.19/0.98  lits                                    46
% 2.19/0.98  lits eq                                 20
% 2.19/0.98  fd_pure                                 0
% 2.19/0.98  fd_pseudo                               0
% 2.19/0.98  fd_cond                                 3
% 2.19/0.98  fd_pseudo_cond                          1
% 2.19/0.98  AC symbols                              0
% 2.19/0.98  
% 2.19/0.98  ------ Schedule dynamic 5 is on 
% 2.19/0.98  
% 2.19/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.19/0.98  
% 2.19/0.98  
% 2.19/0.98  ------ 
% 2.19/0.98  Current options:
% 2.19/0.98  ------ 
% 2.19/0.98  
% 2.19/0.98  ------ Input Options
% 2.19/0.98  
% 2.19/0.98  --out_options                           all
% 2.19/0.98  --tptp_safe_out                         true
% 2.19/0.98  --problem_path                          ""
% 2.19/0.98  --include_path                          ""
% 2.19/0.98  --clausifier                            res/vclausify_rel
% 2.19/0.98  --clausifier_options                    --mode clausify
% 2.19/0.98  --stdin                                 false
% 2.19/0.98  --stats_out                             all
% 2.19/0.98  
% 2.19/0.98  ------ General Options
% 2.19/0.98  
% 2.19/0.98  --fof                                   false
% 2.19/0.98  --time_out_real                         305.
% 2.19/0.98  --time_out_virtual                      -1.
% 2.19/0.98  --symbol_type_check                     false
% 2.19/0.98  --clausify_out                          false
% 2.19/0.98  --sig_cnt_out                           false
% 2.19/0.98  --trig_cnt_out                          false
% 2.19/0.98  --trig_cnt_out_tolerance                1.
% 2.19/0.98  --trig_cnt_out_sk_spl                   false
% 2.19/0.98  --abstr_cl_out                          false
% 2.19/0.98  
% 2.19/0.98  ------ Global Options
% 2.19/0.98  
% 2.19/0.98  --schedule                              default
% 2.19/0.98  --add_important_lit                     false
% 2.19/0.98  --prop_solver_per_cl                    1000
% 2.19/0.98  --min_unsat_core                        false
% 2.19/0.98  --soft_assumptions                      false
% 2.19/0.98  --soft_lemma_size                       3
% 2.19/0.98  --prop_impl_unit_size                   0
% 2.19/0.98  --prop_impl_unit                        []
% 2.19/0.98  --share_sel_clauses                     true
% 2.19/0.98  --reset_solvers                         false
% 2.19/0.98  --bc_imp_inh                            [conj_cone]
% 2.19/0.98  --conj_cone_tolerance                   3.
% 2.19/0.98  --extra_neg_conj                        none
% 2.19/0.98  --large_theory_mode                     true
% 2.19/0.98  --prolific_symb_bound                   200
% 2.19/0.98  --lt_threshold                          2000
% 2.19/0.98  --clause_weak_htbl                      true
% 2.19/0.98  --gc_record_bc_elim                     false
% 2.19/0.98  
% 2.19/0.98  ------ Preprocessing Options
% 2.19/0.98  
% 2.19/0.98  --preprocessing_flag                    true
% 2.19/0.98  --time_out_prep_mult                    0.1
% 2.19/0.98  --splitting_mode                        input
% 2.19/0.98  --splitting_grd                         true
% 2.19/0.98  --splitting_cvd                         false
% 2.19/0.98  --splitting_cvd_svl                     false
% 2.19/0.98  --splitting_nvd                         32
% 2.19/0.98  --sub_typing                            true
% 2.19/0.98  --prep_gs_sim                           true
% 2.19/0.98  --prep_unflatten                        true
% 2.19/0.98  --prep_res_sim                          true
% 2.19/0.98  --prep_upred                            true
% 2.19/0.98  --prep_sem_filter                       exhaustive
% 2.19/0.98  --prep_sem_filter_out                   false
% 2.19/0.98  --pred_elim                             true
% 2.19/0.98  --res_sim_input                         true
% 2.19/0.98  --eq_ax_congr_red                       true
% 2.19/0.98  --pure_diseq_elim                       true
% 2.19/0.98  --brand_transform                       false
% 2.19/0.98  --non_eq_to_eq                          false
% 2.19/0.98  --prep_def_merge                        true
% 2.19/0.98  --prep_def_merge_prop_impl              false
% 2.19/0.98  --prep_def_merge_mbd                    true
% 2.19/0.98  --prep_def_merge_tr_red                 false
% 2.19/0.98  --prep_def_merge_tr_cl                  false
% 2.19/0.98  --smt_preprocessing                     true
% 2.19/0.98  --smt_ac_axioms                         fast
% 2.19/0.98  --preprocessed_out                      false
% 2.19/0.98  --preprocessed_stats                    false
% 2.19/0.98  
% 2.19/0.98  ------ Abstraction refinement Options
% 2.19/0.98  
% 2.19/0.98  --abstr_ref                             []
% 2.19/0.98  --abstr_ref_prep                        false
% 2.19/0.98  --abstr_ref_until_sat                   false
% 2.19/0.98  --abstr_ref_sig_restrict                funpre
% 2.19/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.19/0.98  --abstr_ref_under                       []
% 2.19/0.98  
% 2.19/0.98  ------ SAT Options
% 2.19/0.98  
% 2.19/0.98  --sat_mode                              false
% 2.19/0.98  --sat_fm_restart_options                ""
% 2.19/0.98  --sat_gr_def                            false
% 2.19/0.98  --sat_epr_types                         true
% 2.19/0.98  --sat_non_cyclic_types                  false
% 2.19/0.98  --sat_finite_models                     false
% 2.19/0.98  --sat_fm_lemmas                         false
% 2.19/0.98  --sat_fm_prep                           false
% 2.19/0.98  --sat_fm_uc_incr                        true
% 2.19/0.98  --sat_out_model                         small
% 2.19/0.98  --sat_out_clauses                       false
% 2.19/0.98  
% 2.19/0.98  ------ QBF Options
% 2.19/0.98  
% 2.19/0.98  --qbf_mode                              false
% 2.19/0.98  --qbf_elim_univ                         false
% 2.19/0.98  --qbf_dom_inst                          none
% 2.19/0.98  --qbf_dom_pre_inst                      false
% 2.19/0.98  --qbf_sk_in                             false
% 2.19/0.98  --qbf_pred_elim                         true
% 2.19/0.98  --qbf_split                             512
% 2.19/0.98  
% 2.19/0.98  ------ BMC1 Options
% 2.19/0.98  
% 2.19/0.98  --bmc1_incremental                      false
% 2.19/0.98  --bmc1_axioms                           reachable_all
% 2.19/0.98  --bmc1_min_bound                        0
% 2.19/0.98  --bmc1_max_bound                        -1
% 2.19/0.98  --bmc1_max_bound_default                -1
% 2.19/0.98  --bmc1_symbol_reachability              true
% 2.19/0.98  --bmc1_property_lemmas                  false
% 2.19/0.98  --bmc1_k_induction                      false
% 2.19/0.98  --bmc1_non_equiv_states                 false
% 2.19/0.98  --bmc1_deadlock                         false
% 2.19/0.98  --bmc1_ucm                              false
% 2.19/0.98  --bmc1_add_unsat_core                   none
% 2.19/0.98  --bmc1_unsat_core_children              false
% 2.19/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.19/0.98  --bmc1_out_stat                         full
% 2.19/0.98  --bmc1_ground_init                      false
% 2.19/0.98  --bmc1_pre_inst_next_state              false
% 2.19/0.98  --bmc1_pre_inst_state                   false
% 2.19/0.98  --bmc1_pre_inst_reach_state             false
% 2.19/0.98  --bmc1_out_unsat_core                   false
% 2.19/0.98  --bmc1_aig_witness_out                  false
% 2.19/0.98  --bmc1_verbose                          false
% 2.19/0.98  --bmc1_dump_clauses_tptp                false
% 2.19/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.19/0.98  --bmc1_dump_file                        -
% 2.19/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.19/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.19/0.98  --bmc1_ucm_extend_mode                  1
% 2.19/0.98  --bmc1_ucm_init_mode                    2
% 2.19/0.98  --bmc1_ucm_cone_mode                    none
% 2.19/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.19/0.98  --bmc1_ucm_relax_model                  4
% 2.19/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.19/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.19/0.98  --bmc1_ucm_layered_model                none
% 2.19/0.98  --bmc1_ucm_max_lemma_size               10
% 2.19/0.98  
% 2.19/0.98  ------ AIG Options
% 2.19/0.98  
% 2.19/0.98  --aig_mode                              false
% 2.19/0.98  
% 2.19/0.98  ------ Instantiation Options
% 2.19/0.98  
% 2.19/0.98  --instantiation_flag                    true
% 2.19/0.98  --inst_sos_flag                         false
% 2.19/0.98  --inst_sos_phase                        true
% 2.19/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.19/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.19/0.98  --inst_lit_sel_side                     none
% 2.19/0.98  --inst_solver_per_active                1400
% 2.19/0.98  --inst_solver_calls_frac                1.
% 2.19/0.98  --inst_passive_queue_type               priority_queues
% 2.19/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.19/0.98  --inst_passive_queues_freq              [25;2]
% 2.19/0.98  --inst_dismatching                      true
% 2.19/0.98  --inst_eager_unprocessed_to_passive     true
% 2.19/0.98  --inst_prop_sim_given                   true
% 2.19/0.98  --inst_prop_sim_new                     false
% 2.19/0.98  --inst_subs_new                         false
% 2.19/0.98  --inst_eq_res_simp                      false
% 2.19/0.98  --inst_subs_given                       false
% 2.19/0.98  --inst_orphan_elimination               true
% 2.19/0.98  --inst_learning_loop_flag               true
% 2.19/0.98  --inst_learning_start                   3000
% 2.19/0.98  --inst_learning_factor                  2
% 2.19/0.98  --inst_start_prop_sim_after_learn       3
% 2.19/0.98  --inst_sel_renew                        solver
% 2.19/0.98  --inst_lit_activity_flag                true
% 2.19/0.98  --inst_restr_to_given                   false
% 2.19/0.98  --inst_activity_threshold               500
% 2.19/0.98  --inst_out_proof                        true
% 2.19/0.98  
% 2.19/0.98  ------ Resolution Options
% 2.19/0.98  
% 2.19/0.98  --resolution_flag                       false
% 2.19/0.98  --res_lit_sel                           adaptive
% 2.19/0.98  --res_lit_sel_side                      none
% 2.19/0.98  --res_ordering                          kbo
% 2.19/0.98  --res_to_prop_solver                    active
% 2.19/0.98  --res_prop_simpl_new                    false
% 2.19/0.98  --res_prop_simpl_given                  true
% 2.19/0.98  --res_passive_queue_type                priority_queues
% 2.19/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.19/0.98  --res_passive_queues_freq               [15;5]
% 2.19/0.98  --res_forward_subs                      full
% 2.19/0.98  --res_backward_subs                     full
% 2.19/0.98  --res_forward_subs_resolution           true
% 2.19/0.98  --res_backward_subs_resolution          true
% 2.19/0.98  --res_orphan_elimination                true
% 2.19/0.98  --res_time_limit                        2.
% 2.19/0.98  --res_out_proof                         true
% 2.19/0.98  
% 2.19/0.98  ------ Superposition Options
% 2.19/0.98  
% 2.19/0.98  --superposition_flag                    true
% 2.19/0.98  --sup_passive_queue_type                priority_queues
% 2.19/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.19/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.19/0.98  --demod_completeness_check              fast
% 2.19/0.98  --demod_use_ground                      true
% 2.19/0.98  --sup_to_prop_solver                    passive
% 2.19/0.98  --sup_prop_simpl_new                    true
% 2.19/0.98  --sup_prop_simpl_given                  true
% 2.19/0.98  --sup_fun_splitting                     false
% 2.19/0.98  --sup_smt_interval                      50000
% 2.19/0.98  
% 2.19/0.98  ------ Superposition Simplification Setup
% 2.19/0.98  
% 2.19/0.98  --sup_indices_passive                   []
% 2.19/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.19/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/0.98  --sup_full_bw                           [BwDemod]
% 2.19/0.98  --sup_immed_triv                        [TrivRules]
% 2.19/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.19/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/0.98  --sup_immed_bw_main                     []
% 2.19/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.19/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/0.98  
% 2.19/0.98  ------ Combination Options
% 2.19/0.98  
% 2.19/0.98  --comb_res_mult                         3
% 2.19/0.98  --comb_sup_mult                         2
% 2.19/0.98  --comb_inst_mult                        10
% 2.19/0.98  
% 2.19/0.98  ------ Debug Options
% 2.19/0.98  
% 2.19/0.98  --dbg_backtrace                         false
% 2.19/0.98  --dbg_dump_prop_clauses                 false
% 2.19/0.98  --dbg_dump_prop_clauses_file            -
% 2.19/0.98  --dbg_out_stat                          false
% 2.19/0.98  
% 2.19/0.98  
% 2.19/0.98  
% 2.19/0.98  
% 2.19/0.98  ------ Proving...
% 2.19/0.98  
% 2.19/0.98  
% 2.19/0.98  % SZS status Theorem for theBenchmark.p
% 2.19/0.98  
% 2.19/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.19/0.98  
% 2.19/0.98  fof(f18,axiom,(
% 2.19/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.19/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/0.98  
% 2.19/0.98  fof(f37,plain,(
% 2.19/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.19/0.98    inference(ennf_transformation,[],[f18])).
% 2.19/0.98  
% 2.19/0.98  fof(f74,plain,(
% 2.19/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.19/0.98    inference(cnf_transformation,[],[f37])).
% 2.19/0.98  
% 2.19/0.98  fof(f21,conjecture,(
% 2.19/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 2.19/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/0.98  
% 2.19/0.98  fof(f22,negated_conjecture,(
% 2.19/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 2.19/0.98    inference(negated_conjecture,[],[f21])).
% 2.19/0.98  
% 2.19/0.98  fof(f41,plain,(
% 2.19/0.98    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 2.19/0.98    inference(ennf_transformation,[],[f22])).
% 2.19/0.98  
% 2.19/0.98  fof(f42,plain,(
% 2.19/0.98    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 2.19/0.98    inference(flattening,[],[f41])).
% 2.19/0.98  
% 2.19/0.98  fof(f47,plain,(
% 2.19/0.98    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK3,sK1),sK2) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3))),
% 2.19/0.98    introduced(choice_axiom,[])).
% 2.19/0.98  
% 2.19/0.98  fof(f48,plain,(
% 2.19/0.98    ~r2_hidden(k1_funct_1(sK3,sK1),sK2) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3)),
% 2.19/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f42,f47])).
% 2.19/0.98  
% 2.19/0.98  fof(f80,plain,(
% 2.19/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 2.19/0.98    inference(cnf_transformation,[],[f48])).
% 2.19/0.98  
% 2.19/0.98  fof(f4,axiom,(
% 2.19/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.19/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/0.98  
% 2.19/0.98  fof(f52,plain,(
% 2.19/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.19/0.98    inference(cnf_transformation,[],[f4])).
% 2.19/0.98  
% 2.19/0.98  fof(f5,axiom,(
% 2.19/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.19/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/0.98  
% 2.19/0.98  fof(f53,plain,(
% 2.19/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.19/0.98    inference(cnf_transformation,[],[f5])).
% 2.19/0.98  
% 2.19/0.98  fof(f6,axiom,(
% 2.19/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.19/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/0.98  
% 2.19/0.98  fof(f54,plain,(
% 2.19/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.19/0.98    inference(cnf_transformation,[],[f6])).
% 2.19/0.98  
% 2.19/0.98  fof(f83,plain,(
% 2.19/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.19/0.98    inference(definition_unfolding,[],[f53,f54])).
% 2.19/0.98  
% 2.19/0.98  fof(f84,plain,(
% 2.19/0.98    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.19/0.98    inference(definition_unfolding,[],[f52,f83])).
% 2.19/0.98  
% 2.19/0.98  fof(f87,plain,(
% 2.19/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))),
% 2.19/0.98    inference(definition_unfolding,[],[f80,f84])).
% 2.19/0.98  
% 2.19/0.98  fof(f8,axiom,(
% 2.19/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 2.19/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/0.98  
% 2.19/0.98  fof(f25,plain,(
% 2.19/0.98    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 2.19/0.98    inference(ennf_transformation,[],[f8])).
% 2.19/0.98  
% 2.19/0.98  fof(f56,plain,(
% 2.19/0.98    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 2.19/0.98    inference(cnf_transformation,[],[f25])).
% 2.19/0.98  
% 2.19/0.98  fof(f86,plain,(
% 2.19/0.98    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 2.19/0.98    inference(definition_unfolding,[],[f56,f84])).
% 2.19/0.98  
% 2.19/0.98  fof(f19,axiom,(
% 2.19/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.19/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/0.98  
% 2.19/0.98  fof(f38,plain,(
% 2.19/0.98    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.19/0.98    inference(ennf_transformation,[],[f19])).
% 2.19/0.98  
% 2.19/0.98  fof(f75,plain,(
% 2.19/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.19/0.98    inference(cnf_transformation,[],[f38])).
% 2.19/0.98  
% 2.19/0.98  fof(f11,axiom,(
% 2.19/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.19/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/0.98  
% 2.19/0.98  fof(f28,plain,(
% 2.19/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.19/0.98    inference(ennf_transformation,[],[f11])).
% 2.19/0.98  
% 2.19/0.98  fof(f29,plain,(
% 2.19/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.19/0.98    inference(flattening,[],[f28])).
% 2.19/0.98  
% 2.19/0.98  fof(f60,plain,(
% 2.19/0.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.19/0.98    inference(cnf_transformation,[],[f29])).
% 2.19/0.98  
% 2.19/0.98  fof(f9,axiom,(
% 2.19/0.98    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 2.19/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/0.98  
% 2.19/0.98  fof(f26,plain,(
% 2.19/0.98    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 2.19/0.98    inference(ennf_transformation,[],[f9])).
% 2.19/0.98  
% 2.19/0.98  fof(f57,plain,(
% 2.19/0.98    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 2.19/0.98    inference(cnf_transformation,[],[f26])).
% 2.19/0.98  
% 2.19/0.98  fof(f10,axiom,(
% 2.19/0.98    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 2.19/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/0.98  
% 2.19/0.98  fof(f27,plain,(
% 2.19/0.98    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 2.19/0.98    inference(ennf_transformation,[],[f10])).
% 2.19/0.98  
% 2.19/0.98  fof(f45,plain,(
% 2.19/0.98    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 2.19/0.98    inference(nnf_transformation,[],[f27])).
% 2.19/0.98  
% 2.19/0.98  fof(f59,plain,(
% 2.19/0.98    ( ! [X0,X1] : (r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.19/0.98    inference(cnf_transformation,[],[f45])).
% 2.19/0.98  
% 2.19/0.98  fof(f15,axiom,(
% 2.19/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 2.19/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/0.98  
% 2.19/0.98  fof(f34,plain,(
% 2.19/0.98    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.19/0.98    inference(ennf_transformation,[],[f15])).
% 2.19/0.98  
% 2.19/0.98  fof(f35,plain,(
% 2.19/0.98    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.19/0.98    inference(flattening,[],[f34])).
% 2.19/0.98  
% 2.19/0.98  fof(f69,plain,(
% 2.19/0.98    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.19/0.98    inference(cnf_transformation,[],[f35])).
% 2.19/0.98  
% 2.19/0.98  fof(f76,plain,(
% 2.19/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.19/0.98    inference(cnf_transformation,[],[f38])).
% 2.19/0.98  
% 2.19/0.98  fof(f78,plain,(
% 2.19/0.98    v1_funct_1(sK3)),
% 2.19/0.98    inference(cnf_transformation,[],[f48])).
% 2.19/0.98  
% 2.19/0.98  fof(f82,plain,(
% 2.19/0.98    ~r2_hidden(k1_funct_1(sK3,sK1),sK2)),
% 2.19/0.98    inference(cnf_transformation,[],[f48])).
% 2.19/0.98  
% 2.19/0.98  fof(f13,axiom,(
% 2.19/0.98    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.19/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/0.98  
% 2.19/0.98  fof(f30,plain,(
% 2.19/0.98    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.19/0.98    inference(ennf_transformation,[],[f13])).
% 2.19/0.98  
% 2.19/0.98  fof(f31,plain,(
% 2.19/0.98    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.19/0.98    inference(flattening,[],[f30])).
% 2.19/0.98  
% 2.19/0.98  fof(f64,plain,(
% 2.19/0.98    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.19/0.98    inference(cnf_transformation,[],[f31])).
% 2.19/0.98  
% 2.19/0.98  fof(f2,axiom,(
% 2.19/0.98    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.19/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/0.98  
% 2.19/0.98  fof(f24,plain,(
% 2.19/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.19/0.98    inference(ennf_transformation,[],[f2])).
% 2.19/0.98  
% 2.19/0.98  fof(f43,plain,(
% 2.19/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.19/0.98    introduced(choice_axiom,[])).
% 2.19/0.98  
% 2.19/0.98  fof(f44,plain,(
% 2.19/0.98    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 2.19/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f43])).
% 2.19/0.98  
% 2.19/0.98  fof(f50,plain,(
% 2.19/0.98    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 2.19/0.98    inference(cnf_transformation,[],[f44])).
% 2.19/0.98  
% 2.19/0.98  fof(f20,axiom,(
% 2.19/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 2.19/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/0.98  
% 2.19/0.98  fof(f39,plain,(
% 2.19/0.98    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.19/0.98    inference(ennf_transformation,[],[f20])).
% 2.19/0.98  
% 2.19/0.98  fof(f40,plain,(
% 2.19/0.98    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.19/0.98    inference(flattening,[],[f39])).
% 2.19/0.98  
% 2.19/0.98  fof(f77,plain,(
% 2.19/0.98    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.19/0.98    inference(cnf_transformation,[],[f40])).
% 2.19/0.98  
% 2.19/0.98  fof(f79,plain,(
% 2.19/0.98    v1_funct_2(sK3,k1_tarski(sK1),sK2)),
% 2.19/0.98    inference(cnf_transformation,[],[f48])).
% 2.19/0.98  
% 2.19/0.98  fof(f88,plain,(
% 2.19/0.98    v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2)),
% 2.19/0.98    inference(definition_unfolding,[],[f79,f84])).
% 2.19/0.98  
% 2.19/0.98  fof(f81,plain,(
% 2.19/0.98    k1_xboole_0 != sK2),
% 2.19/0.98    inference(cnf_transformation,[],[f48])).
% 2.19/0.98  
% 2.19/0.98  fof(f1,axiom,(
% 2.19/0.98    v1_xboole_0(k1_xboole_0)),
% 2.19/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/0.98  
% 2.19/0.98  fof(f49,plain,(
% 2.19/0.98    v1_xboole_0(k1_xboole_0)),
% 2.19/0.98    inference(cnf_transformation,[],[f1])).
% 2.19/0.98  
% 2.19/0.98  fof(f7,axiom,(
% 2.19/0.98    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 2.19/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/0.98  
% 2.19/0.98  fof(f55,plain,(
% 2.19/0.98    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 2.19/0.98    inference(cnf_transformation,[],[f7])).
% 2.19/0.98  
% 2.19/0.98  fof(f85,plain,(
% 2.19/0.98    ( ! [X0] : (~v1_xboole_0(k2_enumset1(X0,X0,X0,X0))) )),
% 2.19/0.98    inference(definition_unfolding,[],[f55,f84])).
% 2.19/0.98  
% 2.19/0.98  fof(f14,axiom,(
% 2.19/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 2.19/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/0.98  
% 2.19/0.98  fof(f32,plain,(
% 2.19/0.98    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.19/0.98    inference(ennf_transformation,[],[f14])).
% 2.19/0.98  
% 2.19/0.98  fof(f33,plain,(
% 2.19/0.98    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.19/0.98    inference(flattening,[],[f32])).
% 2.19/0.98  
% 2.19/0.98  fof(f46,plain,(
% 2.19/0.98    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.19/0.98    inference(nnf_transformation,[],[f33])).
% 2.19/0.98  
% 2.19/0.98  fof(f68,plain,(
% 2.19/0.98    ( ! [X2,X0,X1] : (k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2 | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.19/0.98    inference(cnf_transformation,[],[f46])).
% 2.19/0.98  
% 2.19/0.98  fof(f89,plain,(
% 2.19/0.98    ( ! [X0,X1] : (k1_xboole_0 = k1_funct_1(X0,X1) | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.19/0.98    inference(equality_resolution,[],[f68])).
% 2.19/0.98  
% 2.19/0.98  fof(f16,axiom,(
% 2.19/0.98    ! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 2.19/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/0.98  
% 2.19/0.98  fof(f23,plain,(
% 2.19/0.98    ! [X0] : (v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 2.19/0.98    inference(pure_predicate_removal,[],[f16])).
% 2.19/0.98  
% 2.19/0.98  fof(f72,plain,(
% 2.19/0.98    v1_funct_1(k1_xboole_0)),
% 2.19/0.98    inference(cnf_transformation,[],[f23])).
% 2.19/0.98  
% 2.19/0.98  fof(f70,plain,(
% 2.19/0.98    v1_relat_1(k1_xboole_0)),
% 2.19/0.98    inference(cnf_transformation,[],[f23])).
% 2.19/0.98  
% 2.19/0.98  fof(f65,plain,(
% 2.19/0.98    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2 | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.19/0.98    inference(cnf_transformation,[],[f46])).
% 2.19/0.98  
% 2.19/0.98  fof(f91,plain,(
% 2.19/0.98    ( ! [X0,X1] : (r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.19/0.98    inference(equality_resolution,[],[f65])).
% 2.19/0.98  
% 2.19/0.98  fof(f3,axiom,(
% 2.19/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.19/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/0.98  
% 2.19/0.98  fof(f51,plain,(
% 2.19/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.19/0.98    inference(cnf_transformation,[],[f3])).
% 2.19/0.98  
% 2.19/0.98  fof(f17,axiom,(
% 2.19/0.98    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.19/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/0.98  
% 2.19/0.98  fof(f36,plain,(
% 2.19/0.98    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.19/0.98    inference(ennf_transformation,[],[f17])).
% 2.19/0.98  
% 2.19/0.98  fof(f73,plain,(
% 2.19/0.98    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.19/0.98    inference(cnf_transformation,[],[f36])).
% 2.19/0.98  
% 2.19/0.98  cnf(c_22,plain,
% 2.19/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.19/0.98      | v1_relat_1(X0) ),
% 2.19/0.98      inference(cnf_transformation,[],[f74]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_28,negated_conjecture,
% 2.19/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
% 2.19/0.98      inference(cnf_transformation,[],[f87]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_396,plain,
% 2.19/0.98      ( v1_relat_1(X0)
% 2.19/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.19/0.98      | sK3 != X0 ),
% 2.19/0.98      inference(resolution_lifted,[status(thm)],[c_22,c_28]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_397,plain,
% 2.19/0.98      ( v1_relat_1(sK3)
% 2.19/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.19/0.98      inference(unflattening,[status(thm)],[c_396]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1426,plain,
% 2.19/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.19/0.98      | v1_relat_1(sK3) = iProver_top ),
% 2.19/0.98      inference(predicate_to_equality,[status(thm)],[c_397]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1121,plain,( X0 = X0 ),theory(equality) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1567,plain,
% 2.19/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_1121]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1569,plain,
% 2.19/0.98      ( v1_relat_1(sK3)
% 2.19/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_397]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1570,plain,
% 2.19/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
% 2.19/0.98      | v1_relat_1(sK3) = iProver_top ),
% 2.19/0.98      inference(predicate_to_equality,[status(thm)],[c_1569]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1601,plain,
% 2.19/0.98      ( v1_relat_1(sK3) = iProver_top ),
% 2.19/0.98      inference(global_propositional_subsumption,
% 2.19/0.98                [status(thm)],
% 2.19/0.98                [c_1426,c_1567,c_1570]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_4,plain,
% 2.19/0.98      ( ~ v1_relat_1(X0)
% 2.19/0.98      | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
% 2.19/0.98      inference(cnf_transformation,[],[f86]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1436,plain,
% 2.19/0.98      ( k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1)
% 2.19/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.19/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_2448,plain,
% 2.19/0.98      ( k9_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK3,X0) ),
% 2.19/0.98      inference(superposition,[status(thm)],[c_1601,c_1436]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_24,plain,
% 2.19/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.19/0.98      | v4_relat_1(X0,X1) ),
% 2.19/0.98      inference(cnf_transformation,[],[f75]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_8,plain,
% 2.19/0.98      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.19/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_334,plain,
% 2.19/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.19/0.98      | ~ v1_relat_1(X0)
% 2.19/0.98      | k7_relat_1(X0,X1) = X0 ),
% 2.19/0.98      inference(resolution,[status(thm)],[c_24,c_8]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_338,plain,
% 2.19/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.19/0.98      | k7_relat_1(X0,X1) = X0 ),
% 2.19/0.98      inference(global_propositional_subsumption,
% 2.19/0.98                [status(thm)],
% 2.19/0.98                [c_334,c_24,c_22,c_8]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_375,plain,
% 2.19/0.98      ( k7_relat_1(X0,X1) = X0
% 2.19/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.19/0.98      | sK3 != X0 ),
% 2.19/0.98      inference(resolution_lifted,[status(thm)],[c_338,c_28]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_376,plain,
% 2.19/0.98      ( k7_relat_1(sK3,X0) = sK3
% 2.19/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.19/0.98      inference(unflattening,[status(thm)],[c_375]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1583,plain,
% 2.19/0.98      ( k7_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) = sK3 ),
% 2.19/0.98      inference(equality_resolution,[status(thm)],[c_376]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_5,plain,
% 2.19/0.98      ( ~ v1_relat_1(X0)
% 2.19/0.98      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.19/0.98      inference(cnf_transformation,[],[f57]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1435,plain,
% 2.19/0.98      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 2.19/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.19/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_2061,plain,
% 2.19/0.98      ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
% 2.19/0.98      inference(superposition,[status(thm)],[c_1601,c_1435]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_2190,plain,
% 2.19/0.98      ( k9_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) = k2_relat_1(sK3) ),
% 2.19/0.98      inference(superposition,[status(thm)],[c_1583,c_2061]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_2639,plain,
% 2.19/0.98      ( k11_relat_1(sK3,sK1) = k2_relat_1(sK3) ),
% 2.19/0.98      inference(superposition,[status(thm)],[c_2448,c_2190]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_6,plain,
% 2.19/0.98      ( r2_hidden(X0,k1_relat_1(X1))
% 2.19/0.98      | ~ v1_relat_1(X1)
% 2.19/0.98      | k11_relat_1(X1,X0) = k1_xboole_0 ),
% 2.19/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1434,plain,
% 2.19/0.98      ( k11_relat_1(X0,X1) = k1_xboole_0
% 2.19/0.98      | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
% 2.19/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.19/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_17,plain,
% 2.19/0.98      ( ~ v5_relat_1(X0,X1)
% 2.19/0.98      | ~ r2_hidden(X2,k1_relat_1(X0))
% 2.19/0.98      | r2_hidden(k1_funct_1(X0,X2),X1)
% 2.19/0.98      | ~ v1_funct_1(X0)
% 2.19/0.98      | ~ v1_relat_1(X0) ),
% 2.19/0.98      inference(cnf_transformation,[],[f69]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_23,plain,
% 2.19/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.19/0.98      | v5_relat_1(X0,X2) ),
% 2.19/0.98      inference(cnf_transformation,[],[f76]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_384,plain,
% 2.19/0.98      ( v5_relat_1(X0,X1)
% 2.19/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X1))
% 2.19/0.98      | sK3 != X0 ),
% 2.19/0.98      inference(resolution_lifted,[status(thm)],[c_23,c_28]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_385,plain,
% 2.19/0.98      ( v5_relat_1(sK3,X0)
% 2.19/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X0)) ),
% 2.19/0.98      inference(unflattening,[status(thm)],[c_384]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_434,plain,
% 2.19/0.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.19/0.98      | r2_hidden(k1_funct_1(X1,X0),X2)
% 2.19/0.98      | ~ v1_funct_1(X1)
% 2.19/0.98      | ~ v1_relat_1(X1)
% 2.19/0.98      | X3 != X2
% 2.19/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X4,X3))
% 2.19/0.98      | sK3 != X1 ),
% 2.19/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_385]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_435,plain,
% 2.19/0.98      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.19/0.98      | r2_hidden(k1_funct_1(sK3,X0),X1)
% 2.19/0.98      | ~ v1_funct_1(sK3)
% 2.19/0.98      | ~ v1_relat_1(sK3)
% 2.19/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X1)) ),
% 2.19/0.98      inference(unflattening,[status(thm)],[c_434]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_30,negated_conjecture,
% 2.19/0.98      ( v1_funct_1(sK3) ),
% 2.19/0.98      inference(cnf_transformation,[],[f78]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_439,plain,
% 2.19/0.98      ( r2_hidden(k1_funct_1(sK3,X0),X1)
% 2.19/0.98      | ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.19/0.98      | ~ v1_relat_1(sK3)
% 2.19/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X1)) ),
% 2.19/0.98      inference(global_propositional_subsumption,
% 2.19/0.98                [status(thm)],
% 2.19/0.98                [c_435,c_30]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_440,plain,
% 2.19/0.98      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.19/0.98      | r2_hidden(k1_funct_1(sK3,X0),X1)
% 2.19/0.98      | ~ v1_relat_1(sK3)
% 2.19/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X1)) ),
% 2.19/0.98      inference(renaming,[status(thm)],[c_439]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_453,plain,
% 2.19/0.98      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.19/0.98      | r2_hidden(k1_funct_1(sK3,X0),X1)
% 2.19/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X1)) ),
% 2.19/0.98      inference(forward_subsumption_resolution,
% 2.19/0.98                [status(thm)],
% 2.19/0.98                [c_440,c_397]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1425,plain,
% 2.19/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.19/0.98      | r2_hidden(X2,k1_relat_1(sK3)) != iProver_top
% 2.19/0.98      | r2_hidden(k1_funct_1(sK3,X2),X1) = iProver_top ),
% 2.19/0.98      inference(predicate_to_equality,[status(thm)],[c_453]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1865,plain,
% 2.19/0.98      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.19/0.98      | r2_hidden(k1_funct_1(sK3,X0),sK2) = iProver_top ),
% 2.19/0.98      inference(equality_resolution,[status(thm)],[c_1425]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_26,negated_conjecture,
% 2.19/0.98      ( ~ r2_hidden(k1_funct_1(sK3,sK1),sK2) ),
% 2.19/0.98      inference(cnf_transformation,[],[f82]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1429,plain,
% 2.19/0.98      ( r2_hidden(k1_funct_1(sK3,sK1),sK2) != iProver_top ),
% 2.19/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1937,plain,
% 2.19/0.98      ( r2_hidden(sK1,k1_relat_1(sK3)) != iProver_top ),
% 2.19/0.98      inference(superposition,[status(thm)],[c_1865,c_1429]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_2518,plain,
% 2.19/0.98      ( k11_relat_1(sK3,sK1) = k1_xboole_0
% 2.19/0.98      | v1_relat_1(sK3) != iProver_top ),
% 2.19/0.98      inference(superposition,[status(thm)],[c_1434,c_1937]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_2727,plain,
% 2.19/0.98      ( k11_relat_1(sK3,sK1) = k1_xboole_0 ),
% 2.19/0.98      inference(global_propositional_subsumption,
% 2.19/0.98                [status(thm)],
% 2.19/0.98                [c_2518,c_1567,c_1570]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_2731,plain,
% 2.19/0.98      ( k2_relat_1(sK3) = k1_xboole_0 ),
% 2.19/0.98      inference(light_normalisation,[status(thm)],[c_2639,c_2727]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_11,plain,
% 2.19/0.98      ( ~ v1_relat_1(X0)
% 2.19/0.98      | k2_relat_1(X0) != k1_xboole_0
% 2.19/0.98      | k1_xboole_0 = X0 ),
% 2.19/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1432,plain,
% 2.19/0.98      ( k2_relat_1(X0) != k1_xboole_0
% 2.19/0.98      | k1_xboole_0 = X0
% 2.19/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.19/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_2191,plain,
% 2.19/0.98      ( k7_relat_1(sK3,X0) = k1_xboole_0
% 2.19/0.98      | k9_relat_1(sK3,X0) != k1_xboole_0
% 2.19/0.98      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 2.19/0.98      inference(superposition,[status(thm)],[c_2061,c_1432]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_2244,plain,
% 2.19/0.98      ( k7_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) = k1_xboole_0
% 2.19/0.98      | k2_relat_1(sK3) != k1_xboole_0
% 2.19/0.98      | v1_relat_1(k7_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1))) != iProver_top ),
% 2.19/0.98      inference(superposition,[status(thm)],[c_2190,c_2191]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_2245,plain,
% 2.19/0.98      ( k7_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) = k1_xboole_0
% 2.19/0.98      | k2_relat_1(sK3) != k1_xboole_0
% 2.19/0.98      | v1_relat_1(sK3) != iProver_top ),
% 2.19/0.98      inference(light_normalisation,[status(thm)],[c_2244,c_1583]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_2246,plain,
% 2.19/0.98      ( k2_relat_1(sK3) != k1_xboole_0
% 2.19/0.98      | sK3 = k1_xboole_0
% 2.19/0.98      | v1_relat_1(sK3) != iProver_top ),
% 2.19/0.98      inference(demodulation,[status(thm)],[c_2245,c_1583]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_2247,plain,
% 2.19/0.98      ( ~ v1_relat_1(sK3)
% 2.19/0.98      | k2_relat_1(sK3) != k1_xboole_0
% 2.19/0.98      | sK3 = k1_xboole_0 ),
% 2.19/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_2246]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_2249,plain,
% 2.19/0.98      ( sK3 = k1_xboole_0 | k2_relat_1(sK3) != k1_xboole_0 ),
% 2.19/0.98      inference(global_propositional_subsumption,
% 2.19/0.98                [status(thm)],
% 2.19/0.98                [c_2246,c_1567,c_1569,c_2247]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_2250,plain,
% 2.19/0.98      ( k2_relat_1(sK3) != k1_xboole_0 | sK3 = k1_xboole_0 ),
% 2.19/0.98      inference(renaming,[status(thm)],[c_2249]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_2733,plain,
% 2.19/0.98      ( sK3 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.19/0.98      inference(demodulation,[status(thm)],[c_2731,c_2250]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_2737,plain,
% 2.19/0.98      ( sK3 = k1_xboole_0 ),
% 2.19/0.98      inference(equality_resolution_simp,[status(thm)],[c_2733]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1,plain,
% 2.19/0.98      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 2.19/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1437,plain,
% 2.19/0.98      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 2.19/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_25,plain,
% 2.19/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.19/0.98      | ~ r2_hidden(X3,X1)
% 2.19/0.98      | r2_hidden(k1_funct_1(X0,X3),X2)
% 2.19/0.98      | ~ v1_funct_1(X0)
% 2.19/0.98      | k1_xboole_0 = X2 ),
% 2.19/0.98      inference(cnf_transformation,[],[f77]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_29,negated_conjecture,
% 2.19/0.98      ( v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
% 2.19/0.98      inference(cnf_transformation,[],[f88]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_354,plain,
% 2.19/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.19/0.98      | ~ r2_hidden(X3,X1)
% 2.19/0.98      | r2_hidden(k1_funct_1(X0,X3),X2)
% 2.19/0.98      | ~ v1_funct_1(X0)
% 2.19/0.98      | k2_enumset1(sK1,sK1,sK1,sK1) != X1
% 2.19/0.98      | sK2 != X2
% 2.19/0.98      | sK3 != X0
% 2.19/0.98      | k1_xboole_0 = X2 ),
% 2.19/0.98      inference(resolution_lifted,[status(thm)],[c_25,c_29]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_355,plain,
% 2.19/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
% 2.19/0.99      | ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
% 2.19/0.99      | r2_hidden(k1_funct_1(sK3,X0),sK2)
% 2.19/0.99      | ~ v1_funct_1(sK3)
% 2.19/0.99      | k1_xboole_0 = sK2 ),
% 2.19/0.99      inference(unflattening,[status(thm)],[c_354]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_27,negated_conjecture,
% 2.19/0.99      ( k1_xboole_0 != sK2 ),
% 2.19/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_359,plain,
% 2.19/0.99      ( ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
% 2.19/0.99      | r2_hidden(k1_funct_1(sK3,X0),sK2) ),
% 2.19/0.99      inference(global_propositional_subsumption,
% 2.19/0.99                [status(thm)],
% 2.19/0.99                [c_355,c_30,c_28,c_27]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_1427,plain,
% 2.19/0.99      ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
% 2.19/0.99      | r2_hidden(k1_funct_1(sK3,X0),sK2) = iProver_top ),
% 2.19/0.99      inference(predicate_to_equality,[status(thm)],[c_359]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_1794,plain,
% 2.19/0.99      ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_xboole_0
% 2.19/0.99      | r2_hidden(k1_funct_1(sK3,sK0(k2_enumset1(sK1,sK1,sK1,sK1))),sK2) = iProver_top ),
% 2.19/0.99      inference(superposition,[status(thm)],[c_1437,c_1427]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_0,plain,
% 2.19/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.19/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_3,plain,
% 2.19/0.99      ( ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
% 2.19/0.99      inference(cnf_transformation,[],[f85]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_317,plain,
% 2.19/0.99      ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0 ),
% 2.19/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_3]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_1872,plain,
% 2.19/0.99      ( r2_hidden(k1_funct_1(sK3,sK0(k2_enumset1(sK1,sK1,sK1,sK1))),sK2) = iProver_top ),
% 2.19/0.99      inference(forward_subsumption_resolution,
% 2.19/0.99                [status(thm)],
% 2.19/0.99                [c_1794,c_317]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_2813,plain,
% 2.19/0.99      ( r2_hidden(k1_funct_1(k1_xboole_0,sK0(k2_enumset1(sK1,sK1,sK1,sK1))),sK2) = iProver_top ),
% 2.19/0.99      inference(demodulation,[status(thm)],[c_2737,c_1872]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_13,plain,
% 2.19/0.99      ( r2_hidden(X0,k1_relat_1(X1))
% 2.19/0.99      | ~ v1_funct_1(X1)
% 2.19/0.99      | ~ v1_relat_1(X1)
% 2.19/0.99      | k1_funct_1(X1,X0) = k1_xboole_0 ),
% 2.19/0.99      inference(cnf_transformation,[],[f89]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_18,plain,
% 2.19/0.99      ( v1_funct_1(k1_xboole_0) ),
% 2.19/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_489,plain,
% 2.19/0.99      ( r2_hidden(X0,k1_relat_1(X1))
% 2.19/0.99      | ~ v1_relat_1(X1)
% 2.19/0.99      | k1_funct_1(X1,X0) = k1_xboole_0
% 2.19/0.99      | k1_xboole_0 != X1 ),
% 2.19/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_18]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_490,plain,
% 2.19/0.99      ( r2_hidden(X0,k1_relat_1(k1_xboole_0))
% 2.19/0.99      | ~ v1_relat_1(k1_xboole_0)
% 2.19/0.99      | k1_funct_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.19/0.99      inference(unflattening,[status(thm)],[c_489]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_20,plain,
% 2.19/0.99      ( v1_relat_1(k1_xboole_0) ),
% 2.19/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_16,plain,
% 2.19/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.19/0.99      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 2.19/0.99      | ~ v1_funct_1(X1)
% 2.19/0.99      | ~ v1_relat_1(X1) ),
% 2.19/0.99      inference(cnf_transformation,[],[f91]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_467,plain,
% 2.19/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.19/0.99      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 2.19/0.99      | ~ v1_relat_1(X1)
% 2.19/0.99      | k1_xboole_0 != X1 ),
% 2.19/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_18]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_468,plain,
% 2.19/0.99      ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
% 2.19/0.99      | r2_hidden(k4_tarski(X0,k1_funct_1(k1_xboole_0,X0)),k1_xboole_0)
% 2.19/0.99      | ~ v1_relat_1(k1_xboole_0) ),
% 2.19/0.99      inference(unflattening,[status(thm)],[c_467]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_472,plain,
% 2.19/0.99      ( r2_hidden(k4_tarski(X0,k1_funct_1(k1_xboole_0,X0)),k1_xboole_0)
% 2.19/0.99      | ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ),
% 2.19/0.99      inference(global_propositional_subsumption,
% 2.19/0.99                [status(thm)],
% 2.19/0.99                [c_468,c_20]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_473,plain,
% 2.19/0.99      ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
% 2.19/0.99      | r2_hidden(k4_tarski(X0,k1_funct_1(k1_xboole_0,X0)),k1_xboole_0) ),
% 2.19/0.99      inference(renaming,[status(thm)],[c_472]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_2,plain,
% 2.19/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 2.19/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_21,plain,
% 2.19/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 2.19/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_323,plain,
% 2.19/0.99      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 2.19/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_21]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_324,plain,
% 2.19/0.99      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.19/0.99      inference(unflattening,[status(thm)],[c_323]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_482,plain,
% 2.19/0.99      ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ),
% 2.19/0.99      inference(forward_subsumption_resolution,
% 2.19/0.99                [status(thm)],
% 2.19/0.99                [c_473,c_324]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_494,plain,
% 2.19/0.99      ( k1_funct_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.19/0.99      inference(global_propositional_subsumption,
% 2.19/0.99                [status(thm)],
% 2.19/0.99                [c_490,c_20,c_482]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_2847,plain,
% 2.19/0.99      ( r2_hidden(k1_xboole_0,sK2) = iProver_top ),
% 2.19/0.99      inference(demodulation,[status(thm)],[c_2813,c_494]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_533,plain,
% 2.19/0.99      ( r2_hidden(X0,k1_relat_1(X1))
% 2.19/0.99      | ~ v1_relat_1(X1)
% 2.19/0.99      | k1_funct_1(X1,X0) = k1_xboole_0
% 2.19/0.99      | sK3 != X1 ),
% 2.19/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_30]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_534,plain,
% 2.19/0.99      ( r2_hidden(X0,k1_relat_1(sK3))
% 2.19/0.99      | ~ v1_relat_1(sK3)
% 2.19/0.99      | k1_funct_1(sK3,X0) = k1_xboole_0 ),
% 2.19/0.99      inference(unflattening,[status(thm)],[c_533]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_1421,plain,
% 2.19/0.99      ( k1_funct_1(sK3,X0) = k1_xboole_0
% 2.19/0.99      | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
% 2.19/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.19/0.99      inference(predicate_to_equality,[status(thm)],[c_534]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_535,plain,
% 2.19/0.99      ( k1_funct_1(sK3,X0) = k1_xboole_0
% 2.19/0.99      | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
% 2.19/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.19/0.99      inference(predicate_to_equality,[status(thm)],[c_534]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_1797,plain,
% 2.19/0.99      ( r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
% 2.19/0.99      | k1_funct_1(sK3,X0) = k1_xboole_0 ),
% 2.19/0.99      inference(global_propositional_subsumption,
% 2.19/0.99                [status(thm)],
% 2.19/0.99                [c_1421,c_535,c_1567,c_1570]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_1798,plain,
% 2.19/0.99      ( k1_funct_1(sK3,X0) = k1_xboole_0
% 2.19/0.99      | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top ),
% 2.19/0.99      inference(renaming,[status(thm)],[c_1797]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_1941,plain,
% 2.19/0.99      ( k1_funct_1(sK3,sK1) = k1_xboole_0 ),
% 2.19/0.99      inference(superposition,[status(thm)],[c_1798,c_1937]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_1986,plain,
% 2.19/0.99      ( r2_hidden(k1_xboole_0,sK2) != iProver_top ),
% 2.19/0.99      inference(demodulation,[status(thm)],[c_1941,c_1429]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(contradiction,plain,
% 2.19/0.99      ( $false ),
% 2.19/0.99      inference(minisat,[status(thm)],[c_2847,c_1986]) ).
% 2.19/0.99  
% 2.19/0.99  
% 2.19/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.19/0.99  
% 2.19/0.99  ------                               Statistics
% 2.19/0.99  
% 2.19/0.99  ------ General
% 2.19/0.99  
% 2.19/0.99  abstr_ref_over_cycles:                  0
% 2.19/0.99  abstr_ref_under_cycles:                 0
% 2.19/0.99  gc_basic_clause_elim:                   0
% 2.19/0.99  forced_gc_time:                         0
% 2.19/0.99  parsing_time:                           0.013
% 2.19/0.99  unif_index_cands_time:                  0.
% 2.19/0.99  unif_index_add_time:                    0.
% 2.19/0.99  orderings_time:                         0.
% 2.19/0.99  out_proof_time:                         0.01
% 2.19/0.99  total_time:                             0.122
% 2.19/0.99  num_of_symbols:                         55
% 2.19/0.99  num_of_terms:                           2003
% 2.19/0.99  
% 2.19/0.99  ------ Preprocessing
% 2.19/0.99  
% 2.19/0.99  num_of_splits:                          0
% 2.19/0.99  num_of_split_atoms:                     0
% 2.19/0.99  num_of_reused_defs:                     0
% 2.19/0.99  num_eq_ax_congr_red:                    23
% 2.19/0.99  num_of_sem_filtered_clauses:            1
% 2.19/0.99  num_of_subtypes:                        0
% 2.19/0.99  monotx_restored_types:                  0
% 2.19/0.99  sat_num_of_epr_types:                   0
% 2.19/0.99  sat_num_of_non_cyclic_types:            0
% 2.19/0.99  sat_guarded_non_collapsed_types:        0
% 2.19/0.99  num_pure_diseq_elim:                    0
% 2.19/0.99  simp_replaced_by:                       0
% 2.19/0.99  res_preprocessed:                       126
% 2.19/0.99  prep_upred:                             0
% 2.19/0.99  prep_unflattend:                        42
% 2.19/0.99  smt_new_axioms:                         0
% 2.19/0.99  pred_elim_cands:                        2
% 2.19/0.99  pred_elim:                              7
% 2.19/0.99  pred_elim_cl:                           7
% 2.19/0.99  pred_elim_cycles:                       9
% 2.19/0.99  merged_defs:                            0
% 2.19/0.99  merged_defs_ncl:                        0
% 2.19/0.99  bin_hyper_res:                          0
% 2.19/0.99  prep_cycles:                            4
% 2.19/0.99  pred_elim_time:                         0.013
% 2.19/0.99  splitting_time:                         0.
% 2.19/0.99  sem_filter_time:                        0.
% 2.19/0.99  monotx_time:                            0.
% 2.19/0.99  subtype_inf_time:                       0.
% 2.19/0.99  
% 2.19/0.99  ------ Problem properties
% 2.19/0.99  
% 2.19/0.99  clauses:                                23
% 2.19/0.99  conjectures:                            2
% 2.19/0.99  epr:                                    3
% 2.19/0.99  horn:                                   20
% 2.19/0.99  ground:                                 5
% 2.19/0.99  unary:                                  9
% 2.19/0.99  binary:                                 6
% 2.19/0.99  lits:                                   46
% 2.19/0.99  lits_eq:                                20
% 2.19/0.99  fd_pure:                                0
% 2.19/0.99  fd_pseudo:                              0
% 2.19/0.99  fd_cond:                                3
% 2.19/0.99  fd_pseudo_cond:                         1
% 2.19/0.99  ac_symbols:                             0
% 2.19/0.99  
% 2.19/0.99  ------ Propositional Solver
% 2.19/0.99  
% 2.19/0.99  prop_solver_calls:                      28
% 2.19/0.99  prop_fast_solver_calls:                 775
% 2.19/0.99  smt_solver_calls:                       0
% 2.19/0.99  smt_fast_solver_calls:                  0
% 2.19/0.99  prop_num_of_clauses:                    796
% 2.19/0.99  prop_preprocess_simplified:             4008
% 2.19/0.99  prop_fo_subsumed:                       20
% 2.19/0.99  prop_solver_time:                       0.
% 2.19/0.99  smt_solver_time:                        0.
% 2.19/0.99  smt_fast_solver_time:                   0.
% 2.19/0.99  prop_fast_solver_time:                  0.
% 2.19/0.99  prop_unsat_core_time:                   0.
% 2.19/0.99  
% 2.19/0.99  ------ QBF
% 2.19/0.99  
% 2.19/0.99  qbf_q_res:                              0
% 2.19/0.99  qbf_num_tautologies:                    0
% 2.19/0.99  qbf_prep_cycles:                        0
% 2.19/0.99  
% 2.19/0.99  ------ BMC1
% 2.19/0.99  
% 2.19/0.99  bmc1_current_bound:                     -1
% 2.19/0.99  bmc1_last_solved_bound:                 -1
% 2.19/0.99  bmc1_unsat_core_size:                   -1
% 2.19/0.99  bmc1_unsat_core_parents_size:           -1
% 2.19/0.99  bmc1_merge_next_fun:                    0
% 2.19/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.19/0.99  
% 2.19/0.99  ------ Instantiation
% 2.19/0.99  
% 2.19/0.99  inst_num_of_clauses:                    275
% 2.19/0.99  inst_num_in_passive:                    99
% 2.19/0.99  inst_num_in_active:                     167
% 2.19/0.99  inst_num_in_unprocessed:                9
% 2.19/0.99  inst_num_of_loops:                      200
% 2.19/0.99  inst_num_of_learning_restarts:          0
% 2.19/0.99  inst_num_moves_active_passive:          29
% 2.19/0.99  inst_lit_activity:                      0
% 2.19/0.99  inst_lit_activity_moves:                0
% 2.19/0.99  inst_num_tautologies:                   0
% 2.19/0.99  inst_num_prop_implied:                  0
% 2.19/0.99  inst_num_existing_simplified:           0
% 2.19/0.99  inst_num_eq_res_simplified:             0
% 2.19/0.99  inst_num_child_elim:                    0
% 2.19/0.99  inst_num_of_dismatching_blockings:      27
% 2.19/0.99  inst_num_of_non_proper_insts:           197
% 2.19/0.99  inst_num_of_duplicates:                 0
% 2.19/0.99  inst_inst_num_from_inst_to_res:         0
% 2.19/0.99  inst_dismatching_checking_time:         0.
% 2.19/0.99  
% 2.19/0.99  ------ Resolution
% 2.19/0.99  
% 2.19/0.99  res_num_of_clauses:                     0
% 2.19/0.99  res_num_in_passive:                     0
% 2.19/0.99  res_num_in_active:                      0
% 2.19/0.99  res_num_of_loops:                       130
% 2.19/0.99  res_forward_subset_subsumed:            45
% 2.19/0.99  res_backward_subset_subsumed:           1
% 2.19/0.99  res_forward_subsumed:                   0
% 2.19/0.99  res_backward_subsumed:                  0
% 2.19/0.99  res_forward_subsumption_resolution:     2
% 2.19/0.99  res_backward_subsumption_resolution:    0
% 2.19/0.99  res_clause_to_clause_subsumption:       85
% 2.19/0.99  res_orphan_elimination:                 0
% 2.19/0.99  res_tautology_del:                      44
% 2.19/0.99  res_num_eq_res_simplified:              0
% 2.19/0.99  res_num_sel_changes:                    0
% 2.19/0.99  res_moves_from_active_to_pass:          0
% 2.19/0.99  
% 2.19/0.99  ------ Superposition
% 2.19/0.99  
% 2.19/0.99  sup_time_total:                         0.
% 2.19/0.99  sup_time_generating:                    0.
% 2.19/0.99  sup_time_sim_full:                      0.
% 2.19/0.99  sup_time_sim_immed:                     0.
% 2.19/0.99  
% 2.19/0.99  sup_num_of_clauses:                     25
% 2.19/0.99  sup_num_in_active:                      18
% 2.19/0.99  sup_num_in_passive:                     7
% 2.19/0.99  sup_num_of_loops:                       39
% 2.19/0.99  sup_fw_superposition:                   14
% 2.19/0.99  sup_bw_superposition:                   12
% 2.19/0.99  sup_immediate_simplified:               21
% 2.19/0.99  sup_given_eliminated:                   0
% 2.19/0.99  comparisons_done:                       0
% 2.19/0.99  comparisons_avoided:                    0
% 2.19/0.99  
% 2.19/0.99  ------ Simplifications
% 2.19/0.99  
% 2.19/0.99  
% 2.19/0.99  sim_fw_subset_subsumed:                 5
% 2.19/0.99  sim_bw_subset_subsumed:                 1
% 2.19/0.99  sim_fw_subsumed:                        9
% 2.19/0.99  sim_bw_subsumed:                        1
% 2.19/0.99  sim_fw_subsumption_res:                 1
% 2.19/0.99  sim_bw_subsumption_res:                 0
% 2.19/0.99  sim_tautology_del:                      0
% 2.19/0.99  sim_eq_tautology_del:                   3
% 2.19/0.99  sim_eq_res_simp:                        2
% 2.19/0.99  sim_fw_demodulated:                     5
% 2.19/0.99  sim_bw_demodulated:                     22
% 2.19/0.99  sim_light_normalised:                   13
% 2.19/0.99  sim_joinable_taut:                      0
% 2.19/0.99  sim_joinable_simp:                      0
% 2.19/0.99  sim_ac_normalised:                      0
% 2.19/0.99  sim_smt_subsumption:                    0
% 2.19/0.99  
%------------------------------------------------------------------------------
