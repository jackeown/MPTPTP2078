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
% DateTime   : Thu Dec  3 12:05:05 EST 2020

% Result     : Theorem 43.22s
% Output     : CNFRefutation 43.22s
% Verified   : 
% Statistics : Number of formulae       :  259 (1087 expanded)
%              Number of clauses        :  141 ( 285 expanded)
%              Number of leaves         :   33 ( 281 expanded)
%              Depth                    :   20
%              Number of atoms          :  835 (3116 expanded)
%              Number of equality atoms :  479 (1928 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f31,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    inference(negated_conjecture,[],[f31])).

fof(f61,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f62,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f61])).

fof(f77,plain,
    ( ? [X0,X1,X2] :
        ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( k1_tarski(k1_funct_1(sK4,sK2)) != k2_relset_1(k1_tarski(sK2),sK3,sK4)
      & k1_xboole_0 != sK3
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
      & v1_funct_2(sK4,k1_tarski(sK2),sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,
    ( k1_tarski(k1_funct_1(sK4,sK2)) != k2_relset_1(k1_tarski(sK2),sK3,sK4)
    & k1_xboole_0 != sK3
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
    & v1_funct_2(sK4,k1_tarski(sK2),sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f62,f77])).

fof(f136,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) ),
    inference(cnf_transformation,[],[f78])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f89,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f90,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f139,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f89,f90])).

fof(f140,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f88,f139])).

fof(f161,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) ),
    inference(definition_unfolding,[],[f136,f140])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f24])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f109,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ~ ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3 ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f70,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
        | ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) )
      & ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f71,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
        | ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) )
      & ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ) ),
    inference(flattening,[],[f70])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | k2_tarski(X0,X2) = X3
      | k2_tarski(X1,X2) = X3
      | k2_tarski(X0,X1) = X3
      | k1_tarski(X2) = X3
      | k1_tarski(X1) = X3
      | k1_tarski(X0) = X3
      | k1_xboole_0 = X3
      | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f156,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_enumset1(X0,X0,X1,X2) = X3
      | k2_enumset1(X0,X0,X0,X2) = X3
      | k2_enumset1(X1,X1,X1,X2) = X3
      | k2_enumset1(X0,X0,X0,X1) = X3
      | k2_enumset1(X2,X2,X2,X2) = X3
      | k2_enumset1(X1,X1,X1,X1) = X3
      | k2_enumset1(X0,X0,X0,X0) = X3
      | k1_xboole_0 = X3
      | ~ r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(definition_unfolding,[],[f95,f90,f139,f139,f139,f140,f140,f140,f90])).

fof(f1,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f80,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f135,plain,(
    v1_funct_2(sK4,k1_tarski(sK2),sK3) ),
    inference(cnf_transformation,[],[f78])).

fof(f162,plain,(
    v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
    inference(definition_unfolding,[],[f135,f140])).

fof(f134,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f78])).

fof(f138,plain,(
    k1_tarski(k1_funct_1(sK4,sK2)) != k2_relset_1(k1_tarski(sK2),sK3,sK4) ),
    inference(cnf_transformation,[],[f78])).

fof(f160,plain,(
    k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) ),
    inference(definition_unfolding,[],[f138,f140,f140])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f42])).

fof(f112,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0)))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0)))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f50])).

fof(f121,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0)))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f159,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k2_enumset1(X0,X0,X0,X0)))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f121,f140,f140])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f63])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f64])).

fof(f66,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK0(X0,X1,X2) != X1
            & sK0(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( sK0(X0,X1,X2) = X1
          | sK0(X0,X1,X2) = X0
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK0(X0,X1,X2) != X1
              & sK0(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( sK0(X0,X1,X2) = X1
            | sK0(X0,X1,X2) = X0
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f65,f66])).

fof(f83,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f67])).

fof(f145,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f83,f139])).

fof(f165,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f145])).

fof(f166,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f165])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f68])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f69])).

fof(f169,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f93])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f57])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f20,axiom,(
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

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f74,plain,(
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
    inference(nnf_transformation,[],[f47])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | k1_xboole_0 != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f178,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_funct_1(X0,X1)
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f119])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f104,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK0(X0,X1,X2) = X1
      | sK0(X0,X1,X2) = X0
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( k2_enumset1(X0,X0,X0,X1) = X2
      | sK0(X0,X1,X2) = X1
      | sK0(X0,X1,X2) = X0
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f85,f139])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK0(X0,X1,X2) != X1
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( k2_enumset1(X0,X0,X0,X1) = X2
      | sK0(X0,X1,X2) != X1
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f87,f139])).

fof(f18,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f114,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f18])).

fof(f84,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f67])).

fof(f144,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f84,f139])).

fof(f163,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f144])).

fof(f164,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_enumset1(X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f163])).

fof(f30,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f60,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f59])).

fof(f133,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK0(X0,X1,X2) != X0
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( k2_enumset1(X0,X0,X0,X1) = X2
      | sK0(X0,X1,X2) != X0
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f86,f139])).

fof(f8,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f91,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f147,plain,(
    ! [X0] : ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(definition_unfolding,[],[f91,f140])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f137,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_875,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2709,plain,
    ( X0 != X1
    | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) != X1
    | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) = X0 ),
    inference(instantiation,[status(thm)],[c_875])).

cnf(c_137411,plain,
    ( X0 != k2_relat_1(X1)
    | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) = X0
    | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) != k2_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_2709])).

cnf(c_137412,plain,
    ( k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) != k2_relat_1(k1_xboole_0)
    | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) = k1_xboole_0
    | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_137411])).

cnf(c_54,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) ),
    inference(cnf_transformation,[],[f161])).

cnf(c_1925,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_41,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_1936,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_5935,plain,
    ( v4_relat_1(sK4,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1925,c_1936])).

cnf(c_28,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1945,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_21,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X2,X3))
    | k2_enumset1(X1,X1,X2,X3) = X0
    | k2_enumset1(X1,X1,X1,X3) = X0
    | k2_enumset1(X2,X2,X2,X3) = X0
    | k2_enumset1(X1,X1,X1,X2) = X0
    | k2_enumset1(X3,X3,X3,X3) = X0
    | k2_enumset1(X2,X2,X2,X2) = X0
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f156])).

cnf(c_1952,plain,
    ( k2_enumset1(X0,X0,X1,X2) = X3
    | k2_enumset1(X0,X0,X0,X2) = X3
    | k2_enumset1(X1,X1,X1,X2) = X3
    | k2_enumset1(X0,X0,X0,X1) = X3
    | k2_enumset1(X2,X2,X2,X2) = X3
    | k2_enumset1(X1,X1,X1,X1) = X3
    | k2_enumset1(X0,X0,X0,X0) = X3
    | k1_xboole_0 = X3
    | r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_0,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1970,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1969,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3055,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_1970,c_1969])).

cnf(c_9924,plain,
    ( k2_enumset1(X0,X0,X1,X2) = X3
    | k2_enumset1(X0,X0,X0,X2) = X3
    | k2_enumset1(X1,X1,X1,X2) = X3
    | k2_enumset1(X0,X0,X0,X1) = X3
    | k2_enumset1(X2,X2,X2,X2) = X3
    | k2_enumset1(X1,X1,X1,X1) = X3
    | k2_enumset1(X0,X0,X0,X0) = X3
    | o_0_0_xboole_0 = X3
    | r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1952,c_3055])).

cnf(c_9944,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k1_relat_1(X2)
    | k2_enumset1(X0,X0,X1,X3) = k1_relat_1(X2)
    | k2_enumset1(X0,X0,X0,X3) = k1_relat_1(X2)
    | k2_enumset1(X1,X1,X1,X3) = k1_relat_1(X2)
    | k2_enumset1(X3,X3,X3,X3) = k1_relat_1(X2)
    | k2_enumset1(X1,X1,X1,X1) = k1_relat_1(X2)
    | k2_enumset1(X0,X0,X0,X0) = k1_relat_1(X2)
    | k1_relat_1(X2) = o_0_0_xboole_0
    | v4_relat_1(X2,k2_enumset1(X0,X0,X1,X3)) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1945,c_9924])).

cnf(c_131752,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_relat_1(sK4)
    | k1_relat_1(sK4) = o_0_0_xboole_0
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5935,c_9944])).

cnf(c_40,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_2350,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_40])).

cnf(c_132292,plain,
    ( ~ v1_relat_1(sK4)
    | k2_enumset1(sK2,sK2,sK2,sK2) = k1_relat_1(sK4)
    | k1_relat_1(sK4) = o_0_0_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_131752])).

cnf(c_133422,plain,
    ( k1_relat_1(sK4) = o_0_0_xboole_0
    | k2_enumset1(sK2,sK2,sK2,sK2) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_131752,c_54,c_2350,c_132292])).

cnf(c_133423,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_relat_1(sK4)
    | k1_relat_1(sK4) = o_0_0_xboole_0 ),
    inference(renaming,[status(thm)],[c_133422])).

cnf(c_55,negated_conjecture,
    ( v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
    inference(cnf_transformation,[],[f162])).

cnf(c_1924,plain,
    ( v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55])).

cnf(c_133553,plain,
    ( k1_relat_1(sK4) = o_0_0_xboole_0
    | v1_funct_2(sK4,k1_relat_1(sK4),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_133423,c_1924])).

cnf(c_56,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_57,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56])).

cnf(c_59,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_52,negated_conjecture,
    ( k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) ),
    inference(cnf_transformation,[],[f160])).

cnf(c_2351,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2350])).

cnf(c_2409,plain,
    ( v4_relat_1(sK4,k2_enumset1(sK2,sK2,sK2,sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) ),
    inference(instantiation,[status(thm)],[c_41])).

cnf(c_44,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_2467,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))
    | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) = k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_30,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_2642,plain,
    ( ~ v4_relat_1(sK4,k2_enumset1(sK2,sK2,sK2,sK2))
    | ~ v1_relat_1(sK4)
    | k7_relat_1(sK4,k2_enumset1(sK2,sK2,sK2,sK2)) = sK4 ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_888,plain,
    ( X0 != X1
    | k2_relat_1(X0) = k2_relat_1(X1) ),
    theory(equality)).

cnf(c_3906,plain,
    ( X0 != sK4
    | k2_relat_1(X0) = k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_888])).

cnf(c_4883,plain,
    ( k7_relat_1(sK4,k2_enumset1(sK2,sK2,sK2,sK2)) != sK4
    | k2_relat_1(k7_relat_1(sK4,k2_enumset1(sK2,sK2,sK2,sK2))) = k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_3906])).

cnf(c_3104,plain,
    ( X0 != k2_relat_1(sK4)
    | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) = X0
    | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2709])).

cnf(c_3905,plain,
    ( k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) = k2_relat_1(X0)
    | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) != k2_relat_1(sK4)
    | k2_relat_1(X0) != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_3104])).

cnf(c_6917,plain,
    ( k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) = k2_relat_1(k7_relat_1(sK4,k2_enumset1(sK2,sK2,sK2,sK2)))
    | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) != k2_relat_1(sK4)
    | k2_relat_1(k7_relat_1(sK4,k2_enumset1(sK2,sK2,sK2,sK2))) != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_3905])).

cnf(c_2435,plain,
    ( k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != X0
    | k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) = k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)
    | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_875])).

cnf(c_19022,plain,
    ( k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) = k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)
    | k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k2_relat_1(k7_relat_1(sK4,k2_enumset1(sK2,sK2,sK2,sK2)))
    | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) != k2_relat_1(k7_relat_1(sK4,k2_enumset1(sK2,sK2,sK2,sK2))) ),
    inference(instantiation,[status(thm)],[c_2435])).

cnf(c_39,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k2_enumset1(X0,X0,X0,X0))) ),
    inference(cnf_transformation,[],[f159])).

cnf(c_25783,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) = k2_relat_1(k7_relat_1(sK4,k2_enumset1(sK2,sK2,sK2,sK2))) ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_25784,plain,
    ( k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) = k2_relat_1(k7_relat_1(sK4,k2_enumset1(sK2,sK2,sK2,sK2)))
    | r2_hidden(sK2,k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25783])).

cnf(c_7,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

cnf(c_1963,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_133450,plain,
    ( k1_relat_1(sK4) = o_0_0_xboole_0
    | r2_hidden(sK2,k1_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_133423,c_1963])).

cnf(c_135113,plain,
    ( k1_relat_1(sK4) = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_133553,c_57,c_54,c_59,c_52,c_2350,c_2351,c_2409,c_2467,c_2642,c_4883,c_6917,c_19022,c_25784,c_133450])).

cnf(c_1933,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_6127,plain,
    ( k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1925,c_1933])).

cnf(c_43,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_1934,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_6588,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK3)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6127,c_1934])).

cnf(c_6782,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6588,c_59])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1949,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_6787,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6782,c_1949])).

cnf(c_11,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f169])).

cnf(c_3164,plain,
    ( k2_zfmisc_1(o_0_0_xboole_0,X0) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3055,c_11])).

cnf(c_45,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_1932,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_3711,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),o_0_0_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3164,c_1932])).

cnf(c_15613,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(o_0_0_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(sK4),o_0_0_xboole_0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6787,c_3711])).

cnf(c_16703,plain,
    ( r1_tarski(k1_relat_1(sK4),o_0_0_xboole_0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(o_0_0_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15613,c_59,c_2351])).

cnf(c_16704,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(o_0_0_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(sK4),o_0_0_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_16703])).

cnf(c_135149,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(o_0_0_xboole_0)) = iProver_top
    | r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_135113,c_16704])).

cnf(c_2,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1968,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3162,plain,
    ( r1_tarski(o_0_0_xboole_0,X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3055,c_1968])).

cnf(c_135557,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(o_0_0_xboole_0)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_135149,c_3162])).

cnf(c_42,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_1935,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_5644,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3164,c_1935])).

cnf(c_135561,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_135557,c_5644])).

cnf(c_135607,plain,
    ( v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_135561])).

cnf(c_34,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f178])).

cnf(c_2631,plain,
    ( r2_hidden(X0,k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,X0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_72861,plain,
    ( r2_hidden(sK2,k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK2) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2631])).

cnf(c_879,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_61812,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(X2,X3,X4),X4)
    | X4 != X1
    | sK0(X2,X3,X4) != X0 ),
    inference(instantiation,[status(thm)],[c_879])).

cnf(c_61814,plain,
    ( r2_hidden(sK0(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ r2_hidden(k1_xboole_0,k1_xboole_0)
    | sK0(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_61812])).

cnf(c_20118,plain,
    ( X0 != X1
    | X0 = k1_funct_1(sK4,sK2)
    | k1_funct_1(sK4,sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_875])).

cnf(c_20119,plain,
    ( k1_funct_1(sK4,sK2) != k1_xboole_0
    | k1_xboole_0 = k1_funct_1(sK4,sK2)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_20118])).

cnf(c_25,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_22,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_4979,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_25,c_22])).

cnf(c_11652,plain,
    ( ~ r2_hidden(X0,k1_xboole_0)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_4979,c_42])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0,X1,X2),X2)
    | k2_enumset1(X0,X0,X0,X1) = X2
    | sK0(X0,X1,X2) = X1
    | sK0(X0,X1,X2) = X0 ),
    inference(cnf_transformation,[],[f143])).

cnf(c_12296,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK0(X1,X2,k1_xboole_0))
    | k2_enumset1(X1,X1,X1,X2) = k1_xboole_0
    | sK0(X1,X2,k1_xboole_0) = X2
    | sK0(X1,X2,k1_xboole_0) = X1 ),
    inference(resolution,[status(thm)],[c_11652,c_5])).

cnf(c_12297,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k1_xboole_0
    | sK0(X0,X1,k1_xboole_0) = X1
    | sK0(X0,X1,k1_xboole_0) = X0
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(sK0(X0,X1,k1_xboole_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12296])).

cnf(c_12299,plain,
    ( k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | sK0(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | v1_xboole_0(sK0(k1_xboole_0,k1_xboole_0,k1_xboole_0)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_12297])).

cnf(c_3,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k2_enumset1(X0,X0,X0,X1) = X2
    | sK0(X0,X1,X2) != X1 ),
    inference(cnf_transformation,[],[f141])).

cnf(c_874,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_7022,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_875,c_874])).

cnf(c_7360,plain,
    ( ~ v1_xboole_0(X0)
    | X0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7022,c_1])).

cnf(c_9977,plain,
    ( ~ r2_hidden(sK0(X0,k1_xboole_0,X1),X1)
    | ~ v1_xboole_0(sK0(X0,k1_xboole_0,X1))
    | k2_enumset1(X0,X0,X0,k1_xboole_0) = X1 ),
    inference(resolution,[status(thm)],[c_3,c_7360])).

cnf(c_9978,plain,
    ( k2_enumset1(X0,X0,X0,k1_xboole_0) = X1
    | r2_hidden(sK0(X0,k1_xboole_0,X1),X1) != iProver_top
    | v1_xboole_0(sK0(X0,k1_xboole_0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9977])).

cnf(c_9980,plain,
    ( k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | r2_hidden(sK0(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top
    | v1_xboole_0(sK0(k1_xboole_0,k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9978])).

cnf(c_31,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_7377,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_7022,c_31])).

cnf(c_4653,plain,
    ( X0 != X1
    | X0 = k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)
    | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) != X1 ),
    inference(instantiation,[status(thm)],[c_875])).

cnf(c_4654,plain,
    ( k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) != k1_xboole_0
    | k1_xboole_0 = k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4653])).

cnf(c_3943,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k1_funct_1(sK4,sK2),k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4))
    | X1 != k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)
    | X0 != k1_funct_1(sK4,sK2) ),
    inference(instantiation,[status(thm)],[c_879])).

cnf(c_3945,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK2),k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4))
    | r2_hidden(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)
    | k1_xboole_0 != k1_funct_1(sK4,sK2) ),
    inference(instantiation,[status(thm)],[c_3943])).

cnf(c_3908,plain,
    ( k2_relat_1(k1_xboole_0) = k2_relat_1(sK4)
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_3906])).

cnf(c_3907,plain,
    ( k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) != k2_relat_1(sK4)
    | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) = k2_relat_1(k1_xboole_0)
    | k2_relat_1(k1_xboole_0) != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_3905])).

cnf(c_6,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f164])).

cnf(c_3801,plain,
    ( r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_51,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f133])).

cnf(c_2562,plain,
    ( ~ v1_funct_2(X0,X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK3)))
    | ~ r2_hidden(X2,X1)
    | r2_hidden(k1_funct_1(X0,X2),k2_relset_1(X1,sK3,X0))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_51])).

cnf(c_2784,plain,
    ( ~ v1_funct_2(sK4,X0,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK3)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(k1_funct_1(sK4,X1),k2_relset_1(X0,sK3,sK4))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_2562])).

cnf(c_2838,plain,
    ( ~ v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))
    | ~ r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2))
    | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_2784])).

cnf(c_3800,plain,
    ( ~ v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))
    | r2_hidden(k1_funct_1(sK4,sK2),k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4))
    | ~ r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_2838])).

cnf(c_876,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3270,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_enumset1(X1,X1,X1,X1))
    | k2_enumset1(X1,X1,X1,X1) != X0 ),
    inference(instantiation,[status(thm)],[c_876])).

cnf(c_3272,plain,
    ( v1_xboole_0(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0)
    | k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3270])).

cnf(c_2916,plain,
    ( ~ v1_xboole_0(sK4)
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2917,plain,
    ( k1_xboole_0 = sK4
    | v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2916])).

cnf(c_2368,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | X0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_876])).

cnf(c_2372,plain,
    ( X0 != o_0_0_xboole_0
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2368])).

cnf(c_2374,plain,
    ( k1_xboole_0 != o_0_0_xboole_0
    | v1_xboole_0(k1_xboole_0) = iProver_top
    | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2372])).

cnf(c_2373,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | k1_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2368])).

cnf(c_2369,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | k1_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_178,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k2_enumset1(X0,X0,X0,X1) = X2
    | sK0(X0,X1,X2) != X0 ),
    inference(cnf_transformation,[],[f142])).

cnf(c_169,plain,
    ( ~ r2_hidden(sK0(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | sK0(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_165,plain,
    ( k2_enumset1(X0,X0,X0,X1) = X2
    | sK0(X0,X1,X2) = X1
    | sK0(X0,X1,X2) = X0
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_167,plain,
    ( k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | sK0(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | r2_hidden(sK0(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_165])).

cnf(c_9,plain,
    ( ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f147])).

cnf(c_156,plain,
    ( ~ v1_xboole_0(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_154,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_12,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_153,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_53,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f137])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_137412,c_135607,c_72861,c_61814,c_25783,c_20119,c_19022,c_12299,c_9980,c_7377,c_6917,c_4883,c_4654,c_3945,c_3908,c_3907,c_3801,c_3800,c_3272,c_2917,c_2642,c_2467,c_2409,c_2374,c_2373,c_2369,c_2350,c_178,c_0,c_169,c_167,c_156,c_154,c_153,c_52,c_53,c_54,c_55,c_56])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.19/0.34  % DateTime   : Tue Dec  1 18:36:27 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 43.22/6.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 43.22/6.00  
% 43.22/6.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 43.22/6.00  
% 43.22/6.00  ------  iProver source info
% 43.22/6.00  
% 43.22/6.00  git: date: 2020-06-30 10:37:57 +0100
% 43.22/6.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 43.22/6.00  git: non_committed_changes: false
% 43.22/6.00  git: last_make_outside_of_git: false
% 43.22/6.00  
% 43.22/6.00  ------ 
% 43.22/6.00  ------ Parsing...
% 43.22/6.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 43.22/6.00  
% 43.22/6.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 43.22/6.00  
% 43.22/6.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 43.22/6.00  
% 43.22/6.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.22/6.00  ------ Proving...
% 43.22/6.00  ------ Problem Properties 
% 43.22/6.00  
% 43.22/6.00  
% 43.22/6.00  clauses                                 56
% 43.22/6.00  conjectures                             5
% 43.22/6.00  EPR                                     6
% 43.22/6.00  Horn                                    50
% 43.22/6.00  unary                                   28
% 43.22/6.00  binary                                  9
% 43.22/6.00  lits                                    121
% 43.22/6.00  lits eq                                 36
% 43.22/6.00  fd_pure                                 0
% 43.22/6.00  fd_pseudo                               0
% 43.22/6.00  fd_cond                                 3
% 43.22/6.00  fd_pseudo_cond                          5
% 43.22/6.00  AC symbols                              0
% 43.22/6.00  
% 43.22/6.00  ------ Input Options Time Limit: Unbounded
% 43.22/6.00  
% 43.22/6.00  
% 43.22/6.00  ------ 
% 43.22/6.00  Current options:
% 43.22/6.00  ------ 
% 43.22/6.00  
% 43.22/6.00  
% 43.22/6.00  
% 43.22/6.00  
% 43.22/6.00  ------ Proving...
% 43.22/6.00  
% 43.22/6.00  
% 43.22/6.00  % SZS status Theorem for theBenchmark.p
% 43.22/6.00  
% 43.22/6.00  % SZS output start CNFRefutation for theBenchmark.p
% 43.22/6.00  
% 43.22/6.00  fof(f31,conjecture,(
% 43.22/6.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 43.22/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.22/6.00  
% 43.22/6.00  fof(f32,negated_conjecture,(
% 43.22/6.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 43.22/6.00    inference(negated_conjecture,[],[f31])).
% 43.22/6.00  
% 43.22/6.00  fof(f61,plain,(
% 43.22/6.00    ? [X0,X1,X2] : ((k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 43.22/6.00    inference(ennf_transformation,[],[f32])).
% 43.22/6.00  
% 43.22/6.00  fof(f62,plain,(
% 43.22/6.00    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 43.22/6.00    inference(flattening,[],[f61])).
% 43.22/6.00  
% 43.22/6.00  fof(f77,plain,(
% 43.22/6.00    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_tarski(k1_funct_1(sK4,sK2)) != k2_relset_1(k1_tarski(sK2),sK3,sK4) & k1_xboole_0 != sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK4,k1_tarski(sK2),sK3) & v1_funct_1(sK4))),
% 43.22/6.00    introduced(choice_axiom,[])).
% 43.22/6.00  
% 43.22/6.00  fof(f78,plain,(
% 43.22/6.00    k1_tarski(k1_funct_1(sK4,sK2)) != k2_relset_1(k1_tarski(sK2),sK3,sK4) & k1_xboole_0 != sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK4,k1_tarski(sK2),sK3) & v1_funct_1(sK4)),
% 43.22/6.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f62,f77])).
% 43.22/6.00  
% 43.22/6.00  fof(f136,plain,(
% 43.22/6.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))),
% 43.22/6.00    inference(cnf_transformation,[],[f78])).
% 43.22/6.00  
% 43.22/6.00  fof(f5,axiom,(
% 43.22/6.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 43.22/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.22/6.00  
% 43.22/6.00  fof(f88,plain,(
% 43.22/6.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 43.22/6.00    inference(cnf_transformation,[],[f5])).
% 43.22/6.00  
% 43.22/6.00  fof(f6,axiom,(
% 43.22/6.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 43.22/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.22/6.00  
% 43.22/6.00  fof(f89,plain,(
% 43.22/6.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 43.22/6.00    inference(cnf_transformation,[],[f6])).
% 43.22/6.00  
% 43.22/6.00  fof(f7,axiom,(
% 43.22/6.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 43.22/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.22/6.00  
% 43.22/6.00  fof(f90,plain,(
% 43.22/6.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 43.22/6.00    inference(cnf_transformation,[],[f7])).
% 43.22/6.00  
% 43.22/6.00  fof(f139,plain,(
% 43.22/6.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 43.22/6.00    inference(definition_unfolding,[],[f89,f90])).
% 43.22/6.00  
% 43.22/6.00  fof(f140,plain,(
% 43.22/6.00    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 43.22/6.00    inference(definition_unfolding,[],[f88,f139])).
% 43.22/6.00  
% 43.22/6.00  fof(f161,plain,(
% 43.22/6.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))),
% 43.22/6.00    inference(definition_unfolding,[],[f136,f140])).
% 43.22/6.00  
% 43.22/6.00  fof(f24,axiom,(
% 43.22/6.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 43.22/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.22/6.00  
% 43.22/6.00  fof(f33,plain,(
% 43.22/6.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 43.22/6.00    inference(pure_predicate_removal,[],[f24])).
% 43.22/6.00  
% 43.22/6.00  fof(f53,plain,(
% 43.22/6.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 43.22/6.00    inference(ennf_transformation,[],[f33])).
% 43.22/6.00  
% 43.22/6.00  fof(f123,plain,(
% 43.22/6.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 43.22/6.00    inference(cnf_transformation,[],[f53])).
% 43.22/6.00  
% 43.22/6.00  fof(f15,axiom,(
% 43.22/6.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 43.22/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.22/6.00  
% 43.22/6.00  fof(f40,plain,(
% 43.22/6.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 43.22/6.00    inference(ennf_transformation,[],[f15])).
% 43.22/6.00  
% 43.22/6.00  fof(f73,plain,(
% 43.22/6.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 43.22/6.00    inference(nnf_transformation,[],[f40])).
% 43.22/6.00  
% 43.22/6.00  fof(f109,plain,(
% 43.22/6.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 43.22/6.00    inference(cnf_transformation,[],[f73])).
% 43.22/6.00  
% 43.22/6.00  fof(f10,axiom,(
% 43.22/6.00    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 43.22/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.22/6.00  
% 43.22/6.00  fof(f36,plain,(
% 43.22/6.00    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3))),
% 43.22/6.00    inference(ennf_transformation,[],[f10])).
% 43.22/6.00  
% 43.22/6.00  fof(f70,plain,(
% 43.22/6.00    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & ((k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3) | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 43.22/6.00    inference(nnf_transformation,[],[f36])).
% 43.22/6.00  
% 43.22/6.00  fof(f71,plain,(
% 43.22/6.00    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 43.22/6.00    inference(flattening,[],[f70])).
% 43.22/6.00  
% 43.22/6.00  fof(f95,plain,(
% 43.22/6.00    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))) )),
% 43.22/6.00    inference(cnf_transformation,[],[f71])).
% 43.22/6.00  
% 43.22/6.00  fof(f156,plain,(
% 43.22/6.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X0,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X2) = X3 | k2_enumset1(X1,X1,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X1) = X3 | k2_enumset1(X2,X2,X2,X2) = X3 | k2_enumset1(X1,X1,X1,X1) = X3 | k2_enumset1(X0,X0,X0,X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k2_enumset1(X0,X0,X1,X2))) )),
% 43.22/6.00    inference(definition_unfolding,[],[f95,f90,f139,f139,f139,f140,f140,f140,f90])).
% 43.22/6.00  
% 43.22/6.00  fof(f1,axiom,(
% 43.22/6.00    v1_xboole_0(o_0_0_xboole_0)),
% 43.22/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.22/6.00  
% 43.22/6.00  fof(f79,plain,(
% 43.22/6.00    v1_xboole_0(o_0_0_xboole_0)),
% 43.22/6.00    inference(cnf_transformation,[],[f1])).
% 43.22/6.00  
% 43.22/6.00  fof(f2,axiom,(
% 43.22/6.00    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 43.22/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.22/6.00  
% 43.22/6.00  fof(f35,plain,(
% 43.22/6.00    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 43.22/6.00    inference(ennf_transformation,[],[f2])).
% 43.22/6.00  
% 43.22/6.00  fof(f80,plain,(
% 43.22/6.00    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 43.22/6.00    inference(cnf_transformation,[],[f35])).
% 43.22/6.00  
% 43.22/6.00  fof(f23,axiom,(
% 43.22/6.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 43.22/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.22/6.00  
% 43.22/6.00  fof(f52,plain,(
% 43.22/6.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 43.22/6.00    inference(ennf_transformation,[],[f23])).
% 43.22/6.00  
% 43.22/6.00  fof(f122,plain,(
% 43.22/6.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 43.22/6.00    inference(cnf_transformation,[],[f52])).
% 43.22/6.00  
% 43.22/6.00  fof(f135,plain,(
% 43.22/6.00    v1_funct_2(sK4,k1_tarski(sK2),sK3)),
% 43.22/6.00    inference(cnf_transformation,[],[f78])).
% 43.22/6.00  
% 43.22/6.00  fof(f162,plain,(
% 43.22/6.00    v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3)),
% 43.22/6.00    inference(definition_unfolding,[],[f135,f140])).
% 43.22/6.00  
% 43.22/6.00  fof(f134,plain,(
% 43.22/6.00    v1_funct_1(sK4)),
% 43.22/6.00    inference(cnf_transformation,[],[f78])).
% 43.22/6.00  
% 43.22/6.00  fof(f138,plain,(
% 43.22/6.00    k1_tarski(k1_funct_1(sK4,sK2)) != k2_relset_1(k1_tarski(sK2),sK3,sK4)),
% 43.22/6.00    inference(cnf_transformation,[],[f78])).
% 43.22/6.00  
% 43.22/6.00  fof(f160,plain,(
% 43.22/6.00    k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)),
% 43.22/6.00    inference(definition_unfolding,[],[f138,f140,f140])).
% 43.22/6.00  
% 43.22/6.00  fof(f27,axiom,(
% 43.22/6.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 43.22/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.22/6.00  
% 43.22/6.00  fof(f56,plain,(
% 43.22/6.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 43.22/6.00    inference(ennf_transformation,[],[f27])).
% 43.22/6.00  
% 43.22/6.00  fof(f126,plain,(
% 43.22/6.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 43.22/6.00    inference(cnf_transformation,[],[f56])).
% 43.22/6.00  
% 43.22/6.00  fof(f17,axiom,(
% 43.22/6.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 43.22/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.22/6.00  
% 43.22/6.00  fof(f42,plain,(
% 43.22/6.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 43.22/6.00    inference(ennf_transformation,[],[f17])).
% 43.22/6.00  
% 43.22/6.00  fof(f43,plain,(
% 43.22/6.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 43.22/6.00    inference(flattening,[],[f42])).
% 43.22/6.00  
% 43.22/6.00  fof(f112,plain,(
% 43.22/6.00    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 43.22/6.00    inference(cnf_transformation,[],[f43])).
% 43.22/6.00  
% 43.22/6.00  fof(f22,axiom,(
% 43.22/6.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0)))))),
% 43.22/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.22/6.00  
% 43.22/6.00  fof(f50,plain,(
% 43.22/6.00    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 43.22/6.00    inference(ennf_transformation,[],[f22])).
% 43.22/6.00  
% 43.22/6.00  fof(f51,plain,(
% 43.22/6.00    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 43.22/6.00    inference(flattening,[],[f50])).
% 43.22/6.00  
% 43.22/6.00  fof(f121,plain,(
% 43.22/6.00    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 43.22/6.00    inference(cnf_transformation,[],[f51])).
% 43.22/6.00  
% 43.22/6.00  fof(f159,plain,(
% 43.22/6.00    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k2_enumset1(X0,X0,X0,X0))) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 43.22/6.00    inference(definition_unfolding,[],[f121,f140,f140])).
% 43.22/6.00  
% 43.22/6.00  fof(f4,axiom,(
% 43.22/6.00    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 43.22/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.22/6.00  
% 43.22/6.00  fof(f63,plain,(
% 43.22/6.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 43.22/6.00    inference(nnf_transformation,[],[f4])).
% 43.22/6.00  
% 43.22/6.00  fof(f64,plain,(
% 43.22/6.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 43.22/6.00    inference(flattening,[],[f63])).
% 43.22/6.00  
% 43.22/6.00  fof(f65,plain,(
% 43.22/6.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 43.22/6.00    inference(rectify,[],[f64])).
% 43.22/6.00  
% 43.22/6.00  fof(f66,plain,(
% 43.22/6.00    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 43.22/6.00    introduced(choice_axiom,[])).
% 43.22/6.00  
% 43.22/6.00  fof(f67,plain,(
% 43.22/6.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 43.22/6.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f65,f66])).
% 43.22/6.00  
% 43.22/6.00  fof(f83,plain,(
% 43.22/6.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 43.22/6.00    inference(cnf_transformation,[],[f67])).
% 43.22/6.00  
% 43.22/6.00  fof(f145,plain,(
% 43.22/6.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 43.22/6.00    inference(definition_unfolding,[],[f83,f139])).
% 43.22/6.00  
% 43.22/6.00  fof(f165,plain,(
% 43.22/6.00    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 43.22/6.00    inference(equality_resolution,[],[f145])).
% 43.22/6.00  
% 43.22/6.00  fof(f166,plain,(
% 43.22/6.00    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 43.22/6.00    inference(equality_resolution,[],[f165])).
% 43.22/6.00  
% 43.22/6.00  fof(f26,axiom,(
% 43.22/6.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 43.22/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.22/6.00  
% 43.22/6.00  fof(f55,plain,(
% 43.22/6.00    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 43.22/6.00    inference(ennf_transformation,[],[f26])).
% 43.22/6.00  
% 43.22/6.00  fof(f125,plain,(
% 43.22/6.00    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 43.22/6.00    inference(cnf_transformation,[],[f55])).
% 43.22/6.00  
% 43.22/6.00  fof(f12,axiom,(
% 43.22/6.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 43.22/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.22/6.00  
% 43.22/6.00  fof(f72,plain,(
% 43.22/6.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 43.22/6.00    inference(nnf_transformation,[],[f12])).
% 43.22/6.00  
% 43.22/6.00  fof(f105,plain,(
% 43.22/6.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 43.22/6.00    inference(cnf_transformation,[],[f72])).
% 43.22/6.00  
% 43.22/6.00  fof(f9,axiom,(
% 43.22/6.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 43.22/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.22/6.00  
% 43.22/6.00  fof(f68,plain,(
% 43.22/6.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 43.22/6.00    inference(nnf_transformation,[],[f9])).
% 43.22/6.00  
% 43.22/6.00  fof(f69,plain,(
% 43.22/6.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 43.22/6.00    inference(flattening,[],[f68])).
% 43.22/6.00  
% 43.22/6.00  fof(f93,plain,(
% 43.22/6.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 43.22/6.00    inference(cnf_transformation,[],[f69])).
% 43.22/6.00  
% 43.22/6.00  fof(f169,plain,(
% 43.22/6.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 43.22/6.00    inference(equality_resolution,[],[f93])).
% 43.22/6.00  
% 43.22/6.00  fof(f28,axiom,(
% 43.22/6.00    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 43.22/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.22/6.00  
% 43.22/6.00  fof(f57,plain,(
% 43.22/6.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 43.22/6.00    inference(ennf_transformation,[],[f28])).
% 43.22/6.00  
% 43.22/6.00  fof(f58,plain,(
% 43.22/6.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 43.22/6.00    inference(flattening,[],[f57])).
% 43.22/6.00  
% 43.22/6.00  fof(f127,plain,(
% 43.22/6.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 43.22/6.00    inference(cnf_transformation,[],[f58])).
% 43.22/6.00  
% 43.22/6.00  fof(f3,axiom,(
% 43.22/6.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 43.22/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.22/6.00  
% 43.22/6.00  fof(f81,plain,(
% 43.22/6.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 43.22/6.00    inference(cnf_transformation,[],[f3])).
% 43.22/6.00  
% 43.22/6.00  fof(f25,axiom,(
% 43.22/6.00    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 43.22/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.22/6.00  
% 43.22/6.00  fof(f54,plain,(
% 43.22/6.00    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 43.22/6.00    inference(ennf_transformation,[],[f25])).
% 43.22/6.00  
% 43.22/6.00  fof(f124,plain,(
% 43.22/6.00    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 43.22/6.00    inference(cnf_transformation,[],[f54])).
% 43.22/6.00  
% 43.22/6.00  fof(f20,axiom,(
% 43.22/6.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 43.22/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.22/6.00  
% 43.22/6.00  fof(f46,plain,(
% 43.22/6.00    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 43.22/6.00    inference(ennf_transformation,[],[f20])).
% 43.22/6.00  
% 43.22/6.00  fof(f47,plain,(
% 43.22/6.00    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 43.22/6.00    inference(flattening,[],[f46])).
% 43.22/6.00  
% 43.22/6.00  fof(f74,plain,(
% 43.22/6.00    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 43.22/6.00    inference(nnf_transformation,[],[f47])).
% 43.22/6.00  
% 43.22/6.00  fof(f119,plain,(
% 43.22/6.00    ( ! [X2,X0,X1] : (k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2 | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 43.22/6.00    inference(cnf_transformation,[],[f74])).
% 43.22/6.00  
% 43.22/6.00  fof(f178,plain,(
% 43.22/6.00    ( ! [X0,X1] : (k1_xboole_0 = k1_funct_1(X0,X1) | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 43.22/6.00    inference(equality_resolution,[],[f119])).
% 43.22/6.00  
% 43.22/6.00  fof(f13,axiom,(
% 43.22/6.00    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 43.22/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.22/6.00  
% 43.22/6.00  fof(f37,plain,(
% 43.22/6.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 43.22/6.00    inference(ennf_transformation,[],[f13])).
% 43.22/6.00  
% 43.22/6.00  fof(f38,plain,(
% 43.22/6.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 43.22/6.00    inference(flattening,[],[f37])).
% 43.22/6.00  
% 43.22/6.00  fof(f107,plain,(
% 43.22/6.00    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 43.22/6.00    inference(cnf_transformation,[],[f38])).
% 43.22/6.00  
% 43.22/6.00  fof(f11,axiom,(
% 43.22/6.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 43.22/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.22/6.00  
% 43.22/6.00  fof(f104,plain,(
% 43.22/6.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 43.22/6.00    inference(cnf_transformation,[],[f11])).
% 43.22/6.00  
% 43.22/6.00  fof(f85,plain,(
% 43.22/6.00    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 43.22/6.00    inference(cnf_transformation,[],[f67])).
% 43.22/6.00  
% 43.22/6.00  fof(f143,plain,(
% 43.22/6.00    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X0,X1) = X2 | sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 43.22/6.00    inference(definition_unfolding,[],[f85,f139])).
% 43.22/6.00  
% 43.22/6.00  fof(f87,plain,(
% 43.22/6.00    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK0(X0,X1,X2) != X1 | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 43.22/6.00    inference(cnf_transformation,[],[f67])).
% 43.22/6.00  
% 43.22/6.00  fof(f141,plain,(
% 43.22/6.00    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X0,X1) = X2 | sK0(X0,X1,X2) != X1 | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 43.22/6.00    inference(definition_unfolding,[],[f87,f139])).
% 43.22/6.00  
% 43.22/6.00  fof(f18,axiom,(
% 43.22/6.00    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 43.22/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.22/6.00  
% 43.22/6.00  fof(f114,plain,(
% 43.22/6.00    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 43.22/6.00    inference(cnf_transformation,[],[f18])).
% 43.22/6.00  
% 43.22/6.00  fof(f84,plain,(
% 43.22/6.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 43.22/6.00    inference(cnf_transformation,[],[f67])).
% 43.22/6.00  
% 43.22/6.00  fof(f144,plain,(
% 43.22/6.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 43.22/6.00    inference(definition_unfolding,[],[f84,f139])).
% 43.22/6.00  
% 43.22/6.00  fof(f163,plain,(
% 43.22/6.00    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X4) != X2) )),
% 43.22/6.00    inference(equality_resolution,[],[f144])).
% 43.22/6.00  
% 43.22/6.00  fof(f164,plain,(
% 43.22/6.00    ( ! [X4,X0] : (r2_hidden(X4,k2_enumset1(X0,X0,X0,X4))) )),
% 43.22/6.00    inference(equality_resolution,[],[f163])).
% 43.22/6.00  
% 43.22/6.00  fof(f30,axiom,(
% 43.22/6.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 43.22/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.22/6.00  
% 43.22/6.00  fof(f59,plain,(
% 43.22/6.00    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 43.22/6.00    inference(ennf_transformation,[],[f30])).
% 43.22/6.00  
% 43.22/6.00  fof(f60,plain,(
% 43.22/6.00    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 43.22/6.00    inference(flattening,[],[f59])).
% 43.22/6.00  
% 43.22/6.00  fof(f133,plain,(
% 43.22/6.00    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 43.22/6.00    inference(cnf_transformation,[],[f60])).
% 43.22/6.00  
% 43.22/6.00  fof(f86,plain,(
% 43.22/6.00    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK0(X0,X1,X2) != X0 | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 43.22/6.00    inference(cnf_transformation,[],[f67])).
% 43.22/6.00  
% 43.22/6.00  fof(f142,plain,(
% 43.22/6.00    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X0,X1) = X2 | sK0(X0,X1,X2) != X0 | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 43.22/6.00    inference(definition_unfolding,[],[f86,f139])).
% 43.22/6.00  
% 43.22/6.00  fof(f8,axiom,(
% 43.22/6.00    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 43.22/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.22/6.00  
% 43.22/6.00  fof(f91,plain,(
% 43.22/6.00    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 43.22/6.00    inference(cnf_transformation,[],[f8])).
% 43.22/6.00  
% 43.22/6.00  fof(f147,plain,(
% 43.22/6.00    ( ! [X0] : (~v1_xboole_0(k2_enumset1(X0,X0,X0,X0))) )),
% 43.22/6.00    inference(definition_unfolding,[],[f91,f140])).
% 43.22/6.00  
% 43.22/6.00  fof(f92,plain,(
% 43.22/6.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 43.22/6.00    inference(cnf_transformation,[],[f69])).
% 43.22/6.00  
% 43.22/6.00  fof(f137,plain,(
% 43.22/6.00    k1_xboole_0 != sK3),
% 43.22/6.00    inference(cnf_transformation,[],[f78])).
% 43.22/6.00  
% 43.22/6.00  cnf(c_875,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_2709,plain,
% 43.22/6.00      ( X0 != X1
% 43.22/6.00      | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) != X1
% 43.22/6.00      | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) = X0 ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_875]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_137411,plain,
% 43.22/6.00      ( X0 != k2_relat_1(X1)
% 43.22/6.00      | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) = X0
% 43.22/6.00      | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) != k2_relat_1(X1) ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_2709]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_137412,plain,
% 43.22/6.00      ( k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) != k2_relat_1(k1_xboole_0)
% 43.22/6.00      | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) = k1_xboole_0
% 43.22/6.00      | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_137411]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_54,negated_conjecture,
% 43.22/6.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) ),
% 43.22/6.00      inference(cnf_transformation,[],[f161]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_1925,plain,
% 43.22/6.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) = iProver_top ),
% 43.22/6.00      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_41,plain,
% 43.22/6.00      ( v4_relat_1(X0,X1)
% 43.22/6.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 43.22/6.00      inference(cnf_transformation,[],[f123]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_1936,plain,
% 43.22/6.00      ( v4_relat_1(X0,X1) = iProver_top
% 43.22/6.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 43.22/6.00      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_5935,plain,
% 43.22/6.00      ( v4_relat_1(sK4,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
% 43.22/6.00      inference(superposition,[status(thm)],[c_1925,c_1936]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_28,plain,
% 43.22/6.00      ( ~ v4_relat_1(X0,X1)
% 43.22/6.00      | r1_tarski(k1_relat_1(X0),X1)
% 43.22/6.00      | ~ v1_relat_1(X0) ),
% 43.22/6.00      inference(cnf_transformation,[],[f109]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_1945,plain,
% 43.22/6.00      ( v4_relat_1(X0,X1) != iProver_top
% 43.22/6.00      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 43.22/6.00      | v1_relat_1(X0) != iProver_top ),
% 43.22/6.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_21,plain,
% 43.22/6.00      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X2,X3))
% 43.22/6.00      | k2_enumset1(X1,X1,X2,X3) = X0
% 43.22/6.00      | k2_enumset1(X1,X1,X1,X3) = X0
% 43.22/6.00      | k2_enumset1(X2,X2,X2,X3) = X0
% 43.22/6.00      | k2_enumset1(X1,X1,X1,X2) = X0
% 43.22/6.00      | k2_enumset1(X3,X3,X3,X3) = X0
% 43.22/6.00      | k2_enumset1(X2,X2,X2,X2) = X0
% 43.22/6.00      | k2_enumset1(X1,X1,X1,X1) = X0
% 43.22/6.00      | k1_xboole_0 = X0 ),
% 43.22/6.00      inference(cnf_transformation,[],[f156]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_1952,plain,
% 43.22/6.00      ( k2_enumset1(X0,X0,X1,X2) = X3
% 43.22/6.00      | k2_enumset1(X0,X0,X0,X2) = X3
% 43.22/6.00      | k2_enumset1(X1,X1,X1,X2) = X3
% 43.22/6.00      | k2_enumset1(X0,X0,X0,X1) = X3
% 43.22/6.00      | k2_enumset1(X2,X2,X2,X2) = X3
% 43.22/6.00      | k2_enumset1(X1,X1,X1,X1) = X3
% 43.22/6.00      | k2_enumset1(X0,X0,X0,X0) = X3
% 43.22/6.00      | k1_xboole_0 = X3
% 43.22/6.00      | r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) != iProver_top ),
% 43.22/6.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_0,plain,
% 43.22/6.00      ( v1_xboole_0(o_0_0_xboole_0) ),
% 43.22/6.00      inference(cnf_transformation,[],[f79]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_1970,plain,
% 43.22/6.00      ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
% 43.22/6.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_1,plain,
% 43.22/6.00      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 43.22/6.00      inference(cnf_transformation,[],[f80]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_1969,plain,
% 43.22/6.00      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 43.22/6.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_3055,plain,
% 43.22/6.00      ( k1_xboole_0 = o_0_0_xboole_0 ),
% 43.22/6.00      inference(superposition,[status(thm)],[c_1970,c_1969]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_9924,plain,
% 43.22/6.00      ( k2_enumset1(X0,X0,X1,X2) = X3
% 43.22/6.00      | k2_enumset1(X0,X0,X0,X2) = X3
% 43.22/6.00      | k2_enumset1(X1,X1,X1,X2) = X3
% 43.22/6.00      | k2_enumset1(X0,X0,X0,X1) = X3
% 43.22/6.00      | k2_enumset1(X2,X2,X2,X2) = X3
% 43.22/6.00      | k2_enumset1(X1,X1,X1,X1) = X3
% 43.22/6.00      | k2_enumset1(X0,X0,X0,X0) = X3
% 43.22/6.00      | o_0_0_xboole_0 = X3
% 43.22/6.00      | r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) != iProver_top ),
% 43.22/6.00      inference(demodulation,[status(thm)],[c_1952,c_3055]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_9944,plain,
% 43.22/6.00      ( k2_enumset1(X0,X0,X0,X1) = k1_relat_1(X2)
% 43.22/6.00      | k2_enumset1(X0,X0,X1,X3) = k1_relat_1(X2)
% 43.22/6.00      | k2_enumset1(X0,X0,X0,X3) = k1_relat_1(X2)
% 43.22/6.00      | k2_enumset1(X1,X1,X1,X3) = k1_relat_1(X2)
% 43.22/6.00      | k2_enumset1(X3,X3,X3,X3) = k1_relat_1(X2)
% 43.22/6.00      | k2_enumset1(X1,X1,X1,X1) = k1_relat_1(X2)
% 43.22/6.00      | k2_enumset1(X0,X0,X0,X0) = k1_relat_1(X2)
% 43.22/6.00      | k1_relat_1(X2) = o_0_0_xboole_0
% 43.22/6.00      | v4_relat_1(X2,k2_enumset1(X0,X0,X1,X3)) != iProver_top
% 43.22/6.00      | v1_relat_1(X2) != iProver_top ),
% 43.22/6.00      inference(superposition,[status(thm)],[c_1945,c_9924]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_131752,plain,
% 43.22/6.00      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_relat_1(sK4)
% 43.22/6.00      | k1_relat_1(sK4) = o_0_0_xboole_0
% 43.22/6.00      | v1_relat_1(sK4) != iProver_top ),
% 43.22/6.00      inference(superposition,[status(thm)],[c_5935,c_9944]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_40,plain,
% 43.22/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 43.22/6.00      | v1_relat_1(X0) ),
% 43.22/6.00      inference(cnf_transformation,[],[f122]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_2350,plain,
% 43.22/6.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))
% 43.22/6.00      | v1_relat_1(sK4) ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_40]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_132292,plain,
% 43.22/6.00      ( ~ v1_relat_1(sK4)
% 43.22/6.00      | k2_enumset1(sK2,sK2,sK2,sK2) = k1_relat_1(sK4)
% 43.22/6.00      | k1_relat_1(sK4) = o_0_0_xboole_0 ),
% 43.22/6.00      inference(predicate_to_equality_rev,[status(thm)],[c_131752]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_133422,plain,
% 43.22/6.00      ( k1_relat_1(sK4) = o_0_0_xboole_0
% 43.22/6.00      | k2_enumset1(sK2,sK2,sK2,sK2) = k1_relat_1(sK4) ),
% 43.22/6.00      inference(global_propositional_subsumption,
% 43.22/6.00                [status(thm)],
% 43.22/6.00                [c_131752,c_54,c_2350,c_132292]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_133423,plain,
% 43.22/6.00      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_relat_1(sK4)
% 43.22/6.00      | k1_relat_1(sK4) = o_0_0_xboole_0 ),
% 43.22/6.00      inference(renaming,[status(thm)],[c_133422]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_55,negated_conjecture,
% 43.22/6.00      ( v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
% 43.22/6.00      inference(cnf_transformation,[],[f162]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_1924,plain,
% 43.22/6.00      ( v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3) = iProver_top ),
% 43.22/6.00      inference(predicate_to_equality,[status(thm)],[c_55]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_133553,plain,
% 43.22/6.00      ( k1_relat_1(sK4) = o_0_0_xboole_0
% 43.22/6.00      | v1_funct_2(sK4,k1_relat_1(sK4),sK3) = iProver_top ),
% 43.22/6.00      inference(superposition,[status(thm)],[c_133423,c_1924]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_56,negated_conjecture,
% 43.22/6.00      ( v1_funct_1(sK4) ),
% 43.22/6.00      inference(cnf_transformation,[],[f134]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_57,plain,
% 43.22/6.00      ( v1_funct_1(sK4) = iProver_top ),
% 43.22/6.00      inference(predicate_to_equality,[status(thm)],[c_56]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_59,plain,
% 43.22/6.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) = iProver_top ),
% 43.22/6.00      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_52,negated_conjecture,
% 43.22/6.00      ( k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) ),
% 43.22/6.00      inference(cnf_transformation,[],[f160]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_2351,plain,
% 43.22/6.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) != iProver_top
% 43.22/6.00      | v1_relat_1(sK4) = iProver_top ),
% 43.22/6.00      inference(predicate_to_equality,[status(thm)],[c_2350]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_2409,plain,
% 43.22/6.00      ( v4_relat_1(sK4,k2_enumset1(sK2,sK2,sK2,sK2))
% 43.22/6.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_41]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_44,plain,
% 43.22/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 43.22/6.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 43.22/6.00      inference(cnf_transformation,[],[f126]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_2467,plain,
% 43.22/6.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))
% 43.22/6.00      | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) = k2_relat_1(sK4) ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_44]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_30,plain,
% 43.22/6.00      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 43.22/6.00      inference(cnf_transformation,[],[f112]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_2642,plain,
% 43.22/6.00      ( ~ v4_relat_1(sK4,k2_enumset1(sK2,sK2,sK2,sK2))
% 43.22/6.00      | ~ v1_relat_1(sK4)
% 43.22/6.00      | k7_relat_1(sK4,k2_enumset1(sK2,sK2,sK2,sK2)) = sK4 ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_30]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_888,plain,
% 43.22/6.00      ( X0 != X1 | k2_relat_1(X0) = k2_relat_1(X1) ),
% 43.22/6.00      theory(equality) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_3906,plain,
% 43.22/6.00      ( X0 != sK4 | k2_relat_1(X0) = k2_relat_1(sK4) ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_888]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_4883,plain,
% 43.22/6.00      ( k7_relat_1(sK4,k2_enumset1(sK2,sK2,sK2,sK2)) != sK4
% 43.22/6.00      | k2_relat_1(k7_relat_1(sK4,k2_enumset1(sK2,sK2,sK2,sK2))) = k2_relat_1(sK4) ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_3906]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_3104,plain,
% 43.22/6.00      ( X0 != k2_relat_1(sK4)
% 43.22/6.00      | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) = X0
% 43.22/6.00      | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) != k2_relat_1(sK4) ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_2709]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_3905,plain,
% 43.22/6.00      ( k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) = k2_relat_1(X0)
% 43.22/6.00      | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) != k2_relat_1(sK4)
% 43.22/6.00      | k2_relat_1(X0) != k2_relat_1(sK4) ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_3104]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_6917,plain,
% 43.22/6.00      ( k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) = k2_relat_1(k7_relat_1(sK4,k2_enumset1(sK2,sK2,sK2,sK2)))
% 43.22/6.00      | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) != k2_relat_1(sK4)
% 43.22/6.00      | k2_relat_1(k7_relat_1(sK4,k2_enumset1(sK2,sK2,sK2,sK2))) != k2_relat_1(sK4) ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_3905]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_2435,plain,
% 43.22/6.00      ( k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != X0
% 43.22/6.00      | k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) = k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)
% 43.22/6.00      | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) != X0 ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_875]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_19022,plain,
% 43.22/6.00      ( k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) = k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)
% 43.22/6.00      | k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k2_relat_1(k7_relat_1(sK4,k2_enumset1(sK2,sK2,sK2,sK2)))
% 43.22/6.00      | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) != k2_relat_1(k7_relat_1(sK4,k2_enumset1(sK2,sK2,sK2,sK2))) ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_2435]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_39,plain,
% 43.22/6.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 43.22/6.00      | ~ v1_funct_1(X1)
% 43.22/6.00      | ~ v1_relat_1(X1)
% 43.22/6.00      | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k2_enumset1(X0,X0,X0,X0))) ),
% 43.22/6.00      inference(cnf_transformation,[],[f159]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_25783,plain,
% 43.22/6.00      ( ~ r2_hidden(sK2,k1_relat_1(sK4))
% 43.22/6.00      | ~ v1_funct_1(sK4)
% 43.22/6.00      | ~ v1_relat_1(sK4)
% 43.22/6.00      | k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) = k2_relat_1(k7_relat_1(sK4,k2_enumset1(sK2,sK2,sK2,sK2))) ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_39]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_25784,plain,
% 43.22/6.00      ( k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) = k2_relat_1(k7_relat_1(sK4,k2_enumset1(sK2,sK2,sK2,sK2)))
% 43.22/6.00      | r2_hidden(sK2,k1_relat_1(sK4)) != iProver_top
% 43.22/6.00      | v1_funct_1(sK4) != iProver_top
% 43.22/6.00      | v1_relat_1(sK4) != iProver_top ),
% 43.22/6.00      inference(predicate_to_equality,[status(thm)],[c_25783]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_7,plain,
% 43.22/6.00      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
% 43.22/6.00      inference(cnf_transformation,[],[f166]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_1963,plain,
% 43.22/6.00      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
% 43.22/6.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_133450,plain,
% 43.22/6.00      ( k1_relat_1(sK4) = o_0_0_xboole_0
% 43.22/6.00      | r2_hidden(sK2,k1_relat_1(sK4)) = iProver_top ),
% 43.22/6.00      inference(superposition,[status(thm)],[c_133423,c_1963]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_135113,plain,
% 43.22/6.00      ( k1_relat_1(sK4) = o_0_0_xboole_0 ),
% 43.22/6.00      inference(global_propositional_subsumption,
% 43.22/6.00                [status(thm)],
% 43.22/6.00                [c_133553,c_57,c_54,c_59,c_52,c_2350,c_2351,c_2409,
% 43.22/6.00                 c_2467,c_2642,c_4883,c_6917,c_19022,c_25784,c_133450]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_1933,plain,
% 43.22/6.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 43.22/6.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 43.22/6.00      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_6127,plain,
% 43.22/6.00      ( k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) = k2_relat_1(sK4) ),
% 43.22/6.00      inference(superposition,[status(thm)],[c_1925,c_1933]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_43,plain,
% 43.22/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 43.22/6.00      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 43.22/6.00      inference(cnf_transformation,[],[f125]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_1934,plain,
% 43.22/6.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 43.22/6.00      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 43.22/6.00      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_6588,plain,
% 43.22/6.00      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK3)) = iProver_top
% 43.22/6.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) != iProver_top ),
% 43.22/6.00      inference(superposition,[status(thm)],[c_6127,c_1934]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_6782,plain,
% 43.22/6.00      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK3)) = iProver_top ),
% 43.22/6.00      inference(global_propositional_subsumption,
% 43.22/6.00                [status(thm)],
% 43.22/6.00                [c_6588,c_59]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_24,plain,
% 43.22/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 43.22/6.00      inference(cnf_transformation,[],[f105]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_1949,plain,
% 43.22/6.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 43.22/6.00      | r1_tarski(X0,X1) = iProver_top ),
% 43.22/6.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_6787,plain,
% 43.22/6.00      ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
% 43.22/6.00      inference(superposition,[status(thm)],[c_6782,c_1949]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_11,plain,
% 43.22/6.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 43.22/6.00      inference(cnf_transformation,[],[f169]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_3164,plain,
% 43.22/6.00      ( k2_zfmisc_1(o_0_0_xboole_0,X0) = o_0_0_xboole_0 ),
% 43.22/6.00      inference(demodulation,[status(thm)],[c_3055,c_11]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_45,plain,
% 43.22/6.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 43.22/6.00      | ~ r1_tarski(k2_relat_1(X0),X2)
% 43.22/6.00      | ~ r1_tarski(k1_relat_1(X0),X1)
% 43.22/6.00      | ~ v1_relat_1(X0) ),
% 43.22/6.00      inference(cnf_transformation,[],[f127]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_1932,plain,
% 43.22/6.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 43.22/6.00      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 43.22/6.00      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 43.22/6.00      | v1_relat_1(X0) != iProver_top ),
% 43.22/6.00      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_3711,plain,
% 43.22/6.00      ( m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0)) = iProver_top
% 43.22/6.00      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 43.22/6.00      | r1_tarski(k1_relat_1(X0),o_0_0_xboole_0) != iProver_top
% 43.22/6.00      | v1_relat_1(X0) != iProver_top ),
% 43.22/6.00      inference(superposition,[status(thm)],[c_3164,c_1932]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_15613,plain,
% 43.22/6.00      ( m1_subset_1(sK4,k1_zfmisc_1(o_0_0_xboole_0)) = iProver_top
% 43.22/6.00      | r1_tarski(k1_relat_1(sK4),o_0_0_xboole_0) != iProver_top
% 43.22/6.00      | v1_relat_1(sK4) != iProver_top ),
% 43.22/6.00      inference(superposition,[status(thm)],[c_6787,c_3711]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_16703,plain,
% 43.22/6.00      ( r1_tarski(k1_relat_1(sK4),o_0_0_xboole_0) != iProver_top
% 43.22/6.00      | m1_subset_1(sK4,k1_zfmisc_1(o_0_0_xboole_0)) = iProver_top ),
% 43.22/6.00      inference(global_propositional_subsumption,
% 43.22/6.00                [status(thm)],
% 43.22/6.00                [c_15613,c_59,c_2351]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_16704,plain,
% 43.22/6.00      ( m1_subset_1(sK4,k1_zfmisc_1(o_0_0_xboole_0)) = iProver_top
% 43.22/6.00      | r1_tarski(k1_relat_1(sK4),o_0_0_xboole_0) != iProver_top ),
% 43.22/6.00      inference(renaming,[status(thm)],[c_16703]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_135149,plain,
% 43.22/6.00      ( m1_subset_1(sK4,k1_zfmisc_1(o_0_0_xboole_0)) = iProver_top
% 43.22/6.00      | r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0) != iProver_top ),
% 43.22/6.00      inference(demodulation,[status(thm)],[c_135113,c_16704]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_2,plain,
% 43.22/6.00      ( r1_tarski(k1_xboole_0,X0) ),
% 43.22/6.00      inference(cnf_transformation,[],[f81]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_1968,plain,
% 43.22/6.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 43.22/6.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_3162,plain,
% 43.22/6.00      ( r1_tarski(o_0_0_xboole_0,X0) = iProver_top ),
% 43.22/6.00      inference(demodulation,[status(thm)],[c_3055,c_1968]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_135557,plain,
% 43.22/6.00      ( m1_subset_1(sK4,k1_zfmisc_1(o_0_0_xboole_0)) = iProver_top ),
% 43.22/6.00      inference(forward_subsumption_resolution,
% 43.22/6.00                [status(thm)],
% 43.22/6.00                [c_135149,c_3162]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_42,plain,
% 43.22/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 43.22/6.00      | ~ v1_xboole_0(X2)
% 43.22/6.00      | v1_xboole_0(X0) ),
% 43.22/6.00      inference(cnf_transformation,[],[f124]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_1935,plain,
% 43.22/6.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 43.22/6.00      | v1_xboole_0(X2) != iProver_top
% 43.22/6.00      | v1_xboole_0(X0) = iProver_top ),
% 43.22/6.00      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_5644,plain,
% 43.22/6.00      ( m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0)) != iProver_top
% 43.22/6.00      | v1_xboole_0(X1) != iProver_top
% 43.22/6.00      | v1_xboole_0(X0) = iProver_top ),
% 43.22/6.00      inference(superposition,[status(thm)],[c_3164,c_1935]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_135561,plain,
% 43.22/6.00      ( v1_xboole_0(X0) != iProver_top | v1_xboole_0(sK4) = iProver_top ),
% 43.22/6.00      inference(superposition,[status(thm)],[c_135557,c_5644]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_135607,plain,
% 43.22/6.00      ( v1_xboole_0(sK4) = iProver_top
% 43.22/6.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_135561]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_34,plain,
% 43.22/6.00      ( r2_hidden(X0,k1_relat_1(X1))
% 43.22/6.00      | ~ v1_funct_1(X1)
% 43.22/6.00      | ~ v1_relat_1(X1)
% 43.22/6.00      | k1_funct_1(X1,X0) = k1_xboole_0 ),
% 43.22/6.00      inference(cnf_transformation,[],[f178]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_2631,plain,
% 43.22/6.00      ( r2_hidden(X0,k1_relat_1(sK4))
% 43.22/6.00      | ~ v1_funct_1(sK4)
% 43.22/6.00      | ~ v1_relat_1(sK4)
% 43.22/6.00      | k1_funct_1(sK4,X0) = k1_xboole_0 ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_34]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_72861,plain,
% 43.22/6.00      ( r2_hidden(sK2,k1_relat_1(sK4))
% 43.22/6.00      | ~ v1_funct_1(sK4)
% 43.22/6.00      | ~ v1_relat_1(sK4)
% 43.22/6.00      | k1_funct_1(sK4,sK2) = k1_xboole_0 ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_2631]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_879,plain,
% 43.22/6.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 43.22/6.00      theory(equality) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_61812,plain,
% 43.22/6.00      ( ~ r2_hidden(X0,X1)
% 43.22/6.00      | r2_hidden(sK0(X2,X3,X4),X4)
% 43.22/6.00      | X4 != X1
% 43.22/6.00      | sK0(X2,X3,X4) != X0 ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_879]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_61814,plain,
% 43.22/6.00      ( r2_hidden(sK0(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)
% 43.22/6.00      | ~ r2_hidden(k1_xboole_0,k1_xboole_0)
% 43.22/6.00      | sK0(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 43.22/6.00      | k1_xboole_0 != k1_xboole_0 ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_61812]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_20118,plain,
% 43.22/6.00      ( X0 != X1 | X0 = k1_funct_1(sK4,sK2) | k1_funct_1(sK4,sK2) != X1 ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_875]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_20119,plain,
% 43.22/6.00      ( k1_funct_1(sK4,sK2) != k1_xboole_0
% 43.22/6.00      | k1_xboole_0 = k1_funct_1(sK4,sK2)
% 43.22/6.00      | k1_xboole_0 != k1_xboole_0 ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_20118]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_25,plain,
% 43.22/6.00      ( m1_subset_1(X0,X1)
% 43.22/6.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 43.22/6.00      | ~ r2_hidden(X0,X2) ),
% 43.22/6.00      inference(cnf_transformation,[],[f107]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_22,plain,
% 43.22/6.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 43.22/6.00      inference(cnf_transformation,[],[f104]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_4979,plain,
% 43.22/6.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,k1_xboole_0) ),
% 43.22/6.00      inference(resolution,[status(thm)],[c_25,c_22]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_11652,plain,
% 43.22/6.00      ( ~ r2_hidden(X0,k1_xboole_0)
% 43.22/6.00      | ~ v1_xboole_0(X1)
% 43.22/6.00      | v1_xboole_0(X0) ),
% 43.22/6.00      inference(resolution,[status(thm)],[c_4979,c_42]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_5,plain,
% 43.22/6.00      ( r2_hidden(sK0(X0,X1,X2),X2)
% 43.22/6.00      | k2_enumset1(X0,X0,X0,X1) = X2
% 43.22/6.00      | sK0(X0,X1,X2) = X1
% 43.22/6.00      | sK0(X0,X1,X2) = X0 ),
% 43.22/6.00      inference(cnf_transformation,[],[f143]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_12296,plain,
% 43.22/6.00      ( ~ v1_xboole_0(X0)
% 43.22/6.00      | v1_xboole_0(sK0(X1,X2,k1_xboole_0))
% 43.22/6.00      | k2_enumset1(X1,X1,X1,X2) = k1_xboole_0
% 43.22/6.00      | sK0(X1,X2,k1_xboole_0) = X2
% 43.22/6.00      | sK0(X1,X2,k1_xboole_0) = X1 ),
% 43.22/6.00      inference(resolution,[status(thm)],[c_11652,c_5]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_12297,plain,
% 43.22/6.00      ( k2_enumset1(X0,X0,X0,X1) = k1_xboole_0
% 43.22/6.00      | sK0(X0,X1,k1_xboole_0) = X1
% 43.22/6.00      | sK0(X0,X1,k1_xboole_0) = X0
% 43.22/6.00      | v1_xboole_0(X2) != iProver_top
% 43.22/6.00      | v1_xboole_0(sK0(X0,X1,k1_xboole_0)) = iProver_top ),
% 43.22/6.00      inference(predicate_to_equality,[status(thm)],[c_12296]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_12299,plain,
% 43.22/6.00      ( k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
% 43.22/6.00      | sK0(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
% 43.22/6.00      | v1_xboole_0(sK0(k1_xboole_0,k1_xboole_0,k1_xboole_0)) = iProver_top
% 43.22/6.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_12297]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_3,plain,
% 43.22/6.00      ( ~ r2_hidden(sK0(X0,X1,X2),X2)
% 43.22/6.00      | k2_enumset1(X0,X0,X0,X1) = X2
% 43.22/6.00      | sK0(X0,X1,X2) != X1 ),
% 43.22/6.00      inference(cnf_transformation,[],[f141]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_874,plain,( X0 = X0 ),theory(equality) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_7022,plain,
% 43.22/6.00      ( X0 != X1 | X1 = X0 ),
% 43.22/6.00      inference(resolution,[status(thm)],[c_875,c_874]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_7360,plain,
% 43.22/6.00      ( ~ v1_xboole_0(X0) | X0 = k1_xboole_0 ),
% 43.22/6.00      inference(resolution,[status(thm)],[c_7022,c_1]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_9977,plain,
% 43.22/6.00      ( ~ r2_hidden(sK0(X0,k1_xboole_0,X1),X1)
% 43.22/6.00      | ~ v1_xboole_0(sK0(X0,k1_xboole_0,X1))
% 43.22/6.00      | k2_enumset1(X0,X0,X0,k1_xboole_0) = X1 ),
% 43.22/6.00      inference(resolution,[status(thm)],[c_3,c_7360]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_9978,plain,
% 43.22/6.00      ( k2_enumset1(X0,X0,X0,k1_xboole_0) = X1
% 43.22/6.00      | r2_hidden(sK0(X0,k1_xboole_0,X1),X1) != iProver_top
% 43.22/6.00      | v1_xboole_0(sK0(X0,k1_xboole_0,X1)) != iProver_top ),
% 43.22/6.00      inference(predicate_to_equality,[status(thm)],[c_9977]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_9980,plain,
% 43.22/6.00      ( k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
% 43.22/6.00      | r2_hidden(sK0(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top
% 43.22/6.00      | v1_xboole_0(sK0(k1_xboole_0,k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_9978]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_31,plain,
% 43.22/6.00      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 43.22/6.00      inference(cnf_transformation,[],[f114]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_7377,plain,
% 43.22/6.00      ( k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
% 43.22/6.00      inference(resolution,[status(thm)],[c_7022,c_31]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_4653,plain,
% 43.22/6.00      ( X0 != X1
% 43.22/6.00      | X0 = k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)
% 43.22/6.00      | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) != X1 ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_875]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_4654,plain,
% 43.22/6.00      ( k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) != k1_xboole_0
% 43.22/6.00      | k1_xboole_0 = k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)
% 43.22/6.00      | k1_xboole_0 != k1_xboole_0 ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_4653]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_3943,plain,
% 43.22/6.00      ( r2_hidden(X0,X1)
% 43.22/6.00      | ~ r2_hidden(k1_funct_1(sK4,sK2),k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4))
% 43.22/6.00      | X1 != k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)
% 43.22/6.00      | X0 != k1_funct_1(sK4,sK2) ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_879]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_3945,plain,
% 43.22/6.00      ( ~ r2_hidden(k1_funct_1(sK4,sK2),k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4))
% 43.22/6.00      | r2_hidden(k1_xboole_0,k1_xboole_0)
% 43.22/6.00      | k1_xboole_0 != k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)
% 43.22/6.00      | k1_xboole_0 != k1_funct_1(sK4,sK2) ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_3943]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_3908,plain,
% 43.22/6.00      ( k2_relat_1(k1_xboole_0) = k2_relat_1(sK4) | k1_xboole_0 != sK4 ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_3906]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_3907,plain,
% 43.22/6.00      ( k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) != k2_relat_1(sK4)
% 43.22/6.00      | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) = k2_relat_1(k1_xboole_0)
% 43.22/6.00      | k2_relat_1(k1_xboole_0) != k2_relat_1(sK4) ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_3905]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_6,plain,
% 43.22/6.00      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
% 43.22/6.00      inference(cnf_transformation,[],[f164]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_3801,plain,
% 43.22/6.00      ( r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_6]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_51,plain,
% 43.22/6.00      ( ~ v1_funct_2(X0,X1,X2)
% 43.22/6.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 43.22/6.00      | ~ r2_hidden(X3,X1)
% 43.22/6.00      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 43.22/6.00      | ~ v1_funct_1(X0)
% 43.22/6.00      | k1_xboole_0 = X2 ),
% 43.22/6.00      inference(cnf_transformation,[],[f133]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_2562,plain,
% 43.22/6.00      ( ~ v1_funct_2(X0,X1,sK3)
% 43.22/6.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK3)))
% 43.22/6.00      | ~ r2_hidden(X2,X1)
% 43.22/6.00      | r2_hidden(k1_funct_1(X0,X2),k2_relset_1(X1,sK3,X0))
% 43.22/6.00      | ~ v1_funct_1(X0)
% 43.22/6.00      | k1_xboole_0 = sK3 ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_51]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_2784,plain,
% 43.22/6.00      ( ~ v1_funct_2(sK4,X0,sK3)
% 43.22/6.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK3)))
% 43.22/6.00      | ~ r2_hidden(X1,X0)
% 43.22/6.00      | r2_hidden(k1_funct_1(sK4,X1),k2_relset_1(X0,sK3,sK4))
% 43.22/6.00      | ~ v1_funct_1(sK4)
% 43.22/6.00      | k1_xboole_0 = sK3 ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_2562]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_2838,plain,
% 43.22/6.00      ( ~ v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3)
% 43.22/6.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))
% 43.22/6.00      | ~ r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2))
% 43.22/6.00      | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4))
% 43.22/6.00      | ~ v1_funct_1(sK4)
% 43.22/6.00      | k1_xboole_0 = sK3 ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_2784]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_3800,plain,
% 43.22/6.00      ( ~ v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3)
% 43.22/6.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))
% 43.22/6.00      | r2_hidden(k1_funct_1(sK4,sK2),k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4))
% 43.22/6.00      | ~ r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2))
% 43.22/6.00      | ~ v1_funct_1(sK4)
% 43.22/6.00      | k1_xboole_0 = sK3 ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_2838]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_876,plain,
% 43.22/6.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 43.22/6.00      theory(equality) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_3270,plain,
% 43.22/6.00      ( ~ v1_xboole_0(X0)
% 43.22/6.00      | v1_xboole_0(k2_enumset1(X1,X1,X1,X1))
% 43.22/6.00      | k2_enumset1(X1,X1,X1,X1) != X0 ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_876]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_3272,plain,
% 43.22/6.00      ( v1_xboole_0(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 43.22/6.00      | ~ v1_xboole_0(k1_xboole_0)
% 43.22/6.00      | k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_3270]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_2916,plain,
% 43.22/6.00      ( ~ v1_xboole_0(sK4) | k1_xboole_0 = sK4 ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_1]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_2917,plain,
% 43.22/6.00      ( k1_xboole_0 = sK4 | v1_xboole_0(sK4) != iProver_top ),
% 43.22/6.00      inference(predicate_to_equality,[status(thm)],[c_2916]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_2368,plain,
% 43.22/6.00      ( v1_xboole_0(X0)
% 43.22/6.00      | ~ v1_xboole_0(o_0_0_xboole_0)
% 43.22/6.00      | X0 != o_0_0_xboole_0 ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_876]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_2372,plain,
% 43.22/6.00      ( X0 != o_0_0_xboole_0
% 43.22/6.00      | v1_xboole_0(X0) = iProver_top
% 43.22/6.00      | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
% 43.22/6.00      inference(predicate_to_equality,[status(thm)],[c_2368]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_2374,plain,
% 43.22/6.00      ( k1_xboole_0 != o_0_0_xboole_0
% 43.22/6.00      | v1_xboole_0(k1_xboole_0) = iProver_top
% 43.22/6.00      | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_2372]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_2373,plain,
% 43.22/6.00      ( v1_xboole_0(k1_xboole_0)
% 43.22/6.00      | ~ v1_xboole_0(o_0_0_xboole_0)
% 43.22/6.00      | k1_xboole_0 != o_0_0_xboole_0 ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_2368]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_2369,plain,
% 43.22/6.00      ( ~ v1_xboole_0(o_0_0_xboole_0) | k1_xboole_0 = o_0_0_xboole_0 ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_1]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_178,plain,
% 43.22/6.00      ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
% 43.22/6.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_4,plain,
% 43.22/6.00      ( ~ r2_hidden(sK0(X0,X1,X2),X2)
% 43.22/6.00      | k2_enumset1(X0,X0,X0,X1) = X2
% 43.22/6.00      | sK0(X0,X1,X2) != X0 ),
% 43.22/6.00      inference(cnf_transformation,[],[f142]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_169,plain,
% 43.22/6.00      ( ~ r2_hidden(sK0(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)
% 43.22/6.00      | k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
% 43.22/6.00      | sK0(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_4]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_165,plain,
% 43.22/6.00      ( k2_enumset1(X0,X0,X0,X1) = X2
% 43.22/6.00      | sK0(X0,X1,X2) = X1
% 43.22/6.00      | sK0(X0,X1,X2) = X0
% 43.22/6.00      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 43.22/6.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_167,plain,
% 43.22/6.00      ( k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
% 43.22/6.00      | sK0(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
% 43.22/6.00      | r2_hidden(sK0(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_165]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_9,plain,
% 43.22/6.00      ( ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
% 43.22/6.00      inference(cnf_transformation,[],[f147]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_156,plain,
% 43.22/6.00      ( ~ v1_xboole_0(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_9]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_154,plain,
% 43.22/6.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_11]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_12,plain,
% 43.22/6.00      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 43.22/6.00      | k1_xboole_0 = X0
% 43.22/6.00      | k1_xboole_0 = X1 ),
% 43.22/6.00      inference(cnf_transformation,[],[f92]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_153,plain,
% 43.22/6.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 43.22/6.00      | k1_xboole_0 = k1_xboole_0 ),
% 43.22/6.00      inference(instantiation,[status(thm)],[c_12]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_53,negated_conjecture,
% 43.22/6.00      ( k1_xboole_0 != sK3 ),
% 43.22/6.00      inference(cnf_transformation,[],[f137]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(contradiction,plain,
% 43.22/6.00      ( $false ),
% 43.22/6.00      inference(minisat,
% 43.22/6.00                [status(thm)],
% 43.22/6.00                [c_137412,c_135607,c_72861,c_61814,c_25783,c_20119,
% 43.22/6.00                 c_19022,c_12299,c_9980,c_7377,c_6917,c_4883,c_4654,
% 43.22/6.00                 c_3945,c_3908,c_3907,c_3801,c_3800,c_3272,c_2917,c_2642,
% 43.22/6.00                 c_2467,c_2409,c_2374,c_2373,c_2369,c_2350,c_178,c_0,
% 43.22/6.00                 c_169,c_167,c_156,c_154,c_153,c_52,c_53,c_54,c_55,c_56]) ).
% 43.22/6.00  
% 43.22/6.00  
% 43.22/6.00  % SZS output end CNFRefutation for theBenchmark.p
% 43.22/6.00  
% 43.22/6.00  ------                               Statistics
% 43.22/6.00  
% 43.22/6.00  ------ Selected
% 43.22/6.00  
% 43.22/6.00  total_time:                             5.254
% 43.22/6.00  
%------------------------------------------------------------------------------
