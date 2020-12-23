%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:45 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 731 expanded)
%              Number of clauses        :   68 ( 170 expanded)
%              Number of leaves         :   17 ( 175 expanded)
%              Depth                    :   22
%              Number of atoms          :  370 (2154 expanded)
%              Number of equality atoms :  222 ( 947 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f27])).

fof(f35,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))
      & k1_xboole_0 != sK2
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
      & v1_funct_2(sK4,k1_tarski(sK1),sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))
    & k1_xboole_0 != sK2
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
    & v1_funct_2(sK4,k1_tarski(sK1),sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f28,f35])).

fof(f62,plain,(
    v1_funct_2(sK4,k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f67,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f66])).

fof(f78,plain,(
    v1_funct_2(sK4,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
    inference(definition_unfolding,[],[f62,f67])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f63,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) ),
    inference(cnf_transformation,[],[f36])).

fof(f77,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(definition_unfolding,[],[f63,f67])).

fof(f64,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f46,f67])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f72,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f38,f66])).

fof(f81,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f72])).

fof(f82,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f81])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f48,f67])).

fof(f61,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f65,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) ),
    inference(cnf_transformation,[],[f36])).

fof(f76,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) ),
    inference(definition_unfolding,[],[f65,f67,f67])).

cnf(c_7,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1380,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK4,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_367,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_23])).

cnf(c_368,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_367])).

cnf(c_787,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) != X0
    | k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK4 != sK4
    | sK2 != X1
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_368])).

cnf(c_788,plain,
    ( k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4) = k2_enumset1(sK1,sK1,sK1,sK1)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_787])).

cnf(c_22,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_789,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
    | k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4) = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_788,c_22])).

cnf(c_790,plain,
    ( k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4) = k2_enumset1(sK1,sK1,sK1,sK1)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
    inference(renaming,[status(thm)],[c_789])).

cnf(c_850,plain,
    ( k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4) = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(equality_resolution_simp,[status(thm)],[c_790])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_439,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_23])).

cnf(c_440,plain,
    ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_439])).

cnf(c_1519,plain,
    ( k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4) = k1_relat_1(sK4) ),
    inference(equality_resolution,[status(thm)],[c_440])).

cnf(c_2034,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_850,c_1519])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_421,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_23])).

cnf(c_422,plain,
    ( k7_relset_1(X0,X1,sK4,X2) = k9_relat_1(sK4,X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_421])).

cnf(c_1522,plain,
    ( k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(equality_resolution,[status(thm)],[c_422])).

cnf(c_2036,plain,
    ( k7_relset_1(k1_relat_1(sK4),sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(demodulation,[status(thm)],[c_2034,c_1522])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_430,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_23])).

cnf(c_431,plain,
    ( k2_relset_1(X0,X1,sK4) = k2_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_430])).

cnf(c_1504,plain,
    ( k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4) = k2_relat_1(sK4) ),
    inference(equality_resolution,[status(thm)],[c_431])).

cnf(c_2038,plain,
    ( k2_relset_1(k1_relat_1(sK4),sK2,sK4) = k2_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_2034,c_1504])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_403,plain,
    ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_23])).

cnf(c_404,plain,
    ( k7_relset_1(X0,X1,sK4,X0) = k2_relset_1(X0,X1,sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_403])).

cnf(c_1558,plain,
    ( k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,k2_enumset1(sK1,sK1,sK1,sK1)) = k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4) ),
    inference(equality_resolution,[status(thm)],[c_404])).

cnf(c_2967,plain,
    ( k7_relset_1(k1_relat_1(sK4),sK2,sK4,k1_relat_1(sK4)) = k2_relset_1(k1_relat_1(sK4),sK2,sK4) ),
    inference(light_normalisation,[status(thm)],[c_1558,c_2034])).

cnf(c_3404,plain,
    ( k7_relset_1(k1_relat_1(sK4),sK2,sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_2038,c_2967])).

cnf(c_4169,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2036,c_3404])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_448,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_23])).

cnf(c_449,plain,
    ( v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_448])).

cnf(c_1377,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_449])).

cnf(c_1144,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1505,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_1144])).

cnf(c_1511,plain,
    ( v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_449])).

cnf(c_1512,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1511])).

cnf(c_2179,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1377,c_1505,c_1512])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1381,plain,
    ( k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2184,plain,
    ( k9_relat_1(sK4,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_2179,c_1381])).

cnf(c_3554,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) = k11_relat_1(sK4,sK1) ),
    inference(superposition,[status(thm)],[c_2034,c_2184])).

cnf(c_4324,plain,
    ( k11_relat_1(sK4,sK1) = k2_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_4169,c_3554])).

cnf(c_4,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1383,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2083,plain,
    ( r2_hidden(sK1,k1_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2034,c_1383])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_304,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_25])).

cnf(c_305,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_304])).

cnf(c_1378,plain,
    ( k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_305])).

cnf(c_306,plain,
    ( k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_305])).

cnf(c_2320,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1378,c_306,c_1505,c_1512])).

cnf(c_2321,plain,
    ( k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2320])).

cnf(c_3488,plain,
    ( k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k11_relat_1(sK4,sK1) ),
    inference(superposition,[status(thm)],[c_2083,c_2321])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1379,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1922,plain,
    ( r1_tarski(k9_relat_1(sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1522,c_1379])).

cnf(c_3811,plain,
    ( r1_tarski(k9_relat_1(sK4,sK3),k11_relat_1(sK4,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3488,c_1922])).

cnf(c_17508,plain,
    ( r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4324,c_3811])).

cnf(c_18092,plain,
    ( v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1380,c_17508])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18092,c_1512,c_1505])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:11:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.38/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/0.97  
% 3.38/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.38/0.97  
% 3.38/0.97  ------  iProver source info
% 3.38/0.97  
% 3.38/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.38/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.38/0.97  git: non_committed_changes: false
% 3.38/0.97  git: last_make_outside_of_git: false
% 3.38/0.97  
% 3.38/0.97  ------ 
% 3.38/0.97  
% 3.38/0.97  ------ Input Options
% 3.38/0.97  
% 3.38/0.97  --out_options                           all
% 3.38/0.97  --tptp_safe_out                         true
% 3.38/0.97  --problem_path                          ""
% 3.38/0.97  --include_path                          ""
% 3.38/0.97  --clausifier                            res/vclausify_rel
% 3.38/0.97  --clausifier_options                    --mode clausify
% 3.38/0.97  --stdin                                 false
% 3.38/0.97  --stats_out                             all
% 3.38/0.97  
% 3.38/0.97  ------ General Options
% 3.38/0.97  
% 3.38/0.97  --fof                                   false
% 3.38/0.97  --time_out_real                         305.
% 3.38/0.97  --time_out_virtual                      -1.
% 3.38/0.97  --symbol_type_check                     false
% 3.38/0.97  --clausify_out                          false
% 3.38/0.97  --sig_cnt_out                           false
% 3.38/0.97  --trig_cnt_out                          false
% 3.38/0.97  --trig_cnt_out_tolerance                1.
% 3.38/0.97  --trig_cnt_out_sk_spl                   false
% 3.38/0.97  --abstr_cl_out                          false
% 3.38/0.97  
% 3.38/0.97  ------ Global Options
% 3.38/0.97  
% 3.38/0.97  --schedule                              default
% 3.38/0.97  --add_important_lit                     false
% 3.38/0.97  --prop_solver_per_cl                    1000
% 3.38/0.97  --min_unsat_core                        false
% 3.38/0.97  --soft_assumptions                      false
% 3.38/0.97  --soft_lemma_size                       3
% 3.38/0.97  --prop_impl_unit_size                   0
% 3.38/0.97  --prop_impl_unit                        []
% 3.38/0.97  --share_sel_clauses                     true
% 3.38/0.97  --reset_solvers                         false
% 3.38/0.97  --bc_imp_inh                            [conj_cone]
% 3.38/0.97  --conj_cone_tolerance                   3.
% 3.38/0.97  --extra_neg_conj                        none
% 3.38/0.97  --large_theory_mode                     true
% 3.38/0.97  --prolific_symb_bound                   200
% 3.38/0.97  --lt_threshold                          2000
% 3.38/0.97  --clause_weak_htbl                      true
% 3.38/0.97  --gc_record_bc_elim                     false
% 3.38/0.97  
% 3.38/0.97  ------ Preprocessing Options
% 3.38/0.97  
% 3.38/0.97  --preprocessing_flag                    true
% 3.38/0.97  --time_out_prep_mult                    0.1
% 3.38/0.97  --splitting_mode                        input
% 3.38/0.97  --splitting_grd                         true
% 3.38/0.97  --splitting_cvd                         false
% 3.38/0.97  --splitting_cvd_svl                     false
% 3.38/0.97  --splitting_nvd                         32
% 3.38/0.97  --sub_typing                            true
% 3.38/0.97  --prep_gs_sim                           true
% 3.38/0.97  --prep_unflatten                        true
% 3.38/0.97  --prep_res_sim                          true
% 3.38/0.97  --prep_upred                            true
% 3.38/0.97  --prep_sem_filter                       exhaustive
% 3.38/0.97  --prep_sem_filter_out                   false
% 3.38/0.97  --pred_elim                             true
% 3.38/0.97  --res_sim_input                         true
% 3.38/0.97  --eq_ax_congr_red                       true
% 3.38/0.97  --pure_diseq_elim                       true
% 3.38/0.97  --brand_transform                       false
% 3.38/0.97  --non_eq_to_eq                          false
% 3.38/0.97  --prep_def_merge                        true
% 3.38/0.97  --prep_def_merge_prop_impl              false
% 3.38/0.97  --prep_def_merge_mbd                    true
% 3.38/0.97  --prep_def_merge_tr_red                 false
% 3.38/0.97  --prep_def_merge_tr_cl                  false
% 3.38/0.97  --smt_preprocessing                     true
% 3.38/0.97  --smt_ac_axioms                         fast
% 3.38/0.97  --preprocessed_out                      false
% 3.38/0.97  --preprocessed_stats                    false
% 3.38/0.97  
% 3.38/0.97  ------ Abstraction refinement Options
% 3.38/0.97  
% 3.38/0.97  --abstr_ref                             []
% 3.38/0.97  --abstr_ref_prep                        false
% 3.38/0.97  --abstr_ref_until_sat                   false
% 3.38/0.97  --abstr_ref_sig_restrict                funpre
% 3.38/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.38/0.97  --abstr_ref_under                       []
% 3.38/0.97  
% 3.38/0.97  ------ SAT Options
% 3.38/0.97  
% 3.38/0.97  --sat_mode                              false
% 3.38/0.97  --sat_fm_restart_options                ""
% 3.38/0.97  --sat_gr_def                            false
% 3.38/0.97  --sat_epr_types                         true
% 3.38/0.97  --sat_non_cyclic_types                  false
% 3.38/0.97  --sat_finite_models                     false
% 3.38/0.97  --sat_fm_lemmas                         false
% 3.38/0.97  --sat_fm_prep                           false
% 3.38/0.97  --sat_fm_uc_incr                        true
% 3.38/0.97  --sat_out_model                         small
% 3.38/0.97  --sat_out_clauses                       false
% 3.38/0.97  
% 3.38/0.97  ------ QBF Options
% 3.38/0.97  
% 3.38/0.97  --qbf_mode                              false
% 3.38/0.97  --qbf_elim_univ                         false
% 3.38/0.97  --qbf_dom_inst                          none
% 3.38/0.97  --qbf_dom_pre_inst                      false
% 3.38/0.97  --qbf_sk_in                             false
% 3.38/0.97  --qbf_pred_elim                         true
% 3.38/0.97  --qbf_split                             512
% 3.38/0.97  
% 3.38/0.97  ------ BMC1 Options
% 3.38/0.97  
% 3.38/0.97  --bmc1_incremental                      false
% 3.38/0.97  --bmc1_axioms                           reachable_all
% 3.38/0.97  --bmc1_min_bound                        0
% 3.38/0.97  --bmc1_max_bound                        -1
% 3.38/0.97  --bmc1_max_bound_default                -1
% 3.38/0.97  --bmc1_symbol_reachability              true
% 3.38/0.97  --bmc1_property_lemmas                  false
% 3.38/0.97  --bmc1_k_induction                      false
% 3.38/0.97  --bmc1_non_equiv_states                 false
% 3.38/0.97  --bmc1_deadlock                         false
% 3.38/0.97  --bmc1_ucm                              false
% 3.38/0.97  --bmc1_add_unsat_core                   none
% 3.38/0.97  --bmc1_unsat_core_children              false
% 3.38/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.38/0.97  --bmc1_out_stat                         full
% 3.38/0.97  --bmc1_ground_init                      false
% 3.38/0.97  --bmc1_pre_inst_next_state              false
% 3.38/0.97  --bmc1_pre_inst_state                   false
% 3.38/0.97  --bmc1_pre_inst_reach_state             false
% 3.38/0.97  --bmc1_out_unsat_core                   false
% 3.38/0.97  --bmc1_aig_witness_out                  false
% 3.38/0.97  --bmc1_verbose                          false
% 3.38/0.97  --bmc1_dump_clauses_tptp                false
% 3.38/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.38/0.97  --bmc1_dump_file                        -
% 3.38/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.38/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.38/0.97  --bmc1_ucm_extend_mode                  1
% 3.38/0.97  --bmc1_ucm_init_mode                    2
% 3.38/0.97  --bmc1_ucm_cone_mode                    none
% 3.38/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.38/0.97  --bmc1_ucm_relax_model                  4
% 3.38/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.38/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.38/0.97  --bmc1_ucm_layered_model                none
% 3.38/0.97  --bmc1_ucm_max_lemma_size               10
% 3.38/0.97  
% 3.38/0.97  ------ AIG Options
% 3.38/0.97  
% 3.38/0.97  --aig_mode                              false
% 3.38/0.97  
% 3.38/0.97  ------ Instantiation Options
% 3.38/0.97  
% 3.38/0.97  --instantiation_flag                    true
% 3.38/0.97  --inst_sos_flag                         false
% 3.38/0.97  --inst_sos_phase                        true
% 3.38/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.38/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.38/0.97  --inst_lit_sel_side                     num_symb
% 3.38/0.97  --inst_solver_per_active                1400
% 3.38/0.97  --inst_solver_calls_frac                1.
% 3.38/0.97  --inst_passive_queue_type               priority_queues
% 3.38/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.38/0.97  --inst_passive_queues_freq              [25;2]
% 3.38/0.97  --inst_dismatching                      true
% 3.38/0.97  --inst_eager_unprocessed_to_passive     true
% 3.38/0.97  --inst_prop_sim_given                   true
% 3.38/0.97  --inst_prop_sim_new                     false
% 3.38/0.97  --inst_subs_new                         false
% 3.38/0.97  --inst_eq_res_simp                      false
% 3.38/0.97  --inst_subs_given                       false
% 3.38/0.97  --inst_orphan_elimination               true
% 3.38/0.97  --inst_learning_loop_flag               true
% 3.38/0.97  --inst_learning_start                   3000
% 3.38/0.97  --inst_learning_factor                  2
% 3.38/0.97  --inst_start_prop_sim_after_learn       3
% 3.38/0.97  --inst_sel_renew                        solver
% 3.38/0.97  --inst_lit_activity_flag                true
% 3.38/0.97  --inst_restr_to_given                   false
% 3.38/0.97  --inst_activity_threshold               500
% 3.38/0.97  --inst_out_proof                        true
% 3.38/0.97  
% 3.38/0.97  ------ Resolution Options
% 3.38/0.97  
% 3.38/0.97  --resolution_flag                       true
% 3.38/0.97  --res_lit_sel                           adaptive
% 3.38/0.97  --res_lit_sel_side                      none
% 3.38/0.97  --res_ordering                          kbo
% 3.38/0.97  --res_to_prop_solver                    active
% 3.38/0.97  --res_prop_simpl_new                    false
% 3.38/0.97  --res_prop_simpl_given                  true
% 3.38/0.97  --res_passive_queue_type                priority_queues
% 3.38/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.38/0.97  --res_passive_queues_freq               [15;5]
% 3.38/0.97  --res_forward_subs                      full
% 3.38/0.97  --res_backward_subs                     full
% 3.38/0.97  --res_forward_subs_resolution           true
% 3.38/0.97  --res_backward_subs_resolution          true
% 3.38/0.97  --res_orphan_elimination                true
% 3.38/0.97  --res_time_limit                        2.
% 3.38/0.97  --res_out_proof                         true
% 3.38/0.97  
% 3.38/0.97  ------ Superposition Options
% 3.38/0.97  
% 3.38/0.97  --superposition_flag                    true
% 3.38/0.97  --sup_passive_queue_type                priority_queues
% 3.38/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.38/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.38/0.97  --demod_completeness_check              fast
% 3.38/0.97  --demod_use_ground                      true
% 3.38/0.97  --sup_to_prop_solver                    passive
% 3.38/0.97  --sup_prop_simpl_new                    true
% 3.38/0.97  --sup_prop_simpl_given                  true
% 3.38/0.97  --sup_fun_splitting                     false
% 3.38/0.97  --sup_smt_interval                      50000
% 3.38/0.97  
% 3.38/0.97  ------ Superposition Simplification Setup
% 3.38/0.97  
% 3.38/0.97  --sup_indices_passive                   []
% 3.38/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.38/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.38/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.38/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.38/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.38/0.97  --sup_full_bw                           [BwDemod]
% 3.38/0.97  --sup_immed_triv                        [TrivRules]
% 3.38/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.38/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.38/0.97  --sup_immed_bw_main                     []
% 3.38/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.38/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.38/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.38/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.38/0.97  
% 3.38/0.97  ------ Combination Options
% 3.38/0.97  
% 3.38/0.97  --comb_res_mult                         3
% 3.38/0.97  --comb_sup_mult                         2
% 3.38/0.97  --comb_inst_mult                        10
% 3.38/0.97  
% 3.38/0.97  ------ Debug Options
% 3.38/0.97  
% 3.38/0.97  --dbg_backtrace                         false
% 3.38/0.97  --dbg_dump_prop_clauses                 false
% 3.38/0.97  --dbg_dump_prop_clauses_file            -
% 3.38/0.97  --dbg_out_stat                          false
% 3.38/0.97  ------ Parsing...
% 3.38/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.38/0.97  
% 3.38/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.38/0.97  
% 3.38/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.38/0.97  
% 3.38/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.38/0.97  ------ Proving...
% 3.38/0.97  ------ Problem Properties 
% 3.38/0.97  
% 3.38/0.97  
% 3.38/0.97  clauses                                 20
% 3.38/0.97  conjectures                             2
% 3.38/0.97  EPR                                     1
% 3.38/0.97  Horn                                    17
% 3.38/0.97  unary                                   5
% 3.38/0.97  binary                                  8
% 3.38/0.97  lits                                    44
% 3.38/0.97  lits eq                                 31
% 3.38/0.97  fd_pure                                 0
% 3.38/0.97  fd_pseudo                               0
% 3.38/0.97  fd_cond                                 0
% 3.38/0.97  fd_pseudo_cond                          3
% 3.38/0.97  AC symbols                              0
% 3.38/0.97  
% 3.38/0.97  ------ Schedule dynamic 5 is on 
% 3.38/0.97  
% 3.38/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.38/0.97  
% 3.38/0.97  
% 3.38/0.97  ------ 
% 3.38/0.97  Current options:
% 3.38/0.97  ------ 
% 3.38/0.97  
% 3.38/0.97  ------ Input Options
% 3.38/0.97  
% 3.38/0.97  --out_options                           all
% 3.38/0.97  --tptp_safe_out                         true
% 3.38/0.97  --problem_path                          ""
% 3.38/0.97  --include_path                          ""
% 3.38/0.97  --clausifier                            res/vclausify_rel
% 3.38/0.97  --clausifier_options                    --mode clausify
% 3.38/0.97  --stdin                                 false
% 3.38/0.97  --stats_out                             all
% 3.38/0.97  
% 3.38/0.97  ------ General Options
% 3.38/0.97  
% 3.38/0.97  --fof                                   false
% 3.38/0.97  --time_out_real                         305.
% 3.38/0.97  --time_out_virtual                      -1.
% 3.38/0.97  --symbol_type_check                     false
% 3.38/0.97  --clausify_out                          false
% 3.38/0.97  --sig_cnt_out                           false
% 3.38/0.97  --trig_cnt_out                          false
% 3.38/0.97  --trig_cnt_out_tolerance                1.
% 3.38/0.97  --trig_cnt_out_sk_spl                   false
% 3.38/0.97  --abstr_cl_out                          false
% 3.38/0.97  
% 3.38/0.97  ------ Global Options
% 3.38/0.97  
% 3.38/0.97  --schedule                              default
% 3.38/0.97  --add_important_lit                     false
% 3.38/0.97  --prop_solver_per_cl                    1000
% 3.38/0.97  --min_unsat_core                        false
% 3.38/0.97  --soft_assumptions                      false
% 3.38/0.97  --soft_lemma_size                       3
% 3.38/0.97  --prop_impl_unit_size                   0
% 3.38/0.97  --prop_impl_unit                        []
% 3.38/0.97  --share_sel_clauses                     true
% 3.38/0.97  --reset_solvers                         false
% 3.38/0.97  --bc_imp_inh                            [conj_cone]
% 3.38/0.97  --conj_cone_tolerance                   3.
% 3.38/0.97  --extra_neg_conj                        none
% 3.38/0.97  --large_theory_mode                     true
% 3.38/0.97  --prolific_symb_bound                   200
% 3.38/0.97  --lt_threshold                          2000
% 3.38/0.97  --clause_weak_htbl                      true
% 3.38/0.97  --gc_record_bc_elim                     false
% 3.38/0.97  
% 3.38/0.97  ------ Preprocessing Options
% 3.38/0.97  
% 3.38/0.97  --preprocessing_flag                    true
% 3.38/0.97  --time_out_prep_mult                    0.1
% 3.38/0.97  --splitting_mode                        input
% 3.38/0.97  --splitting_grd                         true
% 3.38/0.97  --splitting_cvd                         false
% 3.38/0.97  --splitting_cvd_svl                     false
% 3.38/0.97  --splitting_nvd                         32
% 3.38/0.97  --sub_typing                            true
% 3.38/0.97  --prep_gs_sim                           true
% 3.38/0.97  --prep_unflatten                        true
% 3.38/0.97  --prep_res_sim                          true
% 3.38/0.97  --prep_upred                            true
% 3.38/0.97  --prep_sem_filter                       exhaustive
% 3.38/0.97  --prep_sem_filter_out                   false
% 3.38/0.97  --pred_elim                             true
% 3.38/0.97  --res_sim_input                         true
% 3.38/0.97  --eq_ax_congr_red                       true
% 3.38/0.97  --pure_diseq_elim                       true
% 3.38/0.97  --brand_transform                       false
% 3.38/0.97  --non_eq_to_eq                          false
% 3.38/0.97  --prep_def_merge                        true
% 3.38/0.97  --prep_def_merge_prop_impl              false
% 3.38/0.97  --prep_def_merge_mbd                    true
% 3.38/0.97  --prep_def_merge_tr_red                 false
% 3.38/0.97  --prep_def_merge_tr_cl                  false
% 3.38/0.97  --smt_preprocessing                     true
% 3.38/0.97  --smt_ac_axioms                         fast
% 3.38/0.97  --preprocessed_out                      false
% 3.38/0.97  --preprocessed_stats                    false
% 3.38/0.97  
% 3.38/0.97  ------ Abstraction refinement Options
% 3.38/0.97  
% 3.38/0.97  --abstr_ref                             []
% 3.38/0.97  --abstr_ref_prep                        false
% 3.38/0.97  --abstr_ref_until_sat                   false
% 3.38/0.97  --abstr_ref_sig_restrict                funpre
% 3.38/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.38/0.97  --abstr_ref_under                       []
% 3.38/0.97  
% 3.38/0.97  ------ SAT Options
% 3.38/0.97  
% 3.38/0.97  --sat_mode                              false
% 3.38/0.97  --sat_fm_restart_options                ""
% 3.38/0.97  --sat_gr_def                            false
% 3.38/0.97  --sat_epr_types                         true
% 3.38/0.97  --sat_non_cyclic_types                  false
% 3.38/0.97  --sat_finite_models                     false
% 3.38/0.97  --sat_fm_lemmas                         false
% 3.38/0.97  --sat_fm_prep                           false
% 3.38/0.97  --sat_fm_uc_incr                        true
% 3.38/0.97  --sat_out_model                         small
% 3.38/0.97  --sat_out_clauses                       false
% 3.38/0.97  
% 3.38/0.97  ------ QBF Options
% 3.38/0.97  
% 3.38/0.97  --qbf_mode                              false
% 3.38/0.97  --qbf_elim_univ                         false
% 3.38/0.97  --qbf_dom_inst                          none
% 3.38/0.97  --qbf_dom_pre_inst                      false
% 3.38/0.97  --qbf_sk_in                             false
% 3.38/0.97  --qbf_pred_elim                         true
% 3.38/0.97  --qbf_split                             512
% 3.38/0.97  
% 3.38/0.97  ------ BMC1 Options
% 3.38/0.97  
% 3.38/0.97  --bmc1_incremental                      false
% 3.38/0.97  --bmc1_axioms                           reachable_all
% 3.38/0.97  --bmc1_min_bound                        0
% 3.38/0.97  --bmc1_max_bound                        -1
% 3.38/0.97  --bmc1_max_bound_default                -1
% 3.38/0.97  --bmc1_symbol_reachability              true
% 3.38/0.97  --bmc1_property_lemmas                  false
% 3.38/0.97  --bmc1_k_induction                      false
% 3.38/0.97  --bmc1_non_equiv_states                 false
% 3.38/0.97  --bmc1_deadlock                         false
% 3.38/0.97  --bmc1_ucm                              false
% 3.38/0.97  --bmc1_add_unsat_core                   none
% 3.38/0.97  --bmc1_unsat_core_children              false
% 3.38/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.38/0.97  --bmc1_out_stat                         full
% 3.38/0.97  --bmc1_ground_init                      false
% 3.38/0.97  --bmc1_pre_inst_next_state              false
% 3.38/0.97  --bmc1_pre_inst_state                   false
% 3.38/0.97  --bmc1_pre_inst_reach_state             false
% 3.38/0.97  --bmc1_out_unsat_core                   false
% 3.38/0.97  --bmc1_aig_witness_out                  false
% 3.38/0.97  --bmc1_verbose                          false
% 3.38/0.97  --bmc1_dump_clauses_tptp                false
% 3.38/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.38/0.97  --bmc1_dump_file                        -
% 3.38/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.38/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.38/0.97  --bmc1_ucm_extend_mode                  1
% 3.38/0.97  --bmc1_ucm_init_mode                    2
% 3.38/0.97  --bmc1_ucm_cone_mode                    none
% 3.38/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.38/0.97  --bmc1_ucm_relax_model                  4
% 3.38/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.38/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.38/0.97  --bmc1_ucm_layered_model                none
% 3.38/0.97  --bmc1_ucm_max_lemma_size               10
% 3.38/0.97  
% 3.38/0.97  ------ AIG Options
% 3.38/0.97  
% 3.38/0.97  --aig_mode                              false
% 3.38/0.97  
% 3.38/0.97  ------ Instantiation Options
% 3.38/0.97  
% 3.38/0.97  --instantiation_flag                    true
% 3.38/0.97  --inst_sos_flag                         false
% 3.38/0.97  --inst_sos_phase                        true
% 3.38/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.38/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.38/0.97  --inst_lit_sel_side                     none
% 3.38/0.97  --inst_solver_per_active                1400
% 3.38/0.97  --inst_solver_calls_frac                1.
% 3.38/0.97  --inst_passive_queue_type               priority_queues
% 3.38/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.38/0.97  --inst_passive_queues_freq              [25;2]
% 3.38/0.97  --inst_dismatching                      true
% 3.38/0.97  --inst_eager_unprocessed_to_passive     true
% 3.38/0.97  --inst_prop_sim_given                   true
% 3.38/0.97  --inst_prop_sim_new                     false
% 3.38/0.97  --inst_subs_new                         false
% 3.38/0.97  --inst_eq_res_simp                      false
% 3.38/0.97  --inst_subs_given                       false
% 3.38/0.97  --inst_orphan_elimination               true
% 3.38/0.97  --inst_learning_loop_flag               true
% 3.38/0.97  --inst_learning_start                   3000
% 3.38/0.97  --inst_learning_factor                  2
% 3.38/0.97  --inst_start_prop_sim_after_learn       3
% 3.38/0.97  --inst_sel_renew                        solver
% 3.38/0.97  --inst_lit_activity_flag                true
% 3.38/0.97  --inst_restr_to_given                   false
% 3.38/0.97  --inst_activity_threshold               500
% 3.38/0.97  --inst_out_proof                        true
% 3.38/0.97  
% 3.38/0.97  ------ Resolution Options
% 3.38/0.97  
% 3.38/0.97  --resolution_flag                       false
% 3.38/0.97  --res_lit_sel                           adaptive
% 3.38/0.97  --res_lit_sel_side                      none
% 3.38/0.97  --res_ordering                          kbo
% 3.38/0.97  --res_to_prop_solver                    active
% 3.38/0.97  --res_prop_simpl_new                    false
% 3.38/0.97  --res_prop_simpl_given                  true
% 3.38/0.97  --res_passive_queue_type                priority_queues
% 3.38/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.38/0.97  --res_passive_queues_freq               [15;5]
% 3.38/0.97  --res_forward_subs                      full
% 3.38/0.97  --res_backward_subs                     full
% 3.38/0.97  --res_forward_subs_resolution           true
% 3.38/0.97  --res_backward_subs_resolution          true
% 3.38/0.97  --res_orphan_elimination                true
% 3.38/0.97  --res_time_limit                        2.
% 3.38/0.97  --res_out_proof                         true
% 3.38/0.97  
% 3.38/0.97  ------ Superposition Options
% 3.38/0.97  
% 3.38/0.97  --superposition_flag                    true
% 3.38/0.97  --sup_passive_queue_type                priority_queues
% 3.38/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.38/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.38/0.97  --demod_completeness_check              fast
% 3.38/0.97  --demod_use_ground                      true
% 3.38/0.97  --sup_to_prop_solver                    passive
% 3.38/0.97  --sup_prop_simpl_new                    true
% 3.38/0.97  --sup_prop_simpl_given                  true
% 3.38/0.97  --sup_fun_splitting                     false
% 3.38/0.97  --sup_smt_interval                      50000
% 3.38/0.97  
% 3.38/0.97  ------ Superposition Simplification Setup
% 3.38/0.97  
% 3.38/0.97  --sup_indices_passive                   []
% 3.38/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.38/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.38/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.38/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.38/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.38/0.97  --sup_full_bw                           [BwDemod]
% 3.38/0.97  --sup_immed_triv                        [TrivRules]
% 3.38/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.38/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.38/0.97  --sup_immed_bw_main                     []
% 3.38/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.38/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.38/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.38/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.38/0.97  
% 3.38/0.97  ------ Combination Options
% 3.38/0.97  
% 3.38/0.97  --comb_res_mult                         3
% 3.38/0.97  --comb_sup_mult                         2
% 3.38/0.97  --comb_inst_mult                        10
% 3.38/0.97  
% 3.38/0.97  ------ Debug Options
% 3.38/0.97  
% 3.38/0.97  --dbg_backtrace                         false
% 3.38/0.97  --dbg_dump_prop_clauses                 false
% 3.38/0.97  --dbg_dump_prop_clauses_file            -
% 3.38/0.97  --dbg_out_stat                          false
% 3.38/0.97  
% 3.38/0.97  
% 3.38/0.97  
% 3.38/0.97  
% 3.38/0.97  ------ Proving...
% 3.38/0.97  
% 3.38/0.97  
% 3.38/0.97  % SZS status Theorem for theBenchmark.p
% 3.38/0.97  
% 3.38/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.38/0.97  
% 3.38/0.97  fof(f6,axiom,(
% 3.38/0.97    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 3.38/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.98  
% 3.38/0.98  fof(f17,plain,(
% 3.38/0.98    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.38/0.98    inference(ennf_transformation,[],[f6])).
% 3.38/0.98  
% 3.38/0.98  fof(f47,plain,(
% 3.38/0.98    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.38/0.98    inference(cnf_transformation,[],[f17])).
% 3.38/0.98  
% 3.38/0.98  fof(f14,conjecture,(
% 3.38/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 3.38/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.98  
% 3.38/0.98  fof(f15,negated_conjecture,(
% 3.38/0.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 3.38/0.98    inference(negated_conjecture,[],[f14])).
% 3.38/0.98  
% 3.38/0.98  fof(f27,plain,(
% 3.38/0.98    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)))),
% 3.38/0.98    inference(ennf_transformation,[],[f15])).
% 3.38/0.98  
% 3.38/0.98  fof(f28,plain,(
% 3.38/0.98    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3))),
% 3.38/0.98    inference(flattening,[],[f27])).
% 3.38/0.98  
% 3.38/0.98  fof(f35,plain,(
% 3.38/0.98    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) & k1_xboole_0 != sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK4,k1_tarski(sK1),sK2) & v1_funct_1(sK4))),
% 3.38/0.98    introduced(choice_axiom,[])).
% 3.38/0.98  
% 3.38/0.98  fof(f36,plain,(
% 3.38/0.98    ~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) & k1_xboole_0 != sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK4,k1_tarski(sK1),sK2) & v1_funct_1(sK4)),
% 3.38/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f28,f35])).
% 3.38/0.98  
% 3.38/0.98  fof(f62,plain,(
% 3.38/0.98    v1_funct_2(sK4,k1_tarski(sK1),sK2)),
% 3.38/0.98    inference(cnf_transformation,[],[f36])).
% 3.38/0.98  
% 3.38/0.98  fof(f2,axiom,(
% 3.38/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.38/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.98  
% 3.38/0.98  fof(f43,plain,(
% 3.38/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.38/0.98    inference(cnf_transformation,[],[f2])).
% 3.38/0.98  
% 3.38/0.98  fof(f3,axiom,(
% 3.38/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.38/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.98  
% 3.38/0.98  fof(f44,plain,(
% 3.38/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.38/0.98    inference(cnf_transformation,[],[f3])).
% 3.38/0.98  
% 3.38/0.98  fof(f4,axiom,(
% 3.38/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.38/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.98  
% 3.38/0.98  fof(f45,plain,(
% 3.38/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.38/0.98    inference(cnf_transformation,[],[f4])).
% 3.38/0.98  
% 3.38/0.98  fof(f66,plain,(
% 3.38/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.38/0.98    inference(definition_unfolding,[],[f44,f45])).
% 3.38/0.98  
% 3.38/0.98  fof(f67,plain,(
% 3.38/0.98    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.38/0.98    inference(definition_unfolding,[],[f43,f66])).
% 3.38/0.98  
% 3.38/0.98  fof(f78,plain,(
% 3.38/0.98    v1_funct_2(sK4,k2_enumset1(sK1,sK1,sK1,sK1),sK2)),
% 3.38/0.98    inference(definition_unfolding,[],[f62,f67])).
% 3.38/0.98  
% 3.38/0.98  fof(f13,axiom,(
% 3.38/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.38/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.98  
% 3.38/0.98  fof(f25,plain,(
% 3.38/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.38/0.98    inference(ennf_transformation,[],[f13])).
% 3.38/0.98  
% 3.38/0.98  fof(f26,plain,(
% 3.38/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.38/0.98    inference(flattening,[],[f25])).
% 3.38/0.98  
% 3.38/0.98  fof(f34,plain,(
% 3.38/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.38/0.98    inference(nnf_transformation,[],[f26])).
% 3.38/0.98  
% 3.38/0.98  fof(f55,plain,(
% 3.38/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.38/0.98    inference(cnf_transformation,[],[f34])).
% 3.38/0.98  
% 3.38/0.98  fof(f63,plain,(
% 3.38/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 3.38/0.98    inference(cnf_transformation,[],[f36])).
% 3.38/0.98  
% 3.38/0.98  fof(f77,plain,(
% 3.38/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))),
% 3.38/0.98    inference(definition_unfolding,[],[f63,f67])).
% 3.38/0.98  
% 3.38/0.98  fof(f64,plain,(
% 3.38/0.98    k1_xboole_0 != sK2),
% 3.38/0.98    inference(cnf_transformation,[],[f36])).
% 3.38/0.98  
% 3.38/0.98  fof(f9,axiom,(
% 3.38/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.38/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.98  
% 3.38/0.98  fof(f21,plain,(
% 3.38/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.38/0.98    inference(ennf_transformation,[],[f9])).
% 3.38/0.98  
% 3.38/0.98  fof(f50,plain,(
% 3.38/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.38/0.98    inference(cnf_transformation,[],[f21])).
% 3.38/0.98  
% 3.38/0.98  fof(f11,axiom,(
% 3.38/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.38/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.98  
% 3.38/0.98  fof(f23,plain,(
% 3.38/0.98    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.38/0.98    inference(ennf_transformation,[],[f11])).
% 3.38/0.98  
% 3.38/0.98  fof(f52,plain,(
% 3.38/0.98    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.38/0.98    inference(cnf_transformation,[],[f23])).
% 3.38/0.98  
% 3.38/0.98  fof(f10,axiom,(
% 3.38/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.38/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.98  
% 3.38/0.98  fof(f22,plain,(
% 3.38/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.38/0.98    inference(ennf_transformation,[],[f10])).
% 3.38/0.98  
% 3.38/0.98  fof(f51,plain,(
% 3.38/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.38/0.98    inference(cnf_transformation,[],[f22])).
% 3.38/0.98  
% 3.38/0.98  fof(f12,axiom,(
% 3.38/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 3.38/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.98  
% 3.38/0.98  fof(f24,plain,(
% 3.38/0.98    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.38/0.98    inference(ennf_transformation,[],[f12])).
% 3.38/0.98  
% 3.38/0.98  fof(f53,plain,(
% 3.38/0.98    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.38/0.98    inference(cnf_transformation,[],[f24])).
% 3.38/0.98  
% 3.38/0.98  fof(f8,axiom,(
% 3.38/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.38/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.98  
% 3.38/0.98  fof(f20,plain,(
% 3.38/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.38/0.98    inference(ennf_transformation,[],[f8])).
% 3.38/0.98  
% 3.38/0.98  fof(f49,plain,(
% 3.38/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.38/0.98    inference(cnf_transformation,[],[f20])).
% 3.38/0.98  
% 3.38/0.98  fof(f5,axiom,(
% 3.38/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 3.38/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.98  
% 3.38/0.98  fof(f16,plain,(
% 3.38/0.98    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 3.38/0.98    inference(ennf_transformation,[],[f5])).
% 3.38/0.98  
% 3.38/0.98  fof(f46,plain,(
% 3.38/0.98    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 3.38/0.98    inference(cnf_transformation,[],[f16])).
% 3.38/0.98  
% 3.38/0.98  fof(f74,plain,(
% 3.38/0.98    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 3.38/0.98    inference(definition_unfolding,[],[f46,f67])).
% 3.38/0.98  
% 3.38/0.98  fof(f1,axiom,(
% 3.38/0.98    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.38/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.98  
% 3.38/0.98  fof(f29,plain,(
% 3.38/0.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.38/0.98    inference(nnf_transformation,[],[f1])).
% 3.38/0.98  
% 3.38/0.98  fof(f30,plain,(
% 3.38/0.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.38/0.98    inference(flattening,[],[f29])).
% 3.38/0.98  
% 3.38/0.98  fof(f31,plain,(
% 3.38/0.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.38/0.98    inference(rectify,[],[f30])).
% 3.38/0.98  
% 3.38/0.98  fof(f32,plain,(
% 3.38/0.98    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.38/0.98    introduced(choice_axiom,[])).
% 3.38/0.98  
% 3.38/0.98  fof(f33,plain,(
% 3.38/0.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.38/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 3.38/0.98  
% 3.38/0.98  fof(f38,plain,(
% 3.38/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 3.38/0.98    inference(cnf_transformation,[],[f33])).
% 3.38/0.98  
% 3.38/0.98  fof(f72,plain,(
% 3.38/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 3.38/0.98    inference(definition_unfolding,[],[f38,f66])).
% 3.38/0.98  
% 3.38/0.98  fof(f81,plain,(
% 3.38/0.98    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 3.38/0.98    inference(equality_resolution,[],[f72])).
% 3.38/0.98  
% 3.38/0.98  fof(f82,plain,(
% 3.38/0.98    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 3.38/0.98    inference(equality_resolution,[],[f81])).
% 3.38/0.98  
% 3.38/0.98  fof(f7,axiom,(
% 3.38/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)))),
% 3.38/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.98  
% 3.38/0.98  fof(f18,plain,(
% 3.38/0.98    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.38/0.98    inference(ennf_transformation,[],[f7])).
% 3.38/0.98  
% 3.38/0.98  fof(f19,plain,(
% 3.38/0.98    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.38/0.98    inference(flattening,[],[f18])).
% 3.38/0.98  
% 3.38/0.98  fof(f48,plain,(
% 3.38/0.98    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.38/0.98    inference(cnf_transformation,[],[f19])).
% 3.38/0.98  
% 3.38/0.98  fof(f75,plain,(
% 3.38/0.98    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.38/0.98    inference(definition_unfolding,[],[f48,f67])).
% 3.38/0.98  
% 3.38/0.98  fof(f61,plain,(
% 3.38/0.98    v1_funct_1(sK4)),
% 3.38/0.98    inference(cnf_transformation,[],[f36])).
% 3.38/0.98  
% 3.38/0.98  fof(f65,plain,(
% 3.38/0.98    ~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))),
% 3.38/0.98    inference(cnf_transformation,[],[f36])).
% 3.38/0.98  
% 3.38/0.98  fof(f76,plain,(
% 3.38/0.98    ~r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))),
% 3.38/0.98    inference(definition_unfolding,[],[f65,f67,f67])).
% 3.38/0.98  
% 3.38/0.98  cnf(c_7,plain,
% 3.38/0.98      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 3.38/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_1380,plain,
% 3.38/0.98      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
% 3.38/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.38/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_24,negated_conjecture,
% 3.38/0.98      ( v1_funct_2(sK4,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
% 3.38/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_20,plain,
% 3.38/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.38/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.38/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.38/0.98      | k1_xboole_0 = X2 ),
% 3.38/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_23,negated_conjecture,
% 3.38/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
% 3.38/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_367,plain,
% 3.38/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.38/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.38/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 3.38/0.98      | sK4 != X0
% 3.38/0.98      | k1_xboole_0 = X2 ),
% 3.38/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_23]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_368,plain,
% 3.38/0.98      ( ~ v1_funct_2(sK4,X0,X1)
% 3.38/0.98      | k1_relset_1(X0,X1,sK4) = X0
% 3.38/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.38/0.98      | k1_xboole_0 = X1 ),
% 3.38/0.98      inference(unflattening,[status(thm)],[c_367]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_787,plain,
% 3.38/0.98      ( k2_enumset1(sK1,sK1,sK1,sK1) != X0
% 3.38/0.98      | k1_relset_1(X0,X1,sK4) = X0
% 3.38/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.38/0.98      | sK4 != sK4
% 3.38/0.98      | sK2 != X1
% 3.38/0.98      | k1_xboole_0 = X1 ),
% 3.38/0.98      inference(resolution_lifted,[status(thm)],[c_24,c_368]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_788,plain,
% 3.38/0.98      ( k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4) = k2_enumset1(sK1,sK1,sK1,sK1)
% 3.38/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
% 3.38/0.98      | k1_xboole_0 = sK2 ),
% 3.38/0.98      inference(unflattening,[status(thm)],[c_787]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_22,negated_conjecture,
% 3.38/0.98      ( k1_xboole_0 != sK2 ),
% 3.38/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_789,plain,
% 3.38/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
% 3.38/0.98      | k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4) = k2_enumset1(sK1,sK1,sK1,sK1) ),
% 3.38/0.98      inference(global_propositional_subsumption,
% 3.38/0.98                [status(thm)],
% 3.38/0.98                [c_788,c_22]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_790,plain,
% 3.38/0.98      ( k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4) = k2_enumset1(sK1,sK1,sK1,sK1)
% 3.38/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
% 3.38/0.98      inference(renaming,[status(thm)],[c_789]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_850,plain,
% 3.38/0.98      ( k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4) = k2_enumset1(sK1,sK1,sK1,sK1) ),
% 3.38/0.98      inference(equality_resolution_simp,[status(thm)],[c_790]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_10,plain,
% 3.38/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.38/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.38/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_439,plain,
% 3.38/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.38/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.38/0.98      | sK4 != X2 ),
% 3.38/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_23]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_440,plain,
% 3.38/0.98      ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
% 3.38/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.38/0.98      inference(unflattening,[status(thm)],[c_439]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_1519,plain,
% 3.38/0.98      ( k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4) = k1_relat_1(sK4) ),
% 3.38/0.98      inference(equality_resolution,[status(thm)],[c_440]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_2034,plain,
% 3.38/0.98      ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK4) ),
% 3.38/0.98      inference(light_normalisation,[status(thm)],[c_850,c_1519]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_12,plain,
% 3.38/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.38/0.98      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.38/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_421,plain,
% 3.38/0.98      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.38/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.38/0.98      | sK4 != X2 ),
% 3.38/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_23]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_422,plain,
% 3.38/0.98      ( k7_relset_1(X0,X1,sK4,X2) = k9_relat_1(sK4,X2)
% 3.38/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.38/0.98      inference(unflattening,[status(thm)],[c_421]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_1522,plain,
% 3.38/0.98      ( k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
% 3.38/0.98      inference(equality_resolution,[status(thm)],[c_422]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_2036,plain,
% 3.38/0.98      ( k7_relset_1(k1_relat_1(sK4),sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
% 3.38/0.98      inference(demodulation,[status(thm)],[c_2034,c_1522]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_11,plain,
% 3.38/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.38/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.38/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_430,plain,
% 3.38/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.38/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.38/0.98      | sK4 != X2 ),
% 3.38/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_23]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_431,plain,
% 3.38/0.98      ( k2_relset_1(X0,X1,sK4) = k2_relat_1(sK4)
% 3.38/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.38/0.98      inference(unflattening,[status(thm)],[c_430]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_1504,plain,
% 3.38/0.98      ( k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4) = k2_relat_1(sK4) ),
% 3.38/0.98      inference(equality_resolution,[status(thm)],[c_431]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_2038,plain,
% 3.38/0.98      ( k2_relset_1(k1_relat_1(sK4),sK2,sK4) = k2_relat_1(sK4) ),
% 3.38/0.98      inference(demodulation,[status(thm)],[c_2034,c_1504]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_14,plain,
% 3.38/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.38/0.98      | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
% 3.38/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_403,plain,
% 3.38/0.98      ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
% 3.38/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.38/0.98      | sK4 != X2 ),
% 3.38/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_23]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_404,plain,
% 3.38/0.98      ( k7_relset_1(X0,X1,sK4,X0) = k2_relset_1(X0,X1,sK4)
% 3.38/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.38/0.98      inference(unflattening,[status(thm)],[c_403]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_1558,plain,
% 3.38/0.98      ( k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,k2_enumset1(sK1,sK1,sK1,sK1)) = k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4) ),
% 3.38/0.98      inference(equality_resolution,[status(thm)],[c_404]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_2967,plain,
% 3.38/0.98      ( k7_relset_1(k1_relat_1(sK4),sK2,sK4,k1_relat_1(sK4)) = k2_relset_1(k1_relat_1(sK4),sK2,sK4) ),
% 3.38/0.98      inference(light_normalisation,[status(thm)],[c_1558,c_2034]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_3404,plain,
% 3.38/0.98      ( k7_relset_1(k1_relat_1(sK4),sK2,sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
% 3.38/0.98      inference(demodulation,[status(thm)],[c_2038,c_2967]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_4169,plain,
% 3.38/0.98      ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
% 3.38/0.98      inference(superposition,[status(thm)],[c_2036,c_3404]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_9,plain,
% 3.38/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.38/0.98      | v1_relat_1(X0) ),
% 3.38/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_448,plain,
% 3.38/0.98      ( v1_relat_1(X0)
% 3.38/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 3.38/0.98      | sK4 != X0 ),
% 3.38/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_23]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_449,plain,
% 3.38/0.98      ( v1_relat_1(sK4)
% 3.38/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.38/0.98      inference(unflattening,[status(thm)],[c_448]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_1377,plain,
% 3.38/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.38/0.98      | v1_relat_1(sK4) = iProver_top ),
% 3.38/0.98      inference(predicate_to_equality,[status(thm)],[c_449]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_1144,plain,( X0 = X0 ),theory(equality) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_1505,plain,
% 3.38/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
% 3.38/0.98      inference(instantiation,[status(thm)],[c_1144]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_1511,plain,
% 3.38/0.98      ( v1_relat_1(sK4)
% 3.38/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
% 3.38/0.98      inference(instantiation,[status(thm)],[c_449]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_1512,plain,
% 3.38/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
% 3.38/0.98      | v1_relat_1(sK4) = iProver_top ),
% 3.38/0.98      inference(predicate_to_equality,[status(thm)],[c_1511]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_2179,plain,
% 3.38/0.98      ( v1_relat_1(sK4) = iProver_top ),
% 3.38/0.98      inference(global_propositional_subsumption,
% 3.38/0.98                [status(thm)],
% 3.38/0.98                [c_1377,c_1505,c_1512]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_6,plain,
% 3.38/0.98      ( ~ v1_relat_1(X0)
% 3.38/0.98      | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
% 3.38/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_1381,plain,
% 3.38/0.98      ( k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1)
% 3.38/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.38/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_2184,plain,
% 3.38/0.98      ( k9_relat_1(sK4,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK4,X0) ),
% 3.38/0.98      inference(superposition,[status(thm)],[c_2179,c_1381]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_3554,plain,
% 3.38/0.98      ( k9_relat_1(sK4,k1_relat_1(sK4)) = k11_relat_1(sK4,sK1) ),
% 3.38/0.98      inference(superposition,[status(thm)],[c_2034,c_2184]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_4324,plain,
% 3.38/0.98      ( k11_relat_1(sK4,sK1) = k2_relat_1(sK4) ),
% 3.38/0.98      inference(demodulation,[status(thm)],[c_4169,c_3554]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_4,plain,
% 3.38/0.98      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
% 3.38/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_1383,plain,
% 3.38/0.98      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
% 3.38/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_2083,plain,
% 3.38/0.98      ( r2_hidden(sK1,k1_relat_1(sK4)) = iProver_top ),
% 3.38/0.98      inference(superposition,[status(thm)],[c_2034,c_1383]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_8,plain,
% 3.38/0.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.38/0.98      | ~ v1_funct_1(X1)
% 3.38/0.98      | ~ v1_relat_1(X1)
% 3.38/0.98      | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
% 3.38/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_25,negated_conjecture,
% 3.38/0.98      ( v1_funct_1(sK4) ),
% 3.38/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_304,plain,
% 3.38/0.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.38/0.98      | ~ v1_relat_1(X1)
% 3.38/0.98      | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
% 3.38/0.98      | sK4 != X1 ),
% 3.38/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_25]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_305,plain,
% 3.38/0.98      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 3.38/0.98      | ~ v1_relat_1(sK4)
% 3.38/0.98      | k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0) ),
% 3.38/0.98      inference(unflattening,[status(thm)],[c_304]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_1378,plain,
% 3.38/0.98      ( k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
% 3.38/0.98      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 3.38/0.98      | v1_relat_1(sK4) != iProver_top ),
% 3.38/0.98      inference(predicate_to_equality,[status(thm)],[c_305]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_306,plain,
% 3.38/0.98      ( k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
% 3.38/0.98      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 3.38/0.98      | v1_relat_1(sK4) != iProver_top ),
% 3.38/0.98      inference(predicate_to_equality,[status(thm)],[c_305]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_2320,plain,
% 3.38/0.98      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 3.38/0.98      | k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0) ),
% 3.38/0.98      inference(global_propositional_subsumption,
% 3.38/0.98                [status(thm)],
% 3.38/0.98                [c_1378,c_306,c_1505,c_1512]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_2321,plain,
% 3.38/0.98      ( k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
% 3.38/0.98      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 3.38/0.98      inference(renaming,[status(thm)],[c_2320]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_3488,plain,
% 3.38/0.98      ( k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k11_relat_1(sK4,sK1) ),
% 3.38/0.98      inference(superposition,[status(thm)],[c_2083,c_2321]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_21,negated_conjecture,
% 3.38/0.98      ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) ),
% 3.38/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_1379,plain,
% 3.38/0.98      ( r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
% 3.38/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_1922,plain,
% 3.38/0.98      ( r1_tarski(k9_relat_1(sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
% 3.38/0.98      inference(demodulation,[status(thm)],[c_1522,c_1379]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_3811,plain,
% 3.38/0.98      ( r1_tarski(k9_relat_1(sK4,sK3),k11_relat_1(sK4,sK1)) != iProver_top ),
% 3.38/0.98      inference(demodulation,[status(thm)],[c_3488,c_1922]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_17508,plain,
% 3.38/0.98      ( r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4)) != iProver_top ),
% 3.38/0.98      inference(demodulation,[status(thm)],[c_4324,c_3811]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_18092,plain,
% 3.38/0.98      ( v1_relat_1(sK4) != iProver_top ),
% 3.38/0.98      inference(superposition,[status(thm)],[c_1380,c_17508]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(contradiction,plain,
% 3.38/0.98      ( $false ),
% 3.38/0.98      inference(minisat,[status(thm)],[c_18092,c_1512,c_1505]) ).
% 3.38/0.98  
% 3.38/0.98  
% 3.38/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.38/0.98  
% 3.38/0.98  ------                               Statistics
% 3.38/0.98  
% 3.38/0.98  ------ General
% 3.38/0.98  
% 3.38/0.98  abstr_ref_over_cycles:                  0
% 3.38/0.98  abstr_ref_under_cycles:                 0
% 3.38/0.98  gc_basic_clause_elim:                   0
% 3.38/0.98  forced_gc_time:                         0
% 3.38/0.98  parsing_time:                           0.011
% 3.38/0.98  unif_index_cands_time:                  0.
% 3.38/0.98  unif_index_add_time:                    0.
% 3.38/0.98  orderings_time:                         0.
% 3.38/0.98  out_proof_time:                         0.01
% 3.38/0.98  total_time:                             0.479
% 3.38/0.98  num_of_symbols:                         55
% 3.38/0.98  num_of_terms:                           15436
% 3.38/0.98  
% 3.38/0.98  ------ Preprocessing
% 3.38/0.98  
% 3.38/0.98  num_of_splits:                          0
% 3.38/0.98  num_of_split_atoms:                     0
% 3.38/0.98  num_of_reused_defs:                     0
% 3.38/0.98  num_eq_ax_congr_red:                    36
% 3.38/0.98  num_of_sem_filtered_clauses:            1
% 3.38/0.98  num_of_subtypes:                        0
% 3.38/0.98  monotx_restored_types:                  0
% 3.38/0.98  sat_num_of_epr_types:                   0
% 3.38/0.98  sat_num_of_non_cyclic_types:            0
% 3.38/0.98  sat_guarded_non_collapsed_types:        0
% 3.38/0.98  num_pure_diseq_elim:                    0
% 3.38/0.98  simp_replaced_by:                       0
% 3.38/0.98  res_preprocessed:                       121
% 3.38/0.98  prep_upred:                             0
% 3.38/0.98  prep_unflattend:                        58
% 3.38/0.98  smt_new_axioms:                         0
% 3.38/0.98  pred_elim_cands:                        3
% 3.38/0.98  pred_elim:                              3
% 3.38/0.98  pred_elim_cl:                           6
% 3.38/0.98  pred_elim_cycles:                       11
% 3.38/0.98  merged_defs:                            0
% 3.38/0.98  merged_defs_ncl:                        0
% 3.38/0.98  bin_hyper_res:                          0
% 3.38/0.98  prep_cycles:                            4
% 3.38/0.98  pred_elim_time:                         0.014
% 3.38/0.98  splitting_time:                         0.
% 3.38/0.98  sem_filter_time:                        0.
% 3.38/0.98  monotx_time:                            0.
% 3.38/0.98  subtype_inf_time:                       0.
% 3.38/0.98  
% 3.38/0.98  ------ Problem properties
% 3.38/0.98  
% 3.38/0.98  clauses:                                20
% 3.38/0.98  conjectures:                            2
% 3.38/0.98  epr:                                    1
% 3.38/0.98  horn:                                   17
% 3.38/0.98  ground:                                 5
% 3.38/0.98  unary:                                  5
% 3.38/0.98  binary:                                 8
% 3.38/0.98  lits:                                   44
% 3.38/0.98  lits_eq:                                31
% 3.38/0.98  fd_pure:                                0
% 3.38/0.98  fd_pseudo:                              0
% 3.38/0.98  fd_cond:                                0
% 3.38/0.98  fd_pseudo_cond:                         3
% 3.38/0.98  ac_symbols:                             0
% 3.38/0.98  
% 3.38/0.98  ------ Propositional Solver
% 3.38/0.98  
% 3.38/0.98  prop_solver_calls:                      29
% 3.38/0.98  prop_fast_solver_calls:                 1065
% 3.38/0.98  smt_solver_calls:                       0
% 3.38/0.98  smt_fast_solver_calls:                  0
% 3.38/0.98  prop_num_of_clauses:                    4978
% 3.38/0.98  prop_preprocess_simplified:             12788
% 3.38/0.98  prop_fo_subsumed:                       10
% 3.38/0.98  prop_solver_time:                       0.
% 3.38/0.98  smt_solver_time:                        0.
% 3.38/0.98  smt_fast_solver_time:                   0.
% 3.38/0.98  prop_fast_solver_time:                  0.
% 3.38/0.98  prop_unsat_core_time:                   0.
% 3.38/0.98  
% 3.38/0.98  ------ QBF
% 3.38/0.98  
% 3.38/0.98  qbf_q_res:                              0
% 3.38/0.98  qbf_num_tautologies:                    0
% 3.38/0.98  qbf_prep_cycles:                        0
% 3.38/0.98  
% 3.38/0.98  ------ BMC1
% 3.38/0.98  
% 3.38/0.98  bmc1_current_bound:                     -1
% 3.38/0.98  bmc1_last_solved_bound:                 -1
% 3.38/0.98  bmc1_unsat_core_size:                   -1
% 3.38/0.98  bmc1_unsat_core_parents_size:           -1
% 3.38/0.98  bmc1_merge_next_fun:                    0
% 3.38/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.38/0.98  
% 3.38/0.98  ------ Instantiation
% 3.38/0.98  
% 3.38/0.98  inst_num_of_clauses:                    1456
% 3.38/0.98  inst_num_in_passive:                    902
% 3.38/0.98  inst_num_in_active:                     413
% 3.38/0.98  inst_num_in_unprocessed:                141
% 3.38/0.98  inst_num_of_loops:                      520
% 3.38/0.98  inst_num_of_learning_restarts:          0
% 3.38/0.98  inst_num_moves_active_passive:          105
% 3.38/0.98  inst_lit_activity:                      0
% 3.38/0.98  inst_lit_activity_moves:                0
% 3.38/0.98  inst_num_tautologies:                   0
% 3.38/0.98  inst_num_prop_implied:                  0
% 3.38/0.98  inst_num_existing_simplified:           0
% 3.38/0.98  inst_num_eq_res_simplified:             0
% 3.38/0.98  inst_num_child_elim:                    0
% 3.38/0.98  inst_num_of_dismatching_blockings:      1665
% 3.38/0.98  inst_num_of_non_proper_insts:           1818
% 3.38/0.98  inst_num_of_duplicates:                 0
% 3.38/0.98  inst_inst_num_from_inst_to_res:         0
% 3.38/0.98  inst_dismatching_checking_time:         0.
% 3.38/0.98  
% 3.38/0.98  ------ Resolution
% 3.38/0.98  
% 3.38/0.98  res_num_of_clauses:                     0
% 3.38/0.98  res_num_in_passive:                     0
% 3.38/0.98  res_num_in_active:                      0
% 3.38/0.98  res_num_of_loops:                       125
% 3.38/0.98  res_forward_subset_subsumed:            247
% 3.38/0.98  res_backward_subset_subsumed:           2
% 3.38/0.98  res_forward_subsumed:                   0
% 3.38/0.98  res_backward_subsumed:                  0
% 3.38/0.98  res_forward_subsumption_resolution:     0
% 3.38/0.98  res_backward_subsumption_resolution:    0
% 3.38/0.98  res_clause_to_clause_subsumption:       5569
% 3.38/0.98  res_orphan_elimination:                 0
% 3.38/0.98  res_tautology_del:                      54
% 3.38/0.98  res_num_eq_res_simplified:              1
% 3.38/0.98  res_num_sel_changes:                    0
% 3.38/0.98  res_moves_from_active_to_pass:          0
% 3.38/0.98  
% 3.38/0.98  ------ Superposition
% 3.38/0.98  
% 3.38/0.98  sup_time_total:                         0.
% 3.38/0.98  sup_time_generating:                    0.
% 3.38/0.98  sup_time_sim_full:                      0.
% 3.38/0.98  sup_time_sim_immed:                     0.
% 3.38/0.98  
% 3.38/0.98  sup_num_of_clauses:                     421
% 3.38/0.98  sup_num_in_active:                      73
% 3.38/0.98  sup_num_in_passive:                     348
% 3.38/0.98  sup_num_of_loops:                       102
% 3.38/0.98  sup_fw_superposition:                   526
% 3.38/0.98  sup_bw_superposition:                   538
% 3.38/0.98  sup_immediate_simplified:               320
% 3.38/0.98  sup_given_eliminated:                   0
% 3.38/0.98  comparisons_done:                       0
% 3.38/0.98  comparisons_avoided:                    188
% 3.38/0.98  
% 3.38/0.98  ------ Simplifications
% 3.38/0.98  
% 3.38/0.98  
% 3.38/0.98  sim_fw_subset_subsumed:                 151
% 3.38/0.98  sim_bw_subset_subsumed:                 0
% 3.38/0.98  sim_fw_subsumed:                        101
% 3.38/0.98  sim_bw_subsumed:                        10
% 3.38/0.98  sim_fw_subsumption_res:                 5
% 3.38/0.98  sim_bw_subsumption_res:                 0
% 3.38/0.98  sim_tautology_del:                      0
% 3.38/0.98  sim_eq_tautology_del:                   20
% 3.38/0.98  sim_eq_res_simp:                        0
% 3.38/0.98  sim_fw_demodulated:                     12
% 3.38/0.98  sim_bw_demodulated:                     30
% 3.38/0.98  sim_light_normalised:                   54
% 3.38/0.98  sim_joinable_taut:                      0
% 3.38/0.98  sim_joinable_simp:                      0
% 3.38/0.98  sim_ac_normalised:                      0
% 3.38/0.98  sim_smt_subsumption:                    0
% 3.38/0.98  
%------------------------------------------------------------------------------
