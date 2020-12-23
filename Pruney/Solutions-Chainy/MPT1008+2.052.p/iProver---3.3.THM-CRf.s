%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:15 EST 2020

% Result     : Theorem 0.36s
% Output     : CNFRefutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  164 (1791 expanded)
%              Number of clauses        :   82 ( 370 expanded)
%              Number of leaves         :   23 ( 476 expanded)
%              Depth                    :   27
%              Number of atoms          :  443 (4489 expanded)
%              Number of equality atoms :  246 (2490 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f36,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f44,plain,
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

fof(f45,plain,
    ( k1_tarski(k1_funct_1(sK4,sK2)) != k2_relset_1(k1_tarski(sK2),sK3,sK4)
    & k1_xboole_0 != sK3
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
    & v1_funct_2(sK4,k1_tarski(sK2),sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f36,f44])).

fof(f77,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) ),
    inference(cnf_transformation,[],[f45])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f80,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f81,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f48,f80])).

fof(f99,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) ),
    inference(definition_unfolding,[],[f77,f81])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f37])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k2_enumset1(X1,X1,X1,X2) = X0
      | k2_enumset1(X2,X2,X2,X2) = X0
      | k2_enumset1(X1,X1,X1,X1) = X0
      | o_0_0_xboole_0 = X0
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f51,f80,f81,f81,f46,f80])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f66,f81,f81])).

fof(f75,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f79,plain,(
    k1_tarski(k1_funct_1(sK4,sK2)) != k2_relset_1(k1_tarski(sK2),sK3,sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f97,plain,(
    k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) ),
    inference(definition_unfolding,[],[f79,f81,f81])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f60,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f91,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | o_0_0_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f60,f46,f46])).

fof(f16,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f42])).

fof(f71,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f95,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f71,f46])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f33])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | o_0_0_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(definition_unfolding,[],[f74,f46])).

fof(f76,plain,(
    v1_funct_2(sK4,k1_tarski(sK2),sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f100,plain,(
    v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
    inference(definition_unfolding,[],[f76,f81])).

fof(f78,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f45])).

fof(f98,plain,(
    o_0_0_xboole_0 != sK3 ),
    inference(definition_unfolding,[],[f78,f46])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f88,plain,(
    o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f59,f46,f46])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f82,plain,(
    ! [X0] : r1_tarski(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f47,f46])).

fof(f10,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = X1
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK0(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK0(X0,X1)) = X0
        & v1_funct_1(sK0(X0,X1))
        & v1_relat_1(sK0(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK0(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK0(X0,X1)) = X0
      & v1_funct_1(sK0(X0,X1))
      & v1_relat_1(sK0(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f40])).

fof(f64,plain,(
    ! [X0,X1] : k1_relat_1(sK0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f41])).

fof(f62,plain,(
    ! [X0,X1] : v1_relat_1(sK0(X0,X1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f63,plain,(
    ! [X0,X1] : v1_funct_1(sK0(X0,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_7,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_321,plain,
    ( v4_relat_1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_27])).

cnf(c_322,plain,
    ( v4_relat_1(sK4,X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_321])).

cnf(c_388,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | X2 != X1
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_322])).

cnf(c_389,plain,
    ( r1_tarski(k1_relat_1(sK4),X0)
    | ~ v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_388])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_333,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_27])).

cnf(c_334,plain,
    ( v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_333])).

cnf(c_393,plain,
    ( r1_tarski(k1_relat_1(sK4),X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_389,c_334])).

cnf(c_1359,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | r1_tarski(k1_relat_1(sK4),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_393])).

cnf(c_1637,plain,
    ( r1_tarski(k1_relat_1(sK4),k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1359])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
    | k2_enumset1(X1,X1,X1,X2) = X0
    | k2_enumset1(X2,X2,X2,X2) = X0
    | k2_enumset1(X1,X1,X1,X1) = X0
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1373,plain,
    ( k2_enumset1(X0,X0,X0,X1) = X2
    | k2_enumset1(X1,X1,X1,X1) = X2
    | k2_enumset1(X0,X0,X0,X0) = X2
    | o_0_0_xboole_0 = X2
    | r1_tarski(X2,k2_enumset1(X0,X0,X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2766,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_relat_1(sK4)
    | k1_relat_1(sK4) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_1637,c_1373])).

cnf(c_16,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1367,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2816,plain,
    ( k2_enumset1(k1_funct_1(X0,sK2),k1_funct_1(X0,sK2),k1_funct_1(X0,sK2),k1_funct_1(X0,sK2)) = k2_relat_1(X0)
    | k1_relat_1(X0) != k1_relat_1(sK4)
    | k1_relat_1(sK4) = o_0_0_xboole_0
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2766,c_1367])).

cnf(c_3539,plain,
    ( k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) = k2_relat_1(sK4)
    | k1_relat_1(sK4) = o_0_0_xboole_0
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2816])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_30,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_989,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1518,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) ),
    inference(instantiation,[status(thm)],[c_989])).

cnf(c_1521,plain,
    ( v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) ),
    inference(instantiation,[status(thm)],[c_334])).

cnf(c_1522,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1521])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_312,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_27])).

cnf(c_313,plain,
    ( k2_relset_1(X0,X1,sK4) = k2_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_312])).

cnf(c_1539,plain,
    ( k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) = k2_relat_1(sK4) ),
    inference(equality_resolution,[status(thm)],[c_313])).

cnf(c_25,negated_conjecture,
    ( k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1572,plain,
    ( k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k2_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_1539,c_25])).

cnf(c_3550,plain,
    ( k1_relat_1(sK4) = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3539,c_30,c_1518,c_1522,c_1572])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != o_0_0_xboole_0
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1371,plain,
    ( k1_relat_1(X0) != o_0_0_xboole_0
    | o_0_0_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3567,plain,
    ( sK4 = o_0_0_xboole_0
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3550,c_1371])).

cnf(c_1926,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_989])).

cnf(c_2391,plain,
    ( ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) != o_0_0_xboole_0
    | o_0_0_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_990,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1927,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_990])).

cnf(c_2487,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1927])).

cnf(c_2488,plain,
    ( sK4 != sK4
    | sK4 = o_0_0_xboole_0
    | o_0_0_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_2487])).

cnf(c_3733,plain,
    ( sK4 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3567,c_30,c_1518,c_1521,c_1522,c_1572,c_1926,c_2391,c_2488,c_3539])).

cnf(c_23,plain,
    ( r2_hidden(sK1(X0),X0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1363,plain,
    ( o_0_0_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | o_0_0_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_291,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | k2_enumset1(sK2,sK2,sK2,sK2) != X1
    | sK3 != X2
    | sK4 != X0
    | o_0_0_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_28])).

cnf(c_292,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))
    | ~ r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2))
    | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4))
    | ~ v1_funct_1(sK4)
    | o_0_0_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_291])).

cnf(c_26,negated_conjecture,
    ( o_0_0_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_296,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2))
    | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_292,c_29,c_27,c_26])).

cnf(c_1361,plain,
    ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_296])).

cnf(c_1592,plain,
    ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1361,c_1539])).

cnf(c_2062,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = o_0_0_xboole_0
    | r2_hidden(k1_funct_1(sK4,sK1(k2_enumset1(sK2,sK2,sK2,sK2))),k2_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1363,c_1592])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1366,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2269,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = o_0_0_xboole_0
    | r1_tarski(k2_relat_1(sK4),k1_funct_1(sK4,sK1(k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2062,c_1366])).

cnf(c_3738,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = o_0_0_xboole_0
    | r1_tarski(k2_relat_1(o_0_0_xboole_0),k1_funct_1(o_0_0_xboole_0,sK1(k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3733,c_2269])).

cnf(c_8,plain,
    ( k2_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_3769,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = o_0_0_xboole_0
    | r1_tarski(o_0_0_xboole_0,k1_funct_1(o_0_0_xboole_0,sK1(k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3738,c_8])).

cnf(c_0,plain,
    ( r1_tarski(o_0_0_xboole_0,X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1378,plain,
    ( r1_tarski(o_0_0_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4078,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = o_0_0_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3769,c_1378])).

cnf(c_13,plain,
    ( k1_relat_1(sK0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2752,plain,
    ( k2_enumset1(X0,X0,X0,X0) != X1
    | k2_enumset1(k1_funct_1(sK0(X1,X2),X0),k1_funct_1(sK0(X1,X2),X0),k1_funct_1(sK0(X1,X2),X0),k1_funct_1(sK0(X1,X2),X0)) = k2_relat_1(sK0(X1,X2))
    | v1_funct_1(sK0(X1,X2)) != iProver_top
    | v1_relat_1(sK0(X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_1367])).

cnf(c_15,plain,
    ( v1_relat_1(sK0(X0,X1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1368,plain,
    ( v1_relat_1(sK0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_14,plain,
    ( v1_funct_1(sK0(X0,X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1369,plain,
    ( v1_funct_1(sK0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2805,plain,
    ( k2_enumset1(X0,X0,X0,X0) != X1
    | k2_enumset1(k1_funct_1(sK0(X1,X2),X0),k1_funct_1(sK0(X1,X2),X0),k1_funct_1(sK0(X1,X2),X0),k1_funct_1(sK0(X1,X2),X0)) = k2_relat_1(sK0(X1,X2)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2752,c_1368,c_1369])).

cnf(c_2807,plain,
    ( k2_enumset1(k1_funct_1(sK0(k2_enumset1(X0,X0,X0,X0),X1),X0),k1_funct_1(sK0(k2_enumset1(X0,X0,X0,X0),X1),X0),k1_funct_1(sK0(k2_enumset1(X0,X0,X0,X0),X1),X0),k1_funct_1(sK0(k2_enumset1(X0,X0,X0,X0),X1),X0)) = k2_relat_1(sK0(k2_enumset1(X0,X0,X0,X0),X1)) ),
    inference(equality_resolution,[status(thm)],[c_2805])).

cnf(c_4098,plain,
    ( k2_enumset1(k1_funct_1(sK0(o_0_0_xboole_0,X0),sK2),k1_funct_1(sK0(o_0_0_xboole_0,X0),sK2),k1_funct_1(sK0(o_0_0_xboole_0,X0),sK2),k1_funct_1(sK0(o_0_0_xboole_0,X0),sK2)) = k2_relat_1(sK0(k2_enumset1(sK2,sK2,sK2,sK2),X0)) ),
    inference(superposition,[status(thm)],[c_4078,c_2807])).

cnf(c_4123,plain,
    ( k2_enumset1(k1_funct_1(sK0(o_0_0_xboole_0,X0),sK2),k1_funct_1(sK0(o_0_0_xboole_0,X0),sK2),k1_funct_1(sK0(o_0_0_xboole_0,X0),sK2),k1_funct_1(sK0(o_0_0_xboole_0,X0),sK2)) = k2_relat_1(sK0(o_0_0_xboole_0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_4098,c_4078])).

cnf(c_2197,plain,
    ( sK0(X0,X1) = o_0_0_xboole_0
    | o_0_0_xboole_0 != X0
    | v1_relat_1(sK0(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_1371])).

cnf(c_58,plain,
    ( v1_relat_1(sK0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2259,plain,
    ( o_0_0_xboole_0 != X0
    | sK0(X0,X1) = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2197,c_58])).

cnf(c_2260,plain,
    ( sK0(X0,X1) = o_0_0_xboole_0
    | o_0_0_xboole_0 != X0 ),
    inference(renaming,[status(thm)],[c_2259])).

cnf(c_2264,plain,
    ( sK0(o_0_0_xboole_0,X0) = o_0_0_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_2260])).

cnf(c_4125,plain,
    ( k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK2),k1_funct_1(o_0_0_xboole_0,sK2),k1_funct_1(o_0_0_xboole_0,sK2),k1_funct_1(o_0_0_xboole_0,sK2)) = o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4123,c_8,c_2264])).

cnf(c_3742,plain,
    ( k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK2),k1_funct_1(o_0_0_xboole_0,sK2),k1_funct_1(o_0_0_xboole_0,sK2),k1_funct_1(o_0_0_xboole_0,sK2)) != k2_relat_1(o_0_0_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3733,c_1572])).

cnf(c_3755,plain,
    ( k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK2),k1_funct_1(o_0_0_xboole_0,sK2),k1_funct_1(o_0_0_xboole_0,sK2),k1_funct_1(o_0_0_xboole_0,sK2)) != o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3742,c_8])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4125,c_3755])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:20:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 0.36/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.36/1.03  
% 0.36/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.36/1.03  
% 0.36/1.03  ------  iProver source info
% 0.36/1.03  
% 0.36/1.03  git: date: 2020-06-30 10:37:57 +0100
% 0.36/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.36/1.03  git: non_committed_changes: false
% 0.36/1.03  git: last_make_outside_of_git: false
% 0.36/1.03  
% 0.36/1.03  ------ 
% 0.36/1.03  
% 0.36/1.03  ------ Input Options
% 0.36/1.03  
% 0.36/1.03  --out_options                           all
% 0.36/1.03  --tptp_safe_out                         true
% 0.36/1.03  --problem_path                          ""
% 0.36/1.03  --include_path                          ""
% 0.36/1.03  --clausifier                            res/vclausify_rel
% 0.36/1.03  --clausifier_options                    --mode clausify
% 0.36/1.03  --stdin                                 false
% 0.36/1.03  --stats_out                             all
% 0.36/1.03  
% 0.36/1.03  ------ General Options
% 0.36/1.03  
% 0.36/1.03  --fof                                   false
% 0.36/1.03  --time_out_real                         305.
% 0.36/1.03  --time_out_virtual                      -1.
% 0.36/1.03  --symbol_type_check                     false
% 0.36/1.03  --clausify_out                          false
% 0.36/1.03  --sig_cnt_out                           false
% 0.36/1.03  --trig_cnt_out                          false
% 0.36/1.03  --trig_cnt_out_tolerance                1.
% 0.36/1.03  --trig_cnt_out_sk_spl                   false
% 0.36/1.03  --abstr_cl_out                          false
% 0.36/1.03  
% 0.36/1.03  ------ Global Options
% 0.36/1.03  
% 0.36/1.03  --schedule                              default
% 0.36/1.03  --add_important_lit                     false
% 0.36/1.03  --prop_solver_per_cl                    1000
% 0.36/1.03  --min_unsat_core                        false
% 0.36/1.03  --soft_assumptions                      false
% 0.36/1.03  --soft_lemma_size                       3
% 0.36/1.03  --prop_impl_unit_size                   0
% 0.36/1.03  --prop_impl_unit                        []
% 0.36/1.03  --share_sel_clauses                     true
% 0.36/1.03  --reset_solvers                         false
% 0.36/1.03  --bc_imp_inh                            [conj_cone]
% 0.36/1.03  --conj_cone_tolerance                   3.
% 0.36/1.03  --extra_neg_conj                        none
% 0.36/1.03  --large_theory_mode                     true
% 0.36/1.03  --prolific_symb_bound                   200
% 0.36/1.03  --lt_threshold                          2000
% 0.36/1.03  --clause_weak_htbl                      true
% 0.36/1.03  --gc_record_bc_elim                     false
% 0.36/1.03  
% 0.36/1.03  ------ Preprocessing Options
% 0.36/1.03  
% 0.36/1.03  --preprocessing_flag                    true
% 0.36/1.03  --time_out_prep_mult                    0.1
% 0.36/1.03  --splitting_mode                        input
% 0.36/1.03  --splitting_grd                         true
% 0.36/1.03  --splitting_cvd                         false
% 0.36/1.03  --splitting_cvd_svl                     false
% 0.36/1.03  --splitting_nvd                         32
% 0.36/1.03  --sub_typing                            true
% 0.36/1.03  --prep_gs_sim                           true
% 0.36/1.03  --prep_unflatten                        true
% 0.36/1.03  --prep_res_sim                          true
% 0.36/1.03  --prep_upred                            true
% 0.36/1.03  --prep_sem_filter                       exhaustive
% 0.36/1.03  --prep_sem_filter_out                   false
% 0.36/1.03  --pred_elim                             true
% 0.36/1.03  --res_sim_input                         true
% 0.36/1.03  --eq_ax_congr_red                       true
% 0.36/1.03  --pure_diseq_elim                       true
% 0.36/1.03  --brand_transform                       false
% 0.36/1.03  --non_eq_to_eq                          false
% 0.36/1.03  --prep_def_merge                        true
% 0.36/1.03  --prep_def_merge_prop_impl              false
% 0.36/1.03  --prep_def_merge_mbd                    true
% 0.36/1.03  --prep_def_merge_tr_red                 false
% 0.36/1.03  --prep_def_merge_tr_cl                  false
% 0.36/1.03  --smt_preprocessing                     true
% 0.36/1.03  --smt_ac_axioms                         fast
% 0.36/1.03  --preprocessed_out                      false
% 0.36/1.03  --preprocessed_stats                    false
% 0.36/1.03  
% 0.36/1.03  ------ Abstraction refinement Options
% 0.36/1.03  
% 0.36/1.03  --abstr_ref                             []
% 0.36/1.03  --abstr_ref_prep                        false
% 0.36/1.03  --abstr_ref_until_sat                   false
% 0.36/1.03  --abstr_ref_sig_restrict                funpre
% 0.36/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 0.36/1.03  --abstr_ref_under                       []
% 0.36/1.03  
% 0.36/1.03  ------ SAT Options
% 0.36/1.03  
% 0.36/1.03  --sat_mode                              false
% 0.36/1.03  --sat_fm_restart_options                ""
% 0.36/1.03  --sat_gr_def                            false
% 0.36/1.03  --sat_epr_types                         true
% 0.36/1.03  --sat_non_cyclic_types                  false
% 0.36/1.03  --sat_finite_models                     false
% 0.36/1.03  --sat_fm_lemmas                         false
% 0.36/1.03  --sat_fm_prep                           false
% 0.36/1.03  --sat_fm_uc_incr                        true
% 0.36/1.03  --sat_out_model                         small
% 0.36/1.03  --sat_out_clauses                       false
% 0.36/1.03  
% 0.36/1.03  ------ QBF Options
% 0.36/1.03  
% 0.36/1.03  --qbf_mode                              false
% 0.36/1.03  --qbf_elim_univ                         false
% 0.36/1.03  --qbf_dom_inst                          none
% 0.36/1.03  --qbf_dom_pre_inst                      false
% 0.36/1.03  --qbf_sk_in                             false
% 0.36/1.03  --qbf_pred_elim                         true
% 0.36/1.03  --qbf_split                             512
% 0.36/1.03  
% 0.36/1.03  ------ BMC1 Options
% 0.36/1.03  
% 0.36/1.03  --bmc1_incremental                      false
% 0.36/1.03  --bmc1_axioms                           reachable_all
% 0.36/1.03  --bmc1_min_bound                        0
% 0.36/1.03  --bmc1_max_bound                        -1
% 0.36/1.03  --bmc1_max_bound_default                -1
% 0.36/1.03  --bmc1_symbol_reachability              true
% 0.36/1.03  --bmc1_property_lemmas                  false
% 0.36/1.03  --bmc1_k_induction                      false
% 0.36/1.03  --bmc1_non_equiv_states                 false
% 0.36/1.03  --bmc1_deadlock                         false
% 0.36/1.03  --bmc1_ucm                              false
% 0.36/1.03  --bmc1_add_unsat_core                   none
% 0.36/1.03  --bmc1_unsat_core_children              false
% 0.36/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 0.36/1.03  --bmc1_out_stat                         full
% 0.36/1.03  --bmc1_ground_init                      false
% 0.36/1.03  --bmc1_pre_inst_next_state              false
% 0.36/1.03  --bmc1_pre_inst_state                   false
% 0.36/1.03  --bmc1_pre_inst_reach_state             false
% 0.36/1.03  --bmc1_out_unsat_core                   false
% 0.36/1.03  --bmc1_aig_witness_out                  false
% 0.36/1.03  --bmc1_verbose                          false
% 0.36/1.03  --bmc1_dump_clauses_tptp                false
% 0.36/1.03  --bmc1_dump_unsat_core_tptp             false
% 0.36/1.03  --bmc1_dump_file                        -
% 0.36/1.03  --bmc1_ucm_expand_uc_limit              128
% 0.36/1.03  --bmc1_ucm_n_expand_iterations          6
% 0.36/1.03  --bmc1_ucm_extend_mode                  1
% 0.36/1.03  --bmc1_ucm_init_mode                    2
% 0.36/1.03  --bmc1_ucm_cone_mode                    none
% 0.36/1.03  --bmc1_ucm_reduced_relation_type        0
% 0.36/1.03  --bmc1_ucm_relax_model                  4
% 0.36/1.03  --bmc1_ucm_full_tr_after_sat            true
% 0.36/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 0.36/1.03  --bmc1_ucm_layered_model                none
% 0.36/1.03  --bmc1_ucm_max_lemma_size               10
% 0.36/1.03  
% 0.36/1.03  ------ AIG Options
% 0.36/1.03  
% 0.36/1.03  --aig_mode                              false
% 0.36/1.03  
% 0.36/1.03  ------ Instantiation Options
% 0.36/1.03  
% 0.36/1.03  --instantiation_flag                    true
% 0.36/1.03  --inst_sos_flag                         false
% 0.36/1.03  --inst_sos_phase                        true
% 0.36/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.36/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.36/1.03  --inst_lit_sel_side                     num_symb
% 0.36/1.03  --inst_solver_per_active                1400
% 0.36/1.03  --inst_solver_calls_frac                1.
% 0.36/1.03  --inst_passive_queue_type               priority_queues
% 0.36/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.36/1.03  --inst_passive_queues_freq              [25;2]
% 0.36/1.03  --inst_dismatching                      true
% 0.36/1.03  --inst_eager_unprocessed_to_passive     true
% 0.36/1.03  --inst_prop_sim_given                   true
% 0.36/1.03  --inst_prop_sim_new                     false
% 0.36/1.03  --inst_subs_new                         false
% 0.36/1.03  --inst_eq_res_simp                      false
% 0.36/1.03  --inst_subs_given                       false
% 0.36/1.03  --inst_orphan_elimination               true
% 0.36/1.03  --inst_learning_loop_flag               true
% 0.36/1.03  --inst_learning_start                   3000
% 0.36/1.03  --inst_learning_factor                  2
% 0.36/1.03  --inst_start_prop_sim_after_learn       3
% 0.36/1.03  --inst_sel_renew                        solver
% 0.36/1.03  --inst_lit_activity_flag                true
% 0.36/1.03  --inst_restr_to_given                   false
% 0.36/1.03  --inst_activity_threshold               500
% 0.36/1.03  --inst_out_proof                        true
% 0.36/1.03  
% 0.36/1.03  ------ Resolution Options
% 0.36/1.03  
% 0.36/1.03  --resolution_flag                       true
% 0.36/1.03  --res_lit_sel                           adaptive
% 0.36/1.03  --res_lit_sel_side                      none
% 0.36/1.03  --res_ordering                          kbo
% 0.36/1.03  --res_to_prop_solver                    active
% 0.36/1.03  --res_prop_simpl_new                    false
% 0.36/1.03  --res_prop_simpl_given                  true
% 0.36/1.03  --res_passive_queue_type                priority_queues
% 0.36/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.36/1.03  --res_passive_queues_freq               [15;5]
% 0.36/1.03  --res_forward_subs                      full
% 0.36/1.03  --res_backward_subs                     full
% 0.36/1.03  --res_forward_subs_resolution           true
% 0.36/1.03  --res_backward_subs_resolution          true
% 0.36/1.03  --res_orphan_elimination                true
% 0.36/1.03  --res_time_limit                        2.
% 0.36/1.03  --res_out_proof                         true
% 0.36/1.03  
% 0.36/1.03  ------ Superposition Options
% 0.36/1.03  
% 0.36/1.03  --superposition_flag                    true
% 0.36/1.03  --sup_passive_queue_type                priority_queues
% 0.36/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.36/1.03  --sup_passive_queues_freq               [8;1;4]
% 0.36/1.03  --demod_completeness_check              fast
% 0.36/1.03  --demod_use_ground                      true
% 0.36/1.03  --sup_to_prop_solver                    passive
% 0.36/1.03  --sup_prop_simpl_new                    true
% 0.36/1.03  --sup_prop_simpl_given                  true
% 0.36/1.03  --sup_fun_splitting                     false
% 0.36/1.03  --sup_smt_interval                      50000
% 0.36/1.03  
% 0.36/1.03  ------ Superposition Simplification Setup
% 0.36/1.03  
% 0.36/1.03  --sup_indices_passive                   []
% 0.36/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.36/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.36/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.36/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 0.36/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.36/1.03  --sup_full_bw                           [BwDemod]
% 0.36/1.03  --sup_immed_triv                        [TrivRules]
% 0.36/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.36/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.36/1.03  --sup_immed_bw_main                     []
% 0.36/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.36/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 0.36/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.36/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.36/1.03  
% 0.36/1.03  ------ Combination Options
% 0.36/1.03  
% 0.36/1.03  --comb_res_mult                         3
% 0.36/1.03  --comb_sup_mult                         2
% 0.36/1.03  --comb_inst_mult                        10
% 0.36/1.03  
% 0.36/1.03  ------ Debug Options
% 0.36/1.03  
% 0.36/1.03  --dbg_backtrace                         false
% 0.36/1.03  --dbg_dump_prop_clauses                 false
% 0.36/1.03  --dbg_dump_prop_clauses_file            -
% 0.36/1.03  --dbg_out_stat                          false
% 0.36/1.03  ------ Parsing...
% 0.36/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.36/1.03  
% 0.36/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 0.36/1.03  
% 0.36/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.36/1.03  
% 0.36/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.36/1.03  ------ Proving...
% 0.36/1.03  ------ Problem Properties 
% 0.36/1.03  
% 0.36/1.03  
% 0.36/1.03  clauses                                 26
% 0.36/1.03  conjectures                             3
% 0.36/1.03  EPR                                     4
% 0.36/1.03  Horn                                    24
% 0.36/1.03  unary                                   13
% 0.36/1.03  binary                                  7
% 0.36/1.03  lits                                    48
% 0.36/1.03  lits eq                                 25
% 0.36/1.03  fd_pure                                 0
% 0.36/1.03  fd_pseudo                               0
% 0.36/1.03  fd_cond                                 5
% 0.36/1.03  fd_pseudo_cond                          1
% 0.36/1.03  AC symbols                              0
% 0.36/1.03  
% 0.36/1.03  ------ Schedule dynamic 5 is on 
% 0.36/1.03  
% 0.36/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.36/1.03  
% 0.36/1.03  
% 0.36/1.03  ------ 
% 0.36/1.03  Current options:
% 0.36/1.03  ------ 
% 0.36/1.03  
% 0.36/1.03  ------ Input Options
% 0.36/1.03  
% 0.36/1.03  --out_options                           all
% 0.36/1.03  --tptp_safe_out                         true
% 0.36/1.03  --problem_path                          ""
% 0.36/1.03  --include_path                          ""
% 0.36/1.03  --clausifier                            res/vclausify_rel
% 0.36/1.03  --clausifier_options                    --mode clausify
% 0.36/1.03  --stdin                                 false
% 0.36/1.03  --stats_out                             all
% 0.36/1.03  
% 0.36/1.03  ------ General Options
% 0.36/1.03  
% 0.36/1.03  --fof                                   false
% 0.36/1.03  --time_out_real                         305.
% 0.36/1.03  --time_out_virtual                      -1.
% 0.36/1.03  --symbol_type_check                     false
% 0.36/1.03  --clausify_out                          false
% 0.36/1.03  --sig_cnt_out                           false
% 0.36/1.03  --trig_cnt_out                          false
% 0.36/1.03  --trig_cnt_out_tolerance                1.
% 0.36/1.03  --trig_cnt_out_sk_spl                   false
% 0.36/1.03  --abstr_cl_out                          false
% 0.36/1.03  
% 0.36/1.03  ------ Global Options
% 0.36/1.03  
% 0.36/1.03  --schedule                              default
% 0.36/1.03  --add_important_lit                     false
% 0.36/1.03  --prop_solver_per_cl                    1000
% 0.36/1.03  --min_unsat_core                        false
% 0.36/1.03  --soft_assumptions                      false
% 0.36/1.03  --soft_lemma_size                       3
% 0.36/1.03  --prop_impl_unit_size                   0
% 0.36/1.03  --prop_impl_unit                        []
% 0.36/1.03  --share_sel_clauses                     true
% 0.36/1.03  --reset_solvers                         false
% 0.36/1.03  --bc_imp_inh                            [conj_cone]
% 0.36/1.03  --conj_cone_tolerance                   3.
% 0.36/1.03  --extra_neg_conj                        none
% 0.36/1.03  --large_theory_mode                     true
% 0.36/1.03  --prolific_symb_bound                   200
% 0.36/1.03  --lt_threshold                          2000
% 0.36/1.03  --clause_weak_htbl                      true
% 0.36/1.03  --gc_record_bc_elim                     false
% 0.36/1.03  
% 0.36/1.03  ------ Preprocessing Options
% 0.36/1.03  
% 0.36/1.03  --preprocessing_flag                    true
% 0.36/1.03  --time_out_prep_mult                    0.1
% 0.36/1.03  --splitting_mode                        input
% 0.36/1.03  --splitting_grd                         true
% 0.36/1.03  --splitting_cvd                         false
% 0.36/1.03  --splitting_cvd_svl                     false
% 0.36/1.03  --splitting_nvd                         32
% 0.36/1.03  --sub_typing                            true
% 0.36/1.03  --prep_gs_sim                           true
% 0.36/1.03  --prep_unflatten                        true
% 0.36/1.03  --prep_res_sim                          true
% 0.36/1.03  --prep_upred                            true
% 0.36/1.03  --prep_sem_filter                       exhaustive
% 0.36/1.03  --prep_sem_filter_out                   false
% 0.36/1.03  --pred_elim                             true
% 0.36/1.03  --res_sim_input                         true
% 0.36/1.03  --eq_ax_congr_red                       true
% 0.36/1.03  --pure_diseq_elim                       true
% 0.36/1.03  --brand_transform                       false
% 0.36/1.03  --non_eq_to_eq                          false
% 0.36/1.03  --prep_def_merge                        true
% 0.36/1.03  --prep_def_merge_prop_impl              false
% 0.36/1.03  --prep_def_merge_mbd                    true
% 0.36/1.03  --prep_def_merge_tr_red                 false
% 0.36/1.03  --prep_def_merge_tr_cl                  false
% 0.36/1.03  --smt_preprocessing                     true
% 0.36/1.03  --smt_ac_axioms                         fast
% 0.36/1.03  --preprocessed_out                      false
% 0.36/1.03  --preprocessed_stats                    false
% 0.36/1.03  
% 0.36/1.03  ------ Abstraction refinement Options
% 0.36/1.03  
% 0.36/1.03  --abstr_ref                             []
% 0.36/1.03  --abstr_ref_prep                        false
% 0.36/1.03  --abstr_ref_until_sat                   false
% 0.36/1.03  --abstr_ref_sig_restrict                funpre
% 0.36/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 0.36/1.03  --abstr_ref_under                       []
% 0.36/1.03  
% 0.36/1.03  ------ SAT Options
% 0.36/1.03  
% 0.36/1.03  --sat_mode                              false
% 0.36/1.03  --sat_fm_restart_options                ""
% 0.36/1.03  --sat_gr_def                            false
% 0.36/1.03  --sat_epr_types                         true
% 0.36/1.03  --sat_non_cyclic_types                  false
% 0.36/1.03  --sat_finite_models                     false
% 0.36/1.03  --sat_fm_lemmas                         false
% 0.36/1.03  --sat_fm_prep                           false
% 0.36/1.03  --sat_fm_uc_incr                        true
% 0.36/1.03  --sat_out_model                         small
% 0.36/1.03  --sat_out_clauses                       false
% 0.36/1.03  
% 0.36/1.03  ------ QBF Options
% 0.36/1.03  
% 0.36/1.03  --qbf_mode                              false
% 0.36/1.03  --qbf_elim_univ                         false
% 0.36/1.03  --qbf_dom_inst                          none
% 0.36/1.03  --qbf_dom_pre_inst                      false
% 0.36/1.03  --qbf_sk_in                             false
% 0.36/1.03  --qbf_pred_elim                         true
% 0.36/1.03  --qbf_split                             512
% 0.36/1.03  
% 0.36/1.03  ------ BMC1 Options
% 0.36/1.03  
% 0.36/1.03  --bmc1_incremental                      false
% 0.36/1.03  --bmc1_axioms                           reachable_all
% 0.36/1.03  --bmc1_min_bound                        0
% 0.36/1.03  --bmc1_max_bound                        -1
% 0.36/1.03  --bmc1_max_bound_default                -1
% 0.36/1.03  --bmc1_symbol_reachability              true
% 0.36/1.03  --bmc1_property_lemmas                  false
% 0.36/1.03  --bmc1_k_induction                      false
% 0.36/1.03  --bmc1_non_equiv_states                 false
% 0.36/1.03  --bmc1_deadlock                         false
% 0.36/1.03  --bmc1_ucm                              false
% 0.36/1.03  --bmc1_add_unsat_core                   none
% 0.36/1.03  --bmc1_unsat_core_children              false
% 0.36/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 0.36/1.03  --bmc1_out_stat                         full
% 0.36/1.03  --bmc1_ground_init                      false
% 0.36/1.03  --bmc1_pre_inst_next_state              false
% 0.36/1.03  --bmc1_pre_inst_state                   false
% 0.36/1.03  --bmc1_pre_inst_reach_state             false
% 0.36/1.03  --bmc1_out_unsat_core                   false
% 0.36/1.03  --bmc1_aig_witness_out                  false
% 0.36/1.03  --bmc1_verbose                          false
% 0.36/1.03  --bmc1_dump_clauses_tptp                false
% 0.36/1.03  --bmc1_dump_unsat_core_tptp             false
% 0.36/1.03  --bmc1_dump_file                        -
% 0.36/1.03  --bmc1_ucm_expand_uc_limit              128
% 0.36/1.03  --bmc1_ucm_n_expand_iterations          6
% 0.36/1.03  --bmc1_ucm_extend_mode                  1
% 0.36/1.03  --bmc1_ucm_init_mode                    2
% 0.36/1.03  --bmc1_ucm_cone_mode                    none
% 0.36/1.03  --bmc1_ucm_reduced_relation_type        0
% 0.36/1.03  --bmc1_ucm_relax_model                  4
% 0.36/1.03  --bmc1_ucm_full_tr_after_sat            true
% 0.36/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 0.36/1.03  --bmc1_ucm_layered_model                none
% 0.36/1.03  --bmc1_ucm_max_lemma_size               10
% 0.36/1.03  
% 0.36/1.03  ------ AIG Options
% 0.36/1.03  
% 0.36/1.03  --aig_mode                              false
% 0.36/1.03  
% 0.36/1.03  ------ Instantiation Options
% 0.36/1.03  
% 0.36/1.03  --instantiation_flag                    true
% 0.36/1.03  --inst_sos_flag                         false
% 0.36/1.03  --inst_sos_phase                        true
% 0.36/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.36/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.36/1.03  --inst_lit_sel_side                     none
% 0.36/1.03  --inst_solver_per_active                1400
% 0.36/1.03  --inst_solver_calls_frac                1.
% 0.36/1.03  --inst_passive_queue_type               priority_queues
% 0.36/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.36/1.03  --inst_passive_queues_freq              [25;2]
% 0.36/1.03  --inst_dismatching                      true
% 0.36/1.03  --inst_eager_unprocessed_to_passive     true
% 0.36/1.03  --inst_prop_sim_given                   true
% 0.36/1.03  --inst_prop_sim_new                     false
% 0.36/1.03  --inst_subs_new                         false
% 0.36/1.03  --inst_eq_res_simp                      false
% 0.36/1.03  --inst_subs_given                       false
% 0.36/1.03  --inst_orphan_elimination               true
% 0.36/1.03  --inst_learning_loop_flag               true
% 0.36/1.03  --inst_learning_start                   3000
% 0.36/1.03  --inst_learning_factor                  2
% 0.36/1.03  --inst_start_prop_sim_after_learn       3
% 0.36/1.03  --inst_sel_renew                        solver
% 0.36/1.03  --inst_lit_activity_flag                true
% 0.36/1.03  --inst_restr_to_given                   false
% 0.36/1.03  --inst_activity_threshold               500
% 0.36/1.03  --inst_out_proof                        true
% 0.36/1.03  
% 0.36/1.03  ------ Resolution Options
% 0.36/1.03  
% 0.36/1.03  --resolution_flag                       false
% 0.36/1.03  --res_lit_sel                           adaptive
% 0.36/1.03  --res_lit_sel_side                      none
% 0.36/1.03  --res_ordering                          kbo
% 0.36/1.03  --res_to_prop_solver                    active
% 0.36/1.03  --res_prop_simpl_new                    false
% 0.36/1.03  --res_prop_simpl_given                  true
% 0.36/1.03  --res_passive_queue_type                priority_queues
% 0.36/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.36/1.03  --res_passive_queues_freq               [15;5]
% 0.36/1.03  --res_forward_subs                      full
% 0.36/1.03  --res_backward_subs                     full
% 0.36/1.03  --res_forward_subs_resolution           true
% 0.36/1.03  --res_backward_subs_resolution          true
% 0.36/1.03  --res_orphan_elimination                true
% 0.36/1.03  --res_time_limit                        2.
% 0.36/1.03  --res_out_proof                         true
% 0.36/1.03  
% 0.36/1.03  ------ Superposition Options
% 0.36/1.03  
% 0.36/1.03  --superposition_flag                    true
% 0.36/1.03  --sup_passive_queue_type                priority_queues
% 0.36/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.36/1.03  --sup_passive_queues_freq               [8;1;4]
% 0.36/1.03  --demod_completeness_check              fast
% 0.36/1.03  --demod_use_ground                      true
% 0.36/1.03  --sup_to_prop_solver                    passive
% 0.36/1.03  --sup_prop_simpl_new                    true
% 0.36/1.03  --sup_prop_simpl_given                  true
% 0.36/1.03  --sup_fun_splitting                     false
% 0.36/1.03  --sup_smt_interval                      50000
% 0.36/1.03  
% 0.36/1.03  ------ Superposition Simplification Setup
% 0.36/1.03  
% 0.36/1.03  --sup_indices_passive                   []
% 0.36/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.36/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.36/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.36/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 0.36/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.36/1.03  --sup_full_bw                           [BwDemod]
% 0.36/1.03  --sup_immed_triv                        [TrivRules]
% 0.36/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.36/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.36/1.03  --sup_immed_bw_main                     []
% 0.36/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.36/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 0.36/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.36/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.36/1.03  
% 0.36/1.03  ------ Combination Options
% 0.36/1.03  
% 0.36/1.03  --comb_res_mult                         3
% 0.36/1.03  --comb_sup_mult                         2
% 0.36/1.03  --comb_inst_mult                        10
% 0.36/1.03  
% 0.36/1.03  ------ Debug Options
% 0.36/1.03  
% 0.36/1.03  --dbg_backtrace                         false
% 0.36/1.03  --dbg_dump_prop_clauses                 false
% 0.36/1.03  --dbg_dump_prop_clauses_file            -
% 0.36/1.03  --dbg_out_stat                          false
% 0.36/1.03  
% 0.36/1.03  
% 0.36/1.03  
% 0.36/1.03  
% 0.36/1.03  ------ Proving...
% 0.36/1.03  
% 0.36/1.03  
% 0.36/1.03  % SZS status Theorem for theBenchmark.p
% 0.36/1.03  
% 0.36/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 0.36/1.03  
% 0.36/1.03  fof(f7,axiom,(
% 0.36/1.03    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.36/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.36/1.03  
% 0.36/1.03  fof(f22,plain,(
% 0.36/1.03    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.36/1.03    inference(ennf_transformation,[],[f7])).
% 0.36/1.03  
% 0.36/1.03  fof(f39,plain,(
% 0.36/1.03    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.36/1.03    inference(nnf_transformation,[],[f22])).
% 0.36/1.03  
% 0.36/1.03  fof(f56,plain,(
% 0.36/1.03    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.36/1.03    inference(cnf_transformation,[],[f39])).
% 0.36/1.03  
% 0.36/1.03  fof(f14,axiom,(
% 0.36/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.36/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.36/1.03  
% 0.36/1.03  fof(f20,plain,(
% 0.36/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.36/1.03    inference(pure_predicate_removal,[],[f14])).
% 0.36/1.03  
% 0.36/1.03  fof(f30,plain,(
% 0.36/1.03    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.36/1.03    inference(ennf_transformation,[],[f20])).
% 0.36/1.03  
% 0.36/1.03  fof(f69,plain,(
% 0.36/1.03    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.36/1.03    inference(cnf_transformation,[],[f30])).
% 0.36/1.03  
% 0.36/1.03  fof(f18,conjecture,(
% 0.36/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 0.36/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.36/1.03  
% 0.36/1.03  fof(f19,negated_conjecture,(
% 0.36/1.03    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 0.36/1.03    inference(negated_conjecture,[],[f18])).
% 0.36/1.03  
% 0.36/1.03  fof(f35,plain,(
% 0.36/1.03    ? [X0,X1,X2] : ((k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.36/1.04    inference(ennf_transformation,[],[f19])).
% 0.36/1.04  
% 0.36/1.04  fof(f36,plain,(
% 0.36/1.04    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.36/1.04    inference(flattening,[],[f35])).
% 0.36/1.04  
% 0.36/1.04  fof(f44,plain,(
% 0.36/1.04    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_tarski(k1_funct_1(sK4,sK2)) != k2_relset_1(k1_tarski(sK2),sK3,sK4) & k1_xboole_0 != sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK4,k1_tarski(sK2),sK3) & v1_funct_1(sK4))),
% 0.36/1.04    introduced(choice_axiom,[])).
% 0.36/1.04  
% 0.36/1.04  fof(f45,plain,(
% 0.36/1.04    k1_tarski(k1_funct_1(sK4,sK2)) != k2_relset_1(k1_tarski(sK2),sK3,sK4) & k1_xboole_0 != sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK4,k1_tarski(sK2),sK3) & v1_funct_1(sK4)),
% 0.36/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f36,f44])).
% 0.36/1.04  
% 0.36/1.04  fof(f77,plain,(
% 0.36/1.04    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))),
% 0.36/1.04    inference(cnf_transformation,[],[f45])).
% 0.36/1.04  
% 0.36/1.04  fof(f3,axiom,(
% 0.36/1.04    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.36/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.36/1.04  
% 0.36/1.04  fof(f48,plain,(
% 0.36/1.04    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.36/1.04    inference(cnf_transformation,[],[f3])).
% 0.36/1.04  
% 0.36/1.04  fof(f4,axiom,(
% 0.36/1.04    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.36/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.36/1.04  
% 0.36/1.04  fof(f49,plain,(
% 0.36/1.04    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.36/1.04    inference(cnf_transformation,[],[f4])).
% 0.36/1.04  
% 0.36/1.04  fof(f5,axiom,(
% 0.36/1.04    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.36/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.36/1.04  
% 0.36/1.04  fof(f50,plain,(
% 0.36/1.04    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.36/1.04    inference(cnf_transformation,[],[f5])).
% 0.36/1.04  
% 0.36/1.04  fof(f80,plain,(
% 0.36/1.04    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.36/1.04    inference(definition_unfolding,[],[f49,f50])).
% 0.36/1.04  
% 0.36/1.04  fof(f81,plain,(
% 0.36/1.04    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.36/1.04    inference(definition_unfolding,[],[f48,f80])).
% 0.36/1.04  
% 0.36/1.04  fof(f99,plain,(
% 0.36/1.04    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))),
% 0.36/1.04    inference(definition_unfolding,[],[f77,f81])).
% 0.36/1.04  
% 0.36/1.04  fof(f13,axiom,(
% 0.36/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.36/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.36/1.04  
% 0.36/1.04  fof(f29,plain,(
% 0.36/1.04    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.36/1.04    inference(ennf_transformation,[],[f13])).
% 0.36/1.04  
% 0.36/1.04  fof(f68,plain,(
% 0.36/1.04    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.36/1.04    inference(cnf_transformation,[],[f29])).
% 0.36/1.04  
% 0.36/1.04  fof(f6,axiom,(
% 0.36/1.04    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.36/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.36/1.04  
% 0.36/1.04  fof(f21,plain,(
% 0.36/1.04    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.36/1.04    inference(ennf_transformation,[],[f6])).
% 0.36/1.04  
% 0.36/1.04  fof(f37,plain,(
% 0.36/1.04    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 0.36/1.04    inference(nnf_transformation,[],[f21])).
% 0.36/1.04  
% 0.36/1.04  fof(f38,plain,(
% 0.36/1.04    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 0.36/1.04    inference(flattening,[],[f37])).
% 0.36/1.04  
% 0.36/1.04  fof(f51,plain,(
% 0.36/1.04    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 0.36/1.04    inference(cnf_transformation,[],[f38])).
% 0.36/1.04  
% 0.36/1.04  fof(f1,axiom,(
% 0.36/1.04    k1_xboole_0 = o_0_0_xboole_0),
% 0.36/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.36/1.04  
% 0.36/1.04  fof(f46,plain,(
% 0.36/1.04    k1_xboole_0 = o_0_0_xboole_0),
% 0.36/1.04    inference(cnf_transformation,[],[f1])).
% 0.36/1.04  
% 0.36/1.04  fof(f87,plain,(
% 0.36/1.04    ( ! [X2,X0,X1] : (k2_enumset1(X1,X1,X1,X2) = X0 | k2_enumset1(X2,X2,X2,X2) = X0 | k2_enumset1(X1,X1,X1,X1) = X0 | o_0_0_xboole_0 = X0 | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))) )),
% 0.36/1.04    inference(definition_unfolding,[],[f51,f80,f81,f81,f46,f80])).
% 0.36/1.04  
% 0.36/1.04  fof(f11,axiom,(
% 0.36/1.04    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 0.36/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.36/1.04  
% 0.36/1.04  fof(f26,plain,(
% 0.36/1.04    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.36/1.04    inference(ennf_transformation,[],[f11])).
% 0.36/1.04  
% 0.36/1.04  fof(f27,plain,(
% 0.36/1.04    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.36/1.04    inference(flattening,[],[f26])).
% 0.36/1.04  
% 0.36/1.04  fof(f66,plain,(
% 0.36/1.04    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.36/1.04    inference(cnf_transformation,[],[f27])).
% 0.36/1.04  
% 0.36/1.04  fof(f92,plain,(
% 0.36/1.04    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.36/1.04    inference(definition_unfolding,[],[f66,f81,f81])).
% 0.36/1.04  
% 0.36/1.04  fof(f75,plain,(
% 0.36/1.04    v1_funct_1(sK4)),
% 0.36/1.04    inference(cnf_transformation,[],[f45])).
% 0.36/1.04  
% 0.36/1.04  fof(f15,axiom,(
% 0.36/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 0.36/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.36/1.04  
% 0.36/1.04  fof(f31,plain,(
% 0.36/1.04    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.36/1.04    inference(ennf_transformation,[],[f15])).
% 0.36/1.04  
% 0.36/1.04  fof(f70,plain,(
% 0.36/1.04    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.36/1.04    inference(cnf_transformation,[],[f31])).
% 0.36/1.04  
% 0.36/1.04  fof(f79,plain,(
% 0.36/1.04    k1_tarski(k1_funct_1(sK4,sK2)) != k2_relset_1(k1_tarski(sK2),sK3,sK4)),
% 0.36/1.04    inference(cnf_transformation,[],[f45])).
% 0.36/1.04  
% 0.36/1.04  fof(f97,plain,(
% 0.36/1.04    k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)),
% 0.36/1.04    inference(definition_unfolding,[],[f79,f81,f81])).
% 0.36/1.04  
% 0.36/1.04  fof(f9,axiom,(
% 0.36/1.04    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.36/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.36/1.04  
% 0.36/1.04  fof(f23,plain,(
% 0.36/1.04    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.36/1.04    inference(ennf_transformation,[],[f9])).
% 0.36/1.04  
% 0.36/1.04  fof(f24,plain,(
% 0.36/1.04    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.36/1.04    inference(flattening,[],[f23])).
% 0.36/1.04  
% 0.36/1.04  fof(f60,plain,(
% 0.36/1.04    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.36/1.04    inference(cnf_transformation,[],[f24])).
% 0.36/1.04  
% 0.36/1.04  fof(f91,plain,(
% 0.36/1.04    ( ! [X0] : (o_0_0_xboole_0 = X0 | o_0_0_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.36/1.04    inference(definition_unfolding,[],[f60,f46,f46])).
% 0.36/1.04  
% 0.36/1.04  fof(f16,axiom,(
% 0.36/1.04    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.36/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.36/1.04  
% 0.36/1.04  fof(f32,plain,(
% 0.36/1.04    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.36/1.04    inference(ennf_transformation,[],[f16])).
% 0.36/1.04  
% 0.36/1.04  fof(f42,plain,(
% 0.36/1.04    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)))),
% 0.36/1.04    introduced(choice_axiom,[])).
% 0.36/1.04  
% 0.36/1.04  fof(f43,plain,(
% 0.36/1.04    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)) | k1_xboole_0 = X0)),
% 0.36/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f42])).
% 0.36/1.04  
% 0.36/1.04  fof(f71,plain,(
% 0.36/1.04    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 0.36/1.04    inference(cnf_transformation,[],[f43])).
% 0.36/1.04  
% 0.36/1.04  fof(f95,plain,(
% 0.36/1.04    ( ! [X0] : (r2_hidden(sK1(X0),X0) | o_0_0_xboole_0 = X0) )),
% 0.36/1.04    inference(definition_unfolding,[],[f71,f46])).
% 0.36/1.04  
% 0.36/1.04  fof(f17,axiom,(
% 0.36/1.04    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 0.36/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.36/1.04  
% 0.36/1.04  fof(f33,plain,(
% 0.36/1.04    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.36/1.04    inference(ennf_transformation,[],[f17])).
% 0.36/1.04  
% 0.36/1.04  fof(f34,plain,(
% 0.36/1.04    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.36/1.04    inference(flattening,[],[f33])).
% 0.36/1.04  
% 0.36/1.04  fof(f74,plain,(
% 0.36/1.04    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.36/1.04    inference(cnf_transformation,[],[f34])).
% 0.36/1.04  
% 0.36/1.04  fof(f96,plain,(
% 0.36/1.04    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | o_0_0_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.36/1.04    inference(definition_unfolding,[],[f74,f46])).
% 0.36/1.04  
% 0.36/1.04  fof(f76,plain,(
% 0.36/1.04    v1_funct_2(sK4,k1_tarski(sK2),sK3)),
% 0.36/1.04    inference(cnf_transformation,[],[f45])).
% 0.36/1.04  
% 0.36/1.04  fof(f100,plain,(
% 0.36/1.04    v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3)),
% 0.36/1.04    inference(definition_unfolding,[],[f76,f81])).
% 0.36/1.04  
% 0.36/1.04  fof(f78,plain,(
% 0.36/1.04    k1_xboole_0 != sK3),
% 0.36/1.04    inference(cnf_transformation,[],[f45])).
% 0.36/1.04  
% 0.36/1.04  fof(f98,plain,(
% 0.36/1.04    o_0_0_xboole_0 != sK3),
% 0.36/1.04    inference(definition_unfolding,[],[f78,f46])).
% 0.36/1.04  
% 0.36/1.04  fof(f12,axiom,(
% 0.36/1.04    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.36/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.36/1.04  
% 0.36/1.04  fof(f28,plain,(
% 0.36/1.04    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.36/1.04    inference(ennf_transformation,[],[f12])).
% 0.36/1.04  
% 0.36/1.04  fof(f67,plain,(
% 0.36/1.04    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.36/1.04    inference(cnf_transformation,[],[f28])).
% 0.36/1.04  
% 0.36/1.04  fof(f8,axiom,(
% 0.36/1.04    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.36/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.36/1.04  
% 0.36/1.04  fof(f59,plain,(
% 0.36/1.04    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.36/1.04    inference(cnf_transformation,[],[f8])).
% 0.36/1.04  
% 0.36/1.04  fof(f88,plain,(
% 0.36/1.04    o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0)),
% 0.36/1.04    inference(definition_unfolding,[],[f59,f46,f46])).
% 0.36/1.04  
% 0.36/1.04  fof(f2,axiom,(
% 0.36/1.04    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.36/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.36/1.04  
% 0.36/1.04  fof(f47,plain,(
% 0.36/1.04    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.36/1.04    inference(cnf_transformation,[],[f2])).
% 0.36/1.04  
% 0.36/1.04  fof(f82,plain,(
% 0.36/1.04    ( ! [X0] : (r1_tarski(o_0_0_xboole_0,X0)) )),
% 0.36/1.04    inference(definition_unfolding,[],[f47,f46])).
% 0.36/1.04  
% 0.36/1.04  fof(f10,axiom,(
% 0.36/1.04    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.36/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.36/1.04  
% 0.36/1.04  fof(f25,plain,(
% 0.36/1.04    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.36/1.04    inference(ennf_transformation,[],[f10])).
% 0.36/1.04  
% 0.36/1.04  fof(f40,plain,(
% 0.36/1.04    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK0(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK0(X0,X1)) = X0 & v1_funct_1(sK0(X0,X1)) & v1_relat_1(sK0(X0,X1))))),
% 0.36/1.04    introduced(choice_axiom,[])).
% 0.36/1.04  
% 0.36/1.04  fof(f41,plain,(
% 0.36/1.04    ! [X0,X1] : (! [X3] : (k1_funct_1(sK0(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK0(X0,X1)) = X0 & v1_funct_1(sK0(X0,X1)) & v1_relat_1(sK0(X0,X1)))),
% 0.36/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f40])).
% 0.36/1.04  
% 0.36/1.04  fof(f64,plain,(
% 0.36/1.04    ( ! [X0,X1] : (k1_relat_1(sK0(X0,X1)) = X0) )),
% 0.36/1.04    inference(cnf_transformation,[],[f41])).
% 0.36/1.04  
% 0.36/1.04  fof(f62,plain,(
% 0.36/1.04    ( ! [X0,X1] : (v1_relat_1(sK0(X0,X1))) )),
% 0.36/1.04    inference(cnf_transformation,[],[f41])).
% 0.36/1.04  
% 0.36/1.04  fof(f63,plain,(
% 0.36/1.04    ( ! [X0,X1] : (v1_funct_1(sK0(X0,X1))) )),
% 0.36/1.04    inference(cnf_transformation,[],[f41])).
% 0.36/1.04  
% 0.36/1.04  cnf(c_7,plain,
% 0.36/1.04      ( ~ v4_relat_1(X0,X1)
% 0.36/1.04      | r1_tarski(k1_relat_1(X0),X1)
% 0.36/1.04      | ~ v1_relat_1(X0) ),
% 0.36/1.04      inference(cnf_transformation,[],[f56]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_19,plain,
% 0.36/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.36/1.04      | v4_relat_1(X0,X1) ),
% 0.36/1.04      inference(cnf_transformation,[],[f69]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_27,negated_conjecture,
% 0.36/1.04      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) ),
% 0.36/1.04      inference(cnf_transformation,[],[f99]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_321,plain,
% 0.36/1.04      ( v4_relat_1(X0,X1)
% 0.36/1.04      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 0.36/1.04      | sK4 != X0 ),
% 0.36/1.04      inference(resolution_lifted,[status(thm)],[c_19,c_27]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_322,plain,
% 0.36/1.04      ( v4_relat_1(sK4,X0)
% 0.36/1.04      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 0.36/1.04      inference(unflattening,[status(thm)],[c_321]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_388,plain,
% 0.36/1.04      ( r1_tarski(k1_relat_1(X0),X1)
% 0.36/1.04      | ~ v1_relat_1(X0)
% 0.36/1.04      | X2 != X1
% 0.36/1.04      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
% 0.36/1.04      | sK4 != X0 ),
% 0.36/1.04      inference(resolution_lifted,[status(thm)],[c_7,c_322]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_389,plain,
% 0.36/1.04      ( r1_tarski(k1_relat_1(sK4),X0)
% 0.36/1.04      | ~ v1_relat_1(sK4)
% 0.36/1.04      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 0.36/1.04      inference(unflattening,[status(thm)],[c_388]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_18,plain,
% 0.36/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.36/1.04      | v1_relat_1(X0) ),
% 0.36/1.04      inference(cnf_transformation,[],[f68]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_333,plain,
% 0.36/1.04      ( v1_relat_1(X0)
% 0.36/1.04      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 0.36/1.04      | sK4 != X0 ),
% 0.36/1.04      inference(resolution_lifted,[status(thm)],[c_18,c_27]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_334,plain,
% 0.36/1.04      ( v1_relat_1(sK4)
% 0.36/1.04      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 0.36/1.04      inference(unflattening,[status(thm)],[c_333]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_393,plain,
% 0.36/1.04      ( r1_tarski(k1_relat_1(sK4),X0)
% 0.36/1.04      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 0.36/1.04      inference(global_propositional_subsumption,
% 0.36/1.04                [status(thm)],
% 0.36/1.04                [c_389,c_334]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_1359,plain,
% 0.36/1.04      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 0.36/1.04      | r1_tarski(k1_relat_1(sK4),X0) = iProver_top ),
% 0.36/1.04      inference(predicate_to_equality,[status(thm)],[c_393]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_1637,plain,
% 0.36/1.04      ( r1_tarski(k1_relat_1(sK4),k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
% 0.36/1.04      inference(equality_resolution,[status(thm)],[c_1359]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_5,plain,
% 0.36/1.04      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
% 0.36/1.04      | k2_enumset1(X1,X1,X1,X2) = X0
% 0.36/1.04      | k2_enumset1(X2,X2,X2,X2) = X0
% 0.36/1.04      | k2_enumset1(X1,X1,X1,X1) = X0
% 0.36/1.04      | o_0_0_xboole_0 = X0 ),
% 0.36/1.04      inference(cnf_transformation,[],[f87]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_1373,plain,
% 0.36/1.04      ( k2_enumset1(X0,X0,X0,X1) = X2
% 0.36/1.04      | k2_enumset1(X1,X1,X1,X1) = X2
% 0.36/1.04      | k2_enumset1(X0,X0,X0,X0) = X2
% 0.36/1.04      | o_0_0_xboole_0 = X2
% 0.36/1.04      | r1_tarski(X2,k2_enumset1(X0,X0,X0,X1)) != iProver_top ),
% 0.36/1.04      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_2766,plain,
% 0.36/1.04      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_relat_1(sK4)
% 0.36/1.04      | k1_relat_1(sK4) = o_0_0_xboole_0 ),
% 0.36/1.04      inference(superposition,[status(thm)],[c_1637,c_1373]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_16,plain,
% 0.36/1.04      ( ~ v1_funct_1(X0)
% 0.36/1.04      | ~ v1_relat_1(X0)
% 0.36/1.04      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 0.36/1.04      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 0.36/1.04      inference(cnf_transformation,[],[f92]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_1367,plain,
% 0.36/1.04      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
% 0.36/1.04      | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
% 0.36/1.04      | v1_funct_1(X1) != iProver_top
% 0.36/1.04      | v1_relat_1(X1) != iProver_top ),
% 0.36/1.04      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_2816,plain,
% 0.36/1.04      ( k2_enumset1(k1_funct_1(X0,sK2),k1_funct_1(X0,sK2),k1_funct_1(X0,sK2),k1_funct_1(X0,sK2)) = k2_relat_1(X0)
% 0.36/1.04      | k1_relat_1(X0) != k1_relat_1(sK4)
% 0.36/1.04      | k1_relat_1(sK4) = o_0_0_xboole_0
% 0.36/1.04      | v1_funct_1(X0) != iProver_top
% 0.36/1.04      | v1_relat_1(X0) != iProver_top ),
% 0.36/1.04      inference(superposition,[status(thm)],[c_2766,c_1367]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_3539,plain,
% 0.36/1.04      ( k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) = k2_relat_1(sK4)
% 0.36/1.04      | k1_relat_1(sK4) = o_0_0_xboole_0
% 0.36/1.04      | v1_funct_1(sK4) != iProver_top
% 0.36/1.04      | v1_relat_1(sK4) != iProver_top ),
% 0.36/1.04      inference(equality_resolution,[status(thm)],[c_2816]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_29,negated_conjecture,
% 0.36/1.04      ( v1_funct_1(sK4) ),
% 0.36/1.04      inference(cnf_transformation,[],[f75]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_30,plain,
% 0.36/1.04      ( v1_funct_1(sK4) = iProver_top ),
% 0.36/1.04      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_989,plain,( X0 = X0 ),theory(equality) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_1518,plain,
% 0.36/1.04      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) ),
% 0.36/1.04      inference(instantiation,[status(thm)],[c_989]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_1521,plain,
% 0.36/1.04      ( v1_relat_1(sK4)
% 0.36/1.04      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) ),
% 0.36/1.04      inference(instantiation,[status(thm)],[c_334]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_1522,plain,
% 0.36/1.04      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))
% 0.36/1.04      | v1_relat_1(sK4) = iProver_top ),
% 0.36/1.04      inference(predicate_to_equality,[status(thm)],[c_1521]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_20,plain,
% 0.36/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.36/1.04      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 0.36/1.04      inference(cnf_transformation,[],[f70]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_312,plain,
% 0.36/1.04      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 0.36/1.04      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 0.36/1.04      | sK4 != X2 ),
% 0.36/1.04      inference(resolution_lifted,[status(thm)],[c_20,c_27]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_313,plain,
% 0.36/1.04      ( k2_relset_1(X0,X1,sK4) = k2_relat_1(sK4)
% 0.36/1.04      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 0.36/1.04      inference(unflattening,[status(thm)],[c_312]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_1539,plain,
% 0.36/1.04      ( k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) = k2_relat_1(sK4) ),
% 0.36/1.04      inference(equality_resolution,[status(thm)],[c_313]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_25,negated_conjecture,
% 0.36/1.04      ( k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) ),
% 0.36/1.04      inference(cnf_transformation,[],[f97]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_1572,plain,
% 0.36/1.04      ( k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k2_relat_1(sK4) ),
% 0.36/1.04      inference(demodulation,[status(thm)],[c_1539,c_25]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_3550,plain,
% 0.36/1.04      ( k1_relat_1(sK4) = o_0_0_xboole_0 ),
% 0.36/1.04      inference(global_propositional_subsumption,
% 0.36/1.04                [status(thm)],
% 0.36/1.04                [c_3539,c_30,c_1518,c_1522,c_1572]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_11,plain,
% 0.36/1.04      ( ~ v1_relat_1(X0)
% 0.36/1.04      | k1_relat_1(X0) != o_0_0_xboole_0
% 0.36/1.04      | o_0_0_xboole_0 = X0 ),
% 0.36/1.04      inference(cnf_transformation,[],[f91]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_1371,plain,
% 0.36/1.04      ( k1_relat_1(X0) != o_0_0_xboole_0
% 0.36/1.04      | o_0_0_xboole_0 = X0
% 0.36/1.04      | v1_relat_1(X0) != iProver_top ),
% 0.36/1.04      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_3567,plain,
% 0.36/1.04      ( sK4 = o_0_0_xboole_0 | v1_relat_1(sK4) != iProver_top ),
% 0.36/1.04      inference(superposition,[status(thm)],[c_3550,c_1371]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_1926,plain,
% 0.36/1.04      ( sK4 = sK4 ),
% 0.36/1.04      inference(instantiation,[status(thm)],[c_989]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_2391,plain,
% 0.36/1.04      ( ~ v1_relat_1(sK4)
% 0.36/1.04      | k1_relat_1(sK4) != o_0_0_xboole_0
% 0.36/1.04      | o_0_0_xboole_0 = sK4 ),
% 0.36/1.04      inference(instantiation,[status(thm)],[c_11]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_990,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_1927,plain,
% 0.36/1.04      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 0.36/1.04      inference(instantiation,[status(thm)],[c_990]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_2487,plain,
% 0.36/1.04      ( X0 != sK4 | sK4 = X0 | sK4 != sK4 ),
% 0.36/1.04      inference(instantiation,[status(thm)],[c_1927]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_2488,plain,
% 0.36/1.04      ( sK4 != sK4 | sK4 = o_0_0_xboole_0 | o_0_0_xboole_0 != sK4 ),
% 0.36/1.04      inference(instantiation,[status(thm)],[c_2487]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_3733,plain,
% 0.36/1.04      ( sK4 = o_0_0_xboole_0 ),
% 0.36/1.04      inference(global_propositional_subsumption,
% 0.36/1.04                [status(thm)],
% 0.36/1.04                [c_3567,c_30,c_1518,c_1521,c_1522,c_1572,c_1926,c_2391,
% 0.36/1.04                 c_2488,c_3539]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_23,plain,
% 0.36/1.04      ( r2_hidden(sK1(X0),X0) | o_0_0_xboole_0 = X0 ),
% 0.36/1.04      inference(cnf_transformation,[],[f95]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_1363,plain,
% 0.36/1.04      ( o_0_0_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 0.36/1.04      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_24,plain,
% 0.36/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 0.36/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.36/1.04      | ~ r2_hidden(X3,X1)
% 0.36/1.04      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 0.36/1.04      | ~ v1_funct_1(X0)
% 0.36/1.04      | o_0_0_xboole_0 = X2 ),
% 0.36/1.04      inference(cnf_transformation,[],[f96]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_28,negated_conjecture,
% 0.36/1.04      ( v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
% 0.36/1.04      inference(cnf_transformation,[],[f100]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_291,plain,
% 0.36/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.36/1.04      | ~ r2_hidden(X3,X1)
% 0.36/1.04      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 0.36/1.04      | ~ v1_funct_1(X0)
% 0.36/1.04      | k2_enumset1(sK2,sK2,sK2,sK2) != X1
% 0.36/1.04      | sK3 != X2
% 0.36/1.04      | sK4 != X0
% 0.36/1.04      | o_0_0_xboole_0 = X2 ),
% 0.36/1.04      inference(resolution_lifted,[status(thm)],[c_24,c_28]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_292,plain,
% 0.36/1.04      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))
% 0.36/1.04      | ~ r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2))
% 0.36/1.04      | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4))
% 0.36/1.04      | ~ v1_funct_1(sK4)
% 0.36/1.04      | o_0_0_xboole_0 = sK3 ),
% 0.36/1.04      inference(unflattening,[status(thm)],[c_291]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_26,negated_conjecture,
% 0.36/1.04      ( o_0_0_xboole_0 != sK3 ),
% 0.36/1.04      inference(cnf_transformation,[],[f98]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_296,plain,
% 0.36/1.04      ( ~ r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2))
% 0.36/1.04      | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)) ),
% 0.36/1.04      inference(global_propositional_subsumption,
% 0.36/1.04                [status(thm)],
% 0.36/1.04                [c_292,c_29,c_27,c_26]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_1361,plain,
% 0.36/1.04      ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
% 0.36/1.04      | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)) = iProver_top ),
% 0.36/1.04      inference(predicate_to_equality,[status(thm)],[c_296]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_1592,plain,
% 0.36/1.04      ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
% 0.36/1.04      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top ),
% 0.36/1.04      inference(light_normalisation,[status(thm)],[c_1361,c_1539]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_2062,plain,
% 0.36/1.04      ( k2_enumset1(sK2,sK2,sK2,sK2) = o_0_0_xboole_0
% 0.36/1.04      | r2_hidden(k1_funct_1(sK4,sK1(k2_enumset1(sK2,sK2,sK2,sK2))),k2_relat_1(sK4)) = iProver_top ),
% 0.36/1.04      inference(superposition,[status(thm)],[c_1363,c_1592]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_17,plain,
% 0.36/1.04      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 0.36/1.04      inference(cnf_transformation,[],[f67]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_1366,plain,
% 0.36/1.04      ( r2_hidden(X0,X1) != iProver_top
% 0.36/1.04      | r1_tarski(X1,X0) != iProver_top ),
% 0.36/1.04      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_2269,plain,
% 0.36/1.04      ( k2_enumset1(sK2,sK2,sK2,sK2) = o_0_0_xboole_0
% 0.36/1.04      | r1_tarski(k2_relat_1(sK4),k1_funct_1(sK4,sK1(k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top ),
% 0.36/1.04      inference(superposition,[status(thm)],[c_2062,c_1366]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_3738,plain,
% 0.36/1.04      ( k2_enumset1(sK2,sK2,sK2,sK2) = o_0_0_xboole_0
% 0.36/1.04      | r1_tarski(k2_relat_1(o_0_0_xboole_0),k1_funct_1(o_0_0_xboole_0,sK1(k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top ),
% 0.36/1.04      inference(demodulation,[status(thm)],[c_3733,c_2269]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_8,plain,
% 0.36/1.04      ( k2_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
% 0.36/1.04      inference(cnf_transformation,[],[f88]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_3769,plain,
% 0.36/1.04      ( k2_enumset1(sK2,sK2,sK2,sK2) = o_0_0_xboole_0
% 0.36/1.04      | r1_tarski(o_0_0_xboole_0,k1_funct_1(o_0_0_xboole_0,sK1(k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top ),
% 0.36/1.04      inference(light_normalisation,[status(thm)],[c_3738,c_8]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_0,plain,
% 0.36/1.04      ( r1_tarski(o_0_0_xboole_0,X0) ),
% 0.36/1.04      inference(cnf_transformation,[],[f82]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_1378,plain,
% 0.36/1.04      ( r1_tarski(o_0_0_xboole_0,X0) = iProver_top ),
% 0.36/1.04      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_4078,plain,
% 0.36/1.04      ( k2_enumset1(sK2,sK2,sK2,sK2) = o_0_0_xboole_0 ),
% 0.36/1.04      inference(forward_subsumption_resolution,
% 0.36/1.04                [status(thm)],
% 0.36/1.04                [c_3769,c_1378]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_13,plain,
% 0.36/1.04      ( k1_relat_1(sK0(X0,X1)) = X0 ),
% 0.36/1.04      inference(cnf_transformation,[],[f64]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_2752,plain,
% 0.36/1.04      ( k2_enumset1(X0,X0,X0,X0) != X1
% 0.36/1.04      | k2_enumset1(k1_funct_1(sK0(X1,X2),X0),k1_funct_1(sK0(X1,X2),X0),k1_funct_1(sK0(X1,X2),X0),k1_funct_1(sK0(X1,X2),X0)) = k2_relat_1(sK0(X1,X2))
% 0.36/1.04      | v1_funct_1(sK0(X1,X2)) != iProver_top
% 0.36/1.04      | v1_relat_1(sK0(X1,X2)) != iProver_top ),
% 0.36/1.04      inference(superposition,[status(thm)],[c_13,c_1367]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_15,plain,
% 0.36/1.04      ( v1_relat_1(sK0(X0,X1)) ),
% 0.36/1.04      inference(cnf_transformation,[],[f62]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_1368,plain,
% 0.36/1.04      ( v1_relat_1(sK0(X0,X1)) = iProver_top ),
% 0.36/1.04      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_14,plain,
% 0.36/1.04      ( v1_funct_1(sK0(X0,X1)) ),
% 0.36/1.04      inference(cnf_transformation,[],[f63]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_1369,plain,
% 0.36/1.04      ( v1_funct_1(sK0(X0,X1)) = iProver_top ),
% 0.36/1.04      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_2805,plain,
% 0.36/1.04      ( k2_enumset1(X0,X0,X0,X0) != X1
% 0.36/1.04      | k2_enumset1(k1_funct_1(sK0(X1,X2),X0),k1_funct_1(sK0(X1,X2),X0),k1_funct_1(sK0(X1,X2),X0),k1_funct_1(sK0(X1,X2),X0)) = k2_relat_1(sK0(X1,X2)) ),
% 0.36/1.04      inference(forward_subsumption_resolution,
% 0.36/1.04                [status(thm)],
% 0.36/1.04                [c_2752,c_1368,c_1369]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_2807,plain,
% 0.36/1.04      ( k2_enumset1(k1_funct_1(sK0(k2_enumset1(X0,X0,X0,X0),X1),X0),k1_funct_1(sK0(k2_enumset1(X0,X0,X0,X0),X1),X0),k1_funct_1(sK0(k2_enumset1(X0,X0,X0,X0),X1),X0),k1_funct_1(sK0(k2_enumset1(X0,X0,X0,X0),X1),X0)) = k2_relat_1(sK0(k2_enumset1(X0,X0,X0,X0),X1)) ),
% 0.36/1.04      inference(equality_resolution,[status(thm)],[c_2805]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_4098,plain,
% 0.36/1.04      ( k2_enumset1(k1_funct_1(sK0(o_0_0_xboole_0,X0),sK2),k1_funct_1(sK0(o_0_0_xboole_0,X0),sK2),k1_funct_1(sK0(o_0_0_xboole_0,X0),sK2),k1_funct_1(sK0(o_0_0_xboole_0,X0),sK2)) = k2_relat_1(sK0(k2_enumset1(sK2,sK2,sK2,sK2),X0)) ),
% 0.36/1.04      inference(superposition,[status(thm)],[c_4078,c_2807]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_4123,plain,
% 0.36/1.04      ( k2_enumset1(k1_funct_1(sK0(o_0_0_xboole_0,X0),sK2),k1_funct_1(sK0(o_0_0_xboole_0,X0),sK2),k1_funct_1(sK0(o_0_0_xboole_0,X0),sK2),k1_funct_1(sK0(o_0_0_xboole_0,X0),sK2)) = k2_relat_1(sK0(o_0_0_xboole_0,X0)) ),
% 0.36/1.04      inference(light_normalisation,[status(thm)],[c_4098,c_4078]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_2197,plain,
% 0.36/1.04      ( sK0(X0,X1) = o_0_0_xboole_0
% 0.36/1.04      | o_0_0_xboole_0 != X0
% 0.36/1.04      | v1_relat_1(sK0(X0,X1)) != iProver_top ),
% 0.36/1.04      inference(superposition,[status(thm)],[c_13,c_1371]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_58,plain,
% 0.36/1.04      ( v1_relat_1(sK0(X0,X1)) = iProver_top ),
% 0.36/1.04      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_2259,plain,
% 0.36/1.04      ( o_0_0_xboole_0 != X0 | sK0(X0,X1) = o_0_0_xboole_0 ),
% 0.36/1.04      inference(global_propositional_subsumption,
% 0.36/1.04                [status(thm)],
% 0.36/1.04                [c_2197,c_58]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_2260,plain,
% 0.36/1.04      ( sK0(X0,X1) = o_0_0_xboole_0 | o_0_0_xboole_0 != X0 ),
% 0.36/1.04      inference(renaming,[status(thm)],[c_2259]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_2264,plain,
% 0.36/1.04      ( sK0(o_0_0_xboole_0,X0) = o_0_0_xboole_0 ),
% 0.36/1.04      inference(equality_resolution,[status(thm)],[c_2260]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_4125,plain,
% 0.36/1.04      ( k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK2),k1_funct_1(o_0_0_xboole_0,sK2),k1_funct_1(o_0_0_xboole_0,sK2),k1_funct_1(o_0_0_xboole_0,sK2)) = o_0_0_xboole_0 ),
% 0.36/1.04      inference(light_normalisation,[status(thm)],[c_4123,c_8,c_2264]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_3742,plain,
% 0.36/1.04      ( k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK2),k1_funct_1(o_0_0_xboole_0,sK2),k1_funct_1(o_0_0_xboole_0,sK2),k1_funct_1(o_0_0_xboole_0,sK2)) != k2_relat_1(o_0_0_xboole_0) ),
% 0.36/1.04      inference(demodulation,[status(thm)],[c_3733,c_1572]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_3755,plain,
% 0.36/1.04      ( k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK2),k1_funct_1(o_0_0_xboole_0,sK2),k1_funct_1(o_0_0_xboole_0,sK2),k1_funct_1(o_0_0_xboole_0,sK2)) != o_0_0_xboole_0 ),
% 0.36/1.04      inference(light_normalisation,[status(thm)],[c_3742,c_8]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(contradiction,plain,
% 0.36/1.04      ( $false ),
% 0.36/1.04      inference(minisat,[status(thm)],[c_4125,c_3755]) ).
% 0.36/1.04  
% 0.36/1.04  
% 0.36/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 0.36/1.04  
% 0.36/1.04  ------                               Statistics
% 0.36/1.04  
% 0.36/1.04  ------ General
% 0.36/1.04  
% 0.36/1.04  abstr_ref_over_cycles:                  0
% 0.36/1.04  abstr_ref_under_cycles:                 0
% 0.36/1.04  gc_basic_clause_elim:                   0
% 0.36/1.04  forced_gc_time:                         0
% 0.36/1.04  parsing_time:                           0.008
% 0.36/1.04  unif_index_cands_time:                  0.
% 0.36/1.04  unif_index_add_time:                    0.
% 0.36/1.04  orderings_time:                         0.
% 0.36/1.04  out_proof_time:                         0.009
% 0.36/1.04  total_time:                             0.137
% 0.36/1.04  num_of_symbols:                         52
% 0.36/1.04  num_of_terms:                           3516
% 0.36/1.04  
% 0.36/1.04  ------ Preprocessing
% 0.36/1.04  
% 0.36/1.04  num_of_splits:                          0
% 0.36/1.04  num_of_split_atoms:                     0
% 0.36/1.04  num_of_reused_defs:                     0
% 0.36/1.04  num_eq_ax_congr_red:                    20
% 0.36/1.04  num_of_sem_filtered_clauses:            1
% 0.36/1.04  num_of_subtypes:                        0
% 0.36/1.04  monotx_restored_types:                  0
% 0.36/1.04  sat_num_of_epr_types:                   0
% 0.36/1.04  sat_num_of_non_cyclic_types:            0
% 0.36/1.04  sat_guarded_non_collapsed_types:        0
% 0.36/1.04  num_pure_diseq_elim:                    0
% 0.36/1.04  simp_replaced_by:                       0
% 0.36/1.04  res_preprocessed:                       135
% 0.36/1.04  prep_upred:                             0
% 0.36/1.04  prep_unflattend:                        64
% 0.36/1.04  smt_new_axioms:                         0
% 0.36/1.04  pred_elim_cands:                        4
% 0.36/1.04  pred_elim:                              3
% 0.36/1.04  pred_elim_cl:                           4
% 0.36/1.04  pred_elim_cycles:                       9
% 0.36/1.04  merged_defs:                            0
% 0.36/1.04  merged_defs_ncl:                        0
% 0.36/1.04  bin_hyper_res:                          0
% 0.36/1.04  prep_cycles:                            4
% 0.36/1.04  pred_elim_time:                         0.009
% 0.36/1.04  splitting_time:                         0.
% 0.36/1.04  sem_filter_time:                        0.
% 0.36/1.04  monotx_time:                            0.
% 0.36/1.04  subtype_inf_time:                       0.
% 0.36/1.04  
% 0.36/1.04  ------ Problem properties
% 0.36/1.04  
% 0.36/1.04  clauses:                                26
% 0.36/1.04  conjectures:                            3
% 0.36/1.04  epr:                                    4
% 0.36/1.04  horn:                                   24
% 0.36/1.04  ground:                                 5
% 0.36/1.04  unary:                                  13
% 0.36/1.04  binary:                                 7
% 0.36/1.04  lits:                                   48
% 0.36/1.04  lits_eq:                                25
% 0.36/1.04  fd_pure:                                0
% 0.36/1.04  fd_pseudo:                              0
% 0.36/1.04  fd_cond:                                5
% 0.36/1.04  fd_pseudo_cond:                         1
% 0.36/1.04  ac_symbols:                             0
% 0.36/1.04  
% 0.36/1.04  ------ Propositional Solver
% 0.36/1.04  
% 0.36/1.04  prop_solver_calls:                      28
% 0.36/1.04  prop_fast_solver_calls:                 840
% 0.36/1.04  smt_solver_calls:                       0
% 0.36/1.04  smt_fast_solver_calls:                  0
% 0.36/1.04  prop_num_of_clauses:                    1411
% 0.36/1.04  prop_preprocess_simplified:             5361
% 0.36/1.04  prop_fo_subsumed:                       18
% 0.36/1.04  prop_solver_time:                       0.
% 0.36/1.04  smt_solver_time:                        0.
% 0.36/1.04  smt_fast_solver_time:                   0.
% 0.36/1.04  prop_fast_solver_time:                  0.
% 0.36/1.04  prop_unsat_core_time:                   0.
% 0.36/1.04  
% 0.36/1.04  ------ QBF
% 0.36/1.04  
% 0.36/1.04  qbf_q_res:                              0
% 0.36/1.04  qbf_num_tautologies:                    0
% 0.36/1.04  qbf_prep_cycles:                        0
% 0.36/1.04  
% 0.36/1.04  ------ BMC1
% 0.36/1.04  
% 0.36/1.04  bmc1_current_bound:                     -1
% 0.36/1.04  bmc1_last_solved_bound:                 -1
% 0.36/1.04  bmc1_unsat_core_size:                   -1
% 0.36/1.04  bmc1_unsat_core_parents_size:           -1
% 0.36/1.04  bmc1_merge_next_fun:                    0
% 0.36/1.04  bmc1_unsat_core_clauses_time:           0.
% 0.36/1.04  
% 0.36/1.04  ------ Instantiation
% 0.36/1.04  
% 0.36/1.04  inst_num_of_clauses:                    540
% 0.36/1.04  inst_num_in_passive:                    59
% 0.36/1.04  inst_num_in_active:                     271
% 0.36/1.04  inst_num_in_unprocessed:                211
% 0.36/1.04  inst_num_of_loops:                      320
% 0.36/1.04  inst_num_of_learning_restarts:          0
% 0.36/1.04  inst_num_moves_active_passive:          46
% 0.36/1.04  inst_lit_activity:                      0
% 0.36/1.04  inst_lit_activity_moves:                0
% 0.36/1.04  inst_num_tautologies:                   0
% 0.36/1.04  inst_num_prop_implied:                  0
% 0.36/1.04  inst_num_existing_simplified:           0
% 0.36/1.04  inst_num_eq_res_simplified:             0
% 0.36/1.04  inst_num_child_elim:                    0
% 0.36/1.04  inst_num_of_dismatching_blockings:      70
% 0.36/1.04  inst_num_of_non_proper_insts:           397
% 0.36/1.04  inst_num_of_duplicates:                 0
% 0.36/1.04  inst_inst_num_from_inst_to_res:         0
% 0.36/1.04  inst_dismatching_checking_time:         0.
% 0.36/1.04  
% 0.36/1.04  ------ Resolution
% 0.36/1.04  
% 0.36/1.04  res_num_of_clauses:                     0
% 0.36/1.04  res_num_in_passive:                     0
% 0.36/1.04  res_num_in_active:                      0
% 0.36/1.04  res_num_of_loops:                       139
% 0.36/1.04  res_forward_subset_subsumed:            71
% 0.36/1.04  res_backward_subset_subsumed:           4
% 0.36/1.04  res_forward_subsumed:                   2
% 0.36/1.04  res_backward_subsumed:                  0
% 0.36/1.04  res_forward_subsumption_resolution:     0
% 0.36/1.04  res_backward_subsumption_resolution:    0
% 0.36/1.04  res_clause_to_clause_subsumption:       142
% 0.36/1.04  res_orphan_elimination:                 0
% 0.36/1.04  res_tautology_del:                      69
% 0.36/1.04  res_num_eq_res_simplified:              0
% 0.36/1.04  res_num_sel_changes:                    0
% 0.36/1.04  res_moves_from_active_to_pass:          0
% 0.36/1.04  
% 0.36/1.04  ------ Superposition
% 0.36/1.04  
% 0.36/1.04  sup_time_total:                         0.
% 0.36/1.04  sup_time_generating:                    0.
% 0.36/1.04  sup_time_sim_full:                      0.
% 0.36/1.04  sup_time_sim_immed:                     0.
% 0.36/1.04  
% 0.36/1.04  sup_num_of_clauses:                     42
% 0.36/1.04  sup_num_in_active:                      30
% 0.36/1.04  sup_num_in_passive:                     12
% 0.36/1.04  sup_num_of_loops:                       63
% 0.36/1.04  sup_fw_superposition:                   24
% 0.36/1.04  sup_bw_superposition:                   60
% 0.36/1.04  sup_immediate_simplified:               18
% 0.36/1.04  sup_given_eliminated:                   0
% 0.36/1.04  comparisons_done:                       0
% 0.36/1.04  comparisons_avoided:                    16
% 0.36/1.04  
% 0.36/1.04  ------ Simplifications
% 0.36/1.04  
% 0.36/1.04  
% 0.36/1.04  sim_fw_subset_subsumed:                 5
% 0.36/1.04  sim_bw_subset_subsumed:                 9
% 0.36/1.04  sim_fw_subsumed:                        5
% 0.36/1.04  sim_bw_subsumed:                        0
% 0.36/1.04  sim_fw_subsumption_res:                 3
% 0.36/1.04  sim_bw_subsumption_res:                 0
% 0.36/1.04  sim_tautology_del:                      0
% 0.36/1.04  sim_eq_tautology_del:                   20
% 0.36/1.04  sim_eq_res_simp:                        0
% 0.36/1.04  sim_fw_demodulated:                     2
% 0.36/1.04  sim_bw_demodulated:                     27
% 0.36/1.04  sim_light_normalised:                   14
% 0.36/1.04  sim_joinable_taut:                      0
% 0.36/1.04  sim_joinable_simp:                      0
% 0.36/1.04  sim_ac_normalised:                      0
% 0.36/1.04  sim_smt_subsumption:                    0
% 0.36/1.04  
%------------------------------------------------------------------------------
