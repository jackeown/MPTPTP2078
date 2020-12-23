%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:41:37 EST 2020

% Result     : Theorem 7.47s
% Output     : CNFRefutation 7.47s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 142 expanded)
%              Number of clauses        :   34 (  35 expanded)
%              Number of leaves         :   16 (  33 expanded)
%              Depth                    :   12
%              Number of atoms          :  285 ( 570 expanded)
%              Number of equality atoms :  127 ( 319 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f20])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ( ~ r1_tarski(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f41])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X1,sK2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK1(X0,X1,X2) != X1
            & sK1(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( sK1(X0,X1,X2) = X1
          | sK1(X0,X1,X2) = X0
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK1(X0,X1,X2) != X1
              & sK1(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( sK1(X0,X1,X2) = X1
            | sK1(X0,X1,X2) = X0
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f61,f62])).

fof(f84,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f54,f77])).

fof(f101,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f84])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_tarski(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f56,f77])).

fof(f97,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f82])).

fof(f98,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_enumset1(X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f97])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f96,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f83,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f55,f77])).

fof(f99,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f83])).

fof(f100,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f99])).

fof(f15,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f15])).

fof(f24,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f16])).

fof(f43,plain,
    ( ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0
   => k1_setfam_1(k1_tarski(sK3)) != sK3 ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    k1_setfam_1(k1_tarski(sK3)) != sK3 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f43])).

fof(f76,plain,(
    k1_setfam_1(k1_tarski(sK3)) != sK3 ),
    inference(cnf_transformation,[],[f44])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f78,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f60,f77])).

fof(f91,plain,(
    k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3)) != sK3 ),
    inference(definition_unfolding,[],[f76,f78])).

cnf(c_507,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_17908,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,sK2(k2_enumset1(X3,X3,X3,X4),X2))
    | X2 != X0
    | sK2(k2_enumset1(X3,X3,X3,X4),X2) != X1 ),
    inference(instantiation,[status(thm)],[c_507])).

cnf(c_17910,plain,
    ( r1_tarski(sK3,sK2(k2_enumset1(sK3,sK3,sK3,sK3),sK3))
    | ~ r1_tarski(sK3,sK3)
    | sK2(k2_enumset1(sK3,sK3,sK3,sK3),sK3) != sK3
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_17908])).

cnf(c_25,plain,
    ( ~ r1_tarski(X0,sK2(X1,X0))
    | r1_tarski(X0,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_17822,plain,
    ( ~ r1_tarski(X0,sK2(k2_enumset1(X1,X1,X1,X2),X0))
    | r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
    | k1_xboole_0 = k2_enumset1(X1,X1,X1,X2) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_17829,plain,
    ( ~ r1_tarski(sK3,sK2(k2_enumset1(sK3,sK3,sK3,sK3),sK3))
    | r1_tarski(sK3,k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3)))
    | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_17822])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_26,plain,
    ( r1_tarski(X0,k1_setfam_1(X1))
    | r2_hidden(sK2(X1,X0),X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_17804,plain,
    ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
    | sK2(k2_enumset1(X1,X1,X1,X2),X0) = X1
    | sK2(k2_enumset1(X1,X1,X1,X2),X0) = X2
    | k1_xboole_0 = k2_enumset1(X1,X1,X1,X2) ),
    inference(resolution,[status(thm)],[c_14,c_26])).

cnf(c_17806,plain,
    ( r1_tarski(sK3,k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3)))
    | sK2(k2_enumset1(sK3,sK3,sK3,sK3),sK3) = sK3
    | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_17804])).

cnf(c_21,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_15909,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3))))) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_24,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_10047,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3)))))
    | m1_subset_1(sK3,k1_zfmisc_1(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3))))
    | ~ r2_hidden(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_10077,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3)))))
    | ~ r2_hidden(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_10047])).

cnf(c_506,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_7571,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k2_enumset1(X3,X3,X3,X2))
    | X0 != X2
    | X1 != k2_enumset1(X3,X3,X3,X2) ),
    inference(instantiation,[status(thm)],[c_506])).

cnf(c_7617,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X0))
    | r2_hidden(X2,k1_xboole_0)
    | X2 != X0
    | k1_xboole_0 != k2_enumset1(X1,X1,X1,X0) ),
    inference(instantiation,[status(thm)],[c_7571])).

cnf(c_7619,plain,
    ( ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3))
    | r2_hidden(sK3,k1_xboole_0)
    | sK3 != sK3
    | k1_xboole_0 != k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_7617])).

cnf(c_27,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(X2),X1)
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_12,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_7225,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(k2_enumset1(X2,X2,X2,X0)),X1) ),
    inference(resolution,[status(thm)],[c_27,c_12])).

cnf(c_7227,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3)),sK3)
    | ~ r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_7225])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2976,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3))))
    | r1_tarski(sK3,k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3))) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2973,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3)),sK3)
    | ~ r1_tarski(sK3,k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3)))
    | k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_8,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_83,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_13,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_72,plain,
    ( r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_69,plain,
    ( ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3))
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_28,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3)) != sK3 ),
    inference(cnf_transformation,[],[f91])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17910,c_17829,c_17806,c_15909,c_10077,c_7619,c_7227,c_2976,c_2973,c_83,c_72,c_69,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:41:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.47/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.47/1.49  
% 7.47/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.47/1.49  
% 7.47/1.49  ------  iProver source info
% 7.47/1.49  
% 7.47/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.47/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.47/1.49  git: non_committed_changes: false
% 7.47/1.49  git: last_make_outside_of_git: false
% 7.47/1.49  
% 7.47/1.49  ------ 
% 7.47/1.49  ------ Parsing...
% 7.47/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.47/1.49  
% 7.47/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.47/1.49  
% 7.47/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.47/1.49  
% 7.47/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.47/1.49  ------ Proving...
% 7.47/1.49  ------ Problem Properties 
% 7.47/1.49  
% 7.47/1.49  
% 7.47/1.49  clauses                                 28
% 7.47/1.49  conjectures                             1
% 7.47/1.49  EPR                                     2
% 7.47/1.49  Horn                                    19
% 7.47/1.49  unary                                   6
% 7.47/1.49  binary                                  8
% 7.47/1.49  lits                                    66
% 7.47/1.49  lits eq                                 18
% 7.47/1.49  fd_pure                                 0
% 7.47/1.49  fd_pseudo                               0
% 7.47/1.49  fd_cond                                 2
% 7.47/1.49  fd_pseudo_cond                          9
% 7.47/1.49  AC symbols                              0
% 7.47/1.49  
% 7.47/1.49  ------ Input Options Time Limit: Unbounded
% 7.47/1.49  
% 7.47/1.49  
% 7.47/1.49  
% 7.47/1.49  
% 7.47/1.49  ------ Preprocessing...
% 7.47/1.49  
% 7.47/1.49  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 7.47/1.49  Current options:
% 7.47/1.49  ------ 
% 7.47/1.49  
% 7.47/1.49  
% 7.47/1.49  
% 7.47/1.49  
% 7.47/1.49  ------ Proving...
% 7.47/1.49  
% 7.47/1.49  
% 7.47/1.49  ------ Preprocessing...
% 7.47/1.49  
% 7.47/1.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.47/1.49  
% 7.47/1.49  ------ Proving...
% 7.47/1.49  
% 7.47/1.49  
% 7.47/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.47/1.49  
% 7.47/1.49  ------ Proving...
% 7.47/1.49  
% 7.47/1.49  
% 7.47/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.47/1.49  
% 7.47/1.49  ------ Proving...
% 7.47/1.49  
% 7.47/1.49  
% 7.47/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.47/1.49  
% 7.47/1.49  ------ Proving...
% 7.47/1.49  
% 7.47/1.49  
% 7.47/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.47/1.49  
% 7.47/1.49  ------ Proving...
% 7.47/1.49  
% 7.47/1.49  
% 7.47/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.47/1.49  
% 7.47/1.49  ------ Proving...
% 7.47/1.49  
% 7.47/1.49  
% 7.47/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.47/1.49  
% 7.47/1.49  ------ Proving...
% 7.47/1.49  
% 7.47/1.49  
% 7.47/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.47/1.49  
% 7.47/1.49  ------ Proving...
% 7.47/1.49  
% 7.47/1.49  
% 7.47/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.47/1.49  
% 7.47/1.49  ------ Proving...
% 7.47/1.49  
% 7.47/1.49  
% 7.47/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.47/1.49  
% 7.47/1.49  ------ Proving...
% 7.47/1.49  
% 7.47/1.49  
% 7.47/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.47/1.49  
% 7.47/1.49  ------ Proving...
% 7.47/1.49  
% 7.47/1.49  
% 7.47/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.47/1.49  
% 7.47/1.49  ------ Proving...
% 7.47/1.49  
% 7.47/1.49  
% 7.47/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.47/1.49  
% 7.47/1.49  ------ Proving...
% 7.47/1.49  
% 7.47/1.49  
% 7.47/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.47/1.49  
% 7.47/1.49  ------ Proving...
% 7.47/1.49  
% 7.47/1.49  
% 7.47/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.47/1.49  
% 7.47/1.49  ------ Proving...
% 7.47/1.49  
% 7.47/1.49  
% 7.47/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.47/1.49  
% 7.47/1.49  ------ Proving...
% 7.47/1.49  
% 7.47/1.49  
% 7.47/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.47/1.49  
% 7.47/1.49  ------ Proving...
% 7.47/1.49  
% 7.47/1.49  
% 7.47/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.47/1.49  
% 7.47/1.49  ------ Proving...
% 7.47/1.49  
% 7.47/1.49  
% 7.47/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.47/1.49  
% 7.47/1.49  ------ Proving...
% 7.47/1.49  
% 7.47/1.49  
% 7.47/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.47/1.49  
% 7.47/1.49  ------ Proving...
% 7.47/1.49  
% 7.47/1.49  
% 7.47/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.47/1.49  
% 7.47/1.49  ------ Proving...
% 7.47/1.49  
% 7.47/1.49  
% 7.47/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.47/1.49  
% 7.47/1.49  ------ Proving...
% 7.47/1.49  
% 7.47/1.49  
% 7.47/1.49  % SZS status Theorem for theBenchmark.p
% 7.47/1.49  
% 7.47/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.47/1.49  
% 7.47/1.49  fof(f13,axiom,(
% 7.47/1.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 7.47/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.47/1.49  
% 7.47/1.49  fof(f20,plain,(
% 7.47/1.49    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 7.47/1.49    inference(ennf_transformation,[],[f13])).
% 7.47/1.49  
% 7.47/1.49  fof(f21,plain,(
% 7.47/1.49    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 7.47/1.49    inference(flattening,[],[f20])).
% 7.47/1.49  
% 7.47/1.49  fof(f41,plain,(
% 7.47/1.49    ! [X1,X0] : (? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)) => (~r1_tarski(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 7.47/1.49    introduced(choice_axiom,[])).
% 7.47/1.49  
% 7.47/1.49  fof(f42,plain,(
% 7.47/1.49    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | (~r1_tarski(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 7.47/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f41])).
% 7.47/1.49  
% 7.47/1.49  fof(f74,plain,(
% 7.47/1.49    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X1,sK2(X0,X1))) )),
% 7.47/1.49    inference(cnf_transformation,[],[f42])).
% 7.47/1.49  
% 7.47/1.49  fof(f3,axiom,(
% 7.47/1.49    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 7.47/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.47/1.49  
% 7.47/1.49  fof(f32,plain,(
% 7.47/1.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.47/1.49    inference(nnf_transformation,[],[f3])).
% 7.47/1.49  
% 7.47/1.49  fof(f33,plain,(
% 7.47/1.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.47/1.49    inference(flattening,[],[f32])).
% 7.47/1.49  
% 7.47/1.49  fof(f34,plain,(
% 7.47/1.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.47/1.49    inference(rectify,[],[f33])).
% 7.47/1.49  
% 7.47/1.49  fof(f35,plain,(
% 7.47/1.49    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2))))),
% 7.47/1.49    introduced(choice_axiom,[])).
% 7.47/1.49  
% 7.47/1.49  fof(f36,plain,(
% 7.47/1.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.47/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).
% 7.47/1.49  
% 7.47/1.49  fof(f54,plain,(
% 7.47/1.49    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 7.47/1.49    inference(cnf_transformation,[],[f36])).
% 7.47/1.49  
% 7.47/1.49  fof(f5,axiom,(
% 7.47/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.47/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.47/1.49  
% 7.47/1.49  fof(f61,plain,(
% 7.47/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.47/1.49    inference(cnf_transformation,[],[f5])).
% 7.47/1.49  
% 7.47/1.49  fof(f6,axiom,(
% 7.47/1.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.47/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.47/1.49  
% 7.47/1.49  fof(f62,plain,(
% 7.47/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.47/1.49    inference(cnf_transformation,[],[f6])).
% 7.47/1.49  
% 7.47/1.49  fof(f77,plain,(
% 7.47/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 7.47/1.49    inference(definition_unfolding,[],[f61,f62])).
% 7.47/1.49  
% 7.47/1.49  fof(f84,plain,(
% 7.47/1.49    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 7.47/1.49    inference(definition_unfolding,[],[f54,f77])).
% 7.47/1.49  
% 7.47/1.49  fof(f101,plain,(
% 7.47/1.49    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))) )),
% 7.47/1.49    inference(equality_resolution,[],[f84])).
% 7.47/1.49  
% 7.47/1.49  fof(f73,plain,(
% 7.47/1.49    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | r2_hidden(sK2(X0,X1),X0)) )),
% 7.47/1.49    inference(cnf_transformation,[],[f42])).
% 7.47/1.49  
% 7.47/1.49  fof(f10,axiom,(
% 7.47/1.49    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 7.47/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.47/1.49  
% 7.47/1.49  fof(f69,plain,(
% 7.47/1.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 7.47/1.49    inference(cnf_transformation,[],[f10])).
% 7.47/1.49  
% 7.47/1.49  fof(f12,axiom,(
% 7.47/1.49    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 7.47/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.47/1.49  
% 7.47/1.49  fof(f18,plain,(
% 7.47/1.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 7.47/1.49    inference(ennf_transformation,[],[f12])).
% 7.47/1.49  
% 7.47/1.49  fof(f19,plain,(
% 7.47/1.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.47/1.49    inference(flattening,[],[f18])).
% 7.47/1.49  
% 7.47/1.49  fof(f72,plain,(
% 7.47/1.49    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.47/1.49    inference(cnf_transformation,[],[f19])).
% 7.47/1.49  
% 7.47/1.49  fof(f14,axiom,(
% 7.47/1.49    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r2_hidden(X0,X1)) => r1_tarski(k1_setfam_1(X1),X2))),
% 7.47/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.47/1.49  
% 7.47/1.49  fof(f22,plain,(
% 7.47/1.49    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | (~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)))),
% 7.47/1.49    inference(ennf_transformation,[],[f14])).
% 7.47/1.49  
% 7.47/1.49  fof(f23,plain,(
% 7.47/1.49    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1))),
% 7.47/1.49    inference(flattening,[],[f22])).
% 7.47/1.49  
% 7.47/1.49  fof(f75,plain,(
% 7.47/1.49    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)) )),
% 7.47/1.49    inference(cnf_transformation,[],[f23])).
% 7.47/1.49  
% 7.47/1.49  fof(f56,plain,(
% 7.47/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 7.47/1.49    inference(cnf_transformation,[],[f36])).
% 7.47/1.49  
% 7.47/1.49  fof(f82,plain,(
% 7.47/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 7.47/1.49    inference(definition_unfolding,[],[f56,f77])).
% 7.47/1.49  
% 7.47/1.49  fof(f97,plain,(
% 7.47/1.49    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X4) != X2) )),
% 7.47/1.49    inference(equality_resolution,[],[f82])).
% 7.47/1.49  
% 7.47/1.49  fof(f98,plain,(
% 7.47/1.49    ( ! [X4,X0] : (r2_hidden(X4,k2_enumset1(X0,X0,X0,X4))) )),
% 7.47/1.49    inference(equality_resolution,[],[f97])).
% 7.47/1.49  
% 7.47/1.49  fof(f11,axiom,(
% 7.47/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.47/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.47/1.49  
% 7.47/1.49  fof(f40,plain,(
% 7.47/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.47/1.49    inference(nnf_transformation,[],[f11])).
% 7.47/1.49  
% 7.47/1.49  fof(f70,plain,(
% 7.47/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.47/1.49    inference(cnf_transformation,[],[f40])).
% 7.47/1.49  
% 7.47/1.49  fof(f2,axiom,(
% 7.47/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.47/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.47/1.49  
% 7.47/1.49  fof(f30,plain,(
% 7.47/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.47/1.49    inference(nnf_transformation,[],[f2])).
% 7.47/1.49  
% 7.47/1.49  fof(f31,plain,(
% 7.47/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.47/1.49    inference(flattening,[],[f30])).
% 7.47/1.49  
% 7.47/1.49  fof(f53,plain,(
% 7.47/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.47/1.49    inference(cnf_transformation,[],[f31])).
% 7.47/1.49  
% 7.47/1.49  fof(f51,plain,(
% 7.47/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.47/1.49    inference(cnf_transformation,[],[f31])).
% 7.47/1.49  
% 7.47/1.49  fof(f96,plain,(
% 7.47/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.47/1.49    inference(equality_resolution,[],[f51])).
% 7.47/1.49  
% 7.47/1.49  fof(f55,plain,(
% 7.47/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 7.47/1.49    inference(cnf_transformation,[],[f36])).
% 7.47/1.49  
% 7.47/1.49  fof(f83,plain,(
% 7.47/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 7.47/1.49    inference(definition_unfolding,[],[f55,f77])).
% 7.47/1.49  
% 7.47/1.49  fof(f99,plain,(
% 7.47/1.49    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 7.47/1.49    inference(equality_resolution,[],[f83])).
% 7.47/1.49  
% 7.47/1.49  fof(f100,plain,(
% 7.47/1.49    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 7.47/1.49    inference(equality_resolution,[],[f99])).
% 7.47/1.49  
% 7.47/1.49  fof(f15,conjecture,(
% 7.47/1.49    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 7.47/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.47/1.49  
% 7.47/1.49  fof(f16,negated_conjecture,(
% 7.47/1.49    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 7.47/1.49    inference(negated_conjecture,[],[f15])).
% 7.47/1.49  
% 7.47/1.49  fof(f24,plain,(
% 7.47/1.49    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 7.47/1.49    inference(ennf_transformation,[],[f16])).
% 7.47/1.49  
% 7.47/1.49  fof(f43,plain,(
% 7.47/1.49    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 => k1_setfam_1(k1_tarski(sK3)) != sK3),
% 7.47/1.49    introduced(choice_axiom,[])).
% 7.47/1.49  
% 7.47/1.49  fof(f44,plain,(
% 7.47/1.49    k1_setfam_1(k1_tarski(sK3)) != sK3),
% 7.47/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f43])).
% 7.47/1.49  
% 7.47/1.49  fof(f76,plain,(
% 7.47/1.49    k1_setfam_1(k1_tarski(sK3)) != sK3),
% 7.47/1.49    inference(cnf_transformation,[],[f44])).
% 7.47/1.49  
% 7.47/1.49  fof(f4,axiom,(
% 7.47/1.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.47/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.47/1.49  
% 7.47/1.49  fof(f60,plain,(
% 7.47/1.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.47/1.49    inference(cnf_transformation,[],[f4])).
% 7.47/1.49  
% 7.47/1.49  fof(f78,plain,(
% 7.47/1.49    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 7.47/1.49    inference(definition_unfolding,[],[f60,f77])).
% 7.47/1.49  
% 7.47/1.49  fof(f91,plain,(
% 7.47/1.49    k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3)) != sK3),
% 7.47/1.49    inference(definition_unfolding,[],[f76,f78])).
% 7.47/1.49  
% 7.47/1.49  cnf(c_507,plain,
% 7.47/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.47/1.49      theory(equality) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_17908,plain,
% 7.47/1.49      ( ~ r1_tarski(X0,X1)
% 7.47/1.49      | r1_tarski(X2,sK2(k2_enumset1(X3,X3,X3,X4),X2))
% 7.47/1.49      | X2 != X0
% 7.47/1.49      | sK2(k2_enumset1(X3,X3,X3,X4),X2) != X1 ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_507]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_17910,plain,
% 7.47/1.49      ( r1_tarski(sK3,sK2(k2_enumset1(sK3,sK3,sK3,sK3),sK3))
% 7.47/1.49      | ~ r1_tarski(sK3,sK3)
% 7.47/1.49      | sK2(k2_enumset1(sK3,sK3,sK3,sK3),sK3) != sK3
% 7.47/1.49      | sK3 != sK3 ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_17908]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_25,plain,
% 7.47/1.49      ( ~ r1_tarski(X0,sK2(X1,X0))
% 7.47/1.49      | r1_tarski(X0,k1_setfam_1(X1))
% 7.47/1.49      | k1_xboole_0 = X1 ),
% 7.47/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_17822,plain,
% 7.47/1.49      ( ~ r1_tarski(X0,sK2(k2_enumset1(X1,X1,X1,X2),X0))
% 7.47/1.49      | r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
% 7.47/1.49      | k1_xboole_0 = k2_enumset1(X1,X1,X1,X2) ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_25]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_17829,plain,
% 7.47/1.49      ( ~ r1_tarski(sK3,sK2(k2_enumset1(sK3,sK3,sK3,sK3),sK3))
% 7.47/1.49      | r1_tarski(sK3,k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3)))
% 7.47/1.49      | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_17822]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_14,plain,
% 7.47/1.49      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 7.47/1.49      inference(cnf_transformation,[],[f101]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_26,plain,
% 7.47/1.49      ( r1_tarski(X0,k1_setfam_1(X1))
% 7.47/1.49      | r2_hidden(sK2(X1,X0),X1)
% 7.47/1.49      | k1_xboole_0 = X1 ),
% 7.47/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_17804,plain,
% 7.47/1.49      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
% 7.47/1.49      | sK2(k2_enumset1(X1,X1,X1,X2),X0) = X1
% 7.47/1.49      | sK2(k2_enumset1(X1,X1,X1,X2),X0) = X2
% 7.47/1.49      | k1_xboole_0 = k2_enumset1(X1,X1,X1,X2) ),
% 7.47/1.49      inference(resolution,[status(thm)],[c_14,c_26]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_17806,plain,
% 7.47/1.49      ( r1_tarski(sK3,k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3)))
% 7.47/1.49      | sK2(k2_enumset1(sK3,sK3,sK3,sK3),sK3) = sK3
% 7.47/1.49      | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_17804]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_21,plain,
% 7.47/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 7.47/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_15909,plain,
% 7.47/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3))))) ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_21]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_24,plain,
% 7.47/1.49      ( m1_subset_1(X0,X1)
% 7.47/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.47/1.49      | ~ r2_hidden(X0,X2) ),
% 7.47/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_10047,plain,
% 7.47/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3)))))
% 7.47/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3))))
% 7.47/1.49      | ~ r2_hidden(sK3,X0) ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_24]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_10077,plain,
% 7.47/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3))))
% 7.47/1.49      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3)))))
% 7.47/1.49      | ~ r2_hidden(sK3,k1_xboole_0) ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_10047]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_506,plain,
% 7.47/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.47/1.49      theory(equality) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_7571,plain,
% 7.47/1.49      ( r2_hidden(X0,X1)
% 7.47/1.49      | ~ r2_hidden(X2,k2_enumset1(X3,X3,X3,X2))
% 7.47/1.49      | X0 != X2
% 7.47/1.49      | X1 != k2_enumset1(X3,X3,X3,X2) ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_506]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_7617,plain,
% 7.47/1.49      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X0))
% 7.47/1.49      | r2_hidden(X2,k1_xboole_0)
% 7.47/1.49      | X2 != X0
% 7.47/1.49      | k1_xboole_0 != k2_enumset1(X1,X1,X1,X0) ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_7571]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_7619,plain,
% 7.47/1.49      ( ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3))
% 7.47/1.49      | r2_hidden(sK3,k1_xboole_0)
% 7.47/1.49      | sK3 != sK3
% 7.47/1.49      | k1_xboole_0 != k2_enumset1(sK3,sK3,sK3,sK3) ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_7617]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_27,plain,
% 7.47/1.49      ( ~ r1_tarski(X0,X1)
% 7.47/1.49      | r1_tarski(k1_setfam_1(X2),X1)
% 7.47/1.49      | ~ r2_hidden(X0,X2) ),
% 7.47/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_12,plain,
% 7.47/1.49      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
% 7.47/1.49      inference(cnf_transformation,[],[f98]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_7225,plain,
% 7.47/1.49      ( ~ r1_tarski(X0,X1)
% 7.47/1.49      | r1_tarski(k1_setfam_1(k2_enumset1(X2,X2,X2,X0)),X1) ),
% 7.47/1.49      inference(resolution,[status(thm)],[c_27,c_12]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_7227,plain,
% 7.47/1.49      ( r1_tarski(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3)),sK3)
% 7.47/1.49      | ~ r1_tarski(sK3,sK3) ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_7225]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_23,plain,
% 7.47/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.47/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2976,plain,
% 7.47/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3))))
% 7.47/1.49      | r1_tarski(sK3,k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3))) ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_23]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_6,plain,
% 7.47/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.47/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_2973,plain,
% 7.47/1.49      ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3)),sK3)
% 7.47/1.49      | ~ r1_tarski(sK3,k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3)))
% 7.47/1.49      | k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3)) = sK3 ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_6]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_8,plain,
% 7.47/1.49      ( r1_tarski(X0,X0) ),
% 7.47/1.49      inference(cnf_transformation,[],[f96]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_83,plain,
% 7.47/1.49      ( r1_tarski(sK3,sK3) ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_8]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_13,plain,
% 7.47/1.49      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
% 7.47/1.49      inference(cnf_transformation,[],[f100]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_72,plain,
% 7.47/1.49      ( r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_13]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_69,plain,
% 7.47/1.49      ( ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) | sK3 = sK3 ),
% 7.47/1.49      inference(instantiation,[status(thm)],[c_14]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(c_28,negated_conjecture,
% 7.47/1.49      ( k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3)) != sK3 ),
% 7.47/1.49      inference(cnf_transformation,[],[f91]) ).
% 7.47/1.49  
% 7.47/1.49  cnf(contradiction,plain,
% 7.47/1.49      ( $false ),
% 7.47/1.49      inference(minisat,
% 7.47/1.49                [status(thm)],
% 7.47/1.49                [c_17910,c_17829,c_17806,c_15909,c_10077,c_7619,c_7227,
% 7.47/1.49                 c_2976,c_2973,c_83,c_72,c_69,c_28]) ).
% 7.47/1.49  
% 7.47/1.49  
% 7.47/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.47/1.49  
% 7.47/1.49  ------                               Statistics
% 7.47/1.49  
% 7.47/1.49  ------ Selected
% 7.47/1.49  
% 7.47/1.49  total_time:                             0.584
% 7.47/1.49  
%------------------------------------------------------------------------------
