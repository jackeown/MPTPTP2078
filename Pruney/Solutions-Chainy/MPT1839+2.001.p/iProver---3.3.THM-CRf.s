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
% DateTime   : Thu Dec  3 12:24:41 EST 2020

% Result     : Theorem 23.79s
% Output     : CNFRefutation 23.79s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 145 expanded)
%              Number of clauses        :   46 (  49 expanded)
%              Number of leaves         :   18 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :  271 ( 481 expanded)
%              Number of equality atoms :   49 (  57 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f57])).

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f58,f59])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f29,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f134,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f18,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK5(X0))
        & m1_subset_1(sK5(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X0] :
      ( v1_xboole_0(sK5(X0))
      & m1_subset_1(sK5(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f18,f70])).

fof(f116,plain,(
    ! [X0] : v1_xboole_0(sK5(X0)) ),
    inference(cnf_transformation,[],[f71])).

fof(f3,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK2) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f3,f61])).

fof(f93,plain,(
    v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f115,plain,(
    ! [X0] : m1_subset_1(sK5(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f71])).

fof(f19,axiom,(
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
    inference(nnf_transformation,[],[f19])).

fof(f117,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X3,X2)
              & r1_tarski(X3,X1) )
           => r1_tarski(X3,X0) )
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X1,X2) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f67,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
     => ( ~ r1_tarski(sK4(X0,X1,X2),X0)
        & r1_tarski(sK4(X0,X1,X2),X2)
        & r1_tarski(sK4(X0,X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ( ~ r1_tarski(sK4(X0,X1,X2),X0)
        & r1_tarski(sK4(X0,X1,X2),X2)
        & r1_tarski(sK4(X0,X1,X2),X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f67])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = X0
      | ~ r1_tarski(sK4(X0,X1,X2),X0)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = X0
      | r1_tarski(sK4(X0,X1,X2),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = X0
      | r1_tarski(sK4(X0,X1,X2),X1)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f30,conjecture,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
         => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_zfmisc_1(X0)
          & ~ v1_xboole_0(X0) )
       => ! [X1] :
            ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
           => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f30])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f86,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
     => ( ~ r1_tarski(X0,sK12)
        & ~ v1_xboole_0(k3_xboole_0(X0,sK12)) ) ) ),
    introduced(choice_axiom,[])).

fof(f85,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(X0,X1)
            & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
        & v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(sK11,X1)
          & ~ v1_xboole_0(k3_xboole_0(sK11,X1)) )
      & v1_zfmisc_1(sK11)
      & ~ v1_xboole_0(sK11) ) ),
    introduced(choice_axiom,[])).

fof(f87,plain,
    ( ~ r1_tarski(sK11,sK12)
    & ~ v1_xboole_0(k3_xboole_0(sK11,sK12))
    & v1_zfmisc_1(sK11)
    & ~ v1_xboole_0(sK11) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12])],[f52,f86,f85])).

fof(f138,plain,(
    ~ r1_tarski(sK11,sK12) ),
    inference(cnf_transformation,[],[f87])).

fof(f137,plain,(
    ~ v1_xboole_0(k3_xboole_0(sK11,sK12)) ),
    inference(cnf_transformation,[],[f87])).

fof(f136,plain,(
    v1_zfmisc_1(sK11) ),
    inference(cnf_transformation,[],[f87])).

fof(f135,plain,(
    ~ v1_xboole_0(sK11) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_99271,plain,
    ( ~ r2_hidden(sK1(sK4(sK2,sK11,sK12),sK2),sK4(sK2,sK11,sK12))
    | ~ v1_xboole_0(sK4(sK2,sK11,sK12)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_89749,plain,
    ( r1_tarski(sK4(sK2,sK11,sK12),sK2)
    | r2_hidden(sK1(sK4(sK2,sK11,sK12),sK2),sK4(sK2,sK11,sK12)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_46,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f134])).

cnf(c_20433,plain,
    ( ~ r1_tarski(sK4(sK2,sK11,sK12),sK11)
    | ~ v1_zfmisc_1(sK11)
    | v1_xboole_0(sK4(sK2,sK11,sK12))
    | v1_xboole_0(sK11)
    | sK11 = sK4(sK2,sK11,sK12) ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(c_1436,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2454,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK11,sK12)
    | sK12 != X1
    | sK11 != X0 ),
    inference(instantiation,[status(thm)],[c_1436])).

cnf(c_2664,plain,
    ( ~ r1_tarski(X0,sK12)
    | r1_tarski(sK11,sK12)
    | sK12 != sK12
    | sK11 != X0 ),
    inference(instantiation,[status(thm)],[c_2454])).

cnf(c_11211,plain,
    ( ~ r1_tarski(sK4(sK2,sK11,sK12),sK12)
    | r1_tarski(sK11,sK12)
    | sK12 != sK12
    | sK11 != sK4(sK2,sK11,sK12) ),
    inference(instantiation,[status(thm)],[c_2664])).

cnf(c_2537,plain,
    ( r1_tarski(X0,sK12)
    | r2_hidden(sK1(X0,sK12),X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_6692,plain,
    ( r1_tarski(sK2,sK12)
    | r2_hidden(sK1(sK2,sK12),sK2) ),
    inference(instantiation,[status(thm)],[c_2537])).

cnf(c_27,plain,
    ( v1_xboole_0(sK5(X0)) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_2364,plain,
    ( v1_xboole_0(sK5(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5,plain,
    ( v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2383,plain,
    ( v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_20,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_2370,plain,
    ( X0 = X1
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5922,plain,
    ( sK2 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2383,c_2370])).

cnf(c_5984,plain,
    ( sK5(X0) = sK2 ),
    inference(superposition,[status(thm)],[c_2364,c_5922])).

cnf(c_28,plain,
    ( m1_subset_1(sK5(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_2363,plain,
    ( m1_subset_1(sK5(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_2361,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4926,plain,
    ( r1_tarski(sK5(X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2363,c_2361])).

cnf(c_5988,plain,
    ( r1_tarski(sK2,X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5984,c_4926])).

cnf(c_5996,plain,
    ( r1_tarski(sK2,X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5988])).

cnf(c_5998,plain,
    ( r1_tarski(sK2,sK11) ),
    inference(instantiation,[status(thm)],[c_5996])).

cnf(c_3030,plain,
    ( ~ r2_hidden(sK1(X0,sK12),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_4382,plain,
    ( ~ r2_hidden(sK1(sK2,sK12),sK2)
    | ~ v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3030])).

cnf(c_1432,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3012,plain,
    ( sK12 = sK12 ),
    inference(instantiation,[status(thm)],[c_1432])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | ~ r1_tarski(sK4(X0,X1,X2),X0)
    | k3_xboole_0(X1,X2) = X0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_2757,plain,
    ( ~ r1_tarski(sK4(sK2,sK11,sK12),sK2)
    | ~ r1_tarski(sK2,sK12)
    | ~ r1_tarski(sK2,sK11)
    | k3_xboole_0(sK11,sK12) = sK2 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(sK4(X0,X1,X2),X2)
    | k3_xboole_0(X1,X2) = X0 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_2758,plain,
    ( r1_tarski(sK4(sK2,sK11,sK12),sK12)
    | ~ r1_tarski(sK2,sK12)
    | ~ r1_tarski(sK2,sK11)
    | k3_xboole_0(sK11,sK12) = sK2 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(sK4(X0,X1,X2),X1)
    | k3_xboole_0(X1,X2) = X0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2759,plain,
    ( r1_tarski(sK4(sK2,sK11,sK12),sK11)
    | ~ r1_tarski(sK2,sK12)
    | ~ r1_tarski(sK2,sK11)
    | k3_xboole_0(sK11,sK12) = sK2 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1434,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2465,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k3_xboole_0(sK11,sK12))
    | k3_xboole_0(sK11,sK12) != X0 ),
    inference(instantiation,[status(thm)],[c_1434])).

cnf(c_2606,plain,
    ( v1_xboole_0(k3_xboole_0(sK11,sK12))
    | ~ v1_xboole_0(sK2)
    | k3_xboole_0(sK11,sK12) != sK2 ),
    inference(instantiation,[status(thm)],[c_2465])).

cnf(c_47,negated_conjecture,
    ( ~ r1_tarski(sK11,sK12) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_48,negated_conjecture,
    ( ~ v1_xboole_0(k3_xboole_0(sK11,sK12)) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_49,negated_conjecture,
    ( v1_zfmisc_1(sK11) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_50,negated_conjecture,
    ( ~ v1_xboole_0(sK11) ),
    inference(cnf_transformation,[],[f135])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_99271,c_89749,c_20433,c_11211,c_6692,c_5998,c_4382,c_3012,c_2757,c_2758,c_2759,c_2606,c_5,c_47,c_48,c_49,c_50])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:44:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 23.79/3.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.79/3.51  
% 23.79/3.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.79/3.51  
% 23.79/3.51  ------  iProver source info
% 23.79/3.51  
% 23.79/3.51  git: date: 2020-06-30 10:37:57 +0100
% 23.79/3.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.79/3.51  git: non_committed_changes: false
% 23.79/3.51  git: last_make_outside_of_git: false
% 23.79/3.51  
% 23.79/3.51  ------ 
% 23.79/3.51  
% 23.79/3.51  ------ Input Options
% 23.79/3.51  
% 23.79/3.51  --out_options                           all
% 23.79/3.51  --tptp_safe_out                         true
% 23.79/3.51  --problem_path                          ""
% 23.79/3.51  --include_path                          ""
% 23.79/3.51  --clausifier                            res/vclausify_rel
% 23.79/3.51  --clausifier_options                    ""
% 23.79/3.51  --stdin                                 false
% 23.79/3.51  --stats_out                             all
% 23.79/3.51  
% 23.79/3.51  ------ General Options
% 23.79/3.51  
% 23.79/3.51  --fof                                   false
% 23.79/3.51  --time_out_real                         305.
% 23.79/3.51  --time_out_virtual                      -1.
% 23.79/3.51  --symbol_type_check                     false
% 23.79/3.51  --clausify_out                          false
% 23.79/3.51  --sig_cnt_out                           false
% 23.79/3.51  --trig_cnt_out                          false
% 23.79/3.51  --trig_cnt_out_tolerance                1.
% 23.79/3.51  --trig_cnt_out_sk_spl                   false
% 23.79/3.51  --abstr_cl_out                          false
% 23.79/3.51  
% 23.79/3.51  ------ Global Options
% 23.79/3.51  
% 23.79/3.51  --schedule                              default
% 23.79/3.51  --add_important_lit                     false
% 23.79/3.51  --prop_solver_per_cl                    1000
% 23.79/3.51  --min_unsat_core                        false
% 23.79/3.51  --soft_assumptions                      false
% 23.79/3.51  --soft_lemma_size                       3
% 23.79/3.51  --prop_impl_unit_size                   0
% 23.79/3.51  --prop_impl_unit                        []
% 23.79/3.51  --share_sel_clauses                     true
% 23.79/3.51  --reset_solvers                         false
% 23.79/3.51  --bc_imp_inh                            [conj_cone]
% 23.79/3.51  --conj_cone_tolerance                   3.
% 23.79/3.51  --extra_neg_conj                        none
% 23.79/3.51  --large_theory_mode                     true
% 23.79/3.51  --prolific_symb_bound                   200
% 23.79/3.51  --lt_threshold                          2000
% 23.79/3.51  --clause_weak_htbl                      true
% 23.79/3.51  --gc_record_bc_elim                     false
% 23.79/3.51  
% 23.79/3.51  ------ Preprocessing Options
% 23.79/3.51  
% 23.79/3.51  --preprocessing_flag                    true
% 23.79/3.51  --time_out_prep_mult                    0.1
% 23.79/3.51  --splitting_mode                        input
% 23.79/3.51  --splitting_grd                         true
% 23.79/3.51  --splitting_cvd                         false
% 23.79/3.51  --splitting_cvd_svl                     false
% 23.79/3.51  --splitting_nvd                         32
% 23.79/3.51  --sub_typing                            true
% 23.79/3.51  --prep_gs_sim                           true
% 23.79/3.51  --prep_unflatten                        true
% 23.79/3.51  --prep_res_sim                          true
% 23.79/3.51  --prep_upred                            true
% 23.79/3.51  --prep_sem_filter                       exhaustive
% 23.79/3.51  --prep_sem_filter_out                   false
% 23.79/3.51  --pred_elim                             true
% 23.79/3.51  --res_sim_input                         true
% 23.79/3.51  --eq_ax_congr_red                       true
% 23.79/3.51  --pure_diseq_elim                       true
% 23.79/3.51  --brand_transform                       false
% 23.79/3.51  --non_eq_to_eq                          false
% 23.79/3.51  --prep_def_merge                        true
% 23.79/3.51  --prep_def_merge_prop_impl              false
% 23.79/3.51  --prep_def_merge_mbd                    true
% 23.79/3.51  --prep_def_merge_tr_red                 false
% 23.79/3.51  --prep_def_merge_tr_cl                  false
% 23.79/3.51  --smt_preprocessing                     true
% 23.79/3.51  --smt_ac_axioms                         fast
% 23.79/3.51  --preprocessed_out                      false
% 23.79/3.51  --preprocessed_stats                    false
% 23.79/3.51  
% 23.79/3.51  ------ Abstraction refinement Options
% 23.79/3.51  
% 23.79/3.51  --abstr_ref                             []
% 23.79/3.51  --abstr_ref_prep                        false
% 23.79/3.51  --abstr_ref_until_sat                   false
% 23.79/3.51  --abstr_ref_sig_restrict                funpre
% 23.79/3.51  --abstr_ref_af_restrict_to_split_sk     false
% 23.79/3.51  --abstr_ref_under                       []
% 23.79/3.51  
% 23.79/3.51  ------ SAT Options
% 23.79/3.51  
% 23.79/3.51  --sat_mode                              false
% 23.79/3.51  --sat_fm_restart_options                ""
% 23.79/3.51  --sat_gr_def                            false
% 23.79/3.51  --sat_epr_types                         true
% 23.79/3.51  --sat_non_cyclic_types                  false
% 23.79/3.51  --sat_finite_models                     false
% 23.79/3.51  --sat_fm_lemmas                         false
% 23.79/3.51  --sat_fm_prep                           false
% 23.79/3.51  --sat_fm_uc_incr                        true
% 23.79/3.51  --sat_out_model                         small
% 23.79/3.51  --sat_out_clauses                       false
% 23.79/3.51  
% 23.79/3.51  ------ QBF Options
% 23.79/3.51  
% 23.79/3.51  --qbf_mode                              false
% 23.79/3.51  --qbf_elim_univ                         false
% 23.79/3.51  --qbf_dom_inst                          none
% 23.79/3.51  --qbf_dom_pre_inst                      false
% 23.79/3.51  --qbf_sk_in                             false
% 23.79/3.51  --qbf_pred_elim                         true
% 23.79/3.51  --qbf_split                             512
% 23.79/3.51  
% 23.79/3.51  ------ BMC1 Options
% 23.79/3.51  
% 23.79/3.51  --bmc1_incremental                      false
% 23.79/3.51  --bmc1_axioms                           reachable_all
% 23.79/3.51  --bmc1_min_bound                        0
% 23.79/3.51  --bmc1_max_bound                        -1
% 23.79/3.51  --bmc1_max_bound_default                -1
% 23.79/3.51  --bmc1_symbol_reachability              true
% 23.79/3.51  --bmc1_property_lemmas                  false
% 23.79/3.51  --bmc1_k_induction                      false
% 23.79/3.51  --bmc1_non_equiv_states                 false
% 23.79/3.51  --bmc1_deadlock                         false
% 23.79/3.51  --bmc1_ucm                              false
% 23.79/3.51  --bmc1_add_unsat_core                   none
% 23.79/3.51  --bmc1_unsat_core_children              false
% 23.79/3.51  --bmc1_unsat_core_extrapolate_axioms    false
% 23.79/3.51  --bmc1_out_stat                         full
% 23.79/3.51  --bmc1_ground_init                      false
% 23.79/3.51  --bmc1_pre_inst_next_state              false
% 23.79/3.51  --bmc1_pre_inst_state                   false
% 23.79/3.51  --bmc1_pre_inst_reach_state             false
% 23.79/3.51  --bmc1_out_unsat_core                   false
% 23.79/3.51  --bmc1_aig_witness_out                  false
% 23.79/3.51  --bmc1_verbose                          false
% 23.79/3.51  --bmc1_dump_clauses_tptp                false
% 23.79/3.51  --bmc1_dump_unsat_core_tptp             false
% 23.79/3.51  --bmc1_dump_file                        -
% 23.79/3.51  --bmc1_ucm_expand_uc_limit              128
% 23.79/3.51  --bmc1_ucm_n_expand_iterations          6
% 23.79/3.51  --bmc1_ucm_extend_mode                  1
% 23.79/3.51  --bmc1_ucm_init_mode                    2
% 23.79/3.51  --bmc1_ucm_cone_mode                    none
% 23.79/3.51  --bmc1_ucm_reduced_relation_type        0
% 23.79/3.51  --bmc1_ucm_relax_model                  4
% 23.79/3.51  --bmc1_ucm_full_tr_after_sat            true
% 23.79/3.51  --bmc1_ucm_expand_neg_assumptions       false
% 23.79/3.51  --bmc1_ucm_layered_model                none
% 23.79/3.51  --bmc1_ucm_max_lemma_size               10
% 23.79/3.51  
% 23.79/3.51  ------ AIG Options
% 23.79/3.51  
% 23.79/3.51  --aig_mode                              false
% 23.79/3.51  
% 23.79/3.51  ------ Instantiation Options
% 23.79/3.51  
% 23.79/3.51  --instantiation_flag                    true
% 23.79/3.51  --inst_sos_flag                         true
% 23.79/3.51  --inst_sos_phase                        true
% 23.79/3.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.79/3.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.79/3.51  --inst_lit_sel_side                     num_symb
% 23.79/3.51  --inst_solver_per_active                1400
% 23.79/3.51  --inst_solver_calls_frac                1.
% 23.79/3.51  --inst_passive_queue_type               priority_queues
% 23.79/3.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.79/3.51  --inst_passive_queues_freq              [25;2]
% 23.79/3.51  --inst_dismatching                      true
% 23.79/3.51  --inst_eager_unprocessed_to_passive     true
% 23.79/3.51  --inst_prop_sim_given                   true
% 23.79/3.51  --inst_prop_sim_new                     false
% 23.79/3.51  --inst_subs_new                         false
% 23.79/3.51  --inst_eq_res_simp                      false
% 23.79/3.51  --inst_subs_given                       false
% 23.79/3.51  --inst_orphan_elimination               true
% 23.79/3.51  --inst_learning_loop_flag               true
% 23.79/3.51  --inst_learning_start                   3000
% 23.79/3.51  --inst_learning_factor                  2
% 23.79/3.51  --inst_start_prop_sim_after_learn       3
% 23.79/3.51  --inst_sel_renew                        solver
% 23.79/3.51  --inst_lit_activity_flag                true
% 23.79/3.51  --inst_restr_to_given                   false
% 23.79/3.51  --inst_activity_threshold               500
% 23.79/3.51  --inst_out_proof                        true
% 23.79/3.51  
% 23.79/3.51  ------ Resolution Options
% 23.79/3.51  
% 23.79/3.51  --resolution_flag                       true
% 23.79/3.51  --res_lit_sel                           adaptive
% 23.79/3.51  --res_lit_sel_side                      none
% 23.79/3.51  --res_ordering                          kbo
% 23.79/3.51  --res_to_prop_solver                    active
% 23.79/3.51  --res_prop_simpl_new                    false
% 23.79/3.51  --res_prop_simpl_given                  true
% 23.79/3.51  --res_passive_queue_type                priority_queues
% 23.79/3.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.79/3.51  --res_passive_queues_freq               [15;5]
% 23.79/3.51  --res_forward_subs                      full
% 23.79/3.51  --res_backward_subs                     full
% 23.79/3.51  --res_forward_subs_resolution           true
% 23.79/3.51  --res_backward_subs_resolution          true
% 23.79/3.51  --res_orphan_elimination                true
% 23.79/3.51  --res_time_limit                        2.
% 23.79/3.51  --res_out_proof                         true
% 23.79/3.51  
% 23.79/3.51  ------ Superposition Options
% 23.79/3.51  
% 23.79/3.51  --superposition_flag                    true
% 23.79/3.51  --sup_passive_queue_type                priority_queues
% 23.79/3.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.79/3.51  --sup_passive_queues_freq               [8;1;4]
% 23.79/3.51  --demod_completeness_check              fast
% 23.79/3.51  --demod_use_ground                      true
% 23.79/3.51  --sup_to_prop_solver                    passive
% 23.79/3.51  --sup_prop_simpl_new                    true
% 23.79/3.51  --sup_prop_simpl_given                  true
% 23.79/3.51  --sup_fun_splitting                     true
% 23.79/3.51  --sup_smt_interval                      50000
% 23.79/3.51  
% 23.79/3.51  ------ Superposition Simplification Setup
% 23.79/3.51  
% 23.79/3.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.79/3.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.79/3.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.79/3.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.79/3.51  --sup_full_triv                         [TrivRules;PropSubs]
% 23.79/3.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.79/3.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.79/3.51  --sup_immed_triv                        [TrivRules]
% 23.79/3.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.79/3.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.79/3.51  --sup_immed_bw_main                     []
% 23.79/3.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.79/3.51  --sup_input_triv                        [Unflattening;TrivRules]
% 23.79/3.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.79/3.51  --sup_input_bw                          []
% 23.79/3.51  
% 23.79/3.51  ------ Combination Options
% 23.79/3.51  
% 23.79/3.51  --comb_res_mult                         3
% 23.79/3.51  --comb_sup_mult                         2
% 23.79/3.51  --comb_inst_mult                        10
% 23.79/3.51  
% 23.79/3.51  ------ Debug Options
% 23.79/3.51  
% 23.79/3.51  --dbg_backtrace                         false
% 23.79/3.51  --dbg_dump_prop_clauses                 false
% 23.79/3.51  --dbg_dump_prop_clauses_file            -
% 23.79/3.51  --dbg_out_stat                          false
% 23.79/3.51  ------ Parsing...
% 23.79/3.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.79/3.51  
% 23.79/3.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 23.79/3.51  
% 23.79/3.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.79/3.51  
% 23.79/3.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.79/3.51  ------ Proving...
% 23.79/3.51  ------ Problem Properties 
% 23.79/3.51  
% 23.79/3.51  
% 23.79/3.51  clauses                                 49
% 23.79/3.51  conjectures                             4
% 23.79/3.51  EPR                                     25
% 23.79/3.51  Horn                                    38
% 23.79/3.51  unary                                   19
% 23.79/3.51  binary                                  14
% 23.79/3.51  lits                                    101
% 23.79/3.51  lits eq                                 10
% 23.79/3.51  fd_pure                                 0
% 23.79/3.51  fd_pseudo                               0
% 23.79/3.51  fd_cond                                 0
% 23.79/3.51  fd_pseudo_cond                          6
% 23.79/3.51  AC symbols                              0
% 23.79/3.51  
% 23.79/3.51  ------ Schedule dynamic 5 is on 
% 23.79/3.51  
% 23.79/3.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.79/3.51  
% 23.79/3.51  
% 23.79/3.51  ------ 
% 23.79/3.51  Current options:
% 23.79/3.51  ------ 
% 23.79/3.51  
% 23.79/3.51  ------ Input Options
% 23.79/3.51  
% 23.79/3.51  --out_options                           all
% 23.79/3.51  --tptp_safe_out                         true
% 23.79/3.51  --problem_path                          ""
% 23.79/3.51  --include_path                          ""
% 23.79/3.51  --clausifier                            res/vclausify_rel
% 23.79/3.51  --clausifier_options                    ""
% 23.79/3.51  --stdin                                 false
% 23.79/3.51  --stats_out                             all
% 23.79/3.51  
% 23.79/3.51  ------ General Options
% 23.79/3.51  
% 23.79/3.51  --fof                                   false
% 23.79/3.51  --time_out_real                         305.
% 23.79/3.51  --time_out_virtual                      -1.
% 23.79/3.51  --symbol_type_check                     false
% 23.79/3.51  --clausify_out                          false
% 23.79/3.51  --sig_cnt_out                           false
% 23.79/3.51  --trig_cnt_out                          false
% 23.79/3.51  --trig_cnt_out_tolerance                1.
% 23.79/3.51  --trig_cnt_out_sk_spl                   false
% 23.79/3.51  --abstr_cl_out                          false
% 23.79/3.51  
% 23.79/3.51  ------ Global Options
% 23.79/3.51  
% 23.79/3.51  --schedule                              default
% 23.79/3.51  --add_important_lit                     false
% 23.79/3.51  --prop_solver_per_cl                    1000
% 23.79/3.51  --min_unsat_core                        false
% 23.79/3.51  --soft_assumptions                      false
% 23.79/3.51  --soft_lemma_size                       3
% 23.79/3.51  --prop_impl_unit_size                   0
% 23.79/3.51  --prop_impl_unit                        []
% 23.79/3.51  --share_sel_clauses                     true
% 23.79/3.51  --reset_solvers                         false
% 23.79/3.51  --bc_imp_inh                            [conj_cone]
% 23.79/3.51  --conj_cone_tolerance                   3.
% 23.79/3.51  --extra_neg_conj                        none
% 23.79/3.51  --large_theory_mode                     true
% 23.79/3.51  --prolific_symb_bound                   200
% 23.79/3.51  --lt_threshold                          2000
% 23.79/3.51  --clause_weak_htbl                      true
% 23.79/3.51  --gc_record_bc_elim                     false
% 23.79/3.51  
% 23.79/3.51  ------ Preprocessing Options
% 23.79/3.51  
% 23.79/3.51  --preprocessing_flag                    true
% 23.79/3.51  --time_out_prep_mult                    0.1
% 23.79/3.51  --splitting_mode                        input
% 23.79/3.51  --splitting_grd                         true
% 23.79/3.51  --splitting_cvd                         false
% 23.79/3.51  --splitting_cvd_svl                     false
% 23.79/3.51  --splitting_nvd                         32
% 23.79/3.51  --sub_typing                            true
% 23.79/3.51  --prep_gs_sim                           true
% 23.79/3.51  --prep_unflatten                        true
% 23.79/3.51  --prep_res_sim                          true
% 23.79/3.51  --prep_upred                            true
% 23.79/3.51  --prep_sem_filter                       exhaustive
% 23.79/3.51  --prep_sem_filter_out                   false
% 23.79/3.51  --pred_elim                             true
% 23.79/3.51  --res_sim_input                         true
% 23.79/3.51  --eq_ax_congr_red                       true
% 23.79/3.51  --pure_diseq_elim                       true
% 23.79/3.51  --brand_transform                       false
% 23.79/3.51  --non_eq_to_eq                          false
% 23.79/3.51  --prep_def_merge                        true
% 23.79/3.51  --prep_def_merge_prop_impl              false
% 23.79/3.51  --prep_def_merge_mbd                    true
% 23.79/3.51  --prep_def_merge_tr_red                 false
% 23.79/3.51  --prep_def_merge_tr_cl                  false
% 23.79/3.51  --smt_preprocessing                     true
% 23.79/3.51  --smt_ac_axioms                         fast
% 23.79/3.51  --preprocessed_out                      false
% 23.79/3.51  --preprocessed_stats                    false
% 23.79/3.51  
% 23.79/3.51  ------ Abstraction refinement Options
% 23.79/3.51  
% 23.79/3.51  --abstr_ref                             []
% 23.79/3.51  --abstr_ref_prep                        false
% 23.79/3.51  --abstr_ref_until_sat                   false
% 23.79/3.51  --abstr_ref_sig_restrict                funpre
% 23.79/3.51  --abstr_ref_af_restrict_to_split_sk     false
% 23.79/3.51  --abstr_ref_under                       []
% 23.79/3.51  
% 23.79/3.51  ------ SAT Options
% 23.79/3.51  
% 23.79/3.51  --sat_mode                              false
% 23.79/3.51  --sat_fm_restart_options                ""
% 23.79/3.51  --sat_gr_def                            false
% 23.79/3.51  --sat_epr_types                         true
% 23.79/3.51  --sat_non_cyclic_types                  false
% 23.79/3.51  --sat_finite_models                     false
% 23.79/3.51  --sat_fm_lemmas                         false
% 23.79/3.51  --sat_fm_prep                           false
% 23.79/3.51  --sat_fm_uc_incr                        true
% 23.79/3.51  --sat_out_model                         small
% 23.79/3.51  --sat_out_clauses                       false
% 23.79/3.51  
% 23.79/3.51  ------ QBF Options
% 23.79/3.51  
% 23.79/3.51  --qbf_mode                              false
% 23.79/3.51  --qbf_elim_univ                         false
% 23.79/3.51  --qbf_dom_inst                          none
% 23.79/3.51  --qbf_dom_pre_inst                      false
% 23.79/3.51  --qbf_sk_in                             false
% 23.79/3.51  --qbf_pred_elim                         true
% 23.79/3.51  --qbf_split                             512
% 23.79/3.51  
% 23.79/3.51  ------ BMC1 Options
% 23.79/3.51  
% 23.79/3.51  --bmc1_incremental                      false
% 23.79/3.51  --bmc1_axioms                           reachable_all
% 23.79/3.51  --bmc1_min_bound                        0
% 23.79/3.51  --bmc1_max_bound                        -1
% 23.79/3.51  --bmc1_max_bound_default                -1
% 23.79/3.51  --bmc1_symbol_reachability              true
% 23.79/3.51  --bmc1_property_lemmas                  false
% 23.79/3.51  --bmc1_k_induction                      false
% 23.79/3.51  --bmc1_non_equiv_states                 false
% 23.79/3.51  --bmc1_deadlock                         false
% 23.79/3.51  --bmc1_ucm                              false
% 23.79/3.51  --bmc1_add_unsat_core                   none
% 23.79/3.51  --bmc1_unsat_core_children              false
% 23.79/3.51  --bmc1_unsat_core_extrapolate_axioms    false
% 23.79/3.51  --bmc1_out_stat                         full
% 23.79/3.51  --bmc1_ground_init                      false
% 23.79/3.51  --bmc1_pre_inst_next_state              false
% 23.79/3.51  --bmc1_pre_inst_state                   false
% 23.79/3.51  --bmc1_pre_inst_reach_state             false
% 23.79/3.51  --bmc1_out_unsat_core                   false
% 23.79/3.51  --bmc1_aig_witness_out                  false
% 23.79/3.51  --bmc1_verbose                          false
% 23.79/3.51  --bmc1_dump_clauses_tptp                false
% 23.79/3.51  --bmc1_dump_unsat_core_tptp             false
% 23.79/3.51  --bmc1_dump_file                        -
% 23.79/3.51  --bmc1_ucm_expand_uc_limit              128
% 23.79/3.51  --bmc1_ucm_n_expand_iterations          6
% 23.79/3.51  --bmc1_ucm_extend_mode                  1
% 23.79/3.51  --bmc1_ucm_init_mode                    2
% 23.79/3.51  --bmc1_ucm_cone_mode                    none
% 23.79/3.51  --bmc1_ucm_reduced_relation_type        0
% 23.79/3.51  --bmc1_ucm_relax_model                  4
% 23.79/3.51  --bmc1_ucm_full_tr_after_sat            true
% 23.79/3.51  --bmc1_ucm_expand_neg_assumptions       false
% 23.79/3.51  --bmc1_ucm_layered_model                none
% 23.79/3.51  --bmc1_ucm_max_lemma_size               10
% 23.79/3.51  
% 23.79/3.51  ------ AIG Options
% 23.79/3.51  
% 23.79/3.51  --aig_mode                              false
% 23.79/3.51  
% 23.79/3.51  ------ Instantiation Options
% 23.79/3.51  
% 23.79/3.51  --instantiation_flag                    true
% 23.79/3.51  --inst_sos_flag                         true
% 23.79/3.51  --inst_sos_phase                        true
% 23.79/3.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.79/3.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.79/3.51  --inst_lit_sel_side                     none
% 23.79/3.51  --inst_solver_per_active                1400
% 23.79/3.51  --inst_solver_calls_frac                1.
% 23.79/3.51  --inst_passive_queue_type               priority_queues
% 23.79/3.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.79/3.51  --inst_passive_queues_freq              [25;2]
% 23.79/3.51  --inst_dismatching                      true
% 23.79/3.51  --inst_eager_unprocessed_to_passive     true
% 23.79/3.51  --inst_prop_sim_given                   true
% 23.79/3.51  --inst_prop_sim_new                     false
% 23.79/3.51  --inst_subs_new                         false
% 23.79/3.51  --inst_eq_res_simp                      false
% 23.79/3.51  --inst_subs_given                       false
% 23.79/3.51  --inst_orphan_elimination               true
% 23.79/3.51  --inst_learning_loop_flag               true
% 23.79/3.51  --inst_learning_start                   3000
% 23.79/3.51  --inst_learning_factor                  2
% 23.79/3.51  --inst_start_prop_sim_after_learn       3
% 23.79/3.51  --inst_sel_renew                        solver
% 23.79/3.51  --inst_lit_activity_flag                true
% 23.79/3.51  --inst_restr_to_given                   false
% 23.79/3.51  --inst_activity_threshold               500
% 23.79/3.51  --inst_out_proof                        true
% 23.79/3.51  
% 23.79/3.51  ------ Resolution Options
% 23.79/3.51  
% 23.79/3.51  --resolution_flag                       false
% 23.79/3.51  --res_lit_sel                           adaptive
% 23.79/3.51  --res_lit_sel_side                      none
% 23.79/3.51  --res_ordering                          kbo
% 23.79/3.51  --res_to_prop_solver                    active
% 23.79/3.51  --res_prop_simpl_new                    false
% 23.79/3.51  --res_prop_simpl_given                  true
% 23.79/3.51  --res_passive_queue_type                priority_queues
% 23.79/3.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.79/3.51  --res_passive_queues_freq               [15;5]
% 23.79/3.51  --res_forward_subs                      full
% 23.79/3.51  --res_backward_subs                     full
% 23.79/3.51  --res_forward_subs_resolution           true
% 23.79/3.51  --res_backward_subs_resolution          true
% 23.79/3.51  --res_orphan_elimination                true
% 23.79/3.51  --res_time_limit                        2.
% 23.79/3.51  --res_out_proof                         true
% 23.79/3.51  
% 23.79/3.51  ------ Superposition Options
% 23.79/3.51  
% 23.79/3.51  --superposition_flag                    true
% 23.79/3.51  --sup_passive_queue_type                priority_queues
% 23.79/3.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.79/3.51  --sup_passive_queues_freq               [8;1;4]
% 23.79/3.51  --demod_completeness_check              fast
% 23.79/3.51  --demod_use_ground                      true
% 23.79/3.51  --sup_to_prop_solver                    passive
% 23.79/3.51  --sup_prop_simpl_new                    true
% 23.79/3.51  --sup_prop_simpl_given                  true
% 23.79/3.51  --sup_fun_splitting                     true
% 23.79/3.51  --sup_smt_interval                      50000
% 23.79/3.51  
% 23.79/3.51  ------ Superposition Simplification Setup
% 23.79/3.51  
% 23.79/3.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.79/3.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.79/3.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.79/3.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.79/3.51  --sup_full_triv                         [TrivRules;PropSubs]
% 23.79/3.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.79/3.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.79/3.51  --sup_immed_triv                        [TrivRules]
% 23.79/3.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.79/3.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.79/3.51  --sup_immed_bw_main                     []
% 23.79/3.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.79/3.51  --sup_input_triv                        [Unflattening;TrivRules]
% 23.79/3.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.79/3.51  --sup_input_bw                          []
% 23.79/3.51  
% 23.79/3.51  ------ Combination Options
% 23.79/3.51  
% 23.79/3.51  --comb_res_mult                         3
% 23.79/3.51  --comb_sup_mult                         2
% 23.79/3.51  --comb_inst_mult                        10
% 23.79/3.51  
% 23.79/3.51  ------ Debug Options
% 23.79/3.51  
% 23.79/3.51  --dbg_backtrace                         false
% 23.79/3.51  --dbg_dump_prop_clauses                 false
% 23.79/3.51  --dbg_dump_prop_clauses_file            -
% 23.79/3.51  --dbg_out_stat                          false
% 23.79/3.51  
% 23.79/3.51  
% 23.79/3.51  
% 23.79/3.51  
% 23.79/3.51  ------ Proving...
% 23.79/3.51  
% 23.79/3.51  
% 23.79/3.51  % SZS status Theorem for theBenchmark.p
% 23.79/3.51  
% 23.79/3.51  % SZS output start CNFRefutation for theBenchmark.p
% 23.79/3.51  
% 23.79/3.51  fof(f13,axiom,(
% 23.79/3.51    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 23.79/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.79/3.51  
% 23.79/3.51  fof(f40,plain,(
% 23.79/3.51    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 23.79/3.51    inference(ennf_transformation,[],[f13])).
% 23.79/3.51  
% 23.79/3.51  fof(f107,plain,(
% 23.79/3.51    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1)) )),
% 23.79/3.51    inference(cnf_transformation,[],[f40])).
% 23.79/3.51  
% 23.79/3.51  fof(f2,axiom,(
% 23.79/3.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 23.79/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.79/3.51  
% 23.79/3.51  fof(f33,plain,(
% 23.79/3.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 23.79/3.51    inference(ennf_transformation,[],[f2])).
% 23.79/3.51  
% 23.79/3.51  fof(f57,plain,(
% 23.79/3.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 23.79/3.51    inference(nnf_transformation,[],[f33])).
% 23.79/3.51  
% 23.79/3.51  fof(f58,plain,(
% 23.79/3.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 23.79/3.51    inference(rectify,[],[f57])).
% 23.79/3.51  
% 23.79/3.51  fof(f59,plain,(
% 23.79/3.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 23.79/3.51    introduced(choice_axiom,[])).
% 23.79/3.51  
% 23.79/3.51  fof(f60,plain,(
% 23.79/3.51    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 23.79/3.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f58,f59])).
% 23.79/3.51  
% 23.79/3.51  fof(f91,plain,(
% 23.79/3.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 23.79/3.51    inference(cnf_transformation,[],[f60])).
% 23.79/3.51  
% 23.79/3.51  fof(f29,axiom,(
% 23.79/3.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 23.79/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.79/3.51  
% 23.79/3.51  fof(f49,plain,(
% 23.79/3.51    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 23.79/3.51    inference(ennf_transformation,[],[f29])).
% 23.79/3.51  
% 23.79/3.51  fof(f50,plain,(
% 23.79/3.51    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 23.79/3.51    inference(flattening,[],[f49])).
% 23.79/3.51  
% 23.79/3.51  fof(f134,plain,(
% 23.79/3.51    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 23.79/3.51    inference(cnf_transformation,[],[f50])).
% 23.79/3.51  
% 23.79/3.51  fof(f18,axiom,(
% 23.79/3.51    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.79/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.79/3.51  
% 23.79/3.51  fof(f70,plain,(
% 23.79/3.51    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (v1_xboole_0(sK5(X0)) & m1_subset_1(sK5(X0),k1_zfmisc_1(X0))))),
% 23.79/3.51    introduced(choice_axiom,[])).
% 23.79/3.51  
% 23.79/3.51  fof(f71,plain,(
% 23.79/3.51    ! [X0] : (v1_xboole_0(sK5(X0)) & m1_subset_1(sK5(X0),k1_zfmisc_1(X0)))),
% 23.79/3.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f18,f70])).
% 23.79/3.51  
% 23.79/3.51  fof(f116,plain,(
% 23.79/3.51    ( ! [X0] : (v1_xboole_0(sK5(X0))) )),
% 23.79/3.51    inference(cnf_transformation,[],[f71])).
% 23.79/3.51  
% 23.79/3.51  fof(f3,axiom,(
% 23.79/3.51    ? [X0] : v1_xboole_0(X0)),
% 23.79/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.79/3.51  
% 23.79/3.51  fof(f61,plain,(
% 23.79/3.51    ? [X0] : v1_xboole_0(X0) => v1_xboole_0(sK2)),
% 23.79/3.51    introduced(choice_axiom,[])).
% 23.79/3.51  
% 23.79/3.51  fof(f62,plain,(
% 23.79/3.51    v1_xboole_0(sK2)),
% 23.79/3.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f3,f61])).
% 23.79/3.51  
% 23.79/3.51  fof(f93,plain,(
% 23.79/3.51    v1_xboole_0(sK2)),
% 23.79/3.51    inference(cnf_transformation,[],[f62])).
% 23.79/3.51  
% 23.79/3.51  fof(f14,axiom,(
% 23.79/3.51    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 23.79/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.79/3.51  
% 23.79/3.51  fof(f41,plain,(
% 23.79/3.51    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 23.79/3.51    inference(ennf_transformation,[],[f14])).
% 23.79/3.51  
% 23.79/3.51  fof(f108,plain,(
% 23.79/3.51    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 23.79/3.51    inference(cnf_transformation,[],[f41])).
% 23.79/3.51  
% 23.79/3.51  fof(f115,plain,(
% 23.79/3.51    ( ! [X0] : (m1_subset_1(sK5(X0),k1_zfmisc_1(X0))) )),
% 23.79/3.51    inference(cnf_transformation,[],[f71])).
% 23.79/3.51  
% 23.79/3.51  fof(f19,axiom,(
% 23.79/3.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 23.79/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.79/3.51  
% 23.79/3.51  fof(f72,plain,(
% 23.79/3.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 23.79/3.51    inference(nnf_transformation,[],[f19])).
% 23.79/3.51  
% 23.79/3.51  fof(f117,plain,(
% 23.79/3.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 23.79/3.51    inference(cnf_transformation,[],[f72])).
% 23.79/3.51  
% 23.79/3.51  fof(f8,axiom,(
% 23.79/3.51    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X3,X2) & r1_tarski(X3,X1)) => r1_tarski(X3,X0)) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k3_xboole_0(X1,X2) = X0)),
% 23.79/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.79/3.51  
% 23.79/3.51  fof(f36,plain,(
% 23.79/3.51    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | (? [X3] : (~r1_tarski(X3,X0) & (r1_tarski(X3,X2) & r1_tarski(X3,X1))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 23.79/3.51    inference(ennf_transformation,[],[f8])).
% 23.79/3.51  
% 23.79/3.51  fof(f37,plain,(
% 23.79/3.51    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | ? [X3] : (~r1_tarski(X3,X0) & r1_tarski(X3,X2) & r1_tarski(X3,X1)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 23.79/3.51    inference(flattening,[],[f36])).
% 23.79/3.51  
% 23.79/3.51  fof(f67,plain,(
% 23.79/3.51    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(X3,X0) & r1_tarski(X3,X2) & r1_tarski(X3,X1)) => (~r1_tarski(sK4(X0,X1,X2),X0) & r1_tarski(sK4(X0,X1,X2),X2) & r1_tarski(sK4(X0,X1,X2),X1)))),
% 23.79/3.51    introduced(choice_axiom,[])).
% 23.79/3.51  
% 23.79/3.51  fof(f68,plain,(
% 23.79/3.51    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | (~r1_tarski(sK4(X0,X1,X2),X0) & r1_tarski(sK4(X0,X1,X2),X2) & r1_tarski(sK4(X0,X1,X2),X1)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 23.79/3.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f67])).
% 23.79/3.51  
% 23.79/3.51  fof(f102,plain,(
% 23.79/3.51    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = X0 | ~r1_tarski(sK4(X0,X1,X2),X0) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 23.79/3.51    inference(cnf_transformation,[],[f68])).
% 23.79/3.51  
% 23.79/3.51  fof(f101,plain,(
% 23.79/3.51    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = X0 | r1_tarski(sK4(X0,X1,X2),X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 23.79/3.51    inference(cnf_transformation,[],[f68])).
% 23.79/3.51  
% 23.79/3.51  fof(f100,plain,(
% 23.79/3.51    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = X0 | r1_tarski(sK4(X0,X1,X2),X1) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 23.79/3.51    inference(cnf_transformation,[],[f68])).
% 23.79/3.51  
% 23.79/3.51  fof(f30,conjecture,(
% 23.79/3.51    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 23.79/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.79/3.51  
% 23.79/3.51  fof(f31,negated_conjecture,(
% 23.79/3.51    ~! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 23.79/3.51    inference(negated_conjecture,[],[f30])).
% 23.79/3.51  
% 23.79/3.51  fof(f51,plain,(
% 23.79/3.51    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & (v1_zfmisc_1(X0) & ~v1_xboole_0(X0)))),
% 23.79/3.51    inference(ennf_transformation,[],[f31])).
% 23.79/3.51  
% 23.79/3.51  fof(f52,plain,(
% 23.79/3.51    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & v1_zfmisc_1(X0) & ~v1_xboole_0(X0))),
% 23.79/3.51    inference(flattening,[],[f51])).
% 23.79/3.51  
% 23.79/3.51  fof(f86,plain,(
% 23.79/3.51    ( ! [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) => (~r1_tarski(X0,sK12) & ~v1_xboole_0(k3_xboole_0(X0,sK12)))) )),
% 23.79/3.51    introduced(choice_axiom,[])).
% 23.79/3.51  
% 23.79/3.51  fof(f85,plain,(
% 23.79/3.51    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => (? [X1] : (~r1_tarski(sK11,X1) & ~v1_xboole_0(k3_xboole_0(sK11,X1))) & v1_zfmisc_1(sK11) & ~v1_xboole_0(sK11))),
% 23.79/3.51    introduced(choice_axiom,[])).
% 23.79/3.51  
% 23.79/3.51  fof(f87,plain,(
% 23.79/3.51    (~r1_tarski(sK11,sK12) & ~v1_xboole_0(k3_xboole_0(sK11,sK12))) & v1_zfmisc_1(sK11) & ~v1_xboole_0(sK11)),
% 23.79/3.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12])],[f52,f86,f85])).
% 23.79/3.51  
% 23.79/3.51  fof(f138,plain,(
% 23.79/3.51    ~r1_tarski(sK11,sK12)),
% 23.79/3.51    inference(cnf_transformation,[],[f87])).
% 23.79/3.51  
% 23.79/3.51  fof(f137,plain,(
% 23.79/3.51    ~v1_xboole_0(k3_xboole_0(sK11,sK12))),
% 23.79/3.51    inference(cnf_transformation,[],[f87])).
% 23.79/3.51  
% 23.79/3.51  fof(f136,plain,(
% 23.79/3.51    v1_zfmisc_1(sK11)),
% 23.79/3.51    inference(cnf_transformation,[],[f87])).
% 23.79/3.51  
% 23.79/3.51  fof(f135,plain,(
% 23.79/3.51    ~v1_xboole_0(sK11)),
% 23.79/3.51    inference(cnf_transformation,[],[f87])).
% 23.79/3.51  
% 23.79/3.51  cnf(c_19,plain,
% 23.79/3.51      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 23.79/3.51      inference(cnf_transformation,[],[f107]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_99271,plain,
% 23.79/3.51      ( ~ r2_hidden(sK1(sK4(sK2,sK11,sK12),sK2),sK4(sK2,sK11,sK12))
% 23.79/3.51      | ~ v1_xboole_0(sK4(sK2,sK11,sK12)) ),
% 23.79/3.51      inference(instantiation,[status(thm)],[c_19]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_3,plain,
% 23.79/3.51      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 23.79/3.51      inference(cnf_transformation,[],[f91]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_89749,plain,
% 23.79/3.51      ( r1_tarski(sK4(sK2,sK11,sK12),sK2)
% 23.79/3.51      | r2_hidden(sK1(sK4(sK2,sK11,sK12),sK2),sK4(sK2,sK11,sK12)) ),
% 23.79/3.51      inference(instantiation,[status(thm)],[c_3]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_46,plain,
% 23.79/3.51      ( ~ r1_tarski(X0,X1)
% 23.79/3.51      | ~ v1_zfmisc_1(X1)
% 23.79/3.51      | v1_xboole_0(X0)
% 23.79/3.51      | v1_xboole_0(X1)
% 23.79/3.51      | X1 = X0 ),
% 23.79/3.51      inference(cnf_transformation,[],[f134]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_20433,plain,
% 23.79/3.51      ( ~ r1_tarski(sK4(sK2,sK11,sK12),sK11)
% 23.79/3.51      | ~ v1_zfmisc_1(sK11)
% 23.79/3.51      | v1_xboole_0(sK4(sK2,sK11,sK12))
% 23.79/3.51      | v1_xboole_0(sK11)
% 23.79/3.51      | sK11 = sK4(sK2,sK11,sK12) ),
% 23.79/3.51      inference(instantiation,[status(thm)],[c_46]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_1436,plain,
% 23.79/3.51      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.79/3.51      theory(equality) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_2454,plain,
% 23.79/3.51      ( ~ r1_tarski(X0,X1)
% 23.79/3.51      | r1_tarski(sK11,sK12)
% 23.79/3.51      | sK12 != X1
% 23.79/3.51      | sK11 != X0 ),
% 23.79/3.51      inference(instantiation,[status(thm)],[c_1436]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_2664,plain,
% 23.79/3.51      ( ~ r1_tarski(X0,sK12)
% 23.79/3.51      | r1_tarski(sK11,sK12)
% 23.79/3.51      | sK12 != sK12
% 23.79/3.51      | sK11 != X0 ),
% 23.79/3.51      inference(instantiation,[status(thm)],[c_2454]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_11211,plain,
% 23.79/3.51      ( ~ r1_tarski(sK4(sK2,sK11,sK12),sK12)
% 23.79/3.51      | r1_tarski(sK11,sK12)
% 23.79/3.51      | sK12 != sK12
% 23.79/3.51      | sK11 != sK4(sK2,sK11,sK12) ),
% 23.79/3.51      inference(instantiation,[status(thm)],[c_2664]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_2537,plain,
% 23.79/3.51      ( r1_tarski(X0,sK12) | r2_hidden(sK1(X0,sK12),X0) ),
% 23.79/3.51      inference(instantiation,[status(thm)],[c_3]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_6692,plain,
% 23.79/3.51      ( r1_tarski(sK2,sK12) | r2_hidden(sK1(sK2,sK12),sK2) ),
% 23.79/3.51      inference(instantiation,[status(thm)],[c_2537]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_27,plain,
% 23.79/3.51      ( v1_xboole_0(sK5(X0)) ),
% 23.79/3.51      inference(cnf_transformation,[],[f116]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_2364,plain,
% 23.79/3.51      ( v1_xboole_0(sK5(X0)) = iProver_top ),
% 23.79/3.51      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_5,plain,
% 23.79/3.51      ( v1_xboole_0(sK2) ),
% 23.79/3.51      inference(cnf_transformation,[],[f93]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_2383,plain,
% 23.79/3.51      ( v1_xboole_0(sK2) = iProver_top ),
% 23.79/3.51      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_20,plain,
% 23.79/3.51      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 23.79/3.51      inference(cnf_transformation,[],[f108]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_2370,plain,
% 23.79/3.51      ( X0 = X1
% 23.79/3.51      | v1_xboole_0(X0) != iProver_top
% 23.79/3.51      | v1_xboole_0(X1) != iProver_top ),
% 23.79/3.51      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_5922,plain,
% 23.79/3.51      ( sK2 = X0 | v1_xboole_0(X0) != iProver_top ),
% 23.79/3.51      inference(superposition,[status(thm)],[c_2383,c_2370]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_5984,plain,
% 23.79/3.51      ( sK5(X0) = sK2 ),
% 23.79/3.51      inference(superposition,[status(thm)],[c_2364,c_5922]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_28,plain,
% 23.79/3.51      ( m1_subset_1(sK5(X0),k1_zfmisc_1(X0)) ),
% 23.79/3.51      inference(cnf_transformation,[],[f115]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_2363,plain,
% 23.79/3.51      ( m1_subset_1(sK5(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 23.79/3.51      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_30,plain,
% 23.79/3.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 23.79/3.51      inference(cnf_transformation,[],[f117]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_2361,plain,
% 23.79/3.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 23.79/3.51      | r1_tarski(X0,X1) = iProver_top ),
% 23.79/3.51      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_4926,plain,
% 23.79/3.51      ( r1_tarski(sK5(X0),X0) = iProver_top ),
% 23.79/3.51      inference(superposition,[status(thm)],[c_2363,c_2361]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_5988,plain,
% 23.79/3.51      ( r1_tarski(sK2,X0) = iProver_top ),
% 23.79/3.51      inference(demodulation,[status(thm)],[c_5984,c_4926]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_5996,plain,
% 23.79/3.51      ( r1_tarski(sK2,X0) ),
% 23.79/3.51      inference(predicate_to_equality_rev,[status(thm)],[c_5988]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_5998,plain,
% 23.79/3.51      ( r1_tarski(sK2,sK11) ),
% 23.79/3.51      inference(instantiation,[status(thm)],[c_5996]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_3030,plain,
% 23.79/3.51      ( ~ r2_hidden(sK1(X0,sK12),X0) | ~ v1_xboole_0(X0) ),
% 23.79/3.51      inference(instantiation,[status(thm)],[c_19]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_4382,plain,
% 23.79/3.51      ( ~ r2_hidden(sK1(sK2,sK12),sK2) | ~ v1_xboole_0(sK2) ),
% 23.79/3.51      inference(instantiation,[status(thm)],[c_3030]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_1432,plain,( X0 = X0 ),theory(equality) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_3012,plain,
% 23.79/3.51      ( sK12 = sK12 ),
% 23.79/3.51      inference(instantiation,[status(thm)],[c_1432]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_12,plain,
% 23.79/3.51      ( ~ r1_tarski(X0,X1)
% 23.79/3.51      | ~ r1_tarski(X0,X2)
% 23.79/3.51      | ~ r1_tarski(sK4(X0,X1,X2),X0)
% 23.79/3.51      | k3_xboole_0(X1,X2) = X0 ),
% 23.79/3.51      inference(cnf_transformation,[],[f102]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_2757,plain,
% 23.79/3.51      ( ~ r1_tarski(sK4(sK2,sK11,sK12),sK2)
% 23.79/3.51      | ~ r1_tarski(sK2,sK12)
% 23.79/3.51      | ~ r1_tarski(sK2,sK11)
% 23.79/3.51      | k3_xboole_0(sK11,sK12) = sK2 ),
% 23.79/3.51      inference(instantiation,[status(thm)],[c_12]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_13,plain,
% 23.79/3.51      ( ~ r1_tarski(X0,X1)
% 23.79/3.51      | ~ r1_tarski(X0,X2)
% 23.79/3.51      | r1_tarski(sK4(X0,X1,X2),X2)
% 23.79/3.51      | k3_xboole_0(X1,X2) = X0 ),
% 23.79/3.51      inference(cnf_transformation,[],[f101]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_2758,plain,
% 23.79/3.51      ( r1_tarski(sK4(sK2,sK11,sK12),sK12)
% 23.79/3.51      | ~ r1_tarski(sK2,sK12)
% 23.79/3.51      | ~ r1_tarski(sK2,sK11)
% 23.79/3.51      | k3_xboole_0(sK11,sK12) = sK2 ),
% 23.79/3.51      inference(instantiation,[status(thm)],[c_13]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_14,plain,
% 23.79/3.51      ( ~ r1_tarski(X0,X1)
% 23.79/3.51      | ~ r1_tarski(X0,X2)
% 23.79/3.51      | r1_tarski(sK4(X0,X1,X2),X1)
% 23.79/3.51      | k3_xboole_0(X1,X2) = X0 ),
% 23.79/3.51      inference(cnf_transformation,[],[f100]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_2759,plain,
% 23.79/3.51      ( r1_tarski(sK4(sK2,sK11,sK12),sK11)
% 23.79/3.51      | ~ r1_tarski(sK2,sK12)
% 23.79/3.51      | ~ r1_tarski(sK2,sK11)
% 23.79/3.51      | k3_xboole_0(sK11,sK12) = sK2 ),
% 23.79/3.51      inference(instantiation,[status(thm)],[c_14]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_1434,plain,
% 23.79/3.51      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 23.79/3.51      theory(equality) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_2465,plain,
% 23.79/3.51      ( ~ v1_xboole_0(X0)
% 23.79/3.51      | v1_xboole_0(k3_xboole_0(sK11,sK12))
% 23.79/3.51      | k3_xboole_0(sK11,sK12) != X0 ),
% 23.79/3.51      inference(instantiation,[status(thm)],[c_1434]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_2606,plain,
% 23.79/3.51      ( v1_xboole_0(k3_xboole_0(sK11,sK12))
% 23.79/3.51      | ~ v1_xboole_0(sK2)
% 23.79/3.51      | k3_xboole_0(sK11,sK12) != sK2 ),
% 23.79/3.51      inference(instantiation,[status(thm)],[c_2465]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_47,negated_conjecture,
% 23.79/3.51      ( ~ r1_tarski(sK11,sK12) ),
% 23.79/3.51      inference(cnf_transformation,[],[f138]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_48,negated_conjecture,
% 23.79/3.51      ( ~ v1_xboole_0(k3_xboole_0(sK11,sK12)) ),
% 23.79/3.51      inference(cnf_transformation,[],[f137]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_49,negated_conjecture,
% 23.79/3.51      ( v1_zfmisc_1(sK11) ),
% 23.79/3.51      inference(cnf_transformation,[],[f136]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_50,negated_conjecture,
% 23.79/3.51      ( ~ v1_xboole_0(sK11) ),
% 23.79/3.51      inference(cnf_transformation,[],[f135]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(contradiction,plain,
% 23.79/3.51      ( $false ),
% 23.79/3.51      inference(minisat,
% 23.79/3.51                [status(thm)],
% 23.79/3.51                [c_99271,c_89749,c_20433,c_11211,c_6692,c_5998,c_4382,
% 23.79/3.51                 c_3012,c_2757,c_2758,c_2759,c_2606,c_5,c_47,c_48,c_49,
% 23.79/3.51                 c_50]) ).
% 23.79/3.51  
% 23.79/3.51  
% 23.79/3.51  % SZS output end CNFRefutation for theBenchmark.p
% 23.79/3.51  
% 23.79/3.51  ------                               Statistics
% 23.79/3.51  
% 23.79/3.51  ------ General
% 23.79/3.52  
% 23.79/3.52  abstr_ref_over_cycles:                  0
% 23.79/3.52  abstr_ref_under_cycles:                 0
% 23.79/3.52  gc_basic_clause_elim:                   0
% 23.79/3.52  forced_gc_time:                         0
% 23.79/3.52  parsing_time:                           0.033
% 23.79/3.52  unif_index_cands_time:                  0.
% 23.79/3.52  unif_index_add_time:                    0.
% 23.79/3.52  orderings_time:                         0.
% 23.79/3.52  out_proof_time:                         0.014
% 23.79/3.52  total_time:                             2.841
% 23.79/3.52  num_of_symbols:                         54
% 23.79/3.52  num_of_terms:                           111318
% 23.79/3.52  
% 23.79/3.52  ------ Preprocessing
% 23.79/3.52  
% 23.79/3.52  num_of_splits:                          0
% 23.79/3.52  num_of_split_atoms:                     0
% 23.79/3.52  num_of_reused_defs:                     0
% 23.79/3.52  num_eq_ax_congr_red:                    39
% 23.79/3.52  num_of_sem_filtered_clauses:            1
% 23.79/3.52  num_of_subtypes:                        0
% 23.79/3.52  monotx_restored_types:                  0
% 23.79/3.52  sat_num_of_epr_types:                   0
% 23.79/3.52  sat_num_of_non_cyclic_types:            0
% 23.79/3.52  sat_guarded_non_collapsed_types:        0
% 23.79/3.52  num_pure_diseq_elim:                    0
% 23.79/3.52  simp_replaced_by:                       0
% 23.79/3.52  res_preprocessed:                       217
% 23.79/3.52  prep_upred:                             0
% 23.79/3.52  prep_unflattend:                        64
% 23.79/3.52  smt_new_axioms:                         0
% 23.79/3.52  pred_elim_cands:                        5
% 23.79/3.52  pred_elim:                              0
% 23.79/3.52  pred_elim_cl:                           0
% 23.79/3.52  pred_elim_cycles:                       2
% 23.79/3.52  merged_defs:                            8
% 23.79/3.52  merged_defs_ncl:                        0
% 23.79/3.52  bin_hyper_res:                          10
% 23.79/3.52  prep_cycles:                            4
% 23.79/3.52  pred_elim_time:                         0.018
% 23.79/3.52  splitting_time:                         0.
% 23.79/3.52  sem_filter_time:                        0.
% 23.79/3.52  monotx_time:                            0.
% 23.79/3.52  subtype_inf_time:                       0.
% 23.79/3.52  
% 23.79/3.52  ------ Problem properties
% 23.79/3.52  
% 23.79/3.52  clauses:                                49
% 23.79/3.52  conjectures:                            4
% 23.79/3.52  epr:                                    25
% 23.79/3.52  horn:                                   38
% 23.79/3.52  ground:                                 11
% 23.79/3.52  unary:                                  19
% 23.79/3.52  binary:                                 14
% 23.79/3.52  lits:                                   101
% 23.79/3.52  lits_eq:                                10
% 23.79/3.52  fd_pure:                                0
% 23.79/3.52  fd_pseudo:                              0
% 23.79/3.52  fd_cond:                                0
% 23.79/3.52  fd_pseudo_cond:                         6
% 23.79/3.52  ac_symbols:                             0
% 23.79/3.52  
% 23.79/3.52  ------ Propositional Solver
% 23.79/3.52  
% 23.79/3.52  prop_solver_calls:                      53
% 23.79/3.52  prop_fast_solver_calls:                 2001
% 23.79/3.52  smt_solver_calls:                       0
% 23.79/3.52  smt_fast_solver_calls:                  0
% 23.79/3.52  prop_num_of_clauses:                    50071
% 23.79/3.52  prop_preprocess_simplified:             60625
% 23.79/3.52  prop_fo_subsumed:                       40
% 23.79/3.52  prop_solver_time:                       0.
% 23.79/3.52  smt_solver_time:                        0.
% 23.79/3.52  smt_fast_solver_time:                   0.
% 23.79/3.52  prop_fast_solver_time:                  0.
% 23.79/3.52  prop_unsat_core_time:                   0.004
% 23.79/3.52  
% 23.79/3.52  ------ QBF
% 23.79/3.52  
% 23.79/3.52  qbf_q_res:                              0
% 23.79/3.52  qbf_num_tautologies:                    0
% 23.79/3.52  qbf_prep_cycles:                        0
% 23.79/3.52  
% 23.79/3.52  ------ BMC1
% 23.79/3.52  
% 23.79/3.52  bmc1_current_bound:                     -1
% 23.79/3.52  bmc1_last_solved_bound:                 -1
% 23.79/3.52  bmc1_unsat_core_size:                   -1
% 23.79/3.52  bmc1_unsat_core_parents_size:           -1
% 23.79/3.52  bmc1_merge_next_fun:                    0
% 23.79/3.52  bmc1_unsat_core_clauses_time:           0.
% 23.79/3.52  
% 23.79/3.52  ------ Instantiation
% 23.79/3.52  
% 23.79/3.52  inst_num_of_clauses:                    865
% 23.79/3.52  inst_num_in_passive:                    301
% 23.79/3.52  inst_num_in_active:                     2768
% 23.79/3.52  inst_num_in_unprocessed:                291
% 23.79/3.52  inst_num_of_loops:                      3273
% 23.79/3.52  inst_num_of_learning_restarts:          1
% 23.79/3.52  inst_num_moves_active_passive:          504
% 23.79/3.52  inst_lit_activity:                      0
% 23.79/3.52  inst_lit_activity_moves:                0
% 23.79/3.52  inst_num_tautologies:                   0
% 23.79/3.52  inst_num_prop_implied:                  0
% 23.79/3.52  inst_num_existing_simplified:           0
% 23.79/3.52  inst_num_eq_res_simplified:             0
% 23.79/3.52  inst_num_child_elim:                    0
% 23.79/3.52  inst_num_of_dismatching_blockings:      6321
% 23.79/3.52  inst_num_of_non_proper_insts:           8840
% 23.79/3.52  inst_num_of_duplicates:                 0
% 23.79/3.52  inst_inst_num_from_inst_to_res:         0
% 23.79/3.52  inst_dismatching_checking_time:         0.
% 23.79/3.52  
% 23.79/3.52  ------ Resolution
% 23.79/3.52  
% 23.79/3.52  res_num_of_clauses:                     59
% 23.79/3.52  res_num_in_passive:                     59
% 23.79/3.52  res_num_in_active:                      0
% 23.79/3.52  res_num_of_loops:                       221
% 23.79/3.52  res_forward_subset_subsumed:            1162
% 23.79/3.52  res_backward_subset_subsumed:           14
% 23.79/3.52  res_forward_subsumed:                   4
% 23.79/3.52  res_backward_subsumed:                  0
% 23.79/3.52  res_forward_subsumption_resolution:     2
% 23.79/3.52  res_backward_subsumption_resolution:    0
% 23.79/3.52  res_clause_to_clause_subsumption:       78585
% 23.79/3.52  res_orphan_elimination:                 0
% 23.79/3.52  res_tautology_del:                      713
% 23.79/3.52  res_num_eq_res_simplified:              0
% 23.79/3.52  res_num_sel_changes:                    0
% 23.79/3.52  res_moves_from_active_to_pass:          0
% 23.79/3.52  
% 23.79/3.52  ------ Superposition
% 23.79/3.52  
% 23.79/3.52  sup_time_total:                         0.
% 23.79/3.52  sup_time_generating:                    0.
% 23.79/3.52  sup_time_sim_full:                      0.
% 23.79/3.52  sup_time_sim_immed:                     0.
% 23.79/3.52  
% 23.79/3.52  sup_num_of_clauses:                     9078
% 23.79/3.52  sup_num_in_active:                      628
% 23.79/3.52  sup_num_in_passive:                     8450
% 23.79/3.52  sup_num_of_loops:                       654
% 23.79/3.52  sup_fw_superposition:                   9403
% 23.79/3.52  sup_bw_superposition:                   8986
% 23.79/3.52  sup_immediate_simplified:               6418
% 23.79/3.52  sup_given_eliminated:                   0
% 23.79/3.52  comparisons_done:                       0
% 23.79/3.52  comparisons_avoided:                    0
% 23.79/3.52  
% 23.79/3.52  ------ Simplifications
% 23.79/3.52  
% 23.79/3.52  
% 23.79/3.52  sim_fw_subset_subsumed:                 318
% 23.79/3.52  sim_bw_subset_subsumed:                 24
% 23.79/3.52  sim_fw_subsumed:                        2835
% 23.79/3.52  sim_bw_subsumed:                        227
% 23.79/3.52  sim_fw_subsumption_res:                 0
% 23.79/3.52  sim_bw_subsumption_res:                 0
% 23.79/3.52  sim_tautology_del:                      439
% 23.79/3.52  sim_eq_tautology_del:                   282
% 23.79/3.52  sim_eq_res_simp:                        0
% 23.79/3.52  sim_fw_demodulated:                     2128
% 23.79/3.52  sim_bw_demodulated:                     60
% 23.79/3.52  sim_light_normalised:                   1555
% 23.79/3.52  sim_joinable_taut:                      0
% 23.79/3.52  sim_joinable_simp:                      0
% 23.79/3.52  sim_ac_normalised:                      0
% 23.79/3.52  sim_smt_subsumption:                    0
% 23.79/3.52  
%------------------------------------------------------------------------------
