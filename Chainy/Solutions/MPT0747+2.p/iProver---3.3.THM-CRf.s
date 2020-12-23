%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0747+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:51 EST 2020

% Result     : Theorem 31.15s
% Output     : CNFRefutation 31.15s
% Verified   : 
% Statistics : Number of formulae       :   42 (  74 expanded)
%              Number of clauses        :   21 (  22 expanded)
%              Number of leaves         :    6 (  19 expanded)
%              Depth                    :   11
%              Number of atoms          :  103 ( 223 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1091,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ( v3_ordinal1(X1)
           => ~ r1_tarski(X0,X1) )
        & ! [X1] :
            ( r2_hidden(X1,X0)
           => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1114,plain,(
    ! [X0] :
      ~ ( ! [X1] :
            ( v3_ordinal1(X1)
           => ~ r1_tarski(X0,X1) )
        & ! [X2] :
            ( r2_hidden(X2,X0)
           => v3_ordinal1(X2) ) ) ),
    inference(rectify,[],[f1091])).

fof(f2152,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r1_tarski(X0,X1)
          & v3_ordinal1(X1) )
      | ? [X2] :
          ( ~ v3_ordinal1(X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1114])).

fof(f2829,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ~ v3_ordinal1(X2)
          & r2_hidden(X2,X0) )
     => ( ~ v3_ordinal1(sK244(X0))
        & r2_hidden(sK244(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f2828,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r1_tarski(X0,X1)
          & v3_ordinal1(X1) )
     => ( r1_tarski(X0,sK243(X0))
        & v3_ordinal1(sK243(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2830,plain,(
    ! [X0] :
      ( ( r1_tarski(X0,sK243(X0))
        & v3_ordinal1(sK243(X0)) )
      | ( ~ v3_ordinal1(sK244(X0))
        & r2_hidden(sK244(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK243,sK244])],[f2152,f2829,f2828])).

fof(f4610,plain,(
    ! [X0] :
      ( r1_tarski(X0,sK243(X0))
      | r2_hidden(sK244(X0),X0) ) ),
    inference(cnf_transformation,[],[f2830])).

fof(f1092,conjecture,(
    ! [X0] :
      ~ ! [X1] :
          ( r2_hidden(X1,X0)
        <=> v3_ordinal1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1093,negated_conjecture,(
    ~ ! [X0] :
        ~ ! [X1] :
            ( r2_hidden(X1,X0)
          <=> v3_ordinal1(X1) ) ),
    inference(negated_conjecture,[],[f1092])).

fof(f2153,plain,(
    ? [X0] :
    ! [X1] :
      ( r2_hidden(X1,X0)
    <=> v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f1093])).

fof(f2831,plain,(
    ? [X0] :
    ! [X1] :
      ( ( r2_hidden(X1,X0)
        | ~ v3_ordinal1(X1) )
      & ( v3_ordinal1(X1)
        | ~ r2_hidden(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f2153])).

fof(f2832,plain,
    ( ? [X0] :
      ! [X1] :
        ( ( r2_hidden(X1,X0)
          | ~ v3_ordinal1(X1) )
        & ( v3_ordinal1(X1)
          | ~ r2_hidden(X1,X0) ) )
   => ! [X1] :
        ( ( r2_hidden(X1,sK245)
          | ~ v3_ordinal1(X1) )
        & ( v3_ordinal1(X1)
          | ~ r2_hidden(X1,sK245) ) ) ),
    introduced(choice_axiom,[])).

fof(f2833,plain,(
    ! [X1] :
      ( ( r2_hidden(X1,sK245)
        | ~ v3_ordinal1(X1) )
      & ( v3_ordinal1(X1)
        | ~ r2_hidden(X1,sK245) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK245])],[f2831,f2832])).

fof(f4613,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK245)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f2833])).

fof(f4612,plain,(
    ! [X1] :
      ( v3_ordinal1(X1)
      | ~ r2_hidden(X1,sK245) ) ),
    inference(cnf_transformation,[],[f2833])).

fof(f1098,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2158,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1098])).

fof(f4618,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f2158])).

fof(f4611,plain,(
    ! [X0] :
      ( r1_tarski(X0,sK243(X0))
      | ~ v3_ordinal1(sK244(X0)) ) ),
    inference(cnf_transformation,[],[f2830])).

fof(f4608,plain,(
    ! [X0] :
      ( v3_ordinal1(sK243(X0))
      | r2_hidden(sK244(X0),X0) ) ),
    inference(cnf_transformation,[],[f2830])).

fof(f4609,plain,(
    ! [X0] :
      ( v3_ordinal1(sK243(X0))
      | ~ v3_ordinal1(sK244(X0)) ) ),
    inference(cnf_transformation,[],[f2830])).

cnf(c_1760,plain,
    ( r1_tarski(X0,sK243(X0))
    | r2_hidden(sK244(X0),X0) ),
    inference(cnf_transformation,[],[f4610])).

cnf(c_130094,plain,
    ( r1_tarski(sK245,sK243(sK245))
    | r2_hidden(sK244(sK245),sK245) ),
    inference(instantiation,[status(thm)],[c_1760])).

cnf(c_1763,negated_conjecture,
    ( r2_hidden(X0,sK245)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f4613])).

cnf(c_129201,plain,
    ( r2_hidden(sK243(sK245),sK245)
    | ~ v3_ordinal1(sK243(sK245)) ),
    inference(instantiation,[status(thm)],[c_1763])).

cnf(c_1764,negated_conjecture,
    ( ~ r2_hidden(X0,sK245)
    | v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f4612])).

cnf(c_88911,plain,
    ( ~ r2_hidden(sK244(X0),sK245)
    | v3_ordinal1(sK244(X0)) ),
    inference(instantiation,[status(thm)],[c_1764])).

cnf(c_122683,plain,
    ( ~ r2_hidden(sK244(sK245),sK245)
    | v3_ordinal1(sK244(sK245)) ),
    inference(instantiation,[status(thm)],[c_88911])).

cnf(c_1769,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f4618])).

cnf(c_89489,plain,
    ( ~ r1_tarski(sK245,X0)
    | ~ r2_hidden(X0,sK245) ),
    inference(instantiation,[status(thm)],[c_1769])).

cnf(c_104293,plain,
    ( ~ r1_tarski(sK245,sK243(sK245))
    | ~ r2_hidden(sK243(sK245),sK245) ),
    inference(instantiation,[status(thm)],[c_89489])).

cnf(c_1759,plain,
    ( r1_tarski(X0,sK243(X0))
    | ~ v3_ordinal1(sK244(X0)) ),
    inference(cnf_transformation,[],[f4611])).

cnf(c_104290,plain,
    ( r1_tarski(sK245,sK243(sK245))
    | ~ v3_ordinal1(sK244(sK245)) ),
    inference(instantiation,[status(thm)],[c_1759])).

cnf(c_1762,plain,
    ( r2_hidden(sK244(X0),X0)
    | v3_ordinal1(sK243(X0)) ),
    inference(cnf_transformation,[],[f4608])).

cnf(c_75067,plain,
    ( r2_hidden(sK244(X0),X0) = iProver_top
    | v3_ordinal1(sK243(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1762])).

cnf(c_75065,plain,
    ( r2_hidden(X0,sK245) != iProver_top
    | v3_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1764])).

cnf(c_89026,plain,
    ( v3_ordinal1(sK244(sK245)) = iProver_top
    | v3_ordinal1(sK243(sK245)) = iProver_top ),
    inference(superposition,[status(thm)],[c_75067,c_75065])).

cnf(c_1761,plain,
    ( ~ v3_ordinal1(sK244(X0))
    | v3_ordinal1(sK243(X0)) ),
    inference(cnf_transformation,[],[f4609])).

cnf(c_75068,plain,
    ( v3_ordinal1(sK244(X0)) != iProver_top
    | v3_ordinal1(sK243(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1761])).

cnf(c_89963,plain,
    ( v3_ordinal1(sK243(sK245)) = iProver_top ),
    inference(superposition,[status(thm)],[c_89026,c_75068])).

cnf(c_89964,plain,
    ( v3_ordinal1(sK243(sK245)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_89963])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_130094,c_129201,c_122683,c_104293,c_104290,c_89964])).

%------------------------------------------------------------------------------
