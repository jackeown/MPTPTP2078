%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0757+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:52 EST 2020

% Result     : Theorem 27.06s
% Output     : CNFRefutation 27.06s
% Verified   : 
% Statistics : Number of formulae       :   30 (  58 expanded)
%              Number of clauses        :   10 (  10 expanded)
%              Number of leaves         :    5 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :  105 ( 277 expanded)
%              Number of equality atoms :   20 (  56 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1095,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => r3_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2184,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r3_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1095])).

fof(f4760,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f2184])).

fof(f52,axiom,(
    ! [X0,X1] :
      ( ~ ( ~ r2_xboole_0(X1,X0)
          & X0 != X1
          & ~ r2_xboole_0(X0,X1) )
    <=> r3_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1162,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X1,X0)
        | X0 = X1
        | r2_xboole_0(X0,X1) )
    <=> r3_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f52])).

fof(f2301,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X1,X0)
        | X0 = X1
        | r2_xboole_0(X0,X1)
        | ~ r3_xboole_0(X0,X1) )
      & ( r3_xboole_0(X0,X1)
        | ( ~ r2_xboole_0(X1,X0)
          & X0 != X1
          & ~ r2_xboole_0(X0,X1) ) ) ) ),
    inference(nnf_transformation,[],[f1162])).

fof(f2302,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X1,X0)
        | X0 = X1
        | r2_xboole_0(X0,X1)
        | ~ r3_xboole_0(X0,X1) )
      & ( r3_xboole_0(X0,X1)
        | ( ~ r2_xboole_0(X1,X0)
          & X0 != X1
          & ~ r2_xboole_0(X0,X1) ) ) ) ),
    inference(flattening,[],[f2301])).

fof(f3038,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X1,X0)
      | X0 = X1
      | r2_xboole_0(X0,X1)
      | ~ r3_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2302])).

fof(f1117,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_xboole_0(X1,X0)
              & X0 != X1
              & ~ r2_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1118,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ~ ( ~ r2_xboole_0(X1,X0)
                & X0 != X1
                & ~ r2_xboole_0(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f1117])).

fof(f2213,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_xboole_0(X1,X0)
          & X0 != X1
          & ~ r2_xboole_0(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1118])).

fof(f2214,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_xboole_0(X1,X0)
          & X0 != X1
          & ~ r2_xboole_0(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f2213])).

fof(f2947,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_xboole_0(X1,X0)
          & X0 != X1
          & ~ r2_xboole_0(X0,X1)
          & v3_ordinal1(X1) )
     => ( ~ r2_xboole_0(sK271,X0)
        & sK271 != X0
        & ~ r2_xboole_0(X0,sK271)
        & v3_ordinal1(sK271) ) ) ),
    introduced(choice_axiom,[])).

fof(f2946,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r2_xboole_0(X1,X0)
            & X0 != X1
            & ~ r2_xboole_0(X0,X1)
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ~ r2_xboole_0(X1,sK270)
          & sK270 != X1
          & ~ r2_xboole_0(sK270,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK270) ) ),
    introduced(choice_axiom,[])).

fof(f2948,plain,
    ( ~ r2_xboole_0(sK271,sK270)
    & sK270 != sK271
    & ~ r2_xboole_0(sK270,sK271)
    & v3_ordinal1(sK271)
    & v3_ordinal1(sK270) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK270,sK271])],[f2214,f2947,f2946])).

fof(f4821,plain,(
    ~ r2_xboole_0(sK271,sK270) ),
    inference(cnf_transformation,[],[f2948])).

fof(f4820,plain,(
    sK270 != sK271 ),
    inference(cnf_transformation,[],[f2948])).

fof(f4819,plain,(
    ~ r2_xboole_0(sK270,sK271) ),
    inference(cnf_transformation,[],[f2948])).

fof(f4818,plain,(
    v3_ordinal1(sK271) ),
    inference(cnf_transformation,[],[f2948])).

fof(f4817,plain,(
    v3_ordinal1(sK270) ),
    inference(cnf_transformation,[],[f2948])).

cnf(c_1796,plain,
    ( r3_xboole_0(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f4760])).

cnf(c_89640,plain,
    ( r3_xboole_0(sK271,sK270)
    | ~ v3_ordinal1(sK270)
    | ~ v3_ordinal1(sK271) ),
    inference(instantiation,[status(thm)],[c_1796])).

cnf(c_86,plain,
    ( ~ r3_xboole_0(X0,X1)
    | r2_xboole_0(X1,X0)
    | r2_xboole_0(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f3038])).

cnf(c_84376,plain,
    ( ~ r3_xboole_0(sK271,sK270)
    | r2_xboole_0(sK270,sK271)
    | r2_xboole_0(sK271,sK270)
    | sK270 = sK271 ),
    inference(instantiation,[status(thm)],[c_86])).

cnf(c_1853,negated_conjecture,
    ( ~ r2_xboole_0(sK271,sK270) ),
    inference(cnf_transformation,[],[f4821])).

cnf(c_1854,negated_conjecture,
    ( sK270 != sK271 ),
    inference(cnf_transformation,[],[f4820])).

cnf(c_1855,negated_conjecture,
    ( ~ r2_xboole_0(sK270,sK271) ),
    inference(cnf_transformation,[],[f4819])).

cnf(c_1856,negated_conjecture,
    ( v3_ordinal1(sK271) ),
    inference(cnf_transformation,[],[f4818])).

cnf(c_1857,negated_conjecture,
    ( v3_ordinal1(sK270) ),
    inference(cnf_transformation,[],[f4817])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_89640,c_84376,c_1853,c_1854,c_1855,c_1856,c_1857])).

%------------------------------------------------------------------------------
