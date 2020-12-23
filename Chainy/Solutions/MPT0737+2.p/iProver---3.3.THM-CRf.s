%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0737+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:51 EST 2020

% Result     : Theorem 19.15s
% Output     : CNFRefutation 19.15s
% Verified   : 
% Statistics : Number of formulae       :   36 (  65 expanded)
%              Number of clauses        :   13 (  15 expanded)
%              Number of leaves         :    6 (  17 expanded)
%              Depth                    :    9
%              Number of atoms          :  112 ( 221 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   5 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f38,axiom,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
    <=> ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2202,plain,(
    ! [X0,X1] :
      ( ( r3_xboole_0(X0,X1)
        | ( ~ r1_tarski(X1,X0)
          & ~ r1_tarski(X0,X1) ) )
      & ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1)
        | ~ r3_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f2203,plain,(
    ! [X0,X1] :
      ( ( r3_xboole_0(X0,X1)
        | ( ~ r1_tarski(X1,X0)
          & ~ r1_tarski(X0,X1) ) )
      & ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1)
        | ~ r3_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f2202])).

fof(f2858,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f2203])).

fof(f1076,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => r3_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1077,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => r3_xboole_0(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f1076])).

fof(f2121,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r3_xboole_0(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1077])).

fof(f2785,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r3_xboole_0(X0,X1)
          & v3_ordinal1(X1) )
     => ( ~ r3_xboole_0(X0,sK240)
        & v3_ordinal1(sK240) ) ) ),
    introduced(choice_axiom,[])).

fof(f2784,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r3_xboole_0(X0,X1)
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ~ r3_xboole_0(sK239,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK239) ) ),
    introduced(choice_axiom,[])).

fof(f2786,plain,
    ( ~ r3_xboole_0(sK239,sK240)
    & v3_ordinal1(sK240)
    & v3_ordinal1(sK239) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK239,sK240])],[f2121,f2785,f2784])).

fof(f4536,plain,(
    ~ r3_xboole_0(sK239,sK240) ),
    inference(cnf_transformation,[],[f2786])).

fof(f1065,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2106,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1065])).

fof(f2107,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f2106])).

fof(f2781,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f2107])).

fof(f4520,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f2781])).

fof(f1056,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2098,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1056])).

fof(f2099,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f2098])).

fof(f4505,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f2099])).

fof(f2857,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2203])).

fof(f4535,plain,(
    v3_ordinal1(sK240) ),
    inference(cnf_transformation,[],[f2786])).

fof(f4534,plain,(
    v3_ordinal1(sK239) ),
    inference(cnf_transformation,[],[f2786])).

cnf(c_70,plain,
    ( r3_xboole_0(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2858])).

cnf(c_1732,negated_conjecture,
    ( ~ r3_xboole_0(sK239,sK240) ),
    inference(cnf_transformation,[],[f4536])).

cnf(c_61880,plain,
    ( ~ r1_tarski(sK240,sK239) ),
    inference(resolution,[status(thm)],[c_70,c_1732])).

cnf(c_1719,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f4520])).

cnf(c_1704,plain,
    ( r1_ordinal1(X0,X1)
    | r1_ordinal1(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f4505])).

cnf(c_61842,plain,
    ( r1_ordinal1(X0,X1)
    | r1_tarski(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(resolution,[status(thm)],[c_1719,c_1704])).

cnf(c_61856,plain,
    ( r1_tarski(X0,X1)
    | r1_tarski(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(resolution,[status(thm)],[c_61842,c_1719])).

cnf(c_61886,plain,
    ( r1_tarski(sK239,sK240)
    | ~ v3_ordinal1(sK240)
    | ~ v3_ordinal1(sK239) ),
    inference(resolution,[status(thm)],[c_61880,c_61856])).

cnf(c_71,plain,
    ( r3_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2857])).

cnf(c_61626,plain,
    ( r3_xboole_0(sK239,sK240)
    | ~ r1_tarski(sK239,sK240) ),
    inference(instantiation,[status(thm)],[c_71])).

cnf(c_1733,negated_conjecture,
    ( v3_ordinal1(sK240) ),
    inference(cnf_transformation,[],[f4535])).

cnf(c_1734,negated_conjecture,
    ( v3_ordinal1(sK239) ),
    inference(cnf_transformation,[],[f4534])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_61886,c_61626,c_1732,c_1733,c_1734])).

%------------------------------------------------------------------------------
