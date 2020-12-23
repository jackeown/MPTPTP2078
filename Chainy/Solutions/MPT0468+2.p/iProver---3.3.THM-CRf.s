%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0468+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:40 EST 2020

% Result     : Theorem 18.95s
% Output     : CNFRefutation 18.95s
% Verified   : 
% Statistics : Number of formulae       :   43 (  57 expanded)
%              Number of clauses        :   12 (  12 expanded)
%              Number of leaves         :    9 (  14 expanded)
%              Depth                    :    8
%              Number of atoms          :  128 ( 172 expanded)
%              Number of equality atoms :   26 (  42 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f148,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f807,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f148])).

fof(f1815,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f807])).

fof(f698,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f699,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
         => k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f698])).

fof(f1201,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f699])).

fof(f1202,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f1201])).

fof(f1617,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
        & v1_relat_1(X0) )
   => ( k1_xboole_0 != sK147
      & ! [X2,X1] : ~ r2_hidden(k4_tarski(X1,X2),sK147)
      & v1_relat_1(sK147) ) ),
    introduced(choice_axiom,[])).

fof(f1618,plain,
    ( k1_xboole_0 != sK147
    & ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),sK147)
    & v1_relat_1(sK147) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK147])],[f1202,f1617])).

fof(f2709,plain,(
    ! [X2,X1] : ~ r2_hidden(k4_tarski(X1,X2),sK147) ),
    inference(cnf_transformation,[],[f1618])).

fof(f641,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( X0 = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X0)
              <=> r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1139,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( X0 = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X0)
              <=> r2_hidden(k4_tarski(X2,X3),X1) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f641])).

fof(f1581,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | r2_hidden(k4_tarski(X2,X3),X0) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1139])).

fof(f1582,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | r2_hidden(k4_tarski(X2,X3),X0) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) )
                  & ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f1581])).

fof(f1583,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
            | ~ r2_hidden(k4_tarski(X2,X3),X0) )
          & ( r2_hidden(k4_tarski(X2,X3),X1)
            | r2_hidden(k4_tarski(X2,X3),X0) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK128(X0,X1),sK129(X0,X1)),X1)
          | ~ r2_hidden(k4_tarski(sK128(X0,X1),sK129(X0,X1)),X0) )
        & ( r2_hidden(k4_tarski(sK128(X0,X1),sK129(X0,X1)),X1)
          | r2_hidden(k4_tarski(sK128(X0,X1),sK129(X0,X1)),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1584,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ( ( ~ r2_hidden(k4_tarski(sK128(X0,X1),sK129(X0,X1)),X1)
                  | ~ r2_hidden(k4_tarski(sK128(X0,X1),sK129(X0,X1)),X0) )
                & ( r2_hidden(k4_tarski(sK128(X0,X1),sK129(X0,X1)),X1)
                  | r2_hidden(k4_tarski(sK128(X0,X1),sK129(X0,X1)),X0) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) )
                  & ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK128,sK129])],[f1582,f1583])).

fof(f2630,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(k4_tarski(sK128(X0,X1),sK129(X0,X1)),X1)
      | r2_hidden(k4_tarski(sK128(X0,X1),sK129(X0,X1)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1584])).

fof(f476,axiom,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2375,plain,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f476])).

fof(f458,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2312,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f458])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1626,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f2721,plain,(
    ! [X0] : o_0_0_xboole_0 = k1_subset_1(X0) ),
    inference(definition_unfolding,[],[f2312,f1626])).

fof(f3138,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f2375,f2721])).

fof(f638,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1136,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f638])).

fof(f2623,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1136])).

fof(f2710,plain,(
    k1_xboole_0 != sK147 ),
    inference(cnf_transformation,[],[f1618])).

fof(f3230,plain,(
    o_0_0_xboole_0 != sK147 ),
    inference(definition_unfolding,[],[f2710,f1626])).

fof(f2708,plain,(
    v1_relat_1(sK147) ),
    inference(cnf_transformation,[],[f1618])).

cnf(c_195,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f1815])).

cnf(c_53978,plain,
    ( ~ r2_hidden(k4_tarski(sK128(sK147,o_0_0_xboole_0),sK129(sK147,o_0_0_xboole_0)),o_0_0_xboole_0)
    | ~ v1_xboole_0(o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_195])).

cnf(c_1076,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK147) ),
    inference(cnf_transformation,[],[f2709])).

cnf(c_50049,plain,
    ( ~ r2_hidden(k4_tarski(sK128(sK147,o_0_0_xboole_0),sK129(sK147,o_0_0_xboole_0)),sK147) ),
    inference(instantiation,[status(thm)],[c_1076])).

cnf(c_996,plain,
    ( r2_hidden(k4_tarski(sK128(X0,X1),sK129(X0,X1)),X1)
    | r2_hidden(k4_tarski(sK128(X0,X1),sK129(X0,X1)),X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f2630])).

cnf(c_46661,plain,
    ( r2_hidden(k4_tarski(sK128(sK147,o_0_0_xboole_0),sK129(sK147,o_0_0_xboole_0)),sK147)
    | r2_hidden(k4_tarski(sK128(sK147,o_0_0_xboole_0),sK129(sK147,o_0_0_xboole_0)),o_0_0_xboole_0)
    | ~ v1_relat_1(sK147)
    | ~ v1_relat_1(o_0_0_xboole_0)
    | o_0_0_xboole_0 = sK147 ),
    inference(instantiation,[status(thm)],[c_996])).

cnf(c_743,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3138])).

cnf(c_990,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f2623])).

cnf(c_1315,plain,
    ( v1_relat_1(o_0_0_xboole_0)
    | ~ v1_xboole_0(o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_990])).

cnf(c_1075,negated_conjecture,
    ( o_0_0_xboole_0 != sK147 ),
    inference(cnf_transformation,[],[f3230])).

cnf(c_1077,negated_conjecture,
    ( v1_relat_1(sK147) ),
    inference(cnf_transformation,[],[f2708])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_53978,c_50049,c_46661,c_743,c_1315,c_1075,c_1077])).

%------------------------------------------------------------------------------
