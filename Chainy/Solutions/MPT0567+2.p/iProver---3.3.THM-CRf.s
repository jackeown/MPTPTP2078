%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0567+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:45 EST 2020

% Result     : Theorem 23.15s
% Output     : CNFRefutation 23.15s
% Verified   : 
% Statistics : Number of formulae       :   42 (  53 expanded)
%              Number of clauses        :   10 (  10 expanded)
%              Number of leaves         :   10 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :  105 ( 123 expanded)
%              Number of equality atoms :   21 (  33 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :    9 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f148,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f931,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f148])).

fof(f2130,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f931])).

fof(f750,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1380,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f750])).

fof(f1912,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f1380])).

fof(f1913,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f1912])).

fof(f1914,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK158(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK158(X0,X1,X2)),X2)
        & r2_hidden(sK158(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1915,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK158(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK158(X0,X1,X2)),X2)
            & r2_hidden(sK158(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK158])],[f1913,f1914])).

fof(f3106,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK158(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1915])).

fof(f36,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f852,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f36])).

fof(f1528,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK22(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1529,plain,(
    ! [X0] :
      ( r2_hidden(sK22(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK22])],[f852,f1528])).

fof(f1999,plain,(
    ! [X0] :
      ( r2_hidden(sK22(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1529])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1941,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f3242,plain,(
    ! [X0] :
      ( r2_hidden(sK22(X0),X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f1999,f1941])).

fof(f476,axiom,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2690,plain,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f476])).

fof(f458,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2627,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f458])).

fof(f3211,plain,(
    ! [X0] : o_0_0_xboole_0 = k1_subset_1(X0) ),
    inference(definition_unfolding,[],[f2627,f1941])).

fof(f3628,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f2690,f3211])).

fof(f755,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f756,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f755])).

fof(f1385,plain,(
    ? [X0] :
      ( k1_xboole_0 != k10_relat_1(X0,k1_xboole_0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f756])).

fof(f1916,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k10_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
   => ( k1_xboole_0 != k10_relat_1(sK159,k1_xboole_0)
      & v1_relat_1(sK159) ) ),
    introduced(choice_axiom,[])).

fof(f1917,plain,
    ( k1_xboole_0 != k10_relat_1(sK159,k1_xboole_0)
    & v1_relat_1(sK159) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK159])],[f1385,f1916])).

fof(f3113,plain,(
    k1_xboole_0 != k10_relat_1(sK159,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1917])).

fof(f3733,plain,(
    o_0_0_xboole_0 != k10_relat_1(sK159,o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f3113,f1941,f1941])).

fof(f3112,plain,(
    v1_relat_1(sK159) ),
    inference(cnf_transformation,[],[f1917])).

cnf(c_195,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f2130])).

cnf(c_73998,plain,
    ( ~ r2_hidden(sK158(sK22(k10_relat_1(sK159,o_0_0_xboole_0)),o_0_0_xboole_0,sK159),o_0_0_xboole_0)
    | ~ v1_xboole_0(o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_195])).

cnf(c_1157,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK158(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f3106])).

cnf(c_56429,plain,
    ( r2_hidden(sK158(sK22(k10_relat_1(sK159,o_0_0_xboole_0)),o_0_0_xboole_0,sK159),o_0_0_xboole_0)
    | ~ r2_hidden(sK22(k10_relat_1(sK159,o_0_0_xboole_0)),k10_relat_1(sK159,o_0_0_xboole_0))
    | ~ v1_relat_1(sK159) ),
    inference(instantiation,[status(thm)],[c_1157])).

cnf(c_66,plain,
    ( r2_hidden(sK22(X0),X0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f3242])).

cnf(c_43448,plain,
    ( r2_hidden(sK22(k10_relat_1(sK159,o_0_0_xboole_0)),k10_relat_1(sK159,o_0_0_xboole_0))
    | o_0_0_xboole_0 = k10_relat_1(sK159,o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_66])).

cnf(c_743,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3628])).

cnf(c_1164,negated_conjecture,
    ( o_0_0_xboole_0 != k10_relat_1(sK159,o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3733])).

cnf(c_1165,negated_conjecture,
    ( v1_relat_1(sK159) ),
    inference(cnf_transformation,[],[f3112])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_73998,c_56429,c_43448,c_743,c_1164,c_1165])).

%------------------------------------------------------------------------------
