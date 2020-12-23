%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0570+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:46 EST 2020

% Result     : Theorem 29.93s
% Output     : CNFRefutation 29.93s
% Verified   : 
% Statistics : Number of formulae       :   50 (  74 expanded)
%              Number of clauses        :   18 (  18 expanded)
%              Number of leaves         :    7 (  16 expanded)
%              Depth                    :   10
%              Number of atoms          :  136 ( 226 expanded)
%              Number of equality atoms :   49 (  97 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f28,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f849,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f1987,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f849])).

fof(f133,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f917,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f133])).

fof(f918,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f917])).

fof(f2123,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f918])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1951,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f3342,plain,(
    ! [X2,X0,X1] :
      ( o_0_0_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f2123,f1951])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1539,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f1540,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f1539])).

fof(f2010,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1540])).

fof(f3798,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f2010])).

fof(f760,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
          & r1_tarski(X0,k2_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f761,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
            & r1_tarski(X0,k2_relat_1(X1))
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f760])).

fof(f1393,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      & r1_tarski(X0,k2_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f761])).

fof(f1394,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      & r1_tarski(X0,k2_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f1393])).

fof(f1926,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k10_relat_1(X1,X0)
        & r1_tarski(X0,k2_relat_1(X1))
        & k1_xboole_0 != X0
        & v1_relat_1(X1) )
   => ( k1_xboole_0 = k10_relat_1(sK160,sK159)
      & r1_tarski(sK159,k2_relat_1(sK160))
      & k1_xboole_0 != sK159
      & v1_relat_1(sK160) ) ),
    introduced(choice_axiom,[])).

fof(f1927,plain,
    ( k1_xboole_0 = k10_relat_1(sK160,sK159)
    & r1_tarski(sK159,k2_relat_1(sK160))
    & k1_xboole_0 != sK159
    & v1_relat_1(sK160) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK159,sK160])],[f1394,f1926])).

fof(f3131,plain,(
    k1_xboole_0 = k10_relat_1(sK160,sK159) ),
    inference(cnf_transformation,[],[f1927])).

fof(f3756,plain,(
    o_0_0_xboole_0 = k10_relat_1(sK160,sK159) ),
    inference(definition_unfolding,[],[f3131,f1951])).

fof(f759,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1392,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f759])).

fof(f1925,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k10_relat_1(X1,X0)
          | ~ r1_xboole_0(k2_relat_1(X1),X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1392])).

fof(f3126,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_relat_1(X1),X0)
      | k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1925])).

fof(f3755,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_relat_1(X1),X0)
      | o_0_0_xboole_0 != k10_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f3126,f1951])).

fof(f3130,plain,(
    r1_tarski(sK159,k2_relat_1(sK160)) ),
    inference(cnf_transformation,[],[f1927])).

fof(f3129,plain,(
    k1_xboole_0 != sK159 ),
    inference(cnf_transformation,[],[f1927])).

fof(f3757,plain,(
    o_0_0_xboole_0 != sK159 ),
    inference(definition_unfolding,[],[f3129,f1951])).

fof(f3128,plain,(
    v1_relat_1(sK160) ),
    inference(cnf_transformation,[],[f1927])).

cnf(c_44,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1987])).

cnf(c_73041,plain,
    ( r1_xboole_0(X0,k2_relat_1(sK160))
    | ~ r1_xboole_0(k2_relat_1(sK160),X0) ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_119798,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK160),sK159)
    | r1_xboole_0(sK159,k2_relat_1(sK160)) ),
    inference(instantiation,[status(thm)],[c_73041])).

cnf(c_178,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X2,X0)
    | ~ r1_tarski(X2,X1)
    | o_0_0_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f3342])).

cnf(c_48298,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(sK159,X0)
    | ~ r1_tarski(sK159,X1)
    | o_0_0_xboole_0 = sK159 ),
    inference(instantiation,[status(thm)],[c_178])).

cnf(c_59906,plain,
    ( ~ r1_xboole_0(X0,k2_relat_1(sK160))
    | ~ r1_tarski(sK159,X0)
    | ~ r1_tarski(sK159,k2_relat_1(sK160))
    | o_0_0_xboole_0 = sK159 ),
    inference(instantiation,[status(thm)],[c_48298])).

cnf(c_84695,plain,
    ( ~ r1_xboole_0(sK159,k2_relat_1(sK160))
    | ~ r1_tarski(sK159,k2_relat_1(sK160))
    | ~ r1_tarski(sK159,sK159)
    | o_0_0_xboole_0 = sK159 ),
    inference(instantiation,[status(thm)],[c_59906])).

cnf(c_69,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3798])).

cnf(c_58076,plain,
    ( r1_tarski(sK159,sK159) ),
    inference(instantiation,[status(thm)],[c_69])).

cnf(c_1170,negated_conjecture,
    ( o_0_0_xboole_0 = k10_relat_1(sK160,sK159) ),
    inference(cnf_transformation,[],[f3756])).

cnf(c_1169,plain,
    ( r1_xboole_0(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) != o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f3755])).

cnf(c_34388,plain,
    ( k10_relat_1(X0,X1) != o_0_0_xboole_0
    | r1_xboole_0(k2_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1169])).

cnf(c_50600,plain,
    ( r1_xboole_0(k2_relat_1(sK160),sK159) = iProver_top
    | v1_relat_1(sK160) != iProver_top ),
    inference(superposition,[status(thm)],[c_1170,c_34388])).

cnf(c_50610,plain,
    ( r1_xboole_0(k2_relat_1(sK160),sK159)
    | ~ v1_relat_1(sK160) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_50600])).

cnf(c_1171,negated_conjecture,
    ( r1_tarski(sK159,k2_relat_1(sK160)) ),
    inference(cnf_transformation,[],[f3130])).

cnf(c_1172,negated_conjecture,
    ( o_0_0_xboole_0 != sK159 ),
    inference(cnf_transformation,[],[f3757])).

cnf(c_1173,negated_conjecture,
    ( v1_relat_1(sK160) ),
    inference(cnf_transformation,[],[f3128])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_119798,c_84695,c_58076,c_50610,c_1171,c_1172,c_1173])).

%------------------------------------------------------------------------------
