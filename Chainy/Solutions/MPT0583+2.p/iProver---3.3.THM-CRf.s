%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0583+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:46 EST 2020

% Result     : Theorem 22.88s
% Output     : CNFRefutation 22.88s
% Verified   : 
% Statistics : Number of formulae       :   42 (  62 expanded)
%              Number of clauses        :   15 (  15 expanded)
%              Number of leaves         :    9 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :   90 ( 142 expanded)
%              Number of equality atoms :   36 (  60 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f838,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1504,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f838])).

fof(f1982,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1504])).

fof(f3269,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1982])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1990,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f3847,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k7_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f3269,f1990])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f863,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f2026,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f863])).

fof(f774,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f775,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( r1_xboole_0(X1,k1_relat_1(X0))
           => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f774])).

fof(f1427,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != k7_relat_1(X0,X1)
          & r1_xboole_0(X1,k1_relat_1(X0)) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f775])).

fof(f1965,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != k7_relat_1(X0,X1)
          & r1_xboole_0(X1,k1_relat_1(X0)) )
     => ( k1_xboole_0 != k7_relat_1(X0,sK161)
        & r1_xboole_0(sK161,k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1964,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 != k7_relat_1(X0,X1)
            & r1_xboole_0(X1,k1_relat_1(X0)) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 != k7_relat_1(sK160,X1)
          & r1_xboole_0(X1,k1_relat_1(sK160)) )
      & v1_relat_1(sK160) ) ),
    introduced(choice_axiom,[])).

fof(f1966,plain,
    ( k1_xboole_0 != k7_relat_1(sK160,sK161)
    & r1_xboole_0(sK161,k1_relat_1(sK160))
    & v1_relat_1(sK160) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK160,sK161])],[f1427,f1965,f1964])).

fof(f3185,plain,(
    r1_xboole_0(sK161,k1_relat_1(sK160)) ),
    inference(cnf_transformation,[],[f1966])).

fof(f592,axiom,(
    ! [X0] : r1_setfam_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2931,plain,(
    ! [X0] : r1_setfam_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f592])).

fof(f3753,plain,(
    ! [X0] : r1_setfam_1(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f2931,f1990])).

fof(f593,axiom,(
    ! [X0] :
      ( r1_setfam_1(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1224,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_setfam_1(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f593])).

fof(f2932,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_setfam_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f1224])).

fof(f3754,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ r1_setfam_1(X0,o_0_0_xboole_0) ) ),
    inference(definition_unfolding,[],[f2932,f1990,f1990])).

fof(f3186,plain,(
    k1_xboole_0 != k7_relat_1(sK160,sK161) ),
    inference(cnf_transformation,[],[f1966])).

fof(f3820,plain,(
    o_0_0_xboole_0 != k7_relat_1(sK160,sK161) ),
    inference(definition_unfolding,[],[f3186,f1990])).

fof(f3184,plain,(
    v1_relat_1(sK160) ),
    inference(cnf_transformation,[],[f1966])).

cnf(c_1271,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f3847])).

cnf(c_63131,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK160),sK161)
    | ~ v1_relat_1(sK160)
    | k7_relat_1(sK160,sK161) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1271])).

cnf(c_17401,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_46380,plain,
    ( k7_relat_1(sK160,sK161) != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = k7_relat_1(sK160,sK161) ),
    inference(instantiation,[status(thm)],[c_17401])).

cnf(c_46381,plain,
    ( k7_relat_1(sK160,sK161) != o_0_0_xboole_0
    | o_0_0_xboole_0 = k7_relat_1(sK160,sK161)
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_46380])).

cnf(c_44,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2026])).

cnf(c_1188,negated_conjecture,
    ( r1_xboole_0(sK161,k1_relat_1(sK160)) ),
    inference(cnf_transformation,[],[f3185])).

cnf(c_45078,plain,
    ( r1_xboole_0(k1_relat_1(sK160),sK161) ),
    inference(resolution,[status(thm)],[c_44,c_1188])).

cnf(c_934,plain,
    ( r1_setfam_1(o_0_0_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3753])).

cnf(c_2141,plain,
    ( r1_setfam_1(o_0_0_xboole_0,o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_934])).

cnf(c_935,plain,
    ( ~ r1_setfam_1(X0,o_0_0_xboole_0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f3754])).

cnf(c_2138,plain,
    ( ~ r1_setfam_1(o_0_0_xboole_0,o_0_0_xboole_0)
    | o_0_0_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_935])).

cnf(c_1187,negated_conjecture,
    ( o_0_0_xboole_0 != k7_relat_1(sK160,sK161) ),
    inference(cnf_transformation,[],[f3820])).

cnf(c_1189,negated_conjecture,
    ( v1_relat_1(sK160) ),
    inference(cnf_transformation,[],[f3184])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_63131,c_46381,c_45078,c_2141,c_2138,c_1187,c_1189])).

%------------------------------------------------------------------------------
