%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0904+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:23 EST 2020

% Result     : Theorem 0.67s
% Output     : CNFRefutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :   34 (  59 expanded)
%              Number of clauses        :   20 (  24 expanded)
%              Number of leaves         :    4 (  12 expanded)
%              Depth                    :    7
%              Number of atoms          :   88 ( 166 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f9,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ~ r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
     => ( ~ r1_xboole_0(X3,X7)
        & ~ r1_xboole_0(X2,X6)
        & ~ r1_xboole_0(X1,X5)
        & ~ r1_xboole_0(X0,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ~ r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
       => ( ~ r1_xboole_0(X3,X7)
          & ~ r1_xboole_0(X2,X6)
          & ~ r1_xboole_0(X1,X5)
          & ~ r1_xboole_0(X0,X4) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f6,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( r1_xboole_0(X3,X7)
        | r1_xboole_0(X2,X6)
        | r1_xboole_0(X1,X5)
        | r1_xboole_0(X0,X4) )
      & ~ r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f7,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( r1_xboole_0(X3,X7)
          | r1_xboole_0(X2,X6)
          | r1_xboole_0(X1,X5)
          | r1_xboole_0(X0,X4) )
        & ~ r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) )
   => ( ( r1_xboole_0(sK3,sK7)
        | r1_xboole_0(sK2,sK6)
        | r1_xboole_0(sK1,sK5)
        | r1_xboole_0(sK0,sK4) )
      & ~ r1_xboole_0(k4_zfmisc_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,
    ( ( r1_xboole_0(sK3,sK7)
      | r1_xboole_0(sK2,sK6)
      | r1_xboole_0(sK1,sK5)
      | r1_xboole_0(sK0,sK4) )
    & ~ r1_xboole_0(k4_zfmisc_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f6,f7])).

fof(f13,plain,
    ( r1_xboole_0(sK3,sK7)
    | r1_xboole_0(sK2,sK6)
    | r1_xboole_0(sK1,sK5)
    | r1_xboole_0(sK0,sK4) ),
    inference(cnf_transformation,[],[f8])).

fof(f12,plain,(
    ~ r1_xboole_0(k4_zfmisc_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f14,plain,(
    ~ r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(definition_unfolding,[],[f12,f11,f11])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_157,plain,
    ( r1_xboole_0(k2_zfmisc_1(X0,sK2),k2_zfmisc_1(X1,sK6))
    | ~ r1_xboole_0(sK2,sK6) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1391,plain,
    ( r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,X0),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,X1),sK6))
    | ~ r1_xboole_0(sK2,sK6) ),
    inference(instantiation,[status(thm)],[c_157])).

cnf(c_7124,plain,
    ( r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | ~ r1_xboole_0(sK2,sK6) ),
    inference(instantiation,[status(thm)],[c_1391])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f9])).

cnf(c_194,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(X0,sK2),k2_zfmisc_1(X1,sK6))
    | r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X0,sK2),X2),k2_zfmisc_1(k2_zfmisc_1(X1,sK6),X3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1926,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(X0,sK2),k2_zfmisc_1(X1,sK6))
    | r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X0,sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(X1,sK6),sK7)) ),
    inference(instantiation,[status(thm)],[c_194])).

cnf(c_5609,plain,
    ( r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))
    | ~ r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(instantiation,[status(thm)],[c_1926])).

cnf(c_76,plain,
    ( r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1),k2_zfmisc_1(k2_zfmisc_1(sK4,X2),X3))
    | ~ r1_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK4,X2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_130,plain,
    ( r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),X1))
    | ~ r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_76])).

cnf(c_640,plain,
    ( r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | ~ r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_130])).

cnf(c_61,plain,
    ( r1_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK4,X1))
    | ~ r1_xboole_0(sK0,sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_423,plain,
    ( r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK4,sK5))
    | ~ r1_xboole_0(sK0,sK4) ),
    inference(instantiation,[status(thm)],[c_61])).

cnf(c_293,plain,
    ( r1_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(X1,sK7))
    | ~ r1_xboole_0(sK3,sK7) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_349,plain,
    ( r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))
    | ~ r1_xboole_0(sK3,sK7) ),
    inference(instantiation,[status(thm)],[c_293])).

cnf(c_91,plain,
    ( r1_xboole_0(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK5))
    | ~ r1_xboole_0(sK1,sK5) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_129,plain,
    ( r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK4,sK5))
    | ~ r1_xboole_0(sK1,sK5) ),
    inference(instantiation,[status(thm)],[c_91])).

cnf(c_2,negated_conjecture,
    ( r1_xboole_0(sK0,sK4)
    | r1_xboole_0(sK1,sK5)
    | r1_xboole_0(sK2,sK6)
    | r1_xboole_0(sK3,sK7) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_3,negated_conjecture,
    ( ~ r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(cnf_transformation,[],[f14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7124,c_5609,c_640,c_423,c_349,c_129,c_2,c_3])).


%------------------------------------------------------------------------------
