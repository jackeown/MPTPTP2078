%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0315+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:59 EST 2020

% Result     : Theorem 0.83s
% Output     : CNFRefutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :   36 (  58 expanded)
%              Number of clauses        :   16 (  18 expanded)
%              Number of leaves         :    6 (  14 expanded)
%              Depth                    :    8
%              Number of atoms          :   95 ( 173 expanded)
%              Number of equality atoms :    5 (  10 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f11,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f7,f11])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ~ ( ! [X5,X6] :
            ~ ( r2_hidden(X6,k3_xboole_0(X2,X4))
              & r2_hidden(X5,k3_xboole_0(X1,X3))
              & k4_tarski(X5,X6) = X0 )
        & r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ? [X5,X6] :
          ( r2_hidden(X6,k3_xboole_0(X2,X4))
          & r2_hidden(X5,k3_xboole_0(X1,X3))
          & k4_tarski(X5,X6) = X0 )
      | ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5,X6] :
          ( r2_hidden(X6,k3_xboole_0(X2,X4))
          & r2_hidden(X5,k3_xboole_0(X1,X3))
          & k4_tarski(X5,X6) = X0 )
     => ( r2_hidden(sK1(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4))
        & r2_hidden(sK0(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3))
        & k4_tarski(sK0(X0,X1,X2,X3,X4),sK1(X0,X1,X2,X3,X4)) = X0 ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( r2_hidden(sK1(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4))
        & r2_hidden(sK0(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3))
        & k4_tarski(sK0(X0,X1,X2,X3,X4),sK1(X0,X1,X2,X3,X4)) = X0 )
      | ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f9])).

fof(f17,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK1(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4))
      | ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f16,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK0(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3))
      | ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X3)
          | r1_xboole_0(X0,X1) )
       => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      & ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
        & ( r1_xboole_0(X2,X3)
          | r1_xboole_0(X0,X1) ) )
   => ( ~ r1_xboole_0(k2_zfmisc_1(sK3,sK5),k2_zfmisc_1(sK4,sK6))
      & ( r1_xboole_0(sK5,sK6)
        | r1_xboole_0(sK3,sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(sK3,sK5),k2_zfmisc_1(sK4,sK6))
    & ( r1_xboole_0(sK5,sK6)
      | r1_xboole_0(sK3,sK4) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f8,f13])).

fof(f21,plain,(
    ~ r1_xboole_0(k2_zfmisc_1(sK3,sK5),k2_zfmisc_1(sK4,sK6)) ),
    inference(cnf_transformation,[],[f14])).

fof(f20,plain,
    ( r1_xboole_0(sK5,sK6)
    | r1_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_90,plain,
    ( ~ r1_xboole_0(X0_40,X1_40)
    | ~ r2_hidden(X0_41,k3_xboole_0(X0_40,X1_40)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_313,plain,
    ( ~ r1_xboole_0(sK3,sK4)
    | ~ r2_hidden(sK0(sK2(k2_zfmisc_1(sK3,sK5),k2_zfmisc_1(sK4,sK6)),sK3,sK5,sK4,sK6),k3_xboole_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_90])).

cnf(c_305,plain,
    ( ~ r1_xboole_0(sK5,sK6)
    | ~ r2_hidden(sK1(sK2(k2_zfmisc_1(sK3,sK5),k2_zfmisc_1(sK4,sK6)),sK3,sK5,sK4,sK6),k3_xboole_0(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_90])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)))
    | r2_hidden(sK1(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_93,plain,
    ( ~ r2_hidden(X0_41,k3_xboole_0(k2_zfmisc_1(X0_40,X1_40),k2_zfmisc_1(X2_40,X3_40)))
    | r2_hidden(sK1(X0_41,X0_40,X1_40,X2_40,X3_40),k3_xboole_0(X1_40,X3_40)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_292,plain,
    ( r2_hidden(sK1(sK2(k2_zfmisc_1(sK3,sK5),k2_zfmisc_1(sK4,sK6)),sK3,sK5,sK4,sK6),k3_xboole_0(sK5,sK6))
    | ~ r2_hidden(sK2(k2_zfmisc_1(sK3,sK5),k2_zfmisc_1(sK4,sK6)),k3_xboole_0(k2_zfmisc_1(sK3,sK5),k2_zfmisc_1(sK4,sK6))) ),
    inference(instantiation,[status(thm)],[c_93])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)))
    | r2_hidden(sK0(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3)) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_92,plain,
    ( ~ r2_hidden(X0_41,k3_xboole_0(k2_zfmisc_1(X0_40,X1_40),k2_zfmisc_1(X2_40,X3_40)))
    | r2_hidden(sK0(X0_41,X0_40,X1_40,X2_40,X3_40),k3_xboole_0(X0_40,X2_40)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_293,plain,
    ( r2_hidden(sK0(sK2(k2_zfmisc_1(sK3,sK5),k2_zfmisc_1(sK4,sK6)),sK3,sK5,sK4,sK6),k3_xboole_0(sK3,sK4))
    | ~ r2_hidden(sK2(k2_zfmisc_1(sK3,sK5),k2_zfmisc_1(sK4,sK6)),k3_xboole_0(k2_zfmisc_1(sK3,sK5),k2_zfmisc_1(sK4,sK6))) ),
    inference(instantiation,[status(thm)],[c_92])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_89,plain,
    ( r1_xboole_0(X0_40,X1_40)
    | r2_hidden(sK2(X0_40,X1_40),k3_xboole_0(X0_40,X1_40)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_282,plain,
    ( r1_xboole_0(k2_zfmisc_1(sK3,sK5),k2_zfmisc_1(sK4,sK6))
    | r2_hidden(sK2(k2_zfmisc_1(sK3,sK5),k2_zfmisc_1(sK4,sK6)),k3_xboole_0(k2_zfmisc_1(sK3,sK5),k2_zfmisc_1(sK4,sK6))) ),
    inference(instantiation,[status(thm)],[c_89])).

cnf(c_5,negated_conjecture,
    ( ~ r1_xboole_0(k2_zfmisc_1(sK3,sK5),k2_zfmisc_1(sK4,sK6)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_6,negated_conjecture,
    ( r1_xboole_0(sK5,sK6)
    | r1_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_313,c_305,c_292,c_293,c_282,c_5,c_6])).


%------------------------------------------------------------------------------
