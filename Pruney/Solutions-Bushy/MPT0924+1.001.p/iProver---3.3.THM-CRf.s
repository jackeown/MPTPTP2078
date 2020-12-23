%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0924+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:26 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 147 expanded)
%              Number of clauses        :   27 (  27 expanded)
%              Number of leaves         :    7 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :  225 ( 611 expanded)
%              Number of equality atoms :    7 (  43 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f9])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
    <=> ( r2_hidden(X2,X5)
        & r2_hidden(X1,X4)
        & r2_hidden(X0,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
        | ~ r2_hidden(X2,X5)
        | ~ r2_hidden(X1,X4)
        | ~ r2_hidden(X0,X3) )
      & ( ( r2_hidden(X2,X5)
          & r2_hidden(X1,X4)
          & r2_hidden(X0,X3) )
        | ~ r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f12,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
        | ~ r2_hidden(X2,X5)
        | ~ r2_hidden(X1,X4)
        | ~ r2_hidden(X0,X3) )
      & ( ( r2_hidden(X2,X5)
          & r2_hidden(X1,X4)
          & r2_hidden(X0,X3) )
        | ~ r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) ) ),
    inference(flattening,[],[f11])).

fof(f26,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
      | ~ r2_hidden(X2,X5)
      | ~ r2_hidden(X1,X4)
      | ~ r2_hidden(X0,X3) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(k4_tarski(k4_tarski(X0,X1),X2),k3_zfmisc_1(X3,X4,X5))
      | ~ r2_hidden(X2,X5)
      | ~ r2_hidden(X1,X4)
      | ~ r2_hidden(X0,X3) ) ),
    inference(definition_unfolding,[],[f26,f17])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(X2,X5)
      | ~ r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(X2,X5)
      | ~ r2_hidden(k4_tarski(k4_tarski(X0,X1),X2),k3_zfmisc_1(X3,X4,X5)) ) ),
    inference(definition_unfolding,[],[f25,f17])).

fof(f24,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(X1,X4)
      | ~ r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(X1,X4)
      | ~ r2_hidden(k4_tarski(k4_tarski(X0,X1),X2),k3_zfmisc_1(X3,X4,X5)) ) ),
    inference(definition_unfolding,[],[f24,f17])).

fof(f23,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(X0,X3)
      | ~ r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(X0,X3)
      | ~ r2_hidden(k4_tarski(k4_tarski(X0,X1),X2),k3_zfmisc_1(X3,X4,X5)) ) ),
    inference(definition_unfolding,[],[f23,f17])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
    <=> ( r2_hidden(X3,X7)
        & r2_hidden(X2,X6)
        & r2_hidden(X1,X5)
        & r2_hidden(X0,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
      <=> ( r2_hidden(X3,X7)
          & r2_hidden(X2,X6)
          & r2_hidden(X1,X5)
          & r2_hidden(X0,X4) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
    <~> ( r2_hidden(X3,X7)
        & r2_hidden(X2,X6)
        & r2_hidden(X1,X5)
        & r2_hidden(X0,X4) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f13,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( ~ r2_hidden(X3,X7)
        | ~ r2_hidden(X2,X6)
        | ~ r2_hidden(X1,X5)
        | ~ r2_hidden(X0,X4)
        | ~ r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) )
      & ( ( r2_hidden(X3,X7)
          & r2_hidden(X2,X6)
          & r2_hidden(X1,X5)
          & r2_hidden(X0,X4) )
        | r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f14,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( ~ r2_hidden(X3,X7)
        | ~ r2_hidden(X2,X6)
        | ~ r2_hidden(X1,X5)
        | ~ r2_hidden(X0,X4)
        | ~ r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) )
      & ( ( r2_hidden(X3,X7)
          & r2_hidden(X2,X6)
          & r2_hidden(X1,X5)
          & r2_hidden(X0,X4) )
        | r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) ) ) ),
    inference(flattening,[],[f13])).

fof(f15,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( ~ r2_hidden(X3,X7)
          | ~ r2_hidden(X2,X6)
          | ~ r2_hidden(X1,X5)
          | ~ r2_hidden(X0,X4)
          | ~ r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) )
        & ( ( r2_hidden(X3,X7)
            & r2_hidden(X2,X6)
            & r2_hidden(X1,X5)
            & r2_hidden(X0,X4) )
          | r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) ) )
   => ( ( ~ r2_hidden(sK3,sK7)
        | ~ r2_hidden(sK2,sK6)
        | ~ r2_hidden(sK1,sK5)
        | ~ r2_hidden(sK0,sK4)
        | ~ r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) )
      & ( ( r2_hidden(sK3,sK7)
          & r2_hidden(sK2,sK6)
          & r2_hidden(sK1,sK5)
          & r2_hidden(sK0,sK4) )
        | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ( ~ r2_hidden(sK3,sK7)
      | ~ r2_hidden(sK2,sK6)
      | ~ r2_hidden(sK1,sK5)
      | ~ r2_hidden(sK0,sK4)
      | ~ r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) )
    & ( ( r2_hidden(sK3,sK7)
        & r2_hidden(sK2,sK6)
        & r2_hidden(sK1,sK5)
        & r2_hidden(sK0,sK4) )
      | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f14,f15])).

fof(f31,plain,
    ( ~ r2_hidden(sK3,sK7)
    | ~ r2_hidden(sK2,sK6)
    | ~ r2_hidden(sK1,sK5)
    | ~ r2_hidden(sK0,sK4)
    | ~ r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f18,f17])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X2,X0,X3,X1] : k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f37,plain,
    ( ~ r2_hidden(sK3,sK7)
    | ~ r2_hidden(sK2,sK6)
    | ~ r2_hidden(sK1,sK5)
    | ~ r2_hidden(sK0,sK4)
    | ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k3_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6,sK7)) ),
    inference(definition_unfolding,[],[f31,f32,f22])).

fof(f30,plain,
    ( r2_hidden(sK3,sK7)
    | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f16])).

fof(f38,plain,
    ( r2_hidden(sK3,sK7)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k3_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6,sK7)) ),
    inference(definition_unfolding,[],[f30,f32,f22])).

fof(f29,plain,
    ( r2_hidden(sK2,sK6)
    | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f16])).

fof(f39,plain,
    ( r2_hidden(sK2,sK6)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k3_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6,sK7)) ),
    inference(definition_unfolding,[],[f29,f32,f22])).

fof(f28,plain,
    ( r2_hidden(sK1,sK5)
    | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f16])).

fof(f40,plain,
    ( r2_hidden(sK1,sK5)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k3_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6,sK7)) ),
    inference(definition_unfolding,[],[f28,f32,f22])).

fof(f27,plain,
    ( r2_hidden(sK0,sK4)
    | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f16])).

fof(f41,plain,
    ( r2_hidden(sK0,sK4)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k3_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6,sK7)) ),
    inference(definition_unfolding,[],[f27,f32,f22])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_136,plain,
    ( ~ r2_hidden(X0_40,X0_41)
    | ~ r2_hidden(X1_40,X1_41)
    | r2_hidden(k4_tarski(X1_40,X0_40),k2_zfmisc_1(X1_41,X0_41)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1518,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5))
    | ~ r2_hidden(sK0,sK4)
    | ~ r2_hidden(sK1,sK5) ),
    inference(instantiation,[status(thm)],[c_136])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X4,X5)
    | r2_hidden(k4_tarski(k4_tarski(X4,X2),X0),k3_zfmisc_1(X5,X3,X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_133,plain,
    ( ~ r2_hidden(X0_40,X0_41)
    | ~ r2_hidden(X1_40,X1_41)
    | ~ r2_hidden(X2_40,X2_41)
    | r2_hidden(k4_tarski(k4_tarski(X2_40,X1_40),X0_40),k3_zfmisc_1(X2_41,X1_41,X0_41)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_802,plain,
    ( r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k3_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6,sK7))
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5))
    | ~ r2_hidden(sK2,sK6)
    | ~ r2_hidden(sK3,sK7) ),
    inference(instantiation,[status(thm)],[c_133])).

cnf(c_1,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_135,plain,
    ( r2_hidden(X0_40,X0_41)
    | ~ r2_hidden(k4_tarski(X1_40,X0_40),k2_zfmisc_1(X1_41,X0_41)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_225,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5))
    | r2_hidden(sK1,sK5) ),
    inference(instantiation,[status(thm)],[c_135])).

cnf(c_2,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_134,plain,
    ( r2_hidden(X0_40,X0_41)
    | ~ r2_hidden(k4_tarski(X0_40,X1_40),k2_zfmisc_1(X0_41,X1_41)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_222,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5))
    | r2_hidden(sK0,sK4) ),
    inference(instantiation,[status(thm)],[c_134])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(k4_tarski(X2,X3),X0),k3_zfmisc_1(X4,X5,X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_132,plain,
    ( r2_hidden(X0_40,X0_41)
    | ~ r2_hidden(k4_tarski(k4_tarski(X1_40,X2_40),X0_40),k3_zfmisc_1(X1_41,X2_41,X0_41)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_199,plain,
    ( ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k3_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6,sK7))
    | r2_hidden(sK3,sK7) ),
    inference(instantiation,[status(thm)],[c_132])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(k4_tarski(X2,X0),X3),k3_zfmisc_1(X4,X1,X5)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_131,plain,
    ( r2_hidden(X0_40,X0_41)
    | ~ r2_hidden(k4_tarski(k4_tarski(X1_40,X0_40),X2_40),k3_zfmisc_1(X1_41,X0_41,X2_41)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_196,plain,
    ( ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k3_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6,sK7))
    | r2_hidden(sK2,sK6) ),
    inference(instantiation,[status(thm)],[c_131])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(k4_tarski(X0,X2),X3),k3_zfmisc_1(X1,X4,X5)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_130,plain,
    ( r2_hidden(X0_40,X0_41)
    | ~ r2_hidden(k4_tarski(k4_tarski(X0_40,X1_40),X2_40),k3_zfmisc_1(X0_41,X1_41,X2_41)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_193,plain,
    ( ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k3_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6,sK7))
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_130])).

cnf(c_7,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k3_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6,sK7))
    | ~ r2_hidden(sK0,sK4)
    | ~ r2_hidden(sK1,sK5)
    | ~ r2_hidden(sK2,sK6)
    | ~ r2_hidden(sK3,sK7) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_8,negated_conjecture,
    ( r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k3_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6,sK7))
    | r2_hidden(sK3,sK7) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_9,negated_conjecture,
    ( r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k3_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6,sK7))
    | r2_hidden(sK2,sK6) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_10,negated_conjecture,
    ( r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k3_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6,sK7))
    | r2_hidden(sK1,sK5) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_11,negated_conjecture,
    ( r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k3_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6,sK7))
    | r2_hidden(sK0,sK4) ),
    inference(cnf_transformation,[],[f41])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1518,c_802,c_225,c_222,c_199,c_196,c_193,c_7,c_8,c_9,c_10,c_11])).


%------------------------------------------------------------------------------
