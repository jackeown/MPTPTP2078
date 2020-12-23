%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0337+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:02 EST 2020

% Result     : Theorem 0.47s
% Output     : CNFRefutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   45 (  75 expanded)
%              Number of clauses        :   28 (  35 expanded)
%              Number of leaves         :    5 (  14 expanded)
%              Depth                    :   12
%              Number of atoms          :  115 ( 206 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_xboole_0(X2,X1) )
     => r1_xboole_0(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_xboole_0(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_xboole_0(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_xboole_0(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | ( ~ r1_xboole_0(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f9])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | ~ r1_xboole_0(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( r2_hidden(X3,X1)
            & r2_hidden(X2,X0) )
         => r1_xboole_0(X2,X3) )
     => r1_xboole_0(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ! [X2,X3] :
            ( ( r2_hidden(X3,X1)
              & r2_hidden(X2,X0) )
           => r1_xboole_0(X2,X3) )
       => r1_xboole_0(k3_tarski(X0),k3_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ~ r1_xboole_0(k3_tarski(X0),k3_tarski(X1))
      & ! [X2,X3] :
          ( r1_xboole_0(X2,X3)
          | ~ r2_hidden(X3,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ~ r1_xboole_0(k3_tarski(X0),k3_tarski(X1))
      & ! [X2,X3] :
          ( r1_xboole_0(X2,X3)
          | ~ r2_hidden(X3,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f7])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( ~ r1_xboole_0(k3_tarski(X0),k3_tarski(X1))
        & ! [X2,X3] :
            ( r1_xboole_0(X2,X3)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X0) ) )
   => ( ~ r1_xboole_0(k3_tarski(sK1),k3_tarski(sK2))
      & ! [X3,X2] :
          ( r1_xboole_0(X2,X3)
          | ~ r2_hidden(X3,sK2)
          | ~ r2_hidden(X2,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ~ r1_xboole_0(k3_tarski(sK1),k3_tarski(sK2))
    & ! [X2,X3] :
        ( r1_xboole_0(X2,X3)
        | ~ r2_hidden(X3,sK2)
        | ~ r2_hidden(X2,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f8,f11])).

fof(f16,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(X2,X3)
      | ~ r2_hidden(X3,sK2)
      | ~ r2_hidden(X2,sK1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f17,plain,(
    ~ r1_xboole_0(k3_tarski(sK1),k3_tarski(sK2)) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_58,plain,
    ( ~ r1_xboole_0(X0_34,X1_34)
    | r1_xboole_0(X1_34,X0_34) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_88,plain,
    ( r1_xboole_0(X0_34,k3_tarski(X0_35))
    | ~ r1_xboole_0(k3_tarski(X0_35),X0_34) ),
    inference(instantiation,[status(thm)],[c_58])).

cnf(c_129,plain,
    ( r1_xboole_0(sK0(sK2,X0_34),k3_tarski(X0_35))
    | ~ r1_xboole_0(k3_tarski(X0_35),sK0(sK2,X0_34)) ),
    inference(instantiation,[status(thm)],[c_88])).

cnf(c_704,plain,
    ( r1_xboole_0(sK0(sK2,k3_tarski(sK1)),k3_tarski(sK1))
    | ~ r1_xboole_0(k3_tarski(sK1),sK0(sK2,k3_tarski(sK1))) ),
    inference(instantiation,[status(thm)],[c_129])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(k3_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_56,plain,
    ( r2_hidden(sK0(X0_35,X0_34),X0_35)
    | r1_xboole_0(k3_tarski(X0_35),X0_34) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_146,plain,
    ( r2_hidden(sK0(sK1,X0_34),sK1)
    | r1_xboole_0(k3_tarski(sK1),X0_34) ),
    inference(instantiation,[status(thm)],[c_56])).

cnf(c_157,plain,
    ( r2_hidden(sK0(sK1,sK0(sK2,X0_34)),sK1)
    | r1_xboole_0(k3_tarski(sK1),sK0(sK2,X0_34)) ),
    inference(instantiation,[status(thm)],[c_146])).

cnf(c_501,plain,
    ( r2_hidden(sK0(sK1,sK0(sK2,k3_tarski(sK1))),sK1)
    | r1_xboole_0(k3_tarski(sK1),sK0(sK2,k3_tarski(sK1))) ),
    inference(instantiation,[status(thm)],[c_157])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(sK0(X0,X1),X1)
    | r1_xboole_0(k3_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_57,plain,
    ( ~ r1_xboole_0(sK0(X0_35,X0_34),X0_34)
    | r1_xboole_0(k3_tarski(X0_35),X0_34) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_316,plain,
    ( ~ r1_xboole_0(sK0(X0_35,k3_tarski(X1_35)),k3_tarski(X1_35))
    | r1_xboole_0(k3_tarski(X0_35),k3_tarski(X1_35)) ),
    inference(instantiation,[status(thm)],[c_57])).

cnf(c_424,plain,
    ( ~ r1_xboole_0(sK0(sK2,k3_tarski(sK1)),k3_tarski(sK1))
    | r1_xboole_0(k3_tarski(sK2),k3_tarski(sK1)) ),
    inference(instantiation,[status(thm)],[c_316])).

cnf(c_114,plain,
    ( ~ r1_xboole_0(sK0(X0_35,sK0(sK2,X0_34)),sK0(sK2,X0_34))
    | r1_xboole_0(k3_tarski(X0_35),sK0(sK2,X0_34)) ),
    inference(instantiation,[status(thm)],[c_57])).

cnf(c_369,plain,
    ( ~ r1_xboole_0(sK0(sK1,sK0(sK2,k3_tarski(sK1))),sK0(sK2,k3_tarski(sK1)))
    | r1_xboole_0(k3_tarski(sK1),sK0(sK2,k3_tarski(sK1))) ),
    inference(instantiation,[status(thm)],[c_114])).

cnf(c_4,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | ~ r2_hidden(X1,sK1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_54,negated_conjecture,
    ( ~ r2_hidden(X0_34,sK2)
    | ~ r2_hidden(X1_34,sK1)
    | r1_xboole_0(X1_34,X0_34) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_98,plain,
    ( ~ r2_hidden(X0_34,sK1)
    | ~ r2_hidden(sK0(sK2,X1_34),sK2)
    | r1_xboole_0(X0_34,sK0(sK2,X1_34)) ),
    inference(instantiation,[status(thm)],[c_54])).

cnf(c_113,plain,
    ( ~ r2_hidden(sK0(X0_35,sK0(sK2,X0_34)),sK1)
    | ~ r2_hidden(sK0(sK2,X0_34),sK2)
    | r1_xboole_0(sK0(X0_35,sK0(sK2,X0_34)),sK0(sK2,X0_34)) ),
    inference(instantiation,[status(thm)],[c_98])).

cnf(c_244,plain,
    ( ~ r2_hidden(sK0(X0_35,sK0(sK2,k3_tarski(sK1))),sK1)
    | ~ r2_hidden(sK0(sK2,k3_tarski(sK1)),sK2)
    | r1_xboole_0(sK0(X0_35,sK0(sK2,k3_tarski(sK1))),sK0(sK2,k3_tarski(sK1))) ),
    inference(instantiation,[status(thm)],[c_113])).

cnf(c_246,plain,
    ( ~ r2_hidden(sK0(sK2,k3_tarski(sK1)),sK2)
    | ~ r2_hidden(sK0(sK1,sK0(sK2,k3_tarski(sK1))),sK1)
    | r1_xboole_0(sK0(sK1,sK0(sK2,k3_tarski(sK1))),sK0(sK2,k3_tarski(sK1))) ),
    inference(instantiation,[status(thm)],[c_244])).

cnf(c_97,plain,
    ( r2_hidden(sK0(sK2,X0_34),sK2)
    | r1_xboole_0(k3_tarski(sK2),X0_34) ),
    inference(instantiation,[status(thm)],[c_56])).

cnf(c_213,plain,
    ( r2_hidden(sK0(sK2,k3_tarski(sK1)),sK2)
    | r1_xboole_0(k3_tarski(sK2),k3_tarski(sK1)) ),
    inference(instantiation,[status(thm)],[c_97])).

cnf(c_108,plain,
    ( r1_xboole_0(X0_34,k3_tarski(sK2))
    | ~ r1_xboole_0(k3_tarski(sK2),X0_34) ),
    inference(instantiation,[status(thm)],[c_88])).

cnf(c_188,plain,
    ( ~ r1_xboole_0(k3_tarski(sK2),k3_tarski(sK1))
    | r1_xboole_0(k3_tarski(sK1),k3_tarski(sK2)) ),
    inference(instantiation,[status(thm)],[c_108])).

cnf(c_3,negated_conjecture,
    ( ~ r1_xboole_0(k3_tarski(sK1),k3_tarski(sK2)) ),
    inference(cnf_transformation,[],[f17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_704,c_501,c_424,c_369,c_246,c_213,c_188,c_3])).


%------------------------------------------------------------------------------
