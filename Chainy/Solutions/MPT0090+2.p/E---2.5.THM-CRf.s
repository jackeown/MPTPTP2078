%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0090+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:36 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   42 (  91 expanded)
%              Number of clauses        :   21 (  38 expanded)
%              Number of leaves         :   10 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   71 ( 149 expanded)
%              Number of equality atoms :   33 (  84 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t83_xboole_1,conjecture,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t71_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X2)
        & r1_xboole_0(X1,X2)
        & r1_xboole_0(X3,X2) )
     => X1 = X3 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_xboole_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',t4_xboole_0)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k2_xboole_0)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_xboole_0(X1,X2)
      <=> k4_xboole_0(X1,X2) = X1 ) ),
    inference(assume_negation,[status(cth)],[t83_xboole_1])).

fof(c_0_11,plain,(
    ! [X172] : k3_xboole_0(X172,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_12,plain,(
    ! [X222,X223] : k4_xboole_0(X222,k4_xboole_0(X222,X223)) = k3_xboole_0(X222,X223) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_13,plain,(
    ! [X288,X289,X290] :
      ( k2_xboole_0(X288,X289) != k2_xboole_0(X290,X289)
      | ~ r1_xboole_0(X288,X289)
      | ~ r1_xboole_0(X290,X289)
      | X288 = X290 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t71_xboole_1])])).

fof(c_0_14,negated_conjecture,
    ( ( ~ r1_xboole_0(esk16_0,esk17_0)
      | k4_xboole_0(esk16_0,esk17_0) != esk16_0 )
    & ( r1_xboole_0(esk16_0,esk17_0)
      | k4_xboole_0(esk16_0,esk17_0) = esk16_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_15,plain,(
    ! [X82,X83,X85,X86,X87] :
      ( ( r1_xboole_0(X82,X83)
        | r2_hidden(esk11_2(X82,X83),k3_xboole_0(X82,X83)) )
      & ( ~ r2_hidden(X87,k3_xboole_0(X85,X86))
        | ~ r1_xboole_0(X85,X86) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_16,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X200] : k4_xboole_0(X200,k1_xboole_0) = X200 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_19,plain,
    ( X1 = X3
    | k2_xboole_0(X1,X2) != k2_xboole_0(X3,X2)
    | ~ r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( r1_xboole_0(esk16_0,esk17_0)
    | k4_xboole_0(esk16_0,esk17_0) = esk16_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_21,plain,(
    ! [X312,X313] : r1_xboole_0(k4_xboole_0(X312,X313),X313) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_22,plain,(
    ! [X9,X10] : k2_xboole_0(X9,X10) = k2_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_23,plain,(
    ! [X198,X199] : k2_xboole_0(X198,k4_xboole_0(X199,X198)) = k2_xboole_0(X198,X199) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_25,plain,(
    ! [X272] : r1_xboole_0(X272,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk11_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,negated_conjecture,
    ( k4_xboole_0(esk16_0,esk17_0) = esk16_0
    | X1 = esk16_0
    | k2_xboole_0(X1,esk17_0) != k2_xboole_0(esk16_0,esk17_0)
    | ~ r1_xboole_0(X1,esk17_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_30,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_24,c_0_17])).

cnf(c_0_34,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_36,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk11_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_28,c_0_17])).

cnf(c_0_37,negated_conjecture,
    ( k4_xboole_0(esk16_0,esk17_0) = esk16_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_29]),c_0_30])]),c_0_31]),c_0_32]),c_0_31])])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_27]),c_0_34]),c_0_35])])).

cnf(c_0_39,negated_conjecture,
    ( ~ r1_xboole_0(esk16_0,esk17_0)
    | k4_xboole_0(esk16_0,esk17_0) != esk16_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_40,negated_conjecture,
    ( r1_xboole_0(esk16_0,esk17_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_35]),c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_37])]),c_0_40])]),
    [proof]).
%------------------------------------------------------------------------------
