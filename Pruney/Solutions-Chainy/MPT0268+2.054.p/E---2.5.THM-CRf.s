%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:42:24 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 204 expanded)
%              Number of clauses        :   36 (  93 expanded)
%              Number of leaves         :    9 (  53 expanded)
%              Depth                    :   10
%              Number of atoms          :  170 ( 592 expanded)
%              Number of equality atoms :   81 ( 310 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t65_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(c_0_9,plain,(
    ! [X25,X26,X27,X28,X29,X30,X31,X32,X33,X34] :
      ( ( ~ r2_hidden(X29,X28)
        | X29 = X25
        | X29 = X26
        | X29 = X27
        | X28 != k1_enumset1(X25,X26,X27) )
      & ( X30 != X25
        | r2_hidden(X30,X28)
        | X28 != k1_enumset1(X25,X26,X27) )
      & ( X30 != X26
        | r2_hidden(X30,X28)
        | X28 != k1_enumset1(X25,X26,X27) )
      & ( X30 != X27
        | r2_hidden(X30,X28)
        | X28 != k1_enumset1(X25,X26,X27) )
      & ( esk3_4(X31,X32,X33,X34) != X31
        | ~ r2_hidden(esk3_4(X31,X32,X33,X34),X34)
        | X34 = k1_enumset1(X31,X32,X33) )
      & ( esk3_4(X31,X32,X33,X34) != X32
        | ~ r2_hidden(esk3_4(X31,X32,X33,X34),X34)
        | X34 = k1_enumset1(X31,X32,X33) )
      & ( esk3_4(X31,X32,X33,X34) != X33
        | ~ r2_hidden(esk3_4(X31,X32,X33,X34),X34)
        | X34 = k1_enumset1(X31,X32,X33) )
      & ( r2_hidden(esk3_4(X31,X32,X33,X34),X34)
        | esk3_4(X31,X32,X33,X34) = X31
        | esk3_4(X31,X32,X33,X34) = X32
        | esk3_4(X31,X32,X33,X34) = X33
        | X34 = k1_enumset1(X31,X32,X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_10,plain,(
    ! [X39,X40,X41] : k2_enumset1(X39,X39,X40,X41) = k1_enumset1(X39,X40,X41) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k4_xboole_0(X1,k1_tarski(X2)) = X1
      <=> ~ r2_hidden(X2,X1) ) ),
    inference(assume_negation,[status(cth)],[t65_zfmisc_1])).

fof(c_0_12,plain,(
    ! [X23,X24] :
      ( ( ~ r1_xboole_0(X23,X24)
        | k4_xboole_0(X23,X24) = X23 )
      & ( k4_xboole_0(X23,X24) != X23
        | r1_xboole_0(X23,X24) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_13,plain,(
    ! [X21,X22] : k4_xboole_0(X21,X22) = k5_xboole_0(X21,k3_xboole_0(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_14,plain,(
    ! [X15,X16,X18,X19,X20] :
      ( ( r2_hidden(esk2_2(X15,X16),X15)
        | r1_xboole_0(X15,X16) )
      & ( r2_hidden(esk2_2(X15,X16),X16)
        | r1_xboole_0(X15,X16) )
      & ( ~ r2_hidden(X20,X18)
        | ~ r2_hidden(X20,X19)
        | ~ r1_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_17,negated_conjecture,
    ( ( k4_xboole_0(esk4_0,k1_tarski(esk5_0)) != esk4_0
      | r2_hidden(esk5_0,esk4_0) )
    & ( k4_xboole_0(esk4_0,k1_tarski(esk5_0)) = esk4_0
      | ~ r2_hidden(esk5_0,esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

fof(c_0_18,plain,(
    ! [X36] : k2_tarski(X36,X36) = k1_tarski(X36) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_19,plain,(
    ! [X37,X38] : k1_enumset1(X37,X37,X38) = k2_tarski(X37,X38) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X4,X5) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_25,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0)
    | k4_xboole_0(esk4_0,k1_tarski(esk5_0)) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_30,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_31,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_24])])).

cnf(c_0_33,plain,
    ( X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k2_enumset1(X3,X3,X4,X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_25,c_0_16])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0)
    | k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))) != esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_21]),c_0_16])).

cnf(c_0_35,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1
    | r2_hidden(esk2_2(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_36,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12,X13] :
      ( ( r2_hidden(X9,X6)
        | ~ r2_hidden(X9,X8)
        | X8 != k4_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X9,X7)
        | ~ r2_hidden(X9,X8)
        | X8 != k4_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X10,X6)
        | r2_hidden(X10,X7)
        | r2_hidden(X10,X8)
        | X8 != k4_xboole_0(X6,X7) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | ~ r2_hidden(esk1_3(X11,X12,X13),X11)
        | r2_hidden(esk1_3(X11,X12,X13),X12)
        | X13 = k4_xboole_0(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X11)
        | r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X12)
        | r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k4_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_37,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1
    | r2_hidden(esk2_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_23])).

cnf(c_0_38,plain,
    ( r2_hidden(esk2_2(X1,k2_enumset1(X2,X2,X3,X4)),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k2_enumset1(X4,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk2_2(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))
    | r2_hidden(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( k4_xboole_0(esk4_0,k1_tarski(esk5_0)) = esk4_0
    | ~ r2_hidden(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk2_2(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_37]),c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( esk2_2(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) = esk5_0
    | r2_hidden(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_41,c_0_21])).

cnf(c_0_46,negated_conjecture,
    ( k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))) = esk4_0
    | ~ r2_hidden(esk5_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_27]),c_0_28]),c_0_21]),c_0_16])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_49,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47])])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[c_0_48,c_0_16])).

cnf(c_0_52,negated_conjecture,
    ( ~ r2_hidden(X1,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_51])])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_47])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:22:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.36  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.13/0.36  # and selection function SelectNegativeLiterals.
% 0.13/0.36  #
% 0.13/0.36  # Preprocessing time       : 0.015 s
% 0.13/0.36  # Presaturation interreduction done
% 0.13/0.36  
% 0.13/0.36  # Proof found!
% 0.13/0.36  # SZS status Theorem
% 0.13/0.36  # SZS output start CNFRefutation
% 0.13/0.36  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 0.13/0.36  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.36  fof(t65_zfmisc_1, conjecture, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.13/0.36  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.13/0.36  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.13/0.36  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.13/0.36  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.36  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.36  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.13/0.36  fof(c_0_9, plain, ![X25, X26, X27, X28, X29, X30, X31, X32, X33, X34]:(((~r2_hidden(X29,X28)|(X29=X25|X29=X26|X29=X27)|X28!=k1_enumset1(X25,X26,X27))&(((X30!=X25|r2_hidden(X30,X28)|X28!=k1_enumset1(X25,X26,X27))&(X30!=X26|r2_hidden(X30,X28)|X28!=k1_enumset1(X25,X26,X27)))&(X30!=X27|r2_hidden(X30,X28)|X28!=k1_enumset1(X25,X26,X27))))&((((esk3_4(X31,X32,X33,X34)!=X31|~r2_hidden(esk3_4(X31,X32,X33,X34),X34)|X34=k1_enumset1(X31,X32,X33))&(esk3_4(X31,X32,X33,X34)!=X32|~r2_hidden(esk3_4(X31,X32,X33,X34),X34)|X34=k1_enumset1(X31,X32,X33)))&(esk3_4(X31,X32,X33,X34)!=X33|~r2_hidden(esk3_4(X31,X32,X33,X34),X34)|X34=k1_enumset1(X31,X32,X33)))&(r2_hidden(esk3_4(X31,X32,X33,X34),X34)|(esk3_4(X31,X32,X33,X34)=X31|esk3_4(X31,X32,X33,X34)=X32|esk3_4(X31,X32,X33,X34)=X33)|X34=k1_enumset1(X31,X32,X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.13/0.36  fof(c_0_10, plain, ![X39, X40, X41]:k2_enumset1(X39,X39,X40,X41)=k1_enumset1(X39,X40,X41), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.36  fof(c_0_11, negated_conjecture, ~(![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1)))), inference(assume_negation,[status(cth)],[t65_zfmisc_1])).
% 0.13/0.36  fof(c_0_12, plain, ![X23, X24]:((~r1_xboole_0(X23,X24)|k4_xboole_0(X23,X24)=X23)&(k4_xboole_0(X23,X24)!=X23|r1_xboole_0(X23,X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.13/0.36  fof(c_0_13, plain, ![X21, X22]:k4_xboole_0(X21,X22)=k5_xboole_0(X21,k3_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.13/0.36  fof(c_0_14, plain, ![X15, X16, X18, X19, X20]:(((r2_hidden(esk2_2(X15,X16),X15)|r1_xboole_0(X15,X16))&(r2_hidden(esk2_2(X15,X16),X16)|r1_xboole_0(X15,X16)))&(~r2_hidden(X20,X18)|~r2_hidden(X20,X19)|~r1_xboole_0(X18,X19))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.13/0.36  cnf(c_0_15, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.36  cnf(c_0_16, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.36  fof(c_0_17, negated_conjecture, ((k4_xboole_0(esk4_0,k1_tarski(esk5_0))!=esk4_0|r2_hidden(esk5_0,esk4_0))&(k4_xboole_0(esk4_0,k1_tarski(esk5_0))=esk4_0|~r2_hidden(esk5_0,esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).
% 0.13/0.36  fof(c_0_18, plain, ![X36]:k2_tarski(X36,X36)=k1_tarski(X36), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.36  fof(c_0_19, plain, ![X37, X38]:k1_enumset1(X37,X37,X38)=k2_tarski(X37,X38), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.36  cnf(c_0_20, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.36  cnf(c_0_21, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.36  cnf(c_0_22, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.36  cnf(c_0_23, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.36  cnf(c_0_24, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X4,X5)), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.13/0.36  cnf(c_0_25, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.36  cnf(c_0_26, negated_conjecture, (r2_hidden(esk5_0,esk4_0)|k4_xboole_0(esk4_0,k1_tarski(esk5_0))!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.36  cnf(c_0_27, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.36  cnf(c_0_28, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.36  cnf(c_0_29, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.36  cnf(c_0_30, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.36  cnf(c_0_31, plain, (r2_hidden(esk2_2(X1,X2),X1)|~r2_hidden(X3,X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.13/0.36  cnf(c_0_32, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_24])])).
% 0.13/0.36  cnf(c_0_33, plain, (X1=X5|X1=X4|X1=X3|X2!=k2_enumset1(X3,X3,X4,X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_25, c_0_16])).
% 0.13/0.36  cnf(c_0_34, negated_conjecture, (r2_hidden(esk5_0,esk4_0)|k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))!=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_21]), c_0_16])).
% 0.13/0.36  cnf(c_0_35, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=X1|r2_hidden(esk2_2(X1,X2),X2)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.13/0.36  fof(c_0_36, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:((((r2_hidden(X9,X6)|~r2_hidden(X9,X8)|X8!=k4_xboole_0(X6,X7))&(~r2_hidden(X9,X7)|~r2_hidden(X9,X8)|X8!=k4_xboole_0(X6,X7)))&(~r2_hidden(X10,X6)|r2_hidden(X10,X7)|r2_hidden(X10,X8)|X8!=k4_xboole_0(X6,X7)))&((~r2_hidden(esk1_3(X11,X12,X13),X13)|(~r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X12))|X13=k4_xboole_0(X11,X12))&((r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k4_xboole_0(X11,X12))&(~r2_hidden(esk1_3(X11,X12,X13),X12)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k4_xboole_0(X11,X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.13/0.36  cnf(c_0_37, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=X1|r2_hidden(esk2_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_29, c_0_23])).
% 0.13/0.36  cnf(c_0_38, plain, (r2_hidden(esk2_2(X1,k2_enumset1(X2,X2,X3,X4)),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.13/0.36  cnf(c_0_39, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k2_enumset1(X4,X4,X3,X2))), inference(er,[status(thm)],[c_0_33])).
% 0.13/0.36  cnf(c_0_40, negated_conjecture, (r2_hidden(esk2_2(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))|r2_hidden(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.13/0.36  cnf(c_0_41, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.36  cnf(c_0_42, negated_conjecture, (k4_xboole_0(esk4_0,k1_tarski(esk5_0))=esk4_0|~r2_hidden(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.36  cnf(c_0_43, negated_conjecture, (r2_hidden(esk2_2(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_37]), c_0_38])).
% 0.13/0.36  cnf(c_0_44, negated_conjecture, (esk2_2(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))=esk5_0|r2_hidden(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.13/0.36  cnf(c_0_45, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_41, c_0_21])).
% 0.13/0.36  cnf(c_0_46, negated_conjecture, (k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))=esk4_0|~r2_hidden(esk5_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_27]), c_0_28]), c_0_21]), c_0_16])).
% 0.13/0.36  cnf(c_0_47, negated_conjecture, (r2_hidden(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.13/0.36  cnf(c_0_48, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.36  cnf(c_0_49, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_45])).
% 0.13/0.36  cnf(c_0_50, negated_conjecture, (k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47])])).
% 0.13/0.36  cnf(c_0_51, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X4,X5,X2)), inference(rw,[status(thm)],[c_0_48, c_0_16])).
% 0.13/0.36  cnf(c_0_52, negated_conjecture, (~r2_hidden(X1,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.13/0.36  cnf(c_0_53, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_51])])).
% 0.13/0.36  cnf(c_0_54, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_47])]), ['proof']).
% 0.13/0.36  # SZS output end CNFRefutation
% 0.13/0.36  # Proof object total steps             : 55
% 0.13/0.36  # Proof object clause steps            : 36
% 0.13/0.36  # Proof object formula steps           : 19
% 0.13/0.36  # Proof object conjectures             : 14
% 0.13/0.36  # Proof object clause conjectures      : 11
% 0.13/0.36  # Proof object formula conjectures     : 3
% 0.13/0.36  # Proof object initial clauses used    : 14
% 0.13/0.36  # Proof object initial formulas used   : 9
% 0.13/0.36  # Proof object generating inferences   : 10
% 0.13/0.36  # Proof object simplifying inferences  : 24
% 0.13/0.36  # Training examples: 0 positive, 0 negative
% 0.13/0.36  # Parsed axioms                        : 10
% 0.13/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.36  # Initial clauses                      : 27
% 0.13/0.36  # Removed in clause preprocessing      : 4
% 0.13/0.36  # Initial clauses in saturation        : 23
% 0.13/0.36  # Processed clauses                    : 109
% 0.13/0.36  # ...of these trivial                  : 0
% 0.13/0.36  # ...subsumed                          : 14
% 0.13/0.36  # ...remaining for further processing  : 95
% 0.13/0.36  # Other redundant clauses eliminated   : 17
% 0.13/0.36  # Clauses deleted for lack of memory   : 0
% 0.13/0.36  # Backward-subsumed                    : 0
% 0.13/0.36  # Backward-rewritten                   : 20
% 0.13/0.36  # Generated clauses                    : 341
% 0.13/0.36  # ...of the previous two non-trivial   : 326
% 0.13/0.36  # Contextual simplify-reflections      : 1
% 0.13/0.36  # Paramodulations                      : 327
% 0.13/0.36  # Factorizations                       : 0
% 0.13/0.36  # Equation resolutions                 : 17
% 0.13/0.36  # Propositional unsat checks           : 0
% 0.13/0.36  #    Propositional check models        : 0
% 0.13/0.36  #    Propositional check unsatisfiable : 0
% 0.13/0.36  #    Propositional clauses             : 0
% 0.13/0.36  #    Propositional clauses after purity: 0
% 0.13/0.36  #    Propositional unsat core size     : 0
% 0.13/0.36  #    Propositional preprocessing time  : 0.000
% 0.13/0.36  #    Propositional encoding time       : 0.000
% 0.13/0.36  #    Propositional solver time         : 0.000
% 0.13/0.36  #    Success case prop preproc time    : 0.000
% 0.13/0.36  #    Success case prop encoding time   : 0.000
% 0.13/0.36  #    Success case prop solver time     : 0.000
% 0.13/0.36  # Current number of processed clauses  : 45
% 0.13/0.36  #    Positive orientable unit clauses  : 7
% 0.13/0.36  #    Positive unorientable unit clauses: 0
% 0.13/0.36  #    Negative unit clauses             : 0
% 0.13/0.36  #    Non-unit-clauses                  : 38
% 0.13/0.36  # Current number of unprocessed clauses: 263
% 0.13/0.36  # ...number of literals in the above   : 550
% 0.13/0.36  # Current number of archived formulas  : 0
% 0.13/0.36  # Current number of archived clauses   : 47
% 0.13/0.36  # Clause-clause subsumption calls (NU) : 548
% 0.13/0.36  # Rec. Clause-clause subsumption calls : 450
% 0.13/0.36  # Non-unit clause-clause subsumptions  : 15
% 0.13/0.36  # Unit Clause-clause subsumption calls : 3
% 0.13/0.36  # Rewrite failures with RHS unbound    : 0
% 0.13/0.36  # BW rewrite match attempts            : 7
% 0.13/0.36  # BW rewrite match successes           : 1
% 0.13/0.36  # Condensation attempts                : 0
% 0.13/0.36  # Condensation successes               : 0
% 0.13/0.36  # Termbank termtop insertions          : 7502
% 0.13/0.36  
% 0.13/0.36  # -------------------------------------------------
% 0.13/0.36  # User time                : 0.017 s
% 0.13/0.36  # System time              : 0.005 s
% 0.13/0.36  # Total time               : 0.022 s
% 0.13/0.36  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
