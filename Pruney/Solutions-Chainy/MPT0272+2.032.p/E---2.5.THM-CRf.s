%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:42:54 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 191 expanded)
%              Number of clauses        :   32 (  85 expanded)
%              Number of leaves         :    7 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :  114 ( 452 expanded)
%              Number of equality atoms :   59 ( 270 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t69_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
      | k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_zfmisc_1)).

fof(c_0_7,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k4_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_8,plain,(
    ! [X18,X19] : k4_xboole_0(X18,X19) = k5_xboole_0(X18,k3_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_9,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_11,plain,(
    ! [X20] : k4_xboole_0(X20,k1_xboole_0) = X20 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_12,plain,(
    ! [X23,X24,X25,X26,X27,X28] :
      ( ( ~ r2_hidden(X25,X24)
        | X25 = X23
        | X24 != k1_tarski(X23) )
      & ( X26 != X23
        | r2_hidden(X26,X24)
        | X24 != k1_tarski(X23) )
      & ( ~ r2_hidden(esk2_2(X27,X28),X28)
        | esk2_2(X27,X28) != X27
        | X28 = k1_tarski(X27) )
      & ( r2_hidden(esk2_2(X27,X28),X28)
        | esk2_2(X27,X28) = X27
        | X28 = k1_tarski(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_13,plain,(
    ! [X30] : k2_tarski(X30,X30) = k1_tarski(X30) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_14,plain,(
    ! [X31,X32] : k1_enumset1(X31,X31,X32) = k2_tarski(X31,X32) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
        | k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1) ) ),
    inference(assume_negation,[status(cth)],[t69_zfmisc_1])).

cnf(c_0_16,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_21,negated_conjecture,
    ( k4_xboole_0(k1_tarski(esk3_0),esk4_0) != k1_xboole_0
    & k4_xboole_0(k1_tarski(esk3_0),esk4_0) != k1_tarski(esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_17,c_0_10])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_25,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_26,negated_conjecture,
    ( k4_xboole_0(k1_tarski(esk3_0),esk4_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,k1_enumset1(X1,X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_24])])).

cnf(c_0_30,negated_conjecture,
    ( k4_xboole_0(k1_tarski(esk3_0),esk4_0) != k1_tarski(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( X1 = X3
    | X2 != k1_enumset1(X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_19]),c_0_20])).

cnf(c_0_32,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk3_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_19]),c_0_20]),c_0_10])).

cnf(c_0_33,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_27,c_0_10])).

cnf(c_0_34,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk3_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0)) != k1_enumset1(esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_19]),c_0_19]),c_0_20]),c_0_20]),c_0_10])).

cnf(c_0_36,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_37,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_enumset1(X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk1_3(k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0,k1_xboole_0),k1_enumset1(esk3_0,esk3_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33])]),c_0_34])).

cnf(c_0_39,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk1_3(k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0,k1_enumset1(esk3_0,esk3_0,esk3_0)),k1_enumset1(esk3_0,esk3_0,esk3_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_33])])).

cnf(c_0_41,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_36,c_0_10])).

cnf(c_0_42,negated_conjecture,
    ( esk1_3(k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0,k1_xboole_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_39,c_0_10])).

cnf(c_0_44,negated_conjecture,
    ( esk1_3(k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0,k1_enumset1(esk3_0,esk3_0,esk3_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_32]),c_0_34])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_29])]),c_0_35]),c_0_45]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:45:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.13/0.38  # and selection function SelectNegativeLiterals.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.13/0.38  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.13/0.38  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.13/0.38  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.13/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.38  fof(t69_zfmisc_1, conjecture, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0|k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_zfmisc_1)).
% 0.13/0.38  fof(c_0_7, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6))&(~r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k4_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k4_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.13/0.38  fof(c_0_8, plain, ![X18, X19]:k4_xboole_0(X18,X19)=k5_xboole_0(X18,k3_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.13/0.38  cnf(c_0_9, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_10, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  fof(c_0_11, plain, ![X20]:k4_xboole_0(X20,k1_xboole_0)=X20, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.13/0.38  fof(c_0_12, plain, ![X23, X24, X25, X26, X27, X28]:(((~r2_hidden(X25,X24)|X25=X23|X24!=k1_tarski(X23))&(X26!=X23|r2_hidden(X26,X24)|X24!=k1_tarski(X23)))&((~r2_hidden(esk2_2(X27,X28),X28)|esk2_2(X27,X28)!=X27|X28=k1_tarski(X27))&(r2_hidden(esk2_2(X27,X28),X28)|esk2_2(X27,X28)=X27|X28=k1_tarski(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.13/0.38  fof(c_0_13, plain, ![X30]:k2_tarski(X30,X30)=k1_tarski(X30), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.38  fof(c_0_14, plain, ![X31, X32]:k1_enumset1(X31,X31,X32)=k2_tarski(X31,X32), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.38  fof(c_0_15, negated_conjecture, ~(![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0|k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1))), inference(assume_negation,[status(cth)],[t69_zfmisc_1])).
% 0.13/0.38  cnf(c_0_16, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_9, c_0_10])).
% 0.13/0.38  cnf(c_0_17, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_18, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_19, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_20, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  fof(c_0_21, negated_conjecture, (k4_xboole_0(k1_tarski(esk3_0),esk4_0)!=k1_xboole_0&k4_xboole_0(k1_tarski(esk3_0),esk4_0)!=k1_tarski(esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.13/0.38  cnf(c_0_22, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_23, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_17, c_0_10])).
% 0.13/0.38  cnf(c_0_24, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 0.13/0.38  cnf(c_0_25, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (k4_xboole_0(k1_tarski(esk3_0),esk4_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_27, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_28, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.13/0.38  cnf(c_0_29, plain, (r2_hidden(X1,k1_enumset1(X1,X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_24])])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (k4_xboole_0(k1_tarski(esk3_0),esk4_0)!=k1_tarski(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_31, plain, (X1=X3|X2!=k1_enumset1(X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_19]), c_0_20])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk3_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_19]), c_0_20]), c_0_10])).
% 0.13/0.38  cnf(c_0_33, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_27, c_0_10])).
% 0.13/0.38  cnf(c_0_34, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk3_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0))!=k1_enumset1(esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_19]), c_0_19]), c_0_20]), c_0_20]), c_0_10])).
% 0.13/0.38  cnf(c_0_36, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_37, plain, (X1=X2|~r2_hidden(X1,k1_enumset1(X2,X2,X2))), inference(er,[status(thm)],[c_0_31])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (r2_hidden(esk1_3(k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0,k1_xboole_0),k1_enumset1(esk3_0,esk3_0,esk3_0))), inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33])]), c_0_34])).
% 0.13/0.38  cnf(c_0_39, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (r2_hidden(esk1_3(k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0,k1_enumset1(esk3_0,esk3_0,esk3_0)),k1_enumset1(esk3_0,esk3_0,esk3_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_33])])).
% 0.13/0.38  cnf(c_0_41, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_36, c_0_10])).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (esk1_3(k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0,k1_xboole_0)=esk3_0), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.13/0.38  cnf(c_0_43, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_39, c_0_10])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (esk1_3(k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0,k1_enumset1(esk3_0,esk3_0,esk3_0))=esk3_0), inference(spm,[status(thm)],[c_0_37, c_0_40])).
% 0.13/0.38  cnf(c_0_45, negated_conjecture, (~r2_hidden(esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_32]), c_0_34])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_29])]), c_0_35]), c_0_45]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 47
% 0.13/0.38  # Proof object clause steps            : 32
% 0.13/0.38  # Proof object formula steps           : 15
% 0.13/0.38  # Proof object conjectures             : 13
% 0.13/0.38  # Proof object clause conjectures      : 10
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 12
% 0.13/0.38  # Proof object initial formulas used   : 7
% 0.13/0.38  # Proof object generating inferences   : 8
% 0.13/0.38  # Proof object simplifying inferences  : 30
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 10
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 22
% 0.13/0.38  # Removed in clause preprocessing      : 3
% 0.13/0.38  # Initial clauses in saturation        : 19
% 0.13/0.38  # Processed clauses                    : 105
% 0.13/0.38  # ...of these trivial                  : 3
% 0.13/0.38  # ...subsumed                          : 24
% 0.13/0.38  # ...remaining for further processing  : 78
% 0.13/0.38  # Other redundant clauses eliminated   : 24
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 6
% 0.13/0.38  # Generated clauses                    : 290
% 0.13/0.38  # ...of the previous two non-trivial   : 252
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 267
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 24
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 46
% 0.13/0.38  #    Positive orientable unit clauses  : 11
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 4
% 0.13/0.38  #    Non-unit-clauses                  : 31
% 0.13/0.38  # Current number of unprocessed clauses: 177
% 0.13/0.38  # ...number of literals in the above   : 644
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 27
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 117
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 86
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 6
% 0.13/0.38  # Unit Clause-clause subsumption calls : 19
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 23
% 0.13/0.38  # BW rewrite match successes           : 6
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 5167
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.034 s
% 0.13/0.39  # System time              : 0.003 s
% 0.13/0.39  # Total time               : 0.037 s
% 0.13/0.39  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
