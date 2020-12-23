%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:10 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 160 expanded)
%              Number of clauses        :   27 (  69 expanded)
%              Number of leaves         :   10 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :  137 ( 354 expanded)
%              Number of equality atoms :   56 ( 189 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t17_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),k1_tarski(X4)))
     => ( ( k1_mcart_1(X1) = X2
          | k1_mcart_1(X1) = X3 )
        & k2_mcart_1(X1) = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_mcart_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t15_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),X4))
     => ( ( k1_mcart_1(X1) = X2
          | k1_mcart_1(X1) = X3 )
        & r2_hidden(k2_mcart_1(X1),X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_mcart_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),k1_tarski(X4)))
       => ( ( k1_mcart_1(X1) = X2
            | k1_mcart_1(X1) = X3 )
          & k2_mcart_1(X1) = X4 ) ) ),
    inference(assume_negation,[status(cth)],[t17_mcart_1])).

fof(c_0_11,plain,(
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

fof(c_0_12,plain,(
    ! [X25,X26,X27] :
      ( ( r2_hidden(X25,X26)
        | ~ r2_hidden(X25,k4_xboole_0(X26,k1_tarski(X27))) )
      & ( X25 != X27
        | ~ r2_hidden(X25,k4_xboole_0(X26,k1_tarski(X27))) )
      & ( ~ r2_hidden(X25,X26)
        | X25 = X27
        | r2_hidden(X25,k4_xboole_0(X26,k1_tarski(X27))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

fof(c_0_13,plain,(
    ! [X16] : k2_tarski(X16,X16) = k1_tarski(X16) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_14,plain,(
    ! [X17,X18] : k1_enumset1(X17,X17,X18) = k2_tarski(X17,X18) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_15,plain,(
    ! [X19,X20,X21] : k2_enumset1(X19,X19,X20,X21) = k1_enumset1(X19,X20,X21) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_16,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(k2_tarski(esk3_0,esk4_0),k1_tarski(esk5_0)))
    & ( k1_mcart_1(esk2_0) != esk3_0
      | k2_mcart_1(esk2_0) != esk5_0 )
    & ( k1_mcart_1(esk2_0) != esk4_0
      | k2_mcart_1(esk2_0) != esk5_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).

cnf(c_0_17,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( X1 = X3
    | r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X28,X29,X30] :
      ( ( r2_hidden(k1_mcart_1(X28),X29)
        | ~ r2_hidden(X28,k2_zfmisc_1(X29,X30)) )
      & ( r2_hidden(k2_mcart_1(X28),X30)
        | ~ r2_hidden(X28,k2_zfmisc_1(X29,X30)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(k2_tarski(esk3_0,esk4_0),k1_tarski(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_24,plain,(
    ! [X22,X23,X24] :
      ( ( r2_hidden(X22,X24)
        | ~ r1_tarski(k2_tarski(X22,X23),X24) )
      & ( r2_hidden(X23,X24)
        | ~ r1_tarski(k2_tarski(X22,X23),X24) )
      & ( ~ r2_hidden(X22,X24)
        | ~ r2_hidden(X23,X24)
        | r1_tarski(k2_tarski(X22,X23),X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

fof(c_0_25,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(X14,X15)
        | X14 != X15 )
      & ( r1_tarski(X15,X14)
        | X14 != X15 )
      & ( ~ r1_tarski(X14,X15)
        | ~ r1_tarski(X15,X14)
        | X14 = X15 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_26,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( X1 = X3
    | r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X3,X3,X3,X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21])).

cnf(c_0_28,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_19]),c_0_20]),c_0_20]),c_0_21]),c_0_21])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X3,X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_32,plain,(
    ! [X31,X32,X33,X34] :
      ( ( k1_mcart_1(X31) = X32
        | k1_mcart_1(X31) = X33
        | ~ r2_hidden(X31,k2_zfmisc_1(k2_tarski(X32,X33),X34)) )
      & ( r2_hidden(k2_mcart_1(X31),X34)
        | ~ r2_hidden(X31,k2_zfmisc_1(k2_tarski(X32,X33),X34)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_mcart_1])])])).

cnf(c_0_33,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_enumset1(X3,X3,X3,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_20]),c_0_21])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( k1_mcart_1(X1) = X2
    | k1_mcart_1(X1) = X3
    | ~ r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( esk5_0 = k2_mcart_1(esk2_0)
    | ~ r2_hidden(k2_mcart_1(esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X2,X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,plain,
    ( k1_mcart_1(X1) = X3
    | k1_mcart_1(X1) = X2
    | ~ r2_hidden(X1,k2_zfmisc_1(k2_enumset1(X2,X2,X2,X3),X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_20]),c_0_21])).

cnf(c_0_41,negated_conjecture,
    ( k1_mcart_1(esk2_0) != esk4_0
    | k2_mcart_1(esk2_0) != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_42,negated_conjecture,
    ( esk5_0 = k2_mcart_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( k1_mcart_1(esk2_0) != esk3_0
    | k2_mcart_1(esk2_0) != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_44,negated_conjecture,
    ( esk3_0 = k1_mcart_1(esk2_0)
    | esk4_0 = k1_mcart_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_29])).

cnf(c_0_45,negated_conjecture,
    ( esk4_0 != k1_mcart_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42])])).

cnf(c_0_46,negated_conjecture,
    ( esk3_0 != k1_mcart_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_42])])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[c_0_44,c_0_45]),c_0_46]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:52:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.20/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.041 s
% 0.20/0.40  # Presaturation interreduction done
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(t17_mcart_1, conjecture, ![X1, X2, X3, X4]:(r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),k1_tarski(X4)))=>((k1_mcart_1(X1)=X2|k1_mcart_1(X1)=X3)&k2_mcart_1(X1)=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_mcart_1)).
% 0.20/0.40  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.20/0.40  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 0.20/0.40  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.40  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.40  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.40  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.20/0.40  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.20/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.40  fof(t15_mcart_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),X4))=>((k1_mcart_1(X1)=X2|k1_mcart_1(X1)=X3)&r2_hidden(k2_mcart_1(X1),X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_mcart_1)).
% 0.20/0.40  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3, X4]:(r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),k1_tarski(X4)))=>((k1_mcart_1(X1)=X2|k1_mcart_1(X1)=X3)&k2_mcart_1(X1)=X4))), inference(assume_negation,[status(cth)],[t17_mcart_1])).
% 0.20/0.40  fof(c_0_11, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6))&(~r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k4_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k4_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.20/0.40  fof(c_0_12, plain, ![X25, X26, X27]:(((r2_hidden(X25,X26)|~r2_hidden(X25,k4_xboole_0(X26,k1_tarski(X27))))&(X25!=X27|~r2_hidden(X25,k4_xboole_0(X26,k1_tarski(X27)))))&(~r2_hidden(X25,X26)|X25=X27|r2_hidden(X25,k4_xboole_0(X26,k1_tarski(X27))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 0.20/0.40  fof(c_0_13, plain, ![X16]:k2_tarski(X16,X16)=k1_tarski(X16), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.40  fof(c_0_14, plain, ![X17, X18]:k1_enumset1(X17,X17,X18)=k2_tarski(X17,X18), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.40  fof(c_0_15, plain, ![X19, X20, X21]:k2_enumset1(X19,X19,X20,X21)=k1_enumset1(X19,X20,X21), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.40  fof(c_0_16, negated_conjecture, (r2_hidden(esk2_0,k2_zfmisc_1(k2_tarski(esk3_0,esk4_0),k1_tarski(esk5_0)))&((k1_mcart_1(esk2_0)!=esk3_0|k2_mcart_1(esk2_0)!=esk5_0)&(k1_mcart_1(esk2_0)!=esk4_0|k2_mcart_1(esk2_0)!=esk5_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).
% 0.20/0.40  cnf(c_0_17, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_18, plain, (X1=X3|r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.40  cnf(c_0_19, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.40  cnf(c_0_20, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.40  cnf(c_0_21, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.40  fof(c_0_22, plain, ![X28, X29, X30]:((r2_hidden(k1_mcart_1(X28),X29)|~r2_hidden(X28,k2_zfmisc_1(X29,X30)))&(r2_hidden(k2_mcart_1(X28),X30)|~r2_hidden(X28,k2_zfmisc_1(X29,X30)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.20/0.40  cnf(c_0_23, negated_conjecture, (r2_hidden(esk2_0,k2_zfmisc_1(k2_tarski(esk3_0,esk4_0),k1_tarski(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.40  fof(c_0_24, plain, ![X22, X23, X24]:(((r2_hidden(X22,X24)|~r1_tarski(k2_tarski(X22,X23),X24))&(r2_hidden(X23,X24)|~r1_tarski(k2_tarski(X22,X23),X24)))&(~r2_hidden(X22,X24)|~r2_hidden(X23,X24)|r1_tarski(k2_tarski(X22,X23),X24))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.20/0.40  fof(c_0_25, plain, ![X14, X15]:(((r1_tarski(X14,X15)|X14!=X15)&(r1_tarski(X15,X14)|X14!=X15))&(~r1_tarski(X14,X15)|~r1_tarski(X15,X14)|X14=X15)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.40  cnf(c_0_26, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_17])).
% 0.20/0.40  cnf(c_0_27, plain, (X1=X3|r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X3,X3,X3,X3)))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21])).
% 0.20/0.40  cnf(c_0_28, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.40  cnf(c_0_29, negated_conjecture, (r2_hidden(esk2_0,k2_zfmisc_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_19]), c_0_20]), c_0_20]), c_0_21]), c_0_21])).
% 0.20/0.40  cnf(c_0_30, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X3,X1),X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.40  cnf(c_0_31, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.40  fof(c_0_32, plain, ![X31, X32, X33, X34]:((k1_mcart_1(X31)=X32|k1_mcart_1(X31)=X33|~r2_hidden(X31,k2_zfmisc_1(k2_tarski(X32,X33),X34)))&(r2_hidden(k2_mcart_1(X31),X34)|~r2_hidden(X31,k2_zfmisc_1(k2_tarski(X32,X33),X34)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_mcart_1])])])).
% 0.20/0.40  cnf(c_0_33, plain, (X1=X2|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.40  cnf(c_0_34, negated_conjecture, (r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.40  cnf(c_0_35, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_enumset1(X3,X3,X3,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_20]), c_0_21])).
% 0.20/0.40  cnf(c_0_36, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_31])).
% 0.20/0.40  cnf(c_0_37, plain, (k1_mcart_1(X1)=X2|k1_mcart_1(X1)=X3|~r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),X4))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.40  cnf(c_0_38, negated_conjecture, (esk5_0=k2_mcart_1(esk2_0)|~r2_hidden(k2_mcart_1(esk2_0),X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.40  cnf(c_0_39, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X2,X1))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.40  cnf(c_0_40, plain, (k1_mcart_1(X1)=X3|k1_mcart_1(X1)=X2|~r2_hidden(X1,k2_zfmisc_1(k2_enumset1(X2,X2,X2,X3),X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_20]), c_0_21])).
% 0.20/0.40  cnf(c_0_41, negated_conjecture, (k1_mcart_1(esk2_0)!=esk4_0|k2_mcart_1(esk2_0)!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.40  cnf(c_0_42, negated_conjecture, (esk5_0=k2_mcart_1(esk2_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.40  cnf(c_0_43, negated_conjecture, (k1_mcart_1(esk2_0)!=esk3_0|k2_mcart_1(esk2_0)!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.40  cnf(c_0_44, negated_conjecture, (esk3_0=k1_mcart_1(esk2_0)|esk4_0=k1_mcart_1(esk2_0)), inference(spm,[status(thm)],[c_0_40, c_0_29])).
% 0.20/0.40  cnf(c_0_45, negated_conjecture, (esk4_0!=k1_mcart_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42])])).
% 0.20/0.40  cnf(c_0_46, negated_conjecture, (esk3_0!=k1_mcart_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_42])])).
% 0.20/0.40  cnf(c_0_47, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[c_0_44, c_0_45]), c_0_46]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 48
% 0.20/0.40  # Proof object clause steps            : 27
% 0.20/0.40  # Proof object formula steps           : 21
% 0.20/0.40  # Proof object conjectures             : 14
% 0.20/0.40  # Proof object clause conjectures      : 11
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 12
% 0.20/0.40  # Proof object initial formulas used   : 10
% 0.20/0.40  # Proof object generating inferences   : 7
% 0.20/0.40  # Proof object simplifying inferences  : 19
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 10
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 25
% 0.20/0.40  # Removed in clause preprocessing      : 3
% 0.20/0.40  # Initial clauses in saturation        : 22
% 0.20/0.40  # Processed clauses                    : 55
% 0.20/0.40  # ...of these trivial                  : 0
% 0.20/0.40  # ...subsumed                          : 1
% 0.20/0.40  # ...remaining for further processing  : 53
% 0.20/0.40  # Other redundant clauses eliminated   : 3
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 1
% 0.20/0.40  # Backward-rewritten                   : 6
% 0.20/0.40  # Generated clauses                    : 27
% 0.20/0.40  # ...of the previous two non-trivial   : 23
% 0.20/0.40  # Contextual simplify-reflections      : 0
% 0.20/0.40  # Paramodulations                      : 20
% 0.20/0.40  # Factorizations                       : 0
% 0.20/0.40  # Equation resolutions                 : 6
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 22
% 0.20/0.40  #    Positive orientable unit clauses  : 5
% 0.20/0.40  #    Positive unorientable unit clauses: 0
% 0.20/0.40  #    Negative unit clauses             : 3
% 0.20/0.40  #    Non-unit-clauses                  : 14
% 0.20/0.40  # Current number of unprocessed clauses: 8
% 0.20/0.40  # ...number of literals in the above   : 23
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 31
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 48
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 38
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 2
% 0.20/0.40  # Unit Clause-clause subsumption calls : 1
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 6
% 0.20/0.40  # BW rewrite match successes           : 1
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 1878
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.045 s
% 0.20/0.40  # System time              : 0.004 s
% 0.20/0.40  # Total time               : 0.049 s
% 0.20/0.40  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
