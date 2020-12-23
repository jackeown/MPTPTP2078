%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:03 EST 2020

% Result     : Theorem 26.95s
% Output     : CNFRefutation 26.95s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 244 expanded)
%              Number of clauses        :   32 ( 135 expanded)
%              Number of leaves         :    5 (  52 expanded)
%              Depth                    :   12
%              Number of atoms          :  145 (1149 expanded)
%              Number of equality atoms :   63 ( 468 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(l35_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(t73_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_xboole_0
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(c_0_5,plain,(
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

fof(c_0_6,plain,(
    ! [X14,X15,X16,X17,X18,X19,X20,X21] :
      ( ( ~ r2_hidden(X17,X16)
        | X17 = X14
        | X17 = X15
        | X16 != k2_tarski(X14,X15) )
      & ( X18 != X14
        | r2_hidden(X18,X16)
        | X16 != k2_tarski(X14,X15) )
      & ( X18 != X15
        | r2_hidden(X18,X16)
        | X16 != k2_tarski(X14,X15) )
      & ( esk2_3(X19,X20,X21) != X19
        | ~ r2_hidden(esk2_3(X19,X20,X21),X21)
        | X21 = k2_tarski(X19,X20) )
      & ( esk2_3(X19,X20,X21) != X20
        | ~ r2_hidden(esk2_3(X19,X20,X21),X21)
        | X21 = k2_tarski(X19,X20) )
      & ( r2_hidden(esk2_3(X19,X20,X21),X21)
        | esk2_3(X19,X20,X21) = X19
        | esk2_3(X19,X20,X21) = X20
        | X21 = k2_tarski(X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_7,plain,(
    ! [X28,X29,X30] :
      ( ( r2_hidden(X28,X29)
        | ~ r2_hidden(X28,k4_xboole_0(X29,k1_tarski(X30))) )
      & ( X28 != X30
        | ~ r2_hidden(X28,k4_xboole_0(X29,k1_tarski(X30))) )
      & ( ~ r2_hidden(X28,X29)
        | X28 = X30
        | r2_hidden(X28,k4_xboole_0(X29,k1_tarski(X30))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

cnf(c_0_8,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X23,X24] :
      ( ( k4_xboole_0(k1_tarski(X23),X24) != k1_xboole_0
        | r2_hidden(X23,X24) )
      & ( ~ r2_hidden(X23,X24)
        | k4_xboole_0(k1_tarski(X23),X24) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l35_zfmisc_1])])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,k2_tarski(X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_9])])).

cnf(c_0_14,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X1))) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,k4_xboole_0(k2_tarski(X2,X1),X3))
    | r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_xboole_0
      <=> ( r2_hidden(X1,X3)
          & r2_hidden(X2,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t73_zfmisc_1])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,k1_tarski(X2))
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_16])).

fof(c_0_20,negated_conjecture,
    ( ( k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k1_xboole_0
      | ~ r2_hidden(esk3_0,esk5_0)
      | ~ r2_hidden(esk4_0,esk5_0) )
    & ( r2_hidden(esk3_0,esk5_0)
      | k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k1_xboole_0 )
    & ( r2_hidden(esk4_0,esk5_0)
      | k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])])).

cnf(c_0_21,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0)
    | k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_tarski(X3,X2)) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk1_3(X1,X2,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,k2_tarski(X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_24])])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0)
    | r2_hidden(esk4_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_25])).

cnf(c_0_30,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_31,plain,
    ( esk1_3(k2_tarski(X1,X2),X3,k1_xboole_0) = X2
    | esk1_3(k2_tarski(X1,X2),X3,k1_xboole_0) = X1
    | k4_xboole_0(k2_tarski(X1,X2),X3) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,k4_xboole_0(k2_tarski(X1,X2),X3))
    | r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_12,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_34,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k1_xboole_0
    | ~ r2_hidden(esk3_0,esk5_0)
    | ~ r2_hidden(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[c_0_29,c_0_22])).

cnf(c_0_36,plain,
    ( esk1_3(k2_tarski(X1,X2),X3,k1_xboole_0) = X2
    | k4_xboole_0(k2_tarski(X1,X2),X3) = k1_xboole_0
    | ~ r2_hidden(X1,X3) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_22])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_22])).

cnf(c_0_38,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k1_xboole_0
    | ~ r2_hidden(esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35])])).

cnf(c_0_39,negated_conjecture,
    ( esk1_3(k2_tarski(esk3_0,X1),esk5_0,k1_xboole_0) = X1
    | k4_xboole_0(k2_tarski(esk3_0,X1),esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_37])])).

cnf(c_0_41,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk3_0,X1),esk5_0) = k1_xboole_0
    | ~ r2_hidden(X1,esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_39]),c_0_22])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_35])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:00:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 26.95/27.13  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 26.95/27.13  # and selection function SelectComplexExceptUniqMaxHorn.
% 26.95/27.13  #
% 26.95/27.13  # Preprocessing time       : 0.028 s
% 26.95/27.13  # Presaturation interreduction done
% 26.95/27.13  
% 26.95/27.13  # Proof found!
% 26.95/27.13  # SZS status Theorem
% 26.95/27.13  # SZS output start CNFRefutation
% 26.95/27.13  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 26.95/27.13  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 26.95/27.13  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 26.95/27.13  fof(l35_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 26.95/27.13  fof(t73_zfmisc_1, conjecture, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k1_xboole_0<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_zfmisc_1)).
% 26.95/27.13  fof(c_0_5, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6))&(~r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k4_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k4_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 26.95/27.13  fof(c_0_6, plain, ![X14, X15, X16, X17, X18, X19, X20, X21]:(((~r2_hidden(X17,X16)|(X17=X14|X17=X15)|X16!=k2_tarski(X14,X15))&((X18!=X14|r2_hidden(X18,X16)|X16!=k2_tarski(X14,X15))&(X18!=X15|r2_hidden(X18,X16)|X16!=k2_tarski(X14,X15))))&(((esk2_3(X19,X20,X21)!=X19|~r2_hidden(esk2_3(X19,X20,X21),X21)|X21=k2_tarski(X19,X20))&(esk2_3(X19,X20,X21)!=X20|~r2_hidden(esk2_3(X19,X20,X21),X21)|X21=k2_tarski(X19,X20)))&(r2_hidden(esk2_3(X19,X20,X21),X21)|(esk2_3(X19,X20,X21)=X19|esk2_3(X19,X20,X21)=X20)|X21=k2_tarski(X19,X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 26.95/27.13  fof(c_0_7, plain, ![X28, X29, X30]:(((r2_hidden(X28,X29)|~r2_hidden(X28,k4_xboole_0(X29,k1_tarski(X30))))&(X28!=X30|~r2_hidden(X28,k4_xboole_0(X29,k1_tarski(X30)))))&(~r2_hidden(X28,X29)|X28=X30|r2_hidden(X28,k4_xboole_0(X29,k1_tarski(X30))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 26.95/27.13  cnf(c_0_8, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 26.95/27.13  cnf(c_0_9, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 26.95/27.13  cnf(c_0_10, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 26.95/27.13  fof(c_0_11, plain, ![X23, X24]:((k4_xboole_0(k1_tarski(X23),X24)!=k1_xboole_0|r2_hidden(X23,X24))&(~r2_hidden(X23,X24)|k4_xboole_0(k1_tarski(X23),X24)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l35_zfmisc_1])])).
% 26.95/27.13  cnf(c_0_12, plain, (r2_hidden(X1,k4_xboole_0(X2,X3))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_8])).
% 26.95/27.13  cnf(c_0_13, plain, (r2_hidden(X1,k2_tarski(X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_9])])).
% 26.95/27.13  cnf(c_0_14, plain, (~r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X1)))), inference(er,[status(thm)],[c_0_10])).
% 26.95/27.13  cnf(c_0_15, plain, (k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 26.95/27.13  cnf(c_0_16, plain, (r2_hidden(X1,k4_xboole_0(k2_tarski(X2,X1),X3))|r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 26.95/27.13  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k1_xboole_0<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3)))), inference(assume_negation,[status(cth)],[t73_zfmisc_1])).
% 26.95/27.13  cnf(c_0_18, plain, (~r2_hidden(X1,k1_tarski(X2))|~r2_hidden(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 26.95/27.13  cnf(c_0_19, plain, (r2_hidden(X1,k1_tarski(X1))), inference(spm,[status(thm)],[c_0_14, c_0_16])).
% 26.95/27.13  fof(c_0_20, negated_conjecture, ((k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k1_xboole_0|(~r2_hidden(esk3_0,esk5_0)|~r2_hidden(esk4_0,esk5_0)))&((r2_hidden(esk3_0,esk5_0)|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k1_xboole_0)&(r2_hidden(esk4_0,esk5_0)|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])])).
% 26.95/27.13  cnf(c_0_21, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 26.95/27.13  cnf(c_0_22, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 26.95/27.13  cnf(c_0_23, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 26.95/27.13  cnf(c_0_24, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 26.95/27.13  cnf(c_0_25, negated_conjecture, (r2_hidden(esk4_0,esk5_0)|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 26.95/27.13  cnf(c_0_26, plain, (X1=X2|X1=X3|~r2_hidden(X1,k2_tarski(X3,X2))), inference(er,[status(thm)],[c_0_21])).
% 26.95/27.13  cnf(c_0_27, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|r2_hidden(esk1_3(X1,X2,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 26.95/27.13  cnf(c_0_28, plain, (r2_hidden(X1,k2_tarski(X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_24])])).
% 26.95/27.13  cnf(c_0_29, negated_conjecture, (r2_hidden(esk4_0,esk5_0)|r2_hidden(esk4_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_16, c_0_25])).
% 26.95/27.13  cnf(c_0_30, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 26.95/27.13  cnf(c_0_31, plain, (esk1_3(k2_tarski(X1,X2),X3,k1_xboole_0)=X2|esk1_3(k2_tarski(X1,X2),X3,k1_xboole_0)=X1|k4_xboole_0(k2_tarski(X1,X2),X3)=k1_xboole_0), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 26.95/27.13  cnf(c_0_32, plain, (r2_hidden(X1,k4_xboole_0(k2_tarski(X1,X2),X3))|r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_12, c_0_28])).
% 26.95/27.13  cnf(c_0_33, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 26.95/27.13  cnf(c_0_34, negated_conjecture, (k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k1_xboole_0|~r2_hidden(esk3_0,esk5_0)|~r2_hidden(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 26.95/27.13  cnf(c_0_35, negated_conjecture, (r2_hidden(esk4_0,esk5_0)), inference(sr,[status(thm)],[c_0_29, c_0_22])).
% 26.95/27.13  cnf(c_0_36, plain, (esk1_3(k2_tarski(X1,X2),X3,k1_xboole_0)=X2|k4_xboole_0(k2_tarski(X1,X2),X3)=k1_xboole_0|~r2_hidden(X1,X3)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_22])).
% 26.95/27.13  cnf(c_0_37, negated_conjecture, (r2_hidden(esk3_0,esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_22])).
% 26.95/27.13  cnf(c_0_38, negated_conjecture, (k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k1_xboole_0|~r2_hidden(esk3_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35])])).
% 26.95/27.13  cnf(c_0_39, negated_conjecture, (esk1_3(k2_tarski(esk3_0,X1),esk5_0,k1_xboole_0)=X1|k4_xboole_0(k2_tarski(esk3_0,X1),esk5_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 26.95/27.13  cnf(c_0_40, negated_conjecture, (k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_37])])).
% 26.95/27.13  cnf(c_0_41, negated_conjecture, (k4_xboole_0(k2_tarski(esk3_0,X1),esk5_0)=k1_xboole_0|~r2_hidden(X1,esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_39]), c_0_22])).
% 26.95/27.13  cnf(c_0_42, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_35])]), ['proof']).
% 26.95/27.13  # SZS output end CNFRefutation
% 26.95/27.13  # Proof object total steps             : 43
% 26.95/27.13  # Proof object clause steps            : 32
% 26.95/27.13  # Proof object formula steps           : 11
% 26.95/27.13  # Proof object conjectures             : 14
% 26.95/27.13  # Proof object clause conjectures      : 11
% 26.95/27.13  # Proof object formula conjectures     : 3
% 26.95/27.13  # Proof object initial clauses used    : 11
% 26.95/27.13  # Proof object initial formulas used   : 5
% 26.95/27.13  # Proof object generating inferences   : 13
% 26.95/27.13  # Proof object simplifying inferences  : 17
% 26.95/27.13  # Training examples: 0 positive, 0 negative
% 26.95/27.13  # Parsed axioms                        : 7
% 26.95/27.13  # Removed by relevancy pruning/SinE    : 0
% 26.95/27.13  # Initial clauses                      : 27
% 26.95/27.13  # Removed in clause preprocessing      : 0
% 26.95/27.13  # Initial clauses in saturation        : 27
% 26.95/27.13  # Processed clauses                    : 47026
% 26.95/27.13  # ...of these trivial                  : 63
% 26.95/27.13  # ...subsumed                          : 43070
% 26.95/27.13  # ...remaining for further processing  : 3893
% 26.95/27.13  # Other redundant clauses eliminated   : 11030
% 26.95/27.13  # Clauses deleted for lack of memory   : 0
% 26.95/27.13  # Backward-subsumed                    : 254
% 26.95/27.13  # Backward-rewritten                   : 45
% 26.95/27.13  # Generated clauses                    : 1901135
% 26.95/27.13  # ...of the previous two non-trivial   : 1732676
% 26.95/27.13  # Contextual simplify-reflections      : 15
% 26.95/27.13  # Paramodulations                      : 1888069
% 26.95/27.13  # Factorizations                       : 1806
% 26.95/27.13  # Equation resolutions                 : 11260
% 26.95/27.13  # Propositional unsat checks           : 0
% 26.95/27.13  #    Propositional check models        : 0
% 26.95/27.13  #    Propositional check unsatisfiable : 0
% 26.95/27.13  #    Propositional clauses             : 0
% 26.95/27.13  #    Propositional clauses after purity: 0
% 26.95/27.13  #    Propositional unsat core size     : 0
% 26.95/27.13  #    Propositional preprocessing time  : 0.000
% 26.95/27.13  #    Propositional encoding time       : 0.000
% 26.95/27.13  #    Propositional solver time         : 0.000
% 26.95/27.13  #    Success case prop preproc time    : 0.000
% 26.95/27.13  #    Success case prop encoding time   : 0.000
% 26.95/27.13  #    Success case prop solver time     : 0.000
% 26.95/27.13  # Current number of processed clauses  : 3558
% 26.95/27.13  #    Positive orientable unit clauses  : 52
% 26.95/27.13  #    Positive unorientable unit clauses: 1
% 26.95/27.13  #    Negative unit clauses             : 25
% 26.95/27.13  #    Non-unit-clauses                  : 3480
% 26.95/27.13  # Current number of unprocessed clauses: 1681430
% 26.95/27.13  # ...number of literals in the above   : 10497985
% 26.95/27.13  # Current number of archived formulas  : 0
% 26.95/27.13  # Current number of archived clauses   : 327
% 26.95/27.13  # Clause-clause subsumption calls (NU) : 3713684
% 26.95/27.13  # Rec. Clause-clause subsumption calls : 757412
% 26.95/27.13  # Non-unit clause-clause subsumptions  : 23821
% 26.95/27.13  # Unit Clause-clause subsumption calls : 11644
% 26.95/27.13  # Rewrite failures with RHS unbound    : 0
% 26.95/27.13  # BW rewrite match attempts            : 380
% 26.95/27.13  # BW rewrite match successes           : 20
% 26.95/27.13  # Condensation attempts                : 0
% 26.95/27.13  # Condensation successes               : 0
% 26.95/27.13  # Termbank termtop insertions          : 52332258
% 26.95/27.20  
% 26.95/27.20  # -------------------------------------------------
% 26.95/27.20  # User time                : 26.017 s
% 26.95/27.20  # System time              : 0.834 s
% 26.95/27.20  # Total time               : 26.851 s
% 26.95/27.20  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
