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
% DateTime   : Thu Dec  3 10:48:52 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 159 expanded)
%              Number of clauses        :   30 (  88 expanded)
%              Number of leaves         :    6 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :  121 ( 723 expanded)
%              Number of equality atoms :   43 ( 224 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(t60_relat_1,conjecture,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(c_0_6,plain,(
    ! [X9,X10,X11,X12,X13,X14,X15,X16] :
      ( ( r2_hidden(X12,X9)
        | ~ r2_hidden(X12,X11)
        | X11 != k4_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X12,X10)
        | ~ r2_hidden(X12,X11)
        | X11 != k4_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X13,X9)
        | r2_hidden(X13,X10)
        | r2_hidden(X13,X11)
        | X11 != k4_xboole_0(X9,X10) )
      & ( ~ r2_hidden(esk2_3(X14,X15,X16),X16)
        | ~ r2_hidden(esk2_3(X14,X15,X16),X14)
        | r2_hidden(esk2_3(X14,X15,X16),X15)
        | X16 = k4_xboole_0(X14,X15) )
      & ( r2_hidden(esk2_3(X14,X15,X16),X14)
        | r2_hidden(esk2_3(X14,X15,X16),X16)
        | X16 = k4_xboole_0(X14,X15) )
      & ( ~ r2_hidden(esk2_3(X14,X15,X16),X15)
        | r2_hidden(esk2_3(X14,X15,X16),X16)
        | X16 = k4_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_7,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_8,plain,(
    ! [X18] : k4_xboole_0(X18,k1_xboole_0) = X18 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_9,plain,(
    ! [X19,X20,X21,X23,X24,X25,X26,X28] :
      ( ( ~ r2_hidden(X21,X20)
        | r2_hidden(k4_tarski(X21,esk3_3(X19,X20,X21)),X19)
        | X20 != k1_relat_1(X19) )
      & ( ~ r2_hidden(k4_tarski(X23,X24),X19)
        | r2_hidden(X23,X20)
        | X20 != k1_relat_1(X19) )
      & ( ~ r2_hidden(esk4_2(X25,X26),X26)
        | ~ r2_hidden(k4_tarski(esk4_2(X25,X26),X28),X25)
        | X26 = k1_relat_1(X25) )
      & ( r2_hidden(esk4_2(X25,X26),X26)
        | r2_hidden(k4_tarski(esk4_2(X25,X26),esk5_2(X25,X26)),X25)
        | X26 = k1_relat_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

fof(c_0_10,plain,(
    ! [X30,X31,X32,X34,X35,X36,X37,X39] :
      ( ( ~ r2_hidden(X32,X31)
        | r2_hidden(k4_tarski(esk6_3(X30,X31,X32),X32),X30)
        | X31 != k2_relat_1(X30) )
      & ( ~ r2_hidden(k4_tarski(X35,X34),X30)
        | r2_hidden(X34,X31)
        | X31 != k2_relat_1(X30) )
      & ( ~ r2_hidden(esk7_2(X36,X37),X37)
        | ~ r2_hidden(k4_tarski(X39,esk7_2(X36,X37)),X36)
        | X37 = k2_relat_1(X36) )
      & ( r2_hidden(esk7_2(X36,X37),X37)
        | r2_hidden(k4_tarski(esk8_2(X36,X37),esk7_2(X36,X37)),X36)
        | X37 = k2_relat_1(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_11,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(k4_tarski(X1,esk3_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(esk6_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,plain,
    ( r2_hidden(k4_tarski(X1,esk3_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( r2_hidden(k4_tarski(esk6_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(k4_tarski(X1,esk3_3(k1_xboole_0,k1_relat_1(k1_xboole_0),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(k4_tarski(esk6_3(k1_xboole_0,k2_relat_1(k1_xboole_0),X1),X1),X2)
    | ~ r2_hidden(X1,k2_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_17])).

cnf(c_0_21,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_22,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t60_relat_1])).

cnf(c_0_23,plain,
    ( ~ r2_hidden(X1,k1_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_16])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,k2_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_17])).

cnf(c_0_26,plain,
    ( X1 = k4_xboole_0(X2,X2)
    | r2_hidden(esk2_3(X2,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_19])).

fof(c_0_27,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_28,negated_conjecture,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(fof_nnf,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k4_xboole_0(k1_relat_1(k1_xboole_0),X1) = k1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,plain,
    ( k2_relat_1(k1_xboole_0) = k4_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( k2_relat_1(k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ r2_hidden(esk1_1(k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33])])).

cnf(c_0_37,plain,
    ( k1_relat_1(k1_xboole_0) = k4_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[c_0_30,c_0_33])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_24])).

cnf(c_0_39,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( k4_xboole_0(X1,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_40,c_0_41]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:41:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.42  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.42  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.42  #
% 0.20/0.42  # Preprocessing time       : 0.028 s
% 0.20/0.42  # Presaturation interreduction done
% 0.20/0.42  
% 0.20/0.42  # Proof found!
% 0.20/0.42  # SZS status Theorem
% 0.20/0.42  # SZS output start CNFRefutation
% 0.20/0.42  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.20/0.42  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.20/0.42  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 0.20/0.42  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 0.20/0.42  fof(t60_relat_1, conjecture, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.20/0.42  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.42  fof(c_0_6, plain, ![X9, X10, X11, X12, X13, X14, X15, X16]:((((r2_hidden(X12,X9)|~r2_hidden(X12,X11)|X11!=k4_xboole_0(X9,X10))&(~r2_hidden(X12,X10)|~r2_hidden(X12,X11)|X11!=k4_xboole_0(X9,X10)))&(~r2_hidden(X13,X9)|r2_hidden(X13,X10)|r2_hidden(X13,X11)|X11!=k4_xboole_0(X9,X10)))&((~r2_hidden(esk2_3(X14,X15,X16),X16)|(~r2_hidden(esk2_3(X14,X15,X16),X14)|r2_hidden(esk2_3(X14,X15,X16),X15))|X16=k4_xboole_0(X14,X15))&((r2_hidden(esk2_3(X14,X15,X16),X14)|r2_hidden(esk2_3(X14,X15,X16),X16)|X16=k4_xboole_0(X14,X15))&(~r2_hidden(esk2_3(X14,X15,X16),X15)|r2_hidden(esk2_3(X14,X15,X16),X16)|X16=k4_xboole_0(X14,X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.20/0.42  cnf(c_0_7, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.42  fof(c_0_8, plain, ![X18]:k4_xboole_0(X18,k1_xboole_0)=X18, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.20/0.42  fof(c_0_9, plain, ![X19, X20, X21, X23, X24, X25, X26, X28]:(((~r2_hidden(X21,X20)|r2_hidden(k4_tarski(X21,esk3_3(X19,X20,X21)),X19)|X20!=k1_relat_1(X19))&(~r2_hidden(k4_tarski(X23,X24),X19)|r2_hidden(X23,X20)|X20!=k1_relat_1(X19)))&((~r2_hidden(esk4_2(X25,X26),X26)|~r2_hidden(k4_tarski(esk4_2(X25,X26),X28),X25)|X26=k1_relat_1(X25))&(r2_hidden(esk4_2(X25,X26),X26)|r2_hidden(k4_tarski(esk4_2(X25,X26),esk5_2(X25,X26)),X25)|X26=k1_relat_1(X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.20/0.42  fof(c_0_10, plain, ![X30, X31, X32, X34, X35, X36, X37, X39]:(((~r2_hidden(X32,X31)|r2_hidden(k4_tarski(esk6_3(X30,X31,X32),X32),X30)|X31!=k2_relat_1(X30))&(~r2_hidden(k4_tarski(X35,X34),X30)|r2_hidden(X34,X31)|X31!=k2_relat_1(X30)))&((~r2_hidden(esk7_2(X36,X37),X37)|~r2_hidden(k4_tarski(X39,esk7_2(X36,X37)),X36)|X37=k2_relat_1(X36))&(r2_hidden(esk7_2(X36,X37),X37)|r2_hidden(k4_tarski(esk8_2(X36,X37),esk7_2(X36,X37)),X36)|X37=k2_relat_1(X36)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.20/0.42  cnf(c_0_11, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_7])).
% 0.20/0.42  cnf(c_0_12, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.42  cnf(c_0_13, plain, (r2_hidden(k4_tarski(X1,esk3_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.42  cnf(c_0_14, plain, (r2_hidden(k4_tarski(esk6_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.42  cnf(c_0_15, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.20/0.42  cnf(c_0_16, plain, (r2_hidden(k4_tarski(X1,esk3_3(X2,k1_relat_1(X2),X1)),X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_13])).
% 0.20/0.42  cnf(c_0_17, plain, (r2_hidden(k4_tarski(esk6_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_14])).
% 0.20/0.42  cnf(c_0_18, plain, (~r2_hidden(k4_tarski(X1,esk3_3(k1_xboole_0,k1_relat_1(k1_xboole_0),X1)),X2)|~r2_hidden(X1,k1_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.20/0.42  cnf(c_0_19, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.42  cnf(c_0_20, plain, (~r2_hidden(k4_tarski(esk6_3(k1_xboole_0,k2_relat_1(k1_xboole_0),X1),X1),X2)|~r2_hidden(X1,k2_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_15, c_0_17])).
% 0.20/0.42  cnf(c_0_21, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.42  fof(c_0_22, negated_conjecture, ~((k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0)), inference(assume_negation,[status(cth)],[t60_relat_1])).
% 0.20/0.42  cnf(c_0_23, plain, (~r2_hidden(X1,k1_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_18, c_0_16])).
% 0.20/0.42  cnf(c_0_24, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk2_3(X1,X2,X1),X1)), inference(ef,[status(thm)],[c_0_19])).
% 0.20/0.42  cnf(c_0_25, plain, (~r2_hidden(X1,k2_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_20, c_0_17])).
% 0.20/0.42  cnf(c_0_26, plain, (X1=k4_xboole_0(X2,X2)|r2_hidden(esk2_3(X2,X2,X1),X1)), inference(spm,[status(thm)],[c_0_21, c_0_19])).
% 0.20/0.42  fof(c_0_27, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.42  fof(c_0_28, negated_conjecture, (k1_relat_1(k1_xboole_0)!=k1_xboole_0|k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(fof_nnf,[status(thm)],[c_0_22])).
% 0.20/0.42  cnf(c_0_29, plain, (k4_xboole_0(k1_relat_1(k1_xboole_0),X1)=k1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.42  cnf(c_0_30, plain, (k2_relat_1(k1_xboole_0)=k4_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.42  cnf(c_0_31, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.42  cnf(c_0_32, negated_conjecture, (k1_relat_1(k1_xboole_0)!=k1_xboole_0|k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.42  cnf(c_0_33, plain, (k2_relat_1(k1_xboole_0)=k1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.42  cnf(c_0_34, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.42  cnf(c_0_35, plain, (v1_xboole_0(k1_xboole_0)|~r2_hidden(esk1_1(k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_15, c_0_31])).
% 0.20/0.42  cnf(c_0_36, negated_conjecture, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33])])).
% 0.20/0.42  cnf(c_0_37, plain, (k1_relat_1(k1_xboole_0)=k4_xboole_0(X1,X1)), inference(rw,[status(thm)],[c_0_30, c_0_33])).
% 0.20/0.42  cnf(c_0_38, plain, (k4_xboole_0(X1,X2)=X1|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_34, c_0_24])).
% 0.20/0.42  cnf(c_0_39, plain, (v1_xboole_0(k1_xboole_0)), inference(spm,[status(thm)],[c_0_35, c_0_31])).
% 0.20/0.42  cnf(c_0_40, negated_conjecture, (k4_xboole_0(X1,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.42  cnf(c_0_41, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.42  cnf(c_0_42, negated_conjecture, ($false), inference(spm,[status(thm)],[c_0_40, c_0_41]), ['proof']).
% 0.20/0.42  # SZS output end CNFRefutation
% 0.20/0.42  # Proof object total steps             : 43
% 0.20/0.42  # Proof object clause steps            : 30
% 0.20/0.42  # Proof object formula steps           : 13
% 0.20/0.42  # Proof object conjectures             : 7
% 0.20/0.42  # Proof object clause conjectures      : 4
% 0.20/0.42  # Proof object formula conjectures     : 3
% 0.20/0.42  # Proof object initial clauses used    : 9
% 0.20/0.42  # Proof object initial formulas used   : 6
% 0.20/0.42  # Proof object generating inferences   : 16
% 0.20/0.42  # Proof object simplifying inferences  : 6
% 0.20/0.42  # Training examples: 0 positive, 0 negative
% 0.20/0.42  # Parsed axioms                        : 6
% 0.20/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.42  # Initial clauses                      : 18
% 0.20/0.42  # Removed in clause preprocessing      : 0
% 0.20/0.42  # Initial clauses in saturation        : 18
% 0.20/0.42  # Processed clauses                    : 481
% 0.20/0.42  # ...of these trivial                  : 5
% 0.20/0.42  # ...subsumed                          : 190
% 0.20/0.42  # ...remaining for further processing  : 286
% 0.20/0.42  # Other redundant clauses eliminated   : 7
% 0.20/0.42  # Clauses deleted for lack of memory   : 0
% 0.20/0.42  # Backward-subsumed                    : 0
% 0.20/0.42  # Backward-rewritten                   : 108
% 0.20/0.42  # Generated clauses                    : 3882
% 0.20/0.42  # ...of the previous two non-trivial   : 3815
% 0.20/0.42  # Contextual simplify-reflections      : 0
% 0.20/0.42  # Paramodulations                      : 3867
% 0.20/0.42  # Factorizations                       : 8
% 0.20/0.42  # Equation resolutions                 : 7
% 0.20/0.42  # Propositional unsat checks           : 0
% 0.20/0.42  #    Propositional check models        : 0
% 0.20/0.42  #    Propositional check unsatisfiable : 0
% 0.20/0.42  #    Propositional clauses             : 0
% 0.20/0.42  #    Propositional clauses after purity: 0
% 0.20/0.42  #    Propositional unsat core size     : 0
% 0.20/0.42  #    Propositional preprocessing time  : 0.000
% 0.20/0.42  #    Propositional encoding time       : 0.000
% 0.20/0.42  #    Propositional solver time         : 0.000
% 0.20/0.42  #    Success case prop preproc time    : 0.000
% 0.20/0.42  #    Success case prop encoding time   : 0.000
% 0.20/0.42  #    Success case prop solver time     : 0.000
% 0.20/0.42  # Current number of processed clauses  : 153
% 0.20/0.42  #    Positive orientable unit clauses  : 25
% 0.20/0.42  #    Positive unorientable unit clauses: 1
% 0.20/0.42  #    Negative unit clauses             : 32
% 0.20/0.42  #    Non-unit-clauses                  : 95
% 0.20/0.42  # Current number of unprocessed clauses: 3362
% 0.20/0.42  # ...number of literals in the above   : 6604
% 0.20/0.42  # Current number of archived formulas  : 0
% 0.20/0.42  # Current number of archived clauses   : 126
% 0.20/0.42  # Clause-clause subsumption calls (NU) : 1717
% 0.20/0.42  # Rec. Clause-clause subsumption calls : 1492
% 0.20/0.42  # Non-unit clause-clause subsumptions  : 27
% 0.20/0.42  # Unit Clause-clause subsumption calls : 2544
% 0.20/0.42  # Rewrite failures with RHS unbound    : 6
% 0.20/0.42  # BW rewrite match attempts            : 476
% 0.20/0.42  # BW rewrite match successes           : 17
% 0.20/0.42  # Condensation attempts                : 0
% 0.20/0.42  # Condensation successes               : 0
% 0.20/0.42  # Termbank termtop insertions          : 43188
% 0.20/0.43  
% 0.20/0.43  # -------------------------------------------------
% 0.20/0.43  # User time                : 0.080 s
% 0.20/0.43  # System time              : 0.006 s
% 0.20/0.43  # Total time               : 0.086 s
% 0.20/0.43  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
