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
% DateTime   : Thu Dec  3 10:51:35 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 284 expanded)
%              Number of clauses        :   40 ( 143 expanded)
%              Number of leaves         :    8 (  70 expanded)
%              Depth                    :   15
%              Number of atoms          :  167 (1071 expanded)
%              Number of equality atoms :   46 ( 225 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

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

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(d14_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k10_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(k4_tarski(X4,X5),X1)
                  & r2_hidden(X5,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

fof(t168_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,X1) = k10_relat_1(X2,k3_xboole_0(k2_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

fof(t173_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k10_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(c_0_8,plain,(
    ! [X27,X28,X29,X31,X32,X33,X34,X36] :
      ( ( ~ r2_hidden(X29,X28)
        | r2_hidden(k4_tarski(esk5_3(X27,X28,X29),X29),X27)
        | X28 != k2_relat_1(X27) )
      & ( ~ r2_hidden(k4_tarski(X32,X31),X27)
        | r2_hidden(X31,X28)
        | X28 != k2_relat_1(X27) )
      & ( ~ r2_hidden(esk6_2(X33,X34),X34)
        | ~ r2_hidden(k4_tarski(X36,esk6_2(X33,X34)),X33)
        | X34 = k2_relat_1(X33) )
      & ( r2_hidden(esk6_2(X33,X34),X34)
        | r2_hidden(k4_tarski(esk7_2(X33,X34),esk6_2(X33,X34)),X33)
        | X34 = k2_relat_1(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

fof(c_0_9,plain,(
    ! [X8,X9,X11,X12,X13] :
      ( ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_xboole_0(X8,X9) )
      & ( r2_hidden(esk1_2(X8,X9),X9)
        | r1_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X13,X11)
        | ~ r2_hidden(X13,X12)
        | ~ r1_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_10,plain,
    ( r2_hidden(k4_tarski(esk5_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X6,X7] :
      ( ( ~ r1_xboole_0(X6,X7)
        | k3_xboole_0(X6,X7) = k1_xboole_0 )
      & ( k3_xboole_0(X6,X7) != k1_xboole_0
        | r1_xboole_0(X6,X7) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_14,plain,(
    ! [X14] : k3_xboole_0(X14,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_15,plain,
    ( r2_hidden(k4_tarski(esk5_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(k4_tarski(esk5_3(X1,k2_relat_1(X1),X2),X2),X3)
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_15])).

cnf(c_0_21,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_23,plain,(
    ! [X15,X16,X17,X18,X20,X21,X22,X23,X25] :
      ( ( r2_hidden(k4_tarski(X18,esk2_4(X15,X16,X17,X18)),X15)
        | ~ r2_hidden(X18,X17)
        | X17 != k10_relat_1(X15,X16)
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(esk2_4(X15,X16,X17,X18),X16)
        | ~ r2_hidden(X18,X17)
        | X17 != k10_relat_1(X15,X16)
        | ~ v1_relat_1(X15) )
      & ( ~ r2_hidden(k4_tarski(X20,X21),X15)
        | ~ r2_hidden(X21,X16)
        | r2_hidden(X20,X17)
        | X17 != k10_relat_1(X15,X16)
        | ~ v1_relat_1(X15) )
      & ( ~ r2_hidden(esk3_3(X15,X22,X23),X23)
        | ~ r2_hidden(k4_tarski(esk3_3(X15,X22,X23),X25),X15)
        | ~ r2_hidden(X25,X22)
        | X23 = k10_relat_1(X15,X22)
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(k4_tarski(esk3_3(X15,X22,X23),esk4_3(X15,X22,X23)),X15)
        | r2_hidden(esk3_3(X15,X22,X23),X23)
        | X23 = k10_relat_1(X15,X22)
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(esk4_3(X15,X22,X23),X22)
        | r2_hidden(esk3_3(X15,X22,X23),X23)
        | X23 = k10_relat_1(X15,X22)
        | ~ v1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

fof(c_0_24,plain,(
    ! [X38,X39] :
      ( ~ v1_relat_1(X39)
      | k10_relat_1(X39,X38) = k10_relat_1(X39,k3_xboole_0(k2_relat_1(X39),X38)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_relat_1])])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( k10_relat_1(X2,X1) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t173_relat_1])).

cnf(c_0_26,plain,
    ( ~ r2_hidden(X1,k2_relat_1(X2))
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_15])).

cnf(c_0_27,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_28,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( k10_relat_1(X1,X2) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_32,negated_conjecture,
    ( v1_relat_1(esk9_0)
    & ( k10_relat_1(esk9_0,esk8_0) != k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(esk9_0),esk8_0) )
    & ( k10_relat_1(esk9_0,esk8_0) = k1_xboole_0
      | r1_xboole_0(k2_relat_1(esk9_0),esk8_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

cnf(c_0_33,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

cnf(c_0_34,plain,
    ( r2_hidden(esk2_4(X1,X2,k10_relat_1(X1,X2),X3),X2)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,k10_relat_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( r2_hidden(esk6_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk7_2(X1,X2),esk6_2(X1,X2)),X1)
    | X2 = k2_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_36,plain,
    ( k10_relat_1(X1,k1_xboole_0) = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( k10_relat_1(esk9_0,esk8_0) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(esk9_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k10_relat_1(X1,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk6_2(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_35]),c_0_27])).

cnf(c_0_41,negated_conjecture,
    ( k10_relat_1(esk9_0,esk8_0) = k10_relat_1(esk9_0,k1_xboole_0)
    | k10_relat_1(esk9_0,esk8_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])])).

cnf(c_0_42,plain,
    ( k10_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X5 != k10_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_44,negated_conjecture,
    ( k10_relat_1(esk9_0,esk8_0) = k1_xboole_0
    | k10_relat_1(esk9_0,k1_xboole_0) != k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( k10_relat_1(esk9_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_38])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( k10_relat_1(esk9_0,esk8_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45])])).

cnf(c_0_48,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X1,X2),esk9_0)
    | ~ r2_hidden(X2,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_38])]),c_0_33])).

cnf(c_0_49,negated_conjecture,
    ( ~ r2_hidden(X1,k2_relat_1(esk9_0))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_15])).

cnf(c_0_50,negated_conjecture,
    ( k10_relat_1(esk9_0,esk8_0) != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(esk9_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_51,negated_conjecture,
    ( r1_xboole_0(X1,k2_relat_1(esk9_0))
    | ~ r2_hidden(esk1_2(X1,k2_relat_1(esk9_0)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_17])).

cnf(c_0_52,negated_conjecture,
    ( k10_relat_1(esk9_0,k1_xboole_0) != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(esk9_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( r1_xboole_0(esk8_0,k2_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_12])).

cnf(c_0_54,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(esk9_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_45])])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_53]),c_0_54]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:39:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.50  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05AN
% 0.21/0.50  # and selection function PSelectComplexExceptUniqMaxPosHorn.
% 0.21/0.50  #
% 0.21/0.50  # Preprocessing time       : 0.028 s
% 0.21/0.50  # Presaturation interreduction done
% 0.21/0.50  
% 0.21/0.50  # Proof found!
% 0.21/0.50  # SZS status Theorem
% 0.21/0.50  # SZS output start CNFRefutation
% 0.21/0.50  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 0.21/0.50  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.21/0.50  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.21/0.50  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.21/0.50  fof(d14_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X4,X5),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_1)).
% 0.21/0.50  fof(t168_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k10_relat_1(X2,X1)=k10_relat_1(X2,k3_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 0.21/0.50  fof(t173_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 0.21/0.50  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.21/0.50  fof(c_0_8, plain, ![X27, X28, X29, X31, X32, X33, X34, X36]:(((~r2_hidden(X29,X28)|r2_hidden(k4_tarski(esk5_3(X27,X28,X29),X29),X27)|X28!=k2_relat_1(X27))&(~r2_hidden(k4_tarski(X32,X31),X27)|r2_hidden(X31,X28)|X28!=k2_relat_1(X27)))&((~r2_hidden(esk6_2(X33,X34),X34)|~r2_hidden(k4_tarski(X36,esk6_2(X33,X34)),X33)|X34=k2_relat_1(X33))&(r2_hidden(esk6_2(X33,X34),X34)|r2_hidden(k4_tarski(esk7_2(X33,X34),esk6_2(X33,X34)),X33)|X34=k2_relat_1(X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.21/0.50  fof(c_0_9, plain, ![X8, X9, X11, X12, X13]:(((r2_hidden(esk1_2(X8,X9),X8)|r1_xboole_0(X8,X9))&(r2_hidden(esk1_2(X8,X9),X9)|r1_xboole_0(X8,X9)))&(~r2_hidden(X13,X11)|~r2_hidden(X13,X12)|~r1_xboole_0(X11,X12))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.21/0.50  cnf(c_0_10, plain, (r2_hidden(k4_tarski(esk5_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.50  cnf(c_0_11, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.50  cnf(c_0_12, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.50  fof(c_0_13, plain, ![X6, X7]:((~r1_xboole_0(X6,X7)|k3_xboole_0(X6,X7)=k1_xboole_0)&(k3_xboole_0(X6,X7)!=k1_xboole_0|r1_xboole_0(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.21/0.50  fof(c_0_14, plain, ![X14]:k3_xboole_0(X14,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.21/0.50  cnf(c_0_15, plain, (r2_hidden(k4_tarski(esk5_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_10])).
% 0.21/0.50  cnf(c_0_16, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.21/0.50  cnf(c_0_17, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.50  cnf(c_0_18, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.50  cnf(c_0_19, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.50  cnf(c_0_20, plain, (~r2_hidden(k4_tarski(esk5_3(X1,k2_relat_1(X1),X2),X2),X3)|~r2_hidden(X2,k2_relat_1(X1))|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_11, c_0_15])).
% 0.21/0.50  cnf(c_0_21, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.21/0.50  cnf(c_0_22, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.21/0.50  fof(c_0_23, plain, ![X15, X16, X17, X18, X20, X21, X22, X23, X25]:((((r2_hidden(k4_tarski(X18,esk2_4(X15,X16,X17,X18)),X15)|~r2_hidden(X18,X17)|X17!=k10_relat_1(X15,X16)|~v1_relat_1(X15))&(r2_hidden(esk2_4(X15,X16,X17,X18),X16)|~r2_hidden(X18,X17)|X17!=k10_relat_1(X15,X16)|~v1_relat_1(X15)))&(~r2_hidden(k4_tarski(X20,X21),X15)|~r2_hidden(X21,X16)|r2_hidden(X20,X17)|X17!=k10_relat_1(X15,X16)|~v1_relat_1(X15)))&((~r2_hidden(esk3_3(X15,X22,X23),X23)|(~r2_hidden(k4_tarski(esk3_3(X15,X22,X23),X25),X15)|~r2_hidden(X25,X22))|X23=k10_relat_1(X15,X22)|~v1_relat_1(X15))&((r2_hidden(k4_tarski(esk3_3(X15,X22,X23),esk4_3(X15,X22,X23)),X15)|r2_hidden(esk3_3(X15,X22,X23),X23)|X23=k10_relat_1(X15,X22)|~v1_relat_1(X15))&(r2_hidden(esk4_3(X15,X22,X23),X22)|r2_hidden(esk3_3(X15,X22,X23),X23)|X23=k10_relat_1(X15,X22)|~v1_relat_1(X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).
% 0.21/0.50  fof(c_0_24, plain, ![X38, X39]:(~v1_relat_1(X39)|k10_relat_1(X39,X38)=k10_relat_1(X39,k3_xboole_0(k2_relat_1(X39),X38))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_relat_1])])).
% 0.21/0.50  fof(c_0_25, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1)))), inference(assume_negation,[status(cth)],[t173_relat_1])).
% 0.21/0.50  cnf(c_0_26, plain, (~r2_hidden(X1,k2_relat_1(X2))|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_20, c_0_15])).
% 0.21/0.50  cnf(c_0_27, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.21/0.50  cnf(c_0_28, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.21/0.50  cnf(c_0_29, plain, (r2_hidden(esk2_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k10_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.50  cnf(c_0_30, plain, (k10_relat_1(X1,X2)=k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.50  cnf(c_0_31, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.50  fof(c_0_32, negated_conjecture, (v1_relat_1(esk9_0)&((k10_relat_1(esk9_0,esk8_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk9_0),esk8_0))&(k10_relat_1(esk9_0,esk8_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk9_0),esk8_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).
% 0.21/0.50  cnf(c_0_33, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])])).
% 0.21/0.50  cnf(c_0_34, plain, (r2_hidden(esk2_4(X1,X2,k10_relat_1(X1,X2),X3),X2)|~v1_relat_1(X1)|~r2_hidden(X3,k10_relat_1(X1,X2))), inference(er,[status(thm)],[c_0_29])).
% 0.21/0.50  cnf(c_0_35, plain, (r2_hidden(esk6_2(X1,X2),X2)|r2_hidden(k4_tarski(esk7_2(X1,X2),esk6_2(X1,X2)),X1)|X2=k2_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.50  cnf(c_0_36, plain, (k10_relat_1(X1,k1_xboole_0)=k10_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_xboole_0(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.21/0.50  cnf(c_0_37, negated_conjecture, (k10_relat_1(esk9_0,esk8_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk9_0),esk8_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.50  cnf(c_0_38, negated_conjecture, (v1_relat_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.50  cnf(c_0_39, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k10_relat_1(X1,k1_xboole_0))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.21/0.50  cnf(c_0_40, plain, (X1=k1_xboole_0|r2_hidden(esk6_2(k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_35]), c_0_27])).
% 0.21/0.50  cnf(c_0_41, negated_conjecture, (k10_relat_1(esk9_0,esk8_0)=k10_relat_1(esk9_0,k1_xboole_0)|k10_relat_1(esk9_0,esk8_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])])).
% 0.21/0.50  cnf(c_0_42, plain, (k10_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.21/0.50  cnf(c_0_43, plain, (r2_hidden(X1,X5)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X2,X4)|X5!=k10_relat_1(X3,X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.50  cnf(c_0_44, negated_conjecture, (k10_relat_1(esk9_0,esk8_0)=k1_xboole_0|k10_relat_1(esk9_0,k1_xboole_0)!=k1_xboole_0), inference(ef,[status(thm)],[c_0_41])).
% 0.21/0.50  cnf(c_0_45, negated_conjecture, (k10_relat_1(esk9_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_42, c_0_38])).
% 0.21/0.50  cnf(c_0_46, plain, (r2_hidden(X1,k10_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X4),X2)|~r2_hidden(X4,X3)), inference(er,[status(thm)],[c_0_43])).
% 0.21/0.50  cnf(c_0_47, negated_conjecture, (k10_relat_1(esk9_0,esk8_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_45])])).
% 0.21/0.50  cnf(c_0_48, negated_conjecture, (~r2_hidden(k4_tarski(X1,X2),esk9_0)|~r2_hidden(X2,esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_38])]), c_0_33])).
% 0.21/0.50  cnf(c_0_49, negated_conjecture, (~r2_hidden(X1,k2_relat_1(esk9_0))|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_48, c_0_15])).
% 0.21/0.50  cnf(c_0_50, negated_conjecture, (k10_relat_1(esk9_0,esk8_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk9_0),esk8_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.50  cnf(c_0_51, negated_conjecture, (r1_xboole_0(X1,k2_relat_1(esk9_0))|~r2_hidden(esk1_2(X1,k2_relat_1(esk9_0)),esk8_0)), inference(spm,[status(thm)],[c_0_49, c_0_17])).
% 0.21/0.50  cnf(c_0_52, negated_conjecture, (k10_relat_1(esk9_0,k1_xboole_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk9_0),esk8_0)), inference(spm,[status(thm)],[c_0_50, c_0_44])).
% 0.21/0.50  cnf(c_0_53, negated_conjecture, (r1_xboole_0(esk8_0,k2_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_51, c_0_12])).
% 0.21/0.50  cnf(c_0_54, negated_conjecture, (~r1_xboole_0(k2_relat_1(esk9_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_45])])).
% 0.21/0.50  cnf(c_0_55, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_53]), c_0_54]), ['proof']).
% 0.21/0.50  # SZS output end CNFRefutation
% 0.21/0.50  # Proof object total steps             : 56
% 0.21/0.50  # Proof object clause steps            : 40
% 0.21/0.50  # Proof object formula steps           : 16
% 0.21/0.50  # Proof object conjectures             : 17
% 0.21/0.50  # Proof object clause conjectures      : 14
% 0.21/0.50  # Proof object formula conjectures     : 3
% 0.21/0.50  # Proof object initial clauses used    : 15
% 0.21/0.50  # Proof object initial formulas used   : 8
% 0.21/0.50  # Proof object generating inferences   : 20
% 0.21/0.50  # Proof object simplifying inferences  : 16
% 0.21/0.50  # Training examples: 0 positive, 0 negative
% 0.21/0.50  # Parsed axioms                        : 8
% 0.21/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.50  # Initial clauses                      : 22
% 0.21/0.50  # Removed in clause preprocessing      : 0
% 0.21/0.50  # Initial clauses in saturation        : 22
% 0.21/0.50  # Processed clauses                    : 1811
% 0.21/0.50  # ...of these trivial                  : 2
% 0.21/0.50  # ...subsumed                          : 1506
% 0.21/0.50  # ...remaining for further processing  : 303
% 0.21/0.50  # Other redundant clauses eliminated   : 5
% 0.21/0.50  # Clauses deleted for lack of memory   : 0
% 0.21/0.50  # Backward-subsumed                    : 1
% 0.21/0.50  # Backward-rewritten                   : 5
% 0.21/0.50  # Generated clauses                    : 7296
% 0.21/0.50  # ...of the previous two non-trivial   : 6126
% 0.21/0.50  # Contextual simplify-reflections      : 0
% 0.21/0.50  # Paramodulations                      : 7285
% 0.21/0.50  # Factorizations                       : 5
% 0.21/0.50  # Equation resolutions                 : 5
% 0.21/0.50  # Propositional unsat checks           : 0
% 0.21/0.50  #    Propositional check models        : 0
% 0.21/0.50  #    Propositional check unsatisfiable : 0
% 0.21/0.50  #    Propositional clauses             : 0
% 0.21/0.50  #    Propositional clauses after purity: 0
% 0.21/0.50  #    Propositional unsat core size     : 0
% 0.21/0.50  #    Propositional preprocessing time  : 0.000
% 0.21/0.50  #    Propositional encoding time       : 0.000
% 0.21/0.50  #    Propositional solver time         : 0.000
% 0.21/0.50  #    Success case prop preproc time    : 0.000
% 0.21/0.50  #    Success case prop encoding time   : 0.000
% 0.21/0.50  #    Success case prop solver time     : 0.000
% 0.21/0.50  # Current number of processed clauses  : 269
% 0.21/0.50  #    Positive orientable unit clauses  : 9
% 0.21/0.50  #    Positive unorientable unit clauses: 0
% 0.21/0.50  #    Negative unit clauses             : 2
% 0.21/0.50  #    Non-unit-clauses                  : 258
% 0.21/0.50  # Current number of unprocessed clauses: 4353
% 0.21/0.50  # ...number of literals in the above   : 17300
% 0.21/0.50  # Current number of archived formulas  : 0
% 0.21/0.50  # Current number of archived clauses   : 29
% 0.21/0.50  # Clause-clause subsumption calls (NU) : 19736
% 0.21/0.50  # Rec. Clause-clause subsumption calls : 7205
% 0.21/0.50  # Non-unit clause-clause subsumptions  : 837
% 0.21/0.50  # Unit Clause-clause subsumption calls : 15
% 0.21/0.50  # Rewrite failures with RHS unbound    : 0
% 0.21/0.50  # BW rewrite match attempts            : 2
% 0.21/0.50  # BW rewrite match successes           : 2
% 0.21/0.50  # Condensation attempts                : 0
% 0.21/0.50  # Condensation successes               : 0
% 0.21/0.50  # Termbank termtop insertions          : 140193
% 0.21/0.50  
% 0.21/0.50  # -------------------------------------------------
% 0.21/0.50  # User time                : 0.145 s
% 0.21/0.50  # System time              : 0.008 s
% 0.21/0.50  # Total time               : 0.153 s
% 0.21/0.50  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
