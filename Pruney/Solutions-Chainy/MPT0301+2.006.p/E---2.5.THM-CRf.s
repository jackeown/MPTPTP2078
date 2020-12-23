%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:25 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 262 expanded)
%              Number of clauses        :   38 ( 125 expanded)
%              Number of leaves         :   11 (  66 expanded)
%              Depth                    :   12
%              Number of atoms          :  154 ( 703 expanded)
%              Number of equality atoms :   72 ( 305 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t113_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t46_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t49_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(c_0_11,plain,(
    ! [X23,X24] :
      ( ( r1_tarski(X23,X24)
        | X23 != X24 )
      & ( r1_tarski(X24,X23)
        | X23 != X24 )
      & ( ~ r1_tarski(X23,X24)
        | ~ r1_tarski(X24,X23)
        | X23 = X24 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_12,plain,(
    ! [X27] : r1_tarski(k1_xboole_0,X27) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_zfmisc_1(X1,X2) = k1_xboole_0
      <=> ( X1 = k1_xboole_0
          | X2 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t113_zfmisc_1])).

cnf(c_0_14,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X25,X26] : r1_tarski(k3_xboole_0(X25,X26),X25) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_17,negated_conjecture,
    ( ( esk12_0 != k1_xboole_0
      | k2_zfmisc_1(esk12_0,esk13_0) != k1_xboole_0 )
    & ( esk13_0 != k1_xboole_0
      | k2_zfmisc_1(esk12_0,esk13_0) != k1_xboole_0 )
    & ( k2_zfmisc_1(esk12_0,esk13_0) = k1_xboole_0
      | esk12_0 = k1_xboole_0
      | esk13_0 = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])).

fof(c_0_18,plain,(
    ! [X21] :
      ( X21 = k1_xboole_0
      | r2_hidden(esk3_1(X21),X21) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_19,plain,(
    ! [X13,X14] :
      ( ( ~ r1_xboole_0(X13,X14)
        | k3_xboole_0(X13,X14) = k1_xboole_0 )
      & ( k3_xboole_0(X13,X14) != k1_xboole_0
        | r1_xboole_0(X13,X14) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_20,plain,
    ( k1_xboole_0 = X1
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X38,X39,X40,X41,X44,X45,X46,X47,X48,X49,X51,X52] :
      ( ( r2_hidden(esk5_4(X38,X39,X40,X41),X38)
        | ~ r2_hidden(X41,X40)
        | X40 != k2_zfmisc_1(X38,X39) )
      & ( r2_hidden(esk6_4(X38,X39,X40,X41),X39)
        | ~ r2_hidden(X41,X40)
        | X40 != k2_zfmisc_1(X38,X39) )
      & ( X41 = k4_tarski(esk5_4(X38,X39,X40,X41),esk6_4(X38,X39,X40,X41))
        | ~ r2_hidden(X41,X40)
        | X40 != k2_zfmisc_1(X38,X39) )
      & ( ~ r2_hidden(X45,X38)
        | ~ r2_hidden(X46,X39)
        | X44 != k4_tarski(X45,X46)
        | r2_hidden(X44,X40)
        | X40 != k2_zfmisc_1(X38,X39) )
      & ( ~ r2_hidden(esk7_3(X47,X48,X49),X49)
        | ~ r2_hidden(X51,X47)
        | ~ r2_hidden(X52,X48)
        | esk7_3(X47,X48,X49) != k4_tarski(X51,X52)
        | X49 = k2_zfmisc_1(X47,X48) )
      & ( r2_hidden(esk8_3(X47,X48,X49),X47)
        | r2_hidden(esk7_3(X47,X48,X49),X49)
        | X49 = k2_zfmisc_1(X47,X48) )
      & ( r2_hidden(esk9_3(X47,X48,X49),X48)
        | r2_hidden(esk7_3(X47,X48,X49),X49)
        | X49 = k2_zfmisc_1(X47,X48) )
      & ( esk7_3(X47,X48,X49) = k4_tarski(esk8_3(X47,X48,X49),esk9_3(X47,X48,X49))
        | r2_hidden(esk7_3(X47,X48,X49),X49)
        | X49 = k2_zfmisc_1(X47,X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_23,negated_conjecture,
    ( esk12_0 != k1_xboole_0
    | k2_zfmisc_1(esk12_0,esk13_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
    ! [X15,X16,X18,X19,X20] :
      ( ( r1_xboole_0(X15,X16)
        | r2_hidden(esk2_2(X15,X16),k3_xboole_0(X15,X16)) )
      & ( ~ r2_hidden(X20,k3_xboole_0(X18,X19))
        | ~ r1_xboole_0(X18,X19) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_26,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_28,plain,(
    ! [X61,X62] :
      ( ~ r2_hidden(X61,X62)
      | k2_xboole_0(k1_tarski(X61),X62) = X62 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_zfmisc_1])])).

fof(c_0_29,plain,(
    ! [X37] : k2_tarski(X37,X37) = k1_tarski(X37) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_30,plain,
    ( r2_hidden(esk5_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk3_1(esk12_0),esk12_0)
    | k2_zfmisc_1(k1_xboole_0,esk13_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( esk13_0 != k1_xboole_0
    | k2_zfmisc_1(esk12_0,esk13_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_35,plain,(
    ! [X63,X64] : k2_xboole_0(k1_tarski(X63),X64) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

cnf(c_0_36,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( r2_hidden(esk5_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk3_1(k2_zfmisc_1(k1_xboole_0,esk13_0)),k2_zfmisc_1(k1_xboole_0,esk13_0))
    | r2_hidden(esk3_1(esk12_0),esk12_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_24])).

cnf(c_0_40,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_27])).

cnf(c_0_41,plain,
    ( r2_hidden(esk6_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk3_1(esk13_0),esk13_0)
    | k2_zfmisc_1(esk12_0,k1_xboole_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_24])).

cnf(c_0_43,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( k2_xboole_0(k2_tarski(X1,X1),X2) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk3_1(esk12_0),esk12_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_46,plain,
    ( r2_hidden(esk6_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk3_1(k2_zfmisc_1(esk12_0,k1_xboole_0)),k2_zfmisc_1(esk12_0,k1_xboole_0))
    | r2_hidden(esk3_1(esk13_0),esk13_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_24])).

cnf(c_0_48,plain,
    ( k2_xboole_0(k2_tarski(X1,X1),X2) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_43,c_0_37])).

cnf(c_0_49,negated_conjecture,
    ( k2_xboole_0(k2_tarski(esk3_1(esk12_0),esk3_1(esk12_0)),esk12_0) = esk12_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk3_1(esk13_0),esk13_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_40])).

cnf(c_0_51,plain,
    ( r2_hidden(X5,X6)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X5 != k4_tarski(X1,X3)
    | X6 != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_52,negated_conjecture,
    ( k2_zfmisc_1(esk12_0,esk13_0) = k1_xboole_0
    | esk12_0 = k1_xboole_0
    | esk13_0 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_53,negated_conjecture,
    ( esk12_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( k2_xboole_0(k2_tarski(esk3_1(esk13_0),esk3_1(esk13_0)),esk13_0) = esk13_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_50])).

cnf(c_0_55,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_51])])).

cnf(c_0_56,negated_conjecture,
    ( k2_zfmisc_1(esk12_0,esk13_0) = k1_xboole_0
    | esk13_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( esk13_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_48,c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_1(esk12_0),X1),k2_zfmisc_1(esk12_0,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_45])).

cnf(c_0_59,negated_conjecture,
    ( k2_zfmisc_1(esk12_0,esk13_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_50]),c_0_59]),c_0_40]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:27:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.19/0.39  # and selection function SelectNegativeLiterals.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.030 s
% 0.19/0.39  # Presaturation interreduction done
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.39  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.39  fof(t113_zfmisc_1, conjecture, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.19/0.39  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.19/0.39  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.19/0.39  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.19/0.39  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.19/0.39  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.19/0.39  fof(t46_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 0.19/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.39  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.19/0.39  fof(c_0_11, plain, ![X23, X24]:(((r1_tarski(X23,X24)|X23!=X24)&(r1_tarski(X24,X23)|X23!=X24))&(~r1_tarski(X23,X24)|~r1_tarski(X24,X23)|X23=X24)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.39  fof(c_0_12, plain, ![X27]:r1_tarski(k1_xboole_0,X27), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.39  fof(c_0_13, negated_conjecture, ~(![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0))), inference(assume_negation,[status(cth)],[t113_zfmisc_1])).
% 0.19/0.39  cnf(c_0_14, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.39  cnf(c_0_15, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.39  fof(c_0_16, plain, ![X25, X26]:r1_tarski(k3_xboole_0(X25,X26),X25), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.19/0.39  fof(c_0_17, negated_conjecture, (((esk12_0!=k1_xboole_0|k2_zfmisc_1(esk12_0,esk13_0)!=k1_xboole_0)&(esk13_0!=k1_xboole_0|k2_zfmisc_1(esk12_0,esk13_0)!=k1_xboole_0))&(k2_zfmisc_1(esk12_0,esk13_0)=k1_xboole_0|(esk12_0=k1_xboole_0|esk13_0=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])).
% 0.19/0.39  fof(c_0_18, plain, ![X21]:(X21=k1_xboole_0|r2_hidden(esk3_1(X21),X21)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.19/0.39  fof(c_0_19, plain, ![X13, X14]:((~r1_xboole_0(X13,X14)|k3_xboole_0(X13,X14)=k1_xboole_0)&(k3_xboole_0(X13,X14)!=k1_xboole_0|r1_xboole_0(X13,X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.19/0.39  cnf(c_0_20, plain, (k1_xboole_0=X1|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.39  cnf(c_0_21, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.39  fof(c_0_22, plain, ![X38, X39, X40, X41, X44, X45, X46, X47, X48, X49, X51, X52]:(((((r2_hidden(esk5_4(X38,X39,X40,X41),X38)|~r2_hidden(X41,X40)|X40!=k2_zfmisc_1(X38,X39))&(r2_hidden(esk6_4(X38,X39,X40,X41),X39)|~r2_hidden(X41,X40)|X40!=k2_zfmisc_1(X38,X39)))&(X41=k4_tarski(esk5_4(X38,X39,X40,X41),esk6_4(X38,X39,X40,X41))|~r2_hidden(X41,X40)|X40!=k2_zfmisc_1(X38,X39)))&(~r2_hidden(X45,X38)|~r2_hidden(X46,X39)|X44!=k4_tarski(X45,X46)|r2_hidden(X44,X40)|X40!=k2_zfmisc_1(X38,X39)))&((~r2_hidden(esk7_3(X47,X48,X49),X49)|(~r2_hidden(X51,X47)|~r2_hidden(X52,X48)|esk7_3(X47,X48,X49)!=k4_tarski(X51,X52))|X49=k2_zfmisc_1(X47,X48))&(((r2_hidden(esk8_3(X47,X48,X49),X47)|r2_hidden(esk7_3(X47,X48,X49),X49)|X49=k2_zfmisc_1(X47,X48))&(r2_hidden(esk9_3(X47,X48,X49),X48)|r2_hidden(esk7_3(X47,X48,X49),X49)|X49=k2_zfmisc_1(X47,X48)))&(esk7_3(X47,X48,X49)=k4_tarski(esk8_3(X47,X48,X49),esk9_3(X47,X48,X49))|r2_hidden(esk7_3(X47,X48,X49),X49)|X49=k2_zfmisc_1(X47,X48))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.19/0.39  cnf(c_0_23, negated_conjecture, (esk12_0!=k1_xboole_0|k2_zfmisc_1(esk12_0,esk13_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.39  cnf(c_0_24, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  fof(c_0_25, plain, ![X15, X16, X18, X19, X20]:((r1_xboole_0(X15,X16)|r2_hidden(esk2_2(X15,X16),k3_xboole_0(X15,X16)))&(~r2_hidden(X20,k3_xboole_0(X18,X19))|~r1_xboole_0(X18,X19))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.19/0.39  cnf(c_0_26, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.39  cnf(c_0_27, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.39  fof(c_0_28, plain, ![X61, X62]:(~r2_hidden(X61,X62)|k2_xboole_0(k1_tarski(X61),X62)=X62), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_zfmisc_1])])).
% 0.19/0.39  fof(c_0_29, plain, ![X37]:k2_tarski(X37,X37)=k1_tarski(X37), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.39  cnf(c_0_30, plain, (r2_hidden(esk5_4(X1,X2,X3,X4),X1)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.39  cnf(c_0_31, negated_conjecture, (r2_hidden(esk3_1(esk12_0),esk12_0)|k2_zfmisc_1(k1_xboole_0,esk13_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.39  cnf(c_0_32, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.39  cnf(c_0_33, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.39  cnf(c_0_34, negated_conjecture, (esk13_0!=k1_xboole_0|k2_zfmisc_1(esk12_0,esk13_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.39  fof(c_0_35, plain, ![X63, X64]:k2_xboole_0(k1_tarski(X63),X64)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 0.19/0.39  cnf(c_0_36, plain, (k2_xboole_0(k1_tarski(X1),X2)=X2|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.39  cnf(c_0_37, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.39  cnf(c_0_38, plain, (r2_hidden(esk5_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_30])).
% 0.19/0.39  cnf(c_0_39, negated_conjecture, (r2_hidden(esk3_1(k2_zfmisc_1(k1_xboole_0,esk13_0)),k2_zfmisc_1(k1_xboole_0,esk13_0))|r2_hidden(esk3_1(esk12_0),esk12_0)), inference(spm,[status(thm)],[c_0_31, c_0_24])).
% 0.19/0.39  cnf(c_0_40, plain, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_27])).
% 0.19/0.39  cnf(c_0_41, plain, (r2_hidden(esk6_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.39  cnf(c_0_42, negated_conjecture, (r2_hidden(esk3_1(esk13_0),esk13_0)|k2_zfmisc_1(esk12_0,k1_xboole_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_34, c_0_24])).
% 0.19/0.39  cnf(c_0_43, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.39  cnf(c_0_44, plain, (k2_xboole_0(k2_tarski(X1,X1),X2)=X2|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.39  cnf(c_0_45, negated_conjecture, (r2_hidden(esk3_1(esk12_0),esk12_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])).
% 0.19/0.39  cnf(c_0_46, plain, (r2_hidden(esk6_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_41])).
% 0.19/0.39  cnf(c_0_47, negated_conjecture, (r2_hidden(esk3_1(k2_zfmisc_1(esk12_0,k1_xboole_0)),k2_zfmisc_1(esk12_0,k1_xboole_0))|r2_hidden(esk3_1(esk13_0),esk13_0)), inference(spm,[status(thm)],[c_0_42, c_0_24])).
% 0.19/0.39  cnf(c_0_48, plain, (k2_xboole_0(k2_tarski(X1,X1),X2)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_43, c_0_37])).
% 0.19/0.39  cnf(c_0_49, negated_conjecture, (k2_xboole_0(k2_tarski(esk3_1(esk12_0),esk3_1(esk12_0)),esk12_0)=esk12_0), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.39  cnf(c_0_50, negated_conjecture, (r2_hidden(esk3_1(esk13_0),esk13_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_40])).
% 0.19/0.39  cnf(c_0_51, plain, (r2_hidden(X5,X6)|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X5!=k4_tarski(X1,X3)|X6!=k2_zfmisc_1(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.39  cnf(c_0_52, negated_conjecture, (k2_zfmisc_1(esk12_0,esk13_0)=k1_xboole_0|esk12_0=k1_xboole_0|esk13_0=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.39  cnf(c_0_53, negated_conjecture, (esk12_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.39  cnf(c_0_54, negated_conjecture, (k2_xboole_0(k2_tarski(esk3_1(esk13_0),esk3_1(esk13_0)),esk13_0)=esk13_0), inference(spm,[status(thm)],[c_0_44, c_0_50])).
% 0.19/0.39  cnf(c_0_55, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))|~r2_hidden(X2,X4)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_51])])).
% 0.19/0.39  cnf(c_0_56, negated_conjecture, (k2_zfmisc_1(esk12_0,esk13_0)=k1_xboole_0|esk13_0=k1_xboole_0), inference(sr,[status(thm)],[c_0_52, c_0_53])).
% 0.19/0.39  cnf(c_0_57, negated_conjecture, (esk13_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_48, c_0_54])).
% 0.19/0.39  cnf(c_0_58, negated_conjecture, (r2_hidden(k4_tarski(esk3_1(esk12_0),X1),k2_zfmisc_1(esk12_0,X2))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_55, c_0_45])).
% 0.19/0.39  cnf(c_0_59, negated_conjecture, (k2_zfmisc_1(esk12_0,esk13_0)=k1_xboole_0), inference(sr,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.39  cnf(c_0_60, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_50]), c_0_59]), c_0_40]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 61
% 0.19/0.39  # Proof object clause steps            : 38
% 0.19/0.39  # Proof object formula steps           : 23
% 0.19/0.39  # Proof object conjectures             : 20
% 0.19/0.39  # Proof object clause conjectures      : 17
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 15
% 0.19/0.39  # Proof object initial formulas used   : 11
% 0.19/0.39  # Proof object generating inferences   : 16
% 0.19/0.39  # Proof object simplifying inferences  : 13
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 16
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 36
% 0.19/0.39  # Removed in clause preprocessing      : 1
% 0.19/0.39  # Initial clauses in saturation        : 35
% 0.19/0.39  # Processed clauses                    : 200
% 0.19/0.39  # ...of these trivial                  : 6
% 0.19/0.39  # ...subsumed                          : 65
% 0.19/0.39  # ...remaining for further processing  : 128
% 0.19/0.39  # Other redundant clauses eliminated   : 44
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 0
% 0.19/0.39  # Backward-rewritten                   : 20
% 0.19/0.39  # Generated clauses                    : 731
% 0.19/0.39  # ...of the previous two non-trivial   : 588
% 0.19/0.39  # Contextual simplify-reflections      : 0
% 0.19/0.39  # Paramodulations                      : 687
% 0.19/0.39  # Factorizations                       : 0
% 0.19/0.39  # Equation resolutions                 : 44
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 64
% 0.19/0.39  #    Positive orientable unit clauses  : 19
% 0.19/0.39  #    Positive unorientable unit clauses: 0
% 0.19/0.39  #    Negative unit clauses             : 5
% 0.19/0.39  #    Non-unit-clauses                  : 40
% 0.19/0.39  # Current number of unprocessed clauses: 454
% 0.19/0.39  # ...number of literals in the above   : 1398
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 57
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 795
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 683
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 44
% 0.19/0.39  # Unit Clause-clause subsumption calls : 52
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 10
% 0.19/0.39  # BW rewrite match successes           : 6
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 10071
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.045 s
% 0.19/0.39  # System time              : 0.002 s
% 0.19/0.39  # Total time               : 0.047 s
% 0.19/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
