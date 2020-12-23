%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:36 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 191 expanded)
%              Number of clauses        :   36 (  85 expanded)
%              Number of leaves         :   10 (  49 expanded)
%              Depth                    :   11
%              Number of atoms          :  168 ( 533 expanded)
%              Number of equality atoms :   47 ( 171 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t173_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k10_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

fof(t168_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,X1) = k10_relat_1(X2,k3_xboole_0(k2_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(c_0_10,plain,(
    ! [X20,X21] : k4_xboole_0(X20,k4_xboole_0(X20,X21)) = k3_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_11,plain,(
    ! [X19] : k4_xboole_0(X19,k1_xboole_0) = X19 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_12,plain,(
    ! [X18] : k3_xboole_0(X18,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_13,plain,(
    ! [X22,X23] :
      ( ( ~ r1_xboole_0(X22,X23)
        | k4_xboole_0(X22,X23) = X22 )
      & ( k4_xboole_0(X22,X23) != X22
        | r1_xboole_0(X22,X23) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( k10_relat_1(X2,X1) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t173_relat_1])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X12,X13,X15,X16,X17] :
      ( ( r1_xboole_0(X12,X13)
        | r2_hidden(esk2_2(X12,X13),k3_xboole_0(X12,X13)) )
      & ( ~ r2_hidden(X17,k3_xboole_0(X15,X16))
        | ~ r1_xboole_0(X15,X16) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_19,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_20,plain,(
    ! [X24,X25,X26,X27,X29,X30,X31,X32,X34] :
      ( ( r2_hidden(k4_tarski(X27,esk3_4(X24,X25,X26,X27)),X24)
        | ~ r2_hidden(X27,X26)
        | X26 != k10_relat_1(X24,X25)
        | ~ v1_relat_1(X24) )
      & ( r2_hidden(esk3_4(X24,X25,X26,X27),X25)
        | ~ r2_hidden(X27,X26)
        | X26 != k10_relat_1(X24,X25)
        | ~ v1_relat_1(X24) )
      & ( ~ r2_hidden(k4_tarski(X29,X30),X24)
        | ~ r2_hidden(X30,X25)
        | r2_hidden(X29,X26)
        | X26 != k10_relat_1(X24,X25)
        | ~ v1_relat_1(X24) )
      & ( ~ r2_hidden(esk4_3(X24,X31,X32),X32)
        | ~ r2_hidden(k4_tarski(esk4_3(X24,X31,X32),X34),X24)
        | ~ r2_hidden(X34,X31)
        | X32 = k10_relat_1(X24,X31)
        | ~ v1_relat_1(X24) )
      & ( r2_hidden(k4_tarski(esk4_3(X24,X31,X32),esk5_3(X24,X31,X32)),X24)
        | r2_hidden(esk4_3(X24,X31,X32),X32)
        | X32 = k10_relat_1(X24,X31)
        | ~ v1_relat_1(X24) )
      & ( r2_hidden(esk5_3(X24,X31,X32),X31)
        | r2_hidden(esk4_3(X24,X31,X32),X32)
        | X32 = k10_relat_1(X24,X31)
        | ~ v1_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

fof(c_0_21,negated_conjecture,
    ( v1_relat_1(esk10_0)
    & ( k10_relat_1(esk10_0,esk9_0) != k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(esk10_0),esk9_0) )
    & ( k10_relat_1(esk10_0,esk9_0) = k1_xboole_0
      | r1_xboole_0(k2_relat_1(esk10_0),esk9_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_22,plain,(
    ! [X47,X48] :
      ( ~ v1_relat_1(X48)
      | k10_relat_1(X48,X47) = k10_relat_1(X48,k3_xboole_0(k2_relat_1(X48),X47)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_relat_1])])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_16])).

cnf(c_0_27,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X2)
    | r2_hidden(esk4_3(X1,X2,X3),X3)
    | X3 = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_29,plain,(
    ! [X36,X37,X38,X40,X41,X42,X43,X45] :
      ( ( ~ r2_hidden(X38,X37)
        | r2_hidden(k4_tarski(esk6_3(X36,X37,X38),X38),X36)
        | X37 != k2_relat_1(X36) )
      & ( ~ r2_hidden(k4_tarski(X41,X40),X36)
        | r2_hidden(X40,X37)
        | X37 != k2_relat_1(X36) )
      & ( ~ r2_hidden(esk7_2(X42,X43),X43)
        | ~ r2_hidden(k4_tarski(X45,esk7_2(X42,X43)),X42)
        | X43 = k2_relat_1(X42) )
      & ( r2_hidden(esk7_2(X42,X43),X43)
        | r2_hidden(k4_tarski(esk8_2(X42,X43),esk7_2(X42,X43)),X42)
        | X43 = k2_relat_1(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_30,plain,
    ( k10_relat_1(X1,X2) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_23]),c_0_24])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_17]),c_0_26])])).

cnf(c_0_33,negated_conjecture,
    ( X1 = k10_relat_1(esk10_0,X2)
    | r2_hidden(esk5_3(esk10_0,X2,X1),X2)
    | r2_hidden(esk4_3(esk10_0,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X5 != k10_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_35,plain,
    ( r2_hidden(k4_tarski(esk6_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( k10_relat_1(X1,k1_xboole_0) = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( k10_relat_1(esk10_0,esk9_0) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(esk10_0),esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_38,negated_conjecture,
    ( k10_relat_1(esk10_0,X1) = k1_xboole_0
    | r2_hidden(esk5_3(esk10_0,X1,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( r2_hidden(k4_tarski(esk6_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( k10_relat_1(esk10_0,esk9_0) = k10_relat_1(esk10_0,k1_xboole_0)
    | k10_relat_1(esk10_0,esk9_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_28])])).

cnf(c_0_42,negated_conjecture,
    ( k10_relat_1(esk10_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_38])).

fof(c_0_43,plain,(
    ! [X6,X7,X9,X10,X11] :
      ( ( r2_hidden(esk1_2(X6,X7),X6)
        | r1_xboole_0(X6,X7) )
      & ( r2_hidden(esk1_2(X6,X7),X7)
        | r1_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X11,X9)
        | ~ r2_hidden(X11,X10)
        | ~ r1_xboole_0(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_44,plain,
    ( r2_hidden(esk6_3(X1,k2_relat_1(X1),X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( k10_relat_1(esk10_0,esk9_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42])])).

cnf(c_0_46,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_47,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( ~ r2_hidden(X1,k2_relat_1(esk10_0))
    | ~ r2_hidden(X1,esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_28])]),c_0_32])).

cnf(c_0_49,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( r1_xboole_0(X1,k2_relat_1(esk10_0))
    | ~ r2_hidden(esk1_2(X1,k2_relat_1(esk10_0)),esk9_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_52,negated_conjecture,
    ( k10_relat_1(esk10_0,esk9_0) != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(esk10_0),esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_53,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( r1_xboole_0(esk9_0,k2_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(esk10_0),esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_45])])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:51:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic U_____100_C09_12_F1_SE_CS_SP_PS_S5PRR_RG_ND_S04AN
% 0.19/0.41  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.028 s
% 0.19/0.41  # Presaturation interreduction done
% 0.19/0.41  
% 0.19/0.41  # Proof found!
% 0.19/0.41  # SZS status Theorem
% 0.19/0.41  # SZS output start CNFRefutation
% 0.19/0.41  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.19/0.41  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.19/0.41  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.19/0.41  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.19/0.41  fof(t173_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 0.19/0.42  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.19/0.42  fof(d14_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X4,X5),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 0.19/0.42  fof(t168_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k10_relat_1(X2,X1)=k10_relat_1(X2,k3_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 0.19/0.42  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 0.19/0.42  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.19/0.42  fof(c_0_10, plain, ![X20, X21]:k4_xboole_0(X20,k4_xboole_0(X20,X21))=k3_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.19/0.42  fof(c_0_11, plain, ![X19]:k4_xboole_0(X19,k1_xboole_0)=X19, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.19/0.42  fof(c_0_12, plain, ![X18]:k3_xboole_0(X18,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.19/0.42  fof(c_0_13, plain, ![X22, X23]:((~r1_xboole_0(X22,X23)|k4_xboole_0(X22,X23)=X22)&(k4_xboole_0(X22,X23)!=X22|r1_xboole_0(X22,X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.19/0.42  fof(c_0_14, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1)))), inference(assume_negation,[status(cth)],[t173_relat_1])).
% 0.19/0.42  cnf(c_0_15, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.42  cnf(c_0_16, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.42  cnf(c_0_17, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.42  fof(c_0_18, plain, ![X12, X13, X15, X16, X17]:((r1_xboole_0(X12,X13)|r2_hidden(esk2_2(X12,X13),k3_xboole_0(X12,X13)))&(~r2_hidden(X17,k3_xboole_0(X15,X16))|~r1_xboole_0(X15,X16))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.19/0.42  cnf(c_0_19, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.42  fof(c_0_20, plain, ![X24, X25, X26, X27, X29, X30, X31, X32, X34]:((((r2_hidden(k4_tarski(X27,esk3_4(X24,X25,X26,X27)),X24)|~r2_hidden(X27,X26)|X26!=k10_relat_1(X24,X25)|~v1_relat_1(X24))&(r2_hidden(esk3_4(X24,X25,X26,X27),X25)|~r2_hidden(X27,X26)|X26!=k10_relat_1(X24,X25)|~v1_relat_1(X24)))&(~r2_hidden(k4_tarski(X29,X30),X24)|~r2_hidden(X30,X25)|r2_hidden(X29,X26)|X26!=k10_relat_1(X24,X25)|~v1_relat_1(X24)))&((~r2_hidden(esk4_3(X24,X31,X32),X32)|(~r2_hidden(k4_tarski(esk4_3(X24,X31,X32),X34),X24)|~r2_hidden(X34,X31))|X32=k10_relat_1(X24,X31)|~v1_relat_1(X24))&((r2_hidden(k4_tarski(esk4_3(X24,X31,X32),esk5_3(X24,X31,X32)),X24)|r2_hidden(esk4_3(X24,X31,X32),X32)|X32=k10_relat_1(X24,X31)|~v1_relat_1(X24))&(r2_hidden(esk5_3(X24,X31,X32),X31)|r2_hidden(esk4_3(X24,X31,X32),X32)|X32=k10_relat_1(X24,X31)|~v1_relat_1(X24))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).
% 0.19/0.42  fof(c_0_21, negated_conjecture, (v1_relat_1(esk10_0)&((k10_relat_1(esk10_0,esk9_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk10_0),esk9_0))&(k10_relat_1(esk10_0,esk9_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk10_0),esk9_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.19/0.42  fof(c_0_22, plain, ![X47, X48]:(~v1_relat_1(X48)|k10_relat_1(X48,X47)=k10_relat_1(X48,k3_xboole_0(k2_relat_1(X48),X47))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_relat_1])])).
% 0.19/0.42  cnf(c_0_23, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.42  cnf(c_0_24, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])).
% 0.19/0.42  cnf(c_0_25, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.42  cnf(c_0_26, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_19, c_0_16])).
% 0.19/0.42  cnf(c_0_27, plain, (r2_hidden(esk5_3(X1,X2,X3),X2)|r2_hidden(esk4_3(X1,X2,X3),X3)|X3=k10_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.42  cnf(c_0_28, negated_conjecture, (v1_relat_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.42  fof(c_0_29, plain, ![X36, X37, X38, X40, X41, X42, X43, X45]:(((~r2_hidden(X38,X37)|r2_hidden(k4_tarski(esk6_3(X36,X37,X38),X38),X36)|X37!=k2_relat_1(X36))&(~r2_hidden(k4_tarski(X41,X40),X36)|r2_hidden(X40,X37)|X37!=k2_relat_1(X36)))&((~r2_hidden(esk7_2(X42,X43),X43)|~r2_hidden(k4_tarski(X45,esk7_2(X42,X43)),X42)|X43=k2_relat_1(X42))&(r2_hidden(esk7_2(X42,X43),X43)|r2_hidden(k4_tarski(esk8_2(X42,X43),esk7_2(X42,X43)),X42)|X43=k2_relat_1(X42)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.19/0.42  cnf(c_0_30, plain, (k10_relat_1(X1,X2)=k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.42  cnf(c_0_31, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_23]), c_0_24])).
% 0.19/0.42  cnf(c_0_32, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_17]), c_0_26])])).
% 0.19/0.42  cnf(c_0_33, negated_conjecture, (X1=k10_relat_1(esk10_0,X2)|r2_hidden(esk5_3(esk10_0,X2,X1),X2)|r2_hidden(esk4_3(esk10_0,X2,X1),X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.42  cnf(c_0_34, plain, (r2_hidden(X1,X5)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X2,X4)|X5!=k10_relat_1(X3,X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.42  cnf(c_0_35, plain, (r2_hidden(k4_tarski(esk6_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.42  cnf(c_0_36, plain, (k10_relat_1(X1,k1_xboole_0)=k10_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_xboole_0(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.42  cnf(c_0_37, negated_conjecture, (k10_relat_1(esk10_0,esk9_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk10_0),esk9_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.42  cnf(c_0_38, negated_conjecture, (k10_relat_1(esk10_0,X1)=k1_xboole_0|r2_hidden(esk5_3(esk10_0,X1,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.42  cnf(c_0_39, plain, (r2_hidden(X1,k10_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X4),X2)|~r2_hidden(X4,X3)), inference(er,[status(thm)],[c_0_34])).
% 0.19/0.42  cnf(c_0_40, plain, (r2_hidden(k4_tarski(esk6_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_35])).
% 0.19/0.42  cnf(c_0_41, negated_conjecture, (k10_relat_1(esk10_0,esk9_0)=k10_relat_1(esk10_0,k1_xboole_0)|k10_relat_1(esk10_0,esk9_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_28])])).
% 0.19/0.42  cnf(c_0_42, negated_conjecture, (k10_relat_1(esk10_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_32, c_0_38])).
% 0.19/0.42  fof(c_0_43, plain, ![X6, X7, X9, X10, X11]:(((r2_hidden(esk1_2(X6,X7),X6)|r1_xboole_0(X6,X7))&(r2_hidden(esk1_2(X6,X7),X7)|r1_xboole_0(X6,X7)))&(~r2_hidden(X11,X9)|~r2_hidden(X11,X10)|~r1_xboole_0(X9,X10))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.19/0.42  cnf(c_0_44, plain, (r2_hidden(esk6_3(X1,k2_relat_1(X1),X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.42  cnf(c_0_45, negated_conjecture, (k10_relat_1(esk10_0,esk9_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42])])).
% 0.19/0.42  cnf(c_0_46, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.42  cnf(c_0_47, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.42  cnf(c_0_48, negated_conjecture, (~r2_hidden(X1,k2_relat_1(esk10_0))|~r2_hidden(X1,esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_28])]), c_0_32])).
% 0.19/0.42  cnf(c_0_49, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.42  cnf(c_0_50, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.19/0.42  cnf(c_0_51, negated_conjecture, (r1_xboole_0(X1,k2_relat_1(esk10_0))|~r2_hidden(esk1_2(X1,k2_relat_1(esk10_0)),esk9_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.42  cnf(c_0_52, negated_conjecture, (k10_relat_1(esk10_0,esk9_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk10_0),esk9_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.42  cnf(c_0_53, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_50, c_0_49])).
% 0.19/0.42  cnf(c_0_54, negated_conjecture, (r1_xboole_0(esk9_0,k2_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_51, c_0_47])).
% 0.19/0.42  cnf(c_0_55, negated_conjecture, (~r1_xboole_0(k2_relat_1(esk10_0),esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_45])])).
% 0.19/0.42  cnf(c_0_56, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55]), ['proof']).
% 0.19/0.42  # SZS output end CNFRefutation
% 0.19/0.42  # Proof object total steps             : 57
% 0.19/0.42  # Proof object clause steps            : 36
% 0.19/0.42  # Proof object formula steps           : 21
% 0.19/0.42  # Proof object conjectures             : 16
% 0.19/0.42  # Proof object clause conjectures      : 13
% 0.19/0.42  # Proof object formula conjectures     : 3
% 0.19/0.42  # Proof object initial clauses used    : 16
% 0.19/0.42  # Proof object initial formulas used   : 10
% 0.19/0.42  # Proof object generating inferences   : 16
% 0.19/0.42  # Proof object simplifying inferences  : 16
% 0.19/0.42  # Training examples: 0 positive, 0 negative
% 0.19/0.42  # Parsed axioms                        : 10
% 0.19/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.42  # Initial clauses                      : 24
% 0.19/0.42  # Removed in clause preprocessing      : 0
% 0.19/0.42  # Initial clauses in saturation        : 24
% 0.19/0.42  # Processed clauses                    : 837
% 0.19/0.42  # ...of these trivial                  : 1
% 0.19/0.42  # ...subsumed                          : 625
% 0.19/0.42  # ...remaining for further processing  : 211
% 0.19/0.42  # Other redundant clauses eliminated   : 21
% 0.19/0.42  # Clauses deleted for lack of memory   : 0
% 0.19/0.42  # Backward-subsumed                    : 2
% 0.19/0.42  # Backward-rewritten                   : 7
% 0.19/0.42  # Generated clauses                    : 2521
% 0.19/0.42  # ...of the previous two non-trivial   : 1962
% 0.19/0.42  # Contextual simplify-reflections      : 1
% 0.19/0.42  # Paramodulations                      : 2497
% 0.19/0.42  # Factorizations                       : 3
% 0.19/0.42  # Equation resolutions                 : 21
% 0.19/0.42  # Propositional unsat checks           : 0
% 0.19/0.42  #    Propositional check models        : 0
% 0.19/0.42  #    Propositional check unsatisfiable : 0
% 0.19/0.42  #    Propositional clauses             : 0
% 0.19/0.42  #    Propositional clauses after purity: 0
% 0.19/0.42  #    Propositional unsat core size     : 0
% 0.19/0.42  #    Propositional preprocessing time  : 0.000
% 0.19/0.42  #    Propositional encoding time       : 0.000
% 0.19/0.42  #    Propositional solver time         : 0.000
% 0.19/0.42  #    Success case prop preproc time    : 0.000
% 0.19/0.42  #    Success case prop encoding time   : 0.000
% 0.19/0.42  #    Success case prop solver time     : 0.000
% 0.19/0.42  # Current number of processed clauses  : 173
% 0.19/0.42  #    Positive orientable unit clauses  : 14
% 0.19/0.42  #    Positive unorientable unit clauses: 0
% 0.19/0.42  #    Negative unit clauses             : 2
% 0.19/0.42  #    Non-unit-clauses                  : 157
% 0.19/0.42  # Current number of unprocessed clauses: 1160
% 0.19/0.42  # ...number of literals in the above   : 3294
% 0.19/0.42  # Current number of archived formulas  : 0
% 0.19/0.42  # Current number of archived clauses   : 33
% 0.19/0.42  # Clause-clause subsumption calls (NU) : 6263
% 0.19/0.42  # Rec. Clause-clause subsumption calls : 5848
% 0.19/0.42  # Non-unit clause-clause subsumptions  : 534
% 0.19/0.42  # Unit Clause-clause subsumption calls : 29
% 0.19/0.42  # Rewrite failures with RHS unbound    : 0
% 0.19/0.42  # BW rewrite match attempts            : 9
% 0.19/0.42  # BW rewrite match successes           : 3
% 0.19/0.42  # Condensation attempts                : 0
% 0.19/0.42  # Condensation successes               : 0
% 0.19/0.42  # Termbank termtop insertions          : 32358
% 0.19/0.42  
% 0.19/0.42  # -------------------------------------------------
% 0.19/0.42  # User time                : 0.072 s
% 0.19/0.42  # System time              : 0.005 s
% 0.19/0.42  # Total time               : 0.077 s
% 0.19/0.42  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
