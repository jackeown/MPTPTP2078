%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:53 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 224 expanded)
%              Number of clauses        :   28 ( 105 expanded)
%              Number of leaves         :    9 (  59 expanded)
%              Depth                    :   15
%              Number of atoms          :  109 ( 415 expanded)
%              Number of equality atoms :   48 ( 176 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t27_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),k1_tarski(X3))
     => k2_tarski(X1,X2) = k1_tarski(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_zfmisc_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

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

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(t60_relat_1,conjecture,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(c_0_9,plain,(
    ! [X18,X19] :
      ( ( ~ r1_tarski(k1_tarski(X18),X19)
        | r2_hidden(X18,X19) )
      & ( ~ r2_hidden(X18,X19)
        | r1_tarski(k1_tarski(X18),X19) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

fof(c_0_10,plain,(
    ! [X17] : k2_tarski(X17,X17) = k1_tarski(X17) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_11,plain,(
    ! [X22,X23,X24] :
      ( ~ r1_tarski(k2_tarski(X22,X23),k1_tarski(X24))
      | k2_tarski(X22,X23) = k1_tarski(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_zfmisc_1])])).

fof(c_0_12,plain,(
    ! [X11] :
      ( ~ r1_tarski(X11,k1_xboole_0)
      | X11 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_13,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k2_tarski(X1,X2) = k1_tarski(X3)
    | ~ r1_tarski(k2_tarski(X1,X2),k1_tarski(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r1_tarski(k2_tarski(X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_18,plain,(
    ! [X10] : r1_tarski(k1_xboole_0,X10) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_19,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X3,X3)
    | ~ r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_14]),c_0_14])).

cnf(c_0_20,plain,
    ( k2_tarski(X1,X1) = k1_xboole_0
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X36,X37,X38,X40,X41,X42,X43,X45] :
      ( ( ~ r2_hidden(X38,X37)
        | r2_hidden(k4_tarski(X38,esk2_3(X36,X37,X38)),X36)
        | X37 != k1_relat_1(X36) )
      & ( ~ r2_hidden(k4_tarski(X40,X41),X36)
        | r2_hidden(X40,X37)
        | X37 != k1_relat_1(X36) )
      & ( ~ r2_hidden(esk3_2(X42,X43),X43)
        | ~ r2_hidden(k4_tarski(esk3_2(X42,X43),X45),X42)
        | X43 = k1_relat_1(X42) )
      & ( r2_hidden(esk3_2(X42,X43),X43)
        | r2_hidden(k4_tarski(esk3_2(X42,X43),esk4_2(X42,X43)),X42)
        | X43 = k1_relat_1(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_23,plain,
    ( k2_tarski(X1,X1) = k1_xboole_0
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_24,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)
    | X2 = k1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_25,plain,
    ( k2_tarski(X1,X1) = k1_xboole_0
    | X2 = k1_relat_1(k1_xboole_0)
    | r2_hidden(esk3_2(k1_xboole_0,X2),X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_27,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | k2_tarski(X1,X1) = k1_xboole_0
    | k2_tarski(X2,X2) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_25])).

fof(c_0_28,plain,(
    ! [X47,X48,X49,X51,X52,X53,X54,X56] :
      ( ( ~ r2_hidden(X49,X48)
        | r2_hidden(k4_tarski(esk5_3(X47,X48,X49),X49),X47)
        | X48 != k2_relat_1(X47) )
      & ( ~ r2_hidden(k4_tarski(X52,X51),X47)
        | r2_hidden(X51,X48)
        | X48 != k2_relat_1(X47) )
      & ( ~ r2_hidden(esk6_2(X53,X54),X54)
        | ~ r2_hidden(k4_tarski(X56,esk6_2(X53,X54)),X53)
        | X54 = k2_relat_1(X53) )
      & ( r2_hidden(esk6_2(X53,X54),X54)
        | r2_hidden(k4_tarski(esk7_2(X53,X54),esk6_2(X53,X54)),X53)
        | X54 = k2_relat_1(X53) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

fof(c_0_29,plain,(
    ! [X20,X21] : ~ r2_hidden(X20,k2_zfmisc_1(X20,X21)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X1,X1),X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_14])).

cnf(c_0_31,plain,
    ( k2_tarski(X1,X1) = k1_xboole_0
    | k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_27])).

fof(c_0_32,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t60_relat_1])).

cnf(c_0_33,plain,
    ( r2_hidden(k4_tarski(esk5_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | r2_hidden(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_21])])).

fof(c_0_36,negated_conjecture,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(fof_nnf,[status(thm)],[c_0_32])).

cnf(c_0_37,plain,
    ( r2_hidden(k4_tarski(esk5_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_38,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_40,plain,
    ( k2_tarski(X1,X1) = k1_xboole_0
    | ~ r2_hidden(X2,k2_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_37])).

cnf(c_0_41,plain,
    ( k2_tarski(X1,X1) = k1_xboole_0
    | X2 = k1_xboole_0
    | r2_hidden(esk3_2(k1_xboole_0,X2),X2) ),
    inference(rw,[status(thm)],[c_0_25,c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_38])])).

cnf(c_0_43,plain,
    ( k2_tarski(X1,X1) = k1_xboole_0
    | k2_tarski(X2,X2) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_44,plain,
    ( k2_tarski(X1,X1) = k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_43])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_44]),c_0_21])])).

cnf(c_0_46,plain,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_45])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:52:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.21/0.39  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.21/0.39  #
% 0.21/0.39  # Preprocessing time       : 0.028 s
% 0.21/0.39  # Presaturation interreduction done
% 0.21/0.39  
% 0.21/0.39  # Proof found!
% 0.21/0.39  # SZS status Theorem
% 0.21/0.39  # SZS output start CNFRefutation
% 0.21/0.39  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.21/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.21/0.39  fof(t27_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),k1_tarski(X3))=>k2_tarski(X1,X2)=k1_tarski(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_zfmisc_1)).
% 0.21/0.39  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.21/0.39  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.21/0.39  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 0.21/0.39  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 0.21/0.39  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.21/0.39  fof(t60_relat_1, conjecture, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.21/0.39  fof(c_0_9, plain, ![X18, X19]:((~r1_tarski(k1_tarski(X18),X19)|r2_hidden(X18,X19))&(~r2_hidden(X18,X19)|r1_tarski(k1_tarski(X18),X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.21/0.39  fof(c_0_10, plain, ![X17]:k2_tarski(X17,X17)=k1_tarski(X17), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.39  fof(c_0_11, plain, ![X22, X23, X24]:(~r1_tarski(k2_tarski(X22,X23),k1_tarski(X24))|k2_tarski(X22,X23)=k1_tarski(X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_zfmisc_1])])).
% 0.21/0.39  fof(c_0_12, plain, ![X11]:(~r1_tarski(X11,k1_xboole_0)|X11=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.21/0.39  cnf(c_0_13, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.39  cnf(c_0_14, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_15, plain, (k2_tarski(X1,X2)=k1_tarski(X3)|~r1_tarski(k2_tarski(X1,X2),k1_tarski(X3))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.39  cnf(c_0_16, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.39  cnf(c_0_17, plain, (r1_tarski(k2_tarski(X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.21/0.39  fof(c_0_18, plain, ![X10]:r1_tarski(k1_xboole_0,X10), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.21/0.39  cnf(c_0_19, plain, (k2_tarski(X1,X2)=k2_tarski(X3,X3)|~r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_14]), c_0_14])).
% 0.21/0.39  cnf(c_0_20, plain, (k2_tarski(X1,X1)=k1_xboole_0|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.21/0.39  cnf(c_0_21, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.39  fof(c_0_22, plain, ![X36, X37, X38, X40, X41, X42, X43, X45]:(((~r2_hidden(X38,X37)|r2_hidden(k4_tarski(X38,esk2_3(X36,X37,X38)),X36)|X37!=k1_relat_1(X36))&(~r2_hidden(k4_tarski(X40,X41),X36)|r2_hidden(X40,X37)|X37!=k1_relat_1(X36)))&((~r2_hidden(esk3_2(X42,X43),X43)|~r2_hidden(k4_tarski(esk3_2(X42,X43),X45),X42)|X43=k1_relat_1(X42))&(r2_hidden(esk3_2(X42,X43),X43)|r2_hidden(k4_tarski(esk3_2(X42,X43),esk4_2(X42,X43)),X42)|X43=k1_relat_1(X42)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.21/0.39  cnf(c_0_23, plain, (k2_tarski(X1,X1)=k1_xboole_0|~r2_hidden(X2,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])])).
% 0.21/0.39  cnf(c_0_24, plain, (r2_hidden(esk3_2(X1,X2),X2)|r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)|X2=k1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.39  cnf(c_0_25, plain, (k2_tarski(X1,X1)=k1_xboole_0|X2=k1_relat_1(k1_xboole_0)|r2_hidden(esk3_2(k1_xboole_0,X2),X2)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.21/0.39  cnf(c_0_26, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.39  cnf(c_0_27, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0|k2_tarski(X1,X1)=k1_xboole_0|k2_tarski(X2,X2)=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_25])).
% 0.21/0.39  fof(c_0_28, plain, ![X47, X48, X49, X51, X52, X53, X54, X56]:(((~r2_hidden(X49,X48)|r2_hidden(k4_tarski(esk5_3(X47,X48,X49),X49),X47)|X48!=k2_relat_1(X47))&(~r2_hidden(k4_tarski(X52,X51),X47)|r2_hidden(X51,X48)|X48!=k2_relat_1(X47)))&((~r2_hidden(esk6_2(X53,X54),X54)|~r2_hidden(k4_tarski(X56,esk6_2(X53,X54)),X53)|X54=k2_relat_1(X53))&(r2_hidden(esk6_2(X53,X54),X54)|r2_hidden(k4_tarski(esk7_2(X53,X54),esk6_2(X53,X54)),X53)|X54=k2_relat_1(X53)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.21/0.39  fof(c_0_29, plain, ![X20, X21]:~r2_hidden(X20,k2_zfmisc_1(X20,X21)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.21/0.39  cnf(c_0_30, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X1,X1),X2)), inference(rw,[status(thm)],[c_0_26, c_0_14])).
% 0.21/0.39  cnf(c_0_31, plain, (k2_tarski(X1,X1)=k1_xboole_0|k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(ef,[status(thm)],[c_0_27])).
% 0.21/0.39  fof(c_0_32, negated_conjecture, ~((k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0)), inference(assume_negation,[status(cth)],[t60_relat_1])).
% 0.21/0.39  cnf(c_0_33, plain, (r2_hidden(k4_tarski(esk5_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.39  cnf(c_0_34, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.39  cnf(c_0_35, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0|r2_hidden(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_21])])).
% 0.21/0.39  fof(c_0_36, negated_conjecture, (k1_relat_1(k1_xboole_0)!=k1_xboole_0|k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(fof_nnf,[status(thm)],[c_0_32])).
% 0.21/0.39  cnf(c_0_37, plain, (r2_hidden(k4_tarski(esk5_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_33])).
% 0.21/0.39  cnf(c_0_38, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.21/0.39  cnf(c_0_39, negated_conjecture, (k1_relat_1(k1_xboole_0)!=k1_xboole_0|k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.21/0.39  cnf(c_0_40, plain, (k2_tarski(X1,X1)=k1_xboole_0|~r2_hidden(X2,k2_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_23, c_0_37])).
% 0.21/0.39  cnf(c_0_41, plain, (k2_tarski(X1,X1)=k1_xboole_0|X2=k1_xboole_0|r2_hidden(esk3_2(k1_xboole_0,X2),X2)), inference(rw,[status(thm)],[c_0_25, c_0_38])).
% 0.21/0.39  cnf(c_0_42, negated_conjecture, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_38])])).
% 0.21/0.39  cnf(c_0_43, plain, (k2_tarski(X1,X1)=k1_xboole_0|k2_tarski(X2,X2)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 0.21/0.39  cnf(c_0_44, plain, (k2_tarski(X1,X1)=k1_xboole_0), inference(ef,[status(thm)],[c_0_43])).
% 0.21/0.39  cnf(c_0_45, plain, (r2_hidden(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_44]), c_0_21])])).
% 0.21/0.39  cnf(c_0_46, plain, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_45])]), ['proof']).
% 0.21/0.39  # SZS output end CNFRefutation
% 0.21/0.39  # Proof object total steps             : 47
% 0.21/0.39  # Proof object clause steps            : 28
% 0.21/0.39  # Proof object formula steps           : 19
% 0.21/0.39  # Proof object conjectures             : 5
% 0.21/0.39  # Proof object clause conjectures      : 2
% 0.21/0.39  # Proof object formula conjectures     : 3
% 0.21/0.39  # Proof object initial clauses used    : 10
% 0.21/0.39  # Proof object initial formulas used   : 9
% 0.21/0.39  # Proof object generating inferences   : 10
% 0.21/0.39  # Proof object simplifying inferences  : 18
% 0.21/0.39  # Training examples: 0 positive, 0 negative
% 0.21/0.39  # Parsed axioms                        : 21
% 0.21/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.39  # Initial clauses                      : 31
% 0.21/0.39  # Removed in clause preprocessing      : 2
% 0.21/0.39  # Initial clauses in saturation        : 29
% 0.21/0.39  # Processed clauses                    : 218
% 0.21/0.39  # ...of these trivial                  : 0
% 0.21/0.39  # ...subsumed                          : 66
% 0.21/0.39  # ...remaining for further processing  : 152
% 0.21/0.39  # Other redundant clauses eliminated   : 4
% 0.21/0.39  # Clauses deleted for lack of memory   : 0
% 0.21/0.39  # Backward-subsumed                    : 25
% 0.21/0.39  # Backward-rewritten                   : 75
% 0.21/0.39  # Generated clauses                    : 885
% 0.21/0.39  # ...of the previous two non-trivial   : 860
% 0.21/0.39  # Contextual simplify-reflections      : 2
% 0.21/0.39  # Paramodulations                      : 875
% 0.21/0.39  # Factorizations                       : 6
% 0.21/0.39  # Equation resolutions                 : 4
% 0.21/0.39  # Propositional unsat checks           : 0
% 0.21/0.39  #    Propositional check models        : 0
% 0.21/0.39  #    Propositional check unsatisfiable : 0
% 0.21/0.39  #    Propositional clauses             : 0
% 0.21/0.39  #    Propositional clauses after purity: 0
% 0.21/0.39  #    Propositional unsat core size     : 0
% 0.21/0.39  #    Propositional preprocessing time  : 0.000
% 0.21/0.39  #    Propositional encoding time       : 0.000
% 0.21/0.39  #    Propositional solver time         : 0.000
% 0.21/0.39  #    Success case prop preproc time    : 0.000
% 0.21/0.39  #    Success case prop encoding time   : 0.000
% 0.21/0.39  #    Success case prop solver time     : 0.000
% 0.21/0.39  # Current number of processed clauses  : 19
% 0.21/0.39  #    Positive orientable unit clauses  : 7
% 0.21/0.39  #    Positive unorientable unit clauses: 0
% 0.21/0.39  #    Negative unit clauses             : 2
% 0.21/0.39  #    Non-unit-clauses                  : 10
% 0.21/0.39  # Current number of unprocessed clauses: 618
% 0.21/0.39  # ...number of literals in the above   : 1826
% 0.21/0.39  # Current number of archived formulas  : 0
% 0.21/0.39  # Current number of archived clauses   : 131
% 0.21/0.39  # Clause-clause subsumption calls (NU) : 2574
% 0.21/0.39  # Rec. Clause-clause subsumption calls : 1679
% 0.21/0.39  # Non-unit clause-clause subsumptions  : 72
% 0.21/0.39  # Unit Clause-clause subsumption calls : 26
% 0.21/0.39  # Rewrite failures with RHS unbound    : 0
% 0.21/0.39  # BW rewrite match attempts            : 39
% 0.21/0.39  # BW rewrite match successes           : 37
% 0.21/0.39  # Condensation attempts                : 0
% 0.21/0.39  # Condensation successes               : 0
% 0.21/0.39  # Termbank termtop insertions          : 12070
% 0.21/0.39  
% 0.21/0.39  # -------------------------------------------------
% 0.21/0.39  # User time                : 0.045 s
% 0.21/0.39  # System time              : 0.004 s
% 0.21/0.39  # Total time               : 0.049 s
% 0.21/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
