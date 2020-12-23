%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:26 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 234 expanded)
%              Number of clauses        :   35 ( 115 expanded)
%              Number of leaves         :    8 (  57 expanded)
%              Depth                    :   12
%              Number of atoms          :  150 ( 809 expanded)
%              Number of equality atoms :   57 ( 289 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(t69_xboole_1,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_tarski(X2,X1)
          & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(t113_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(c_0_8,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_9,plain,(
    ! [X17,X18,X19,X20,X23,X24,X25,X26,X27,X28,X30,X31] :
      ( ( r2_hidden(esk3_4(X17,X18,X19,X20),X17)
        | ~ r2_hidden(X20,X19)
        | X19 != k2_zfmisc_1(X17,X18) )
      & ( r2_hidden(esk4_4(X17,X18,X19,X20),X18)
        | ~ r2_hidden(X20,X19)
        | X19 != k2_zfmisc_1(X17,X18) )
      & ( X20 = k4_tarski(esk3_4(X17,X18,X19,X20),esk4_4(X17,X18,X19,X20))
        | ~ r2_hidden(X20,X19)
        | X19 != k2_zfmisc_1(X17,X18) )
      & ( ~ r2_hidden(X24,X17)
        | ~ r2_hidden(X25,X18)
        | X23 != k4_tarski(X24,X25)
        | r2_hidden(X23,X19)
        | X19 != k2_zfmisc_1(X17,X18) )
      & ( ~ r2_hidden(esk5_3(X26,X27,X28),X28)
        | ~ r2_hidden(X30,X26)
        | ~ r2_hidden(X31,X27)
        | esk5_3(X26,X27,X28) != k4_tarski(X30,X31)
        | X28 = k2_zfmisc_1(X26,X27) )
      & ( r2_hidden(esk6_3(X26,X27,X28),X26)
        | r2_hidden(esk5_3(X26,X27,X28),X28)
        | X28 = k2_zfmisc_1(X26,X27) )
      & ( r2_hidden(esk7_3(X26,X27,X28),X27)
        | r2_hidden(esk5_3(X26,X27,X28),X28)
        | X28 = k2_zfmisc_1(X26,X27) )
      & ( esk5_3(X26,X27,X28) = k4_tarski(esk6_3(X26,X27,X28),esk7_3(X26,X27,X28))
        | r2_hidden(esk5_3(X26,X27,X28),X28)
        | X28 = k2_zfmisc_1(X26,X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_10,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,plain,(
    ! [X15,X16] :
      ( v1_xboole_0(X16)
      | ~ r1_tarski(X16,X15)
      | ~ r1_xboole_0(X16,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

fof(c_0_13,plain,(
    ! [X13] : r1_tarski(k1_xboole_0,X13) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_14,plain,
    ( X1 != k2_zfmisc_1(X2,X3)
    | ~ r2_hidden(X4,X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

fof(c_0_15,plain,(
    ! [X11] :
      ( X11 = k1_xboole_0
      | r2_hidden(esk2_1(X11),X11) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_16,plain,(
    ! [X34,X35,X36,X37] :
      ( ( r2_hidden(X34,X36)
        | ~ r2_hidden(k4_tarski(X34,X35),k2_zfmisc_1(X36,X37)) )
      & ( r2_hidden(X35,X37)
        | ~ r2_hidden(k4_tarski(X34,X35),k2_zfmisc_1(X36,X37)) )
      & ( ~ r2_hidden(X34,X36)
        | ~ r2_hidden(X35,X37)
        | r2_hidden(k4_tarski(X34,X35),k2_zfmisc_1(X36,X37)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_zfmisc_1(X1,X2) = k1_xboole_0
      <=> ( X1 = k1_xboole_0
          | X2 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t113_zfmisc_1])).

cnf(c_0_18,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_20,plain,(
    ! [X14] : r1_xboole_0(X14,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X2,X3))
    | ~ v1_xboole_0(X2) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_24,negated_conjecture,
    ( ( esk8_0 != k1_xboole_0
      | k2_zfmisc_1(esk8_0,esk9_0) != k1_xboole_0 )
    & ( esk9_0 != k1_xboole_0
      | k2_zfmisc_1(esk8_0,esk9_0) != k1_xboole_0 )
    & ( k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0
      | esk8_0 = k1_xboole_0
      | esk9_0 = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])])).

cnf(c_0_25,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | ~ v1_xboole_0(k2_zfmisc_1(X4,X2)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk9_0 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1)
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_14,c_0_27])).

cnf(c_0_32,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_33,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | ~ r2_hidden(X1,esk9_0)
    | ~ r2_hidden(X2,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

cnf(c_0_34,negated_conjecture,
    ( esk8_0 != k1_xboole_0
    | k2_zfmisc_1(esk8_0,esk9_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_22])).

cnf(c_0_36,plain,
    ( v1_xboole_0(X1)
    | X1 != k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_27])).

cnf(c_0_38,plain,
    ( r2_hidden(esk4_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_39,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk9_0 = k1_xboole_0
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_22])).

cnf(c_0_40,negated_conjecture,
    ( ~ v1_xboole_0(esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_27]),c_0_35])).

cnf(c_0_41,plain,
    ( v1_xboole_0(X1)
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_30])).

cnf(c_0_42,plain,
    ( X1 != k2_zfmisc_1(X2,k1_xboole_0)
    | ~ r2_hidden(X3,X1)
    | ~ v1_xboole_0(X4) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_22])).

cnf(c_0_44,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X2,k1_xboole_0))
    | ~ v1_xboole_0(X3) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( esk9_0 != k1_xboole_0
    | k2_zfmisc_1(esk8_0,esk9_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_47,negated_conjecture,
    ( esk9_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_48,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_22])).

cnf(c_0_49,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,k1_xboole_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47]),c_0_47])])).

cnf(c_0_50,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_48,c_0_30])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:53:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.14/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.027 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.14/0.38  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.14/0.38  fof(t69_xboole_1, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>~((r1_tarski(X2,X1)&r1_xboole_0(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 0.14/0.38  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.14/0.38  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.14/0.38  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.14/0.38  fof(t113_zfmisc_1, conjecture, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.14/0.38  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.14/0.38  fof(c_0_8, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.14/0.38  fof(c_0_9, plain, ![X17, X18, X19, X20, X23, X24, X25, X26, X27, X28, X30, X31]:(((((r2_hidden(esk3_4(X17,X18,X19,X20),X17)|~r2_hidden(X20,X19)|X19!=k2_zfmisc_1(X17,X18))&(r2_hidden(esk4_4(X17,X18,X19,X20),X18)|~r2_hidden(X20,X19)|X19!=k2_zfmisc_1(X17,X18)))&(X20=k4_tarski(esk3_4(X17,X18,X19,X20),esk4_4(X17,X18,X19,X20))|~r2_hidden(X20,X19)|X19!=k2_zfmisc_1(X17,X18)))&(~r2_hidden(X24,X17)|~r2_hidden(X25,X18)|X23!=k4_tarski(X24,X25)|r2_hidden(X23,X19)|X19!=k2_zfmisc_1(X17,X18)))&((~r2_hidden(esk5_3(X26,X27,X28),X28)|(~r2_hidden(X30,X26)|~r2_hidden(X31,X27)|esk5_3(X26,X27,X28)!=k4_tarski(X30,X31))|X28=k2_zfmisc_1(X26,X27))&(((r2_hidden(esk6_3(X26,X27,X28),X26)|r2_hidden(esk5_3(X26,X27,X28),X28)|X28=k2_zfmisc_1(X26,X27))&(r2_hidden(esk7_3(X26,X27,X28),X27)|r2_hidden(esk5_3(X26,X27,X28),X28)|X28=k2_zfmisc_1(X26,X27)))&(esk5_3(X26,X27,X28)=k4_tarski(esk6_3(X26,X27,X28),esk7_3(X26,X27,X28))|r2_hidden(esk5_3(X26,X27,X28),X28)|X28=k2_zfmisc_1(X26,X27))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.14/0.38  cnf(c_0_10, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_11, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X1)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  fof(c_0_12, plain, ![X15, X16]:(v1_xboole_0(X16)|(~r1_tarski(X16,X15)|~r1_xboole_0(X16,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).
% 0.14/0.38  fof(c_0_13, plain, ![X13]:r1_tarski(k1_xboole_0,X13), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.14/0.38  cnf(c_0_14, plain, (X1!=k2_zfmisc_1(X2,X3)|~r2_hidden(X4,X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.14/0.38  fof(c_0_15, plain, ![X11]:(X11=k1_xboole_0|r2_hidden(esk2_1(X11),X11)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.14/0.38  fof(c_0_16, plain, ![X34, X35, X36, X37]:(((r2_hidden(X34,X36)|~r2_hidden(k4_tarski(X34,X35),k2_zfmisc_1(X36,X37)))&(r2_hidden(X35,X37)|~r2_hidden(k4_tarski(X34,X35),k2_zfmisc_1(X36,X37))))&(~r2_hidden(X34,X36)|~r2_hidden(X35,X37)|r2_hidden(k4_tarski(X34,X35),k2_zfmisc_1(X36,X37)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.14/0.38  fof(c_0_17, negated_conjecture, ~(![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0))), inference(assume_negation,[status(cth)],[t113_zfmisc_1])).
% 0.14/0.38  cnf(c_0_18, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_19, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  fof(c_0_20, plain, ![X14]:r1_xboole_0(X14,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.14/0.38  cnf(c_0_21, plain, (~r2_hidden(X1,k2_zfmisc_1(X2,X3))|~v1_xboole_0(X2)), inference(er,[status(thm)],[c_0_14])).
% 0.14/0.38  cnf(c_0_22, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  cnf(c_0_23, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.38  fof(c_0_24, negated_conjecture, (((esk8_0!=k1_xboole_0|k2_zfmisc_1(esk8_0,esk9_0)!=k1_xboole_0)&(esk9_0!=k1_xboole_0|k2_zfmisc_1(esk8_0,esk9_0)!=k1_xboole_0))&(k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0|(esk8_0=k1_xboole_0|esk9_0=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])])).
% 0.14/0.38  cnf(c_0_25, plain, (v1_xboole_0(k1_xboole_0)|~r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.14/0.38  cnf(c_0_26, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.38  cnf(c_0_27, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.14/0.38  cnf(c_0_28, plain, (~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|~v1_xboole_0(k2_zfmisc_1(X4,X2))), inference(spm,[status(thm)],[c_0_10, c_0_23])).
% 0.14/0.38  cnf(c_0_29, negated_conjecture, (k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0|esk8_0=k1_xboole_0|esk9_0=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.38  cnf(c_0_30, plain, (v1_xboole_0(k1_xboole_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.14/0.38  cnf(c_0_31, plain, (X1!=k1_xboole_0|~r2_hidden(X2,X1)|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_14, c_0_27])).
% 0.14/0.38  cnf(c_0_32, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_33, negated_conjecture, (esk9_0=k1_xboole_0|esk8_0=k1_xboole_0|~r2_hidden(X1,esk9_0)|~r2_hidden(X2,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])])).
% 0.14/0.38  cnf(c_0_34, negated_conjecture, (esk8_0!=k1_xboole_0|k2_zfmisc_1(esk8_0,esk9_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.38  cnf(c_0_35, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_10, c_0_22])).
% 0.14/0.38  cnf(c_0_36, plain, (v1_xboole_0(X1)|X1!=k1_xboole_0|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.14/0.38  cnf(c_0_37, plain, (~r2_hidden(X1,k1_xboole_0)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_21, c_0_27])).
% 0.14/0.38  cnf(c_0_38, plain, (r2_hidden(esk4_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_39, negated_conjecture, (esk8_0=k1_xboole_0|esk9_0=k1_xboole_0|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_33, c_0_22])).
% 0.14/0.38  cnf(c_0_40, negated_conjecture, (~v1_xboole_0(esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_27]), c_0_35])).
% 0.14/0.38  cnf(c_0_41, plain, (v1_xboole_0(X1)|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_30])).
% 0.14/0.38  cnf(c_0_42, plain, (X1!=k2_zfmisc_1(X2,k1_xboole_0)|~r2_hidden(X3,X1)|~v1_xboole_0(X4)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.14/0.38  cnf(c_0_43, negated_conjecture, (esk9_0=k1_xboole_0|esk8_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_39, c_0_22])).
% 0.14/0.38  cnf(c_0_44, negated_conjecture, (esk8_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.14/0.38  cnf(c_0_45, plain, (~r2_hidden(X1,k2_zfmisc_1(X2,k1_xboole_0))|~v1_xboole_0(X3)), inference(er,[status(thm)],[c_0_42])).
% 0.14/0.38  cnf(c_0_46, negated_conjecture, (esk9_0!=k1_xboole_0|k2_zfmisc_1(esk8_0,esk9_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.38  cnf(c_0_47, negated_conjecture, (esk9_0=k1_xboole_0), inference(sr,[status(thm)],[c_0_43, c_0_44])).
% 0.14/0.38  cnf(c_0_48, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_45, c_0_22])).
% 0.14/0.38  cnf(c_0_49, negated_conjecture, (k2_zfmisc_1(esk8_0,k1_xboole_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47]), c_0_47])])).
% 0.14/0.38  cnf(c_0_50, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_48, c_0_30])).
% 0.14/0.38  cnf(c_0_51, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_50])]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 52
% 0.14/0.38  # Proof object clause steps            : 35
% 0.14/0.38  # Proof object formula steps           : 17
% 0.14/0.38  # Proof object conjectures             : 14
% 0.14/0.38  # Proof object clause conjectures      : 11
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 12
% 0.14/0.38  # Proof object initial formulas used   : 8
% 0.14/0.38  # Proof object generating inferences   : 20
% 0.14/0.38  # Proof object simplifying inferences  : 9
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 8
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 20
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 20
% 0.14/0.38  # Processed clauses                    : 70
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 9
% 0.14/0.38  # ...remaining for further processing  : 61
% 0.14/0.38  # Other redundant clauses eliminated   : 0
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 4
% 0.14/0.38  # Backward-rewritten                   : 9
% 0.14/0.38  # Generated clauses                    : 82
% 0.14/0.38  # ...of the previous two non-trivial   : 70
% 0.14/0.38  # Contextual simplify-reflections      : 1
% 0.14/0.38  # Paramodulations                      : 79
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 2
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 27
% 0.14/0.38  #    Positive orientable unit clauses  : 5
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 2
% 0.14/0.38  #    Non-unit-clauses                  : 20
% 0.14/0.38  # Current number of unprocessed clauses: 32
% 0.14/0.38  # ...number of literals in the above   : 104
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 34
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 128
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 71
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 9
% 0.14/0.38  # Unit Clause-clause subsumption calls : 7
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 5
% 0.14/0.38  # BW rewrite match successes           : 5
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 2152
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.030 s
% 0.14/0.38  # System time              : 0.003 s
% 0.14/0.38  # Total time               : 0.034 s
% 0.14/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
