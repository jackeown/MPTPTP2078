%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:30 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   31 ( 306 expanded)
%              Number of clauses        :   22 ( 161 expanded)
%              Number of leaves         :    4 (  70 expanded)
%              Depth                    :   11
%              Number of atoms          :  104 (1181 expanded)
%              Number of equality atoms :   56 ( 544 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

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

fof(t113_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(c_0_4,plain,(
    ! [X25,X26,X27] :
      ( ( r2_hidden(X25,X26)
        | ~ r2_hidden(X25,k4_xboole_0(X26,k1_tarski(X27))) )
      & ( X25 != X27
        | ~ r2_hidden(X25,k4_xboole_0(X26,k1_tarski(X27))) )
      & ( ~ r2_hidden(X25,X26)
        | X25 = X27
        | r2_hidden(X25,k4_xboole_0(X26,k1_tarski(X27))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

cnf(c_0_5,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_6,plain,(
    ! [X7] : k4_xboole_0(k1_xboole_0,X7) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_7,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X1))) ),
    inference(er,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,plain,(
    ! [X8,X9,X10,X11,X14,X15,X16,X17,X18,X19,X21,X22] :
      ( ( r2_hidden(esk1_4(X8,X9,X10,X11),X8)
        | ~ r2_hidden(X11,X10)
        | X10 != k2_zfmisc_1(X8,X9) )
      & ( r2_hidden(esk2_4(X8,X9,X10,X11),X9)
        | ~ r2_hidden(X11,X10)
        | X10 != k2_zfmisc_1(X8,X9) )
      & ( X11 = k4_tarski(esk1_4(X8,X9,X10,X11),esk2_4(X8,X9,X10,X11))
        | ~ r2_hidden(X11,X10)
        | X10 != k2_zfmisc_1(X8,X9) )
      & ( ~ r2_hidden(X15,X8)
        | ~ r2_hidden(X16,X9)
        | X14 != k4_tarski(X15,X16)
        | r2_hidden(X14,X10)
        | X10 != k2_zfmisc_1(X8,X9) )
      & ( ~ r2_hidden(esk3_3(X17,X18,X19),X19)
        | ~ r2_hidden(X21,X17)
        | ~ r2_hidden(X22,X18)
        | esk3_3(X17,X18,X19) != k4_tarski(X21,X22)
        | X19 = k2_zfmisc_1(X17,X18) )
      & ( r2_hidden(esk4_3(X17,X18,X19),X17)
        | r2_hidden(esk3_3(X17,X18,X19),X19)
        | X19 = k2_zfmisc_1(X17,X18) )
      & ( r2_hidden(esk5_3(X17,X18,X19),X18)
        | r2_hidden(esk3_3(X17,X18,X19),X19)
        | X19 = k2_zfmisc_1(X17,X18) )
      & ( esk3_3(X17,X18,X19) = k4_tarski(esk4_3(X17,X18,X19),esk5_3(X17,X18,X19))
        | r2_hidden(esk3_3(X17,X18,X19),X19)
        | X19 = k2_zfmisc_1(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_zfmisc_1(X1,X2) = k1_xboole_0
      <=> ( X1 = k1_xboole_0
          | X2 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t113_zfmisc_1])).

cnf(c_0_11,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_12,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X1)
    | r2_hidden(esk3_3(X1,X2,X3),X3)
    | X3 = k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r2_hidden(X5,X6)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X5 != k4_tarski(X1,X3)
    | X6 != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,negated_conjecture,
    ( ( esk6_0 != k1_xboole_0
      | k2_zfmisc_1(esk6_0,esk7_0) != k1_xboole_0 )
    & ( esk7_0 != k1_xboole_0
      | k2_zfmisc_1(esk6_0,esk7_0) != k1_xboole_0 )
    & ( k2_zfmisc_1(esk6_0,esk7_0) = k1_xboole_0
      | esk6_0 = k1_xboole_0
      | esk7_0 = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).

cnf(c_0_15,plain,
    ( X1 = k2_zfmisc_1(k1_xboole_0,X2)
    | r2_hidden(esk3_3(k1_xboole_0,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_13])])).

cnf(c_0_17,negated_conjecture,
    ( k2_zfmisc_1(esk6_0,esk7_0) = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_11,c_0_15])).

cnf(c_0_19,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | ~ r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X2,esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_11])).

cnf(c_0_21,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_3(k1_xboole_0,X2,X1),X1) ),
    inference(rw,[status(thm)],[c_0_15,c_0_18])).

cnf(c_0_22,plain,
    ( r2_hidden(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X2,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( esk7_0 != k1_xboole_0
    | k2_zfmisc_1(esk6_0,esk7_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_21])).

cnf(c_0_27,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | k2_zfmisc_1(esk6_0,esk7_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_29,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_18]),c_0_29])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:18:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.36  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.36  #
% 0.20/0.36  # Preprocessing time       : 0.016 s
% 0.20/0.36  # Presaturation interreduction done
% 0.20/0.36  
% 0.20/0.36  # Proof found!
% 0.20/0.36  # SZS status Theorem
% 0.20/0.36  # SZS output start CNFRefutation
% 0.20/0.36  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 0.20/0.36  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 0.20/0.36  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.20/0.36  fof(t113_zfmisc_1, conjecture, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.20/0.36  fof(c_0_4, plain, ![X25, X26, X27]:(((r2_hidden(X25,X26)|~r2_hidden(X25,k4_xboole_0(X26,k1_tarski(X27))))&(X25!=X27|~r2_hidden(X25,k4_xboole_0(X26,k1_tarski(X27)))))&(~r2_hidden(X25,X26)|X25=X27|r2_hidden(X25,k4_xboole_0(X26,k1_tarski(X27))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 0.20/0.36  cnf(c_0_5, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.36  fof(c_0_6, plain, ![X7]:k4_xboole_0(k1_xboole_0,X7)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.20/0.36  cnf(c_0_7, plain, (~r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X1)))), inference(er,[status(thm)],[c_0_5])).
% 0.20/0.36  cnf(c_0_8, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.36  fof(c_0_9, plain, ![X8, X9, X10, X11, X14, X15, X16, X17, X18, X19, X21, X22]:(((((r2_hidden(esk1_4(X8,X9,X10,X11),X8)|~r2_hidden(X11,X10)|X10!=k2_zfmisc_1(X8,X9))&(r2_hidden(esk2_4(X8,X9,X10,X11),X9)|~r2_hidden(X11,X10)|X10!=k2_zfmisc_1(X8,X9)))&(X11=k4_tarski(esk1_4(X8,X9,X10,X11),esk2_4(X8,X9,X10,X11))|~r2_hidden(X11,X10)|X10!=k2_zfmisc_1(X8,X9)))&(~r2_hidden(X15,X8)|~r2_hidden(X16,X9)|X14!=k4_tarski(X15,X16)|r2_hidden(X14,X10)|X10!=k2_zfmisc_1(X8,X9)))&((~r2_hidden(esk3_3(X17,X18,X19),X19)|(~r2_hidden(X21,X17)|~r2_hidden(X22,X18)|esk3_3(X17,X18,X19)!=k4_tarski(X21,X22))|X19=k2_zfmisc_1(X17,X18))&(((r2_hidden(esk4_3(X17,X18,X19),X17)|r2_hidden(esk3_3(X17,X18,X19),X19)|X19=k2_zfmisc_1(X17,X18))&(r2_hidden(esk5_3(X17,X18,X19),X18)|r2_hidden(esk3_3(X17,X18,X19),X19)|X19=k2_zfmisc_1(X17,X18)))&(esk3_3(X17,X18,X19)=k4_tarski(esk4_3(X17,X18,X19),esk5_3(X17,X18,X19))|r2_hidden(esk3_3(X17,X18,X19),X19)|X19=k2_zfmisc_1(X17,X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.20/0.36  fof(c_0_10, negated_conjecture, ~(![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0))), inference(assume_negation,[status(cth)],[t113_zfmisc_1])).
% 0.20/0.36  cnf(c_0_11, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_7, c_0_8])).
% 0.20/0.36  cnf(c_0_12, plain, (r2_hidden(esk4_3(X1,X2,X3),X1)|r2_hidden(esk3_3(X1,X2,X3),X3)|X3=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.36  cnf(c_0_13, plain, (r2_hidden(X5,X6)|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X5!=k4_tarski(X1,X3)|X6!=k2_zfmisc_1(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.36  fof(c_0_14, negated_conjecture, (((esk6_0!=k1_xboole_0|k2_zfmisc_1(esk6_0,esk7_0)!=k1_xboole_0)&(esk7_0!=k1_xboole_0|k2_zfmisc_1(esk6_0,esk7_0)!=k1_xboole_0))&(k2_zfmisc_1(esk6_0,esk7_0)=k1_xboole_0|(esk6_0=k1_xboole_0|esk7_0=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).
% 0.20/0.36  cnf(c_0_15, plain, (X1=k2_zfmisc_1(k1_xboole_0,X2)|r2_hidden(esk3_3(k1_xboole_0,X2,X1),X1)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.20/0.36  cnf(c_0_16, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))|~r2_hidden(X2,X4)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_13])])).
% 0.20/0.36  cnf(c_0_17, negated_conjecture, (k2_zfmisc_1(esk6_0,esk7_0)=k1_xboole_0|esk6_0=k1_xboole_0|esk7_0=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.36  cnf(c_0_18, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_11, c_0_15])).
% 0.20/0.36  cnf(c_0_19, plain, (r2_hidden(esk2_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.36  cnf(c_0_20, negated_conjecture, (esk7_0=k1_xboole_0|esk6_0=k1_xboole_0|~r2_hidden(X1,esk7_0)|~r2_hidden(X2,esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_11])).
% 0.20/0.36  cnf(c_0_21, plain, (X1=k1_xboole_0|r2_hidden(esk3_3(k1_xboole_0,X2,X1),X1)), inference(rw,[status(thm)],[c_0_15, c_0_18])).
% 0.20/0.36  cnf(c_0_22, plain, (r2_hidden(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_19])).
% 0.20/0.36  cnf(c_0_23, negated_conjecture, (esk6_0=k1_xboole_0|esk7_0=k1_xboole_0|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.36  cnf(c_0_24, plain, (~r2_hidden(X1,k2_zfmisc_1(X2,k1_xboole_0))), inference(spm,[status(thm)],[c_0_11, c_0_22])).
% 0.20/0.36  cnf(c_0_25, negated_conjecture, (esk7_0!=k1_xboole_0|k2_zfmisc_1(esk6_0,esk7_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.36  cnf(c_0_26, negated_conjecture, (esk7_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_21])).
% 0.20/0.36  cnf(c_0_27, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_21])).
% 0.20/0.36  cnf(c_0_28, negated_conjecture, (esk6_0!=k1_xboole_0|k2_zfmisc_1(esk6_0,esk7_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.36  cnf(c_0_29, negated_conjecture, (esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])])).
% 0.20/0.36  cnf(c_0_30, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_18]), c_0_29])]), ['proof']).
% 0.20/0.36  # SZS output end CNFRefutation
% 0.20/0.36  # Proof object total steps             : 31
% 0.20/0.36  # Proof object clause steps            : 22
% 0.20/0.36  # Proof object formula steps           : 9
% 0.20/0.36  # Proof object conjectures             : 11
% 0.20/0.36  # Proof object clause conjectures      : 8
% 0.20/0.36  # Proof object formula conjectures     : 3
% 0.20/0.36  # Proof object initial clauses used    : 8
% 0.20/0.36  # Proof object initial formulas used   : 4
% 0.20/0.36  # Proof object generating inferences   : 9
% 0.20/0.36  # Proof object simplifying inferences  : 12
% 0.20/0.36  # Training examples: 0 positive, 0 negative
% 0.20/0.36  # Parsed axioms                        : 4
% 0.20/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.36  # Initial clauses                      : 15
% 0.20/0.36  # Removed in clause preprocessing      : 0
% 0.20/0.36  # Initial clauses in saturation        : 15
% 0.20/0.36  # Processed clauses                    : 121
% 0.20/0.36  # ...of these trivial                  : 0
% 0.20/0.36  # ...subsumed                          : 55
% 0.20/0.36  # ...remaining for further processing  : 66
% 0.20/0.36  # Other redundant clauses eliminated   : 6
% 0.20/0.36  # Clauses deleted for lack of memory   : 0
% 0.20/0.36  # Backward-subsumed                    : 7
% 0.20/0.36  # Backward-rewritten                   : 18
% 0.20/0.36  # Generated clauses                    : 297
% 0.20/0.36  # ...of the previous two non-trivial   : 309
% 0.20/0.36  # Contextual simplify-reflections      : 0
% 0.20/0.36  # Paramodulations                      : 292
% 0.20/0.36  # Factorizations                       : 0
% 0.20/0.36  # Equation resolutions                 : 6
% 0.20/0.36  # Propositional unsat checks           : 0
% 0.20/0.36  #    Propositional check models        : 0
% 0.20/0.36  #    Propositional check unsatisfiable : 0
% 0.20/0.36  #    Propositional clauses             : 0
% 0.20/0.36  #    Propositional clauses after purity: 0
% 0.20/0.36  #    Propositional unsat core size     : 0
% 0.20/0.36  #    Propositional preprocessing time  : 0.000
% 0.20/0.36  #    Propositional encoding time       : 0.000
% 0.20/0.36  #    Propositional solver time         : 0.000
% 0.20/0.36  #    Success case prop preproc time    : 0.000
% 0.20/0.36  #    Success case prop encoding time   : 0.000
% 0.20/0.36  #    Success case prop solver time     : 0.000
% 0.20/0.36  # Current number of processed clauses  : 21
% 0.20/0.36  #    Positive orientable unit clauses  : 4
% 0.20/0.36  #    Positive unorientable unit clauses: 0
% 0.20/0.36  #    Negative unit clauses             : 2
% 0.20/0.36  #    Non-unit-clauses                  : 15
% 0.20/0.36  # Current number of unprocessed clauses: 208
% 0.20/0.36  # ...number of literals in the above   : 567
% 0.20/0.36  # Current number of archived formulas  : 0
% 0.20/0.36  # Current number of archived clauses   : 40
% 0.20/0.36  # Clause-clause subsumption calls (NU) : 64
% 0.20/0.36  # Rec. Clause-clause subsumption calls : 47
% 0.20/0.36  # Non-unit clause-clause subsumptions  : 7
% 0.20/0.36  # Unit Clause-clause subsumption calls : 37
% 0.20/0.36  # Rewrite failures with RHS unbound    : 0
% 0.20/0.36  # BW rewrite match attempts            : 7
% 0.20/0.36  # BW rewrite match successes           : 7
% 0.20/0.36  # Condensation attempts                : 0
% 0.20/0.36  # Condensation successes               : 0
% 0.20/0.36  # Termbank termtop insertions          : 4503
% 0.20/0.36  
% 0.20/0.36  # -------------------------------------------------
% 0.20/0.36  # User time                : 0.017 s
% 0.20/0.36  # System time              : 0.006 s
% 0.20/0.36  # Total time               : 0.023 s
% 0.20/0.36  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
