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
% DateTime   : Thu Dec  3 10:43:27 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 779 expanded)
%              Number of clauses        :   32 ( 367 expanded)
%              Number of leaves         :    6 ( 191 expanded)
%              Depth                    :   12
%              Number of atoms          :  123 (2636 expanded)
%              Number of equality atoms :   60 (1419 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t113_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

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

fof(l33_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1)
    <=> ~ r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(l35_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_zfmisc_1(X1,X2) = k1_xboole_0
      <=> ( X1 = k1_xboole_0
          | X2 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t113_zfmisc_1])).

fof(c_0_7,negated_conjecture,
    ( ( esk9_0 != k1_xboole_0
      | k2_zfmisc_1(esk9_0,esk10_0) != k1_xboole_0 )
    & ( esk10_0 != k1_xboole_0
      | k2_zfmisc_1(esk9_0,esk10_0) != k1_xboole_0 )
    & ( k2_zfmisc_1(esk9_0,esk10_0) = k1_xboole_0
      | esk9_0 = k1_xboole_0
      | esk10_0 = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).

fof(c_0_8,plain,(
    ! [X26] :
      ( X26 = k1_xboole_0
      | r2_hidden(esk3_1(X26),X26) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_9,plain,(
    ! [X32,X33,X34,X35,X38,X39,X40,X41,X42,X43,X45,X46] :
      ( ( r2_hidden(esk4_4(X32,X33,X34,X35),X32)
        | ~ r2_hidden(X35,X34)
        | X34 != k2_zfmisc_1(X32,X33) )
      & ( r2_hidden(esk5_4(X32,X33,X34,X35),X33)
        | ~ r2_hidden(X35,X34)
        | X34 != k2_zfmisc_1(X32,X33) )
      & ( X35 = k4_tarski(esk4_4(X32,X33,X34,X35),esk5_4(X32,X33,X34,X35))
        | ~ r2_hidden(X35,X34)
        | X34 != k2_zfmisc_1(X32,X33) )
      & ( ~ r2_hidden(X39,X32)
        | ~ r2_hidden(X40,X33)
        | X38 != k4_tarski(X39,X40)
        | r2_hidden(X38,X34)
        | X34 != k2_zfmisc_1(X32,X33) )
      & ( ~ r2_hidden(esk6_3(X41,X42,X43),X43)
        | ~ r2_hidden(X45,X41)
        | ~ r2_hidden(X46,X42)
        | esk6_3(X41,X42,X43) != k4_tarski(X45,X46)
        | X43 = k2_zfmisc_1(X41,X42) )
      & ( r2_hidden(esk7_3(X41,X42,X43),X41)
        | r2_hidden(esk6_3(X41,X42,X43),X43)
        | X43 = k2_zfmisc_1(X41,X42) )
      & ( r2_hidden(esk8_3(X41,X42,X43),X42)
        | r2_hidden(esk6_3(X41,X42,X43),X43)
        | X43 = k2_zfmisc_1(X41,X42) )
      & ( esk6_3(X41,X42,X43) = k4_tarski(esk7_3(X41,X42,X43),esk8_3(X41,X42,X43))
        | r2_hidden(esk6_3(X41,X42,X43),X43)
        | X43 = k2_zfmisc_1(X41,X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_10,negated_conjecture,
    ( esk9_0 != k1_xboole_0
    | k2_zfmisc_1(esk9_0,esk10_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X49,X50] :
      ( ( k4_xboole_0(k1_tarski(X49),X50) != k1_tarski(X49)
        | ~ r2_hidden(X49,X50) )
      & ( r2_hidden(X49,X50)
        | k4_xboole_0(k1_tarski(X49),X50) = k1_tarski(X49) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l33_zfmisc_1])])])).

fof(c_0_13,plain,(
    ! [X29] : k4_xboole_0(X29,k1_xboole_0) = X29 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_14,plain,
    ( r2_hidden(esk4_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(esk3_1(esk9_0),esk9_0)
    | k2_zfmisc_1(k1_xboole_0,esk10_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( k4_xboole_0(k1_tarski(X1),X2) != k1_tarski(X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( r2_hidden(X5,X6)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X5 != k4_tarski(X1,X3)
    | X6 != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,plain,
    ( r2_hidden(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk3_1(k2_zfmisc_1(k1_xboole_0,esk10_0)),k2_zfmisc_1(k1_xboole_0,esk10_0))
    | r2_hidden(esk3_1(esk9_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_11])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( esk10_0 != k1_xboole_0
    | k2_zfmisc_1(esk9_0,esk10_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_23,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_18])])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk3_1(esk9_0),esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

cnf(c_0_25,plain,
    ( r2_hidden(esk5_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk3_1(esk10_0),esk10_0)
    | k2_zfmisc_1(esk9_0,k1_xboole_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_11])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_1(esk9_0),X1),k2_zfmisc_1(esk9_0,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,plain,
    ( r2_hidden(esk5_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk3_1(k2_zfmisc_1(esk9_0,k1_xboole_0)),k2_zfmisc_1(esk9_0,k1_xboole_0))
    | r2_hidden(esk3_1(esk10_0),esk10_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_11])).

cnf(c_0_30,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_11])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_1(esk9_0),esk3_1(esk9_0)),k2_zfmisc_1(esk9_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk3_1(esk10_0),esk10_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_21])).

fof(c_0_33,plain,(
    ! [X51,X52] :
      ( ( k4_xboole_0(k1_tarski(X51),X52) != k1_xboole_0
        | r2_hidden(X51,X52) )
      & ( ~ r2_hidden(X51,X52)
        | k4_xboole_0(k1_tarski(X51),X52) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l35_zfmisc_1])])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk3_1(k2_zfmisc_1(esk9_0,esk9_0)),k2_zfmisc_1(esk9_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_1(esk9_0),esk3_1(esk10_0)),k2_zfmisc_1(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( k2_zfmisc_1(esk9_0,esk10_0) = k1_xboole_0
    | esk9_0 = k1_xboole_0
    | esk10_0 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_37,plain,
    ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk5_4(esk9_0,esk9_0,k2_zfmisc_1(esk9_0,esk9_0),esk3_1(k2_zfmisc_1(esk9_0,esk9_0))),esk9_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | esk9_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_21])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( k4_xboole_0(k1_tarski(esk5_4(esk9_0,esk9_0,k2_zfmisc_1(esk9_0,esk9_0),esk3_1(k2_zfmisc_1(esk9_0,esk9_0)))),esk9_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( esk9_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_39]),c_0_21])).

cnf(c_0_43,plain,
    ( k1_tarski(X1) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_17]),c_0_21])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_17]),c_0_43]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:26:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.19/0.40  # and selection function SelectNegativeLiterals.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.029 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(t113_zfmisc_1, conjecture, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.19/0.40  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.19/0.40  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.19/0.40  fof(l33_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)<=>~(r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 0.19/0.40  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.19/0.40  fof(l35_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 0.19/0.40  fof(c_0_6, negated_conjecture, ~(![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0))), inference(assume_negation,[status(cth)],[t113_zfmisc_1])).
% 0.19/0.40  fof(c_0_7, negated_conjecture, (((esk9_0!=k1_xboole_0|k2_zfmisc_1(esk9_0,esk10_0)!=k1_xboole_0)&(esk10_0!=k1_xboole_0|k2_zfmisc_1(esk9_0,esk10_0)!=k1_xboole_0))&(k2_zfmisc_1(esk9_0,esk10_0)=k1_xboole_0|(esk9_0=k1_xboole_0|esk10_0=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).
% 0.19/0.40  fof(c_0_8, plain, ![X26]:(X26=k1_xboole_0|r2_hidden(esk3_1(X26),X26)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.19/0.40  fof(c_0_9, plain, ![X32, X33, X34, X35, X38, X39, X40, X41, X42, X43, X45, X46]:(((((r2_hidden(esk4_4(X32,X33,X34,X35),X32)|~r2_hidden(X35,X34)|X34!=k2_zfmisc_1(X32,X33))&(r2_hidden(esk5_4(X32,X33,X34,X35),X33)|~r2_hidden(X35,X34)|X34!=k2_zfmisc_1(X32,X33)))&(X35=k4_tarski(esk4_4(X32,X33,X34,X35),esk5_4(X32,X33,X34,X35))|~r2_hidden(X35,X34)|X34!=k2_zfmisc_1(X32,X33)))&(~r2_hidden(X39,X32)|~r2_hidden(X40,X33)|X38!=k4_tarski(X39,X40)|r2_hidden(X38,X34)|X34!=k2_zfmisc_1(X32,X33)))&((~r2_hidden(esk6_3(X41,X42,X43),X43)|(~r2_hidden(X45,X41)|~r2_hidden(X46,X42)|esk6_3(X41,X42,X43)!=k4_tarski(X45,X46))|X43=k2_zfmisc_1(X41,X42))&(((r2_hidden(esk7_3(X41,X42,X43),X41)|r2_hidden(esk6_3(X41,X42,X43),X43)|X43=k2_zfmisc_1(X41,X42))&(r2_hidden(esk8_3(X41,X42,X43),X42)|r2_hidden(esk6_3(X41,X42,X43),X43)|X43=k2_zfmisc_1(X41,X42)))&(esk6_3(X41,X42,X43)=k4_tarski(esk7_3(X41,X42,X43),esk8_3(X41,X42,X43))|r2_hidden(esk6_3(X41,X42,X43),X43)|X43=k2_zfmisc_1(X41,X42))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.19/0.40  cnf(c_0_10, negated_conjecture, (esk9_0!=k1_xboole_0|k2_zfmisc_1(esk9_0,esk10_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.40  cnf(c_0_11, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.40  fof(c_0_12, plain, ![X49, X50]:((k4_xboole_0(k1_tarski(X49),X50)!=k1_tarski(X49)|~r2_hidden(X49,X50))&(r2_hidden(X49,X50)|k4_xboole_0(k1_tarski(X49),X50)=k1_tarski(X49))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l33_zfmisc_1])])])).
% 0.19/0.40  fof(c_0_13, plain, ![X29]:k4_xboole_0(X29,k1_xboole_0)=X29, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.19/0.40  cnf(c_0_14, plain, (r2_hidden(esk4_4(X1,X2,X3,X4),X1)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.40  cnf(c_0_15, negated_conjecture, (r2_hidden(esk3_1(esk9_0),esk9_0)|k2_zfmisc_1(k1_xboole_0,esk10_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.19/0.40  cnf(c_0_16, plain, (k4_xboole_0(k1_tarski(X1),X2)!=k1_tarski(X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.40  cnf(c_0_17, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.40  cnf(c_0_18, plain, (r2_hidden(X5,X6)|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X5!=k4_tarski(X1,X3)|X6!=k2_zfmisc_1(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.40  cnf(c_0_19, plain, (r2_hidden(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_14])).
% 0.19/0.40  cnf(c_0_20, negated_conjecture, (r2_hidden(esk3_1(k2_zfmisc_1(k1_xboole_0,esk10_0)),k2_zfmisc_1(k1_xboole_0,esk10_0))|r2_hidden(esk3_1(esk9_0),esk9_0)), inference(spm,[status(thm)],[c_0_15, c_0_11])).
% 0.19/0.40  cnf(c_0_21, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.40  cnf(c_0_22, negated_conjecture, (esk10_0!=k1_xboole_0|k2_zfmisc_1(esk9_0,esk10_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.40  cnf(c_0_23, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))|~r2_hidden(X2,X4)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_18])])).
% 0.19/0.40  cnf(c_0_24, negated_conjecture, (r2_hidden(esk3_1(esk9_0),esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])).
% 0.19/0.40  cnf(c_0_25, plain, (r2_hidden(esk5_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.40  cnf(c_0_26, negated_conjecture, (r2_hidden(esk3_1(esk10_0),esk10_0)|k2_zfmisc_1(esk9_0,k1_xboole_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_22, c_0_11])).
% 0.19/0.40  cnf(c_0_27, negated_conjecture, (r2_hidden(k4_tarski(esk3_1(esk9_0),X1),k2_zfmisc_1(esk9_0,X2))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.40  cnf(c_0_28, plain, (r2_hidden(esk5_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_25])).
% 0.19/0.40  cnf(c_0_29, negated_conjecture, (r2_hidden(esk3_1(k2_zfmisc_1(esk9_0,k1_xboole_0)),k2_zfmisc_1(esk9_0,k1_xboole_0))|r2_hidden(esk3_1(esk10_0),esk10_0)), inference(spm,[status(thm)],[c_0_26, c_0_11])).
% 0.19/0.40  cnf(c_0_30, plain, (r2_hidden(esk3_1(X1),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_21, c_0_11])).
% 0.19/0.40  cnf(c_0_31, negated_conjecture, (r2_hidden(k4_tarski(esk3_1(esk9_0),esk3_1(esk9_0)),k2_zfmisc_1(esk9_0,esk9_0))), inference(spm,[status(thm)],[c_0_27, c_0_24])).
% 0.19/0.40  cnf(c_0_32, negated_conjecture, (r2_hidden(esk3_1(esk10_0),esk10_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_21])).
% 0.19/0.40  fof(c_0_33, plain, ![X51, X52]:((k4_xboole_0(k1_tarski(X51),X52)!=k1_xboole_0|r2_hidden(X51,X52))&(~r2_hidden(X51,X52)|k4_xboole_0(k1_tarski(X51),X52)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l35_zfmisc_1])])).
% 0.19/0.40  cnf(c_0_34, negated_conjecture, (r2_hidden(esk3_1(k2_zfmisc_1(esk9_0,esk9_0)),k2_zfmisc_1(esk9_0,esk9_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.40  cnf(c_0_35, negated_conjecture, (r2_hidden(k4_tarski(esk3_1(esk9_0),esk3_1(esk10_0)),k2_zfmisc_1(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_27, c_0_32])).
% 0.19/0.40  cnf(c_0_36, negated_conjecture, (k2_zfmisc_1(esk9_0,esk10_0)=k1_xboole_0|esk9_0=k1_xboole_0|esk10_0=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.40  cnf(c_0_37, plain, (k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.40  cnf(c_0_38, negated_conjecture, (r2_hidden(esk5_4(esk9_0,esk9_0,k2_zfmisc_1(esk9_0,esk9_0),esk3_1(k2_zfmisc_1(esk9_0,esk9_0))),esk9_0)), inference(spm,[status(thm)],[c_0_28, c_0_34])).
% 0.19/0.40  cnf(c_0_39, negated_conjecture, (esk10_0=k1_xboole_0|esk9_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_21])).
% 0.19/0.40  cnf(c_0_40, plain, (r2_hidden(X1,X2)|k4_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.40  cnf(c_0_41, negated_conjecture, (k4_xboole_0(k1_tarski(esk5_4(esk9_0,esk9_0,k2_zfmisc_1(esk9_0,esk9_0),esk3_1(k2_zfmisc_1(esk9_0,esk9_0)))),esk9_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.40  cnf(c_0_42, negated_conjecture, (esk9_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_39]), c_0_21])).
% 0.19/0.40  cnf(c_0_43, plain, (k1_tarski(X1)!=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_17]), c_0_21])).
% 0.19/0.40  cnf(c_0_44, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_17]), c_0_43]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 45
% 0.19/0.40  # Proof object clause steps            : 32
% 0.19/0.40  # Proof object formula steps           : 13
% 0.19/0.40  # Proof object conjectures             : 21
% 0.19/0.40  # Proof object clause conjectures      : 18
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 11
% 0.19/0.40  # Proof object initial formulas used   : 6
% 0.19/0.40  # Proof object generating inferences   : 17
% 0.19/0.40  # Proof object simplifying inferences  : 18
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 11
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 32
% 0.19/0.40  # Removed in clause preprocessing      : 1
% 0.19/0.40  # Initial clauses in saturation        : 31
% 0.19/0.40  # Processed clauses                    : 228
% 0.19/0.40  # ...of these trivial                  : 4
% 0.19/0.40  # ...subsumed                          : 77
% 0.19/0.40  # ...remaining for further processing  : 147
% 0.19/0.40  # Other redundant clauses eliminated   : 22
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 1
% 0.19/0.40  # Backward-rewritten                   : 44
% 0.19/0.40  # Generated clauses                    : 1586
% 0.19/0.40  # ...of the previous two non-trivial   : 1294
% 0.19/0.40  # Contextual simplify-reflections      : 0
% 0.19/0.40  # Paramodulations                      : 1565
% 0.19/0.40  # Factorizations                       : 0
% 0.19/0.40  # Equation resolutions                 : 22
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 61
% 0.19/0.40  #    Positive orientable unit clauses  : 19
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 2
% 0.19/0.40  #    Non-unit-clauses                  : 40
% 0.19/0.40  # Current number of unprocessed clauses: 1124
% 0.19/0.40  # ...number of literals in the above   : 3228
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 77
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 840
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 503
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 30
% 0.19/0.40  # Unit Clause-clause subsumption calls : 248
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 11
% 0.19/0.40  # BW rewrite match successes           : 4
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 20970
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.049 s
% 0.19/0.40  # System time              : 0.008 s
% 0.19/0.40  # Total time               : 0.057 s
% 0.19/0.40  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
