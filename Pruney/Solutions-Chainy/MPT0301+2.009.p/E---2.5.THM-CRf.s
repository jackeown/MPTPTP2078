%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:26 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 639 expanded)
%              Number of clauses        :   31 ( 295 expanded)
%              Number of leaves         :    6 ( 163 expanded)
%              Depth                    :   11
%              Number of atoms          :  118 (1805 expanded)
%              Number of equality atoms :   57 (1028 expanded)
%              Maximal formula depth    :   23 (   3 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(t67_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1)
    <=> ~ r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

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

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_zfmisc_1(X1,X2) = k1_xboole_0
      <=> ( X1 = k1_xboole_0
          | X2 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t113_zfmisc_1])).

fof(c_0_7,negated_conjecture,
    ( ( esk10_0 != k1_xboole_0
      | k2_zfmisc_1(esk10_0,esk11_0) != k1_xboole_0 )
    & ( esk11_0 != k1_xboole_0
      | k2_zfmisc_1(esk10_0,esk11_0) != k1_xboole_0 )
    & ( k2_zfmisc_1(esk10_0,esk11_0) = k1_xboole_0
      | esk10_0 = k1_xboole_0
      | esk11_0 = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).

fof(c_0_8,plain,(
    ! [X19] :
      ( X19 = k1_xboole_0
      | r2_hidden(esk3_1(X19),X19) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_9,plain,(
    ! [X61,X62] :
      ( ( k4_xboole_0(k1_tarski(X61),X62) != k1_tarski(X61)
        | ~ r2_hidden(X61,X62) )
      & ( r2_hidden(X61,X62)
        | k4_xboole_0(k1_tarski(X61),X62) = k1_tarski(X61) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t67_zfmisc_1])])])).

fof(c_0_10,plain,(
    ! [X37] : k2_tarski(X37,X37) = k1_tarski(X37) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_11,plain,(
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

cnf(c_0_12,negated_conjecture,
    ( esk11_0 != k1_xboole_0
    | k2_zfmisc_1(esk10_0,esk11_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k4_xboole_0(k1_tarski(X1),X2) != k1_tarski(X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
    ! [X22] : k4_xboole_0(X22,k1_xboole_0) = X22 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_17,plain,
    ( r2_hidden(esk6_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk3_1(esk11_0),esk11_0)
    | k2_zfmisc_1(esk10_0,k1_xboole_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,plain,
    ( k4_xboole_0(k2_tarski(X1,X1),X2) != k2_tarski(X1,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_15]),c_0_15])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( esk10_0 != k1_xboole_0
    | k2_zfmisc_1(esk10_0,esk11_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_22,plain,
    ( r2_hidden(X5,X6)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X5 != k4_tarski(X1,X3)
    | X6 != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_23,plain,
    ( r2_hidden(esk6_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk3_1(k2_zfmisc_1(esk10_0,k1_xboole_0)),k2_zfmisc_1(esk10_0,k1_xboole_0))
    | r2_hidden(esk3_1(esk11_0),esk11_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_13])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( r2_hidden(esk5_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk3_1(esk10_0),esk10_0)
    | k2_zfmisc_1(k1_xboole_0,esk11_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_13])).

cnf(c_0_28,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_22])])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk3_1(esk11_0),esk11_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_30,plain,
    ( r2_hidden(esk5_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk3_1(k2_zfmisc_1(k1_xboole_0,esk11_0)),k2_zfmisc_1(k1_xboole_0,esk11_0))
    | r2_hidden(esk3_1(esk10_0),esk10_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_13])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_1(esk11_0),X1),k2_zfmisc_1(esk11_0,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk3_1(esk10_0),esk10_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk3_1(esk11_0)),k2_zfmisc_1(X2,esk11_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_13])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_1(esk11_0),esk3_1(esk10_0)),k2_zfmisc_1(esk11_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_1(esk10_0),esk3_1(esk11_0)),k2_zfmisc_1(esk10_0,esk11_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( k2_zfmisc_1(esk10_0,esk11_0) = k1_xboole_0
    | esk10_0 = k1_xboole_0
    | esk11_0 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk3_1(k2_zfmisc_1(esk11_0,esk10_0)),k2_zfmisc_1(esk11_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( esk11_0 = k1_xboole_0
    | esk10_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_25])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk6_4(esk11_0,esk10_0,k2_zfmisc_1(esk11_0,esk10_0),esk3_1(k2_zfmisc_1(esk11_0,esk10_0))),esk10_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( esk10_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_40]),c_0_25])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_25]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:10:10 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
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
% 0.19/0.40  fof(t67_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)<=>~(r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 0.19/0.40  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.40  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.19/0.40  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.19/0.40  fof(c_0_6, negated_conjecture, ~(![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0))), inference(assume_negation,[status(cth)],[t113_zfmisc_1])).
% 0.19/0.40  fof(c_0_7, negated_conjecture, (((esk10_0!=k1_xboole_0|k2_zfmisc_1(esk10_0,esk11_0)!=k1_xboole_0)&(esk11_0!=k1_xboole_0|k2_zfmisc_1(esk10_0,esk11_0)!=k1_xboole_0))&(k2_zfmisc_1(esk10_0,esk11_0)=k1_xboole_0|(esk10_0=k1_xboole_0|esk11_0=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).
% 0.19/0.40  fof(c_0_8, plain, ![X19]:(X19=k1_xboole_0|r2_hidden(esk3_1(X19),X19)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.19/0.41  fof(c_0_9, plain, ![X61, X62]:((k4_xboole_0(k1_tarski(X61),X62)!=k1_tarski(X61)|~r2_hidden(X61,X62))&(r2_hidden(X61,X62)|k4_xboole_0(k1_tarski(X61),X62)=k1_tarski(X61))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t67_zfmisc_1])])])).
% 0.19/0.41  fof(c_0_10, plain, ![X37]:k2_tarski(X37,X37)=k1_tarski(X37), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.41  fof(c_0_11, plain, ![X38, X39, X40, X41, X44, X45, X46, X47, X48, X49, X51, X52]:(((((r2_hidden(esk5_4(X38,X39,X40,X41),X38)|~r2_hidden(X41,X40)|X40!=k2_zfmisc_1(X38,X39))&(r2_hidden(esk6_4(X38,X39,X40,X41),X39)|~r2_hidden(X41,X40)|X40!=k2_zfmisc_1(X38,X39)))&(X41=k4_tarski(esk5_4(X38,X39,X40,X41),esk6_4(X38,X39,X40,X41))|~r2_hidden(X41,X40)|X40!=k2_zfmisc_1(X38,X39)))&(~r2_hidden(X45,X38)|~r2_hidden(X46,X39)|X44!=k4_tarski(X45,X46)|r2_hidden(X44,X40)|X40!=k2_zfmisc_1(X38,X39)))&((~r2_hidden(esk7_3(X47,X48,X49),X49)|(~r2_hidden(X51,X47)|~r2_hidden(X52,X48)|esk7_3(X47,X48,X49)!=k4_tarski(X51,X52))|X49=k2_zfmisc_1(X47,X48))&(((r2_hidden(esk8_3(X47,X48,X49),X47)|r2_hidden(esk7_3(X47,X48,X49),X49)|X49=k2_zfmisc_1(X47,X48))&(r2_hidden(esk9_3(X47,X48,X49),X48)|r2_hidden(esk7_3(X47,X48,X49),X49)|X49=k2_zfmisc_1(X47,X48)))&(esk7_3(X47,X48,X49)=k4_tarski(esk8_3(X47,X48,X49),esk9_3(X47,X48,X49))|r2_hidden(esk7_3(X47,X48,X49),X49)|X49=k2_zfmisc_1(X47,X48))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.19/0.41  cnf(c_0_12, negated_conjecture, (esk11_0!=k1_xboole_0|k2_zfmisc_1(esk10_0,esk11_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.41  cnf(c_0_13, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.41  cnf(c_0_14, plain, (k4_xboole_0(k1_tarski(X1),X2)!=k1_tarski(X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.41  cnf(c_0_15, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.41  fof(c_0_16, plain, ![X22]:k4_xboole_0(X22,k1_xboole_0)=X22, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.19/0.41  cnf(c_0_17, plain, (r2_hidden(esk6_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.41  cnf(c_0_18, negated_conjecture, (r2_hidden(esk3_1(esk11_0),esk11_0)|k2_zfmisc_1(esk10_0,k1_xboole_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.19/0.41  cnf(c_0_19, plain, (k4_xboole_0(k2_tarski(X1,X1),X2)!=k2_tarski(X1,X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14, c_0_15]), c_0_15])).
% 0.19/0.41  cnf(c_0_20, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.41  cnf(c_0_21, negated_conjecture, (esk10_0!=k1_xboole_0|k2_zfmisc_1(esk10_0,esk11_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.41  cnf(c_0_22, plain, (r2_hidden(X5,X6)|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X5!=k4_tarski(X1,X3)|X6!=k2_zfmisc_1(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.41  cnf(c_0_23, plain, (r2_hidden(esk6_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_17])).
% 0.19/0.41  cnf(c_0_24, negated_conjecture, (r2_hidden(esk3_1(k2_zfmisc_1(esk10_0,k1_xboole_0)),k2_zfmisc_1(esk10_0,k1_xboole_0))|r2_hidden(esk3_1(esk11_0),esk11_0)), inference(spm,[status(thm)],[c_0_18, c_0_13])).
% 0.19/0.41  cnf(c_0_25, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.41  cnf(c_0_26, plain, (r2_hidden(esk5_4(X1,X2,X3,X4),X1)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.41  cnf(c_0_27, negated_conjecture, (r2_hidden(esk3_1(esk10_0),esk10_0)|k2_zfmisc_1(k1_xboole_0,esk11_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_21, c_0_13])).
% 0.19/0.41  cnf(c_0_28, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))|~r2_hidden(X2,X4)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_22])])).
% 0.19/0.41  cnf(c_0_29, negated_conjecture, (r2_hidden(esk3_1(esk11_0),esk11_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])).
% 0.19/0.41  cnf(c_0_30, plain, (r2_hidden(esk5_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_26])).
% 0.19/0.41  cnf(c_0_31, negated_conjecture, (r2_hidden(esk3_1(k2_zfmisc_1(k1_xboole_0,esk11_0)),k2_zfmisc_1(k1_xboole_0,esk11_0))|r2_hidden(esk3_1(esk10_0),esk10_0)), inference(spm,[status(thm)],[c_0_27, c_0_13])).
% 0.19/0.41  cnf(c_0_32, negated_conjecture, (r2_hidden(k4_tarski(esk3_1(esk11_0),X1),k2_zfmisc_1(esk11_0,X2))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.41  cnf(c_0_33, negated_conjecture, (r2_hidden(esk3_1(esk10_0),esk10_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_25])).
% 0.19/0.41  cnf(c_0_34, negated_conjecture, (r2_hidden(k4_tarski(X1,esk3_1(esk11_0)),k2_zfmisc_1(X2,esk11_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.41  cnf(c_0_35, plain, (r2_hidden(esk3_1(X1),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_25, c_0_13])).
% 0.19/0.41  cnf(c_0_36, negated_conjecture, (r2_hidden(k4_tarski(esk3_1(esk11_0),esk3_1(esk10_0)),k2_zfmisc_1(esk11_0,esk10_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.41  cnf(c_0_37, negated_conjecture, (r2_hidden(k4_tarski(esk3_1(esk10_0),esk3_1(esk11_0)),k2_zfmisc_1(esk10_0,esk11_0))), inference(spm,[status(thm)],[c_0_34, c_0_33])).
% 0.19/0.41  cnf(c_0_38, negated_conjecture, (k2_zfmisc_1(esk10_0,esk11_0)=k1_xboole_0|esk10_0=k1_xboole_0|esk11_0=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.41  cnf(c_0_39, negated_conjecture, (r2_hidden(esk3_1(k2_zfmisc_1(esk11_0,esk10_0)),k2_zfmisc_1(esk11_0,esk10_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.41  cnf(c_0_40, negated_conjecture, (esk11_0=k1_xboole_0|esk10_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_25])).
% 0.19/0.41  cnf(c_0_41, negated_conjecture, (r2_hidden(esk6_4(esk11_0,esk10_0,k2_zfmisc_1(esk11_0,esk10_0),esk3_1(k2_zfmisc_1(esk11_0,esk10_0))),esk10_0)), inference(spm,[status(thm)],[c_0_23, c_0_39])).
% 0.19/0.41  cnf(c_0_42, negated_conjecture, (esk10_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_40]), c_0_25])).
% 0.19/0.41  cnf(c_0_43, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_25]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 44
% 0.19/0.41  # Proof object clause steps            : 31
% 0.19/0.41  # Proof object formula steps           : 13
% 0.19/0.41  # Proof object conjectures             : 21
% 0.19/0.41  # Proof object clause conjectures      : 18
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 10
% 0.19/0.41  # Proof object initial formulas used   : 6
% 0.19/0.41  # Proof object generating inferences   : 16
% 0.19/0.41  # Proof object simplifying inferences  : 15
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 18
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 37
% 0.19/0.41  # Removed in clause preprocessing      : 3
% 0.19/0.41  # Initial clauses in saturation        : 34
% 0.19/0.41  # Processed clauses                    : 350
% 0.19/0.41  # ...of these trivial                  : 30
% 0.19/0.41  # ...subsumed                          : 123
% 0.19/0.41  # ...remaining for further processing  : 197
% 0.19/0.41  # Other redundant clauses eliminated   : 177
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 1
% 0.19/0.41  # Backward-rewritten                   : 63
% 0.19/0.41  # Generated clauses                    : 4291
% 0.19/0.41  # ...of the previous two non-trivial   : 3007
% 0.19/0.41  # Contextual simplify-reflections      : 0
% 0.19/0.41  # Paramodulations                      : 4116
% 0.19/0.41  # Factorizations                       : 0
% 0.19/0.41  # Equation resolutions                 : 177
% 0.19/0.41  # Propositional unsat checks           : 0
% 0.19/0.41  #    Propositional check models        : 0
% 0.19/0.41  #    Propositional check unsatisfiable : 0
% 0.19/0.41  #    Propositional clauses             : 0
% 0.19/0.41  #    Propositional clauses after purity: 0
% 0.19/0.41  #    Propositional unsat core size     : 0
% 0.19/0.41  #    Propositional preprocessing time  : 0.000
% 0.19/0.41  #    Propositional encoding time       : 0.000
% 0.19/0.41  #    Propositional solver time         : 0.000
% 0.19/0.41  #    Success case prop preproc time    : 0.000
% 0.19/0.41  #    Success case prop encoding time   : 0.000
% 0.19/0.41  #    Success case prop solver time     : 0.000
% 0.19/0.41  # Current number of processed clauses  : 92
% 0.19/0.41  #    Positive orientable unit clauses  : 30
% 0.19/0.41  #    Positive unorientable unit clauses: 0
% 0.19/0.41  #    Negative unit clauses             : 5
% 0.19/0.41  #    Non-unit-clauses                  : 57
% 0.19/0.41  # Current number of unprocessed clauses: 2722
% 0.19/0.41  # ...number of literals in the above   : 7016
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 101
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 604
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 549
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 82
% 0.19/0.41  # Unit Clause-clause subsumption calls : 72
% 0.19/0.41  # Rewrite failures with RHS unbound    : 0
% 0.19/0.41  # BW rewrite match attempts            : 22
% 0.19/0.41  # BW rewrite match successes           : 9
% 0.19/0.41  # Condensation attempts                : 0
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 50786
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.075 s
% 0.19/0.41  # System time              : 0.004 s
% 0.19/0.41  # Total time               : 0.079 s
% 0.19/0.41  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
