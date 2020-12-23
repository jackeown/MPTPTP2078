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
% DateTime   : Thu Dec  3 10:38:25 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 109 expanded)
%              Number of clauses        :   20 (  45 expanded)
%              Number of leaves         :    8 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :   82 ( 163 expanded)
%              Number of equality atoms :   39 ( 114 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   11 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t23_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( X1 != X2
     => k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X2)) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_zfmisc_1)).

fof(t17_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X1 != X2
     => r1_xboole_0(k1_tarski(X1),k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t77_enumset1,axiom,(
    ! [X1,X2] : k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

fof(l35_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(t22_zfmisc_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k1_tarski(X1),k2_tarski(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_zfmisc_1)).

fof(l38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
    <=> ( ~ r2_hidden(X1,X3)
        & ( r2_hidden(X2,X3)
          | X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).

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

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( X1 != X2
       => k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X2)) = k1_tarski(X1) ) ),
    inference(assume_negation,[status(cth)],[t23_zfmisc_1])).

fof(c_0_9,plain,(
    ! [X42,X43] :
      ( X42 = X43
      | r1_xboole_0(k1_tarski(X42),k1_tarski(X43)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_zfmisc_1])])).

fof(c_0_10,plain,(
    ! [X34] : k2_tarski(X34,X34) = k1_tarski(X34) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_11,plain,(
    ! [X35,X36] : k2_enumset1(X35,X35,X35,X36) = k2_tarski(X35,X36) ),
    inference(variable_rename,[status(thm)],[t77_enumset1])).

fof(c_0_12,plain,(
    ! [X37,X38] :
      ( ( k4_xboole_0(k1_tarski(X37),X38) != k1_xboole_0
        | r2_hidden(X37,X38) )
      & ( ~ r2_hidden(X37,X38)
        | k4_xboole_0(k1_tarski(X37),X38) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l35_zfmisc_1])])).

fof(c_0_13,plain,(
    ! [X46,X47] : k4_xboole_0(k1_tarski(X46),k2_tarski(X46,X47)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t22_zfmisc_1])).

fof(c_0_14,negated_conjecture,
    ( esk4_0 != esk5_0
    & k4_xboole_0(k2_tarski(esk4_0,esk5_0),k1_tarski(esk5_0)) != k1_tarski(esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_15,plain,
    ( X1 = X2
    | r1_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_18,plain,(
    ! [X39,X40,X41] :
      ( ( ~ r2_hidden(X39,X41)
        | k4_xboole_0(k2_tarski(X39,X40),X41) != k1_tarski(X39) )
      & ( r2_hidden(X40,X41)
        | X39 = X40
        | k4_xboole_0(k2_tarski(X39,X40),X41) != k1_tarski(X39) )
      & ( ~ r2_hidden(X40,X41)
        | r2_hidden(X39,X41)
        | k4_xboole_0(k2_tarski(X39,X40),X41) = k1_tarski(X39) )
      & ( X39 != X40
        | r2_hidden(X39,X41)
        | k4_xboole_0(k2_tarski(X39,X40),X41) = k1_tarski(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l38_zfmisc_1])])])])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k4_xboole_0(k1_tarski(X1),k2_tarski(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_21,plain,(
    ! [X5,X6,X8,X9,X10] :
      ( ( r2_hidden(esk1_2(X5,X6),X5)
        | r1_xboole_0(X5,X6) )
      & ( r2_hidden(esk1_2(X5,X6),X6)
        | r1_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | ~ r1_xboole_0(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_22,negated_conjecture,
    ( esk4_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( X1 = X2
    | r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_16]),c_0_17]),c_0_17])).

cnf(c_0_24,plain,
    ( r2_hidden(X3,X2)
    | k4_xboole_0(k2_tarski(X3,X1),X2) = k1_tarski(X3)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(k2_enumset1(X1,X1,X1,X1),X2) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_16]),c_0_17])).

cnf(c_0_26,plain,
    ( k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_16]),c_0_17]),c_0_17])).

cnf(c_0_27,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( r1_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23])])).

cnf(c_0_29,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk4_0,esk5_0),k1_tarski(esk5_0)) != k1_tarski(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_30,plain,
    ( k4_xboole_0(k2_enumset1(X3,X3,X3,X1),X2) = k2_enumset1(X3,X3,X3,X3)
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_16]),c_0_17]),c_0_17])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( ~ r2_hidden(X1,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))
    | ~ r2_hidden(X1,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( k4_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) != k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_16]),c_0_16]),c_0_17]),c_0_17]),c_0_17])).

cnf(c_0_34,plain,
    ( k4_xboole_0(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X2,X2,X2,X3)) = k2_enumset1(X1,X1,X1,X1)
    | r2_hidden(X1,k2_enumset1(X2,X2,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( ~ r2_hidden(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:00:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 1.89/2.06  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 1.89/2.06  # and selection function SelectNegativeLiterals.
% 1.89/2.06  #
% 1.89/2.06  # Preprocessing time       : 0.028 s
% 1.89/2.06  # Presaturation interreduction done
% 1.89/2.06  
% 1.89/2.06  # Proof found!
% 1.89/2.06  # SZS status Theorem
% 1.89/2.06  # SZS output start CNFRefutation
% 1.89/2.06  fof(t23_zfmisc_1, conjecture, ![X1, X2]:(X1!=X2=>k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X2))=k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_zfmisc_1)).
% 1.89/2.06  fof(t17_zfmisc_1, axiom, ![X1, X2]:(X1!=X2=>r1_xboole_0(k1_tarski(X1),k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 1.89/2.06  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.89/2.06  fof(t77_enumset1, axiom, ![X1, X2]:k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_enumset1)).
% 1.89/2.06  fof(l35_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 1.89/2.06  fof(t22_zfmisc_1, axiom, ![X1, X2]:k4_xboole_0(k1_tarski(X1),k2_tarski(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_zfmisc_1)).
% 1.89/2.06  fof(l38_zfmisc_1, axiom, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k1_tarski(X1)<=>(~(r2_hidden(X1,X3))&(r2_hidden(X2,X3)|X1=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 1.89/2.06  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.89/2.06  fof(c_0_8, negated_conjecture, ~(![X1, X2]:(X1!=X2=>k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X2))=k1_tarski(X1))), inference(assume_negation,[status(cth)],[t23_zfmisc_1])).
% 1.89/2.06  fof(c_0_9, plain, ![X42, X43]:(X42=X43|r1_xboole_0(k1_tarski(X42),k1_tarski(X43))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_zfmisc_1])])).
% 1.89/2.06  fof(c_0_10, plain, ![X34]:k2_tarski(X34,X34)=k1_tarski(X34), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 1.89/2.06  fof(c_0_11, plain, ![X35, X36]:k2_enumset1(X35,X35,X35,X36)=k2_tarski(X35,X36), inference(variable_rename,[status(thm)],[t77_enumset1])).
% 1.89/2.06  fof(c_0_12, plain, ![X37, X38]:((k4_xboole_0(k1_tarski(X37),X38)!=k1_xboole_0|r2_hidden(X37,X38))&(~r2_hidden(X37,X38)|k4_xboole_0(k1_tarski(X37),X38)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l35_zfmisc_1])])).
% 1.89/2.06  fof(c_0_13, plain, ![X46, X47]:k4_xboole_0(k1_tarski(X46),k2_tarski(X46,X47))=k1_xboole_0, inference(variable_rename,[status(thm)],[t22_zfmisc_1])).
% 1.89/2.06  fof(c_0_14, negated_conjecture, (esk4_0!=esk5_0&k4_xboole_0(k2_tarski(esk4_0,esk5_0),k1_tarski(esk5_0))!=k1_tarski(esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 1.89/2.06  cnf(c_0_15, plain, (X1=X2|r1_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.89/2.06  cnf(c_0_16, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.89/2.06  cnf(c_0_17, plain, (k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.89/2.06  fof(c_0_18, plain, ![X39, X40, X41]:(((~r2_hidden(X39,X41)|k4_xboole_0(k2_tarski(X39,X40),X41)!=k1_tarski(X39))&(r2_hidden(X40,X41)|X39=X40|k4_xboole_0(k2_tarski(X39,X40),X41)!=k1_tarski(X39)))&((~r2_hidden(X40,X41)|r2_hidden(X39,X41)|k4_xboole_0(k2_tarski(X39,X40),X41)=k1_tarski(X39))&(X39!=X40|r2_hidden(X39,X41)|k4_xboole_0(k2_tarski(X39,X40),X41)=k1_tarski(X39)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l38_zfmisc_1])])])])).
% 1.89/2.06  cnf(c_0_19, plain, (r2_hidden(X1,X2)|k4_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.89/2.06  cnf(c_0_20, plain, (k4_xboole_0(k1_tarski(X1),k2_tarski(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.89/2.06  fof(c_0_21, plain, ![X5, X6, X8, X9, X10]:(((r2_hidden(esk1_2(X5,X6),X5)|r1_xboole_0(X5,X6))&(r2_hidden(esk1_2(X5,X6),X6)|r1_xboole_0(X5,X6)))&(~r2_hidden(X10,X8)|~r2_hidden(X10,X9)|~r1_xboole_0(X8,X9))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 1.89/2.06  cnf(c_0_22, negated_conjecture, (esk4_0!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.89/2.06  cnf(c_0_23, plain, (X1=X2|r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_16]), c_0_17]), c_0_17])).
% 1.89/2.06  cnf(c_0_24, plain, (r2_hidden(X3,X2)|k4_xboole_0(k2_tarski(X3,X1),X2)=k1_tarski(X3)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.89/2.06  cnf(c_0_25, plain, (r2_hidden(X1,X2)|k4_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_16]), c_0_17])).
% 1.89/2.06  cnf(c_0_26, plain, (k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_16]), c_0_17]), c_0_17])).
% 1.89/2.06  cnf(c_0_27, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.89/2.06  cnf(c_0_28, negated_conjecture, (r1_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23])])).
% 1.89/2.06  cnf(c_0_29, negated_conjecture, (k4_xboole_0(k2_tarski(esk4_0,esk5_0),k1_tarski(esk5_0))!=k1_tarski(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.89/2.06  cnf(c_0_30, plain, (k4_xboole_0(k2_enumset1(X3,X3,X3,X1),X2)=k2_enumset1(X3,X3,X3,X3)|r2_hidden(X3,X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_16]), c_0_17]), c_0_17])).
% 1.89/2.06  cnf(c_0_31, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X2))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 1.89/2.06  cnf(c_0_32, negated_conjecture, (~r2_hidden(X1,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))|~r2_hidden(X1,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 1.89/2.06  cnf(c_0_33, negated_conjecture, (k4_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))!=k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_16]), c_0_16]), c_0_17]), c_0_17]), c_0_17])).
% 1.89/2.06  cnf(c_0_34, plain, (k4_xboole_0(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X2,X2,X2,X3))=k2_enumset1(X1,X1,X1,X1)|r2_hidden(X1,k2_enumset1(X2,X2,X2,X3))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 1.89/2.06  cnf(c_0_35, negated_conjecture, (~r2_hidden(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_32, c_0_31])).
% 1.89/2.06  cnf(c_0_36, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), ['proof']).
% 1.89/2.06  # SZS output end CNFRefutation
% 1.89/2.06  # Proof object total steps             : 37
% 1.89/2.06  # Proof object clause steps            : 20
% 1.89/2.06  # Proof object formula steps           : 17
% 1.89/2.06  # Proof object conjectures             : 10
% 1.89/2.06  # Proof object clause conjectures      : 7
% 1.89/2.06  # Proof object formula conjectures     : 3
% 1.89/2.06  # Proof object initial clauses used    : 9
% 1.89/2.06  # Proof object initial formulas used   : 8
% 1.89/2.06  # Proof object generating inferences   : 6
% 1.89/2.06  # Proof object simplifying inferences  : 19
% 1.89/2.06  # Training examples: 0 positive, 0 negative
% 1.89/2.06  # Parsed axioms                        : 16
% 1.89/2.06  # Removed by relevancy pruning/SinE    : 0
% 1.89/2.06  # Initial clauses                      : 28
% 1.89/2.06  # Removed in clause preprocessing      : 3
% 1.89/2.06  # Initial clauses in saturation        : 25
% 1.89/2.06  # Processed clauses                    : 5297
% 1.89/2.06  # ...of these trivial                  : 203
% 1.89/2.06  # ...subsumed                          : 4259
% 1.89/2.06  # ...remaining for further processing  : 835
% 1.89/2.06  # Other redundant clauses eliminated   : 4909
% 1.89/2.06  # Clauses deleted for lack of memory   : 0
% 1.89/2.06  # Backward-subsumed                    : 29
% 1.89/2.06  # Backward-rewritten                   : 82
% 1.89/2.06  # Generated clauses                    : 283037
% 1.89/2.06  # ...of the previous two non-trivial   : 247726
% 1.89/2.06  # Contextual simplify-reflections      : 7
% 1.89/2.06  # Paramodulations                      : 278097
% 1.89/2.06  # Factorizations                       : 25
% 1.89/2.06  # Equation resolutions                 : 4916
% 1.89/2.06  # Propositional unsat checks           : 0
% 1.89/2.06  #    Propositional check models        : 0
% 1.89/2.06  #    Propositional check unsatisfiable : 0
% 1.89/2.06  #    Propositional clauses             : 0
% 1.89/2.06  #    Propositional clauses after purity: 0
% 1.89/2.06  #    Propositional unsat core size     : 0
% 1.89/2.06  #    Propositional preprocessing time  : 0.000
% 1.89/2.06  #    Propositional encoding time       : 0.000
% 1.89/2.06  #    Propositional solver time         : 0.000
% 1.89/2.06  #    Success case prop preproc time    : 0.000
% 1.89/2.06  #    Success case prop encoding time   : 0.000
% 1.89/2.06  #    Success case prop solver time     : 0.000
% 1.89/2.06  # Current number of processed clauses  : 695
% 1.89/2.06  #    Positive orientable unit clauses  : 82
% 1.89/2.06  #    Positive unorientable unit clauses: 0
% 1.89/2.06  #    Negative unit clauses             : 9
% 1.89/2.06  #    Non-unit-clauses                  : 604
% 1.89/2.06  # Current number of unprocessed clauses: 241650
% 1.89/2.06  # ...number of literals in the above   : 847037
% 1.89/2.06  # Current number of archived formulas  : 0
% 1.89/2.06  # Current number of archived clauses   : 139
% 1.89/2.06  # Clause-clause subsumption calls (NU) : 63465
% 1.89/2.06  # Rec. Clause-clause subsumption calls : 40439
% 1.89/2.06  # Non-unit clause-clause subsumptions  : 3888
% 1.89/2.06  # Unit Clause-clause subsumption calls : 1516
% 1.89/2.06  # Rewrite failures with RHS unbound    : 0
% 1.89/2.06  # BW rewrite match attempts            : 198
% 1.89/2.06  # BW rewrite match successes           : 77
% 1.89/2.06  # Condensation attempts                : 0
% 1.89/2.06  # Condensation successes               : 0
% 1.89/2.06  # Termbank termtop insertions          : 8251885
% 1.89/2.07  
% 1.89/2.07  # -------------------------------------------------
% 1.89/2.07  # User time                : 1.642 s
% 1.89/2.07  # System time              : 0.092 s
% 1.89/2.07  # Total time               : 1.734 s
% 1.89/2.07  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
