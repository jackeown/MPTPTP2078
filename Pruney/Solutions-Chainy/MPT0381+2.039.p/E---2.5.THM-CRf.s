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
% DateTime   : Thu Dec  3 10:46:58 EST 2020

% Result     : Theorem 0.17s
% Output     : CNFRefutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 250 expanded)
%              Number of clauses        :   23 ( 110 expanded)
%              Number of leaves         :    7 (  61 expanded)
%              Depth                    :   11
%              Number of atoms          :   99 ( 706 expanded)
%              Number of equality atoms :    5 (  30 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t63_subset_1,conjecture,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(t55_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,X1)
     => ( X1 != k1_xboole_0
       => m1_subset_1(k1_tarski(X2),k1_zfmisc_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r2_hidden(X1,X2)
       => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    inference(assume_negation,[status(cth)],[t63_subset_1])).

fof(c_0_8,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0)
    & ~ m1_subset_1(k1_tarski(esk1_0),k1_zfmisc_1(esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_9,plain,(
    ! [X15,X16] :
      ( ~ m1_subset_1(X16,X15)
      | X15 = k1_xboole_0
      | m1_subset_1(k1_tarski(X16),k1_zfmisc_1(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_subset_1])])).

fof(c_0_10,plain,(
    ! [X9,X10] :
      ( ( ~ m1_subset_1(X10,X9)
        | r2_hidden(X10,X9)
        | v1_xboole_0(X9) )
      & ( ~ r2_hidden(X10,X9)
        | m1_subset_1(X10,X9)
        | v1_xboole_0(X9) )
      & ( ~ m1_subset_1(X10,X9)
        | v1_xboole_0(X10)
        | ~ v1_xboole_0(X9) )
      & ( ~ v1_xboole_0(X10)
        | m1_subset_1(X10,X9)
        | ~ v1_xboole_0(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_11,plain,(
    ! [X7,X8] :
      ( ~ r2_hidden(X7,X8)
      | ~ v1_xboole_0(X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_12,negated_conjecture,
    ( ~ m1_subset_1(k1_tarski(esk1_0),k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( X2 = k1_xboole_0
    | m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | ~ m1_subset_1(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_19,plain,(
    ! [X14] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X14)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_20,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_16])])).

fof(c_0_22,plain,(
    ! [X11,X12,X13] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | ~ r2_hidden(X13,X12)
      | r2_hidden(X13,X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_24,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_26,negated_conjecture,
    ( ~ v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( v1_xboole_0(k1_zfmisc_1(X1))
    | r2_hidden(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_24]),c_0_26])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X3,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_27,c_0_18])).

cnf(c_0_31,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_32,plain,(
    ! [X4,X5,X6] :
      ( ( ~ r2_hidden(X4,X5)
        | ~ r2_hidden(X4,X6)
        | ~ r2_hidden(X4,k5_xboole_0(X5,X6)) )
      & ( r2_hidden(X4,X5)
        | r2_hidden(X4,X6)
        | ~ r2_hidden(X4,k5_xboole_0(X5,X6)) )
      & ( ~ r2_hidden(X4,X5)
        | r2_hidden(X4,X6)
        | r2_hidden(X4,k5_xboole_0(X5,X6)) )
      & ( ~ r2_hidden(X4,X6)
        | r2_hidden(X4,X5)
        | r2_hidden(X4,k5_xboole_0(X5,X6)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk1_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_16,c_0_21])).

cnf(c_0_35,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_36]),c_0_36])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.31  % Computer   : n025.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 19:14:35 EST 2020
% 0.17/0.31  % CPUTime    : 
% 0.17/0.32  # Version: 2.5pre002
% 0.17/0.32  # No SInE strategy applied
% 0.17/0.32  # Trying AutoSched0 for 299 seconds
% 0.17/0.34  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.17/0.34  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.17/0.34  #
% 0.17/0.34  # Preprocessing time       : 0.026 s
% 0.17/0.34  
% 0.17/0.34  # Proof found!
% 0.17/0.34  # SZS status Theorem
% 0.17/0.34  # SZS output start CNFRefutation
% 0.17/0.34  fof(t63_subset_1, conjecture, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 0.17/0.34  fof(t55_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,X1)=>(X1!=k1_xboole_0=>m1_subset_1(k1_tarski(X2),k1_zfmisc_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_subset_1)).
% 0.17/0.34  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.17/0.34  fof(t7_boole, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_boole)).
% 0.17/0.34  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.17/0.34  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.17/0.34  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 0.17/0.34  fof(c_0_7, negated_conjecture, ~(![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)))), inference(assume_negation,[status(cth)],[t63_subset_1])).
% 0.17/0.34  fof(c_0_8, negated_conjecture, (r2_hidden(esk1_0,esk2_0)&~m1_subset_1(k1_tarski(esk1_0),k1_zfmisc_1(esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.17/0.34  fof(c_0_9, plain, ![X15, X16]:(~m1_subset_1(X16,X15)|(X15=k1_xboole_0|m1_subset_1(k1_tarski(X16),k1_zfmisc_1(X15)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_subset_1])])).
% 0.17/0.34  fof(c_0_10, plain, ![X9, X10]:(((~m1_subset_1(X10,X9)|r2_hidden(X10,X9)|v1_xboole_0(X9))&(~r2_hidden(X10,X9)|m1_subset_1(X10,X9)|v1_xboole_0(X9)))&((~m1_subset_1(X10,X9)|v1_xboole_0(X10)|~v1_xboole_0(X9))&(~v1_xboole_0(X10)|m1_subset_1(X10,X9)|~v1_xboole_0(X9)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.17/0.34  fof(c_0_11, plain, ![X7, X8]:(~r2_hidden(X7,X8)|~v1_xboole_0(X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).
% 0.17/0.34  cnf(c_0_12, negated_conjecture, (~m1_subset_1(k1_tarski(esk1_0),k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.17/0.34  cnf(c_0_13, plain, (X2=k1_xboole_0|m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.17/0.34  cnf(c_0_14, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.17/0.34  cnf(c_0_15, plain, (~r2_hidden(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.17/0.34  cnf(c_0_16, negated_conjecture, (r2_hidden(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.17/0.34  cnf(c_0_17, negated_conjecture, (esk2_0=k1_xboole_0|~m1_subset_1(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.17/0.34  cnf(c_0_18, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_14, c_0_15])).
% 0.17/0.34  fof(c_0_19, plain, ![X14]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X14)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.17/0.34  cnf(c_0_20, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.17/0.34  cnf(c_0_21, negated_conjecture, (esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_16])])).
% 0.17/0.34  fof(c_0_22, plain, ![X11, X12, X13]:(~m1_subset_1(X12,k1_zfmisc_1(X11))|(~r2_hidden(X13,X12)|r2_hidden(X13,X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.17/0.34  cnf(c_0_23, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.17/0.34  cnf(c_0_24, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.17/0.34  cnf(c_0_25, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.17/0.34  cnf(c_0_26, negated_conjecture, (~v1_xboole_0(k1_xboole_0)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.17/0.34  cnf(c_0_27, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.17/0.34  cnf(c_0_28, plain, (v1_xboole_0(k1_zfmisc_1(X1))|r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.17/0.34  cnf(c_0_29, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_24]), c_0_26])).
% 0.17/0.34  cnf(c_0_30, plain, (r2_hidden(X1,X2)|~r2_hidden(X3,k1_zfmisc_1(X2))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_27, c_0_18])).
% 0.17/0.34  cnf(c_0_31, plain, (r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[c_0_28, c_0_29])).
% 0.17/0.34  fof(c_0_32, plain, ![X4, X5, X6]:(((~r2_hidden(X4,X5)|~r2_hidden(X4,X6)|~r2_hidden(X4,k5_xboole_0(X5,X6)))&(r2_hidden(X4,X5)|r2_hidden(X4,X6)|~r2_hidden(X4,k5_xboole_0(X5,X6))))&((~r2_hidden(X4,X5)|r2_hidden(X4,X6)|r2_hidden(X4,k5_xboole_0(X5,X6)))&(~r2_hidden(X4,X6)|r2_hidden(X4,X5)|r2_hidden(X4,k5_xboole_0(X5,X6))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 0.17/0.34  cnf(c_0_33, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.17/0.34  cnf(c_0_34, negated_conjecture, (r2_hidden(esk1_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_16, c_0_21])).
% 0.17/0.34  cnf(c_0_35, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.17/0.34  cnf(c_0_36, negated_conjecture, (r2_hidden(esk1_0,X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.17/0.34  cnf(c_0_37, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_36]), c_0_36])]), ['proof']).
% 0.17/0.34  # SZS output end CNFRefutation
% 0.17/0.34  # Proof object total steps             : 38
% 0.17/0.34  # Proof object clause steps            : 23
% 0.17/0.34  # Proof object formula steps           : 15
% 0.17/0.34  # Proof object conjectures             : 12
% 0.17/0.34  # Proof object clause conjectures      : 9
% 0.17/0.34  # Proof object formula conjectures     : 3
% 0.17/0.34  # Proof object initial clauses used    : 10
% 0.17/0.34  # Proof object initial formulas used   : 7
% 0.17/0.34  # Proof object generating inferences   : 9
% 0.17/0.34  # Proof object simplifying inferences  : 10
% 0.17/0.34  # Training examples: 0 positive, 0 negative
% 0.17/0.34  # Parsed axioms                        : 7
% 0.17/0.34  # Removed by relevancy pruning/SinE    : 0
% 0.17/0.34  # Initial clauses                      : 14
% 0.17/0.34  # Removed in clause preprocessing      : 0
% 0.17/0.35  # Initial clauses in saturation        : 14
% 0.17/0.35  # Processed clauses                    : 33
% 0.17/0.35  # ...of these trivial                  : 0
% 0.17/0.35  # ...subsumed                          : 5
% 0.17/0.35  # ...remaining for further processing  : 28
% 0.17/0.35  # Other redundant clauses eliminated   : 0
% 0.17/0.35  # Clauses deleted for lack of memory   : 0
% 0.17/0.35  # Backward-subsumed                    : 0
% 0.17/0.35  # Backward-rewritten                   : 6
% 0.17/0.35  # Generated clauses                    : 29
% 0.17/0.35  # ...of the previous two non-trivial   : 25
% 0.17/0.35  # Contextual simplify-reflections      : 1
% 0.17/0.35  # Paramodulations                      : 28
% 0.17/0.35  # Factorizations                       : 0
% 0.17/0.35  # Equation resolutions                 : 0
% 0.17/0.35  # Propositional unsat checks           : 0
% 0.17/0.35  #    Propositional check models        : 0
% 0.17/0.35  #    Propositional check unsatisfiable : 0
% 0.17/0.35  #    Propositional clauses             : 0
% 0.17/0.35  #    Propositional clauses after purity: 0
% 0.17/0.35  #    Propositional unsat core size     : 0
% 0.17/0.35  #    Propositional preprocessing time  : 0.000
% 0.17/0.35  #    Propositional encoding time       : 0.000
% 0.17/0.35  #    Propositional solver time         : 0.000
% 0.17/0.35  #    Success case prop preproc time    : 0.000
% 0.17/0.35  #    Success case prop encoding time   : 0.000
% 0.17/0.35  #    Success case prop solver time     : 0.000
% 0.17/0.35  # Current number of processed clauses  : 21
% 0.17/0.35  #    Positive orientable unit clauses  : 4
% 0.17/0.35  #    Positive unorientable unit clauses: 0
% 0.17/0.35  #    Negative unit clauses             : 4
% 0.17/0.35  #    Non-unit-clauses                  : 13
% 0.17/0.35  # Current number of unprocessed clauses: 5
% 0.17/0.35  # ...number of literals in the above   : 15
% 0.17/0.35  # Current number of archived formulas  : 0
% 0.17/0.35  # Current number of archived clauses   : 7
% 0.17/0.35  # Clause-clause subsumption calls (NU) : 14
% 0.17/0.35  # Rec. Clause-clause subsumption calls : 12
% 0.17/0.35  # Non-unit clause-clause subsumptions  : 2
% 0.17/0.35  # Unit Clause-clause subsumption calls : 4
% 0.17/0.35  # Rewrite failures with RHS unbound    : 0
% 0.17/0.35  # BW rewrite match attempts            : 2
% 0.17/0.35  # BW rewrite match successes           : 2
% 0.17/0.35  # Condensation attempts                : 0
% 0.17/0.35  # Condensation successes               : 0
% 0.17/0.35  # Termbank termtop insertions          : 1167
% 0.17/0.35  
% 0.17/0.35  # -------------------------------------------------
% 0.17/0.35  # User time                : 0.030 s
% 0.17/0.35  # System time              : 0.001 s
% 0.17/0.35  # Total time               : 0.031 s
% 0.17/0.35  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
