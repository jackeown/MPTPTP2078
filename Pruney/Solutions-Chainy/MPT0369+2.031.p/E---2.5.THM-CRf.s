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
% DateTime   : Thu Dec  3 10:46:47 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   27 (  39 expanded)
%              Number of clauses        :   16 (  16 expanded)
%              Number of leaves         :    5 (   9 expanded)
%              Depth                    :    7
%              Number of atoms          :   92 ( 152 expanded)
%              Number of equality atoms :   19 (  31 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t50_subset_1,conjecture,(
    ! [X1] :
      ( X1 != k1_xboole_0
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => ! [X3] :
              ( m1_subset_1(X3,X1)
             => ( ~ r2_hidden(X3,X2)
               => r2_hidden(X3,k3_subset_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( X1 != k1_xboole_0
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X1))
           => ! [X3] :
                ( m1_subset_1(X3,X1)
               => ( ~ r2_hidden(X3,X2)
                 => r2_hidden(X3,k3_subset_1(X1,X2)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t50_subset_1])).

fof(c_0_6,plain,(
    ! [X15,X16] :
      ( ( ~ m1_subset_1(X16,X15)
        | r2_hidden(X16,X15)
        | v1_xboole_0(X15) )
      & ( ~ r2_hidden(X16,X15)
        | m1_subset_1(X16,X15)
        | v1_xboole_0(X15) )
      & ( ~ m1_subset_1(X16,X15)
        | v1_xboole_0(X16)
        | ~ v1_xboole_0(X15) )
      & ( ~ v1_xboole_0(X16)
        | m1_subset_1(X16,X15)
        | ~ v1_xboole_0(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_7,negated_conjecture,
    ( esk2_0 != k1_xboole_0
    & m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    & m1_subset_1(esk4_0,esk2_0)
    & ~ r2_hidden(esk4_0,esk3_0)
    & ~ r2_hidden(esk4_0,k3_subset_1(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

fof(c_0_8,plain,(
    ! [X17,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(X17))
      | k3_subset_1(X17,X18) = k4_xboole_0(X17,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_9,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k4_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_10,plain,(
    ! [X14] :
      ( ~ v1_xboole_0(X14)
      | X14 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( v1_xboole_0(esk2_0)
    | r2_hidden(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,negated_conjecture,
    ( ~ r2_hidden(esk4_0,k3_subset_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_20,negated_conjecture,
    ( k3_subset_1(esk2_0,esk3_0) = k4_xboole_0(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk4_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( ~ r2_hidden(esk4_0,k4_xboole_0(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk4_0,k4_xboole_0(esk2_0,X1))
    | r2_hidden(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( ~ r2_hidden(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:27:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.19/0.36  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 0.19/0.36  # and selection function SelectNewComplexAHP.
% 0.19/0.36  #
% 0.19/0.36  # Preprocessing time       : 0.028 s
% 0.19/0.36  
% 0.19/0.36  # Proof found!
% 0.19/0.36  # SZS status Theorem
% 0.19/0.36  # SZS output start CNFRefutation
% 0.19/0.36  fof(t50_subset_1, conjecture, ![X1]:(X1!=k1_xboole_0=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,X1)=>(~(r2_hidden(X3,X2))=>r2_hidden(X3,k3_subset_1(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_subset_1)).
% 0.19/0.36  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.19/0.36  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.19/0.36  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.19/0.36  fof(t6_boole, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_boole)).
% 0.19/0.36  fof(c_0_5, negated_conjecture, ~(![X1]:(X1!=k1_xboole_0=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,X1)=>(~(r2_hidden(X3,X2))=>r2_hidden(X3,k3_subset_1(X1,X2))))))), inference(assume_negation,[status(cth)],[t50_subset_1])).
% 0.19/0.36  fof(c_0_6, plain, ![X15, X16]:(((~m1_subset_1(X16,X15)|r2_hidden(X16,X15)|v1_xboole_0(X15))&(~r2_hidden(X16,X15)|m1_subset_1(X16,X15)|v1_xboole_0(X15)))&((~m1_subset_1(X16,X15)|v1_xboole_0(X16)|~v1_xboole_0(X15))&(~v1_xboole_0(X16)|m1_subset_1(X16,X15)|~v1_xboole_0(X15)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.19/0.36  fof(c_0_7, negated_conjecture, (esk2_0!=k1_xboole_0&(m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))&(m1_subset_1(esk4_0,esk2_0)&(~r2_hidden(esk4_0,esk3_0)&~r2_hidden(esk4_0,k3_subset_1(esk2_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).
% 0.19/0.36  fof(c_0_8, plain, ![X17, X18]:(~m1_subset_1(X18,k1_zfmisc_1(X17))|k3_subset_1(X17,X18)=k4_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.19/0.36  fof(c_0_9, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6))&(~r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k4_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k4_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.19/0.36  fof(c_0_10, plain, ![X14]:(~v1_xboole_0(X14)|X14=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).
% 0.19/0.36  cnf(c_0_11, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.36  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.36  cnf(c_0_13, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.36  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.36  cnf(c_0_15, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.36  cnf(c_0_16, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.36  cnf(c_0_17, negated_conjecture, (v1_xboole_0(esk2_0)|r2_hidden(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.19/0.36  cnf(c_0_18, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.36  cnf(c_0_19, negated_conjecture, (~r2_hidden(esk4_0,k3_subset_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.36  cnf(c_0_20, negated_conjecture, (k3_subset_1(esk2_0,esk3_0)=k4_xboole_0(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.36  cnf(c_0_21, plain, (r2_hidden(X1,k4_xboole_0(X2,X3))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_15])).
% 0.19/0.36  cnf(c_0_22, negated_conjecture, (r2_hidden(esk4_0,esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])).
% 0.19/0.36  cnf(c_0_23, negated_conjecture, (~r2_hidden(esk4_0,k4_xboole_0(esk2_0,esk3_0))), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.36  cnf(c_0_24, negated_conjecture, (r2_hidden(esk4_0,k4_xboole_0(esk2_0,X1))|r2_hidden(esk4_0,X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.36  cnf(c_0_25, negated_conjecture, (~r2_hidden(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.36  cnf(c_0_26, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), ['proof']).
% 0.19/0.36  # SZS output end CNFRefutation
% 0.19/0.36  # Proof object total steps             : 27
% 0.19/0.36  # Proof object clause steps            : 16
% 0.19/0.36  # Proof object formula steps           : 11
% 0.19/0.36  # Proof object conjectures             : 14
% 0.19/0.36  # Proof object clause conjectures      : 11
% 0.19/0.36  # Proof object formula conjectures     : 3
% 0.19/0.36  # Proof object initial clauses used    : 9
% 0.19/0.36  # Proof object initial formulas used   : 5
% 0.19/0.36  # Proof object generating inferences   : 6
% 0.19/0.36  # Proof object simplifying inferences  : 3
% 0.19/0.36  # Training examples: 0 positive, 0 negative
% 0.19/0.36  # Parsed axioms                        : 5
% 0.19/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.36  # Initial clauses                      : 17
% 0.19/0.36  # Removed in clause preprocessing      : 0
% 0.19/0.36  # Initial clauses in saturation        : 17
% 0.19/0.36  # Processed clauses                    : 54
% 0.19/0.36  # ...of these trivial                  : 1
% 0.19/0.36  # ...subsumed                          : 10
% 0.19/0.36  # ...remaining for further processing  : 43
% 0.19/0.36  # Other redundant clauses eliminated   : 3
% 0.19/0.36  # Clauses deleted for lack of memory   : 0
% 0.19/0.36  # Backward-subsumed                    : 0
% 0.19/0.36  # Backward-rewritten                   : 2
% 0.19/0.36  # Generated clauses                    : 102
% 0.19/0.36  # ...of the previous two non-trivial   : 78
% 0.19/0.36  # Contextual simplify-reflections      : 1
% 0.19/0.36  # Paramodulations                      : 94
% 0.19/0.36  # Factorizations                       : 2
% 0.19/0.36  # Equation resolutions                 : 6
% 0.19/0.36  # Propositional unsat checks           : 0
% 0.19/0.36  #    Propositional check models        : 0
% 0.19/0.36  #    Propositional check unsatisfiable : 0
% 0.19/0.36  #    Propositional clauses             : 0
% 0.19/0.36  #    Propositional clauses after purity: 0
% 0.19/0.36  #    Propositional unsat core size     : 0
% 0.19/0.36  #    Propositional preprocessing time  : 0.000
% 0.19/0.36  #    Propositional encoding time       : 0.000
% 0.19/0.36  #    Propositional solver time         : 0.000
% 0.19/0.36  #    Success case prop preproc time    : 0.000
% 0.19/0.36  #    Success case prop encoding time   : 0.000
% 0.19/0.36  #    Success case prop solver time     : 0.000
% 0.19/0.36  # Current number of processed clauses  : 41
% 0.19/0.36  #    Positive orientable unit clauses  : 6
% 0.19/0.36  #    Positive unorientable unit clauses: 0
% 0.19/0.36  #    Negative unit clauses             : 3
% 0.19/0.36  #    Non-unit-clauses                  : 32
% 0.19/0.36  # Current number of unprocessed clauses: 38
% 0.19/0.36  # ...number of literals in the above   : 117
% 0.19/0.36  # Current number of archived formulas  : 0
% 0.19/0.36  # Current number of archived clauses   : 2
% 0.19/0.36  # Clause-clause subsumption calls (NU) : 110
% 0.19/0.36  # Rec. Clause-clause subsumption calls : 73
% 0.19/0.36  # Non-unit clause-clause subsumptions  : 11
% 0.19/0.36  # Unit Clause-clause subsumption calls : 2
% 0.19/0.36  # Rewrite failures with RHS unbound    : 0
% 0.19/0.36  # BW rewrite match attempts            : 3
% 0.19/0.36  # BW rewrite match successes           : 2
% 0.19/0.36  # Condensation attempts                : 0
% 0.19/0.36  # Condensation successes               : 0
% 0.19/0.36  # Termbank termtop insertions          : 2029
% 0.19/0.36  
% 0.19/0.36  # -------------------------------------------------
% 0.19/0.36  # User time                : 0.031 s
% 0.19/0.36  # System time              : 0.003 s
% 0.19/0.36  # Total time               : 0.035 s
% 0.19/0.36  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
