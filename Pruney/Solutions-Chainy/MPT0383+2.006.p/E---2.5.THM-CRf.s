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
% DateTime   : Thu Dec  3 10:47:00 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 157 expanded)
%              Number of clauses        :   27 (  72 expanded)
%              Number of leaves         :    8 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  120 ( 457 expanded)
%              Number of equality atoms :   11 (  55 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t65_subset_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ~ ( r2_hidden(X4,X3)
        & r1_tarski(X3,k2_zfmisc_1(X1,X2))
        & ! [X5] :
            ( m1_subset_1(X5,X1)
           => ! [X6] :
                ( m1_subset_1(X6,X2)
               => X4 != k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_subset_1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(l139_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
        & ! [X4,X5] : k4_tarski(X4,X5) != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(c_0_8,plain,(
    ! [X11,X12,X13] :
      ( ~ r1_tarski(k2_xboole_0(X11,X12),X13)
      | r1_tarski(X11,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

fof(c_0_9,plain,(
    ! [X14,X15] :
      ( ~ r1_tarski(X14,X15)
      | k2_xboole_0(X14,X15) = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ~ ( r2_hidden(X4,X3)
          & r1_tarski(X3,k2_zfmisc_1(X1,X2))
          & ! [X5] :
              ( m1_subset_1(X5,X1)
             => ! [X6] :
                  ( m1_subset_1(X6,X2)
                 => X4 != k4_tarski(X5,X6) ) ) ) ),
    inference(assume_negation,[status(cth)],[t65_subset_1])).

cnf(c_0_11,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,negated_conjecture,(
    ! [X33,X34] :
      ( r2_hidden(esk7_0,esk6_0)
      & r1_tarski(esk6_0,k2_zfmisc_1(esk4_0,esk5_0))
      & ( ~ m1_subset_1(X33,esk4_0)
        | ~ m1_subset_1(X34,esk5_0)
        | esk7_0 != k4_tarski(X33,X34) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).

fof(c_0_14,plain,(
    ! [X21,X22] :
      ( ( ~ r1_tarski(k1_tarski(X21),X22)
        | r2_hidden(X21,X22) )
      & ( ~ r2_hidden(X21,X22)
        | r1_tarski(k1_tarski(X21),X22) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(esk6_0,k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(X1,k2_zfmisc_1(esk4_0,esk5_0))
    | ~ r1_tarski(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_19,plain,(
    ! [X16,X17,X18] :
      ( ~ r2_hidden(X16,k2_zfmisc_1(X17,X18))
      | k4_tarski(esk2_1(X16),esk3_1(X16)) = X16 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk4_0,esk5_0))
    | ~ r1_tarski(k1_tarski(X1),esk6_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_21,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k4_tarski(esk2_1(X1),esk3_1(X1)) = X1
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk4_0,esk5_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_24,plain,(
    ! [X27,X28] :
      ( ( ~ m1_subset_1(X28,X27)
        | r2_hidden(X28,X27)
        | v1_xboole_0(X27) )
      & ( ~ r2_hidden(X28,X27)
        | m1_subset_1(X28,X27)
        | v1_xboole_0(X27) )
      & ( ~ m1_subset_1(X28,X27)
        | v1_xboole_0(X28)
        | ~ v1_xboole_0(X27) )
      & ( ~ v1_xboole_0(X28)
        | m1_subset_1(X28,X27)
        | ~ v1_xboole_0(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_25,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_26,negated_conjecture,
    ( ~ m1_subset_1(X1,esk4_0)
    | ~ m1_subset_1(X2,esk5_0)
    | esk7_0 != k4_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,negated_conjecture,
    ( k4_tarski(esk2_1(X1),esk3_1(X1)) = X1
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_31,plain,(
    ! [X23,X24,X25,X26] :
      ( ( r2_hidden(X23,X25)
        | ~ r2_hidden(k4_tarski(X23,X24),k2_zfmisc_1(X25,X26)) )
      & ( r2_hidden(X24,X26)
        | ~ r2_hidden(k4_tarski(X23,X24),k2_zfmisc_1(X25,X26)) )
      & ( ~ r2_hidden(X23,X25)
        | ~ r2_hidden(X24,X26)
        | r2_hidden(k4_tarski(X23,X24),k2_zfmisc_1(X25,X26)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_32,negated_conjecture,
    ( ~ m1_subset_1(esk3_1(esk7_0),esk5_0)
    | ~ m1_subset_1(esk2_1(esk7_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27])]),c_0_28])])).

cnf(c_0_33,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( ~ m1_subset_1(esk2_1(esk7_0),esk4_0)
    | ~ r2_hidden(esk3_1(esk7_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(k4_tarski(X2,X1),esk6_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_23])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( ~ r2_hidden(esk3_1(esk7_0),esk5_0)
    | ~ r2_hidden(esk2_1(esk7_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk3_1(X1),esk5_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_27])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(k4_tarski(X1,X2),esk6_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_23])).

cnf(c_0_41,negated_conjecture,
    ( ~ r2_hidden(esk2_1(esk7_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_28])])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk2_1(X1),esk4_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_27])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_28])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:00:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.19/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.027 s
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.19/0.37  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.19/0.37  fof(t65_subset_1, conjecture, ![X1, X2, X3, X4]:~(((r2_hidden(X4,X3)&r1_tarski(X3,k2_zfmisc_1(X1,X2)))&![X5]:(m1_subset_1(X5,X1)=>![X6]:(m1_subset_1(X6,X2)=>X4!=k4_tarski(X5,X6))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_subset_1)).
% 0.19/0.37  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.19/0.37  fof(l139_zfmisc_1, axiom, ![X1, X2, X3]:~((r2_hidden(X1,k2_zfmisc_1(X2,X3))&![X4, X5]:k4_tarski(X4,X5)!=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 0.19/0.37  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.19/0.37  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.37  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.19/0.37  fof(c_0_8, plain, ![X11, X12, X13]:(~r1_tarski(k2_xboole_0(X11,X12),X13)|r1_tarski(X11,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.19/0.37  fof(c_0_9, plain, ![X14, X15]:(~r1_tarski(X14,X15)|k2_xboole_0(X14,X15)=X15), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.19/0.37  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3, X4]:~(((r2_hidden(X4,X3)&r1_tarski(X3,k2_zfmisc_1(X1,X2)))&![X5]:(m1_subset_1(X5,X1)=>![X6]:(m1_subset_1(X6,X2)=>X4!=k4_tarski(X5,X6)))))), inference(assume_negation,[status(cth)],[t65_subset_1])).
% 0.19/0.37  cnf(c_0_11, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.37  cnf(c_0_12, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  fof(c_0_13, negated_conjecture, ![X33, X34]:((r2_hidden(esk7_0,esk6_0)&r1_tarski(esk6_0,k2_zfmisc_1(esk4_0,esk5_0)))&(~m1_subset_1(X33,esk4_0)|(~m1_subset_1(X34,esk5_0)|esk7_0!=k4_tarski(X33,X34)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).
% 0.19/0.37  fof(c_0_14, plain, ![X21, X22]:((~r1_tarski(k1_tarski(X21),X22)|r2_hidden(X21,X22))&(~r2_hidden(X21,X22)|r1_tarski(k1_tarski(X21),X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.19/0.37  cnf(c_0_15, plain, (r1_tarski(X1,X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.19/0.37  cnf(c_0_16, negated_conjecture, (r1_tarski(esk6_0,k2_zfmisc_1(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_17, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  cnf(c_0_18, negated_conjecture, (r1_tarski(X1,k2_zfmisc_1(esk4_0,esk5_0))|~r1_tarski(X1,esk6_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.19/0.37  fof(c_0_19, plain, ![X16, X17, X18]:(~r2_hidden(X16,k2_zfmisc_1(X17,X18))|k4_tarski(esk2_1(X16),esk3_1(X16))=X16), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).
% 0.19/0.37  cnf(c_0_20, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(esk4_0,esk5_0))|~r1_tarski(k1_tarski(X1),esk6_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.37  cnf(c_0_21, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  cnf(c_0_22, plain, (k4_tarski(esk2_1(X1),esk3_1(X1))=X1|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.37  cnf(c_0_23, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(esk4_0,esk5_0))|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.37  fof(c_0_24, plain, ![X27, X28]:(((~m1_subset_1(X28,X27)|r2_hidden(X28,X27)|v1_xboole_0(X27))&(~r2_hidden(X28,X27)|m1_subset_1(X28,X27)|v1_xboole_0(X27)))&((~m1_subset_1(X28,X27)|v1_xboole_0(X28)|~v1_xboole_0(X27))&(~v1_xboole_0(X28)|m1_subset_1(X28,X27)|~v1_xboole_0(X27)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.19/0.37  fof(c_0_25, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.37  cnf(c_0_26, negated_conjecture, (~m1_subset_1(X1,esk4_0)|~m1_subset_1(X2,esk5_0)|esk7_0!=k4_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_27, negated_conjecture, (k4_tarski(esk2_1(X1),esk3_1(X1))=X1|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.37  cnf(c_0_28, negated_conjecture, (r2_hidden(esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_29, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.37  cnf(c_0_30, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.37  fof(c_0_31, plain, ![X23, X24, X25, X26]:(((r2_hidden(X23,X25)|~r2_hidden(k4_tarski(X23,X24),k2_zfmisc_1(X25,X26)))&(r2_hidden(X24,X26)|~r2_hidden(k4_tarski(X23,X24),k2_zfmisc_1(X25,X26))))&(~r2_hidden(X23,X25)|~r2_hidden(X24,X26)|r2_hidden(k4_tarski(X23,X24),k2_zfmisc_1(X25,X26)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.19/0.37  cnf(c_0_32, negated_conjecture, (~m1_subset_1(esk3_1(esk7_0),esk5_0)|~m1_subset_1(esk2_1(esk7_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27])]), c_0_28])])).
% 0.19/0.37  cnf(c_0_33, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.37  cnf(c_0_34, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.37  cnf(c_0_35, negated_conjecture, (~m1_subset_1(esk2_1(esk7_0),esk4_0)|~r2_hidden(esk3_1(esk7_0),esk5_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.37  cnf(c_0_36, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(k4_tarski(X2,X1),esk6_0)), inference(spm,[status(thm)],[c_0_34, c_0_23])).
% 0.19/0.37  cnf(c_0_37, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.37  cnf(c_0_38, negated_conjecture, (~r2_hidden(esk3_1(esk7_0),esk5_0)|~r2_hidden(esk2_1(esk7_0),esk4_0)), inference(spm,[status(thm)],[c_0_35, c_0_33])).
% 0.19/0.37  cnf(c_0_39, negated_conjecture, (r2_hidden(esk3_1(X1),esk5_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_36, c_0_27])).
% 0.19/0.37  cnf(c_0_40, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(k4_tarski(X1,X2),esk6_0)), inference(spm,[status(thm)],[c_0_37, c_0_23])).
% 0.19/0.37  cnf(c_0_41, negated_conjecture, (~r2_hidden(esk2_1(esk7_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_28])])).
% 0.19/0.37  cnf(c_0_42, negated_conjecture, (r2_hidden(esk2_1(X1),esk4_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_40, c_0_27])).
% 0.19/0.37  cnf(c_0_43, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_28])]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 44
% 0.19/0.37  # Proof object clause steps            : 27
% 0.19/0.37  # Proof object formula steps           : 17
% 0.19/0.37  # Proof object conjectures             : 19
% 0.19/0.37  # Proof object clause conjectures      : 16
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 12
% 0.19/0.37  # Proof object initial formulas used   : 8
% 0.19/0.37  # Proof object generating inferences   : 14
% 0.19/0.37  # Proof object simplifying inferences  : 8
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 8
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 17
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 17
% 0.19/0.37  # Processed clauses                    : 41
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 2
% 0.19/0.37  # ...remaining for further processing  : 39
% 0.19/0.37  # Other redundant clauses eliminated   : 1
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 0
% 0.19/0.37  # Generated clauses                    : 42
% 0.19/0.37  # ...of the previous two non-trivial   : 33
% 0.19/0.37  # Contextual simplify-reflections      : 1
% 0.19/0.37  # Paramodulations                      : 41
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 1
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 39
% 0.19/0.37  #    Positive orientable unit clauses  : 2
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 2
% 0.19/0.37  #    Non-unit-clauses                  : 35
% 0.19/0.37  # Current number of unprocessed clauses: 9
% 0.19/0.37  # ...number of literals in the above   : 27
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 0
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 104
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 92
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 3
% 0.19/0.37  # Unit Clause-clause subsumption calls : 28
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 0
% 0.19/0.37  # BW rewrite match successes           : 0
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 1623
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.029 s
% 0.19/0.37  # System time              : 0.003 s
% 0.19/0.37  # Total time               : 0.032 s
% 0.19/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
