%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:57:09 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   32 (  43 expanded)
%              Number of clauses        :   19 (  19 expanded)
%              Number of leaves         :    6 (  10 expanded)
%              Depth                    :    9
%              Number of atoms          :   80 ( 122 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t17_relset_1,conjecture,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
     => ( ( r1_tarski(X1,X2)
          & r1_tarski(X3,X4) )
       => m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_relset_1)).

fof(t119_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4) )
     => r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_zfmisc_1)).

fof(t79_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] :
        ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
       => ( ( r1_tarski(X1,X2)
            & r1_tarski(X3,X4) )
         => m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) ) ) ),
    inference(assume_negation,[status(cth)],[t17_relset_1])).

fof(c_0_7,plain,(
    ! [X17,X18,X19,X20] :
      ( ~ r1_tarski(X17,X18)
      | ~ r1_tarski(X19,X20)
      | r1_tarski(k2_zfmisc_1(X17,X19),k2_zfmisc_1(X18,X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t119_zfmisc_1])])).

fof(c_0_8,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk6_0)))
    & r1_tarski(esk4_0,esk5_0)
    & r1_tarski(esk6_0,esk7_0)
    & ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk7_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_9,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( r1_tarski(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_11,plain,(
    ! [X21,X22] :
      ( ~ r1_tarski(X21,X22)
      | r1_tarski(k1_zfmisc_1(X21),k1_zfmisc_1(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).

cnf(c_0_12,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(X1,esk6_0),k2_zfmisc_1(X2,esk7_0))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_14,plain,(
    ! [X27,X28] :
      ( ( ~ m1_subset_1(X27,k1_zfmisc_1(X28))
        | r1_tarski(X27,X28) )
      & ( ~ r1_tarski(X27,X28)
        | m1_subset_1(X27,k1_zfmisc_1(X28)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_15,plain,
    ( r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk4_0,esk6_0),k2_zfmisc_1(esk5_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_17,plain,(
    ! [X10,X11,X12,X13,X14,X15] :
      ( ( ~ r2_hidden(X12,X11)
        | r1_tarski(X12,X10)
        | X11 != k1_zfmisc_1(X10) )
      & ( ~ r1_tarski(X13,X10)
        | r2_hidden(X13,X11)
        | X11 != k1_zfmisc_1(X10) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | ~ r1_tarski(esk2_2(X14,X15),X14)
        | X15 = k1_zfmisc_1(X14) )
      & ( r2_hidden(esk2_2(X14,X15),X15)
        | r1_tarski(esk2_2(X14,X15),X14)
        | X15 = k1_zfmisc_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_18,plain,(
    ! [X29,X30,X31] :
      ( ~ r2_hidden(X29,X30)
      | ~ m1_subset_1(X30,k1_zfmisc_1(X31))
      | m1_subset_1(X29,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_19,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk6_0)),k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_24,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk6_0)),k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk7_0)))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk8_0,k2_zfmisc_1(esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk7_0)))
    | ~ r2_hidden(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:57:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 1.63/1.78  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 1.63/1.78  # and selection function SelectNewComplexAHP.
% 1.63/1.78  #
% 1.63/1.78  # Preprocessing time       : 0.028 s
% 1.63/1.78  
% 1.63/1.78  # Proof found!
% 1.63/1.78  # SZS status Theorem
% 1.63/1.78  # SZS output start CNFRefutation
% 1.63/1.78  fof(t17_relset_1, conjecture, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))=>((r1_tarski(X1,X2)&r1_tarski(X3,X4))=>m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_relset_1)).
% 1.63/1.78  fof(t119_zfmisc_1, axiom, ![X1, X2, X3, X4]:((r1_tarski(X1,X2)&r1_tarski(X3,X4))=>r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_zfmisc_1)).
% 1.63/1.78  fof(t79_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 1.63/1.78  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.63/1.78  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.63/1.78  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 1.63/1.78  fof(c_0_6, negated_conjecture, ~(![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))=>((r1_tarski(X1,X2)&r1_tarski(X3,X4))=>m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))))), inference(assume_negation,[status(cth)],[t17_relset_1])).
% 1.63/1.78  fof(c_0_7, plain, ![X17, X18, X19, X20]:(~r1_tarski(X17,X18)|~r1_tarski(X19,X20)|r1_tarski(k2_zfmisc_1(X17,X19),k2_zfmisc_1(X18,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t119_zfmisc_1])])).
% 1.63/1.78  fof(c_0_8, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk6_0)))&((r1_tarski(esk4_0,esk5_0)&r1_tarski(esk6_0,esk7_0))&~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk7_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 1.63/1.78  cnf(c_0_9, plain, (r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))|~r1_tarski(X1,X2)|~r1_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 1.63/1.78  cnf(c_0_10, negated_conjecture, (r1_tarski(esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.63/1.78  fof(c_0_11, plain, ![X21, X22]:(~r1_tarski(X21,X22)|r1_tarski(k1_zfmisc_1(X21),k1_zfmisc_1(X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).
% 1.63/1.78  cnf(c_0_12, negated_conjecture, (r1_tarski(k2_zfmisc_1(X1,esk6_0),k2_zfmisc_1(X2,esk7_0))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 1.63/1.78  cnf(c_0_13, negated_conjecture, (r1_tarski(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.63/1.78  fof(c_0_14, plain, ![X27, X28]:((~m1_subset_1(X27,k1_zfmisc_1(X28))|r1_tarski(X27,X28))&(~r1_tarski(X27,X28)|m1_subset_1(X27,k1_zfmisc_1(X28)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 1.63/1.78  cnf(c_0_15, plain, (r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.63/1.78  cnf(c_0_16, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk4_0,esk6_0),k2_zfmisc_1(esk5_0,esk7_0))), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 1.63/1.78  fof(c_0_17, plain, ![X10, X11, X12, X13, X14, X15]:(((~r2_hidden(X12,X11)|r1_tarski(X12,X10)|X11!=k1_zfmisc_1(X10))&(~r1_tarski(X13,X10)|r2_hidden(X13,X11)|X11!=k1_zfmisc_1(X10)))&((~r2_hidden(esk2_2(X14,X15),X15)|~r1_tarski(esk2_2(X14,X15),X14)|X15=k1_zfmisc_1(X14))&(r2_hidden(esk2_2(X14,X15),X15)|r1_tarski(esk2_2(X14,X15),X14)|X15=k1_zfmisc_1(X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 1.63/1.78  fof(c_0_18, plain, ![X29, X30, X31]:(~r2_hidden(X29,X30)|~m1_subset_1(X30,k1_zfmisc_1(X31))|m1_subset_1(X29,X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 1.63/1.78  cnf(c_0_19, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.63/1.78  cnf(c_0_20, negated_conjecture, (r1_tarski(k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk6_0)),k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk7_0)))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 1.63/1.78  cnf(c_0_21, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.63/1.78  cnf(c_0_22, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.63/1.78  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.63/1.78  cnf(c_0_24, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.63/1.78  cnf(c_0_25, negated_conjecture, (m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk6_0)),k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk7_0))))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 1.63/1.78  cnf(c_0_26, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_21])).
% 1.63/1.78  cnf(c_0_27, negated_conjecture, (r1_tarski(esk8_0,k2_zfmisc_1(esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 1.63/1.78  cnf(c_0_28, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk7_0)))|~r2_hidden(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk6_0)))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 1.63/1.78  cnf(c_0_29, negated_conjecture, (r2_hidden(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk6_0)))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 1.63/1.78  cnf(c_0_30, negated_conjecture, (~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.63/1.78  cnf(c_0_31, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30]), ['proof']).
% 1.63/1.78  # SZS output end CNFRefutation
% 1.63/1.78  # Proof object total steps             : 32
% 1.63/1.78  # Proof object clause steps            : 19
% 1.63/1.78  # Proof object formula steps           : 13
% 1.63/1.78  # Proof object conjectures             : 15
% 1.63/1.78  # Proof object clause conjectures      : 12
% 1.63/1.78  # Proof object formula conjectures     : 3
% 1.63/1.78  # Proof object initial clauses used    : 10
% 1.63/1.78  # Proof object initial formulas used   : 6
% 1.63/1.78  # Proof object generating inferences   : 9
% 1.63/1.78  # Proof object simplifying inferences  : 1
% 1.63/1.78  # Training examples: 0 positive, 0 negative
% 1.63/1.78  # Parsed axioms                        : 9
% 1.63/1.78  # Removed by relevancy pruning/SinE    : 0
% 1.63/1.78  # Initial clauses                      : 18
% 1.63/1.78  # Removed in clause preprocessing      : 0
% 1.63/1.78  # Initial clauses in saturation        : 18
% 1.63/1.78  # Processed clauses                    : 2587
% 1.63/1.78  # ...of these trivial                  : 288
% 1.63/1.78  # ...subsumed                          : 335
% 1.63/1.78  # ...remaining for further processing  : 1964
% 1.63/1.78  # Other redundant clauses eliminated   : 0
% 1.63/1.78  # Clauses deleted for lack of memory   : 0
% 1.63/1.78  # Backward-subsumed                    : 0
% 1.63/1.78  # Backward-rewritten                   : 0
% 1.63/1.78  # Generated clauses                    : 297603
% 1.63/1.78  # ...of the previous two non-trivial   : 296929
% 1.63/1.78  # Contextual simplify-reflections      : 0
% 1.63/1.78  # Paramodulations                      : 297590
% 1.63/1.78  # Factorizations                       : 10
% 1.63/1.78  # Equation resolutions                 : 2
% 1.63/1.78  # Propositional unsat checks           : 0
% 1.63/1.78  #    Propositional check models        : 0
% 1.63/1.78  #    Propositional check unsatisfiable : 0
% 1.63/1.78  #    Propositional clauses             : 0
% 1.63/1.78  #    Propositional clauses after purity: 0
% 1.63/1.78  #    Propositional unsat core size     : 0
% 1.63/1.78  #    Propositional preprocessing time  : 0.000
% 1.63/1.78  #    Propositional encoding time       : 0.000
% 1.63/1.78  #    Propositional solver time         : 0.000
% 1.63/1.78  #    Success case prop preproc time    : 0.000
% 1.63/1.78  #    Success case prop encoding time   : 0.000
% 1.63/1.78  #    Success case prop solver time     : 0.000
% 1.63/1.78  # Current number of processed clauses  : 1963
% 1.63/1.78  #    Positive orientable unit clauses  : 968
% 1.63/1.78  #    Positive unorientable unit clauses: 0
% 1.63/1.78  #    Negative unit clauses             : 5
% 1.63/1.78  #    Non-unit-clauses                  : 990
% 1.63/1.78  # Current number of unprocessed clauses: 294360
% 1.63/1.78  # ...number of literals in the above   : 399060
% 1.63/1.78  # Current number of archived formulas  : 0
% 1.63/1.78  # Current number of archived clauses   : 1
% 1.63/1.78  # Clause-clause subsumption calls (NU) : 75383
% 1.63/1.78  # Rec. Clause-clause subsumption calls : 61237
% 1.63/1.78  # Non-unit clause-clause subsumptions  : 100
% 1.63/1.78  # Unit Clause-clause subsumption calls : 16472
% 1.63/1.78  # Rewrite failures with RHS unbound    : 0
% 1.63/1.78  # BW rewrite match attempts            : 5075
% 1.63/1.78  # BW rewrite match successes           : 0
% 1.63/1.78  # Condensation attempts                : 0
% 1.63/1.78  # Condensation successes               : 0
% 1.63/1.78  # Termbank termtop insertions          : 6078776
% 1.63/1.80  
% 1.63/1.80  # -------------------------------------------------
% 1.63/1.80  # User time                : 1.318 s
% 1.63/1.80  # System time              : 0.141 s
% 1.63/1.80  # Total time               : 1.459 s
% 1.63/1.80  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
