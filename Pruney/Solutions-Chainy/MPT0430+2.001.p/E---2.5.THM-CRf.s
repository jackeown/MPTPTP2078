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
% DateTime   : Thu Dec  3 10:48:04 EST 2020

% Result     : Theorem 0.08s
% Output     : CNFRefutation 0.08s
% Verified   : 
% Statistics : Number of formulae       :   35 (  69 expanded)
%              Number of clauses        :   20 (  27 expanded)
%              Number of leaves         :    7 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :   87 ( 226 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t62_setfam_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
         => ( ( v3_setfam_1(X2,X1)
              & r1_tarski(X3,X2) )
           => v3_setfam_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_setfam_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(d13_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( v3_setfam_1(X2,X1)
      <=> ~ r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_setfam_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
           => ( ( v3_setfam_1(X2,X1)
                & r1_tarski(X3,X2) )
             => v3_setfam_1(X3,X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t62_setfam_1])).

fof(c_0_8,plain,(
    ! [X14,X15] :
      ( ( ~ m1_subset_1(X14,k1_zfmisc_1(X15))
        | r1_tarski(X14,X15) )
      & ( ~ r1_tarski(X14,X15)
        | m1_subset_1(X14,k1_zfmisc_1(X15)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_9,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
    & v3_setfam_1(esk3_0,esk2_0)
    & r1_tarski(esk4_0,esk3_0)
    & ~ v3_setfam_1(esk4_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X10,X11] :
      ( ( ~ v3_setfam_1(X11,X10)
        | ~ r2_hidden(X10,X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X10))) )
      & ( r2_hidden(X10,X11)
        | v3_setfam_1(X11,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X10))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_setfam_1])])])])).

fof(c_0_11,plain,(
    ! [X16,X17,X18] :
      ( ~ r2_hidden(X16,X17)
      | ~ m1_subset_1(X17,k1_zfmisc_1(X18))
      | m1_subset_1(X16,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_12,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_15,negated_conjecture,
    ( ~ v3_setfam_1(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X2)
    | v3_setfam_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_20,plain,(
    ! [X8,X9] :
      ( ~ v1_xboole_0(X8)
      | ~ m1_subset_1(X9,k1_zfmisc_1(X8))
      | v1_xboole_0(X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_21,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

fof(c_0_23,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(X12,X13)
      | v1_xboole_0(X13)
      | r2_hidden(X12,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(X1,esk3_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( ~ v3_setfam_1(X1,X2)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_26,negated_conjecture,
    ( v3_setfam_1(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_28,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_30,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

cnf(c_0_33,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_19]),c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.08/0.26  % Computer   : n015.cluster.edu
% 0.08/0.26  % Model      : x86_64 x86_64
% 0.08/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.26  % Memory     : 8042.1875MB
% 0.08/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.26  % CPULimit   : 60
% 0.08/0.26  % WCLimit    : 600
% 0.08/0.26  % DateTime   : Tue Dec  1 10:00:08 EST 2020
% 0.08/0.26  % CPUTime    : 
% 0.08/0.26  # Version: 2.5pre002
% 0.08/0.26  # No SInE strategy applied
% 0.08/0.26  # Trying AutoSched0 for 299 seconds
% 0.08/0.27  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.08/0.27  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.08/0.27  #
% 0.08/0.27  # Preprocessing time       : 0.013 s
% 0.08/0.27  
% 0.08/0.27  # Proof found!
% 0.08/0.27  # SZS status Theorem
% 0.08/0.27  # SZS output start CNFRefutation
% 0.08/0.27  fof(t62_setfam_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>((v3_setfam_1(X2,X1)&r1_tarski(X3,X2))=>v3_setfam_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_setfam_1)).
% 0.08/0.27  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.08/0.27  fof(d13_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(v3_setfam_1(X2,X1)<=>~(r2_hidden(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_setfam_1)).
% 0.08/0.27  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.08/0.27  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.08/0.27  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.08/0.27  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.08/0.27  fof(c_0_7, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>((v3_setfam_1(X2,X1)&r1_tarski(X3,X2))=>v3_setfam_1(X3,X1))))), inference(assume_negation,[status(cth)],[t62_setfam_1])).
% 0.08/0.27  fof(c_0_8, plain, ![X14, X15]:((~m1_subset_1(X14,k1_zfmisc_1(X15))|r1_tarski(X14,X15))&(~r1_tarski(X14,X15)|m1_subset_1(X14,k1_zfmisc_1(X15)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.08/0.27  fof(c_0_9, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))&(m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))&((v3_setfam_1(esk3_0,esk2_0)&r1_tarski(esk4_0,esk3_0))&~v3_setfam_1(esk4_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.08/0.27  fof(c_0_10, plain, ![X10, X11]:((~v3_setfam_1(X11,X10)|~r2_hidden(X10,X11)|~m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X10))))&(r2_hidden(X10,X11)|v3_setfam_1(X11,X10)|~m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X10))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_setfam_1])])])])).
% 0.08/0.27  fof(c_0_11, plain, ![X16, X17, X18]:(~r2_hidden(X16,X17)|~m1_subset_1(X17,k1_zfmisc_1(X18))|m1_subset_1(X16,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.08/0.27  cnf(c_0_12, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.08/0.27  cnf(c_0_13, negated_conjecture, (r1_tarski(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.08/0.27  fof(c_0_14, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.08/0.27  cnf(c_0_15, negated_conjecture, (~v3_setfam_1(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.08/0.27  cnf(c_0_16, plain, (r2_hidden(X1,X2)|v3_setfam_1(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.08/0.27  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.08/0.27  cnf(c_0_18, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.08/0.27  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.08/0.27  fof(c_0_20, plain, ![X8, X9]:(~v1_xboole_0(X8)|(~m1_subset_1(X9,k1_zfmisc_1(X8))|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.08/0.27  cnf(c_0_21, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.08/0.27  cnf(c_0_22, negated_conjecture, (r2_hidden(esk2_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])])).
% 0.08/0.27  fof(c_0_23, plain, ![X12, X13]:(~m1_subset_1(X12,X13)|(v1_xboole_0(X13)|r2_hidden(X12,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.08/0.27  cnf(c_0_24, negated_conjecture, (m1_subset_1(X1,esk3_0)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.08/0.27  cnf(c_0_25, plain, (~v3_setfam_1(X1,X2)|~r2_hidden(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.08/0.27  cnf(c_0_26, negated_conjecture, (v3_setfam_1(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.08/0.27  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.08/0.27  cnf(c_0_28, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.08/0.27  cnf(c_0_29, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.08/0.27  cnf(c_0_30, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.08/0.27  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_24, c_0_22])).
% 0.08/0.27  cnf(c_0_32, negated_conjecture, (~r2_hidden(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])])).
% 0.08/0.27  cnf(c_0_33, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_19]), c_0_29])).
% 0.08/0.27  cnf(c_0_34, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33]), ['proof']).
% 0.08/0.27  # SZS output end CNFRefutation
% 0.08/0.27  # Proof object total steps             : 35
% 0.08/0.27  # Proof object clause steps            : 20
% 0.08/0.27  # Proof object formula steps           : 15
% 0.08/0.27  # Proof object conjectures             : 16
% 0.08/0.27  # Proof object clause conjectures      : 13
% 0.08/0.27  # Proof object formula conjectures     : 3
% 0.08/0.27  # Proof object initial clauses used    : 12
% 0.08/0.27  # Proof object initial formulas used   : 7
% 0.08/0.27  # Proof object generating inferences   : 8
% 0.08/0.27  # Proof object simplifying inferences  : 7
% 0.08/0.27  # Training examples: 0 positive, 0 negative
% 0.08/0.27  # Parsed axioms                        : 7
% 0.08/0.27  # Removed by relevancy pruning/SinE    : 0
% 0.08/0.27  # Initial clauses                      : 14
% 0.08/0.27  # Removed in clause preprocessing      : 0
% 0.08/0.27  # Initial clauses in saturation        : 14
% 0.08/0.27  # Processed clauses                    : 28
% 0.08/0.27  # ...of these trivial                  : 0
% 0.08/0.27  # ...subsumed                          : 1
% 0.08/0.27  # ...remaining for further processing  : 27
% 0.08/0.27  # Other redundant clauses eliminated   : 0
% 0.08/0.27  # Clauses deleted for lack of memory   : 0
% 0.08/0.27  # Backward-subsumed                    : 0
% 0.08/0.27  # Backward-rewritten                   : 0
% 0.08/0.27  # Generated clauses                    : 22
% 0.08/0.27  # ...of the previous two non-trivial   : 18
% 0.08/0.27  # Contextual simplify-reflections      : 0
% 0.08/0.27  # Paramodulations                      : 22
% 0.08/0.27  # Factorizations                       : 0
% 0.08/0.27  # Equation resolutions                 : 0
% 0.08/0.27  # Propositional unsat checks           : 0
% 0.08/0.27  #    Propositional check models        : 0
% 0.08/0.27  #    Propositional check unsatisfiable : 0
% 0.08/0.27  #    Propositional clauses             : 0
% 0.08/0.27  #    Propositional clauses after purity: 0
% 0.08/0.27  #    Propositional unsat core size     : 0
% 0.08/0.27  #    Propositional preprocessing time  : 0.000
% 0.08/0.27  #    Propositional encoding time       : 0.000
% 0.08/0.27  #    Propositional solver time         : 0.000
% 0.08/0.27  #    Success case prop preproc time    : 0.000
% 0.08/0.27  #    Success case prop encoding time   : 0.000
% 0.08/0.27  #    Success case prop solver time     : 0.000
% 0.08/0.27  # Current number of processed clauses  : 27
% 0.08/0.27  #    Positive orientable unit clauses  : 7
% 0.08/0.27  #    Positive unorientable unit clauses: 0
% 0.08/0.27  #    Negative unit clauses             : 5
% 0.08/0.27  #    Non-unit-clauses                  : 15
% 0.08/0.27  # Current number of unprocessed clauses: 4
% 0.08/0.27  # ...number of literals in the above   : 4
% 0.08/0.27  # Current number of archived formulas  : 0
% 0.08/0.27  # Current number of archived clauses   : 0
% 0.08/0.27  # Clause-clause subsumption calls (NU) : 8
% 0.08/0.27  # Rec. Clause-clause subsumption calls : 7
% 0.08/0.27  # Non-unit clause-clause subsumptions  : 0
% 0.08/0.27  # Unit Clause-clause subsumption calls : 8
% 0.08/0.27  # Rewrite failures with RHS unbound    : 0
% 0.08/0.27  # BW rewrite match attempts            : 0
% 0.08/0.27  # BW rewrite match successes           : 0
% 0.08/0.27  # Condensation attempts                : 0
% 0.08/0.27  # Condensation successes               : 0
% 0.08/0.27  # Termbank termtop insertions          : 1100
% 0.08/0.27  
% 0.08/0.27  # -------------------------------------------------
% 0.08/0.27  # User time                : 0.011 s
% 0.08/0.27  # System time              : 0.004 s
% 0.08/0.27  # Total time               : 0.016 s
% 0.08/0.27  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
