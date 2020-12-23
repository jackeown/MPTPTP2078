%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:57:21 EST 2020

% Result     : Theorem 0.07s
% Output     : CNFRefutation 0.07s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 267 expanded)
%              Number of clauses        :   27 ( 123 expanded)
%              Number of leaves         :    5 (  61 expanded)
%              Depth                    :   11
%              Number of atoms          :  103 ( 948 expanded)
%              Number of equality atoms :   30 ( 287 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t23_relset_1,conjecture,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ! [X4] :
            ~ ( r2_hidden(X4,X2)
              & ! [X5] : ~ r2_hidden(k4_tarski(X5,X4),X3) )
      <=> k2_relset_1(X1,X2,X3) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(dt_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
       => ( ! [X4] :
              ~ ( r2_hidden(X4,X2)
                & ! [X5] : ~ r2_hidden(k4_tarski(X5,X4),X3) )
        <=> k2_relset_1(X1,X2,X3) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t23_relset_1])).

fof(c_0_6,plain,(
    ! [X23,X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | k2_relset_1(X23,X24,X25) = k2_relat_1(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_7,negated_conjecture,(
    ! [X30,X31] :
      ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
      & ( r2_hidden(esk7_0,esk5_0)
        | k2_relset_1(esk4_0,esk5_0,esk6_0) != esk5_0 )
      & ( ~ r2_hidden(k4_tarski(X30,esk7_0),esk6_0)
        | k2_relset_1(esk4_0,esk5_0,esk6_0) != esk5_0 )
      & ( ~ r2_hidden(X31,esk5_0)
        | r2_hidden(k4_tarski(esk8_1(X31),X31),esk6_0)
        | k2_relset_1(esk4_0,esk5_0,esk6_0) = esk5_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])])])).

fof(c_0_8,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | m1_subset_1(k2_relset_1(X20,X21,X22),k1_zfmisc_1(X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).

cnf(c_0_9,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X9,X10,X11,X13,X14,X15,X16,X18] :
      ( ( ~ r2_hidden(X11,X10)
        | r2_hidden(k4_tarski(esk1_3(X9,X10,X11),X11),X9)
        | X10 != k2_relat_1(X9) )
      & ( ~ r2_hidden(k4_tarski(X14,X13),X9)
        | r2_hidden(X13,X10)
        | X10 != k2_relat_1(X9) )
      & ( ~ r2_hidden(esk2_2(X15,X16),X16)
        | ~ r2_hidden(k4_tarski(X18,esk2_2(X15,X16)),X15)
        | X16 = k2_relat_1(X15) )
      & ( r2_hidden(esk2_2(X15,X16),X16)
        | r2_hidden(k4_tarski(esk3_2(X15,X16),esk2_2(X15,X16)),X15)
        | X16 = k2_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

fof(c_0_12,plain,(
    ! [X6,X7,X8] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | ~ r2_hidden(X8,X7)
      | r2_hidden(X8,X6) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_13,plain,
    ( m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( k2_relset_1(esk4_0,esk5_0,esk6_0) = k2_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_15,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(k2_relat_1(esk6_0),k1_zfmisc_1(esk5_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_10]),c_0_14])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk3_2(X1,X2),esk2_2(X1,X2)),X1)
    | X2 = k2_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_1(X1),X1),esk6_0)
    | k2_relset_1(esk4_0,esk5_0,esk6_0) = esk5_0
    | ~ r2_hidden(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,plain,
    ( X1 = k2_relat_1(X2)
    | r2_hidden(esk2_2(X2,X1),k2_relat_1(X2))
    | r2_hidden(esk2_2(X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,plain,
    ( X2 = k2_relat_1(X1)
    | ~ r2_hidden(esk2_2(X1,X2),X2)
    | ~ r2_hidden(k4_tarski(X3,esk2_2(X1,X2)),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,negated_conjecture,
    ( k2_relat_1(esk6_0) = esk5_0
    | r2_hidden(k4_tarski(esk8_1(X1),X1),esk6_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(rw,[status(thm)],[c_0_20,c_0_14])).

cnf(c_0_25,negated_conjecture,
    ( X1 = k2_relat_1(esk6_0)
    | r2_hidden(esk2_2(esk6_0,X1),esk5_0)
    | r2_hidden(esk2_2(esk6_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X1,esk7_0),esk6_0)
    | k2_relset_1(esk4_0,esk5_0,esk6_0) != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_27,negated_conjecture,
    ( k2_relat_1(esk6_0) = esk5_0
    | X1 = k2_relat_1(esk6_0)
    | ~ r2_hidden(esk2_2(esk6_0,X1),esk5_0)
    | ~ r2_hidden(esk2_2(esk6_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( k2_relat_1(esk6_0) = esk5_0
    | r2_hidden(esk2_2(esk6_0,esk5_0),esk5_0) ),
    inference(ef,[status(thm)],[c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk7_0,esk5_0)
    | k2_relset_1(esk4_0,esk5_0,esk6_0) != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_30,negated_conjecture,
    ( k2_relat_1(esk6_0) != esk5_0
    | ~ r2_hidden(k4_tarski(X1,esk7_0),esk6_0) ),
    inference(rw,[status(thm)],[c_0_26,c_0_14])).

cnf(c_0_31,negated_conjecture,
    ( k2_relat_1(esk6_0) = esk5_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_28])).

cnf(c_0_32,plain,
    ( r2_hidden(k4_tarski(esk1_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk7_0,esk5_0)
    | k2_relat_1(esk6_0) != esk5_0 ),
    inference(rw,[status(thm)],[c_0_29,c_0_14])).

cnf(c_0_34,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X1,esk7_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31])])).

cnf(c_0_35,plain,
    ( r2_hidden(k4_tarski(esk1_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk7_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_31])])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_31]),c_0_36])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.07  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.07/0.26  % Computer   : n011.cluster.edu
% 0.07/0.26  % Model      : x86_64 x86_64
% 0.07/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.26  % Memory     : 8042.1875MB
% 0.07/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.26  % CPULimit   : 60
% 0.07/0.26  % WCLimit    : 600
% 0.07/0.26  % DateTime   : Tue Dec  1 11:03:41 EST 2020
% 0.07/0.26  % CPUTime    : 
% 0.07/0.26  # Version: 2.5pre002
% 0.07/0.26  # No SInE strategy applied
% 0.07/0.26  # Trying AutoSched0 for 299 seconds
% 0.07/0.28  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.07/0.28  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.07/0.28  #
% 0.07/0.28  # Preprocessing time       : 0.012 s
% 0.07/0.28  
% 0.07/0.28  # Proof found!
% 0.07/0.28  # SZS status Theorem
% 0.07/0.28  # SZS output start CNFRefutation
% 0.07/0.28  fof(t23_relset_1, conjecture, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~(r2_hidden(k4_tarski(X5,X4),X3))))<=>k2_relset_1(X1,X2,X3)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_relset_1)).
% 0.07/0.28  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.07/0.28  fof(dt_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 0.07/0.28  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 0.07/0.28  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.07/0.28  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~(r2_hidden(k4_tarski(X5,X4),X3))))<=>k2_relset_1(X1,X2,X3)=X2))), inference(assume_negation,[status(cth)],[t23_relset_1])).
% 0.07/0.28  fof(c_0_6, plain, ![X23, X24, X25]:(~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))|k2_relset_1(X23,X24,X25)=k2_relat_1(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.07/0.28  fof(c_0_7, negated_conjecture, ![X30, X31]:(m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))&(((r2_hidden(esk7_0,esk5_0)|k2_relset_1(esk4_0,esk5_0,esk6_0)!=esk5_0)&(~r2_hidden(k4_tarski(X30,esk7_0),esk6_0)|k2_relset_1(esk4_0,esk5_0,esk6_0)!=esk5_0))&(~r2_hidden(X31,esk5_0)|r2_hidden(k4_tarski(esk8_1(X31),X31),esk6_0)|k2_relset_1(esk4_0,esk5_0,esk6_0)=esk5_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])])])).
% 0.07/0.28  fof(c_0_8, plain, ![X20, X21, X22]:(~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|m1_subset_1(k2_relset_1(X20,X21,X22),k1_zfmisc_1(X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).
% 0.07/0.28  cnf(c_0_9, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.07/0.28  cnf(c_0_10, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.07/0.28  fof(c_0_11, plain, ![X9, X10, X11, X13, X14, X15, X16, X18]:(((~r2_hidden(X11,X10)|r2_hidden(k4_tarski(esk1_3(X9,X10,X11),X11),X9)|X10!=k2_relat_1(X9))&(~r2_hidden(k4_tarski(X14,X13),X9)|r2_hidden(X13,X10)|X10!=k2_relat_1(X9)))&((~r2_hidden(esk2_2(X15,X16),X16)|~r2_hidden(k4_tarski(X18,esk2_2(X15,X16)),X15)|X16=k2_relat_1(X15))&(r2_hidden(esk2_2(X15,X16),X16)|r2_hidden(k4_tarski(esk3_2(X15,X16),esk2_2(X15,X16)),X15)|X16=k2_relat_1(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.07/0.28  fof(c_0_12, plain, ![X6, X7, X8]:(~m1_subset_1(X7,k1_zfmisc_1(X6))|(~r2_hidden(X8,X7)|r2_hidden(X8,X6))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.07/0.28  cnf(c_0_13, plain, (m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.07/0.28  cnf(c_0_14, negated_conjecture, (k2_relset_1(esk4_0,esk5_0,esk6_0)=k2_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.07/0.28  cnf(c_0_15, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.07/0.28  cnf(c_0_16, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.07/0.28  cnf(c_0_17, negated_conjecture, (m1_subset_1(k2_relat_1(esk6_0),k1_zfmisc_1(esk5_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_10]), c_0_14])).
% 0.07/0.28  cnf(c_0_18, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)), inference(er,[status(thm)],[c_0_15])).
% 0.07/0.28  cnf(c_0_19, plain, (r2_hidden(esk2_2(X1,X2),X2)|r2_hidden(k4_tarski(esk3_2(X1,X2),esk2_2(X1,X2)),X1)|X2=k2_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.07/0.28  cnf(c_0_20, negated_conjecture, (r2_hidden(k4_tarski(esk8_1(X1),X1),esk6_0)|k2_relset_1(esk4_0,esk5_0,esk6_0)=esk5_0|~r2_hidden(X1,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.07/0.28  cnf(c_0_21, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.07/0.28  cnf(c_0_22, plain, (X1=k2_relat_1(X2)|r2_hidden(esk2_2(X2,X1),k2_relat_1(X2))|r2_hidden(esk2_2(X2,X1),X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.07/0.28  cnf(c_0_23, plain, (X2=k2_relat_1(X1)|~r2_hidden(esk2_2(X1,X2),X2)|~r2_hidden(k4_tarski(X3,esk2_2(X1,X2)),X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.07/0.28  cnf(c_0_24, negated_conjecture, (k2_relat_1(esk6_0)=esk5_0|r2_hidden(k4_tarski(esk8_1(X1),X1),esk6_0)|~r2_hidden(X1,esk5_0)), inference(rw,[status(thm)],[c_0_20, c_0_14])).
% 0.07/0.28  cnf(c_0_25, negated_conjecture, (X1=k2_relat_1(esk6_0)|r2_hidden(esk2_2(esk6_0,X1),esk5_0)|r2_hidden(esk2_2(esk6_0,X1),X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.07/0.28  cnf(c_0_26, negated_conjecture, (~r2_hidden(k4_tarski(X1,esk7_0),esk6_0)|k2_relset_1(esk4_0,esk5_0,esk6_0)!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.07/0.28  cnf(c_0_27, negated_conjecture, (k2_relat_1(esk6_0)=esk5_0|X1=k2_relat_1(esk6_0)|~r2_hidden(esk2_2(esk6_0,X1),esk5_0)|~r2_hidden(esk2_2(esk6_0,X1),X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.07/0.28  cnf(c_0_28, negated_conjecture, (k2_relat_1(esk6_0)=esk5_0|r2_hidden(esk2_2(esk6_0,esk5_0),esk5_0)), inference(ef,[status(thm)],[c_0_25])).
% 0.07/0.28  cnf(c_0_29, negated_conjecture, (r2_hidden(esk7_0,esk5_0)|k2_relset_1(esk4_0,esk5_0,esk6_0)!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.07/0.28  cnf(c_0_30, negated_conjecture, (k2_relat_1(esk6_0)!=esk5_0|~r2_hidden(k4_tarski(X1,esk7_0),esk6_0)), inference(rw,[status(thm)],[c_0_26, c_0_14])).
% 0.07/0.28  cnf(c_0_31, negated_conjecture, (k2_relat_1(esk6_0)=esk5_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_28])).
% 0.07/0.28  cnf(c_0_32, plain, (r2_hidden(k4_tarski(esk1_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.07/0.28  cnf(c_0_33, negated_conjecture, (r2_hidden(esk7_0,esk5_0)|k2_relat_1(esk6_0)!=esk5_0), inference(rw,[status(thm)],[c_0_29, c_0_14])).
% 0.07/0.28  cnf(c_0_34, negated_conjecture, (~r2_hidden(k4_tarski(X1,esk7_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31])])).
% 0.07/0.28  cnf(c_0_35, plain, (r2_hidden(k4_tarski(esk1_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_32])).
% 0.07/0.28  cnf(c_0_36, negated_conjecture, (r2_hidden(esk7_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_31])])).
% 0.07/0.28  cnf(c_0_37, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_31]), c_0_36])]), ['proof']).
% 0.07/0.28  # SZS output end CNFRefutation
% 0.07/0.28  # Proof object total steps             : 38
% 0.07/0.28  # Proof object clause steps            : 27
% 0.07/0.28  # Proof object formula steps           : 11
% 0.07/0.28  # Proof object conjectures             : 20
% 0.07/0.28  # Proof object clause conjectures      : 17
% 0.07/0.28  # Proof object formula conjectures     : 3
% 0.07/0.28  # Proof object initial clauses used    : 11
% 0.07/0.28  # Proof object initial formulas used   : 5
% 0.07/0.28  # Proof object generating inferences   : 9
% 0.07/0.28  # Proof object simplifying inferences  : 14
% 0.07/0.28  # Training examples: 0 positive, 0 negative
% 0.07/0.28  # Parsed axioms                        : 5
% 0.07/0.28  # Removed by relevancy pruning/SinE    : 0
% 0.07/0.28  # Initial clauses                      : 11
% 0.07/0.28  # Removed in clause preprocessing      : 0
% 0.07/0.28  # Initial clauses in saturation        : 11
% 0.07/0.28  # Processed clauses                    : 37
% 0.07/0.28  # ...of these trivial                  : 0
% 0.07/0.28  # ...subsumed                          : 3
% 0.07/0.28  # ...remaining for further processing  : 34
% 0.07/0.28  # Other redundant clauses eliminated   : 2
% 0.07/0.28  # Clauses deleted for lack of memory   : 0
% 0.07/0.28  # Backward-subsumed                    : 0
% 0.07/0.28  # Backward-rewritten                   : 12
% 0.07/0.28  # Generated clauses                    : 38
% 0.07/0.28  # ...of the previous two non-trivial   : 30
% 0.07/0.28  # Contextual simplify-reflections      : 1
% 0.07/0.28  # Paramodulations                      : 28
% 0.07/0.28  # Factorizations                       : 8
% 0.07/0.28  # Equation resolutions                 : 2
% 0.07/0.28  # Propositional unsat checks           : 0
% 0.07/0.28  #    Propositional check models        : 0
% 0.07/0.28  #    Propositional check unsatisfiable : 0
% 0.07/0.28  #    Propositional clauses             : 0
% 0.07/0.28  #    Propositional clauses after purity: 0
% 0.07/0.28  #    Propositional unsat core size     : 0
% 0.07/0.28  #    Propositional preprocessing time  : 0.000
% 0.07/0.28  #    Propositional encoding time       : 0.000
% 0.07/0.28  #    Propositional solver time         : 0.000
% 0.07/0.28  #    Success case prop preproc time    : 0.000
% 0.07/0.28  #    Success case prop encoding time   : 0.000
% 0.07/0.28  #    Success case prop solver time     : 0.000
% 0.07/0.28  # Current number of processed clauses  : 20
% 0.07/0.28  #    Positive orientable unit clauses  : 5
% 0.07/0.28  #    Positive unorientable unit clauses: 0
% 0.07/0.28  #    Negative unit clauses             : 1
% 0.07/0.28  #    Non-unit-clauses                  : 14
% 0.07/0.28  # Current number of unprocessed clauses: 3
% 0.07/0.28  # ...number of literals in the above   : 10
% 0.07/0.28  # Current number of archived formulas  : 0
% 0.07/0.28  # Current number of archived clauses   : 12
% 0.07/0.28  # Clause-clause subsumption calls (NU) : 23
% 0.07/0.28  # Rec. Clause-clause subsumption calls : 18
% 0.07/0.28  # Non-unit clause-clause subsumptions  : 4
% 0.07/0.28  # Unit Clause-clause subsumption calls : 1
% 0.07/0.28  # Rewrite failures with RHS unbound    : 0
% 0.07/0.28  # BW rewrite match attempts            : 2
% 0.07/0.28  # BW rewrite match successes           : 2
% 0.07/0.28  # Condensation attempts                : 0
% 0.07/0.28  # Condensation successes               : 0
% 0.07/0.28  # Termbank termtop insertions          : 1526
% 0.07/0.28  
% 0.07/0.28  # -------------------------------------------------
% 0.07/0.28  # User time                : 0.013 s
% 0.07/0.28  # System time              : 0.001 s
% 0.07/0.28  # Total time               : 0.015 s
% 0.07/0.28  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
