%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:57:22 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 291 expanded)
%              Number of clauses        :   30 ( 135 expanded)
%              Number of leaves         :    7 (  67 expanded)
%              Depth                    :   13
%              Number of atoms          :  138 (1129 expanded)
%              Number of equality atoms :   33 ( 282 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
       => ( ! [X4] :
              ~ ( r2_hidden(X4,X2)
                & ! [X5] : ~ r2_hidden(k4_tarski(X5,X4),X3) )
        <=> k2_relset_1(X1,X2,X3) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t23_relset_1])).

fof(c_0_8,plain,(
    ! [X12,X13,X14] :
      ( ~ r2_hidden(X12,X13)
      | ~ m1_subset_1(X13,k1_zfmisc_1(X14))
      | m1_subset_1(X12,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_9,negated_conjecture,(
    ! [X36,X37] :
      ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
      & ( r2_hidden(esk7_0,esk5_0)
        | k2_relset_1(esk4_0,esk5_0,esk6_0) != esk5_0 )
      & ( ~ r2_hidden(k4_tarski(X36,esk7_0),esk6_0)
        | k2_relset_1(esk4_0,esk5_0,esk6_0) != esk5_0 )
      & ( ~ r2_hidden(X37,esk5_0)
        | r2_hidden(k4_tarski(esk8_1(X37),X37),esk6_0)
        | k2_relset_1(esk4_0,esk5_0,esk6_0) = esk5_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])])])).

fof(c_0_10,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X10,X11)
      | v1_xboole_0(X11)
      | r2_hidden(X10,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_11,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(X1,k2_zfmisc_1(esk4_0,esk5_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

fof(c_0_15,plain,(
    ! [X18,X19,X20,X22,X23,X24,X25,X27] :
      ( ( ~ r2_hidden(X20,X19)
        | r2_hidden(k4_tarski(esk1_3(X18,X19,X20),X20),X18)
        | X19 != k2_relat_1(X18) )
      & ( ~ r2_hidden(k4_tarski(X23,X22),X18)
        | r2_hidden(X22,X19)
        | X19 != k2_relat_1(X18) )
      & ( ~ r2_hidden(esk2_2(X24,X25),X25)
        | ~ r2_hidden(k4_tarski(X27,esk2_2(X24,X25)),X24)
        | X25 = k2_relat_1(X24) )
      & ( r2_hidden(esk2_2(X24,X25),X25)
        | r2_hidden(k4_tarski(esk3_2(X24,X25),esk2_2(X24,X25)),X24)
        | X25 = k2_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

fof(c_0_16,plain,(
    ! [X15,X16,X17] :
      ( ~ r2_hidden(X15,X16)
      | ~ m1_subset_1(X16,k1_zfmisc_1(X17))
      | ~ v1_xboole_0(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_17,plain,(
    ! [X6,X7,X8,X9] :
      ( ( r2_hidden(X6,X8)
        | ~ r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(X8,X9)) )
      & ( r2_hidden(X7,X9)
        | ~ r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(X8,X9)) )
      & ( ~ r2_hidden(X6,X8)
        | ~ r2_hidden(X7,X9)
        | r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(X8,X9)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_18,negated_conjecture,
    ( v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0))
    | r2_hidden(X1,k2_zfmisc_1(esk4_0,esk5_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk3_2(X1,X2),esk2_2(X1,X2)),X1)
    | X2 = k2_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X29,X30,X31] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | k2_relset_1(X29,X30,X31) = k2_relat_1(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( X1 = k2_relat_1(esk6_0)
    | v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0))
    | r2_hidden(k4_tarski(esk3_2(esk6_0,X1),esk2_2(esk6_0,X1)),k2_zfmisc_1(esk4_0,esk5_0))
    | r2_hidden(esk2_2(esk6_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( ~ v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_12])).

cnf(c_0_26,negated_conjecture,
    ( X1 = k2_relat_1(esk6_0)
    | v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0))
    | r2_hidden(esk2_2(esk6_0,X1),esk5_0)
    | r2_hidden(esk2_2(esk6_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_1(X1),X1),esk6_0)
    | k2_relset_1(esk4_0,esk5_0,esk6_0) = esk5_0
    | ~ r2_hidden(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_28,negated_conjecture,
    ( k2_relset_1(esk4_0,esk5_0,esk6_0) = k2_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_12])).

cnf(c_0_29,negated_conjecture,
    ( X1 = k2_relat_1(esk6_0)
    | r2_hidden(esk2_2(esk6_0,X1),esk5_0)
    | r2_hidden(esk2_2(esk6_0,X1),X1)
    | ~ r2_hidden(X2,esk6_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X1,esk7_0),esk6_0)
    | k2_relset_1(esk4_0,esk5_0,esk6_0) != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_31,plain,
    ( r2_hidden(k4_tarski(esk1_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_32,plain,
    ( X2 = k2_relat_1(X1)
    | ~ r2_hidden(esk2_2(X1,X2),X2)
    | ~ r2_hidden(k4_tarski(X3,esk2_2(X1,X2)),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_33,negated_conjecture,
    ( k2_relat_1(esk6_0) = esk5_0
    | r2_hidden(k4_tarski(esk8_1(X1),X1),esk6_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( X1 = k2_relat_1(esk6_0)
    | X2 = k2_relat_1(esk6_0)
    | r2_hidden(esk2_2(esk6_0,X2),esk5_0)
    | r2_hidden(esk2_2(esk6_0,X1),X1)
    | r2_hidden(esk2_2(esk6_0,X2),X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_19])).

cnf(c_0_35,negated_conjecture,
    ( k2_relat_1(esk6_0) != esk5_0
    | ~ r2_hidden(k4_tarski(X1,esk7_0),esk6_0) ),
    inference(rw,[status(thm)],[c_0_30,c_0_28])).

cnf(c_0_36,plain,
    ( r2_hidden(k4_tarski(esk1_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( k2_relat_1(esk6_0) = esk5_0
    | X1 = k2_relat_1(esk6_0)
    | ~ r2_hidden(esk2_2(esk6_0,X1),esk5_0)
    | ~ r2_hidden(esk2_2(esk6_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( k2_relat_1(esk6_0) = esk5_0
    | r2_hidden(esk2_2(esk6_0,esk5_0),esk5_0) ),
    inference(ef,[status(thm)],[c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk7_0,esk5_0)
    | k2_relset_1(esk4_0,esk5_0,esk6_0) != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_40,negated_conjecture,
    ( k2_relat_1(esk6_0) != esk5_0
    | ~ r2_hidden(esk7_0,k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( k2_relat_1(esk6_0) = esk5_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk7_0,esk5_0)
    | k2_relat_1(esk6_0) != esk5_0 ),
    inference(rw,[status(thm)],[c_0_39,c_0_28])).

cnf(c_0_43,negated_conjecture,
    ( ~ r2_hidden(esk7_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41]),c_0_41])])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_41])]),c_0_43]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:50:07 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  # Version: 2.5pre002
% 0.19/0.34  # No SInE strategy applied
% 0.19/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.19/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.028 s
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(t23_relset_1, conjecture, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~(r2_hidden(k4_tarski(X5,X4),X3))))<=>k2_relset_1(X1,X2,X3)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_relset_1)).
% 0.19/0.39  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.19/0.39  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.19/0.39  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 0.19/0.39  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.19/0.39  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.19/0.39  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.19/0.39  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~(r2_hidden(k4_tarski(X5,X4),X3))))<=>k2_relset_1(X1,X2,X3)=X2))), inference(assume_negation,[status(cth)],[t23_relset_1])).
% 0.19/0.39  fof(c_0_8, plain, ![X12, X13, X14]:(~r2_hidden(X12,X13)|~m1_subset_1(X13,k1_zfmisc_1(X14))|m1_subset_1(X12,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.19/0.39  fof(c_0_9, negated_conjecture, ![X36, X37]:(m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))&(((r2_hidden(esk7_0,esk5_0)|k2_relset_1(esk4_0,esk5_0,esk6_0)!=esk5_0)&(~r2_hidden(k4_tarski(X36,esk7_0),esk6_0)|k2_relset_1(esk4_0,esk5_0,esk6_0)!=esk5_0))&(~r2_hidden(X37,esk5_0)|r2_hidden(k4_tarski(esk8_1(X37),X37),esk6_0)|k2_relset_1(esk4_0,esk5_0,esk6_0)=esk5_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])])])).
% 0.19/0.39  fof(c_0_10, plain, ![X10, X11]:(~m1_subset_1(X10,X11)|(v1_xboole_0(X11)|r2_hidden(X10,X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.19/0.39  cnf(c_0_11, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.39  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  cnf(c_0_13, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.39  cnf(c_0_14, negated_conjecture, (m1_subset_1(X1,k2_zfmisc_1(esk4_0,esk5_0))|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.19/0.39  fof(c_0_15, plain, ![X18, X19, X20, X22, X23, X24, X25, X27]:(((~r2_hidden(X20,X19)|r2_hidden(k4_tarski(esk1_3(X18,X19,X20),X20),X18)|X19!=k2_relat_1(X18))&(~r2_hidden(k4_tarski(X23,X22),X18)|r2_hidden(X22,X19)|X19!=k2_relat_1(X18)))&((~r2_hidden(esk2_2(X24,X25),X25)|~r2_hidden(k4_tarski(X27,esk2_2(X24,X25)),X24)|X25=k2_relat_1(X24))&(r2_hidden(esk2_2(X24,X25),X25)|r2_hidden(k4_tarski(esk3_2(X24,X25),esk2_2(X24,X25)),X24)|X25=k2_relat_1(X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.19/0.39  fof(c_0_16, plain, ![X15, X16, X17]:(~r2_hidden(X15,X16)|~m1_subset_1(X16,k1_zfmisc_1(X17))|~v1_xboole_0(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.19/0.39  fof(c_0_17, plain, ![X6, X7, X8, X9]:(((r2_hidden(X6,X8)|~r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(X8,X9)))&(r2_hidden(X7,X9)|~r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(X8,X9))))&(~r2_hidden(X6,X8)|~r2_hidden(X7,X9)|r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(X8,X9)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.19/0.39  cnf(c_0_18, negated_conjecture, (v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0))|r2_hidden(X1,k2_zfmisc_1(esk4_0,esk5_0))|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.39  cnf(c_0_19, plain, (r2_hidden(esk2_2(X1,X2),X2)|r2_hidden(k4_tarski(esk3_2(X1,X2),esk2_2(X1,X2)),X1)|X2=k2_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.39  fof(c_0_20, plain, ![X29, X30, X31]:(~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|k2_relset_1(X29,X30,X31)=k2_relat_1(X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.19/0.39  cnf(c_0_21, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.39  cnf(c_0_22, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.39  cnf(c_0_23, negated_conjecture, (X1=k2_relat_1(esk6_0)|v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0))|r2_hidden(k4_tarski(esk3_2(esk6_0,X1),esk2_2(esk6_0,X1)),k2_zfmisc_1(esk4_0,esk5_0))|r2_hidden(esk2_2(esk6_0,X1),X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.19/0.39  cnf(c_0_24, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.39  cnf(c_0_25, negated_conjecture, (~v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0))|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_21, c_0_12])).
% 0.19/0.39  cnf(c_0_26, negated_conjecture, (X1=k2_relat_1(esk6_0)|v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0))|r2_hidden(esk2_2(esk6_0,X1),esk5_0)|r2_hidden(esk2_2(esk6_0,X1),X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.39  cnf(c_0_27, negated_conjecture, (r2_hidden(k4_tarski(esk8_1(X1),X1),esk6_0)|k2_relset_1(esk4_0,esk5_0,esk6_0)=esk5_0|~r2_hidden(X1,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  cnf(c_0_28, negated_conjecture, (k2_relset_1(esk4_0,esk5_0,esk6_0)=k2_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_24, c_0_12])).
% 0.19/0.39  cnf(c_0_29, negated_conjecture, (X1=k2_relat_1(esk6_0)|r2_hidden(esk2_2(esk6_0,X1),esk5_0)|r2_hidden(esk2_2(esk6_0,X1),X1)|~r2_hidden(X2,esk6_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.39  cnf(c_0_30, negated_conjecture, (~r2_hidden(k4_tarski(X1,esk7_0),esk6_0)|k2_relset_1(esk4_0,esk5_0,esk6_0)!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  cnf(c_0_31, plain, (r2_hidden(k4_tarski(esk1_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.39  cnf(c_0_32, plain, (X2=k2_relat_1(X1)|~r2_hidden(esk2_2(X1,X2),X2)|~r2_hidden(k4_tarski(X3,esk2_2(X1,X2)),X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.39  cnf(c_0_33, negated_conjecture, (k2_relat_1(esk6_0)=esk5_0|r2_hidden(k4_tarski(esk8_1(X1),X1),esk6_0)|~r2_hidden(X1,esk5_0)), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.39  cnf(c_0_34, negated_conjecture, (X1=k2_relat_1(esk6_0)|X2=k2_relat_1(esk6_0)|r2_hidden(esk2_2(esk6_0,X2),esk5_0)|r2_hidden(esk2_2(esk6_0,X1),X1)|r2_hidden(esk2_2(esk6_0,X2),X2)), inference(spm,[status(thm)],[c_0_29, c_0_19])).
% 0.19/0.39  cnf(c_0_35, negated_conjecture, (k2_relat_1(esk6_0)!=esk5_0|~r2_hidden(k4_tarski(X1,esk7_0),esk6_0)), inference(rw,[status(thm)],[c_0_30, c_0_28])).
% 0.19/0.39  cnf(c_0_36, plain, (r2_hidden(k4_tarski(esk1_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_31])).
% 0.19/0.39  cnf(c_0_37, negated_conjecture, (k2_relat_1(esk6_0)=esk5_0|X1=k2_relat_1(esk6_0)|~r2_hidden(esk2_2(esk6_0,X1),esk5_0)|~r2_hidden(esk2_2(esk6_0,X1),X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.39  cnf(c_0_38, negated_conjecture, (k2_relat_1(esk6_0)=esk5_0|r2_hidden(esk2_2(esk6_0,esk5_0),esk5_0)), inference(ef,[status(thm)],[c_0_34])).
% 0.19/0.39  cnf(c_0_39, negated_conjecture, (r2_hidden(esk7_0,esk5_0)|k2_relset_1(esk4_0,esk5_0,esk6_0)!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  cnf(c_0_40, negated_conjecture, (k2_relat_1(esk6_0)!=esk5_0|~r2_hidden(esk7_0,k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.39  cnf(c_0_41, negated_conjecture, (k2_relat_1(esk6_0)=esk5_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_38])).
% 0.19/0.39  cnf(c_0_42, negated_conjecture, (r2_hidden(esk7_0,esk5_0)|k2_relat_1(esk6_0)!=esk5_0), inference(rw,[status(thm)],[c_0_39, c_0_28])).
% 0.19/0.39  cnf(c_0_43, negated_conjecture, (~r2_hidden(esk7_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41]), c_0_41])])).
% 0.19/0.39  cnf(c_0_44, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_41])]), c_0_43]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 45
% 0.19/0.39  # Proof object clause steps            : 30
% 0.19/0.39  # Proof object formula steps           : 15
% 0.19/0.39  # Proof object conjectures             : 24
% 0.19/0.39  # Proof object clause conjectures      : 21
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 12
% 0.19/0.39  # Proof object initial formulas used   : 7
% 0.19/0.39  # Proof object generating inferences   : 12
% 0.19/0.39  # Proof object simplifying inferences  : 11
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 7
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 15
% 0.19/0.39  # Removed in clause preprocessing      : 0
% 0.19/0.39  # Initial clauses in saturation        : 15
% 0.19/0.39  # Processed clauses                    : 109
% 0.19/0.39  # ...of these trivial                  : 0
% 0.19/0.39  # ...subsumed                          : 13
% 0.19/0.39  # ...remaining for further processing  : 95
% 0.19/0.39  # Other redundant clauses eliminated   : 2
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 7
% 0.19/0.39  # Backward-rewritten                   : 47
% 0.19/0.39  # Generated clauses                    : 1007
% 0.19/0.39  # ...of the previous two non-trivial   : 1000
% 0.19/0.39  # Contextual simplify-reflections      : 1
% 0.19/0.39  # Paramodulations                      : 989
% 0.19/0.39  # Factorizations                       : 16
% 0.19/0.39  # Equation resolutions                 : 2
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 39
% 0.19/0.39  #    Positive orientable unit clauses  : 2
% 0.19/0.39  #    Positive unorientable unit clauses: 0
% 0.19/0.39  #    Negative unit clauses             : 1
% 0.19/0.39  #    Non-unit-clauses                  : 36
% 0.19/0.39  # Current number of unprocessed clauses: 904
% 0.19/0.39  # ...number of literals in the above   : 4637
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 54
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 628
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 320
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 21
% 0.19/0.39  # Unit Clause-clause subsumption calls : 2
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 2
% 0.19/0.39  # BW rewrite match successes           : 2
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 19372
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.052 s
% 0.19/0.39  # System time              : 0.006 s
% 0.19/0.39  # Total time               : 0.059 s
% 0.19/0.39  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
