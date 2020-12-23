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
% DateTime   : Thu Dec  3 10:57:06 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 (  79 expanded)
%              Number of clauses        :   26 (  34 expanded)
%              Number of leaves         :    9 (  20 expanded)
%              Depth                    :   10
%              Number of atoms          :   96 ( 181 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t13_relset_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
     => ( r1_tarski(k1_relat_1(X4),X2)
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t194_relat_1,axiom,(
    ! [X1,X2] : r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t194_relat_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(t118_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => ( r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
        & r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(t21_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
       => ( r1_tarski(k1_relat_1(X4),X2)
         => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ) ),
    inference(assume_negation,[status(cth)],[t13_relset_1])).

fof(c_0_10,plain,(
    ! [X13,X14] :
      ( ( ~ m1_subset_1(X13,k1_zfmisc_1(X14))
        | r1_tarski(X13,X14) )
      & ( ~ r1_tarski(X13,X14)
        | m1_subset_1(X13,k1_zfmisc_1(X14)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_11,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))
    & r1_tarski(k1_relat_1(esk4_0),esk2_0)
    & ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_12,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(X15))
      | v1_relat_1(X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_13,plain,(
    ! [X17,X18] : v1_relat_1(k2_zfmisc_1(X17,X18)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_14,plain,(
    ! [X7,X8,X9] :
      ( ~ r1_tarski(X7,X8)
      | ~ r1_tarski(X8,X9)
      | r1_tarski(X7,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_15,plain,(
    ! [X19,X20] : r1_tarski(k2_relat_1(k2_zfmisc_1(X19,X20)),X20) ),
    inference(variable_rename,[status(thm)],[t194_relat_1])).

fof(c_0_16,plain,(
    ! [X22,X23] :
      ( ( r1_tarski(k1_relat_1(X22),k1_relat_1(X23))
        | ~ r1_tarski(X22,X23)
        | ~ v1_relat_1(X23)
        | ~ v1_relat_1(X22) )
      & ( r1_tarski(k2_relat_1(X22),k2_relat_1(X23))
        | ~ r1_tarski(X22,X23)
        | ~ v1_relat_1(X23)
        | ~ v1_relat_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk4_0,k2_zfmisc_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_18]),c_0_20])])).

fof(c_0_26,plain,(
    ! [X10,X11,X12] :
      ( ( r1_tarski(k2_zfmisc_1(X10,X12),k2_zfmisc_1(X11,X12))
        | ~ r1_tarski(X10,X11) )
      & ( r1_tarski(k2_zfmisc_1(X12,X10),k2_zfmisc_1(X12,X11))
        | ~ r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k2_relat_1(k2_zfmisc_1(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk4_0),k2_relat_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_20]),c_0_25])])).

cnf(c_0_29,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk4_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_31,plain,(
    ! [X21] :
      ( ~ v1_relat_1(X21)
      | r1_tarski(X21,k2_zfmisc_1(k1_relat_1(X21),k2_relat_1(X21))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).

cnf(c_0_32,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(k1_relat_1(esk4_0),X1),k2_zfmisc_1(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(X1,k2_relat_1(esk4_0)),k2_zfmisc_1(X1,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(X1,k2_zfmisc_1(esk2_0,X2))
    | ~ r1_tarski(X1,k2_zfmisc_1(k1_relat_1(esk4_0),X2)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(esk4_0,k2_zfmisc_1(k1_relat_1(esk4_0),k2_relat_1(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_25])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(X1,k2_zfmisc_1(X2,esk3_0))
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,k2_relat_1(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(esk4_0,k2_zfmisc_1(esk2_0,k2_relat_1(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_41,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(esk4_0,k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:19:40 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.40  # AutoSched0-Mode selected heuristic G_E___208_B01_00_F1_SE_CS_SP_PS_S064A
% 0.21/0.40  # and selection function SelectComplexG.
% 0.21/0.40  #
% 0.21/0.40  # Preprocessing time       : 0.039 s
% 0.21/0.40  # Presaturation interreduction done
% 0.21/0.40  
% 0.21/0.40  # Proof found!
% 0.21/0.40  # SZS status Theorem
% 0.21/0.40  # SZS output start CNFRefutation
% 0.21/0.40  fof(t13_relset_1, conjecture, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))=>(r1_tarski(k1_relat_1(X4),X2)=>m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 0.21/0.40  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.21/0.40  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.21/0.40  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.21/0.40  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.21/0.40  fof(t194_relat_1, axiom, ![X1, X2]:r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t194_relat_1)).
% 0.21/0.40  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 0.21/0.40  fof(t118_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>(r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 0.21/0.40  fof(t21_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 0.21/0.40  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))=>(r1_tarski(k1_relat_1(X4),X2)=>m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))))), inference(assume_negation,[status(cth)],[t13_relset_1])).
% 0.21/0.40  fof(c_0_10, plain, ![X13, X14]:((~m1_subset_1(X13,k1_zfmisc_1(X14))|r1_tarski(X13,X14))&(~r1_tarski(X13,X14)|m1_subset_1(X13,k1_zfmisc_1(X14)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.21/0.40  fof(c_0_11, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))&(r1_tarski(k1_relat_1(esk4_0),esk2_0)&~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.21/0.40  fof(c_0_12, plain, ![X15, X16]:(~v1_relat_1(X15)|(~m1_subset_1(X16,k1_zfmisc_1(X15))|v1_relat_1(X16))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.21/0.40  fof(c_0_13, plain, ![X17, X18]:v1_relat_1(k2_zfmisc_1(X17,X18)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.21/0.40  fof(c_0_14, plain, ![X7, X8, X9]:(~r1_tarski(X7,X8)|~r1_tarski(X8,X9)|r1_tarski(X7,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.21/0.40  fof(c_0_15, plain, ![X19, X20]:r1_tarski(k2_relat_1(k2_zfmisc_1(X19,X20)),X20), inference(variable_rename,[status(thm)],[t194_relat_1])).
% 0.21/0.40  fof(c_0_16, plain, ![X22, X23]:((r1_tarski(k1_relat_1(X22),k1_relat_1(X23))|~r1_tarski(X22,X23)|~v1_relat_1(X23)|~v1_relat_1(X22))&(r1_tarski(k2_relat_1(X22),k2_relat_1(X23))|~r1_tarski(X22,X23)|~v1_relat_1(X23)|~v1_relat_1(X22))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.21/0.40  cnf(c_0_17, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.40  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.40  cnf(c_0_19, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.40  cnf(c_0_20, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.40  cnf(c_0_21, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.40  cnf(c_0_22, plain, (r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.40  cnf(c_0_23, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.40  cnf(c_0_24, negated_conjecture, (r1_tarski(esk4_0,k2_zfmisc_1(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.21/0.40  cnf(c_0_25, negated_conjecture, (v1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_18]), c_0_20])])).
% 0.21/0.40  fof(c_0_26, plain, ![X10, X11, X12]:((r1_tarski(k2_zfmisc_1(X10,X12),k2_zfmisc_1(X11,X12))|~r1_tarski(X10,X11))&(r1_tarski(k2_zfmisc_1(X12,X10),k2_zfmisc_1(X12,X11))|~r1_tarski(X10,X11))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).
% 0.21/0.40  cnf(c_0_27, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k2_relat_1(k2_zfmisc_1(X3,X2)))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.21/0.40  cnf(c_0_28, negated_conjecture, (r1_tarski(k2_relat_1(esk4_0),k2_relat_1(k2_zfmisc_1(esk1_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_20]), c_0_25])])).
% 0.21/0.40  cnf(c_0_29, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.40  cnf(c_0_30, negated_conjecture, (r1_tarski(k1_relat_1(esk4_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.40  fof(c_0_31, plain, ![X21]:(~v1_relat_1(X21)|r1_tarski(X21,k2_zfmisc_1(k1_relat_1(X21),k2_relat_1(X21)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).
% 0.21/0.40  cnf(c_0_32, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.40  cnf(c_0_33, negated_conjecture, (r1_tarski(k2_relat_1(esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.21/0.40  cnf(c_0_34, negated_conjecture, (r1_tarski(k2_zfmisc_1(k1_relat_1(esk4_0),X1),k2_zfmisc_1(esk2_0,X1))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.21/0.40  cnf(c_0_35, plain, (r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.40  cnf(c_0_36, negated_conjecture, (r1_tarski(k2_zfmisc_1(X1,k2_relat_1(esk4_0)),k2_zfmisc_1(X1,esk3_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.21/0.40  cnf(c_0_37, negated_conjecture, (r1_tarski(X1,k2_zfmisc_1(esk2_0,X2))|~r1_tarski(X1,k2_zfmisc_1(k1_relat_1(esk4_0),X2))), inference(spm,[status(thm)],[c_0_21, c_0_34])).
% 0.21/0.40  cnf(c_0_38, negated_conjecture, (r1_tarski(esk4_0,k2_zfmisc_1(k1_relat_1(esk4_0),k2_relat_1(esk4_0)))), inference(spm,[status(thm)],[c_0_35, c_0_25])).
% 0.21/0.40  cnf(c_0_39, negated_conjecture, (r1_tarski(X1,k2_zfmisc_1(X2,esk3_0))|~r1_tarski(X1,k2_zfmisc_1(X2,k2_relat_1(esk4_0)))), inference(spm,[status(thm)],[c_0_21, c_0_36])).
% 0.21/0.40  cnf(c_0_40, negated_conjecture, (r1_tarski(esk4_0,k2_zfmisc_1(esk2_0,k2_relat_1(esk4_0)))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.21/0.40  cnf(c_0_41, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.40  cnf(c_0_42, negated_conjecture, (r1_tarski(esk4_0,k2_zfmisc_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.21/0.40  cnf(c_0_43, negated_conjecture, (~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.40  cnf(c_0_44, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43]), ['proof']).
% 0.21/0.40  # SZS output end CNFRefutation
% 0.21/0.40  # Proof object total steps             : 45
% 0.21/0.40  # Proof object clause steps            : 26
% 0.21/0.40  # Proof object formula steps           : 19
% 0.21/0.40  # Proof object conjectures             : 18
% 0.21/0.40  # Proof object clause conjectures      : 15
% 0.21/0.40  # Proof object formula conjectures     : 3
% 0.21/0.40  # Proof object initial clauses used    : 13
% 0.21/0.40  # Proof object initial formulas used   : 9
% 0.21/0.40  # Proof object generating inferences   : 13
% 0.21/0.40  # Proof object simplifying inferences  : 6
% 0.21/0.40  # Training examples: 0 positive, 0 negative
% 0.21/0.40  # Parsed axioms                        : 10
% 0.21/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.40  # Initial clauses                      : 17
% 0.21/0.40  # Removed in clause preprocessing      : 0
% 0.21/0.40  # Initial clauses in saturation        : 17
% 0.21/0.40  # Processed clauses                    : 144
% 0.21/0.40  # ...of these trivial                  : 0
% 0.21/0.40  # ...subsumed                          : 0
% 0.21/0.40  # ...remaining for further processing  : 144
% 0.21/0.40  # Other redundant clauses eliminated   : 2
% 0.21/0.40  # Clauses deleted for lack of memory   : 0
% 0.21/0.40  # Backward-subsumed                    : 0
% 0.21/0.40  # Backward-rewritten                   : 0
% 0.21/0.40  # Generated clauses                    : 356
% 0.21/0.40  # ...of the previous two non-trivial   : 293
% 0.21/0.40  # Contextual simplify-reflections      : 8
% 0.21/0.40  # Paramodulations                      : 354
% 0.21/0.40  # Factorizations                       : 0
% 0.21/0.40  # Equation resolutions                 : 2
% 0.21/0.40  # Propositional unsat checks           : 0
% 0.21/0.40  #    Propositional check models        : 0
% 0.21/0.40  #    Propositional check unsatisfiable : 0
% 0.21/0.40  #    Propositional clauses             : 0
% 0.21/0.40  #    Propositional clauses after purity: 0
% 0.21/0.40  #    Propositional unsat core size     : 0
% 0.21/0.40  #    Propositional preprocessing time  : 0.000
% 0.21/0.40  #    Propositional encoding time       : 0.000
% 0.21/0.40  #    Propositional solver time         : 0.000
% 0.21/0.40  #    Success case prop preproc time    : 0.000
% 0.21/0.40  #    Success case prop encoding time   : 0.000
% 0.21/0.40  #    Success case prop solver time     : 0.000
% 0.21/0.40  # Current number of processed clauses  : 126
% 0.21/0.40  #    Positive orientable unit clauses  : 55
% 0.21/0.40  #    Positive unorientable unit clauses: 0
% 0.21/0.40  #    Negative unit clauses             : 1
% 0.21/0.40  #    Non-unit-clauses                  : 70
% 0.21/0.40  # Current number of unprocessed clauses: 182
% 0.21/0.40  # ...number of literals in the above   : 240
% 0.21/0.40  # Current number of archived formulas  : 0
% 0.21/0.40  # Current number of archived clauses   : 16
% 0.21/0.40  # Clause-clause subsumption calls (NU) : 236
% 0.21/0.40  # Rec. Clause-clause subsumption calls : 224
% 0.21/0.40  # Non-unit clause-clause subsumptions  : 8
% 0.21/0.40  # Unit Clause-clause subsumption calls : 5
% 0.21/0.40  # Rewrite failures with RHS unbound    : 0
% 0.21/0.40  # BW rewrite match attempts            : 35
% 0.21/0.40  # BW rewrite match successes           : 0
% 0.21/0.40  # Condensation attempts                : 0
% 0.21/0.40  # Condensation successes               : 0
% 0.21/0.40  # Termbank termtop insertions          : 6725
% 0.21/0.40  
% 0.21/0.40  # -------------------------------------------------
% 0.21/0.40  # User time                : 0.055 s
% 0.21/0.40  # System time              : 0.004 s
% 0.21/0.40  # Total time               : 0.059 s
% 0.21/0.40  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
