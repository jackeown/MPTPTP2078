%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:57:06 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   32 (  53 expanded)
%              Number of clauses        :   17 (  21 expanded)
%              Number of leaves         :    7 (  14 expanded)
%              Depth                    :    8
%              Number of atoms          :   79 ( 131 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(cc6_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1) )
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X2))
         => v5_relat_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_relat_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(t13_relset_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
     => ( r1_tarski(k1_relat_1(X4),X2)
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t194_relat_1,axiom,(
    ! [X1,X2] : r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t194_relat_1)).

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(c_0_7,plain,(
    ! [X10,X11] :
      ( ( ~ v5_relat_1(X11,X10)
        | r1_tarski(k2_relat_1(X11),X10)
        | ~ v1_relat_1(X11) )
      & ( ~ r1_tarski(k2_relat_1(X11),X10)
        | v5_relat_1(X11,X10)
        | ~ v1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

fof(c_0_8,plain,(
    ! [X7,X8,X9] :
      ( ~ v1_relat_1(X8)
      | ~ v5_relat_1(X8,X7)
      | ~ m1_subset_1(X9,k1_zfmisc_1(X8))
      | v5_relat_1(X9,X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc6_relat_1])])])).

fof(c_0_9,plain,(
    ! [X5,X6] :
      ( ~ v1_relat_1(X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X5))
      | v1_relat_1(X6) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
       => ( r1_tarski(k1_relat_1(X4),X2)
         => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ) ),
    inference(assume_negation,[status(cth)],[t13_relset_1])).

cnf(c_0_11,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( v5_relat_1(X3,X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))
    & r1_tarski(k1_relat_1(esk4_0),esk2_0)
    & ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_15,plain,(
    ! [X12,X13] : v1_relat_1(k2_zfmisc_1(X12,X13)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_16,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk4_0),X1)
    | ~ v5_relat_1(k2_zfmisc_1(esk1_0,esk3_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])])).

cnf(c_0_20,plain,
    ( v5_relat_1(X1,X2)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_21,plain,(
    ! [X14,X15] : r1_tarski(k2_relat_1(k2_zfmisc_1(X14,X15)),X15) ),
    inference(variable_rename,[status(thm)],[t194_relat_1])).

fof(c_0_22,plain,(
    ! [X16,X17,X18] :
      ( ~ v1_relat_1(X18)
      | ~ r1_tarski(k1_relat_1(X18),X16)
      | ~ r1_tarski(k2_relat_1(X18),X17)
      | m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk4_0),X1)
    | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(esk1_0,esk3_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_18])])).

cnf(c_0_24,plain,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_17]),c_0_18])])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))
    | ~ r1_tarski(k1_relat_1(esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk4_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_30,negated_conjecture,
    ( ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:59:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S024I
% 0.13/0.37  # and selection function SelectOptimalRestrPDepth2.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.027 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 0.13/0.37  fof(cc6_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v5_relat_1(X2,X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X2))=>v5_relat_1(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_relat_1)).
% 0.13/0.37  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.13/0.37  fof(t13_relset_1, conjecture, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))=>(r1_tarski(k1_relat_1(X4),X2)=>m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relset_1)).
% 0.13/0.37  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.13/0.37  fof(t194_relat_1, axiom, ![X1, X2]:r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t194_relat_1)).
% 0.13/0.37  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 0.13/0.37  fof(c_0_7, plain, ![X10, X11]:((~v5_relat_1(X11,X10)|r1_tarski(k2_relat_1(X11),X10)|~v1_relat_1(X11))&(~r1_tarski(k2_relat_1(X11),X10)|v5_relat_1(X11,X10)|~v1_relat_1(X11))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.13/0.37  fof(c_0_8, plain, ![X7, X8, X9]:(~v1_relat_1(X8)|~v5_relat_1(X8,X7)|(~m1_subset_1(X9,k1_zfmisc_1(X8))|v5_relat_1(X9,X7))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc6_relat_1])])])).
% 0.13/0.37  fof(c_0_9, plain, ![X5, X6]:(~v1_relat_1(X5)|(~m1_subset_1(X6,k1_zfmisc_1(X5))|v1_relat_1(X6))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.13/0.37  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))=>(r1_tarski(k1_relat_1(X4),X2)=>m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))))), inference(assume_negation,[status(cth)],[t13_relset_1])).
% 0.13/0.37  cnf(c_0_11, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_12, plain, (v5_relat_1(X3,X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_13, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  fof(c_0_14, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))&(r1_tarski(k1_relat_1(esk4_0),esk2_0)&~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.13/0.37  fof(c_0_15, plain, ![X12, X13]:v1_relat_1(k2_zfmisc_1(X12,X13)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.13/0.37  cnf(c_0_16, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X3))|~v1_relat_1(X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13])).
% 0.13/0.37  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_18, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.37  cnf(c_0_19, negated_conjecture, (r1_tarski(k2_relat_1(esk4_0),X1)|~v5_relat_1(k2_zfmisc_1(esk1_0,esk3_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])])).
% 0.13/0.37  cnf(c_0_20, plain, (v5_relat_1(X1,X2)|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  fof(c_0_21, plain, ![X14, X15]:r1_tarski(k2_relat_1(k2_zfmisc_1(X14,X15)),X15), inference(variable_rename,[status(thm)],[t194_relat_1])).
% 0.13/0.37  fof(c_0_22, plain, ![X16, X17, X18]:(~v1_relat_1(X18)|(~r1_tarski(k1_relat_1(X18),X16)|~r1_tarski(k2_relat_1(X18),X17)|m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 0.13/0.37  cnf(c_0_23, negated_conjecture, (r1_tarski(k2_relat_1(esk4_0),X1)|~r1_tarski(k2_relat_1(k2_zfmisc_1(esk1_0,esk3_0)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_18])])).
% 0.13/0.37  cnf(c_0_24, plain, (r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.37  cnf(c_0_25, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.37  cnf(c_0_26, negated_conjecture, (r1_tarski(k2_relat_1(esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.37  cnf(c_0_27, negated_conjecture, (v1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_17]), c_0_18])])).
% 0.13/0.37  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))|~r1_tarski(k1_relat_1(esk4_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])])).
% 0.13/0.37  cnf(c_0_29, negated_conjecture, (r1_tarski(k1_relat_1(esk4_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_30, negated_conjecture, (~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_31, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 32
% 0.13/0.37  # Proof object clause steps            : 17
% 0.13/0.37  # Proof object formula steps           : 15
% 0.13/0.37  # Proof object conjectures             : 12
% 0.13/0.37  # Proof object clause conjectures      : 9
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 10
% 0.13/0.37  # Proof object initial formulas used   : 7
% 0.13/0.37  # Proof object generating inferences   : 7
% 0.13/0.37  # Proof object simplifying inferences  : 10
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 7
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 10
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 10
% 0.13/0.37  # Processed clauses                    : 29
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 0
% 0.13/0.37  # ...remaining for further processing  : 29
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 0
% 0.13/0.37  # Generated clauses                    : 22
% 0.13/0.37  # ...of the previous two non-trivial   : 20
% 0.13/0.37  # Contextual simplify-reflections      : 2
% 0.13/0.37  # Paramodulations                      : 22
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 0
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 19
% 0.13/0.37  #    Positive orientable unit clauses  : 6
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 1
% 0.13/0.37  #    Non-unit-clauses                  : 12
% 0.13/0.37  # Current number of unprocessed clauses: 11
% 0.13/0.37  # ...number of literals in the above   : 64
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 10
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 13
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 13
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 2
% 0.13/0.37  # Unit Clause-clause subsumption calls : 2
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 2
% 0.13/0.37  # BW rewrite match successes           : 0
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 1228
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.026 s
% 0.13/0.37  # System time              : 0.005 s
% 0.13/0.37  # Total time               : 0.032 s
% 0.13/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
