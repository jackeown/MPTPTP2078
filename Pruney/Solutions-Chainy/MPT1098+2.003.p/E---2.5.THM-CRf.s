%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:08:30 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   43 (  81 expanded)
%              Number of clauses        :   26 (  33 expanded)
%              Number of leaves         :    8 (  20 expanded)
%              Depth                    :   12
%              Number of atoms          :  130 ( 306 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t13_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
     => ( r1_tarski(k1_relat_1(X4),X2)
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t33_finset_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( v1_finset_1(X1)
        & r1_tarski(X1,k2_zfmisc_1(X2,X3))
        & ! [X4] :
            ~ ( v1_finset_1(X4)
              & r1_tarski(X4,X2)
              & r1_tarski(X1,k2_zfmisc_1(X4,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_finset_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t32_finset_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( v1_finset_1(X1)
        & r1_tarski(X1,k2_zfmisc_1(X2,X3))
        & ! [X4,X5] :
            ~ ( v1_finset_1(X4)
              & r1_tarski(X4,X2)
              & v1_finset_1(X5)
              & r1_tarski(X5,X3)
              & r1_tarski(X1,k2_zfmisc_1(X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_finset_1)).

fof(c_0_8,plain,(
    ! [X17,X18,X19,X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X17,X19)))
      | ~ r1_tarski(k1_relat_1(X20),X18)
      | m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_relset_1])])).

fof(c_0_9,plain,(
    ! [X6,X7] :
      ( ( ~ m1_subset_1(X6,k1_zfmisc_1(X7))
        | r1_tarski(X6,X7) )
      & ( ~ r1_tarski(X6,X7)
        | m1_subset_1(X6,k1_zfmisc_1(X7)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( v1_finset_1(X1)
          & r1_tarski(X1,k2_zfmisc_1(X2,X3))
          & ! [X4] :
              ~ ( v1_finset_1(X4)
                & r1_tarski(X4,X2)
                & r1_tarski(X1,k2_zfmisc_1(X4,X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t33_finset_1])).

cnf(c_0_11,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(k1_relat_1(X1),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,negated_conjecture,(
    ! [X29] :
      ( v1_finset_1(esk3_0)
      & r1_tarski(esk3_0,k2_zfmisc_1(esk4_0,esk5_0))
      & ( ~ v1_finset_1(X29)
        | ~ r1_tarski(X29,esk4_0)
        | ~ r1_tarski(esk3_0,k2_zfmisc_1(X29,esk5_0)) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).

cnf(c_0_14,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(X1,k2_zfmisc_1(X4,X3))
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( r1_tarski(esk3_0,k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_16,plain,(
    ! [X10,X11] :
      ( ( ~ v4_relat_1(X11,X10)
        | r1_tarski(k1_relat_1(X11),X10)
        | ~ v1_relat_1(X11) )
      & ( ~ r1_tarski(k1_relat_1(X11),X10)
        | v4_relat_1(X11,X10)
        | ~ v1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

fof(c_0_17,plain,(
    ! [X8,X9] :
      ( ~ v1_relat_1(X8)
      | ~ m1_subset_1(X9,k1_zfmisc_1(X8))
      | v1_relat_1(X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk5_0)))
    | ~ r1_tarski(k1_relat_1(esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X14,X15,X16] :
      ( ( v4_relat_1(X16,X14)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) )
      & ( v5_relat_1(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_21,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X12,X13] : v1_relat_1(k2_zfmisc_1(X12,X13)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk5_0)))
    | ~ v4_relat_1(esk3_0,X1)
    | ~ v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_12])).

cnf(c_0_27,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk3_0,k2_zfmisc_1(X1,esk5_0))
    | ~ v4_relat_1(esk3_0,X1)
    | ~ v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( v4_relat_1(X1,X2)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_12])).

cnf(c_0_30,plain,
    ( v1_relat_1(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_31,plain,(
    ! [X21,X22,X23] :
      ( ( v1_finset_1(esk1_3(X21,X22,X23))
        | ~ v1_finset_1(X21)
        | ~ r1_tarski(X21,k2_zfmisc_1(X22,X23)) )
      & ( r1_tarski(esk1_3(X21,X22,X23),X22)
        | ~ v1_finset_1(X21)
        | ~ r1_tarski(X21,k2_zfmisc_1(X22,X23)) )
      & ( v1_finset_1(esk2_3(X21,X22,X23))
        | ~ v1_finset_1(X21)
        | ~ r1_tarski(X21,k2_zfmisc_1(X22,X23)) )
      & ( r1_tarski(esk2_3(X21,X22,X23),X23)
        | ~ v1_finset_1(X21)
        | ~ r1_tarski(X21,k2_zfmisc_1(X22,X23)) )
      & ( r1_tarski(X21,k2_zfmisc_1(esk1_3(X21,X22,X23),esk2_3(X21,X22,X23)))
        | ~ v1_finset_1(X21)
        | ~ r1_tarski(X21,k2_zfmisc_1(X22,X23)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_finset_1])])])])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(esk3_0,k2_zfmisc_1(X1,esk5_0))
    | ~ r1_tarski(esk3_0,k2_zfmisc_1(X1,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,k2_zfmisc_1(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)))
    | ~ v1_finset_1(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( v1_finset_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(esk3_0,k2_zfmisc_1(esk1_3(esk3_0,X1,X2),esk5_0))
    | ~ r1_tarski(esk3_0,k2_zfmisc_1(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

cnf(c_0_36,negated_conjecture,
    ( ~ v1_finset_1(X1)
    | ~ r1_tarski(X1,esk4_0)
    | ~ r1_tarski(esk3_0,k2_zfmisc_1(X1,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(esk3_0,k2_zfmisc_1(esk1_3(esk3_0,esk4_0,esk5_0),esk5_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_15])).

cnf(c_0_38,negated_conjecture,
    ( ~ v1_finset_1(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ r1_tarski(esk1_3(esk3_0,esk4_0,esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_39,plain,
    ( r1_tarski(esk1_3(X1,X2,X3),X2)
    | ~ v1_finset_1(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( ~ v1_finset_1(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_34]),c_0_15])])).

cnf(c_0_41,plain,
    ( v1_finset_1(esk1_3(X1,X2,X3))
    | ~ v1_finset_1(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_34]),c_0_15])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:34:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S022N
% 0.14/0.39  # and selection function SelectOptimalRestrDepth2.
% 0.14/0.39  #
% 0.14/0.39  # Preprocessing time       : 0.039 s
% 0.14/0.39  # Presaturation interreduction done
% 0.14/0.39  
% 0.14/0.39  # Proof found!
% 0.14/0.39  # SZS status Theorem
% 0.14/0.39  # SZS output start CNFRefutation
% 0.14/0.39  fof(t13_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))=>(r1_tarski(k1_relat_1(X4),X2)=>m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relset_1)).
% 0.14/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.14/0.39  fof(t33_finset_1, conjecture, ![X1, X2, X3]:~(((v1_finset_1(X1)&r1_tarski(X1,k2_zfmisc_1(X2,X3)))&![X4]:~(((v1_finset_1(X4)&r1_tarski(X4,X2))&r1_tarski(X1,k2_zfmisc_1(X4,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_finset_1)).
% 0.14/0.39  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 0.14/0.39  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.14/0.39  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.14/0.39  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.14/0.39  fof(t32_finset_1, axiom, ![X1, X2, X3]:~(((v1_finset_1(X1)&r1_tarski(X1,k2_zfmisc_1(X2,X3)))&![X4, X5]:~(((((v1_finset_1(X4)&r1_tarski(X4,X2))&v1_finset_1(X5))&r1_tarski(X5,X3))&r1_tarski(X1,k2_zfmisc_1(X4,X5)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_finset_1)).
% 0.14/0.39  fof(c_0_8, plain, ![X17, X18, X19, X20]:(~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X17,X19)))|(~r1_tarski(k1_relat_1(X20),X18)|m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_relset_1])])).
% 0.14/0.39  fof(c_0_9, plain, ![X6, X7]:((~m1_subset_1(X6,k1_zfmisc_1(X7))|r1_tarski(X6,X7))&(~r1_tarski(X6,X7)|m1_subset_1(X6,k1_zfmisc_1(X7)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.14/0.39  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3]:~(((v1_finset_1(X1)&r1_tarski(X1,k2_zfmisc_1(X2,X3)))&![X4]:~(((v1_finset_1(X4)&r1_tarski(X4,X2))&r1_tarski(X1,k2_zfmisc_1(X4,X3))))))), inference(assume_negation,[status(cth)],[t33_finset_1])).
% 0.14/0.39  cnf(c_0_11, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(k1_relat_1(X1),X4)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.39  cnf(c_0_12, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.39  fof(c_0_13, negated_conjecture, ![X29]:((v1_finset_1(esk3_0)&r1_tarski(esk3_0,k2_zfmisc_1(esk4_0,esk5_0)))&(~v1_finset_1(X29)|~r1_tarski(X29,esk4_0)|~r1_tarski(esk3_0,k2_zfmisc_1(X29,esk5_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).
% 0.14/0.39  cnf(c_0_14, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(X1,k2_zfmisc_1(X4,X3))|~r1_tarski(k1_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.14/0.39  cnf(c_0_15, negated_conjecture, (r1_tarski(esk3_0,k2_zfmisc_1(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.39  fof(c_0_16, plain, ![X10, X11]:((~v4_relat_1(X11,X10)|r1_tarski(k1_relat_1(X11),X10)|~v1_relat_1(X11))&(~r1_tarski(k1_relat_1(X11),X10)|v4_relat_1(X11,X10)|~v1_relat_1(X11))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.14/0.39  fof(c_0_17, plain, ![X8, X9]:(~v1_relat_1(X8)|(~m1_subset_1(X9,k1_zfmisc_1(X8))|v1_relat_1(X9))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.14/0.39  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk5_0)))|~r1_tarski(k1_relat_1(esk3_0),X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.14/0.39  cnf(c_0_19, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.39  fof(c_0_20, plain, ![X14, X15, X16]:((v4_relat_1(X16,X14)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))))&(v5_relat_1(X16,X15)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.14/0.39  cnf(c_0_21, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.39  fof(c_0_22, plain, ![X12, X13]:v1_relat_1(k2_zfmisc_1(X12,X13)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.14/0.39  cnf(c_0_23, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.39  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk5_0)))|~v4_relat_1(esk3_0,X1)|~v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.14/0.39  cnf(c_0_25, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.39  cnf(c_0_26, plain, (v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_21, c_0_12])).
% 0.14/0.39  cnf(c_0_27, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.39  cnf(c_0_28, negated_conjecture, (r1_tarski(esk3_0,k2_zfmisc_1(X1,esk5_0))|~v4_relat_1(esk3_0,X1)|~v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.14/0.39  cnf(c_0_29, plain, (v4_relat_1(X1,X2)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_25, c_0_12])).
% 0.14/0.39  cnf(c_0_30, plain, (v1_relat_1(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.14/0.39  fof(c_0_31, plain, ![X21, X22, X23]:(((((v1_finset_1(esk1_3(X21,X22,X23))|(~v1_finset_1(X21)|~r1_tarski(X21,k2_zfmisc_1(X22,X23))))&(r1_tarski(esk1_3(X21,X22,X23),X22)|(~v1_finset_1(X21)|~r1_tarski(X21,k2_zfmisc_1(X22,X23)))))&(v1_finset_1(esk2_3(X21,X22,X23))|(~v1_finset_1(X21)|~r1_tarski(X21,k2_zfmisc_1(X22,X23)))))&(r1_tarski(esk2_3(X21,X22,X23),X23)|(~v1_finset_1(X21)|~r1_tarski(X21,k2_zfmisc_1(X22,X23)))))&(r1_tarski(X21,k2_zfmisc_1(esk1_3(X21,X22,X23),esk2_3(X21,X22,X23)))|(~v1_finset_1(X21)|~r1_tarski(X21,k2_zfmisc_1(X22,X23))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_finset_1])])])])).
% 0.14/0.39  cnf(c_0_32, negated_conjecture, (r1_tarski(esk3_0,k2_zfmisc_1(X1,esk5_0))|~r1_tarski(esk3_0,k2_zfmisc_1(X1,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 0.14/0.39  cnf(c_0_33, plain, (r1_tarski(X1,k2_zfmisc_1(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)))|~v1_finset_1(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.39  cnf(c_0_34, negated_conjecture, (v1_finset_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.39  cnf(c_0_35, negated_conjecture, (r1_tarski(esk3_0,k2_zfmisc_1(esk1_3(esk3_0,X1,X2),esk5_0))|~r1_tarski(esk3_0,k2_zfmisc_1(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])])).
% 0.14/0.39  cnf(c_0_36, negated_conjecture, (~v1_finset_1(X1)|~r1_tarski(X1,esk4_0)|~r1_tarski(esk3_0,k2_zfmisc_1(X1,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.39  cnf(c_0_37, negated_conjecture, (r1_tarski(esk3_0,k2_zfmisc_1(esk1_3(esk3_0,esk4_0,esk5_0),esk5_0))), inference(spm,[status(thm)],[c_0_35, c_0_15])).
% 0.14/0.39  cnf(c_0_38, negated_conjecture, (~v1_finset_1(esk1_3(esk3_0,esk4_0,esk5_0))|~r1_tarski(esk1_3(esk3_0,esk4_0,esk5_0),esk4_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.14/0.39  cnf(c_0_39, plain, (r1_tarski(esk1_3(X1,X2,X3),X2)|~v1_finset_1(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.39  cnf(c_0_40, negated_conjecture, (~v1_finset_1(esk1_3(esk3_0,esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_34]), c_0_15])])).
% 0.14/0.39  cnf(c_0_41, plain, (v1_finset_1(esk1_3(X1,X2,X3))|~v1_finset_1(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.39  cnf(c_0_42, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_34]), c_0_15])]), ['proof']).
% 0.14/0.39  # SZS output end CNFRefutation
% 0.14/0.39  # Proof object total steps             : 43
% 0.14/0.39  # Proof object clause steps            : 26
% 0.14/0.39  # Proof object formula steps           : 17
% 0.14/0.39  # Proof object conjectures             : 15
% 0.14/0.39  # Proof object clause conjectures      : 12
% 0.14/0.39  # Proof object formula conjectures     : 3
% 0.14/0.39  # Proof object initial clauses used    : 13
% 0.14/0.39  # Proof object initial formulas used   : 8
% 0.14/0.39  # Proof object generating inferences   : 13
% 0.14/0.39  # Proof object simplifying inferences  : 9
% 0.14/0.39  # Training examples: 0 positive, 0 negative
% 0.14/0.39  # Parsed axioms                        : 8
% 0.14/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.39  # Initial clauses                      : 17
% 0.14/0.39  # Removed in clause preprocessing      : 0
% 0.14/0.39  # Initial clauses in saturation        : 17
% 0.14/0.39  # Processed clauses                    : 75
% 0.14/0.39  # ...of these trivial                  : 1
% 0.14/0.39  # ...subsumed                          : 9
% 0.14/0.39  # ...remaining for further processing  : 65
% 0.14/0.39  # Other redundant clauses eliminated   : 0
% 0.14/0.39  # Clauses deleted for lack of memory   : 0
% 0.14/0.39  # Backward-subsumed                    : 1
% 0.14/0.39  # Backward-rewritten                   : 3
% 0.14/0.39  # Generated clauses                    : 114
% 0.14/0.39  # ...of the previous two non-trivial   : 110
% 0.14/0.39  # Contextual simplify-reflections      : 3
% 0.14/0.39  # Paramodulations                      : 114
% 0.14/0.39  # Factorizations                       : 0
% 0.14/0.39  # Equation resolutions                 : 0
% 0.14/0.39  # Propositional unsat checks           : 0
% 0.14/0.39  #    Propositional check models        : 0
% 0.14/0.39  #    Propositional check unsatisfiable : 0
% 0.14/0.39  #    Propositional clauses             : 0
% 0.14/0.39  #    Propositional clauses after purity: 0
% 0.14/0.39  #    Propositional unsat core size     : 0
% 0.14/0.39  #    Propositional preprocessing time  : 0.000
% 0.14/0.39  #    Propositional encoding time       : 0.000
% 0.14/0.39  #    Propositional solver time         : 0.000
% 0.14/0.39  #    Success case prop preproc time    : 0.000
% 0.14/0.39  #    Success case prop encoding time   : 0.000
% 0.14/0.39  #    Success case prop solver time     : 0.000
% 0.14/0.39  # Current number of processed clauses  : 44
% 0.14/0.39  #    Positive orientable unit clauses  : 6
% 0.14/0.39  #    Positive unorientable unit clauses: 0
% 0.14/0.39  #    Negative unit clauses             : 1
% 0.14/0.39  #    Non-unit-clauses                  : 37
% 0.14/0.39  # Current number of unprocessed clauses: 68
% 0.14/0.39  # ...number of literals in the above   : 280
% 0.14/0.39  # Current number of archived formulas  : 0
% 0.14/0.39  # Current number of archived clauses   : 21
% 0.14/0.39  # Clause-clause subsumption calls (NU) : 220
% 0.14/0.39  # Rec. Clause-clause subsumption calls : 153
% 0.14/0.39  # Non-unit clause-clause subsumptions  : 12
% 0.14/0.39  # Unit Clause-clause subsumption calls : 60
% 0.14/0.39  # Rewrite failures with RHS unbound    : 0
% 0.14/0.39  # BW rewrite match attempts            : 3
% 0.14/0.39  # BW rewrite match successes           : 2
% 0.14/0.39  # Condensation attempts                : 0
% 0.14/0.39  # Condensation successes               : 0
% 0.14/0.39  # Termbank termtop insertions          : 2925
% 0.14/0.39  
% 0.14/0.39  # -------------------------------------------------
% 0.14/0.39  # User time                : 0.044 s
% 0.14/0.39  # System time              : 0.004 s
% 0.14/0.39  # Total time               : 0.047 s
% 0.14/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
