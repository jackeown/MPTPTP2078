%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:57:50 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   46 (  85 expanded)
%              Number of clauses        :   25 (  35 expanded)
%              Number of leaves         :   10 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :  104 ( 197 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t34_relset_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
     => ( r1_tarski(X2,X3)
       => r2_relset_1(X2,X1,k5_relset_1(X2,X1,X4,X3),X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relset_1)).

fof(redefinition_k5_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k5_relset_1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(reflexivity_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => r2_relset_1(X1,X2,X3,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t193_relat_1,axiom,(
    ! [X1,X2] : r1_tarski(k1_relat_1(k2_zfmisc_1(X1,X2)),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_relat_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
       => ( r1_tarski(X2,X3)
         => r2_relset_1(X2,X1,k5_relset_1(X2,X1,X4,X3),X4) ) ) ),
    inference(assume_negation,[status(cth)],[t34_relset_1])).

fof(c_0_11,plain,(
    ! [X20,X21,X22,X23] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | k5_relset_1(X20,X21,X22,X23) = k7_relat_1(X22,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_relset_1])])).

fof(c_0_12,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))
    & r1_tarski(esk2_0,esk3_0)
    & ~ r2_relset_1(esk2_0,esk1_0,k5_relset_1(esk2_0,esk1_0,esk4_0,esk3_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_13,plain,
    ( k5_relset_1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_15,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(X10))
      | v1_relat_1(X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_16,plain,(
    ! [X12,X13] : v1_relat_1(k2_zfmisc_1(X12,X13)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_17,plain,(
    ! [X24,X25,X26,X27] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
      | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
      | r2_relset_1(X24,X25,X26,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[reflexivity_r2_relset_1])])).

cnf(c_0_18,negated_conjecture,
    ( ~ r2_relset_1(esk2_0,esk1_0,k5_relset_1(esk2_0,esk1_0,esk4_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( k5_relset_1(esk2_0,esk1_0,esk4_0,X1) = k7_relat_1(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_20,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X19)
      | ~ r1_tarski(k1_relat_1(X19),X18)
      | k7_relat_1(X19,X18) = X19 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

cnf(c_0_21,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( r2_relset_1(X2,X3,X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X5,X6,X7] :
      ( ~ r1_tarski(X5,X6)
      | ~ r1_tarski(X6,X7)
      | r1_tarski(X5,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_25,plain,(
    ! [X14,X15] : r1_tarski(k1_relat_1(k2_zfmisc_1(X14,X15)),X14) ),
    inference(variable_rename,[status(thm)],[t193_relat_1])).

cnf(c_0_26,negated_conjecture,
    ( ~ r2_relset_1(esk2_0,esk1_0,k7_relat_1(esk4_0,esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_14]),c_0_22])])).

cnf(c_0_29,negated_conjecture,
    ( r2_relset_1(esk2_0,esk1_0,X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_14])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( r1_tarski(k1_relat_1(k2_zfmisc_1(X1,X2)),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_32,plain,(
    ! [X16,X17] :
      ( ( r1_tarski(k1_relat_1(X16),k1_relat_1(X17))
        | ~ r1_tarski(X16,X17)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16) )
      & ( r1_tarski(k2_relat_1(X16),k2_relat_1(X17))
        | ~ r1_tarski(X16,X17)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

fof(c_0_33,plain,(
    ! [X8,X9] :
      ( ( ~ m1_subset_1(X8,k1_zfmisc_1(X9))
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | m1_subset_1(X8,k1_zfmisc_1(X9)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_34,negated_conjecture,
    ( ~ r2_relset_1(esk2_0,esk1_0,esk4_0,esk4_0)
    | ~ r1_tarski(k1_relat_1(esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

cnf(c_0_35,negated_conjecture,
    ( r2_relset_1(esk2_0,esk1_0,esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_14])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_relat_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35])])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_36])).

cnf(c_0_42,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_22])])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(esk4_0,k2_zfmisc_1(esk2_0,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_14])).

cnf(c_0_44,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_28])]),c_0_44]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:32:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.19/0.35  # No SInE strategy applied
% 0.19/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.027 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t34_relset_1, conjecture, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>(r1_tarski(X2,X3)=>r2_relset_1(X2,X1,k5_relset_1(X2,X1,X4,X3),X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_relset_1)).
% 0.19/0.38  fof(redefinition_k5_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k5_relset_1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 0.19/0.38  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.19/0.38  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.19/0.38  fof(reflexivity_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>r2_relset_1(X1,X2,X3,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 0.19/0.38  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 0.19/0.38  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.19/0.38  fof(t193_relat_1, axiom, ![X1, X2]:r1_tarski(k1_relat_1(k2_zfmisc_1(X1,X2)),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t193_relat_1)).
% 0.19/0.38  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 0.19/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.38  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>(r1_tarski(X2,X3)=>r2_relset_1(X2,X1,k5_relset_1(X2,X1,X4,X3),X4)))), inference(assume_negation,[status(cth)],[t34_relset_1])).
% 0.19/0.38  fof(c_0_11, plain, ![X20, X21, X22, X23]:(~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|k5_relset_1(X20,X21,X22,X23)=k7_relat_1(X22,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_relset_1])])).
% 0.19/0.38  fof(c_0_12, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))&(r1_tarski(esk2_0,esk3_0)&~r2_relset_1(esk2_0,esk1_0,k5_relset_1(esk2_0,esk1_0,esk4_0,esk3_0),esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.19/0.38  cnf(c_0_13, plain, (k5_relset_1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  fof(c_0_15, plain, ![X10, X11]:(~v1_relat_1(X10)|(~m1_subset_1(X11,k1_zfmisc_1(X10))|v1_relat_1(X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.19/0.38  fof(c_0_16, plain, ![X12, X13]:v1_relat_1(k2_zfmisc_1(X12,X13)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.19/0.38  fof(c_0_17, plain, ![X24, X25, X26, X27]:(~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))|r2_relset_1(X24,X25,X26,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[reflexivity_r2_relset_1])])).
% 0.19/0.38  cnf(c_0_18, negated_conjecture, (~r2_relset_1(esk2_0,esk1_0,k5_relset_1(esk2_0,esk1_0,esk4_0,esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_19, negated_conjecture, (k5_relset_1(esk2_0,esk1_0,esk4_0,X1)=k7_relat_1(esk4_0,X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.38  fof(c_0_20, plain, ![X18, X19]:(~v1_relat_1(X19)|(~r1_tarski(k1_relat_1(X19),X18)|k7_relat_1(X19,X18)=X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 0.19/0.38  cnf(c_0_21, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_22, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_23, plain, (r2_relset_1(X2,X3,X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.38  fof(c_0_24, plain, ![X5, X6, X7]:(~r1_tarski(X5,X6)|~r1_tarski(X6,X7)|r1_tarski(X5,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.19/0.38  fof(c_0_25, plain, ![X14, X15]:r1_tarski(k1_relat_1(k2_zfmisc_1(X14,X15)),X14), inference(variable_rename,[status(thm)],[t193_relat_1])).
% 0.19/0.38  cnf(c_0_26, negated_conjecture, (~r2_relset_1(esk2_0,esk1_0,k7_relat_1(esk4_0,esk3_0),esk4_0)), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.19/0.38  cnf(c_0_27, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.38  cnf(c_0_28, negated_conjecture, (v1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_14]), c_0_22])])).
% 0.19/0.38  cnf(c_0_29, negated_conjecture, (r2_relset_1(esk2_0,esk1_0,X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))), inference(spm,[status(thm)],[c_0_23, c_0_14])).
% 0.19/0.38  cnf(c_0_30, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.38  cnf(c_0_31, plain, (r1_tarski(k1_relat_1(k2_zfmisc_1(X1,X2)),X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.38  fof(c_0_32, plain, ![X16, X17]:((r1_tarski(k1_relat_1(X16),k1_relat_1(X17))|~r1_tarski(X16,X17)|~v1_relat_1(X17)|~v1_relat_1(X16))&(r1_tarski(k2_relat_1(X16),k2_relat_1(X17))|~r1_tarski(X16,X17)|~v1_relat_1(X17)|~v1_relat_1(X16))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.19/0.38  fof(c_0_33, plain, ![X8, X9]:((~m1_subset_1(X8,k1_zfmisc_1(X9))|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|m1_subset_1(X8,k1_zfmisc_1(X9)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.38  cnf(c_0_34, negated_conjecture, (~r2_relset_1(esk2_0,esk1_0,esk4_0,esk4_0)|~r1_tarski(k1_relat_1(esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])])).
% 0.19/0.38  cnf(c_0_35, negated_conjecture, (r2_relset_1(esk2_0,esk1_0,esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_29, c_0_14])).
% 0.19/0.38  cnf(c_0_36, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_37, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_relat_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.38  cnf(c_0_38, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.38  cnf(c_0_39, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.38  cnf(c_0_40, negated_conjecture, (~r1_tarski(k1_relat_1(esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35])])).
% 0.19/0.38  cnf(c_0_41, negated_conjecture, (r1_tarski(X1,esk3_0)|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_30, c_0_36])).
% 0.19/0.38  cnf(c_0_42, plain, (r1_tarski(k1_relat_1(X1),X2)|~v1_relat_1(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_22])])).
% 0.19/0.38  cnf(c_0_43, negated_conjecture, (r1_tarski(esk4_0,k2_zfmisc_1(esk2_0,esk1_0))), inference(spm,[status(thm)],[c_0_39, c_0_14])).
% 0.19/0.38  cnf(c_0_44, negated_conjecture, (~r1_tarski(k1_relat_1(esk4_0),esk2_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.38  cnf(c_0_45, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_28])]), c_0_44]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 46
% 0.19/0.38  # Proof object clause steps            : 25
% 0.19/0.38  # Proof object formula steps           : 21
% 0.19/0.38  # Proof object conjectures             : 17
% 0.19/0.38  # Proof object clause conjectures      : 14
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 12
% 0.19/0.38  # Proof object initial formulas used   : 10
% 0.19/0.38  # Proof object generating inferences   : 11
% 0.19/0.38  # Proof object simplifying inferences  : 12
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 10
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 14
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 14
% 0.19/0.38  # Processed clauses                    : 53
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 2
% 0.19/0.38  # ...remaining for further processing  : 51
% 0.19/0.38  # Other redundant clauses eliminated   : 0
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 2
% 0.19/0.38  # Generated clauses                    : 39
% 0.19/0.38  # ...of the previous two non-trivial   : 36
% 0.19/0.38  # Contextual simplify-reflections      : 0
% 0.19/0.38  # Paramodulations                      : 39
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 0
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 35
% 0.19/0.38  #    Positive orientable unit clauses  : 8
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 3
% 0.19/0.38  #    Non-unit-clauses                  : 24
% 0.19/0.38  # Current number of unprocessed clauses: 11
% 0.19/0.38  # ...number of literals in the above   : 34
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 16
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 48
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 41
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 2
% 0.19/0.38  # Unit Clause-clause subsumption calls : 25
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 4
% 0.19/0.38  # BW rewrite match successes           : 2
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 1669
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.028 s
% 0.19/0.38  # System time              : 0.005 s
% 0.19/0.38  # Total time               : 0.033 s
% 0.19/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
