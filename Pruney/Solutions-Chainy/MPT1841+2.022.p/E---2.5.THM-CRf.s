%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:56 EST 2020

% Result     : Theorem 0.06s
% Output     : CNFRefutation 0.06s
% Verified   : 
% Statistics : Number of formulae       :   37 (  54 expanded)
%              Number of clauses        :   18 (  20 expanded)
%              Number of leaves         :    9 (  14 expanded)
%              Depth                    :    6
%              Number of atoms          :   81 ( 143 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t6_tex_2,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,X1)
         => ~ ( v1_subset_1(k6_domain_1(X1,X2),X1)
              & v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(cc2_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & v1_zfmisc_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => ( ~ v1_xboole_0(X2)
           => ~ v1_subset_1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(fc3_subset_1,axiom,(
    ! [X1,X2,X3,X4] : ~ v1_xboole_0(k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_subset_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( m1_subset_1(X2,X1)
           => ~ ( v1_subset_1(k6_domain_1(X1,X2),X1)
                & v1_zfmisc_1(X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t6_tex_2])).

fof(c_0_10,plain,(
    ! [X19,X20] :
      ( v1_xboole_0(X19)
      | ~ m1_subset_1(X20,X19)
      | k6_domain_1(X19,X20) = k1_tarski(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_11,plain,(
    ! [X5] : k2_tarski(X5,X5) = k1_tarski(X5) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_12,plain,(
    ! [X6,X7] : k1_enumset1(X6,X6,X7) = k2_tarski(X6,X7) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,plain,(
    ! [X8,X9,X10] : k2_enumset1(X8,X8,X9,X10) = k1_enumset1(X8,X9,X10) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_14,plain,(
    ! [X21,X22] :
      ( v1_xboole_0(X21)
      | ~ v1_zfmisc_1(X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(X21))
      | v1_xboole_0(X22)
      | ~ v1_subset_1(X22,X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_tex_2])])])])).

fof(c_0_15,plain,(
    ! [X15,X16] :
      ( ~ v1_xboole_0(X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(X15))
      | v1_xboole_0(X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

fof(c_0_16,plain,(
    ! [X17,X18] :
      ( v1_xboole_0(X17)
      | ~ m1_subset_1(X18,X17)
      | m1_subset_1(k6_domain_1(X17,X18),k1_zfmisc_1(X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

fof(c_0_17,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    & m1_subset_1(esk2_0,esk1_0)
    & v1_subset_1(k6_domain_1(esk1_0,esk2_0),esk1_0)
    & v1_zfmisc_1(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

cnf(c_0_18,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_zfmisc_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_27,plain,(
    ! [X11,X12,X13,X14] : ~ v1_xboole_0(k2_enumset1(X11,X12,X13,X14)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc3_subset_1])])).

cnf(c_0_28,plain,
    ( k6_domain_1(X1,X2) = k2_enumset1(X2,X2,X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21])).

cnf(c_0_29,plain,
    ( v1_xboole_0(X1)
    | ~ v1_subset_1(X1,X2)
    | ~ v1_zfmisc_1(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(csr,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(k6_domain_1(esk1_0,esk2_0),k1_zfmisc_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( v1_subset_1(k6_domain_1(esk1_0,esk2_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_32,negated_conjecture,
    ( v1_zfmisc_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_33,plain,
    ( ~ v1_xboole_0(k2_enumset1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0) = k6_domain_1(esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_25]),c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( v1_xboole_0(k6_domain_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32])])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.06/0.25  % Computer   : n002.cluster.edu
% 0.06/0.25  % Model      : x86_64 x86_64
% 0.06/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.25  % Memory     : 8042.1875MB
% 0.06/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.25  % CPULimit   : 60
% 0.06/0.25  % WCLimit    : 600
% 0.06/0.25  % DateTime   : Tue Dec  1 09:48:51 EST 2020
% 0.06/0.25  % CPUTime    : 
% 0.06/0.25  # Version: 2.5pre002
% 0.06/0.26  # No SInE strategy applied
% 0.06/0.26  # Trying AutoSched0 for 299 seconds
% 0.06/0.27  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.06/0.27  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.06/0.27  #
% 0.06/0.27  # Preprocessing time       : 0.012 s
% 0.06/0.27  # Presaturation interreduction done
% 0.06/0.27  
% 0.06/0.27  # Proof found!
% 0.06/0.27  # SZS status Theorem
% 0.06/0.27  # SZS output start CNFRefutation
% 0.06/0.27  fof(t6_tex_2, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,X1)=>~((v1_subset_1(k6_domain_1(X1,X2),X1)&v1_zfmisc_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 0.06/0.27  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.06/0.27  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.06/0.27  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.06/0.27  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.06/0.27  fof(cc2_tex_2, axiom, ![X1]:((~(v1_xboole_0(X1))&v1_zfmisc_1(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(~(v1_xboole_0(X2))=>~(v1_subset_1(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 0.06/0.27  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.06/0.27  fof(dt_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 0.06/0.27  fof(fc3_subset_1, axiom, ![X1, X2, X3, X4]:~(v1_xboole_0(k2_enumset1(X1,X2,X3,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_subset_1)).
% 0.06/0.27  fof(c_0_9, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,X1)=>~((v1_subset_1(k6_domain_1(X1,X2),X1)&v1_zfmisc_1(X1)))))), inference(assume_negation,[status(cth)],[t6_tex_2])).
% 0.06/0.27  fof(c_0_10, plain, ![X19, X20]:(v1_xboole_0(X19)|~m1_subset_1(X20,X19)|k6_domain_1(X19,X20)=k1_tarski(X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.06/0.27  fof(c_0_11, plain, ![X5]:k2_tarski(X5,X5)=k1_tarski(X5), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.06/0.27  fof(c_0_12, plain, ![X6, X7]:k1_enumset1(X6,X6,X7)=k2_tarski(X6,X7), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.06/0.27  fof(c_0_13, plain, ![X8, X9, X10]:k2_enumset1(X8,X8,X9,X10)=k1_enumset1(X8,X9,X10), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.06/0.27  fof(c_0_14, plain, ![X21, X22]:(v1_xboole_0(X21)|~v1_zfmisc_1(X21)|(~m1_subset_1(X22,k1_zfmisc_1(X21))|(v1_xboole_0(X22)|~v1_subset_1(X22,X21)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_tex_2])])])])).
% 0.06/0.27  fof(c_0_15, plain, ![X15, X16]:(~v1_xboole_0(X15)|(~m1_subset_1(X16,k1_zfmisc_1(X15))|v1_xboole_0(X16))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.06/0.27  fof(c_0_16, plain, ![X17, X18]:(v1_xboole_0(X17)|~m1_subset_1(X18,X17)|m1_subset_1(k6_domain_1(X17,X18),k1_zfmisc_1(X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).
% 0.06/0.27  fof(c_0_17, negated_conjecture, (~v1_xboole_0(esk1_0)&(m1_subset_1(esk2_0,esk1_0)&(v1_subset_1(k6_domain_1(esk1_0,esk2_0),esk1_0)&v1_zfmisc_1(esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).
% 0.06/0.27  cnf(c_0_18, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.06/0.27  cnf(c_0_19, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.06/0.27  cnf(c_0_20, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.06/0.27  cnf(c_0_21, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.06/0.27  cnf(c_0_22, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|~v1_zfmisc_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~v1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.06/0.27  cnf(c_0_23, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.06/0.27  cnf(c_0_24, plain, (v1_xboole_0(X1)|m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.06/0.27  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.06/0.27  cnf(c_0_26, negated_conjecture, (~v1_xboole_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.06/0.27  fof(c_0_27, plain, ![X11, X12, X13, X14]:~v1_xboole_0(k2_enumset1(X11,X12,X13,X14)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc3_subset_1])])).
% 0.06/0.27  cnf(c_0_28, plain, (k6_domain_1(X1,X2)=k2_enumset1(X2,X2,X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21])).
% 0.06/0.27  cnf(c_0_29, plain, (v1_xboole_0(X1)|~v1_subset_1(X1,X2)|~v1_zfmisc_1(X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(csr,[status(thm)],[c_0_22, c_0_23])).
% 0.06/0.27  cnf(c_0_30, negated_conjecture, (m1_subset_1(k6_domain_1(esk1_0,esk2_0),k1_zfmisc_1(esk1_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])).
% 0.06/0.27  cnf(c_0_31, negated_conjecture, (v1_subset_1(k6_domain_1(esk1_0,esk2_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.06/0.27  cnf(c_0_32, negated_conjecture, (v1_zfmisc_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.06/0.27  cnf(c_0_33, plain, (~v1_xboole_0(k2_enumset1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.06/0.27  cnf(c_0_34, negated_conjecture, (k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)=k6_domain_1(esk1_0,esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_25]), c_0_26])).
% 0.06/0.27  cnf(c_0_35, negated_conjecture, (v1_xboole_0(k6_domain_1(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32])])).
% 0.06/0.27  cnf(c_0_36, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])]), ['proof']).
% 0.06/0.27  # SZS output end CNFRefutation
% 0.06/0.27  # Proof object total steps             : 37
% 0.06/0.27  # Proof object clause steps            : 18
% 0.06/0.27  # Proof object formula steps           : 19
% 0.06/0.27  # Proof object conjectures             : 11
% 0.06/0.27  # Proof object clause conjectures      : 8
% 0.06/0.27  # Proof object formula conjectures     : 3
% 0.06/0.27  # Proof object initial clauses used    : 12
% 0.06/0.27  # Proof object initial formulas used   : 9
% 0.06/0.27  # Proof object generating inferences   : 4
% 0.06/0.27  # Proof object simplifying inferences  : 11
% 0.06/0.27  # Training examples: 0 positive, 0 negative
% 0.06/0.27  # Parsed axioms                        : 9
% 0.06/0.27  # Removed by relevancy pruning/SinE    : 0
% 0.06/0.27  # Initial clauses                      : 12
% 0.06/0.27  # Removed in clause preprocessing      : 3
% 0.06/0.27  # Initial clauses in saturation        : 9
% 0.06/0.27  # Processed clauses                    : 22
% 0.06/0.27  # ...of these trivial                  : 1
% 0.06/0.27  # ...subsumed                          : 0
% 0.06/0.27  # ...remaining for further processing  : 21
% 0.06/0.27  # Other redundant clauses eliminated   : 0
% 0.06/0.27  # Clauses deleted for lack of memory   : 0
% 0.06/0.27  # Backward-subsumed                    : 0
% 0.06/0.27  # Backward-rewritten                   : 0
% 0.06/0.27  # Generated clauses                    : 7
% 0.06/0.27  # ...of the previous two non-trivial   : 6
% 0.06/0.27  # Contextual simplify-reflections      : 1
% 0.06/0.27  # Paramodulations                      : 7
% 0.06/0.27  # Factorizations                       : 0
% 0.06/0.27  # Equation resolutions                 : 0
% 0.06/0.27  # Propositional unsat checks           : 0
% 0.06/0.27  #    Propositional check models        : 0
% 0.06/0.27  #    Propositional check unsatisfiable : 0
% 0.06/0.27  #    Propositional clauses             : 0
% 0.06/0.27  #    Propositional clauses after purity: 0
% 0.06/0.27  #    Propositional unsat core size     : 0
% 0.06/0.27  #    Propositional preprocessing time  : 0.000
% 0.06/0.27  #    Propositional encoding time       : 0.000
% 0.06/0.27  #    Propositional solver time         : 0.000
% 0.06/0.27  #    Success case prop preproc time    : 0.000
% 0.06/0.27  #    Success case prop encoding time   : 0.000
% 0.06/0.27  #    Success case prop solver time     : 0.000
% 0.06/0.27  # Current number of processed clauses  : 12
% 0.06/0.27  #    Positive orientable unit clauses  : 6
% 0.06/0.27  #    Positive unorientable unit clauses: 0
% 0.06/0.27  #    Negative unit clauses             : 2
% 0.06/0.27  #    Non-unit-clauses                  : 4
% 0.06/0.27  # Current number of unprocessed clauses: 2
% 0.06/0.27  # ...number of literals in the above   : 4
% 0.06/0.27  # Current number of archived formulas  : 0
% 0.06/0.27  # Current number of archived clauses   : 12
% 0.06/0.27  # Clause-clause subsumption calls (NU) : 1
% 0.06/0.27  # Rec. Clause-clause subsumption calls : 1
% 0.06/0.27  # Non-unit clause-clause subsumptions  : 1
% 0.06/0.27  # Unit Clause-clause subsumption calls : 0
% 0.06/0.27  # Rewrite failures with RHS unbound    : 0
% 0.06/0.27  # BW rewrite match attempts            : 0
% 0.06/0.27  # BW rewrite match successes           : 0
% 0.06/0.27  # Condensation attempts                : 0
% 0.06/0.27  # Condensation successes               : 0
% 0.06/0.27  # Termbank termtop insertions          : 919
% 0.06/0.27  
% 0.06/0.27  # -------------------------------------------------
% 0.06/0.27  # User time                : 0.013 s
% 0.06/0.27  # System time              : 0.001 s
% 0.06/0.27  # Total time               : 0.014 s
% 0.06/0.27  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
