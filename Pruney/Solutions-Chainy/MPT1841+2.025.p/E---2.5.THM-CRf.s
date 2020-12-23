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
% DateTime   : Thu Dec  3 11:18:56 EST 2020

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   47 (  80 expanded)
%              Number of clauses        :   24 (  32 expanded)
%              Number of leaves         :   11 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   94 ( 172 expanded)
%              Number of equality atoms :   27 (  43 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t49_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( m1_subset_1(X2,X1)
           => ~ ( v1_subset_1(k6_domain_1(X1,X2),X1)
                & v1_zfmisc_1(X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t6_tex_2])).

fof(c_0_12,plain,(
    ! [X18,X19] :
      ( v1_xboole_0(X18)
      | ~ v1_zfmisc_1(X18)
      | ~ m1_subset_1(X19,k1_zfmisc_1(X18))
      | v1_xboole_0(X19)
      | ~ v1_subset_1(X19,X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_tex_2])])])])).

fof(c_0_13,plain,(
    ! [X12,X13] :
      ( ~ v1_xboole_0(X12)
      | ~ m1_subset_1(X13,k1_zfmisc_1(X12))
      | v1_xboole_0(X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

fof(c_0_14,plain,(
    ! [X14,X15] :
      ( v1_xboole_0(X14)
      | ~ m1_subset_1(X15,X14)
      | m1_subset_1(k6_domain_1(X14,X15),k1_zfmisc_1(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

fof(c_0_15,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    & m1_subset_1(esk2_0,esk1_0)
    & v1_subset_1(k6_domain_1(esk1_0,esk2_0),esk1_0)
    & v1_zfmisc_1(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

fof(c_0_16,plain,(
    ! [X8,X9] : k3_tarski(k2_tarski(X8,X9)) = k2_xboole_0(X8,X9) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_17,plain,(
    ! [X6,X7] : k1_enumset1(X6,X6,X7) = k2_tarski(X6,X7) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_18,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_zfmisc_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_23,plain,(
    ! [X10,X11] : k2_xboole_0(k1_tarski(X10),X11) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

fof(c_0_24,plain,(
    ! [X5] : k2_tarski(X5,X5) = k1_tarski(X5) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_25,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_27,plain,(
    ! [X4] : k2_xboole_0(X4,k1_xboole_0) = X4 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_28,plain,(
    ! [X16,X17] :
      ( v1_xboole_0(X16)
      | ~ m1_subset_1(X17,X16)
      | k6_domain_1(X16,X17) = k1_tarski(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_29,plain,(
    ! [X3] :
      ( ~ v1_xboole_0(X3)
      | X3 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_30,plain,
    ( v1_xboole_0(X1)
    | ~ v1_subset_1(X1,X2)
    | ~ v1_zfmisc_1(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(csr,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(k6_domain_1(esk1_0,esk2_0),k1_zfmisc_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( v1_subset_1(k6_domain_1(esk1_0,esk2_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_33,negated_conjecture,
    ( v1_zfmisc_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_34,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_37,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,negated_conjecture,
    ( v1_xboole_0(k6_domain_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33])])).

cnf(c_0_41,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1),X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35]),c_0_26]),c_0_36])).

cnf(c_0_42,plain,
    ( k3_tarski(k1_enumset1(X1,X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_37,c_0_36])).

cnf(c_0_43,plain,
    ( k6_domain_1(X1,X2) = k1_enumset1(X2,X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_35]),c_0_26])).

cnf(c_0_44,negated_conjecture,
    ( k6_domain_1(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,plain,
    ( k1_enumset1(X1,X1,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_21]),c_0_44]),c_0_45]),c_0_22]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.31  % Computer   : n017.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 18:24:31 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.11/0.32  # Version: 2.5pre002
% 0.11/0.32  # No SInE strategy applied
% 0.11/0.32  # Trying AutoSched0 for 299 seconds
% 0.11/0.33  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.11/0.33  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.11/0.33  #
% 0.11/0.33  # Preprocessing time       : 0.017 s
% 0.11/0.33  # Presaturation interreduction done
% 0.11/0.33  
% 0.11/0.33  # Proof found!
% 0.11/0.33  # SZS status Theorem
% 0.11/0.33  # SZS output start CNFRefutation
% 0.11/0.33  fof(t6_tex_2, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,X1)=>~((v1_subset_1(k6_domain_1(X1,X2),X1)&v1_zfmisc_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 0.11/0.33  fof(cc2_tex_2, axiom, ![X1]:((~(v1_xboole_0(X1))&v1_zfmisc_1(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(~(v1_xboole_0(X2))=>~(v1_subset_1(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 0.11/0.33  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.11/0.33  fof(dt_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 0.11/0.33  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.11/0.33  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.11/0.33  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.11/0.33  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.11/0.33  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.11/0.33  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.11/0.33  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.11/0.33  fof(c_0_11, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,X1)=>~((v1_subset_1(k6_domain_1(X1,X2),X1)&v1_zfmisc_1(X1)))))), inference(assume_negation,[status(cth)],[t6_tex_2])).
% 0.11/0.33  fof(c_0_12, plain, ![X18, X19]:(v1_xboole_0(X18)|~v1_zfmisc_1(X18)|(~m1_subset_1(X19,k1_zfmisc_1(X18))|(v1_xboole_0(X19)|~v1_subset_1(X19,X18)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_tex_2])])])])).
% 0.11/0.33  fof(c_0_13, plain, ![X12, X13]:(~v1_xboole_0(X12)|(~m1_subset_1(X13,k1_zfmisc_1(X12))|v1_xboole_0(X13))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.11/0.33  fof(c_0_14, plain, ![X14, X15]:(v1_xboole_0(X14)|~m1_subset_1(X15,X14)|m1_subset_1(k6_domain_1(X14,X15),k1_zfmisc_1(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).
% 0.11/0.33  fof(c_0_15, negated_conjecture, (~v1_xboole_0(esk1_0)&(m1_subset_1(esk2_0,esk1_0)&(v1_subset_1(k6_domain_1(esk1_0,esk2_0),esk1_0)&v1_zfmisc_1(esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).
% 0.11/0.33  fof(c_0_16, plain, ![X8, X9]:k3_tarski(k2_tarski(X8,X9))=k2_xboole_0(X8,X9), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.11/0.33  fof(c_0_17, plain, ![X6, X7]:k1_enumset1(X6,X6,X7)=k2_tarski(X6,X7), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.11/0.33  cnf(c_0_18, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|~v1_zfmisc_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~v1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.11/0.33  cnf(c_0_19, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.11/0.33  cnf(c_0_20, plain, (v1_xboole_0(X1)|m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.11/0.33  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.11/0.33  cnf(c_0_22, negated_conjecture, (~v1_xboole_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.11/0.33  fof(c_0_23, plain, ![X10, X11]:k2_xboole_0(k1_tarski(X10),X11)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 0.11/0.33  fof(c_0_24, plain, ![X5]:k2_tarski(X5,X5)=k1_tarski(X5), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.11/0.33  cnf(c_0_25, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.11/0.33  cnf(c_0_26, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.11/0.33  fof(c_0_27, plain, ![X4]:k2_xboole_0(X4,k1_xboole_0)=X4, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.11/0.33  fof(c_0_28, plain, ![X16, X17]:(v1_xboole_0(X16)|~m1_subset_1(X17,X16)|k6_domain_1(X16,X17)=k1_tarski(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.11/0.33  fof(c_0_29, plain, ![X3]:(~v1_xboole_0(X3)|X3=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.11/0.33  cnf(c_0_30, plain, (v1_xboole_0(X1)|~v1_subset_1(X1,X2)|~v1_zfmisc_1(X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(csr,[status(thm)],[c_0_18, c_0_19])).
% 0.11/0.33  cnf(c_0_31, negated_conjecture, (m1_subset_1(k6_domain_1(esk1_0,esk2_0),k1_zfmisc_1(esk1_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])).
% 0.11/0.33  cnf(c_0_32, negated_conjecture, (v1_subset_1(k6_domain_1(esk1_0,esk2_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.11/0.33  cnf(c_0_33, negated_conjecture, (v1_zfmisc_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.11/0.33  cnf(c_0_34, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.11/0.33  cnf(c_0_35, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.11/0.33  cnf(c_0_36, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.11/0.33  cnf(c_0_37, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.11/0.33  cnf(c_0_38, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.11/0.33  cnf(c_0_39, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.11/0.33  cnf(c_0_40, negated_conjecture, (v1_xboole_0(k6_domain_1(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33])])).
% 0.11/0.33  cnf(c_0_41, plain, (k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1),X2))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35]), c_0_26]), c_0_36])).
% 0.11/0.33  cnf(c_0_42, plain, (k3_tarski(k1_enumset1(X1,X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_37, c_0_36])).
% 0.11/0.33  cnf(c_0_43, plain, (k6_domain_1(X1,X2)=k1_enumset1(X2,X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_35]), c_0_26])).
% 0.11/0.33  cnf(c_0_44, negated_conjecture, (k6_domain_1(esk1_0,esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.11/0.33  cnf(c_0_45, plain, (k1_enumset1(X1,X1,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.11/0.33  cnf(c_0_46, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_21]), c_0_44]), c_0_45]), c_0_22]), ['proof']).
% 0.11/0.33  # SZS output end CNFRefutation
% 0.11/0.33  # Proof object total steps             : 47
% 0.11/0.33  # Proof object clause steps            : 24
% 0.11/0.33  # Proof object formula steps           : 23
% 0.11/0.33  # Proof object conjectures             : 11
% 0.11/0.33  # Proof object clause conjectures      : 8
% 0.11/0.33  # Proof object formula conjectures     : 3
% 0.11/0.33  # Proof object initial clauses used    : 14
% 0.11/0.33  # Proof object initial formulas used   : 11
% 0.11/0.33  # Proof object generating inferences   : 5
% 0.11/0.33  # Proof object simplifying inferences  : 15
% 0.11/0.33  # Training examples: 0 positive, 0 negative
% 0.11/0.33  # Parsed axioms                        : 11
% 0.11/0.33  # Removed by relevancy pruning/SinE    : 0
% 0.11/0.33  # Initial clauses                      : 14
% 0.11/0.33  # Removed in clause preprocessing      : 3
% 0.11/0.33  # Initial clauses in saturation        : 11
% 0.11/0.33  # Processed clauses                    : 28
% 0.11/0.33  # ...of these trivial                  : 0
% 0.11/0.33  # ...subsumed                          : 1
% 0.11/0.33  # ...remaining for further processing  : 27
% 0.11/0.33  # Other redundant clauses eliminated   : 0
% 0.11/0.33  # Clauses deleted for lack of memory   : 0
% 0.11/0.33  # Backward-subsumed                    : 0
% 0.11/0.33  # Backward-rewritten                   : 3
% 0.11/0.33  # Generated clauses                    : 7
% 0.11/0.33  # ...of the previous two non-trivial   : 9
% 0.11/0.33  # Contextual simplify-reflections      : 1
% 0.11/0.33  # Paramodulations                      : 7
% 0.11/0.33  # Factorizations                       : 0
% 0.11/0.33  # Equation resolutions                 : 0
% 0.11/0.33  # Propositional unsat checks           : 0
% 0.11/0.33  #    Propositional check models        : 0
% 0.11/0.33  #    Propositional check unsatisfiable : 0
% 0.11/0.33  #    Propositional clauses             : 0
% 0.11/0.33  #    Propositional clauses after purity: 0
% 0.11/0.33  #    Propositional unsat core size     : 0
% 0.11/0.33  #    Propositional preprocessing time  : 0.000
% 0.11/0.33  #    Propositional encoding time       : 0.000
% 0.11/0.33  #    Propositional solver time         : 0.000
% 0.11/0.33  #    Success case prop preproc time    : 0.000
% 0.11/0.33  #    Success case prop encoding time   : 0.000
% 0.11/0.33  #    Success case prop solver time     : 0.000
% 0.11/0.33  # Current number of processed clauses  : 13
% 0.11/0.33  #    Positive orientable unit clauses  : 5
% 0.11/0.33  #    Positive unorientable unit clauses: 0
% 0.11/0.33  #    Negative unit clauses             : 3
% 0.11/0.33  #    Non-unit-clauses                  : 5
% 0.11/0.33  # Current number of unprocessed clauses: 3
% 0.11/0.33  # ...number of literals in the above   : 4
% 0.11/0.33  # Current number of archived formulas  : 0
% 0.11/0.33  # Current number of archived clauses   : 17
% 0.11/0.33  # Clause-clause subsumption calls (NU) : 8
% 0.11/0.33  # Rec. Clause-clause subsumption calls : 7
% 0.11/0.33  # Non-unit clause-clause subsumptions  : 1
% 0.11/0.33  # Unit Clause-clause subsumption calls : 2
% 0.11/0.33  # Rewrite failures with RHS unbound    : 0
% 0.11/0.33  # BW rewrite match attempts            : 1
% 0.11/0.33  # BW rewrite match successes           : 1
% 0.11/0.33  # Condensation attempts                : 0
% 0.11/0.33  # Condensation successes               : 0
% 0.11/0.33  # Termbank termtop insertions          : 982
% 0.11/0.33  
% 0.11/0.33  # -------------------------------------------------
% 0.11/0.33  # User time                : 0.016 s
% 0.11/0.33  # System time              : 0.005 s
% 0.11/0.33  # Total time               : 0.021 s
% 0.11/0.33  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
