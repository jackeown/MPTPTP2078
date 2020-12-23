%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:05:56 EST 2020

% Result     : Theorem 0.08s
% Output     : CNFRefutation 0.08s
% Verified   : 
% Statistics : Number of formulae       :   35 ( 210 expanded)
%              Number of clauses        :   23 (  71 expanded)
%              Number of leaves         :    6 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :  103 (1201 expanded)
%              Number of equality atoms :   24 ( 312 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t85_funct_2,conjecture,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ( v2_funct_1(X2)
       => ! [X3,X4] :
            ( ( r2_hidden(X3,X1)
              & r2_hidden(X4,X1)
              & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) )
           => X3 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_2)).

fof(t32_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( v2_funct_1(X4)
          & r2_hidden(X3,X1) )
       => ( X2 = k1_xboole_0
          | k1_funct_1(k2_funct_1(X4),k1_funct_1(X4,X3)) = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(dt_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(t67_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => k1_relset_1(X1,X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_funct_2(X2,X1,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
       => ( v2_funct_1(X2)
         => ! [X3,X4] :
              ( ( r2_hidden(X3,X1)
                & r2_hidden(X4,X1)
                & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) )
             => X3 = X4 ) ) ) ),
    inference(assume_negation,[status(cth)],[t85_funct_2])).

fof(c_0_7,plain,(
    ! [X14,X15,X16,X17] :
      ( ~ v1_funct_1(X17)
      | ~ v1_funct_2(X17,X14,X15)
      | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
      | ~ v2_funct_1(X17)
      | ~ r2_hidden(X16,X14)
      | X15 = k1_xboole_0
      | k1_funct_1(k2_funct_1(X17),k1_funct_1(X17,X16)) = X16 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_funct_2])])).

fof(c_0_8,negated_conjecture,
    ( v1_funct_1(esk2_0)
    & v1_funct_2(esk2_0,esk1_0,esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    & v2_funct_1(esk2_0)
    & r2_hidden(esk3_0,esk1_0)
    & r2_hidden(esk4_0,esk1_0)
    & k1_funct_1(esk2_0,esk3_0) = k1_funct_1(esk2_0,esk4_0)
    & esk3_0 != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_9,plain,(
    ! [X5,X6,X7] :
      ( ~ r2_hidden(X5,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X7))
      | ~ v1_xboole_0(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_10,plain,(
    ! [X8,X9,X10] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | m1_subset_1(k1_relset_1(X8,X9,X10),k1_zfmisc_1(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).

cnf(c_0_11,plain,
    ( X3 = k1_xboole_0
    | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X4)) = X4
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( v2_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( v1_funct_2(esk2_0,esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_18,plain,(
    ! [X18,X19] :
      ( ~ v1_funct_1(X19)
      | ~ v1_funct_2(X19,X18,X18)
      | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X18,X18)))
      | k1_relset_1(X18,X18,X19) = X18 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_funct_2])])).

cnf(c_0_19,negated_conjecture,
    ( k1_funct_1(k2_funct_1(esk2_0),k1_funct_1(esk2_0,X1)) = X1
    | esk1_0 = k1_xboole_0
    | ~ r2_hidden(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_14]),c_0_15])])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,negated_conjecture,
    ( k1_funct_1(esk2_0,esk3_0) = k1_funct_1(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,k1_relset_1(X2,X3,X1))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,plain,
    ( k1_relset_1(X2,X2,X1) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( k1_funct_1(k2_funct_1(esk2_0),k1_funct_1(esk2_0,esk3_0)) = esk4_0
    | esk1_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( k1_funct_1(k2_funct_1(esk2_0),k1_funct_1(esk2_0,esk3_0)) = esk3_0
    | esk1_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_19,c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( esk3_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_28,plain,
    ( ~ v1_funct_2(X1,X2,X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))
    | ~ r2_hidden(X3,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( ~ r2_hidden(X1,esk1_0)
    | ~ v1_xboole_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_12]),c_0_14]),c_0_15])])).

cnf(c_0_31,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk4_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_20,c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_29]),c_0_29]),c_0_31])])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_32,c_0_33]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.08  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.08/0.28  % Computer   : n021.cluster.edu
% 0.08/0.28  % Model      : x86_64 x86_64
% 0.08/0.28  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.28  % Memory     : 8042.1875MB
% 0.08/0.28  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.28  % CPULimit   : 60
% 0.08/0.28  % WCLimit    : 600
% 0.08/0.28  % DateTime   : Tue Dec  1 15:18:49 EST 2020
% 0.08/0.28  % CPUTime    : 
% 0.08/0.28  # Version: 2.5pre002
% 0.08/0.28  # No SInE strategy applied
% 0.08/0.28  # Trying AutoSched0 for 299 seconds
% 0.08/0.30  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.08/0.30  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.08/0.30  #
% 0.08/0.30  # Preprocessing time       : 0.025 s
% 0.08/0.30  # Presaturation interreduction done
% 0.08/0.30  
% 0.08/0.30  # Proof found!
% 0.08/0.30  # SZS status Theorem
% 0.08/0.30  # SZS output start CNFRefutation
% 0.08/0.30  fof(t85_funct_2, conjecture, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(v2_funct_1(X2)=>![X3, X4]:(((r2_hidden(X3,X1)&r2_hidden(X4,X1))&k1_funct_1(X2,X3)=k1_funct_1(X2,X4))=>X3=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_funct_2)).
% 0.08/0.30  fof(t32_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X4)&r2_hidden(X3,X1))=>(X2=k1_xboole_0|k1_funct_1(k2_funct_1(X4),k1_funct_1(X4,X3))=X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_funct_2)).
% 0.08/0.30  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.08/0.30  fof(dt_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 0.08/0.30  fof(t67_funct_2, axiom, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>k1_relset_1(X1,X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 0.08/0.30  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.08/0.30  fof(c_0_6, negated_conjecture, ~(![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(v2_funct_1(X2)=>![X3, X4]:(((r2_hidden(X3,X1)&r2_hidden(X4,X1))&k1_funct_1(X2,X3)=k1_funct_1(X2,X4))=>X3=X4)))), inference(assume_negation,[status(cth)],[t85_funct_2])).
% 0.08/0.30  fof(c_0_7, plain, ![X14, X15, X16, X17]:(~v1_funct_1(X17)|~v1_funct_2(X17,X14,X15)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))|(~v2_funct_1(X17)|~r2_hidden(X16,X14)|(X15=k1_xboole_0|k1_funct_1(k2_funct_1(X17),k1_funct_1(X17,X16))=X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_funct_2])])).
% 0.08/0.30  fof(c_0_8, negated_conjecture, (((v1_funct_1(esk2_0)&v1_funct_2(esk2_0,esk1_0,esk1_0))&m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))))&(v2_funct_1(esk2_0)&(((r2_hidden(esk3_0,esk1_0)&r2_hidden(esk4_0,esk1_0))&k1_funct_1(esk2_0,esk3_0)=k1_funct_1(esk2_0,esk4_0))&esk3_0!=esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.08/0.30  fof(c_0_9, plain, ![X5, X6, X7]:(~r2_hidden(X5,X6)|~m1_subset_1(X6,k1_zfmisc_1(X7))|~v1_xboole_0(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.08/0.30  fof(c_0_10, plain, ![X8, X9, X10]:(~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))|m1_subset_1(k1_relset_1(X8,X9,X10),k1_zfmisc_1(X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).
% 0.08/0.31  cnf(c_0_11, plain, (X3=k1_xboole_0|k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X4))=X4|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v2_funct_1(X1)|~r2_hidden(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.08/0.31  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.08/0.31  cnf(c_0_13, negated_conjecture, (v2_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.08/0.31  cnf(c_0_14, negated_conjecture, (v1_funct_2(esk2_0,esk1_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.08/0.31  cnf(c_0_15, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.08/0.31  cnf(c_0_16, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.08/0.31  cnf(c_0_17, plain, (m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.08/0.31  fof(c_0_18, plain, ![X18, X19]:(~v1_funct_1(X19)|~v1_funct_2(X19,X18,X18)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X18,X18)))|k1_relset_1(X18,X18,X19)=X18), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_funct_2])])).
% 0.08/0.31  cnf(c_0_19, negated_conjecture, (k1_funct_1(k2_funct_1(esk2_0),k1_funct_1(esk2_0,X1))=X1|esk1_0=k1_xboole_0|~r2_hidden(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13]), c_0_14]), c_0_15])])).
% 0.08/0.31  cnf(c_0_20, negated_conjecture, (r2_hidden(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.08/0.31  cnf(c_0_21, negated_conjecture, (k1_funct_1(esk2_0,esk3_0)=k1_funct_1(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.08/0.31  cnf(c_0_22, negated_conjecture, (r2_hidden(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.08/0.31  cnf(c_0_23, plain, (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,k1_relset_1(X2,X3,X1))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.08/0.31  cnf(c_0_24, plain, (k1_relset_1(X2,X2,X1)=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.08/0.31  cnf(c_0_25, negated_conjecture, (k1_funct_1(k2_funct_1(esk2_0),k1_funct_1(esk2_0,esk3_0))=esk4_0|esk1_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])).
% 0.08/0.31  cnf(c_0_26, negated_conjecture, (k1_funct_1(k2_funct_1(esk2_0),k1_funct_1(esk2_0,esk3_0))=esk3_0|esk1_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_19, c_0_22])).
% 0.08/0.31  cnf(c_0_27, negated_conjecture, (esk3_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.08/0.31  cnf(c_0_28, plain, (~v1_funct_2(X1,X2,X2)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))|~r2_hidden(X3,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.08/0.31  cnf(c_0_29, negated_conjecture, (esk1_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])).
% 0.08/0.31  cnf(c_0_30, negated_conjecture, (~r2_hidden(X1,esk1_0)|~v1_xboole_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_12]), c_0_14]), c_0_15])])).
% 0.08/0.31  cnf(c_0_31, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.08/0.31  cnf(c_0_32, negated_conjecture, (r2_hidden(esk4_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_20, c_0_29])).
% 0.08/0.31  cnf(c_0_33, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_29]), c_0_29]), c_0_31])])).
% 0.08/0.31  cnf(c_0_34, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_32, c_0_33]), ['proof']).
% 0.08/0.31  # SZS output end CNFRefutation
% 0.08/0.31  # Proof object total steps             : 35
% 0.08/0.31  # Proof object clause steps            : 23
% 0.08/0.31  # Proof object formula steps           : 12
% 0.08/0.31  # Proof object conjectures             : 19
% 0.08/0.31  # Proof object clause conjectures      : 16
% 0.08/0.31  # Proof object formula conjectures     : 3
% 0.08/0.31  # Proof object initial clauses used    : 13
% 0.08/0.31  # Proof object initial formulas used   : 6
% 0.08/0.31  # Proof object generating inferences   : 7
% 0.08/0.31  # Proof object simplifying inferences  : 15
% 0.08/0.31  # Training examples: 0 positive, 0 negative
% 0.08/0.31  # Parsed axioms                        : 7
% 0.08/0.31  # Removed by relevancy pruning/SinE    : 0
% 0.08/0.31  # Initial clauses                      : 14
% 0.08/0.31  # Removed in clause preprocessing      : 0
% 0.08/0.31  # Initial clauses in saturation        : 14
% 0.08/0.31  # Processed clauses                    : 50
% 0.08/0.31  # ...of these trivial                  : 0
% 0.08/0.31  # ...subsumed                          : 3
% 0.08/0.31  # ...remaining for further processing  : 47
% 0.08/0.31  # Other redundant clauses eliminated   : 0
% 0.08/0.31  # Clauses deleted for lack of memory   : 0
% 0.08/0.31  # Backward-subsumed                    : 0
% 0.08/0.31  # Backward-rewritten                   : 14
% 0.08/0.31  # Generated clauses                    : 32
% 0.08/0.31  # ...of the previous two non-trivial   : 41
% 0.08/0.31  # Contextual simplify-reflections      : 0
% 0.08/0.31  # Paramodulations                      : 31
% 0.08/0.31  # Factorizations                       : 0
% 0.08/0.31  # Equation resolutions                 : 0
% 0.08/0.31  # Propositional unsat checks           : 0
% 0.08/0.31  #    Propositional check models        : 0
% 0.08/0.31  #    Propositional check unsatisfiable : 0
% 0.08/0.31  #    Propositional clauses             : 0
% 0.08/0.31  #    Propositional clauses after purity: 0
% 0.08/0.31  #    Propositional unsat core size     : 0
% 0.08/0.31  #    Propositional preprocessing time  : 0.000
% 0.08/0.31  #    Propositional encoding time       : 0.000
% 0.08/0.31  #    Propositional solver time         : 0.000
% 0.08/0.31  #    Success case prop preproc time    : 0.000
% 0.08/0.31  #    Success case prop encoding time   : 0.000
% 0.08/0.31  #    Success case prop solver time     : 0.000
% 0.08/0.31  # Current number of processed clauses  : 18
% 0.08/0.31  #    Positive orientable unit clauses  : 5
% 0.08/0.31  #    Positive unorientable unit clauses: 0
% 0.08/0.31  #    Negative unit clauses             : 2
% 0.08/0.31  #    Non-unit-clauses                  : 11
% 0.08/0.31  # Current number of unprocessed clauses: 19
% 0.08/0.31  # ...number of literals in the above   : 54
% 0.08/0.31  # Current number of archived formulas  : 0
% 0.08/0.31  # Current number of archived clauses   : 29
% 0.08/0.31  # Clause-clause subsumption calls (NU) : 192
% 0.08/0.31  # Rec. Clause-clause subsumption calls : 48
% 0.08/0.31  # Non-unit clause-clause subsumptions  : 3
% 0.08/0.31  # Unit Clause-clause subsumption calls : 11
% 0.08/0.31  # Rewrite failures with RHS unbound    : 0
% 0.08/0.31  # BW rewrite match attempts            : 1
% 0.08/0.31  # BW rewrite match successes           : 1
% 0.08/0.31  # Condensation attempts                : 0
% 0.08/0.31  # Condensation successes               : 0
% 0.08/0.31  # Termbank termtop insertions          : 1691
% 0.08/0.31  
% 0.08/0.31  # -------------------------------------------------
% 0.08/0.31  # User time                : 0.026 s
% 0.08/0.31  # System time              : 0.003 s
% 0.08/0.31  # Total time               : 0.029 s
% 0.08/0.31  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
