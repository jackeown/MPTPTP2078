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
% DateTime   : Thu Dec  3 11:13:23 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   33 (  63 expanded)
%              Number of clauses        :   18 (  27 expanded)
%              Number of leaves         :    7 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :   68 ( 142 expanded)
%              Number of equality atoms :   20 (  34 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t38_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X3)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_tops_2)).

fof(t29_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => u1_struct_0(k1_pre_topc(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

fof(d10_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( ( X2 != k1_xboole_0
         => k8_setfam_1(X1,X2) = k6_setfam_1(X1,X2) )
        & ( X2 = k1_xboole_0
         => k8_setfam_1(X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(dt_k8_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k8_setfam_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X3)))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t38_tops_2])).

fof(c_0_8,plain,(
    ! [X18,X19] :
      ( ~ l1_pre_topc(X18)
      | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
      | u1_struct_0(k1_pre_topc(X18,X19)) = X19 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_pre_topc])])])).

fof(c_0_9,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ~ m1_subset_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(esk1_0,esk3_0)))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X11,X12] :
      ( ( X12 = k1_xboole_0
        | k8_setfam_1(X11,X12) = k6_setfam_1(X11,X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(X11))) )
      & ( X12 != k1_xboole_0
        | k8_setfam_1(X11,X12) = X11
        | ~ m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(X11))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_setfam_1])])])).

fof(c_0_11,plain,(
    ! [X10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X10)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_12,plain,
    ( u1_struct_0(k1_pre_topc(X1,X2)) = X2
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_15,plain,(
    ! [X7,X8,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(X7))
      | k9_subset_1(X7,X8,X9) = k3_xboole_0(X8,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_16,plain,(
    ! [X13,X14] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13)))
      | m1_subset_1(k8_setfam_1(X13,X14),k1_zfmisc_1(X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_setfam_1])])).

cnf(c_0_17,plain,
    ( k8_setfam_1(X2,X1) = X2
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(esk1_0,esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,negated_conjecture,
    ( u1_struct_0(k1_pre_topc(esk1_0,esk3_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])])).

cnf(c_0_21,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( m1_subset_1(k8_setfam_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k8_setfam_1(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_17]),c_0_18])])).

fof(c_0_24,plain,(
    ! [X4,X5,X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(X4))
      | m1_subset_1(k9_subset_1(X4,X5,X6),k1_zfmisc_1(X4)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

cnf(c_0_25,negated_conjecture,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),k1_zfmisc_1(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),X1,esk3_0) = k3_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_13])).

cnf(c_0_27,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_18]),c_0_23])).

cnf(c_0_28,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( ~ m1_subset_1(k3_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,plain,
    ( k9_subset_1(X1,X2,X1) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_27])).

cnf(c_0_31,plain,
    ( m1_subset_1(k9_subset_1(X1,X2,X1),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30]),c_0_31])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:34:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S03AN
% 0.12/0.38  # and selection function SelectComplex.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.026 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(t38_tops_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_tops_2)).
% 0.12/0.38  fof(t29_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>u1_struct_0(k1_pre_topc(X1,X2))=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_pre_topc)).
% 0.12/0.38  fof(d10_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>((X2!=k1_xboole_0=>k8_setfam_1(X1,X2)=k6_setfam_1(X1,X2))&(X2=k1_xboole_0=>k8_setfam_1(X1,X2)=X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 0.12/0.38  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.12/0.38  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.12/0.38  fof(dt_k8_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>m1_subset_1(k8_setfam_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 0.12/0.38  fof(dt_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 0.12/0.38  fof(c_0_7, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X3)))))))), inference(assume_negation,[status(cth)],[t38_tops_2])).
% 0.12/0.38  fof(c_0_8, plain, ![X18, X19]:(~l1_pre_topc(X18)|(~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|u1_struct_0(k1_pre_topc(X18,X19))=X19)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_pre_topc])])])).
% 0.12/0.38  fof(c_0_9, negated_conjecture, (l1_pre_topc(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&~m1_subset_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(esk1_0,esk3_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.12/0.38  fof(c_0_10, plain, ![X11, X12]:((X12=k1_xboole_0|k8_setfam_1(X11,X12)=k6_setfam_1(X11,X12)|~m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(X11))))&(X12!=k1_xboole_0|k8_setfam_1(X11,X12)=X11|~m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(X11))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_setfam_1])])])).
% 0.12/0.38  fof(c_0_11, plain, ![X10]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X10)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.12/0.38  cnf(c_0_12, plain, (u1_struct_0(k1_pre_topc(X1,X2))=X2|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.38  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.38  cnf(c_0_14, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.38  fof(c_0_15, plain, ![X7, X8, X9]:(~m1_subset_1(X9,k1_zfmisc_1(X7))|k9_subset_1(X7,X8,X9)=k3_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.12/0.38  fof(c_0_16, plain, ![X13, X14]:(~m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13)))|m1_subset_1(k8_setfam_1(X13,X14),k1_zfmisc_1(X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_setfam_1])])).
% 0.12/0.38  cnf(c_0_17, plain, (k8_setfam_1(X2,X1)=X2|X1!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.38  cnf(c_0_18, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  cnf(c_0_19, negated_conjecture, (~m1_subset_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(esk1_0,esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.38  cnf(c_0_20, negated_conjecture, (u1_struct_0(k1_pre_topc(esk1_0,esk3_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])])).
% 0.12/0.38  cnf(c_0_21, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.38  cnf(c_0_22, plain, (m1_subset_1(k8_setfam_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.38  cnf(c_0_23, plain, (k8_setfam_1(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_17]), c_0_18])])).
% 0.12/0.38  fof(c_0_24, plain, ![X4, X5, X6]:(~m1_subset_1(X6,k1_zfmisc_1(X4))|m1_subset_1(k9_subset_1(X4,X5,X6),k1_zfmisc_1(X4))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).
% 0.12/0.38  cnf(c_0_25, negated_conjecture, (~m1_subset_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),k1_zfmisc_1(esk3_0))), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.12/0.38  cnf(c_0_26, negated_conjecture, (k9_subset_1(u1_struct_0(esk1_0),X1,esk3_0)=k3_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_21, c_0_13])).
% 0.12/0.38  cnf(c_0_27, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_18]), c_0_23])).
% 0.12/0.38  cnf(c_0_28, plain, (m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.38  cnf(c_0_29, negated_conjecture, (~m1_subset_1(k3_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(esk3_0))), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.12/0.38  cnf(c_0_30, plain, (k9_subset_1(X1,X2,X1)=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_21, c_0_27])).
% 0.12/0.38  cnf(c_0_31, plain, (m1_subset_1(k9_subset_1(X1,X2,X1),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_28, c_0_27])).
% 0.12/0.38  cnf(c_0_32, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30]), c_0_31])]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 33
% 0.12/0.38  # Proof object clause steps            : 18
% 0.12/0.38  # Proof object formula steps           : 15
% 0.12/0.38  # Proof object conjectures             : 11
% 0.12/0.38  # Proof object clause conjectures      : 8
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 9
% 0.12/0.38  # Proof object initial formulas used   : 7
% 0.12/0.38  # Proof object generating inferences   : 5
% 0.12/0.38  # Proof object simplifying inferences  : 11
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 8
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 12
% 0.12/0.38  # Removed in clause preprocessing      : 0
% 0.12/0.38  # Initial clauses in saturation        : 12
% 0.12/0.38  # Processed clauses                    : 72
% 0.12/0.38  # ...of these trivial                  : 1
% 0.12/0.38  # ...subsumed                          : 2
% 0.12/0.38  # ...remaining for further processing  : 69
% 0.12/0.38  # Other redundant clauses eliminated   : 1
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 1
% 0.12/0.38  # Backward-rewritten                   : 23
% 0.12/0.38  # Generated clauses                    : 92
% 0.12/0.38  # ...of the previous two non-trivial   : 109
% 0.12/0.38  # Contextual simplify-reflections      : 0
% 0.12/0.38  # Paramodulations                      : 91
% 0.12/0.38  # Factorizations                       : 0
% 0.12/0.38  # Equation resolutions                 : 1
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 32
% 0.12/0.38  #    Positive orientable unit clauses  : 13
% 0.12/0.38  #    Positive unorientable unit clauses: 1
% 0.12/0.38  #    Negative unit clauses             : 0
% 0.12/0.38  #    Non-unit-clauses                  : 18
% 0.12/0.38  # Current number of unprocessed clauses: 42
% 0.12/0.38  # ...number of literals in the above   : 62
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 36
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 134
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 114
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 3
% 0.12/0.38  # Unit Clause-clause subsumption calls : 5
% 0.12/0.38  # Rewrite failures with RHS unbound    : 6
% 0.12/0.38  # BW rewrite match attempts            : 62
% 0.12/0.38  # BW rewrite match successes           : 21
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 2370
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.028 s
% 0.12/0.38  # System time              : 0.006 s
% 0.12/0.38  # Total time               : 0.034 s
% 0.12/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
