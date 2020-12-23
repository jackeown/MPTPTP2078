%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:13:25 EST 2020

% Result     : Theorem 18.06s
% Output     : CNFRefutation 18.06s
% Verified   : 
% Statistics : Number of formulae       :   48 (  75 expanded)
%              Number of clauses        :   25 (  29 expanded)
%              Number of leaves         :   11 (  19 expanded)
%              Depth                    :    9
%              Number of atoms          :  133 ( 253 expanded)
%              Number of equality atoms :   28 (  49 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t95_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k3_tarski(X1),k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(t99_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(redefinition_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k5_setfam_1(X1,X2) = k3_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(t42_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                 => ( r1_tarski(X2,k5_setfam_1(u1_struct_0(X1),X4))
                   => r1_tarski(k9_subset_1(u1_struct_0(X1),X2,X3),k5_setfam_1(u1_struct_0(k1_pre_topc(X1,X3)),k1_tops_2(X1,X3,X4))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_tops_2)).

fof(t43_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ( r1_tarski(X2,k5_setfam_1(u1_struct_0(X1),X3))
               => X2 = k5_setfam_1(u1_struct_0(k1_pre_topc(X1,X2)),k1_tops_2(X1,X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_2)).

fof(dt_k1_tops_2,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
     => m1_subset_1(k1_tops_2(X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2))))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t29_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => u1_struct_0(k1_pre_topc(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

fof(c_0_11,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | r1_tarski(k3_tarski(X8),k3_tarski(X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).

fof(c_0_12,plain,(
    ! [X10] : k3_tarski(k1_zfmisc_1(X10)) = X10 ),
    inference(variable_rename,[status(thm)],[t99_zfmisc_1])).

fof(c_0_13,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_14,plain,
    ( r1_tarski(k3_tarski(X1),k3_tarski(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X5] : k3_xboole_0(X5,X5) = X5 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_17,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(X14))
      | k9_subset_1(X14,X15,X16) = k3_xboole_0(X15,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_18,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r1_tarski(k3_tarski(X1),X2)
    | ~ r1_tarski(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_20,plain,(
    ! [X17,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17)))
      | k5_setfam_1(X17,X18) = k3_tarski(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).

fof(c_0_21,plain,(
    ! [X26,X27,X28,X29] :
      ( ~ l1_pre_topc(X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
      | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
      | ~ m1_subset_1(X29,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26))))
      | ~ r1_tarski(X27,k5_setfam_1(u1_struct_0(X26),X29))
      | r1_tarski(k9_subset_1(u1_struct_0(X26),X27,X28),k5_setfam_1(u1_struct_0(k1_pre_topc(X26,X28)),k1_tops_2(X26,X28,X29))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t42_tops_2])])])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
               => ( r1_tarski(X2,k5_setfam_1(u1_struct_0(X1),X3))
                 => X2 = k5_setfam_1(u1_struct_0(k1_pre_topc(X1,X2)),k1_tops_2(X1,X2,X3)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t43_tops_2])).

cnf(c_0_25,plain,
    ( X1 = k3_tarski(X2)
    | ~ r1_tarski(X1,k3_tarski(X2))
    | ~ r1_tarski(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( k5_setfam_1(X2,X1) = k3_tarski(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(X1),X2,X3),k5_setfam_1(u1_struct_0(k1_pre_topc(X1,X3)),k1_tops_2(X1,X3,X4)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(X2,k5_setfam_1(u1_struct_0(X1),X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k9_subset_1(X1,X2,X2) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_29,plain,(
    ! [X23,X24,X25] :
      ( ~ l1_pre_topc(X23)
      | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
      | ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))
      | m1_subset_1(k1_tops_2(X23,X24,X25),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X23,X24))))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_2])])).

fof(c_0_30,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    & r1_tarski(esk2_0,k5_setfam_1(u1_struct_0(esk1_0),esk3_0))
    & esk2_0 != k5_setfam_1(u1_struct_0(k1_pre_topc(esk1_0,esk2_0)),k1_tops_2(esk1_0,esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

cnf(c_0_31,plain,
    ( X1 = k5_setfam_1(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ r1_tarski(X1,k5_setfam_1(X2,X3))
    | ~ r1_tarski(X3,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X2,X1)),k1_tops_2(X2,X1,X3)))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X1,k5_setfam_1(u1_struct_0(X2),X3)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( m1_subset_1(k1_tops_2(X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( esk2_0 != k5_setfam_1(u1_struct_0(k1_pre_topc(esk1_0,esk2_0)),k1_tops_2(esk1_0,esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,plain,
    ( k5_setfam_1(u1_struct_0(k1_pre_topc(X1,X2)),k1_tops_2(X1,X2,X3)) = X2
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k1_tops_2(X1,X2,X3),k1_zfmisc_1(X2))
    | ~ r1_tarski(X2,k5_setfam_1(u1_struct_0(X1),X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(esk2_0,k5_setfam_1(u1_struct_0(esk1_0),esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_40,plain,(
    ! [X19,X20] :
      ( ( ~ m1_subset_1(X19,k1_zfmisc_1(X20))
        | r1_tarski(X19,X20) )
      & ( ~ r1_tarski(X19,X20)
        | m1_subset_1(X19,k1_zfmisc_1(X20)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_41,plain,(
    ! [X21,X22] :
      ( ~ l1_pre_topc(X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
      | u1_struct_0(k1_pre_topc(X21,X22)) = X22 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_pre_topc])])])).

cnf(c_0_42,negated_conjecture,
    ( ~ r1_tarski(k1_tops_2(esk1_0,esk2_0,esk3_0),k1_zfmisc_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_44,plain,
    ( u1_struct_0(k1_pre_topc(X1,X2)) = X2
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( ~ m1_subset_1(k1_tops_2(esk1_0,esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_46,plain,
    ( m1_subset_1(k1_tops_2(X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_36]),c_0_37]),c_0_38])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:33:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 18.06/18.23  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 18.06/18.23  # and selection function SelectComplexExceptUniqMaxHorn.
% 18.06/18.23  #
% 18.06/18.23  # Preprocessing time       : 0.028 s
% 18.06/18.23  # Presaturation interreduction done
% 18.06/18.23  
% 18.06/18.23  # Proof found!
% 18.06/18.23  # SZS status Theorem
% 18.06/18.23  # SZS output start CNFRefutation
% 18.06/18.23  fof(t95_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k3_tarski(X1),k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 18.06/18.23  fof(t99_zfmisc_1, axiom, ![X1]:k3_tarski(k1_zfmisc_1(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 18.06/18.23  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 18.06/18.23  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 18.06/18.23  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 18.06/18.23  fof(redefinition_k5_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k5_setfam_1(X1,X2)=k3_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 18.06/18.23  fof(t42_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,k5_setfam_1(u1_struct_0(X1),X4))=>r1_tarski(k9_subset_1(u1_struct_0(X1),X2,X3),k5_setfam_1(u1_struct_0(k1_pre_topc(X1,X3)),k1_tops_2(X1,X3,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_tops_2)).
% 18.06/18.23  fof(t43_tops_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,k5_setfam_1(u1_struct_0(X1),X3))=>X2=k5_setfam_1(u1_struct_0(k1_pre_topc(X1,X2)),k1_tops_2(X1,X2,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tops_2)).
% 18.06/18.23  fof(dt_k1_tops_2, axiom, ![X1, X2, X3]:(((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))))=>m1_subset_1(k1_tops_2(X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_2)).
% 18.06/18.23  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 18.06/18.23  fof(t29_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>u1_struct_0(k1_pre_topc(X1,X2))=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_pre_topc)).
% 18.06/18.23  fof(c_0_11, plain, ![X8, X9]:(~r1_tarski(X8,X9)|r1_tarski(k3_tarski(X8),k3_tarski(X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).
% 18.06/18.23  fof(c_0_12, plain, ![X10]:k3_tarski(k1_zfmisc_1(X10))=X10, inference(variable_rename,[status(thm)],[t99_zfmisc_1])).
% 18.06/18.23  fof(c_0_13, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 18.06/18.23  cnf(c_0_14, plain, (r1_tarski(k3_tarski(X1),k3_tarski(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 18.06/18.23  cnf(c_0_15, plain, (k3_tarski(k1_zfmisc_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 18.06/18.23  fof(c_0_16, plain, ![X5]:k3_xboole_0(X5,X5)=X5, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 18.06/18.23  fof(c_0_17, plain, ![X14, X15, X16]:(~m1_subset_1(X16,k1_zfmisc_1(X14))|k9_subset_1(X14,X15,X16)=k3_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 18.06/18.23  cnf(c_0_18, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 18.06/18.23  cnf(c_0_19, plain, (r1_tarski(k3_tarski(X1),X2)|~r1_tarski(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 18.06/18.23  fof(c_0_20, plain, ![X17, X18]:(~m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17)))|k5_setfam_1(X17,X18)=k3_tarski(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).
% 18.06/18.23  fof(c_0_21, plain, ![X26, X27, X28, X29]:(~l1_pre_topc(X26)|(~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|(~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|(~m1_subset_1(X29,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26))))|(~r1_tarski(X27,k5_setfam_1(u1_struct_0(X26),X29))|r1_tarski(k9_subset_1(u1_struct_0(X26),X27,X28),k5_setfam_1(u1_struct_0(k1_pre_topc(X26,X28)),k1_tops_2(X26,X28,X29)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t42_tops_2])])])).
% 18.06/18.23  cnf(c_0_22, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 18.06/18.23  cnf(c_0_23, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 18.06/18.23  fof(c_0_24, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,k5_setfam_1(u1_struct_0(X1),X3))=>X2=k5_setfam_1(u1_struct_0(k1_pre_topc(X1,X2)),k1_tops_2(X1,X2,X3))))))), inference(assume_negation,[status(cth)],[t43_tops_2])).
% 18.06/18.23  cnf(c_0_25, plain, (X1=k3_tarski(X2)|~r1_tarski(X1,k3_tarski(X2))|~r1_tarski(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 18.06/18.23  cnf(c_0_26, plain, (k5_setfam_1(X2,X1)=k3_tarski(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 18.06/18.23  cnf(c_0_27, plain, (r1_tarski(k9_subset_1(u1_struct_0(X1),X2,X3),k5_setfam_1(u1_struct_0(k1_pre_topc(X1,X3)),k1_tops_2(X1,X3,X4)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~r1_tarski(X2,k5_setfam_1(u1_struct_0(X1),X4))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 18.06/18.23  cnf(c_0_28, plain, (k9_subset_1(X1,X2,X2)=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 18.06/18.23  fof(c_0_29, plain, ![X23, X24, X25]:(~l1_pre_topc(X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))|m1_subset_1(k1_tops_2(X23,X24,X25),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X23,X24)))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_2])])).
% 18.06/18.23  fof(c_0_30, negated_conjecture, (l1_pre_topc(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))&(r1_tarski(esk2_0,k5_setfam_1(u1_struct_0(esk1_0),esk3_0))&esk2_0!=k5_setfam_1(u1_struct_0(k1_pre_topc(esk1_0,esk2_0)),k1_tops_2(esk1_0,esk2_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).
% 18.06/18.23  cnf(c_0_31, plain, (X1=k5_setfam_1(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))|~r1_tarski(X1,k5_setfam_1(X2,X3))|~r1_tarski(X3,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 18.06/18.23  cnf(c_0_32, plain, (r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X2,X1)),k1_tops_2(X2,X1,X3)))|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X1,k5_setfam_1(u1_struct_0(X2),X3))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 18.06/18.23  cnf(c_0_33, plain, (m1_subset_1(k1_tops_2(X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 18.06/18.23  cnf(c_0_34, negated_conjecture, (esk2_0!=k5_setfam_1(u1_struct_0(k1_pre_topc(esk1_0,esk2_0)),k1_tops_2(esk1_0,esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 18.06/18.23  cnf(c_0_35, plain, (k5_setfam_1(u1_struct_0(k1_pre_topc(X1,X2)),k1_tops_2(X1,X2,X3))=X2|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k1_tops_2(X1,X2,X3),k1_zfmisc_1(X2))|~r1_tarski(X2,k5_setfam_1(u1_struct_0(X1),X3))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])).
% 18.06/18.23  cnf(c_0_36, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 18.06/18.23  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 18.06/18.23  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 18.06/18.23  cnf(c_0_39, negated_conjecture, (r1_tarski(esk2_0,k5_setfam_1(u1_struct_0(esk1_0),esk3_0))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 18.06/18.23  fof(c_0_40, plain, ![X19, X20]:((~m1_subset_1(X19,k1_zfmisc_1(X20))|r1_tarski(X19,X20))&(~r1_tarski(X19,X20)|m1_subset_1(X19,k1_zfmisc_1(X20)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 18.06/18.23  fof(c_0_41, plain, ![X21, X22]:(~l1_pre_topc(X21)|(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|u1_struct_0(k1_pre_topc(X21,X22))=X22)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_pre_topc])])])).
% 18.06/18.23  cnf(c_0_42, negated_conjecture, (~r1_tarski(k1_tops_2(esk1_0,esk2_0,esk3_0),k1_zfmisc_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])])).
% 18.06/18.23  cnf(c_0_43, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 18.06/18.23  cnf(c_0_44, plain, (u1_struct_0(k1_pre_topc(X1,X2))=X2|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 18.06/18.23  cnf(c_0_45, negated_conjecture, (~m1_subset_1(k1_tops_2(esk1_0,esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 18.06/18.23  cnf(c_0_46, plain, (m1_subset_1(k1_tops_2(X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X2)))|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_33, c_0_44])).
% 18.06/18.23  cnf(c_0_47, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_36]), c_0_37]), c_0_38])]), ['proof']).
% 18.06/18.23  # SZS output end CNFRefutation
% 18.06/18.23  # Proof object total steps             : 48
% 18.06/18.23  # Proof object clause steps            : 25
% 18.06/18.23  # Proof object formula steps           : 23
% 18.06/18.23  # Proof object conjectures             : 11
% 18.06/18.23  # Proof object clause conjectures      : 8
% 18.06/18.23  # Proof object formula conjectures     : 3
% 18.06/18.23  # Proof object initial clauses used    : 15
% 18.06/18.23  # Proof object initial formulas used   : 11
% 18.06/18.23  # Proof object generating inferences   : 10
% 18.06/18.23  # Proof object simplifying inferences  : 10
% 18.06/18.23  # Training examples: 0 positive, 0 negative
% 18.06/18.23  # Parsed axioms                        : 12
% 18.06/18.23  # Removed by relevancy pruning/SinE    : 0
% 18.06/18.23  # Initial clauses                      : 19
% 18.06/18.23  # Removed in clause preprocessing      : 0
% 18.06/18.23  # Initial clauses in saturation        : 19
% 18.06/18.23  # Processed clauses                    : 43459
% 18.06/18.23  # ...of these trivial                  : 25
% 18.06/18.23  # ...subsumed                          : 35134
% 18.06/18.23  # ...remaining for further processing  : 8300
% 18.06/18.23  # Other redundant clauses eliminated   : 2
% 18.06/18.23  # Clauses deleted for lack of memory   : 0
% 18.06/18.23  # Backward-subsumed                    : 475
% 18.06/18.23  # Backward-rewritten                   : 14
% 18.06/18.23  # Generated clauses                    : 2048322
% 18.06/18.23  # ...of the previous two non-trivial   : 1926950
% 18.06/18.23  # Contextual simplify-reflections      : 692
% 18.06/18.23  # Paramodulations                      : 2048320
% 18.06/18.23  # Factorizations                       : 0
% 18.06/18.23  # Equation resolutions                 : 2
% 18.06/18.23  # Propositional unsat checks           : 1
% 18.06/18.23  #    Propositional check models        : 1
% 18.06/18.23  #    Propositional check unsatisfiable : 0
% 18.06/18.23  #    Propositional clauses             : 0
% 18.06/18.23  #    Propositional clauses after purity: 0
% 18.06/18.23  #    Propositional unsat core size     : 0
% 18.06/18.23  #    Propositional preprocessing time  : 0.000
% 18.06/18.23  #    Propositional encoding time       : 0.284
% 18.06/18.23  #    Propositional solver time         : 0.021
% 18.06/18.23  #    Success case prop preproc time    : 0.000
% 18.06/18.23  #    Success case prop encoding time   : 0.000
% 18.06/18.23  #    Success case prop solver time     : 0.000
% 18.06/18.23  # Current number of processed clauses  : 7791
% 18.06/18.23  #    Positive orientable unit clauses  : 30
% 18.06/18.23  #    Positive unorientable unit clauses: 0
% 18.06/18.23  #    Negative unit clauses             : 5
% 18.06/18.23  #    Non-unit-clauses                  : 7756
% 18.06/18.23  # Current number of unprocessed clauses: 1882949
% 18.06/18.23  # ...number of literals in the above   : 15210688
% 18.06/18.23  # Current number of archived formulas  : 0
% 18.06/18.23  # Current number of archived clauses   : 507
% 18.06/18.23  # Clause-clause subsumption calls (NU) : 11478941
% 18.06/18.23  # Rec. Clause-clause subsumption calls : 737600
% 18.06/18.23  # Non-unit clause-clause subsumptions  : 36298
% 18.06/18.23  # Unit Clause-clause subsumption calls : 3959
% 18.06/18.23  # Rewrite failures with RHS unbound    : 0
% 18.06/18.23  # BW rewrite match attempts            : 60
% 18.06/18.23  # BW rewrite match successes           : 12
% 18.06/18.23  # Condensation attempts                : 0
% 18.06/18.23  # Condensation successes               : 0
% 18.06/18.23  # Termbank termtop insertions          : 58286660
% 18.10/18.32  
% 18.10/18.32  # -------------------------------------------------
% 18.10/18.32  # User time                : 17.196 s
% 18.10/18.32  # System time              : 0.776 s
% 18.10/18.32  # Total time               : 17.973 s
% 18.10/18.32  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
