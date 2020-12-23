%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:53 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 148 expanded)
%              Number of clauses        :   34 (  59 expanded)
%              Number of leaves         :   11 (  37 expanded)
%              Depth                    :   14
%              Number of atoms          :  132 ( 416 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t49_tops_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => r1_tarski(k4_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3)),k1_tops_1(X1,k4_subset_1(u1_struct_0(X1),X2,X3))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tops_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t48_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r1_tarski(X2,X3)
               => r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => r1_tarski(k4_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3)),k1_tops_1(X1,k4_subset_1(u1_struct_0(X1),X2,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t49_tops_1])).

fof(c_0_12,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ~ r1_tarski(k4_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)),k1_tops_1(esk1_0,k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_13,plain,(
    ! [X19,X20,X21] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(X19))
      | ~ m1_subset_1(X21,k1_zfmisc_1(X19))
      | k4_subset_1(X19,X20,X21) = k2_xboole_0(X20,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_14,negated_conjecture,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)),k1_tops_1(esk1_0,k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)),k1_tops_1(esk1_0,k2_xboole_0(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17])])).

fof(c_0_19,plain,(
    ! [X16,X17,X18] :
      ( ~ r1_tarski(X16,X17)
      | ~ r1_tarski(X18,X17)
      | r1_tarski(k2_xboole_0(X16,X18),X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

fof(c_0_20,plain,(
    ! [X11,X12,X13] :
      ( ~ r1_tarski(k4_xboole_0(X11,X12),X13)
      | r1_tarski(X11,k2_xboole_0(X12,X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

fof(c_0_21,plain,(
    ! [X9,X10] : r1_tarski(k4_xboole_0(X9,X10),X9) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_22,negated_conjecture,
    ( ~ m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k2_xboole_0(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)),k1_tops_1(esk1_0,k2_xboole_0(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_15])).

cnf(c_0_23,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_24,plain,(
    ! [X26,X27,X28] :
      ( ~ l1_pre_topc(X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
      | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
      | ~ r1_tarski(X27,X28)
      | r1_tarski(k1_tops_1(X26,X27),k1_tops_1(X26,X28)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( ~ m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,esk3_0),k1_tops_1(esk1_0,k2_xboole_0(esk2_0,esk3_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,k2_xboole_0(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_31,plain,(
    ! [X14,X15] : r1_tarski(X14,k2_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_32,negated_conjecture,
    ( ~ m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,k2_xboole_0(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_16]),c_0_30])])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_34,plain,(
    ! [X22,X23] :
      ( ( ~ m1_subset_1(X22,k1_zfmisc_1(X23))
        | r1_tarski(X22,X23) )
      & ( ~ r1_tarski(X22,X23)
        | m1_subset_1(X22,k1_zfmisc_1(X23)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_35,negated_conjecture,
    ( ~ m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_28]),c_0_29]),c_0_17]),c_0_33])])).

cnf(c_0_36,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( ~ m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k2_xboole_0(esk2_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_38,plain,(
    ! [X4,X5,X6] :
      ( ~ r1_tarski(k2_xboole_0(X4,X5),X6)
      | r1_tarski(X4,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

fof(c_0_39,plain,(
    ! [X7,X8] :
      ( ~ r1_tarski(X7,X8)
      | k2_xboole_0(X7,X8) = X8 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_40,negated_conjecture,
    ( ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k2_xboole_0(esk2_0,esk3_0),u1_struct_0(esk1_0))
    | ~ r1_tarski(k1_tops_1(esk1_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_36])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_43,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_44,plain,(
    ! [X24,X25] :
      ( ~ l1_pre_topc(X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
      | r1_tarski(k1_tops_1(X24,X25),X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

cnf(c_0_45,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(esk2_0,esk3_0),u1_struct_0(esk1_0))
    | ~ r1_tarski(k1_tops_1(esk1_0,esk3_0),u1_struct_0(esk1_0))
    | ~ r1_tarski(k1_tops_1(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(esk3_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_16])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(esk2_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_17])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(esk1_0,esk3_0),u1_struct_0(esk1_0))
    | ~ r1_tarski(k1_tops_1(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_23]),c_0_46]),c_0_47])])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_16]),c_0_29])])).

cnf(c_0_53,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_17]),c_0_29])])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:06:45 EST 2020
% 0.18/0.33  % CPUTime    : 
% 0.18/0.34  # Version: 2.5pre002
% 0.18/0.34  # No SInE strategy applied
% 0.18/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.18/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.18/0.38  #
% 0.18/0.38  # Preprocessing time       : 0.039 s
% 0.18/0.38  # Presaturation interreduction done
% 0.18/0.38  
% 0.18/0.38  # Proof found!
% 0.18/0.38  # SZS status Theorem
% 0.18/0.38  # SZS output start CNFRefutation
% 0.18/0.38  fof(t49_tops_1, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k4_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3)),k1_tops_1(X1,k4_subset_1(u1_struct_0(X1),X2,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_tops_1)).
% 0.18/0.38  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.18/0.38  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 0.18/0.38  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 0.18/0.38  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.18/0.38  fof(t48_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 0.18/0.38  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.18/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.18/0.38  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.18/0.38  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.18/0.38  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 0.18/0.38  fof(c_0_11, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k4_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3)),k1_tops_1(X1,k4_subset_1(u1_struct_0(X1),X2,X3))))))), inference(assume_negation,[status(cth)],[t49_tops_1])).
% 0.18/0.38  fof(c_0_12, negated_conjecture, (l1_pre_topc(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&~r1_tarski(k4_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)),k1_tops_1(esk1_0,k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.18/0.38  fof(c_0_13, plain, ![X19, X20, X21]:(~m1_subset_1(X20,k1_zfmisc_1(X19))|~m1_subset_1(X21,k1_zfmisc_1(X19))|k4_subset_1(X19,X20,X21)=k2_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.18/0.38  cnf(c_0_14, negated_conjecture, (~r1_tarski(k4_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)),k1_tops_1(esk1_0,k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.38  cnf(c_0_15, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.38  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.38  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.38  cnf(c_0_18, negated_conjecture, (~r1_tarski(k4_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)),k1_tops_1(esk1_0,k2_xboole_0(esk2_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_17])])).
% 0.18/0.38  fof(c_0_19, plain, ![X16, X17, X18]:(~r1_tarski(X16,X17)|~r1_tarski(X18,X17)|r1_tarski(k2_xboole_0(X16,X18),X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 0.18/0.38  fof(c_0_20, plain, ![X11, X12, X13]:(~r1_tarski(k4_xboole_0(X11,X12),X13)|r1_tarski(X11,k2_xboole_0(X12,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 0.18/0.38  fof(c_0_21, plain, ![X9, X10]:r1_tarski(k4_xboole_0(X9,X10),X9), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.18/0.38  cnf(c_0_22, negated_conjecture, (~m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k2_xboole_0(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)),k1_tops_1(esk1_0,k2_xboole_0(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_18, c_0_15])).
% 0.18/0.38  cnf(c_0_23, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.38  fof(c_0_24, plain, ![X26, X27, X28]:(~l1_pre_topc(X26)|(~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|(~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|(~r1_tarski(X27,X28)|r1_tarski(k1_tops_1(X26,X27),k1_tops_1(X26,X28)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).
% 0.18/0.38  cnf(c_0_25, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.38  cnf(c_0_26, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.38  cnf(c_0_27, negated_conjecture, (~m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k1_tops_1(esk1_0,esk3_0),k1_tops_1(esk1_0,k2_xboole_0(esk2_0,esk3_0)))|~r1_tarski(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,k2_xboole_0(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.18/0.38  cnf(c_0_28, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.38  cnf(c_0_29, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.38  cnf(c_0_30, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.18/0.38  fof(c_0_31, plain, ![X14, X15]:r1_tarski(X14,k2_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.18/0.38  cnf(c_0_32, negated_conjecture, (~m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k2_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,k2_xboole_0(esk2_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_16]), c_0_30])])).
% 0.18/0.38  cnf(c_0_33, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.18/0.38  fof(c_0_34, plain, ![X22, X23]:((~m1_subset_1(X22,k1_zfmisc_1(X23))|r1_tarski(X22,X23))&(~r1_tarski(X22,X23)|m1_subset_1(X22,k1_zfmisc_1(X23)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.18/0.38  cnf(c_0_35, negated_conjecture, (~m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k2_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_28]), c_0_29]), c_0_17]), c_0_33])])).
% 0.18/0.38  cnf(c_0_36, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.38  cnf(c_0_37, negated_conjecture, (~m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k2_xboole_0(esk2_0,esk3_0),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.18/0.38  fof(c_0_38, plain, ![X4, X5, X6]:(~r1_tarski(k2_xboole_0(X4,X5),X6)|r1_tarski(X4,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.18/0.38  fof(c_0_39, plain, ![X7, X8]:(~r1_tarski(X7,X8)|k2_xboole_0(X7,X8)=X8), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.18/0.38  cnf(c_0_40, negated_conjecture, (~m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k2_xboole_0(esk2_0,esk3_0),u1_struct_0(esk1_0))|~r1_tarski(k1_tops_1(esk1_0,esk3_0),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_37, c_0_36])).
% 0.18/0.38  cnf(c_0_41, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.38  cnf(c_0_42, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.18/0.38  cnf(c_0_43, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.18/0.38  fof(c_0_44, plain, ![X24, X25]:(~l1_pre_topc(X24)|(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|r1_tarski(k1_tops_1(X24,X25),X25))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 0.18/0.38  cnf(c_0_45, negated_conjecture, (~r1_tarski(k2_xboole_0(esk2_0,esk3_0),u1_struct_0(esk1_0))|~r1_tarski(k1_tops_1(esk1_0,esk3_0),u1_struct_0(esk1_0))|~r1_tarski(k1_tops_1(esk1_0,esk2_0),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_40, c_0_36])).
% 0.18/0.38  cnf(c_0_46, negated_conjecture, (r1_tarski(esk3_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_41, c_0_16])).
% 0.18/0.38  cnf(c_0_47, negated_conjecture, (r1_tarski(esk2_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_41, c_0_17])).
% 0.18/0.38  cnf(c_0_48, plain, (r1_tarski(X1,X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.18/0.38  cnf(c_0_49, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.18/0.38  cnf(c_0_50, negated_conjecture, (~r1_tarski(k1_tops_1(esk1_0,esk3_0),u1_struct_0(esk1_0))|~r1_tarski(k1_tops_1(esk1_0,esk2_0),u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_23]), c_0_46]), c_0_47])])).
% 0.18/0.38  cnf(c_0_51, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_48, c_0_46])).
% 0.18/0.38  cnf(c_0_52, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_16]), c_0_29])])).
% 0.18/0.38  cnf(c_0_53, negated_conjecture, (~r1_tarski(k1_tops_1(esk1_0,esk2_0),u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])])).
% 0.18/0.38  cnf(c_0_54, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_48, c_0_47])).
% 0.18/0.38  cnf(c_0_55, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_17]), c_0_29])])).
% 0.18/0.38  cnf(c_0_56, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])]), ['proof']).
% 0.18/0.38  # SZS output end CNFRefutation
% 0.18/0.38  # Proof object total steps             : 57
% 0.18/0.38  # Proof object clause steps            : 34
% 0.18/0.38  # Proof object formula steps           : 23
% 0.18/0.38  # Proof object conjectures             : 24
% 0.18/0.38  # Proof object clause conjectures      : 21
% 0.18/0.38  # Proof object formula conjectures     : 3
% 0.18/0.38  # Proof object initial clauses used    : 15
% 0.18/0.38  # Proof object initial formulas used   : 11
% 0.18/0.38  # Proof object generating inferences   : 19
% 0.18/0.38  # Proof object simplifying inferences  : 22
% 0.18/0.38  # Training examples: 0 positive, 0 negative
% 0.18/0.38  # Parsed axioms                        : 11
% 0.18/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.38  # Initial clauses                      : 15
% 0.18/0.38  # Removed in clause preprocessing      : 0
% 0.18/0.38  # Initial clauses in saturation        : 15
% 0.18/0.38  # Processed clauses                    : 86
% 0.18/0.38  # ...of these trivial                  : 1
% 0.18/0.38  # ...subsumed                          : 10
% 0.18/0.38  # ...remaining for further processing  : 75
% 0.18/0.38  # Other redundant clauses eliminated   : 0
% 0.18/0.38  # Clauses deleted for lack of memory   : 0
% 0.18/0.38  # Backward-subsumed                    : 7
% 0.18/0.38  # Backward-rewritten                   : 5
% 0.18/0.38  # Generated clauses                    : 119
% 0.18/0.38  # ...of the previous two non-trivial   : 105
% 0.18/0.38  # Contextual simplify-reflections      : 2
% 0.18/0.38  # Paramodulations                      : 119
% 0.18/0.38  # Factorizations                       : 0
% 0.18/0.38  # Equation resolutions                 : 0
% 0.18/0.38  # Propositional unsat checks           : 0
% 0.18/0.38  #    Propositional check models        : 0
% 0.18/0.38  #    Propositional check unsatisfiable : 0
% 0.18/0.38  #    Propositional clauses             : 0
% 0.18/0.38  #    Propositional clauses after purity: 0
% 0.18/0.38  #    Propositional unsat core size     : 0
% 0.18/0.38  #    Propositional preprocessing time  : 0.000
% 0.18/0.38  #    Propositional encoding time       : 0.000
% 0.18/0.38  #    Propositional solver time         : 0.000
% 0.18/0.38  #    Success case prop preproc time    : 0.000
% 0.18/0.38  #    Success case prop encoding time   : 0.000
% 0.18/0.38  #    Success case prop solver time     : 0.000
% 0.18/0.38  # Current number of processed clauses  : 48
% 0.18/0.38  #    Positive orientable unit clauses  : 16
% 0.18/0.38  #    Positive unorientable unit clauses: 0
% 0.18/0.38  #    Negative unit clauses             : 4
% 0.18/0.38  #    Non-unit-clauses                  : 28
% 0.18/0.38  # Current number of unprocessed clauses: 47
% 0.18/0.38  # ...number of literals in the above   : 106
% 0.18/0.38  # Current number of archived formulas  : 0
% 0.18/0.38  # Current number of archived clauses   : 27
% 0.18/0.38  # Clause-clause subsumption calls (NU) : 458
% 0.18/0.38  # Rec. Clause-clause subsumption calls : 250
% 0.18/0.38  # Non-unit clause-clause subsumptions  : 14
% 0.18/0.38  # Unit Clause-clause subsumption calls : 52
% 0.18/0.38  # Rewrite failures with RHS unbound    : 0
% 0.18/0.38  # BW rewrite match attempts            : 35
% 0.18/0.38  # BW rewrite match successes           : 5
% 0.18/0.38  # Condensation attempts                : 0
% 0.18/0.38  # Condensation successes               : 0
% 0.18/0.38  # Termbank termtop insertions          : 2915
% 0.18/0.38  
% 0.18/0.38  # -------------------------------------------------
% 0.18/0.38  # User time                : 0.046 s
% 0.18/0.38  # System time              : 0.001 s
% 0.18/0.38  # Total time               : 0.047 s
% 0.18/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
