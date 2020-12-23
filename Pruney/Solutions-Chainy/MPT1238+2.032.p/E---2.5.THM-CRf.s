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
% DateTime   : Thu Dec  3 11:10:52 EST 2020

% Result     : Theorem 7.20s
% Output     : CNFRefutation 7.20s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 245 expanded)
%              Number of clauses        :   56 ( 112 expanded)
%              Number of leaves         :   11 (  58 expanded)
%              Depth                    :   14
%              Number of atoms          :  173 ( 638 expanded)
%              Number of equality atoms :   29 (  69 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t49_tops_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => r1_tarski(k4_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3)),k1_tops_1(X1,k4_subset_1(u1_struct_0(X1),X2,X3))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tops_1)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t48_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r1_tarski(X2,X3)
               => r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(c_0_11,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_12,plain,(
    ! [X14,X15] : r1_tarski(X14,k2_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => r1_tarski(k4_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3)),k1_tops_1(X1,k4_subset_1(u1_struct_0(X1),X2,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t49_tops_1])).

cnf(c_0_14,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X16,X17,X18] :
      ( ~ r1_tarski(X16,X17)
      | ~ r1_tarski(X18,X17)
      | r1_tarski(k2_xboole_0(X16,X18),X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_18,plain,(
    ! [X22,X23] :
      ( ( ~ m1_subset_1(X22,k1_zfmisc_1(X23))
        | r1_tarski(X22,X23) )
      & ( ~ r1_tarski(X22,X23)
        | m1_subset_1(X22,k1_zfmisc_1(X23)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ~ r1_tarski(k4_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)),k1_tops_1(esk1_0,k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_20,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(k2_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X24,X25] :
      ( ~ l1_pre_topc(X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
      | r1_tarski(k1_tops_1(X24,X25),X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

fof(c_0_26,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | r1_tarski(X6,k2_xboole_0(X8,X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk3_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_31,plain,(
    ! [X19,X20,X21] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(X19))
      | ~ m1_subset_1(X21,k1_zfmisc_1(X19))
      | k4_subset_1(X19,X20,X21) = k2_xboole_0(X20,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

fof(c_0_32,plain,(
    ! [X9,X10,X11] :
      ( ~ r1_tarski(k2_xboole_0(X9,X10),X11)
      | r1_tarski(X9,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(esk1_0),esk3_0) = u1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_35,plain,(
    ! [X12,X13] :
      ( ~ r1_tarski(X12,X13)
      | k2_xboole_0(X12,X13) = X13 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_24])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_44,plain,
    ( k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(k2_xboole_0(X1,X2),esk3_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( k2_xboole_0(k1_tops_1(esk1_0,esk3_0),esk3_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),X1,esk3_0) = k2_xboole_0(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_24])).

cnf(c_0_49,plain,
    ( k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3)
    | ~ r1_tarski(X3,X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_38])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_22])])).

cnf(c_0_51,negated_conjecture,
    ( k2_xboole_0(k1_tops_1(esk1_0,esk2_0),esk2_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_47])).

fof(c_0_52,plain,(
    ! [X26,X27,X28] :
      ( ~ l1_pre_topc(X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
      | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
      | ~ r1_tarski(X27,X28)
      | r1_tarski(k1_tops_1(X26,X27),k1_tops_1(X26,X28)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).

cnf(c_0_53,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(X2,X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_41,c_0_33])).

cnf(c_0_54,negated_conjecture,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)),k1_tops_1(esk1_0,k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_55,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0) = k2_xboole_0(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_43])).

cnf(c_0_56,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),X1,k1_tops_1(esk1_0,esk3_0)) = k2_xboole_0(X1,k1_tops_1(esk1_0,esk3_0))
    | ~ r1_tarski(X1,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk2_0),X1)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(esk2_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_43])).

cnf(c_0_59,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_60,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = X3
    | ~ r1_tarski(X2,X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_41,c_0_21])).

cnf(c_0_61,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X1,X3))) = k2_xboole_0(X2,k2_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_15])).

cnf(c_0_62,negated_conjecture,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)),k1_tops_1(esk1_0,k2_xboole_0(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_63,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)) = k2_xboole_0(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_59,c_0_30])).

cnf(c_0_65,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(X1,esk3_0),u1_struct_0(esk1_0)) = u1_struct_0(esk1_0)
    | ~ r1_tarski(X1,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_28])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(k2_xboole_0(X3,k2_xboole_0(X1,X4)),X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_61])).

cnf(c_0_67,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_41,c_0_22])).

cnf(c_0_68,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)),k1_tops_1(esk1_0,k2_xboole_0(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X2,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_64,c_0_38])).

cnf(c_0_70,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(esk2_0,esk3_0),u1_struct_0(esk1_0)) = u1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_58])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(k2_xboole_0(X3,X1),X2) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(esk1_0,esk3_0),k1_tops_1(esk1_0,k2_xboole_0(esk2_0,esk3_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,k2_xboole_0(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_21])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk3_0),k1_tops_1(esk1_0,X1))
    | ~ r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_24])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk2_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_70])).

cnf(c_0_75,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_22])).

cnf(c_0_76,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,k2_xboole_0(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74]),c_0_75])])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,X1))
    | ~ r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_43])).

cnf(c_0_78,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_74]),c_0_15])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:13:44 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 7.20/7.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S050I
% 7.20/7.37  # and selection function PSelectNewComplexExceptUniqMaxHorn.
% 7.20/7.37  #
% 7.20/7.37  # Preprocessing time       : 0.028 s
% 7.20/7.37  # Presaturation interreduction done
% 7.20/7.37  
% 7.20/7.37  # Proof found!
% 7.20/7.37  # SZS status Theorem
% 7.20/7.37  # SZS output start CNFRefutation
% 7.20/7.37  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.20/7.37  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.20/7.37  fof(t49_tops_1, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k4_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3)),k1_tops_1(X1,k4_subset_1(u1_struct_0(X1),X2,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tops_1)).
% 7.20/7.37  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 7.20/7.37  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.20/7.37  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 7.20/7.37  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 7.20/7.37  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 7.20/7.37  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 7.20/7.37  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 7.20/7.37  fof(t48_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 7.20/7.37  fof(c_0_11, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 7.20/7.37  fof(c_0_12, plain, ![X14, X15]:r1_tarski(X14,k2_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 7.20/7.37  fof(c_0_13, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k4_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3)),k1_tops_1(X1,k4_subset_1(u1_struct_0(X1),X2,X3))))))), inference(assume_negation,[status(cth)],[t49_tops_1])).
% 7.20/7.37  cnf(c_0_14, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 7.20/7.37  cnf(c_0_15, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 7.20/7.37  fof(c_0_16, plain, ![X16, X17, X18]:(~r1_tarski(X16,X17)|~r1_tarski(X18,X17)|r1_tarski(k2_xboole_0(X16,X18),X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 7.20/7.37  cnf(c_0_17, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 7.20/7.37  fof(c_0_18, plain, ![X22, X23]:((~m1_subset_1(X22,k1_zfmisc_1(X23))|r1_tarski(X22,X23))&(~r1_tarski(X22,X23)|m1_subset_1(X22,k1_zfmisc_1(X23)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 7.20/7.37  fof(c_0_19, negated_conjecture, (l1_pre_topc(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&~r1_tarski(k4_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)),k1_tops_1(esk1_0,k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 7.20/7.37  cnf(c_0_20, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(k2_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 7.20/7.37  cnf(c_0_21, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 7.20/7.37  cnf(c_0_22, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_17])).
% 7.20/7.37  cnf(c_0_23, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 7.20/7.37  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 7.20/7.37  fof(c_0_25, plain, ![X24, X25]:(~l1_pre_topc(X24)|(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|r1_tarski(k1_tops_1(X24,X25),X25))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 7.20/7.37  fof(c_0_26, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|r1_tarski(X6,k2_xboole_0(X8,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 7.20/7.37  cnf(c_0_27, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])])).
% 7.20/7.37  cnf(c_0_28, negated_conjecture, (r1_tarski(esk3_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 7.20/7.37  cnf(c_0_29, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 7.20/7.37  cnf(c_0_30, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 7.20/7.37  fof(c_0_31, plain, ![X19, X20, X21]:(~m1_subset_1(X20,k1_zfmisc_1(X19))|~m1_subset_1(X21,k1_zfmisc_1(X19))|k4_subset_1(X19,X20,X21)=k2_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 7.20/7.37  fof(c_0_32, plain, ![X9, X10, X11]:(~r1_tarski(k2_xboole_0(X9,X10),X11)|r1_tarski(X9,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 7.20/7.37  cnf(c_0_33, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 7.20/7.37  cnf(c_0_34, negated_conjecture, (k2_xboole_0(u1_struct_0(esk1_0),esk3_0)=u1_struct_0(esk1_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 7.20/7.37  fof(c_0_35, plain, ![X12, X13]:(~r1_tarski(X12,X13)|k2_xboole_0(X12,X13)=X13), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 7.20/7.37  cnf(c_0_36, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,X1),X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 7.20/7.37  cnf(c_0_37, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 7.20/7.37  cnf(c_0_38, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 7.20/7.37  cnf(c_0_39, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 7.20/7.37  cnf(c_0_40, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 7.20/7.37  cnf(c_0_41, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 7.20/7.37  cnf(c_0_42, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_36, c_0_24])).
% 7.20/7.37  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 7.20/7.37  cnf(c_0_44, plain, (k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 7.20/7.37  cnf(c_0_45, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(k2_xboole_0(X1,X2),esk3_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 7.20/7.37  cnf(c_0_46, negated_conjecture, (k2_xboole_0(k1_tops_1(esk1_0,esk3_0),esk3_0)=esk3_0), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 7.20/7.37  cnf(c_0_47, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_36, c_0_43])).
% 7.20/7.37  cnf(c_0_48, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),X1,esk3_0)=k2_xboole_0(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_37, c_0_24])).
% 7.20/7.37  cnf(c_0_49, plain, (k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)|~r1_tarski(X3,X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_44, c_0_38])).
% 7.20/7.37  cnf(c_0_50, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk3_0),u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_22])])).
% 7.20/7.37  cnf(c_0_51, negated_conjecture, (k2_xboole_0(k1_tops_1(esk1_0,esk2_0),esk2_0)=esk2_0), inference(spm,[status(thm)],[c_0_41, c_0_47])).
% 7.20/7.37  fof(c_0_52, plain, ![X26, X27, X28]:(~l1_pre_topc(X26)|(~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|(~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|(~r1_tarski(X27,X28)|r1_tarski(k1_tops_1(X26,X27),k1_tops_1(X26,X28)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).
% 7.20/7.37  cnf(c_0_53, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(X2,X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_41, c_0_33])).
% 7.20/7.37  cnf(c_0_54, negated_conjecture, (~r1_tarski(k4_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)),k1_tops_1(esk1_0,k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 7.20/7.37  cnf(c_0_55, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)=k2_xboole_0(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_48, c_0_43])).
% 7.20/7.37  cnf(c_0_56, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),X1,k1_tops_1(esk1_0,esk3_0))=k2_xboole_0(X1,k1_tops_1(esk1_0,esk3_0))|~r1_tarski(X1,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 7.20/7.37  cnf(c_0_57, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk2_0),X1)|~r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_39, c_0_51])).
% 7.20/7.37  cnf(c_0_58, negated_conjecture, (r1_tarski(esk2_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_23, c_0_43])).
% 7.20/7.37  cnf(c_0_59, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 7.20/7.37  cnf(c_0_60, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=X3|~r1_tarski(X2,X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_41, c_0_21])).
% 7.20/7.37  cnf(c_0_61, plain, (k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X1,X3)))=k2_xboole_0(X2,k2_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_53, c_0_15])).
% 7.20/7.37  cnf(c_0_62, negated_conjecture, (~r1_tarski(k4_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)),k1_tops_1(esk1_0,k2_xboole_0(esk2_0,esk3_0)))), inference(rw,[status(thm)],[c_0_54, c_0_55])).
% 7.20/7.37  cnf(c_0_63, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0))=k2_xboole_0(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])])).
% 7.20/7.37  cnf(c_0_64, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_59, c_0_30])).
% 7.20/7.37  cnf(c_0_65, negated_conjecture, (k2_xboole_0(k2_xboole_0(X1,esk3_0),u1_struct_0(esk1_0))=u1_struct_0(esk1_0)|~r1_tarski(X1,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_60, c_0_28])).
% 7.20/7.37  cnf(c_0_66, plain, (r1_tarski(X1,X2)|~r1_tarski(k2_xboole_0(X3,k2_xboole_0(X1,X4)),X2)), inference(spm,[status(thm)],[c_0_39, c_0_61])).
% 7.20/7.37  cnf(c_0_67, plain, (k2_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_41, c_0_22])).
% 7.20/7.37  cnf(c_0_68, negated_conjecture, (~r1_tarski(k2_xboole_0(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)),k1_tops_1(esk1_0,k2_xboole_0(esk2_0,esk3_0)))), inference(rw,[status(thm)],[c_0_62, c_0_63])).
% 7.20/7.37  cnf(c_0_69, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X2,u1_struct_0(esk1_0))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_64, c_0_38])).
% 7.20/7.37  cnf(c_0_70, negated_conjecture, (k2_xboole_0(k2_xboole_0(esk2_0,esk3_0),u1_struct_0(esk1_0))=u1_struct_0(esk1_0)), inference(spm,[status(thm)],[c_0_65, c_0_58])).
% 7.20/7.37  cnf(c_0_71, plain, (r1_tarski(X1,X2)|~r1_tarski(k2_xboole_0(X3,X1),X2)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 7.20/7.37  cnf(c_0_72, negated_conjecture, (~r1_tarski(k1_tops_1(esk1_0,esk3_0),k1_tops_1(esk1_0,k2_xboole_0(esk2_0,esk3_0)))|~r1_tarski(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,k2_xboole_0(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_68, c_0_21])).
% 7.20/7.37  cnf(c_0_73, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk3_0),k1_tops_1(esk1_0,X1))|~r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_69, c_0_24])).
% 7.20/7.37  cnf(c_0_74, negated_conjecture, (r1_tarski(k2_xboole_0(esk2_0,esk3_0),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_15, c_0_70])).
% 7.20/7.37  cnf(c_0_75, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_71, c_0_22])).
% 7.20/7.37  cnf(c_0_76, negated_conjecture, (~r1_tarski(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,k2_xboole_0(esk2_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_74]), c_0_75])])).
% 7.20/7.37  cnf(c_0_77, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,X1))|~r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_69, c_0_43])).
% 7.20/7.37  cnf(c_0_78, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_74]), c_0_15])]), ['proof']).
% 7.20/7.37  # SZS output end CNFRefutation
% 7.20/7.37  # Proof object total steps             : 79
% 7.20/7.37  # Proof object clause steps            : 56
% 7.20/7.37  # Proof object formula steps           : 23
% 7.20/7.37  # Proof object conjectures             : 35
% 7.20/7.37  # Proof object clause conjectures      : 32
% 7.20/7.37  # Proof object formula conjectures     : 3
% 7.20/7.37  # Proof object initial clauses used    : 16
% 7.20/7.37  # Proof object initial formulas used   : 11
% 7.20/7.37  # Proof object generating inferences   : 37
% 7.20/7.37  # Proof object simplifying inferences  : 15
% 7.20/7.37  # Training examples: 0 positive, 0 negative
% 7.20/7.37  # Parsed axioms                        : 11
% 7.20/7.37  # Removed by relevancy pruning/SinE    : 0
% 7.20/7.37  # Initial clauses                      : 17
% 7.20/7.37  # Removed in clause preprocessing      : 0
% 7.20/7.37  # Initial clauses in saturation        : 17
% 7.20/7.37  # Processed clauses                    : 69834
% 7.20/7.37  # ...of these trivial                  : 1946
% 7.20/7.37  # ...subsumed                          : 60664
% 7.20/7.37  # ...remaining for further processing  : 7224
% 7.20/7.37  # Other redundant clauses eliminated   : 2
% 7.20/7.37  # Clauses deleted for lack of memory   : 0
% 7.20/7.37  # Backward-subsumed                    : 62
% 7.20/7.37  # Backward-rewritten                   : 1587
% 7.20/7.37  # Generated clauses                    : 1319981
% 7.20/7.37  # ...of the previous two non-trivial   : 1021135
% 7.20/7.37  # Contextual simplify-reflections      : 75
% 7.20/7.37  # Paramodulations                      : 1319979
% 7.20/7.37  # Factorizations                       : 0
% 7.20/7.37  # Equation resolutions                 : 2
% 7.20/7.37  # Propositional unsat checks           : 0
% 7.20/7.37  #    Propositional check models        : 0
% 7.20/7.37  #    Propositional check unsatisfiable : 0
% 7.20/7.37  #    Propositional clauses             : 0
% 7.20/7.37  #    Propositional clauses after purity: 0
% 7.20/7.37  #    Propositional unsat core size     : 0
% 7.20/7.37  #    Propositional preprocessing time  : 0.000
% 7.20/7.37  #    Propositional encoding time       : 0.000
% 7.20/7.37  #    Propositional solver time         : 0.000
% 7.20/7.37  #    Success case prop preproc time    : 0.000
% 7.20/7.37  #    Success case prop encoding time   : 0.000
% 7.20/7.37  #    Success case prop solver time     : 0.000
% 7.20/7.37  # Current number of processed clauses  : 5557
% 7.20/7.37  #    Positive orientable unit clauses  : 885
% 7.20/7.37  #    Positive unorientable unit clauses: 1
% 7.20/7.37  #    Negative unit clauses             : 4
% 7.20/7.37  #    Non-unit-clauses                  : 4667
% 7.20/7.37  # Current number of unprocessed clauses: 940607
% 7.20/7.37  # ...number of literals in the above   : 2115540
% 7.20/7.37  # Current number of archived formulas  : 0
% 7.20/7.37  # Current number of archived clauses   : 1665
% 7.20/7.37  # Clause-clause subsumption calls (NU) : 3534355
% 7.20/7.37  # Rec. Clause-clause subsumption calls : 3230293
% 7.20/7.37  # Non-unit clause-clause subsumptions  : 60384
% 7.20/7.37  # Unit Clause-clause subsumption calls : 253865
% 7.20/7.37  # Rewrite failures with RHS unbound    : 0
% 7.20/7.37  # BW rewrite match attempts            : 16393
% 7.20/7.37  # BW rewrite match successes           : 2977
% 7.20/7.37  # Condensation attempts                : 0
% 7.20/7.37  # Condensation successes               : 0
% 7.20/7.37  # Termbank termtop insertions          : 23211165
% 7.20/7.40  
% 7.20/7.40  # -------------------------------------------------
% 7.20/7.40  # User time                : 6.723 s
% 7.20/7.40  # System time              : 0.328 s
% 7.20/7.40  # Total time               : 7.051 s
% 7.20/7.40  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
