%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:39 EST 2020

% Result     : Theorem 17.25s
% Output     : CNFRefutation 17.25s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 499 expanded)
%              Number of clauses        :   56 ( 177 expanded)
%              Number of leaves         :   10 ( 123 expanded)
%              Depth                    :   13
%              Number of atoms          :  292 (2758 expanded)
%              Number of equality atoms :   29 ( 186 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t22_waybel_9,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(k9_yellow_6(X1,X2)))
                 => m1_subset_1(k3_xboole_0(X3,X4),u1_struct_0(k9_yellow_6(X1,X2))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_waybel_9)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t38_yellow_6,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))
             => ? [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                  & X4 = X3
                  & r2_hidden(X2,X4)
                  & v3_pre_topc(X4,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_yellow_6)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t39_yellow_6,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r2_hidden(X3,u1_struct_0(k9_yellow_6(X1,X2)))
              <=> ( r2_hidden(X2,X3)
                  & v3_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_yellow_6)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(fc6_tops_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & v3_pre_topc(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & v3_pre_topc(X3,X1)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k3_xboole_0(X2,X3),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_tops_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(k9_yellow_6(X1,X2)))
                   => m1_subset_1(k3_xboole_0(X3,X4),u1_struct_0(k9_yellow_6(X1,X2))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t22_waybel_9])).

fof(c_0_11,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_12,plain,(
    ! [X19,X20] : k1_setfam_1(k2_tarski(X19,X20)) = k3_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_13,plain,(
    ! [X29,X30,X31] :
      ( ( m1_subset_1(esk2_3(X29,X30,X31),k1_zfmisc_1(u1_struct_0(X29)))
        | ~ m1_subset_1(X31,u1_struct_0(k9_yellow_6(X29,X30)))
        | ~ m1_subset_1(X30,u1_struct_0(X29))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( esk2_3(X29,X30,X31) = X31
        | ~ m1_subset_1(X31,u1_struct_0(k9_yellow_6(X29,X30)))
        | ~ m1_subset_1(X30,u1_struct_0(X29))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( r2_hidden(X30,esk2_3(X29,X30,X31))
        | ~ m1_subset_1(X31,u1_struct_0(k9_yellow_6(X29,X30)))
        | ~ m1_subset_1(X30,u1_struct_0(X29))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( v3_pre_topc(esk2_3(X29,X30,X31),X29)
        | ~ m1_subset_1(X31,u1_struct_0(k9_yellow_6(X29,X30)))
        | ~ m1_subset_1(X30,u1_struct_0(X29))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_yellow_6])])])])])])).

fof(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk5_0,u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))
    & m1_subset_1(esk6_0,u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))
    & ~ m1_subset_1(k3_xboole_0(esk5_0,esk6_0),u1_struct_0(k9_yellow_6(esk3_0,esk4_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

cnf(c_0_15,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( esk2_3(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(k9_yellow_6(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_23,plain,(
    ! [X14,X15] : r1_tarski(k3_xboole_0(X14,X15),X14) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_24,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_25,plain,
    ( X3 = k1_setfam_1(k2_tarski(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_26,plain,(
    ! [X16,X17,X18] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(X16))
      | ~ r2_hidden(X18,X17)
      | r2_hidden(X18,X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_27,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_28,negated_conjecture,
    ( esk2_3(esk3_0,esk4_0,esk6_0) = esk6_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_30,plain,(
    ! [X21,X22] :
      ( ( ~ m1_subset_1(X21,k1_zfmisc_1(X22))
        | r1_tarski(X21,X22) )
      & ( ~ r1_tarski(X21,X22)
        | m1_subset_1(X21,k1_zfmisc_1(X22)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_31,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_32,plain,(
    ! [X33,X34,X35] :
      ( ( r2_hidden(X34,X35)
        | ~ r2_hidden(X35,u1_struct_0(k9_yellow_6(X33,X34)))
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ m1_subset_1(X34,u1_struct_0(X33))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( v3_pre_topc(X35,X33)
        | ~ r2_hidden(X35,u1_struct_0(k9_yellow_6(X33,X34)))
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ m1_subset_1(X34,u1_struct_0(X33))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( ~ r2_hidden(X34,X35)
        | ~ v3_pre_topc(X35,X33)
        | r2_hidden(X35,u1_struct_0(k9_yellow_6(X33,X34)))
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ m1_subset_1(X34,u1_struct_0(X33))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t39_yellow_6])])])])])).

fof(c_0_33,plain,(
    ! [X23,X24,X25] :
      ( ~ r2_hidden(X23,X24)
      | ~ m1_subset_1(X24,k1_zfmisc_1(X25))
      | m1_subset_1(X23,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_34,plain,
    ( X3 = k1_setfam_1(k2_tarski(X1,X2))
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_24,c_0_16])).

cnf(c_0_35,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X2
    | r2_hidden(esk1_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_18]),c_0_28]),c_0_19]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | X3 != k1_setfam_1(k2_tarski(X4,X2))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_29,c_0_16])).

cnf(c_0_39,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_31,c_0_16])).

cnf(c_0_41,plain,
    ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X3,X1)))
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,X2)
    | ~ v3_pre_topc(X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X2
    | ~ r2_hidden(esk1_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_setfam_1(k2_tarski(X3,X2))) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,u1_struct_0(k9_yellow_6(X1,X3)))
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,X2) ),
    inference(csr,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( k1_setfam_1(k2_tarski(u1_struct_0(esk3_0),X1)) = X1
    | ~ r2_hidden(esk1_3(u1_struct_0(esk3_0),X1,X1),esk6_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,plain,
    ( k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X2,X3)))) = k1_setfam_1(k2_tarski(X2,X3))
    | r2_hidden(esk1_3(X1,k1_setfam_1(k2_tarski(X2,X3)),k1_setfam_1(k2_tarski(X2,X3))),X3) ),
    inference(spm,[status(thm)],[c_0_45,c_0_35])).

cnf(c_0_50,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_46])).

cnf(c_0_51,plain,
    ( k1_setfam_1(k2_tarski(X1,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_43,c_0_35])).

cnf(c_0_52,plain,
    ( v2_struct_0(X1)
    | r2_hidden(k1_setfam_1(k2_tarski(u1_struct_0(X1),X2)),u1_struct_0(k9_yellow_6(X1,X3)))
    | ~ v3_pre_topc(k1_setfam_1(k2_tarski(u1_struct_0(X1),X2)),X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ r2_hidden(X3,k1_setfam_1(k2_tarski(u1_struct_0(X1),X2))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( k1_setfam_1(k2_tarski(u1_struct_0(esk3_0),k1_setfam_1(k2_tarski(X1,esk6_0)))) = k1_setfam_1(k2_tarski(X1,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

fof(c_0_54,plain,(
    ! [X26,X27,X28] :
      ( ~ v2_pre_topc(X26)
      | ~ l1_pre_topc(X26)
      | ~ v3_pre_topc(X27,X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
      | ~ v3_pre_topc(X28,X26)
      | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
      | v3_pre_topc(k3_xboole_0(X27,X28),X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_tops_1])])).

cnf(c_0_55,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(k1_setfam_1(k2_tarski(X1,esk6_0)),u1_struct_0(k9_yellow_6(esk3_0,X2)))
    | ~ v3_pre_topc(k1_setfam_1(k2_tarski(X1,esk6_0)),esk3_0)
    | ~ r2_hidden(X2,k1_setfam_1(k2_tarski(X1,esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_19]),c_0_20])]),c_0_22])).

cnf(c_0_57,plain,
    ( v3_pre_topc(k3_xboole_0(X2,X3),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_58,plain,
    ( v3_pre_topc(esk2_3(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(k9_yellow_6(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_60,negated_conjecture,
    ( ~ m1_subset_1(k3_xboole_0(esk5_0,esk6_0),u1_struct_0(k9_yellow_6(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X1,esk6_0)),u1_struct_0(k9_yellow_6(esk3_0,X2)))
    | ~ v3_pre_topc(k1_setfam_1(k2_tarski(X1,esk6_0)),esk3_0)
    | ~ r2_hidden(X2,k1_setfam_1(k2_tarski(X1,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_62,plain,
    ( v3_pre_topc(k1_setfam_1(k2_tarski(X2,X3)),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v3_pre_topc(X3,X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(rw,[status(thm)],[c_0_57,c_0_16])).

cnf(c_0_63,negated_conjecture,
    ( v3_pre_topc(esk6_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_18]),c_0_28]),c_0_19]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_64,negated_conjecture,
    ( esk2_3(esk3_0,esk4_0,esk5_0) = esk5_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_59]),c_0_19]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_66,negated_conjecture,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(esk5_0,esk6_0)),u1_struct_0(k9_yellow_6(esk3_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_60,c_0_16])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X1,esk6_0)),u1_struct_0(k9_yellow_6(esk3_0,X2)))
    | ~ v3_pre_topc(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(X2,k1_setfam_1(k2_tarski(X1,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63]),c_0_19]),c_0_20]),c_0_37])])).

cnf(c_0_68,negated_conjecture,
    ( v3_pre_topc(esk5_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_64]),c_0_19]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_59]),c_0_64]),c_0_19]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,X4)
    | X4 != k1_setfam_1(k2_tarski(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_65,c_0_16])).

cnf(c_0_71,plain,
    ( r2_hidden(X1,esk2_3(X2,X1,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(k9_yellow_6(X2,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_72,negated_conjecture,
    ( ~ r2_hidden(esk4_0,k1_setfam_1(k2_tarski(esk5_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68]),c_0_69])])).

cnf(c_0_73,plain,
    ( r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X3)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk4_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_18]),c_0_28]),c_0_19]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_59]),c_0_64]),c_0_19]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_76,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74]),c_0_75])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:11:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 17.25/17.46  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 17.25/17.46  # and selection function SelectComplexExceptUniqMaxHorn.
% 17.25/17.46  #
% 17.25/17.46  # Preprocessing time       : 0.029 s
% 17.25/17.46  # Presaturation interreduction done
% 17.25/17.46  
% 17.25/17.46  # Proof found!
% 17.25/17.46  # SZS status Theorem
% 17.25/17.46  # SZS output start CNFRefutation
% 17.25/17.46  fof(t22_waybel_9, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))=>![X4]:(m1_subset_1(X4,u1_struct_0(k9_yellow_6(X1,X2)))=>m1_subset_1(k3_xboole_0(X3,X4),u1_struct_0(k9_yellow_6(X1,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_waybel_9)).
% 17.25/17.46  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 17.25/17.46  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 17.25/17.46  fof(t38_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))=>?[X4]:(((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&X4=X3)&r2_hidden(X2,X4))&v3_pre_topc(X4,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_yellow_6)).
% 17.25/17.46  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 17.25/17.46  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 17.25/17.46  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 17.25/17.46  fof(t39_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X3,u1_struct_0(k9_yellow_6(X1,X2)))<=>(r2_hidden(X2,X3)&v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_yellow_6)).
% 17.25/17.46  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 17.25/17.46  fof(fc6_tops_1, axiom, ![X1, X2, X3]:((((((v2_pre_topc(X1)&l1_pre_topc(X1))&v3_pre_topc(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&v3_pre_topc(X3,X1))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k3_xboole_0(X2,X3),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_tops_1)).
% 17.25/17.46  fof(c_0_10, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))=>![X4]:(m1_subset_1(X4,u1_struct_0(k9_yellow_6(X1,X2)))=>m1_subset_1(k3_xboole_0(X3,X4),u1_struct_0(k9_yellow_6(X1,X2)))))))), inference(assume_negation,[status(cth)],[t22_waybel_9])).
% 17.25/17.46  fof(c_0_11, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6))&(r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k3_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k3_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))&(r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 17.25/17.46  fof(c_0_12, plain, ![X19, X20]:k1_setfam_1(k2_tarski(X19,X20))=k3_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 17.25/17.46  fof(c_0_13, plain, ![X29, X30, X31]:((((m1_subset_1(esk2_3(X29,X30,X31),k1_zfmisc_1(u1_struct_0(X29)))|~m1_subset_1(X31,u1_struct_0(k9_yellow_6(X29,X30)))|~m1_subset_1(X30,u1_struct_0(X29))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)))&(esk2_3(X29,X30,X31)=X31|~m1_subset_1(X31,u1_struct_0(k9_yellow_6(X29,X30)))|~m1_subset_1(X30,u1_struct_0(X29))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29))))&(r2_hidden(X30,esk2_3(X29,X30,X31))|~m1_subset_1(X31,u1_struct_0(k9_yellow_6(X29,X30)))|~m1_subset_1(X30,u1_struct_0(X29))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29))))&(v3_pre_topc(esk2_3(X29,X30,X31),X29)|~m1_subset_1(X31,u1_struct_0(k9_yellow_6(X29,X30)))|~m1_subset_1(X30,u1_struct_0(X29))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_yellow_6])])])])])])).
% 17.25/17.46  fof(c_0_14, negated_conjecture, (((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,u1_struct_0(esk3_0))&(m1_subset_1(esk5_0,u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))&(m1_subset_1(esk6_0,u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))&~m1_subset_1(k3_xboole_0(esk5_0,esk6_0),u1_struct_0(k9_yellow_6(esk3_0,esk4_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 17.25/17.46  cnf(c_0_15, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 17.25/17.46  cnf(c_0_16, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 17.25/17.46  cnf(c_0_17, plain, (esk2_3(X1,X2,X3)=X3|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 17.25/17.46  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 17.25/17.46  cnf(c_0_19, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 17.25/17.46  cnf(c_0_20, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 17.25/17.46  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 17.25/17.46  cnf(c_0_22, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 17.25/17.46  fof(c_0_23, plain, ![X14, X15]:r1_tarski(k3_xboole_0(X14,X15),X14), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 17.25/17.46  cnf(c_0_24, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 17.25/17.46  cnf(c_0_25, plain, (X3=k1_setfam_1(k2_tarski(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 17.25/17.46  fof(c_0_26, plain, ![X16, X17, X18]:(~m1_subset_1(X17,k1_zfmisc_1(X16))|(~r2_hidden(X18,X17)|r2_hidden(X18,X16))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 17.25/17.46  cnf(c_0_27, plain, (m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 17.25/17.46  cnf(c_0_28, negated_conjecture, (esk2_3(esk3_0,esk4_0,esk6_0)=esk6_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20]), c_0_21])]), c_0_22])).
% 17.25/17.46  cnf(c_0_29, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 17.25/17.46  fof(c_0_30, plain, ![X21, X22]:((~m1_subset_1(X21,k1_zfmisc_1(X22))|r1_tarski(X21,X22))&(~r1_tarski(X21,X22)|m1_subset_1(X21,k1_zfmisc_1(X22)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 17.25/17.46  cnf(c_0_31, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 17.25/17.46  fof(c_0_32, plain, ![X33, X34, X35]:(((r2_hidden(X34,X35)|~r2_hidden(X35,u1_struct_0(k9_yellow_6(X33,X34)))|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))|~m1_subset_1(X34,u1_struct_0(X33))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)))&(v3_pre_topc(X35,X33)|~r2_hidden(X35,u1_struct_0(k9_yellow_6(X33,X34)))|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))|~m1_subset_1(X34,u1_struct_0(X33))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33))))&(~r2_hidden(X34,X35)|~v3_pre_topc(X35,X33)|r2_hidden(X35,u1_struct_0(k9_yellow_6(X33,X34)))|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))|~m1_subset_1(X34,u1_struct_0(X33))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t39_yellow_6])])])])])).
% 17.25/17.46  fof(c_0_33, plain, ![X23, X24, X25]:(~r2_hidden(X23,X24)|~m1_subset_1(X24,k1_zfmisc_1(X25))|m1_subset_1(X23,X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 17.25/17.46  cnf(c_0_34, plain, (X3=k1_setfam_1(k2_tarski(X1,X2))|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_24, c_0_16])).
% 17.25/17.46  cnf(c_0_35, plain, (k1_setfam_1(k2_tarski(X1,X2))=X2|r2_hidden(esk1_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_25])).
% 17.25/17.46  cnf(c_0_36, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 17.25/17.46  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_18]), c_0_28]), c_0_19]), c_0_20]), c_0_21])]), c_0_22])).
% 17.25/17.46  cnf(c_0_38, plain, (r2_hidden(X1,X2)|X3!=k1_setfam_1(k2_tarski(X4,X2))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_29, c_0_16])).
% 17.25/17.46  cnf(c_0_39, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 17.25/17.46  cnf(c_0_40, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_31, c_0_16])).
% 17.25/17.46  cnf(c_0_41, plain, (r2_hidden(X2,u1_struct_0(k9_yellow_6(X3,X1)))|v2_struct_0(X3)|~r2_hidden(X1,X2)|~v3_pre_topc(X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X1,u1_struct_0(X3))|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 17.25/17.46  cnf(c_0_42, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 17.25/17.46  cnf(c_0_43, plain, (k1_setfam_1(k2_tarski(X1,X2))=X2|~r2_hidden(esk1_3(X1,X2,X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_35])).
% 17.25/17.46  cnf(c_0_44, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 17.25/17.46  cnf(c_0_45, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_setfam_1(k2_tarski(X3,X2)))), inference(er,[status(thm)],[c_0_38])).
% 17.25/17.46  cnf(c_0_46, plain, (m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 17.25/17.46  cnf(c_0_47, plain, (v2_struct_0(X1)|r2_hidden(X2,u1_struct_0(k9_yellow_6(X1,X3)))|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X3,X2)), inference(csr,[status(thm)],[c_0_41, c_0_42])).
% 17.25/17.46  cnf(c_0_48, negated_conjecture, (k1_setfam_1(k2_tarski(u1_struct_0(esk3_0),X1))=X1|~r2_hidden(esk1_3(u1_struct_0(esk3_0),X1,X1),esk6_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 17.25/17.46  cnf(c_0_49, plain, (k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X2,X3))))=k1_setfam_1(k2_tarski(X2,X3))|r2_hidden(esk1_3(X1,k1_setfam_1(k2_tarski(X2,X3)),k1_setfam_1(k2_tarski(X2,X3))),X3)), inference(spm,[status(thm)],[c_0_45, c_0_35])).
% 17.25/17.46  cnf(c_0_50, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X3)))), inference(spm,[status(thm)],[c_0_42, c_0_46])).
% 17.25/17.46  cnf(c_0_51, plain, (k1_setfam_1(k2_tarski(X1,X1))=X1), inference(spm,[status(thm)],[c_0_43, c_0_35])).
% 17.25/17.46  cnf(c_0_52, plain, (v2_struct_0(X1)|r2_hidden(k1_setfam_1(k2_tarski(u1_struct_0(X1),X2)),u1_struct_0(k9_yellow_6(X1,X3)))|~v3_pre_topc(k1_setfam_1(k2_tarski(u1_struct_0(X1),X2)),X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~r2_hidden(X3,k1_setfam_1(k2_tarski(u1_struct_0(X1),X2)))), inference(spm,[status(thm)],[c_0_47, c_0_46])).
% 17.25/17.46  cnf(c_0_53, negated_conjecture, (k1_setfam_1(k2_tarski(u1_struct_0(esk3_0),k1_setfam_1(k2_tarski(X1,esk6_0))))=k1_setfam_1(k2_tarski(X1,esk6_0))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 17.25/17.46  fof(c_0_54, plain, ![X26, X27, X28]:(~v2_pre_topc(X26)|~l1_pre_topc(X26)|~v3_pre_topc(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|~v3_pre_topc(X28,X26)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|v3_pre_topc(k3_xboole_0(X27,X28),X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_tops_1])])).
% 17.25/17.46  cnf(c_0_55, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 17.25/17.46  cnf(c_0_56, negated_conjecture, (r2_hidden(k1_setfam_1(k2_tarski(X1,esk6_0)),u1_struct_0(k9_yellow_6(esk3_0,X2)))|~v3_pre_topc(k1_setfam_1(k2_tarski(X1,esk6_0)),esk3_0)|~r2_hidden(X2,k1_setfam_1(k2_tarski(X1,esk6_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_19]), c_0_20])]), c_0_22])).
% 17.25/17.46  cnf(c_0_57, plain, (v3_pre_topc(k3_xboole_0(X2,X3),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v3_pre_topc(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X3,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 17.25/17.46  cnf(c_0_58, plain, (v3_pre_topc(esk2_3(X1,X2,X3),X1)|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 17.25/17.46  cnf(c_0_59, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 17.25/17.46  cnf(c_0_60, negated_conjecture, (~m1_subset_1(k3_xboole_0(esk5_0,esk6_0),u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 17.25/17.46  cnf(c_0_61, negated_conjecture, (m1_subset_1(k1_setfam_1(k2_tarski(X1,esk6_0)),u1_struct_0(k9_yellow_6(esk3_0,X2)))|~v3_pre_topc(k1_setfam_1(k2_tarski(X1,esk6_0)),esk3_0)|~r2_hidden(X2,k1_setfam_1(k2_tarski(X1,esk6_0)))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 17.25/17.46  cnf(c_0_62, plain, (v3_pre_topc(k1_setfam_1(k2_tarski(X2,X3)),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v3_pre_topc(X3,X1)|~v3_pre_topc(X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(rw,[status(thm)],[c_0_57, c_0_16])).
% 17.25/17.46  cnf(c_0_63, negated_conjecture, (v3_pre_topc(esk6_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_18]), c_0_28]), c_0_19]), c_0_20]), c_0_21])]), c_0_22])).
% 17.25/17.46  cnf(c_0_64, negated_conjecture, (esk2_3(esk3_0,esk4_0,esk5_0)=esk5_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_59]), c_0_19]), c_0_20]), c_0_21])]), c_0_22])).
% 17.25/17.46  cnf(c_0_65, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 17.25/17.46  cnf(c_0_66, negated_conjecture, (~m1_subset_1(k1_setfam_1(k2_tarski(esk5_0,esk6_0)),u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))), inference(rw,[status(thm)],[c_0_60, c_0_16])).
% 17.25/17.46  cnf(c_0_67, negated_conjecture, (m1_subset_1(k1_setfam_1(k2_tarski(X1,esk6_0)),u1_struct_0(k9_yellow_6(esk3_0,X2)))|~v3_pre_topc(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(X2,k1_setfam_1(k2_tarski(X1,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63]), c_0_19]), c_0_20]), c_0_37])])).
% 17.25/17.46  cnf(c_0_68, negated_conjecture, (v3_pre_topc(esk5_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_64]), c_0_19]), c_0_20]), c_0_21])]), c_0_22])).
% 17.25/17.46  cnf(c_0_69, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_59]), c_0_64]), c_0_19]), c_0_20]), c_0_21])]), c_0_22])).
% 17.25/17.46  cnf(c_0_70, plain, (r2_hidden(X1,X4)|X4!=k1_setfam_1(k2_tarski(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_65, c_0_16])).
% 17.25/17.46  cnf(c_0_71, plain, (r2_hidden(X1,esk2_3(X2,X1,X3))|v2_struct_0(X2)|~m1_subset_1(X3,u1_struct_0(k9_yellow_6(X2,X1)))|~m1_subset_1(X1,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 17.25/17.46  cnf(c_0_72, negated_conjecture, (~r2_hidden(esk4_0,k1_setfam_1(k2_tarski(esk5_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68]), c_0_69])])).
% 17.25/17.46  cnf(c_0_73, plain, (r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X3)))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_70])).
% 17.25/17.46  cnf(c_0_74, negated_conjecture, (r2_hidden(esk4_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_18]), c_0_28]), c_0_19]), c_0_20]), c_0_21])]), c_0_22])).
% 17.25/17.46  cnf(c_0_75, negated_conjecture, (r2_hidden(esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_59]), c_0_64]), c_0_19]), c_0_20]), c_0_21])]), c_0_22])).
% 17.25/17.46  cnf(c_0_76, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_74]), c_0_75])]), ['proof']).
% 17.25/17.46  # SZS output end CNFRefutation
% 17.25/17.46  # Proof object total steps             : 77
% 17.25/17.46  # Proof object clause steps            : 56
% 17.25/17.46  # Proof object formula steps           : 21
% 17.25/17.46  # Proof object conjectures             : 27
% 17.25/17.46  # Proof object clause conjectures      : 24
% 17.25/17.46  # Proof object formula conjectures     : 3
% 17.25/17.46  # Proof object initial clauses used    : 22
% 17.25/17.46  # Proof object initial formulas used   : 10
% 17.25/17.46  # Proof object generating inferences   : 24
% 17.25/17.46  # Proof object simplifying inferences  : 72
% 17.25/17.46  # Training examples: 0 positive, 0 negative
% 17.25/17.46  # Parsed axioms                        : 10
% 17.25/17.46  # Removed by relevancy pruning/SinE    : 0
% 17.25/17.46  # Initial clauses                      : 27
% 17.25/17.46  # Removed in clause preprocessing      : 1
% 17.25/17.46  # Initial clauses in saturation        : 26
% 17.25/17.46  # Processed clauses                    : 11922
% 17.25/17.46  # ...of these trivial                  : 165
% 17.25/17.46  # ...subsumed                          : 7734
% 17.25/17.46  # ...remaining for further processing  : 4023
% 17.25/17.46  # Other redundant clauses eliminated   : 3
% 17.25/17.46  # Clauses deleted for lack of memory   : 0
% 17.25/17.46  # Backward-subsumed                    : 333
% 17.25/17.46  # Backward-rewritten                   : 92
% 17.25/17.46  # Generated clauses                    : 1621206
% 17.25/17.46  # ...of the previous two non-trivial   : 1447872
% 17.25/17.46  # Contextual simplify-reflections      : 140
% 17.25/17.46  # Paramodulations                      : 1620331
% 17.25/17.46  # Factorizations                       : 872
% 17.25/17.46  # Equation resolutions                 : 3
% 17.25/17.46  # Propositional unsat checks           : 0
% 17.25/17.46  #    Propositional check models        : 0
% 17.25/17.46  #    Propositional check unsatisfiable : 0
% 17.25/17.46  #    Propositional clauses             : 0
% 17.25/17.46  #    Propositional clauses after purity: 0
% 17.25/17.46  #    Propositional unsat core size     : 0
% 17.25/17.46  #    Propositional preprocessing time  : 0.000
% 17.25/17.46  #    Propositional encoding time       : 0.000
% 17.25/17.46  #    Propositional solver time         : 0.000
% 17.25/17.46  #    Success case prop preproc time    : 0.000
% 17.25/17.46  #    Success case prop encoding time   : 0.000
% 17.25/17.46  #    Success case prop solver time     : 0.000
% 17.25/17.46  # Current number of processed clauses  : 3569
% 17.25/17.46  #    Positive orientable unit clauses  : 62
% 17.25/17.46  #    Positive unorientable unit clauses: 0
% 17.25/17.46  #    Negative unit clauses             : 6
% 17.25/17.46  #    Non-unit-clauses                  : 3501
% 17.25/17.46  # Current number of unprocessed clauses: 1434819
% 17.25/17.46  # ...number of literals in the above   : 9436543
% 17.25/17.46  # Current number of archived formulas  : 0
% 17.25/17.46  # Current number of archived clauses   : 452
% 17.25/17.46  # Clause-clause subsumption calls (NU) : 4311354
% 17.25/17.46  # Rec. Clause-clause subsumption calls : 863727
% 17.25/17.46  # Non-unit clause-clause subsumptions  : 7568
% 17.25/17.46  # Unit Clause-clause subsumption calls : 13811
% 17.25/17.46  # Rewrite failures with RHS unbound    : 0
% 17.25/17.46  # BW rewrite match attempts            : 317
% 17.25/17.46  # BW rewrite match successes           : 36
% 17.25/17.46  # Condensation attempts                : 0
% 17.25/17.46  # Condensation successes               : 0
% 17.25/17.46  # Termbank termtop insertions          : 50524412
% 17.31/17.53  
% 17.31/17.53  # -------------------------------------------------
% 17.31/17.53  # User time                : 16.571 s
% 17.31/17.53  # System time              : 0.608 s
% 17.31/17.53  # Total time               : 17.179 s
% 17.31/17.53  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
