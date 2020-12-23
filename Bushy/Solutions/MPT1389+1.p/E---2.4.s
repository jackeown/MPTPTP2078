%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : connsp_2__t14_connsp_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:52 EDT 2019

% Result     : Theorem 0.66s
% Output     : CNFRefutation 0.66s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 957 expanded)
%              Number of clauses        :   71 ( 360 expanded)
%              Number of leaves         :   17 ( 233 expanded)
%              Depth                    :   20
%              Number of atoms          :  453 (5713 expanded)
%              Number of equality atoms :   47 ( 608 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   64 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t14_connsp_2.p',t5_subset)).

fof(d7_connsp_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = k1_connsp_1(X1,X2)
              <=> ? [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                    & ! [X5] :
                        ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                       => ( r2_hidden(X5,X4)
                        <=> ( v2_connsp_1(X5,X1)
                            & r2_hidden(X2,X5) ) ) )
                    & k5_setfam_1(u1_struct_0(X1),X4) = X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t14_connsp_2.p',d7_connsp_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t14_connsp_2.p',t4_subset)).

fof(t14_connsp_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X2))
                 => ( X3 = X4
                   => r1_tarski(k1_connsp_1(X2,X4),k1_connsp_1(X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t14_connsp_2.p',t14_connsp_2)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t14_connsp_2.p',t2_subset)).

fof(dt_k1_connsp_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k1_connsp_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t14_connsp_2.p',dt_k1_connsp_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t14_connsp_2.p',dt_m1_pre_topc)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t14_connsp_2.p',t1_subset)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t14_connsp_2.p',cc1_pre_topc)).

fof(fc2_connsp_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v1_xboole_0(k1_connsp_1(X1,X2))
        & v2_connsp_1(k1_connsp_1(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t14_connsp_2.p',fc2_connsp_1)).

fof(t40_connsp_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r2_hidden(X2,k1_connsp_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t14_connsp_2.p',t40_connsp_1)).

fof(t24_connsp_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( X3 = X4
                   => ( v2_connsp_1(X3,X1)
                    <=> v2_connsp_1(X4,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t14_connsp_2.p',t24_connsp_1)).

fof(t39_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t14_connsp_2.p',t39_pre_topc)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t14_connsp_2.p',existence_m1_subset_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t14_connsp_2.p',t7_boole)).

fof(t92_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t14_connsp_2.p',t92_zfmisc_1)).

fof(redefinition_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k5_setfam_1(X1,X2) = k3_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t14_connsp_2.p',redefinition_k5_setfam_1)).

fof(c_0_17,plain,(
    ! [X52,X53,X54] :
      ( ~ r2_hidden(X52,X53)
      | ~ m1_subset_1(X53,k1_zfmisc_1(X54))
      | ~ v1_xboole_0(X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_18,plain,(
    ! [X12,X13,X14,X16,X17] :
      ( ( m1_subset_1(esk5_3(X12,X13,X14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | X14 != k1_connsp_1(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ l1_pre_topc(X12) )
      & ( v2_connsp_1(X16,X12)
        | ~ r2_hidden(X16,esk5_3(X12,X13,X14))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X12)))
        | X14 != k1_connsp_1(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ l1_pre_topc(X12) )
      & ( r2_hidden(X13,X16)
        | ~ r2_hidden(X16,esk5_3(X12,X13,X14))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X12)))
        | X14 != k1_connsp_1(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ l1_pre_topc(X12) )
      & ( ~ v2_connsp_1(X16,X12)
        | ~ r2_hidden(X13,X16)
        | r2_hidden(X16,esk5_3(X12,X13,X14))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X12)))
        | X14 != k1_connsp_1(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ l1_pre_topc(X12) )
      & ( k5_setfam_1(u1_struct_0(X12),esk5_3(X12,X13,X14)) = X14
        | X14 != k1_connsp_1(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk6_4(X12,X13,X14,X17),k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | k5_setfam_1(u1_struct_0(X12),X17) != X14
        | X14 = k1_connsp_1(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ l1_pre_topc(X12) )
      & ( ~ r2_hidden(esk6_4(X12,X13,X14,X17),X17)
        | ~ v2_connsp_1(esk6_4(X12,X13,X14,X17),X12)
        | ~ r2_hidden(X13,esk6_4(X12,X13,X14,X17))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | k5_setfam_1(u1_struct_0(X12),X17) != X14
        | X14 = k1_connsp_1(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ l1_pre_topc(X12) )
      & ( v2_connsp_1(esk6_4(X12,X13,X14,X17),X12)
        | r2_hidden(esk6_4(X12,X13,X14,X17),X17)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | k5_setfam_1(u1_struct_0(X12),X17) != X14
        | X14 = k1_connsp_1(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ l1_pre_topc(X12) )
      & ( r2_hidden(X13,esk6_4(X12,X13,X14,X17))
        | r2_hidden(esk6_4(X12,X13,X14,X17),X17)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | k5_setfam_1(u1_struct_0(X12),X17) != X14
        | X14 = k1_connsp_1(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ l1_pre_topc(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_connsp_1])])])])])).

fof(c_0_19,plain,(
    ! [X49,X50,X51] :
      ( ~ r2_hidden(X49,X50)
      | ~ m1_subset_1(X50,k1_zfmisc_1(X51))
      | m1_subset_1(X49,X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X2))
                   => ( X3 = X4
                     => r1_tarski(k1_connsp_1(X2,X4),k1_connsp_1(X1,X3)) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t14_connsp_2])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( m1_subset_1(esk5_3(X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | X3 != k1_connsp_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,esk5_3(X2,X3,X4))
    | ~ v2_connsp_1(X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | X4 != k1_connsp_1(X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X40,X41] :
      ( ~ m1_subset_1(X40,X41)
      | v1_xboole_0(X41)
      | r2_hidden(X40,X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_26,plain,(
    ! [X19,X20] :
      ( ~ l1_pre_topc(X19)
      | ~ m1_subset_1(X20,u1_struct_0(X19))
      | m1_subset_1(k1_connsp_1(X19,X20),k1_zfmisc_1(u1_struct_0(X19))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_connsp_1])])).

fof(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & m1_pre_topc(esk2_0,esk1_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk4_0,u1_struct_0(esk2_0))
    & esk3_0 = esk4_0
    & ~ r1_tarski(k1_connsp_1(esk2_0,esk4_0),k1_connsp_1(esk1_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).

fof(c_0_28,plain,(
    ! [X24,X25] :
      ( ~ l1_pre_topc(X24)
      | ~ m1_pre_topc(X25,X24)
      | l1_pre_topc(X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_29,plain,
    ( X1 != k1_connsp_1(X2,X3)
    | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X4,esk5_3(X2,X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,esk5_3(X2,X3,X4))
    | X4 != k1_connsp_1(X2,X3)
    | ~ v2_connsp_1(X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( m1_subset_1(k1_connsp_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( esk3_0 = esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( X1 != k1_connsp_1(X2,X3)
    | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_connsp_1(X4,X2)
    | ~ r2_hidden(X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_24])).

fof(c_0_39,plain,(
    ! [X34,X35] :
      ( ~ r2_hidden(X34,X35)
      | m1_subset_1(X34,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_40,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(k1_connsp_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])])).

fof(c_0_43,plain,(
    ! [X62,X63] :
      ( ~ v2_pre_topc(X62)
      | ~ l1_pre_topc(X62)
      | ~ m1_pre_topc(X63,X62)
      | v2_pre_topc(X63) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

cnf(c_0_44,plain,
    ( k1_connsp_1(X1,X2) != k1_connsp_1(X1,X3)
    | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_connsp_1(X4,X1)
    | ~ r2_hidden(X3,X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_32])).

cnf(c_0_45,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk2_0)))
    | r2_hidden(k1_connsp_1(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])])).

fof(c_0_47,plain,(
    ! [X64,X65] :
      ( ( ~ v1_xboole_0(k1_connsp_1(X64,X65))
        | v2_struct_0(X64)
        | ~ v2_pre_topc(X64)
        | ~ l1_pre_topc(X64)
        | ~ m1_subset_1(X65,u1_struct_0(X64)) )
      & ( v2_connsp_1(k1_connsp_1(X64,X65),X64)
        | v2_struct_0(X64)
        | ~ v2_pre_topc(X64)
        | ~ l1_pre_topc(X64)
        | ~ m1_subset_1(X65,u1_struct_0(X64)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_connsp_1])])])])).

cnf(c_0_48,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_50,plain,
    ( k1_connsp_1(X1,X2) != k1_connsp_1(X1,X3)
    | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_connsp_1(k1_connsp_1(X1,X4),X1)
    | ~ r2_hidden(X3,k1_connsp_1(X1,X4))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_32])).

cnf(c_0_51,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk2_0)))
    | m1_subset_1(k1_connsp_1(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,plain,
    ( v2_connsp_1(k1_connsp_1(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_54,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_36]),c_0_37]),c_0_49])])).

fof(c_0_55,plain,(
    ! [X47,X48] :
      ( v2_struct_0(X47)
      | ~ v2_pre_topc(X47)
      | ~ l1_pre_topc(X47)
      | ~ m1_subset_1(X48,u1_struct_0(X47))
      | r2_hidden(X48,k1_connsp_1(X47,X48)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t40_connsp_1])])])])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(k1_connsp_1(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | k1_connsp_1(esk2_0,X1) != k1_connsp_1(esk2_0,X2)
    | ~ v2_connsp_1(k1_connsp_1(esk2_0,X3),esk2_0)
    | ~ r2_hidden(X2,k1_connsp_1(esk2_0,X3))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_42])])).

cnf(c_0_57,negated_conjecture,
    ( v2_connsp_1(k1_connsp_1(esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_41]),c_0_53]),c_0_42]),c_0_54])])).

cnf(c_0_58,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k1_connsp_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(k1_connsp_1(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | k1_connsp_1(esk2_0,X1) != k1_connsp_1(esk2_0,X2)
    | ~ r2_hidden(X2,k1_connsp_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_41])])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk3_0,k1_connsp_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_41]),c_0_53]),c_0_42]),c_0_54])])).

fof(c_0_61,plain,(
    ! [X36,X37,X38,X39] :
      ( ( ~ v2_connsp_1(X38,X36)
        | v2_connsp_1(X39,X37)
        | X38 != X39
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X37)))
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ m1_pre_topc(X37,X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) )
      & ( ~ v2_connsp_1(X39,X37)
        | v2_connsp_1(X38,X36)
        | X38 != X39
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X37)))
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ m1_pre_topc(X37,X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_connsp_1])])])])).

fof(c_0_62,plain,(
    ! [X42,X43,X44] :
      ( ~ l1_pre_topc(X42)
      | ~ m1_pre_topc(X43,X42)
      | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
      | m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X42))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).

fof(c_0_63,plain,(
    ! [X30] : m1_subset_1(esk10_1(X30),X30) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(k1_connsp_1(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | k1_connsp_1(esk2_0,X1) != k1_connsp_1(esk2_0,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_65,plain,
    ( v2_connsp_1(X3,X4)
    | ~ v2_connsp_1(X1,X2)
    | X3 != X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_pre_topc(X2,X4)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_66,plain,
    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_67,plain,
    ( m1_subset_1(esk10_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

fof(c_0_68,plain,(
    ! [X56,X57] :
      ( ~ r2_hidden(X56,X57)
      | ~ v1_xboole_0(X57) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(k1_connsp_1(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_41])).

cnf(c_0_70,plain,
    ( v2_connsp_1(X1,X2)
    | ~ v2_connsp_1(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_65]),c_0_66])).

cnf(c_0_71,plain,
    ( m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_hidden(X1,k1_connsp_1(X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_32])).

cnf(c_0_72,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk10_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_67])).

cnf(c_0_73,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( m1_subset_1(k1_connsp_1(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_69])).

cnf(c_0_75,plain,
    ( v2_connsp_1(k1_connsp_1(X1,X2),X3)
    | ~ v2_connsp_1(k1_connsp_1(X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_32]),c_0_35])).

cnf(c_0_76,plain,
    ( v1_xboole_0(k1_connsp_1(X1,X2))
    | m1_subset_1(esk10_1(k1_connsp_1(X1,X2)),u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( ~ v1_xboole_0(k1_connsp_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_60])).

fof(c_0_78,plain,(
    ! [X60,X61] :
      ( ~ r2_hidden(X60,X61)
      | r1_tarski(X60,k3_tarski(X61)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t92_zfmisc_1])])).

fof(c_0_79,plain,(
    ! [X32,X33] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(k1_zfmisc_1(X32)))
      | k5_setfam_1(X32,X33) = k3_tarski(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).

cnf(c_0_80,negated_conjecture,
    ( k1_connsp_1(X1,X2) != k1_connsp_1(X1,X3)
    | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_connsp_1(k1_connsp_1(esk2_0,esk3_0),X1)
    | ~ r2_hidden(X3,k1_connsp_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_74])).

cnf(c_0_81,negated_conjecture,
    ( v2_connsp_1(k1_connsp_1(esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_57]),c_0_41])])).

cnf(c_0_82,plain,
    ( m1_subset_1(k1_connsp_1(X1,X2),k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_32]),c_0_35])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(esk10_1(k1_connsp_1(esk2_0,esk3_0)),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_41]),c_0_42])]),c_0_77])).

cnf(c_0_84,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_85,plain,
    ( k5_setfam_1(X2,X1) = k3_tarski(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_86,negated_conjecture,
    ( k1_connsp_1(X1,X2) != k1_connsp_1(X1,X3)
    | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,k1_connsp_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_87,plain,
    ( m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_hidden(X1,k1_connsp_1(X3,X4))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_82])).

cnf(c_0_88,negated_conjecture,
    ( r2_hidden(esk10_1(k1_connsp_1(esk2_0,esk3_0)),k1_connsp_1(esk2_0,esk10_1(k1_connsp_1(esk2_0,esk3_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_83]),c_0_42]),c_0_54])]),c_0_53])).

cnf(c_0_89,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_90,plain,
    ( r1_tarski(X1,k5_setfam_1(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_91,plain,
    ( k5_setfam_1(u1_struct_0(X1),esk5_3(X1,X2,X3)) = X3
    | X3 != k1_connsp_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_92,negated_conjecture,
    ( k1_connsp_1(X1,X2) != k1_connsp_1(X1,esk10_1(k1_connsp_1(esk2_0,esk3_0)))
    | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_72]),c_0_77])).

cnf(c_0_93,negated_conjecture,
    ( m1_subset_1(esk10_1(k1_connsp_1(esk2_0,esk3_0)),u1_struct_0(X1))
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_83])])).

cnf(c_0_94,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk1_0)))
    | r2_hidden(k1_connsp_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_89]),c_0_37])])).

cnf(c_0_95,plain,
    ( r1_tarski(X1,X2)
    | X2 != k1_connsp_1(X3,X4)
    | ~ r2_hidden(X1,esk5_3(X3,X4,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ l1_pre_topc(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_22])).

cnf(c_0_96,negated_conjecture,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_92]),c_0_93])).

cnf(c_0_97,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk1_0)))
    | m1_subset_1(k1_connsp_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_94])).

cnf(c_0_98,plain,
    ( r1_tarski(X1,X2)
    | X2 != k1_connsp_1(X3,X4)
    | ~ v2_connsp_1(X1,X3)
    | ~ r2_hidden(X4,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_30]),c_0_24])).

cnf(c_0_99,negated_conjecture,
    ( m1_subset_1(k1_connsp_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_36]),c_0_37]),c_0_49])])).

cnf(c_0_100,negated_conjecture,
    ( ~ r1_tarski(k1_connsp_1(esk2_0,esk4_0),k1_connsp_1(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_101,negated_conjecture,
    ( r1_tarski(X1,k1_connsp_1(esk1_0,esk3_0))
    | k1_connsp_1(esk1_0,esk3_0) != k1_connsp_1(esk1_0,X2)
    | ~ v2_connsp_1(X1,esk1_0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_37])])).

cnf(c_0_102,negated_conjecture,
    ( ~ r1_tarski(k1_connsp_1(esk2_0,esk3_0),k1_connsp_1(esk1_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_100,c_0_34])).

cnf(c_0_103,negated_conjecture,
    ( k1_connsp_1(esk1_0,esk3_0) != k1_connsp_1(esk1_0,X1)
    | ~ v2_connsp_1(k1_connsp_1(esk2_0,esk3_0),esk1_0)
    | ~ r2_hidden(X1,k1_connsp_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_74]),c_0_36]),c_0_37])]),c_0_102])).

cnf(c_0_104,negated_conjecture,
    ( k1_connsp_1(esk1_0,esk3_0) != k1_connsp_1(esk1_0,X1)
    | ~ r2_hidden(X1,k1_connsp_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_81]),c_0_36]),c_0_37]),c_0_49])])).

cnf(c_0_105,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_104,c_0_60]),
    [proof]).
%------------------------------------------------------------------------------
