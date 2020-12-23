%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1712+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:38 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 416 expanded)
%              Number of clauses        :   50 ( 136 expanded)
%              Number of leaves         :    7 (  97 expanded)
%              Depth                    :   13
%              Number of atoms          :  397 (4865 expanded)
%              Number of equality atoms :   26 ( 580 expanded)
%              Maximal formula depth    :   27 (   6 average)
%              Maximal clause size      :   60 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t21_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X3))
                         => ( ( X5 = X4
                              & X6 = X4 )
                           => ! [X7] :
                                ( m1_connsp_2(X7,X2,X5)
                               => ! [X8] :
                                    ( m1_connsp_2(X8,X3,X6)
                                   => ? [X9] :
                                        ( m1_connsp_2(X9,k1_tsep_1(X1,X2,X3),X4)
                                        & r1_tarski(X9,k2_xboole_0(X7,X8)) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_tmap_1)).

fof(t20_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X3))
                         => ( ( X5 = X4
                              & X6 = X4 )
                           => ! [X7] :
                                ( m1_connsp_2(X7,X2,X5)
                               => ! [X8] :
                                    ( m1_connsp_2(X8,X3,X6)
                                   => ? [X9] :
                                        ( m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3))))
                                        & v3_pre_topc(X9,k1_tsep_1(X1,X2,X3))
                                        & r2_hidden(X4,X9)
                                        & r1_tarski(X9,k2_xboole_0(X7,X8)) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tmap_1)).

fof(dt_k1_tsep_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X2,X1)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X3,X1) )
     => ( ~ v2_struct_0(k1_tsep_1(X1,X2,X3))
        & v1_pre_topc(k1_tsep_1(X1,X2,X3))
        & m1_pre_topc(k1_tsep_1(X1,X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(t5_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ( v3_pre_topc(X2,X1)
                  & r2_hidden(X3,X2) )
               => m1_connsp_2(X2,X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & m1_pre_topc(X3,X1) )
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))
                   => ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X2))
                       => ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X3))
                           => ( ( X5 = X4
                                & X6 = X4 )
                             => ! [X7] :
                                  ( m1_connsp_2(X7,X2,X5)
                                 => ! [X8] :
                                      ( m1_connsp_2(X8,X3,X6)
                                     => ? [X9] :
                                          ( m1_connsp_2(X9,k1_tsep_1(X1,X2,X3),X4)
                                          & r1_tarski(X9,k2_xboole_0(X7,X8)) ) ) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t21_tmap_1])).

fof(c_0_8,plain,(
    ! [X17,X18,X19,X20,X21,X22,X23,X24] :
      ( ( m1_subset_1(esk1_8(X17,X18,X19,X20,X21,X22,X23,X24),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X17,X18,X19))))
        | ~ m1_connsp_2(X24,X19,X22)
        | ~ m1_connsp_2(X23,X18,X21)
        | X21 != X20
        | X22 != X20
        | ~ m1_subset_1(X22,u1_struct_0(X19))
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ m1_subset_1(X20,u1_struct_0(k1_tsep_1(X17,X18,X19)))
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( v3_pre_topc(esk1_8(X17,X18,X19,X20,X21,X22,X23,X24),k1_tsep_1(X17,X18,X19))
        | ~ m1_connsp_2(X24,X19,X22)
        | ~ m1_connsp_2(X23,X18,X21)
        | X21 != X20
        | X22 != X20
        | ~ m1_subset_1(X22,u1_struct_0(X19))
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ m1_subset_1(X20,u1_struct_0(k1_tsep_1(X17,X18,X19)))
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( r2_hidden(X20,esk1_8(X17,X18,X19,X20,X21,X22,X23,X24))
        | ~ m1_connsp_2(X24,X19,X22)
        | ~ m1_connsp_2(X23,X18,X21)
        | X21 != X20
        | X22 != X20
        | ~ m1_subset_1(X22,u1_struct_0(X19))
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ m1_subset_1(X20,u1_struct_0(k1_tsep_1(X17,X18,X19)))
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( r1_tarski(esk1_8(X17,X18,X19,X20,X21,X22,X23,X24),k2_xboole_0(X23,X24))
        | ~ m1_connsp_2(X24,X19,X22)
        | ~ m1_connsp_2(X23,X18,X21)
        | X21 != X20
        | X22 != X20
        | ~ m1_subset_1(X22,u1_struct_0(X19))
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ m1_subset_1(X20,u1_struct_0(k1_tsep_1(X17,X18,X19)))
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t20_tmap_1])])])])])])).

fof(c_0_9,negated_conjecture,(
    ! [X40] :
      ( ~ v2_struct_0(esk2_0)
      & v2_pre_topc(esk2_0)
      & l1_pre_topc(esk2_0)
      & ~ v2_struct_0(esk3_0)
      & m1_pre_topc(esk3_0,esk2_0)
      & ~ v2_struct_0(esk4_0)
      & m1_pre_topc(esk4_0,esk2_0)
      & m1_subset_1(esk5_0,u1_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0)))
      & m1_subset_1(esk6_0,u1_struct_0(esk3_0))
      & m1_subset_1(esk7_0,u1_struct_0(esk4_0))
      & esk6_0 = esk5_0
      & esk7_0 = esk5_0
      & m1_connsp_2(esk8_0,esk3_0,esk6_0)
      & m1_connsp_2(esk9_0,esk4_0,esk7_0)
      & ( ~ m1_connsp_2(X40,k1_tsep_1(esk2_0,esk3_0,esk4_0),esk5_0)
        | ~ r1_tarski(X40,k2_xboole_0(esk8_0,esk9_0)) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])])).

cnf(c_0_10,plain,
    ( m1_subset_1(esk1_8(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3))))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X8,X3,X6)
    | ~ m1_connsp_2(X7,X2,X5)
    | X5 != X4
    | X6 != X4
    | ~ m1_subset_1(X6,u1_struct_0(X3))
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( esk7_0 = esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( esk6_0 = esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_15,plain,(
    ! [X12,X13,X14] :
      ( ( ~ v2_struct_0(k1_tsep_1(X12,X13,X14))
        | v2_struct_0(X12)
        | ~ l1_pre_topc(X12)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,X12)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X12) )
      & ( v1_pre_topc(k1_tsep_1(X12,X13,X14))
        | v2_struct_0(X12)
        | ~ l1_pre_topc(X12)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,X12)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X12) )
      & ( m1_pre_topc(k1_tsep_1(X12,X13,X14),X12)
        | v2_struct_0(X12)
        | ~ l1_pre_topc(X12)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,X12)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).

cnf(c_0_16,plain,
    ( m1_subset_1(esk1_8(X1,X2,X3,X4,X4,X4,X5,X6),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3))))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X6,X3,X4)
    | ~ m1_connsp_2(X5,X2,X4)
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_10])])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_27,negated_conjecture,
    ( m1_connsp_2(esk9_0,esk4_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_28,plain,
    ( m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_29,plain,(
    ! [X29,X30,X31] :
      ( v2_struct_0(X29)
      | ~ v2_pre_topc(X29)
      | ~ l1_pre_topc(X29)
      | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
      | ~ m1_subset_1(X31,u1_struct_0(X29))
      | ~ v3_pre_topc(X30,X29)
      | ~ r2_hidden(X31,X30)
      | m1_connsp_2(X30,X29,X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_connsp_2])])])])).

fof(c_0_30,plain,(
    ! [X26,X27,X28] :
      ( ~ r2_hidden(X26,X27)
      | ~ m1_subset_1(X27,k1_zfmisc_1(X28))
      | m1_subset_1(X26,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk1_8(esk2_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,X1,X2),k1_zfmisc_1(u1_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0))))
    | ~ m1_connsp_2(X2,esk4_0,esk5_0)
    | ~ m1_connsp_2(X1,esk3_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23])]),c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( m1_connsp_2(esk9_0,esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_27,c_0_12])).

cnf(c_0_33,negated_conjecture,
    ( m1_connsp_2(esk8_0,esk3_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_34,plain,(
    ! [X15,X16] :
      ( ~ l1_pre_topc(X15)
      | ~ m1_pre_topc(X16,X15)
      | l1_pre_topc(X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_35,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(k1_tsep_1(esk2_0,X1,esk4_0),esk2_0)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_20]),c_0_22])]),c_0_26]),c_0_24])).

fof(c_0_36,plain,(
    ! [X10,X11] :
      ( ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | ~ m1_pre_topc(X11,X10)
      | v2_pre_topc(X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

cnf(c_0_37,plain,
    ( v2_struct_0(X1)
    | m1_connsp_2(X2,X1,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v3_pre_topc(X2,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk1_8(esk2_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,X1,esk9_0),k1_zfmisc_1(u1_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0))))
    | ~ m1_connsp_2(X1,esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( m1_connsp_2(esk8_0,esk3_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_33,c_0_14])).

cnf(c_0_41,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk2_0,esk3_0,esk4_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_21]),c_0_25])).

cnf(c_0_43,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,plain,
    ( v3_pre_topc(esk1_8(X1,X2,X3,X4,X5,X6,X7,X8),k1_tsep_1(X1,X2,X3))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X8,X3,X6)
    | ~ m1_connsp_2(X7,X2,X5)
    | X5 != X4
    | X6 != X4
    | ~ m1_subset_1(X6,u1_struct_0(X3))
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_45,plain,
    ( m1_connsp_2(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X3,X1)
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk1_8(esk2_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,esk8_0,esk9_0),k1_zfmisc_1(u1_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( l1_pre_topc(k1_tsep_1(esk2_0,esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_22])])).

cnf(c_0_48,negated_conjecture,
    ( v2_pre_topc(k1_tsep_1(esk2_0,esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_42]),c_0_22]),c_0_23])])).

cnf(c_0_49,plain,
    ( v3_pre_topc(esk1_8(X1,X2,X3,X4,X4,X4,X5,X6),k1_tsep_1(X1,X2,X3))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X6,X3,X4)
    | ~ m1_connsp_2(X5,X2,X4)
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_44])])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,esk1_8(X2,X3,X4,X1,X5,X6,X7,X8))
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X8,X4,X6)
    | ~ m1_connsp_2(X7,X3,X5)
    | X5 != X1
    | X6 != X1
    | ~ m1_subset_1(X6,u1_struct_0(X4))
    | ~ m1_subset_1(X5,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(k1_tsep_1(X2,X3,X4)))
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_51,negated_conjecture,
    ( m1_connsp_2(esk1_8(esk2_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,esk8_0,esk9_0),k1_tsep_1(esk2_0,esk3_0,esk4_0),X1)
    | v2_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0))
    | ~ r2_hidden(X1,esk1_8(esk2_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,esk8_0,esk9_0))
    | ~ v3_pre_topc(esk1_8(esk2_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,esk8_0,esk9_0),k1_tsep_1(esk2_0,esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_48])])).

cnf(c_0_52,negated_conjecture,
    ( v3_pre_topc(esk1_8(esk2_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,X1,X2),k1_tsep_1(esk2_0,esk3_0,esk4_0))
    | ~ m1_connsp_2(X2,esk4_0,esk5_0)
    | ~ m1_connsp_2(X1,esk3_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23])]),c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,esk1_8(X2,X3,X4,X1,X1,X1,X5,X6))
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X6,X4,X1)
    | ~ m1_connsp_2(X5,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(k1_tsep_1(X2,X3,X4)))
    | ~ m1_subset_1(X1,u1_struct_0(X4))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_50])])).

cnf(c_0_54,negated_conjecture,
    ( m1_connsp_2(esk1_8(esk2_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,esk8_0,esk9_0),k1_tsep_1(esk2_0,esk3_0,esk4_0),X1)
    | v2_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0))
    | ~ r2_hidden(X1,esk1_8(esk2_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,esk8_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_32]),c_0_40])])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk5_0,esk1_8(esk2_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,X1,X2))
    | ~ m1_connsp_2(X2,esk4_0,esk5_0)
    | ~ m1_connsp_2(X1,esk3_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23])]),c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_56,plain,
    ( r1_tarski(esk1_8(X1,X2,X3,X4,X5,X6,X7,X8),k2_xboole_0(X7,X8))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X8,X3,X6)
    | ~ m1_connsp_2(X7,X2,X5)
    | X5 != X4
    | X6 != X4
    | ~ m1_subset_1(X6,u1_struct_0(X3))
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_57,negated_conjecture,
    ( ~ m1_connsp_2(X1,k1_tsep_1(esk2_0,esk3_0,esk4_0),esk5_0)
    | ~ r1_tarski(X1,k2_xboole_0(esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_58,negated_conjecture,
    ( m1_connsp_2(esk1_8(esk2_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,esk8_0,esk9_0),k1_tsep_1(esk2_0,esk3_0,esk4_0),esk5_0)
    | v2_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_32]),c_0_40])])).

cnf(c_0_59,plain,
    ( r1_tarski(esk1_8(X1,X2,X3,X4,X4,X4,X5,X6),k2_xboole_0(X5,X6))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X6,X3,X4)
    | ~ m1_connsp_2(X5,X2,X4)
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_56])])).

cnf(c_0_60,negated_conjecture,
    ( v2_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0))
    | ~ r1_tarski(esk1_8(esk2_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,esk8_0,esk9_0),k2_xboole_0(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(esk1_8(esk2_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,X1,X2),k2_xboole_0(X1,X2))
    | ~ m1_connsp_2(X2,esk4_0,esk5_0)
    | ~ m1_connsp_2(X1,esk3_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23])]),c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_62,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k1_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_63,negated_conjecture,
    ( v2_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_32]),c_0_40])])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_20]),c_0_21]),c_0_22])]),c_0_26]),c_0_25]),c_0_24]),
    [proof]).

%------------------------------------------------------------------------------
