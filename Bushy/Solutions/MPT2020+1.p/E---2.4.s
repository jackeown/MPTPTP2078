%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : waybel_9__t19_waybel_9.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:08 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 127 expanded)
%              Number of clauses        :   30 (  47 expanded)
%              Number of leaves         :    6 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :  144 ( 693 expanded)
%              Number of equality atoms :   22 ( 140 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t19_waybel_9,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
                 => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                      & X3 = X4
                      & v1_tops_2(X3,X1) )
                   => v1_tops_2(X4,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t19_waybel_9.p',t19_waybel_9)).

fof(free_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3,X4] :
          ( g1_pre_topc(X1,X2) = g1_pre_topc(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t19_waybel_9.p',free_g1_pre_topc)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t19_waybel_9.p',dt_u1_pre_topc)).

fof(d1_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v1_tops_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r2_hidden(X3,X2)
                 => v3_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t19_waybel_9.p',d1_tops_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t19_waybel_9.p',t4_subset)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t19_waybel_9.p',d5_pre_topc)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( l1_pre_topc(X2)
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
                   => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                        & X3 = X4
                        & v1_tops_2(X3,X1) )
                     => v1_tops_2(X4,X2) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t19_waybel_9])).

fof(c_0_7,plain,(
    ! [X26,X27,X28,X29] :
      ( ( X26 = X28
        | g1_pre_topc(X26,X27) != g1_pre_topc(X28,X29)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(X26))) )
      & ( X27 = X29
        | g1_pre_topc(X26,X27) != g1_pre_topc(X28,X29)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(X26))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).

fof(c_0_8,plain,(
    ! [X21] :
      ( ~ l1_pre_topc(X21)
      | m1_subset_1(u1_pre_topc(X21),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X21)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_9,plain,(
    ! [X12,X13,X14] :
      ( ( ~ v1_tops_2(X13,X12)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ r2_hidden(X14,X13)
        | v3_pre_topc(X14,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk5_2(X12,X13),k1_zfmisc_1(u1_struct_0(X12)))
        | v1_tops_2(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | ~ l1_pre_topc(X12) )
      & ( r2_hidden(esk5_2(X12,X13),X13)
        | v1_tops_2(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | ~ l1_pre_topc(X12) )
      & ( ~ v3_pre_topc(esk5_2(X12,X13),X12)
        | v1_tops_2(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | ~ l1_pre_topc(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_2])])])])])).

fof(c_0_10,plain,(
    ! [X36,X37,X38] :
      ( ~ r2_hidden(X36,X37)
      | ~ m1_subset_1(X37,k1_zfmisc_1(X38))
      | m1_subset_1(X36,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_11,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    & g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))
    & esk3_0 = esk4_0
    & v1_tops_2(esk3_0,esk1_0)
    & ~ v1_tops_2(esk4_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_12,plain,
    ( X1 = X2
    | g1_pre_topc(X3,X1) != g1_pre_topc(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tops_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( esk3_0 = esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( u1_pre_topc(X1) = X2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_21,plain,(
    ! [X16,X17] :
      ( ( ~ v3_pre_topc(X17,X16)
        | r2_hidden(X17,u1_pre_topc(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ l1_pre_topc(X16) )
      & ( ~ r2_hidden(X17,u1_pre_topc(X16))
        | v3_pre_topc(X17,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ l1_pre_topc(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_23,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ v1_tops_2(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( v1_tops_2(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_25,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_26,negated_conjecture,
    ( ~ v1_tops_2(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( u1_pre_topc(esk2_0) = X1
    | g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) != g1_pre_topc(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( v3_pre_topc(X1,esk1_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_22]),c_0_24]),c_0_25])])).

cnf(c_0_32,plain,
    ( v1_tops_2(X2,X1)
    | ~ v3_pre_topc(esk5_2(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_33,negated_conjecture,
    ( ~ v1_tops_2(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_26,c_0_17])).

cnf(c_0_34,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( u1_pre_topc(esk2_0) = u1_pre_topc(esk1_0) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(X1,u1_pre_topc(esk1_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_25])]),c_0_31])).

cnf(c_0_38,plain,
    ( r2_hidden(esk5_2(X1,X2),X2)
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_39,negated_conjecture,
    ( ~ v3_pre_topc(esk5_2(esk2_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_27]),c_0_20])]),c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( v3_pre_topc(X1,esk2_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_20])]),c_0_36]),c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk5_2(esk2_0,esk3_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_27]),c_0_20])]),c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])]),
    [proof]).
%------------------------------------------------------------------------------
