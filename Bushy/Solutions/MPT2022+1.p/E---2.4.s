%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : waybel_9__t21_waybel_9.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:08 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   29 ( 108 expanded)
%              Number of clauses        :   20 (  35 expanded)
%              Number of leaves         :    4 (  27 expanded)
%              Depth                    :    5
%              Number of atoms          :  143 ( 657 expanded)
%              Number of equality atoms :    3 (  15 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/waybel_9__t21_waybel_9.p',t38_yellow_6)).

fof(t21_waybel_9,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))
             => m1_connsp_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t21_waybel_9.p',t21_waybel_9)).

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
    file('/export/starexec/sandbox2/benchmark/waybel_9__t21_waybel_9.p',t5_connsp_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t21_waybel_9.p',t4_subset)).

fof(c_0_4,plain,(
    ! [X61,X62,X63] :
      ( ( m1_subset_1(esk11_3(X61,X62,X63),k1_zfmisc_1(u1_struct_0(X61)))
        | ~ m1_subset_1(X63,u1_struct_0(k9_yellow_6(X61,X62)))
        | ~ m1_subset_1(X62,u1_struct_0(X61))
        | v2_struct_0(X61)
        | ~ v2_pre_topc(X61)
        | ~ l1_pre_topc(X61) )
      & ( esk11_3(X61,X62,X63) = X63
        | ~ m1_subset_1(X63,u1_struct_0(k9_yellow_6(X61,X62)))
        | ~ m1_subset_1(X62,u1_struct_0(X61))
        | v2_struct_0(X61)
        | ~ v2_pre_topc(X61)
        | ~ l1_pre_topc(X61) )
      & ( r2_hidden(X62,esk11_3(X61,X62,X63))
        | ~ m1_subset_1(X63,u1_struct_0(k9_yellow_6(X61,X62)))
        | ~ m1_subset_1(X62,u1_struct_0(X61))
        | v2_struct_0(X61)
        | ~ v2_pre_topc(X61)
        | ~ l1_pre_topc(X61) )
      & ( v3_pre_topc(esk11_3(X61,X62,X63),X61)
        | ~ m1_subset_1(X63,u1_struct_0(k9_yellow_6(X61,X62)))
        | ~ m1_subset_1(X62,u1_struct_0(X61))
        | v2_struct_0(X61)
        | ~ v2_pre_topc(X61)
        | ~ l1_pre_topc(X61) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_yellow_6])])])])])])).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))
               => m1_connsp_2(X3,X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t21_waybel_9])).

fof(c_0_6,plain,(
    ! [X70,X71,X72] :
      ( v2_struct_0(X70)
      | ~ v2_pre_topc(X70)
      | ~ l1_pre_topc(X70)
      | ~ m1_subset_1(X71,k1_zfmisc_1(u1_struct_0(X70)))
      | ~ m1_subset_1(X72,u1_struct_0(X70))
      | ~ v3_pre_topc(X71,X70)
      | ~ r2_hidden(X72,X71)
      | m1_connsp_2(X71,X70,X72) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_connsp_2])])])])).

fof(c_0_7,plain,(
    ! [X67,X68,X69] :
      ( ~ r2_hidden(X67,X68)
      | ~ m1_subset_1(X68,k1_zfmisc_1(X69))
      | m1_subset_1(X67,X69) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_8,plain,
    ( v3_pre_topc(esk11_3(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,plain,
    ( esk11_3(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk3_0,u1_struct_0(k9_yellow_6(esk1_0,esk2_0)))
    & ~ m1_connsp_2(esk3_0,esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,esk11_3(X2,X1,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(k9_yellow_6(X2,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_12,plain,
    ( m1_subset_1(esk11_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,plain,
    ( v2_struct_0(X1)
    | m1_connsp_2(X2,X1,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v3_pre_topc(X2,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,plain,
    ( v3_pre_topc(X1,X2)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(X2,X3)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(k9_yellow_6(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X2)
    | v2_struct_0(X3)
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X3,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X3) ),
    inference(spm,[status(thm)],[c_0_11,c_0_9])).

cnf(c_0_22,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(X2,X3)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_9])).

cnf(c_0_23,negated_conjecture,
    ( ~ m1_connsp_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_24,plain,
    ( m1_connsp_2(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ v3_pre_topc(X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_25,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_16]),c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_16]),c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_18]),c_0_19])]),c_0_20]),
    [proof]).
%------------------------------------------------------------------------------
