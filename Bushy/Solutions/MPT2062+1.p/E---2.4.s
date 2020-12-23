%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow19__t22_yellow19.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:50 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   39 (  99 expanded)
%              Number of clauses        :   26 (  37 expanded)
%              Number of leaves         :    6 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :  138 ( 510 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   23 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t22_yellow19,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2,X3,X4] :
          ( ( r1_tarski(X2,X3)
            & r2_waybel_7(X1,X2,X4) )
         => r2_waybel_7(X1,X3,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t22_yellow19.p',t22_yellow19)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t22_yellow19.p',t3_subset)).

fof(d5_waybel_7,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2,X3] :
          ( r2_waybel_7(X1,X2,X3)
        <=> ! [X4] :
              ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v3_pre_topc(X4,X1)
                  & r2_hidden(X3,X4) )
               => r2_hidden(X4,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t22_yellow19.p',d5_waybel_7)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t22_yellow19.p',t4_subset)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t22_yellow19.p',t5_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t22_yellow19.p',t2_subset)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2,X3,X4] :
            ( ( r1_tarski(X2,X3)
              & r2_waybel_7(X1,X2,X4) )
           => r2_waybel_7(X1,X3,X4) ) ) ),
    inference(assume_negation,[status(cth)],[t22_yellow19])).

fof(c_0_7,plain,(
    ! [X27,X28] :
      ( ( ~ m1_subset_1(X27,k1_zfmisc_1(X28))
        | r1_tarski(X27,X28) )
      & ( ~ r1_tarski(X27,X28)
        | m1_subset_1(X27,k1_zfmisc_1(X28)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_8,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & r1_tarski(esk2_0,esk3_0)
    & r2_waybel_7(esk1_0,esk2_0,esk4_0)
    & ~ r2_waybel_7(esk1_0,esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).

fof(c_0_9,plain,(
    ! [X11,X12,X13,X14,X15,X16] :
      ( ( ~ r2_waybel_7(X11,X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ v3_pre_topc(X14,X11)
        | ~ r2_hidden(X13,X14)
        | r2_hidden(X14,X12)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( m1_subset_1(esk5_3(X11,X15,X16),k1_zfmisc_1(u1_struct_0(X11)))
        | r2_waybel_7(X11,X15,X16)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( v3_pre_topc(esk5_3(X11,X15,X16),X11)
        | r2_waybel_7(X11,X15,X16)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( r2_hidden(X16,esk5_3(X11,X15,X16))
        | r2_waybel_7(X11,X15,X16)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( ~ r2_hidden(esk5_3(X11,X15,X16),X15)
        | r2_waybel_7(X11,X15,X16)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_waybel_7])])])])])])).

fof(c_0_10,plain,(
    ! [X29,X30,X31] :
      ( ~ r2_hidden(X29,X30)
      | ~ m1_subset_1(X30,k1_zfmisc_1(X31))
      | m1_subset_1(X29,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_11,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,plain,(
    ! [X32,X33,X34] :
      ( ~ r2_hidden(X32,X33)
      | ~ m1_subset_1(X33,k1_zfmisc_1(X34))
      | ~ v1_xboole_0(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_14,plain,
    ( m1_subset_1(esk5_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_waybel_7(X1,X2,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,plain,
    ( v3_pre_topc(esk5_3(X1,X2,X3),X1)
    | r2_waybel_7(X1,X2,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_18,plain,(
    ! [X25,X26] :
      ( ~ m1_subset_1(X25,X26)
      | v1_xboole_0(X26)
      | r2_hidden(X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_19,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( r2_hidden(X4,X2)
    | ~ r2_waybel_7(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X4,X1)
    | ~ r2_hidden(X3,X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk5_3(esk1_0,X1,X2),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | r2_waybel_7(esk1_0,X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])])).

cnf(c_0_24,negated_conjecture,
    ( v3_pre_topc(esk5_3(esk1_0,X1,X2),esk1_0)
    | r2_waybel_7(esk1_0,X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_15]),c_0_16])])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,esk5_3(X2,X3,X1))
    | r2_waybel_7(X2,X3,X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(X1,esk3_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,X1,X2),X3)
    | r2_waybel_7(esk1_0,X1,X2)
    | ~ r2_hidden(X4,esk5_3(esk1_0,X1,X2))
    | ~ r2_waybel_7(esk1_0,X3,X4) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_15]),c_0_16])]),c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(X1,esk5_3(esk1_0,X2,X1))
    | r2_waybel_7(esk1_0,X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_15]),c_0_16])])).

cnf(c_0_31,plain,
    ( r2_waybel_7(X1,X2,X3)
    | ~ r2_hidden(esk5_3(X1,X2,X3),X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,X1,X2),X3)
    | r2_waybel_7(esk1_0,X1,X2)
    | ~ r2_waybel_7(esk1_0,X3,X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( r2_waybel_7(esk1_0,esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_35,negated_conjecture,
    ( r2_waybel_7(X1,esk3_0,X2)
    | ~ r2_hidden(esk5_3(X1,esk3_0,X2),esk2_0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,X1,esk4_0),esk2_0)
    | r2_waybel_7(esk1_0,X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( ~ r2_waybel_7(esk1_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_15]),c_0_16])]),c_0_37]),
    [proof]).
%------------------------------------------------------------------------------
