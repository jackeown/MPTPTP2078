%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:13:14 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 149 expanded)
%              Number of clauses        :   26 (  54 expanded)
%              Number of leaves         :    7 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :  246 ( 766 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   27 (   5 average)
%              Maximal clause size      :   90 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t26_tops_2,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v1_tops_2(X2,X1)
           => v3_pre_topc(k5_setfam_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tops_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(t7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => ( r2_hidden(X4,X2)
                 => r2_hidden(X4,X3) ) )
           => r1_tarski(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

fof(d1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v2_pre_topc(X1)
      <=> ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
          & ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ( r1_tarski(X2,u1_pre_topc(X1))
               => r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)) ) )
          & ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X1))
                      & r2_hidden(X3,u1_pre_topc(X1)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ( v1_tops_2(X2,X1)
             => v3_pre_topc(k5_setfam_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t26_tops_2])).

fof(c_0_8,plain,(
    ! [X22,X23,X24] :
      ( ( ~ v1_tops_2(X23,X22)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ r2_hidden(X24,X23)
        | v3_pre_topc(X24,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))
        | ~ l1_pre_topc(X22) )
      & ( m1_subset_1(esk5_2(X22,X23),k1_zfmisc_1(u1_struct_0(X22)))
        | v1_tops_2(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))
        | ~ l1_pre_topc(X22) )
      & ( r2_hidden(esk5_2(X22,X23),X23)
        | v1_tops_2(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))
        | ~ l1_pre_topc(X22) )
      & ( ~ v3_pre_topc(esk5_2(X22,X23),X22)
        | v1_tops_2(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))
        | ~ l1_pre_topc(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_2])])])])])).

fof(c_0_9,plain,(
    ! [X9,X10,X11] :
      ( ~ r2_hidden(X9,X10)
      | ~ m1_subset_1(X10,k1_zfmisc_1(X11))
      | m1_subset_1(X9,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_10,negated_conjecture,
    ( v2_pre_topc(esk6_0)
    & l1_pre_topc(esk6_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0))))
    & v1_tops_2(esk7_0,esk6_0)
    & ~ v3_pre_topc(k5_setfam_1(u1_struct_0(esk6_0),esk7_0),esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_11,plain,(
    ! [X19,X20] :
      ( ( ~ v3_pre_topc(X20,X19)
        | r2_hidden(X20,u1_pre_topc(X19))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) )
      & ( ~ r2_hidden(X20,u1_pre_topc(X19))
        | v3_pre_topc(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

fof(c_0_12,plain,(
    ! [X21] :
      ( ~ l1_pre_topc(X21)
      | m1_subset_1(u1_pre_topc(X21),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X21)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_13,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tops_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( ~ v3_pre_topc(k5_setfam_1(u1_struct_0(esk6_0),esk7_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( v3_pre_topc(X1,X2)
    | ~ v1_tops_2(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) ),
    inference(csr,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( v1_tops_2(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_22,plain,(
    ! [X5,X6,X7] :
      ( ( m1_subset_1(esk1_3(X5,X6,X7),X5)
        | r1_tarski(X6,X7)
        | ~ m1_subset_1(X7,k1_zfmisc_1(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(X5)) )
      & ( r2_hidden(esk1_3(X5,X6,X7),X6)
        | r1_tarski(X6,X7)
        | ~ m1_subset_1(X7,k1_zfmisc_1(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(X5)) )
      & ( ~ r2_hidden(esk1_3(X5,X6,X7),X7)
        | r1_tarski(X6,X7)
        | ~ m1_subset_1(X7,k1_zfmisc_1(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(X5)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).

cnf(c_0_23,negated_conjecture,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(esk6_0),esk7_0),u1_pre_topc(esk6_0))
    | ~ m1_subset_1(k5_setfam_1(u1_struct_0(esk6_0),esk7_0),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

cnf(c_0_24,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_18])).

fof(c_0_25,plain,(
    ! [X12,X13,X14,X15] :
      ( ( r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | ~ r1_tarski(X13,u1_pre_topc(X12))
        | r2_hidden(k5_setfam_1(u1_struct_0(X12),X13),u1_pre_topc(X12))
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ r2_hidden(X14,u1_pre_topc(X12))
        | ~ r2_hidden(X15,u1_pre_topc(X12))
        | r2_hidden(k9_subset_1(u1_struct_0(X12),X14,X15),u1_pre_topc(X12))
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk3_1(X12),k1_zfmisc_1(u1_struct_0(X12)))
        | m1_subset_1(esk2_1(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk4_1(X12),k1_zfmisc_1(u1_struct_0(X12)))
        | m1_subset_1(esk2_1(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( r2_hidden(esk3_1(X12),u1_pre_topc(X12))
        | m1_subset_1(esk2_1(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( r2_hidden(esk4_1(X12),u1_pre_topc(X12))
        | m1_subset_1(esk2_1(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X12),esk3_1(X12),esk4_1(X12)),u1_pre_topc(X12))
        | m1_subset_1(esk2_1(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk3_1(X12),k1_zfmisc_1(u1_struct_0(X12)))
        | r1_tarski(esk2_1(X12),u1_pre_topc(X12))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk4_1(X12),k1_zfmisc_1(u1_struct_0(X12)))
        | r1_tarski(esk2_1(X12),u1_pre_topc(X12))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( r2_hidden(esk3_1(X12),u1_pre_topc(X12))
        | r1_tarski(esk2_1(X12),u1_pre_topc(X12))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( r2_hidden(esk4_1(X12),u1_pre_topc(X12))
        | r1_tarski(esk2_1(X12),u1_pre_topc(X12))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X12),esk3_1(X12),esk4_1(X12)),u1_pre_topc(X12))
        | r1_tarski(esk2_1(X12),u1_pre_topc(X12))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk3_1(X12),k1_zfmisc_1(u1_struct_0(X12)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X12),esk2_1(X12)),u1_pre_topc(X12))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk4_1(X12),k1_zfmisc_1(u1_struct_0(X12)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X12),esk2_1(X12)),u1_pre_topc(X12))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( r2_hidden(esk3_1(X12),u1_pre_topc(X12))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X12),esk2_1(X12)),u1_pre_topc(X12))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( r2_hidden(esk4_1(X12),u1_pre_topc(X12))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X12),esk2_1(X12)),u1_pre_topc(X12))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X12),esk3_1(X12),esk4_1(X12)),u1_pre_topc(X12))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X12),esk2_1(X12)),u1_pre_topc(X12))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_27,negated_conjecture,
    ( v3_pre_topc(X1,esk6_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_17])])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_20])).

cnf(c_0_29,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(esk6_0),esk7_0),u1_pre_topc(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_17])])).

cnf(c_0_31,plain,
    ( r2_hidden(k5_setfam_1(u1_struct_0(X2),X1),u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ r1_tarski(X1,u1_pre_topc(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( v2_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_33,plain,
    ( r1_tarski(X2,X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(X1,u1_pre_topc(esk6_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_17])]),c_0_28])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,u1_pre_topc(X2))
    | r2_hidden(esk1_3(k1_zfmisc_1(u1_struct_0(X2)),X1,u1_pre_topc(X2)),X1)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_18])).

cnf(c_0_36,negated_conjecture,
    ( ~ r1_tarski(esk7_0,u1_pre_topc(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_17]),c_0_20])])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(X1,u1_pre_topc(esk6_0))
    | ~ r2_hidden(esk1_3(X2,X1,u1_pre_topc(esk6_0)),esk7_0)
    | ~ m1_subset_1(u1_pre_topc(esk6_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk1_3(k1_zfmisc_1(u1_struct_0(esk6_0)),esk7_0,u1_pre_topc(esk6_0)),esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_20]),c_0_17])]),c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( ~ m1_subset_1(u1_pre_topc(esk6_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_20])]),c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_18]),c_0_17])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:53:38 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.18/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.18/0.38  #
% 0.18/0.38  # Preprocessing time       : 0.029 s
% 0.18/0.38  # Presaturation interreduction done
% 0.18/0.38  
% 0.18/0.38  # Proof found!
% 0.18/0.38  # SZS status Theorem
% 0.18/0.38  # SZS output start CNFRefutation
% 0.18/0.38  fof(t26_tops_2, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(v1_tops_2(X2,X1)=>v3_pre_topc(k5_setfam_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_tops_2)).
% 0.18/0.38  fof(d1_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(v1_tops_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X3,X2)=>v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_2)).
% 0.18/0.38  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.18/0.38  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 0.18/0.38  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.18/0.38  fof(t7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,X2)=>r2_hidden(X4,X3)))=>r1_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_subset_1)).
% 0.18/0.38  fof(d1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(X1)<=>((r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,u1_pre_topc(X1))=>r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,u1_pre_topc(X1))&r2_hidden(X3,u1_pre_topc(X1)))=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 0.18/0.38  fof(c_0_7, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(v1_tops_2(X2,X1)=>v3_pre_topc(k5_setfam_1(u1_struct_0(X1),X2),X1))))), inference(assume_negation,[status(cth)],[t26_tops_2])).
% 0.18/0.38  fof(c_0_8, plain, ![X22, X23, X24]:((~v1_tops_2(X23,X22)|(~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))|(~r2_hidden(X24,X23)|v3_pre_topc(X24,X22)))|~m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))|~l1_pre_topc(X22))&((m1_subset_1(esk5_2(X22,X23),k1_zfmisc_1(u1_struct_0(X22)))|v1_tops_2(X23,X22)|~m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))|~l1_pre_topc(X22))&((r2_hidden(esk5_2(X22,X23),X23)|v1_tops_2(X23,X22)|~m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))|~l1_pre_topc(X22))&(~v3_pre_topc(esk5_2(X22,X23),X22)|v1_tops_2(X23,X22)|~m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))|~l1_pre_topc(X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_2])])])])])).
% 0.18/0.38  fof(c_0_9, plain, ![X9, X10, X11]:(~r2_hidden(X9,X10)|~m1_subset_1(X10,k1_zfmisc_1(X11))|m1_subset_1(X9,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.18/0.38  fof(c_0_10, negated_conjecture, ((v2_pre_topc(esk6_0)&l1_pre_topc(esk6_0))&(m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0))))&(v1_tops_2(esk7_0,esk6_0)&~v3_pre_topc(k5_setfam_1(u1_struct_0(esk6_0),esk7_0),esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.18/0.38  fof(c_0_11, plain, ![X19, X20]:((~v3_pre_topc(X20,X19)|r2_hidden(X20,u1_pre_topc(X19))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~l1_pre_topc(X19))&(~r2_hidden(X20,u1_pre_topc(X19))|v3_pre_topc(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~l1_pre_topc(X19))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 0.18/0.38  fof(c_0_12, plain, ![X21]:(~l1_pre_topc(X21)|m1_subset_1(u1_pre_topc(X21),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X21))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.18/0.38  cnf(c_0_13, plain, (v3_pre_topc(X3,X2)|~v1_tops_2(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.38  cnf(c_0_14, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.38  cnf(c_0_15, negated_conjecture, (~v3_pre_topc(k5_setfam_1(u1_struct_0(esk6_0),esk7_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.38  cnf(c_0_16, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.38  cnf(c_0_17, negated_conjecture, (l1_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.38  cnf(c_0_18, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.38  cnf(c_0_19, plain, (v3_pre_topc(X1,X2)|~v1_tops_2(X3,X2)|~l1_pre_topc(X2)|~r2_hidden(X1,X3)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))), inference(csr,[status(thm)],[c_0_13, c_0_14])).
% 0.18/0.38  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0))))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.38  cnf(c_0_21, negated_conjecture, (v1_tops_2(esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.38  fof(c_0_22, plain, ![X5, X6, X7]:((m1_subset_1(esk1_3(X5,X6,X7),X5)|r1_tarski(X6,X7)|~m1_subset_1(X7,k1_zfmisc_1(X5))|~m1_subset_1(X6,k1_zfmisc_1(X5)))&((r2_hidden(esk1_3(X5,X6,X7),X6)|r1_tarski(X6,X7)|~m1_subset_1(X7,k1_zfmisc_1(X5))|~m1_subset_1(X6,k1_zfmisc_1(X5)))&(~r2_hidden(esk1_3(X5,X6,X7),X7)|r1_tarski(X6,X7)|~m1_subset_1(X7,k1_zfmisc_1(X5))|~m1_subset_1(X6,k1_zfmisc_1(X5))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).
% 0.18/0.38  cnf(c_0_23, negated_conjecture, (~r2_hidden(k5_setfam_1(u1_struct_0(esk6_0),esk7_0),u1_pre_topc(esk6_0))|~m1_subset_1(k5_setfam_1(u1_struct_0(esk6_0),esk7_0),k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])])).
% 0.18/0.38  cnf(c_0_24, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)|~r2_hidden(X1,u1_pre_topc(X2))), inference(spm,[status(thm)],[c_0_14, c_0_18])).
% 0.18/0.38  fof(c_0_25, plain, ![X12, X13, X14, X15]:((((r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))|~v2_pre_topc(X12)|~l1_pre_topc(X12))&(~m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))|(~r1_tarski(X13,u1_pre_topc(X12))|r2_hidden(k5_setfam_1(u1_struct_0(X12),X13),u1_pre_topc(X12)))|~v2_pre_topc(X12)|~l1_pre_topc(X12)))&(~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|(~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X12)))|(~r2_hidden(X14,u1_pre_topc(X12))|~r2_hidden(X15,u1_pre_topc(X12))|r2_hidden(k9_subset_1(u1_struct_0(X12),X14,X15),u1_pre_topc(X12))))|~v2_pre_topc(X12)|~l1_pre_topc(X12)))&(((m1_subset_1(esk3_1(X12),k1_zfmisc_1(u1_struct_0(X12)))|(m1_subset_1(esk2_1(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12))&((m1_subset_1(esk4_1(X12),k1_zfmisc_1(u1_struct_0(X12)))|(m1_subset_1(esk2_1(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12))&(((r2_hidden(esk3_1(X12),u1_pre_topc(X12))|(m1_subset_1(esk2_1(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12))&(r2_hidden(esk4_1(X12),u1_pre_topc(X12))|(m1_subset_1(esk2_1(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12)))&(~r2_hidden(k9_subset_1(u1_struct_0(X12),esk3_1(X12),esk4_1(X12)),u1_pre_topc(X12))|(m1_subset_1(esk2_1(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12)))))&(((m1_subset_1(esk3_1(X12),k1_zfmisc_1(u1_struct_0(X12)))|(r1_tarski(esk2_1(X12),u1_pre_topc(X12))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12))&((m1_subset_1(esk4_1(X12),k1_zfmisc_1(u1_struct_0(X12)))|(r1_tarski(esk2_1(X12),u1_pre_topc(X12))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12))&(((r2_hidden(esk3_1(X12),u1_pre_topc(X12))|(r1_tarski(esk2_1(X12),u1_pre_topc(X12))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12))&(r2_hidden(esk4_1(X12),u1_pre_topc(X12))|(r1_tarski(esk2_1(X12),u1_pre_topc(X12))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12)))&(~r2_hidden(k9_subset_1(u1_struct_0(X12),esk3_1(X12),esk4_1(X12)),u1_pre_topc(X12))|(r1_tarski(esk2_1(X12),u1_pre_topc(X12))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12)))))&((m1_subset_1(esk3_1(X12),k1_zfmisc_1(u1_struct_0(X12)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X12),esk2_1(X12)),u1_pre_topc(X12))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12))&((m1_subset_1(esk4_1(X12),k1_zfmisc_1(u1_struct_0(X12)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X12),esk2_1(X12)),u1_pre_topc(X12))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12))&(((r2_hidden(esk3_1(X12),u1_pre_topc(X12))|(~r2_hidden(k5_setfam_1(u1_struct_0(X12),esk2_1(X12)),u1_pre_topc(X12))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12))&(r2_hidden(esk4_1(X12),u1_pre_topc(X12))|(~r2_hidden(k5_setfam_1(u1_struct_0(X12),esk2_1(X12)),u1_pre_topc(X12))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12)))&(~r2_hidden(k9_subset_1(u1_struct_0(X12),esk3_1(X12),esk4_1(X12)),u1_pre_topc(X12))|(~r2_hidden(k5_setfam_1(u1_struct_0(X12),esk2_1(X12)),u1_pre_topc(X12))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).
% 0.18/0.38  cnf(c_0_26, plain, (r2_hidden(X1,u1_pre_topc(X2))|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.38  cnf(c_0_27, negated_conjecture, (v3_pre_topc(X1,esk6_0)|~r2_hidden(X1,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_17])])).
% 0.18/0.38  cnf(c_0_28, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_14, c_0_20])).
% 0.18/0.38  cnf(c_0_29, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r1_tarski(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.38  cnf(c_0_30, negated_conjecture, (~r2_hidden(k5_setfam_1(u1_struct_0(esk6_0),esk7_0),u1_pre_topc(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_17])])).
% 0.18/0.38  cnf(c_0_31, plain, (r2_hidden(k5_setfam_1(u1_struct_0(X2),X1),u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~r1_tarski(X1,u1_pre_topc(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.18/0.38  cnf(c_0_32, negated_conjecture, (v2_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.38  cnf(c_0_33, plain, (r1_tarski(X2,X3)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.38  cnf(c_0_34, negated_conjecture, (r2_hidden(X1,u1_pre_topc(esk6_0))|~r2_hidden(X1,esk7_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_17])]), c_0_28])).
% 0.18/0.38  cnf(c_0_35, plain, (r1_tarski(X1,u1_pre_topc(X2))|r2_hidden(esk1_3(k1_zfmisc_1(u1_struct_0(X2)),X1,u1_pre_topc(X2)),X1)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))), inference(spm,[status(thm)],[c_0_29, c_0_18])).
% 0.18/0.38  cnf(c_0_36, negated_conjecture, (~r1_tarski(esk7_0,u1_pre_topc(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_17]), c_0_20])])).
% 0.18/0.38  cnf(c_0_37, negated_conjecture, (r1_tarski(X1,u1_pre_topc(esk6_0))|~r2_hidden(esk1_3(X2,X1,u1_pre_topc(esk6_0)),esk7_0)|~m1_subset_1(u1_pre_topc(esk6_0),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.18/0.38  cnf(c_0_38, negated_conjecture, (r2_hidden(esk1_3(k1_zfmisc_1(u1_struct_0(esk6_0)),esk7_0,u1_pre_topc(esk6_0)),esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_20]), c_0_17])]), c_0_36])).
% 0.18/0.38  cnf(c_0_39, negated_conjecture, (~m1_subset_1(u1_pre_topc(esk6_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_20])]), c_0_36])).
% 0.18/0.38  cnf(c_0_40, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_18]), c_0_17])]), ['proof']).
% 0.18/0.38  # SZS output end CNFRefutation
% 0.18/0.38  # Proof object total steps             : 41
% 0.18/0.38  # Proof object clause steps            : 26
% 0.18/0.38  # Proof object formula steps           : 15
% 0.18/0.38  # Proof object conjectures             : 18
% 0.18/0.38  # Proof object clause conjectures      : 15
% 0.18/0.38  # Proof object formula conjectures     : 3
% 0.18/0.38  # Proof object initial clauses used    : 13
% 0.18/0.38  # Proof object initial formulas used   : 7
% 0.18/0.38  # Proof object generating inferences   : 12
% 0.18/0.38  # Proof object simplifying inferences  : 23
% 0.18/0.38  # Training examples: 0 positive, 0 negative
% 0.18/0.38  # Parsed axioms                        : 7
% 0.18/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.38  # Initial clauses                      : 34
% 0.18/0.38  # Removed in clause preprocessing      : 0
% 0.18/0.38  # Initial clauses in saturation        : 34
% 0.18/0.38  # Processed clauses                    : 162
% 0.18/0.38  # ...of these trivial                  : 0
% 0.18/0.38  # ...subsumed                          : 18
% 0.18/0.38  # ...remaining for further processing  : 144
% 0.18/0.38  # Other redundant clauses eliminated   : 0
% 0.18/0.38  # Clauses deleted for lack of memory   : 0
% 0.18/0.38  # Backward-subsumed                    : 0
% 0.18/0.38  # Backward-rewritten                   : 3
% 0.18/0.38  # Generated clauses                    : 224
% 0.18/0.38  # ...of the previous two non-trivial   : 189
% 0.18/0.38  # Contextual simplify-reflections      : 5
% 0.18/0.38  # Paramodulations                      : 224
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
% 0.18/0.38  # Current number of processed clauses  : 107
% 0.18/0.38  #    Positive orientable unit clauses  : 7
% 0.18/0.38  #    Positive unorientable unit clauses: 0
% 0.18/0.38  #    Negative unit clauses             : 5
% 0.18/0.38  #    Non-unit-clauses                  : 95
% 0.18/0.38  # Current number of unprocessed clauses: 92
% 0.18/0.38  # ...number of literals in the above   : 338
% 0.18/0.38  # Current number of archived formulas  : 0
% 0.18/0.38  # Current number of archived clauses   : 37
% 0.18/0.38  # Clause-clause subsumption calls (NU) : 1237
% 0.18/0.38  # Rec. Clause-clause subsumption calls : 505
% 0.18/0.38  # Non-unit clause-clause subsumptions  : 18
% 0.18/0.38  # Unit Clause-clause subsumption calls : 33
% 0.18/0.38  # Rewrite failures with RHS unbound    : 0
% 0.18/0.38  # BW rewrite match attempts            : 1
% 0.18/0.38  # BW rewrite match successes           : 1
% 0.18/0.38  # Condensation attempts                : 0
% 0.18/0.38  # Condensation successes               : 0
% 0.18/0.38  # Termbank termtop insertions          : 11299
% 0.18/0.38  
% 0.18/0.38  # -------------------------------------------------
% 0.18/0.38  # User time                : 0.040 s
% 0.18/0.38  # System time              : 0.005 s
% 0.18/0.38  # Total time               : 0.045 s
% 0.18/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
