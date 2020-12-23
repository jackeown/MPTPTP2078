%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1308+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:05 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   37 (  80 expanded)
%              Number of clauses        :   22 (  29 expanded)
%              Number of leaves         :    7 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :  223 ( 410 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   27 (   5 average)
%              Maximal clause size      :   90 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t26_tops_2,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v1_tops_2(X2,X1)
           => v3_pre_topc(k5_setfam_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tops_2)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(dt_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k5_setfam_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

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

fof(c_0_7,plain,(
    ! [X11,X12,X13] :
      ( ( ~ v1_tops_2(X12,X11)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ r2_hidden(X13,X12)
        | v3_pre_topc(X13,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X11))))
        | ~ l1_pre_topc(X11) )
      & ( m1_subset_1(esk4_2(X11,X12),k1_zfmisc_1(u1_struct_0(X11)))
        | v1_tops_2(X12,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X11))))
        | ~ l1_pre_topc(X11) )
      & ( r2_hidden(esk4_2(X11,X12),X12)
        | v1_tops_2(X12,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X11))))
        | ~ l1_pre_topc(X11) )
      & ( ~ v3_pre_topc(esk4_2(X11,X12),X11)
        | v1_tops_2(X12,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X11))))
        | ~ l1_pre_topc(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_2])])])])])).

fof(c_0_8,plain,(
    ! [X25,X26,X27] :
      ( ~ r2_hidden(X25,X26)
      | ~ m1_subset_1(X26,k1_zfmisc_1(X27))
      | m1_subset_1(X25,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ( v1_tops_2(X2,X1)
             => v3_pre_topc(k5_setfam_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t26_tops_2])).

cnf(c_0_10,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tops_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,negated_conjecture,
    ( v2_pre_topc(esk6_0)
    & l1_pre_topc(esk6_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0))))
    & v1_tops_2(esk7_0,esk6_0)
    & ~ v3_pre_topc(k5_setfam_1(u1_struct_0(esk6_0),esk7_0),esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_13,plain,(
    ! [X21,X22] :
      ( ( ~ v3_pre_topc(X22,X21)
        | r2_hidden(X22,u1_pre_topc(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ l1_pre_topc(X21) )
      & ( ~ r2_hidden(X22,u1_pre_topc(X21))
        | v3_pre_topc(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_14,plain,
    ( v3_pre_topc(X1,X2)
    | ~ v1_tops_2(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ r2_hidden(X1,X3)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( v1_tops_2(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X15,X16,X17,X18,X19] :
      ( ( ~ r1_tarski(X15,X16)
        | ~ r2_hidden(X17,X15)
        | r2_hidden(X17,X16) )
      & ( r2_hidden(esk5_2(X18,X19),X18)
        | r1_tarski(X18,X19) )
      & ( ~ r2_hidden(esk5_2(X18,X19),X19)
        | r1_tarski(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( v3_pre_topc(X1,esk6_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17])])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( ~ v3_pre_topc(k5_setfam_1(u1_struct_0(esk6_0),esk7_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_24,plain,(
    ! [X23,X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(X23)))
      | m1_subset_1(k5_setfam_1(X23,X24),k1_zfmisc_1(X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_setfam_1])])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk5_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(X1,u1_pre_topc(esk6_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_17])]),c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( ~ m1_subset_1(k5_setfam_1(u1_struct_0(esk6_0),esk7_0),k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(esk6_0),esk7_0),u1_pre_topc(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_17])])).

cnf(c_0_28,plain,
    ( m1_subset_1(k5_setfam_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_29,plain,(
    ! [X4,X5,X6,X7] :
      ( ( r2_hidden(u1_struct_0(X4),u1_pre_topc(X4))
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X4))))
        | ~ r1_tarski(X5,u1_pre_topc(X4))
        | r2_hidden(k5_setfam_1(u1_struct_0(X4),X5),u1_pre_topc(X4))
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X4)))
        | ~ r2_hidden(X6,u1_pre_topc(X4))
        | ~ r2_hidden(X7,u1_pre_topc(X4))
        | r2_hidden(k9_subset_1(u1_struct_0(X4),X6,X7),u1_pre_topc(X4))
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( m1_subset_1(esk2_1(X4),k1_zfmisc_1(u1_struct_0(X4)))
        | m1_subset_1(esk1_1(X4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X4))))
        | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X4))
        | v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( m1_subset_1(esk3_1(X4),k1_zfmisc_1(u1_struct_0(X4)))
        | m1_subset_1(esk1_1(X4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X4))))
        | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X4))
        | v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( r2_hidden(esk2_1(X4),u1_pre_topc(X4))
        | m1_subset_1(esk1_1(X4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X4))))
        | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X4))
        | v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( r2_hidden(esk3_1(X4),u1_pre_topc(X4))
        | m1_subset_1(esk1_1(X4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X4))))
        | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X4))
        | v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X4),esk2_1(X4),esk3_1(X4)),u1_pre_topc(X4))
        | m1_subset_1(esk1_1(X4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X4))))
        | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X4))
        | v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( m1_subset_1(esk2_1(X4),k1_zfmisc_1(u1_struct_0(X4)))
        | r1_tarski(esk1_1(X4),u1_pre_topc(X4))
        | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X4))
        | v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( m1_subset_1(esk3_1(X4),k1_zfmisc_1(u1_struct_0(X4)))
        | r1_tarski(esk1_1(X4),u1_pre_topc(X4))
        | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X4))
        | v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( r2_hidden(esk2_1(X4),u1_pre_topc(X4))
        | r1_tarski(esk1_1(X4),u1_pre_topc(X4))
        | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X4))
        | v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( r2_hidden(esk3_1(X4),u1_pre_topc(X4))
        | r1_tarski(esk1_1(X4),u1_pre_topc(X4))
        | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X4))
        | v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X4),esk2_1(X4),esk3_1(X4)),u1_pre_topc(X4))
        | r1_tarski(esk1_1(X4),u1_pre_topc(X4))
        | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X4))
        | v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( m1_subset_1(esk2_1(X4),k1_zfmisc_1(u1_struct_0(X4)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X4),esk1_1(X4)),u1_pre_topc(X4))
        | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X4))
        | v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( m1_subset_1(esk3_1(X4),k1_zfmisc_1(u1_struct_0(X4)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X4),esk1_1(X4)),u1_pre_topc(X4))
        | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X4))
        | v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( r2_hidden(esk2_1(X4),u1_pre_topc(X4))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X4),esk1_1(X4)),u1_pre_topc(X4))
        | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X4))
        | v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( r2_hidden(esk3_1(X4),u1_pre_topc(X4))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X4),esk1_1(X4)),u1_pre_topc(X4))
        | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X4))
        | v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X4),esk2_1(X4),esk3_1(X4)),u1_pre_topc(X4))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X4),esk1_1(X4)),u1_pre_topc(X4))
        | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X4))
        | v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(X1,u1_pre_topc(esk6_0))
    | ~ r2_hidden(esk5_2(X1,u1_pre_topc(esk6_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,plain,
    ( r2_hidden(esk5_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_32,negated_conjecture,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(esk6_0),esk7_0),u1_pre_topc(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_15])])).

cnf(c_0_33,plain,
    ( r2_hidden(k5_setfam_1(u1_struct_0(X2),X1),u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ r1_tarski(X1,u1_pre_topc(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk7_0,u1_pre_topc(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( v2_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_15]),c_0_35]),c_0_17])]),
    [proof]).

%------------------------------------------------------------------------------
