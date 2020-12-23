%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:13:13 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 130 expanded)
%              Number of clauses        :   30 (  49 expanded)
%              Number of leaves         :    8 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :  257 ( 691 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   27 (   5 average)
%              Maximal clause size      :   90 (   2 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tops_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_2)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(dt_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k5_setfam_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ( v1_tops_2(X2,X1)
             => v3_pre_topc(k5_setfam_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t26_tops_2])).

fof(c_0_9,plain,(
    ! [X30,X31,X32] :
      ( ( ~ v1_tops_2(X31,X30)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ r2_hidden(X32,X31)
        | v3_pre_topc(X32,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X30))))
        | ~ l1_pre_topc(X30) )
      & ( m1_subset_1(esk6_2(X30,X31),k1_zfmisc_1(u1_struct_0(X30)))
        | v1_tops_2(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X30))))
        | ~ l1_pre_topc(X30) )
      & ( r2_hidden(esk6_2(X30,X31),X31)
        | v1_tops_2(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X30))))
        | ~ l1_pre_topc(X30) )
      & ( ~ v3_pre_topc(esk6_2(X30,X31),X30)
        | v1_tops_2(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X30))))
        | ~ l1_pre_topc(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_2])])])])])).

fof(c_0_10,negated_conjecture,
    ( v2_pre_topc(esk7_0)
    & l1_pre_topc(esk7_0)
    & m1_subset_1(esk8_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0))))
    & v1_tops_2(esk8_0,esk7_0)
    & ~ v3_pre_topc(k5_setfam_1(u1_struct_0(esk7_0),esk8_0),esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_11,plain,(
    ! [X10,X11,X12,X13,X14,X15] :
      ( ( ~ r2_hidden(X12,X11)
        | r1_tarski(X12,X10)
        | X11 != k1_zfmisc_1(X10) )
      & ( ~ r1_tarski(X13,X10)
        | r2_hidden(X13,X11)
        | X11 != k1_zfmisc_1(X10) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | ~ r1_tarski(esk2_2(X14,X15),X14)
        | X15 = k1_zfmisc_1(X14) )
      & ( r2_hidden(esk2_2(X14,X15),X15)
        | r1_tarski(esk2_2(X14,X15),X14)
        | X15 = k1_zfmisc_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_12,plain,(
    ! [X28,X29] :
      ( ( ~ v3_pre_topc(X29,X28)
        | r2_hidden(X29,u1_pre_topc(X28))
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ l1_pre_topc(X28) )
      & ( ~ r2_hidden(X29,u1_pre_topc(X28))
        | v3_pre_topc(X29,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ l1_pre_topc(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_13,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tops_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( v1_tops_2(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_17,plain,(
    ! [X19,X20] :
      ( ( ~ m1_subset_1(X19,k1_zfmisc_1(X20))
        | r1_tarski(X19,X20) )
      & ( ~ r1_tarski(X19,X20)
        | m1_subset_1(X19,k1_zfmisc_1(X20)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_19,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( v3_pre_topc(X1,esk7_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16])])).

cnf(c_0_22,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( ~ v3_pre_topc(k5_setfam_1(u1_struct_0(esk7_0),esk8_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_27,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_28,plain,(
    ! [X17,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17)))
      | m1_subset_1(k5_setfam_1(X17,X18),k1_zfmisc_1(X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_setfam_1])])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(X1,u1_pre_topc(esk7_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_16])])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_33,negated_conjecture,
    ( ~ m1_subset_1(k5_setfam_1(u1_struct_0(esk7_0),esk8_0),k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(esk7_0),esk8_0),u1_pre_topc(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_16])])).

cnf(c_0_34,plain,
    ( m1_subset_1(k5_setfam_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_35,plain,(
    ! [X21,X22,X23,X24] :
      ( ( r2_hidden(u1_struct_0(X21),u1_pre_topc(X21))
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( ~ m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X21))))
        | ~ r1_tarski(X22,u1_pre_topc(X21))
        | r2_hidden(k5_setfam_1(u1_struct_0(X21),X22),u1_pre_topc(X21))
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ r2_hidden(X23,u1_pre_topc(X21))
        | ~ r2_hidden(X24,u1_pre_topc(X21))
        | r2_hidden(k9_subset_1(u1_struct_0(X21),X23,X24),u1_pre_topc(X21))
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( m1_subset_1(esk4_1(X21),k1_zfmisc_1(u1_struct_0(X21)))
        | m1_subset_1(esk3_1(X21),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X21))))
        | ~ r2_hidden(u1_struct_0(X21),u1_pre_topc(X21))
        | v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( m1_subset_1(esk5_1(X21),k1_zfmisc_1(u1_struct_0(X21)))
        | m1_subset_1(esk3_1(X21),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X21))))
        | ~ r2_hidden(u1_struct_0(X21),u1_pre_topc(X21))
        | v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( r2_hidden(esk4_1(X21),u1_pre_topc(X21))
        | m1_subset_1(esk3_1(X21),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X21))))
        | ~ r2_hidden(u1_struct_0(X21),u1_pre_topc(X21))
        | v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( r2_hidden(esk5_1(X21),u1_pre_topc(X21))
        | m1_subset_1(esk3_1(X21),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X21))))
        | ~ r2_hidden(u1_struct_0(X21),u1_pre_topc(X21))
        | v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X21),esk4_1(X21),esk5_1(X21)),u1_pre_topc(X21))
        | m1_subset_1(esk3_1(X21),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X21))))
        | ~ r2_hidden(u1_struct_0(X21),u1_pre_topc(X21))
        | v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( m1_subset_1(esk4_1(X21),k1_zfmisc_1(u1_struct_0(X21)))
        | r1_tarski(esk3_1(X21),u1_pre_topc(X21))
        | ~ r2_hidden(u1_struct_0(X21),u1_pre_topc(X21))
        | v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( m1_subset_1(esk5_1(X21),k1_zfmisc_1(u1_struct_0(X21)))
        | r1_tarski(esk3_1(X21),u1_pre_topc(X21))
        | ~ r2_hidden(u1_struct_0(X21),u1_pre_topc(X21))
        | v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( r2_hidden(esk4_1(X21),u1_pre_topc(X21))
        | r1_tarski(esk3_1(X21),u1_pre_topc(X21))
        | ~ r2_hidden(u1_struct_0(X21),u1_pre_topc(X21))
        | v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( r2_hidden(esk5_1(X21),u1_pre_topc(X21))
        | r1_tarski(esk3_1(X21),u1_pre_topc(X21))
        | ~ r2_hidden(u1_struct_0(X21),u1_pre_topc(X21))
        | v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X21),esk4_1(X21),esk5_1(X21)),u1_pre_topc(X21))
        | r1_tarski(esk3_1(X21),u1_pre_topc(X21))
        | ~ r2_hidden(u1_struct_0(X21),u1_pre_topc(X21))
        | v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( m1_subset_1(esk4_1(X21),k1_zfmisc_1(u1_struct_0(X21)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X21),esk3_1(X21)),u1_pre_topc(X21))
        | ~ r2_hidden(u1_struct_0(X21),u1_pre_topc(X21))
        | v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( m1_subset_1(esk5_1(X21),k1_zfmisc_1(u1_struct_0(X21)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X21),esk3_1(X21)),u1_pre_topc(X21))
        | ~ r2_hidden(u1_struct_0(X21),u1_pre_topc(X21))
        | v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( r2_hidden(esk4_1(X21),u1_pre_topc(X21))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X21),esk3_1(X21)),u1_pre_topc(X21))
        | ~ r2_hidden(u1_struct_0(X21),u1_pre_topc(X21))
        | v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( r2_hidden(esk5_1(X21),u1_pre_topc(X21))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X21),esk3_1(X21)),u1_pre_topc(X21))
        | ~ r2_hidden(u1_struct_0(X21),u1_pre_topc(X21))
        | v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X21),esk4_1(X21),esk5_1(X21)),u1_pre_topc(X21))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X21),esk3_1(X21)),u1_pre_topc(X21))
        | ~ r2_hidden(u1_struct_0(X21),u1_pre_topc(X21))
        | v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(X1,u1_pre_topc(esk7_0))
    | ~ r2_hidden(X1,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_38,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(esk7_0),esk8_0),u1_pre_topc(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_14])])).

cnf(c_0_40,plain,
    ( r2_hidden(k5_setfam_1(u1_struct_0(X2),X1),u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ r1_tarski(X1,u1_pre_topc(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( v2_pre_topc(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(X1,u1_pre_topc(esk7_0))
    | ~ r2_hidden(esk1_2(X1,u1_pre_topc(esk7_0)),k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ r2_hidden(esk1_2(X1,u1_pre_topc(esk7_0)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk1_2(esk8_0,X1),k1_zfmisc_1(u1_struct_0(esk7_0)))
    | r1_tarski(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_14])).

cnf(c_0_44,negated_conjecture,
    ( ~ r1_tarski(esk8_0,u1_pre_topc(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_16]),c_0_14])])).

cnf(c_0_45,negated_conjecture,
    ( ~ r2_hidden(esk1_2(esk8_0,u1_pre_topc(esk7_0)),esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_25]),c_0_44]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:50:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.030 s
% 0.19/0.39  # Presaturation interreduction done
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(t26_tops_2, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(v1_tops_2(X2,X1)=>v3_pre_topc(k5_setfam_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_tops_2)).
% 0.19/0.39  fof(d1_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(v1_tops_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X3,X2)=>v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_2)).
% 0.19/0.39  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.19/0.39  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 0.19/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.39  fof(dt_k5_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>m1_subset_1(k5_setfam_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 0.19/0.39  fof(d1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(X1)<=>((r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,u1_pre_topc(X1))=>r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,u1_pre_topc(X1))&r2_hidden(X3,u1_pre_topc(X1)))=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_pre_topc)).
% 0.19/0.39  fof(c_0_8, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(v1_tops_2(X2,X1)=>v3_pre_topc(k5_setfam_1(u1_struct_0(X1),X2),X1))))), inference(assume_negation,[status(cth)],[t26_tops_2])).
% 0.19/0.39  fof(c_0_9, plain, ![X30, X31, X32]:((~v1_tops_2(X31,X30)|(~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))|(~r2_hidden(X32,X31)|v3_pre_topc(X32,X30)))|~m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X30))))|~l1_pre_topc(X30))&((m1_subset_1(esk6_2(X30,X31),k1_zfmisc_1(u1_struct_0(X30)))|v1_tops_2(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X30))))|~l1_pre_topc(X30))&((r2_hidden(esk6_2(X30,X31),X31)|v1_tops_2(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X30))))|~l1_pre_topc(X30))&(~v3_pre_topc(esk6_2(X30,X31),X30)|v1_tops_2(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X30))))|~l1_pre_topc(X30))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_2])])])])])).
% 0.19/0.39  fof(c_0_10, negated_conjecture, ((v2_pre_topc(esk7_0)&l1_pre_topc(esk7_0))&(m1_subset_1(esk8_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0))))&(v1_tops_2(esk8_0,esk7_0)&~v3_pre_topc(k5_setfam_1(u1_struct_0(esk7_0),esk8_0),esk7_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.19/0.39  fof(c_0_11, plain, ![X10, X11, X12, X13, X14, X15]:(((~r2_hidden(X12,X11)|r1_tarski(X12,X10)|X11!=k1_zfmisc_1(X10))&(~r1_tarski(X13,X10)|r2_hidden(X13,X11)|X11!=k1_zfmisc_1(X10)))&((~r2_hidden(esk2_2(X14,X15),X15)|~r1_tarski(esk2_2(X14,X15),X14)|X15=k1_zfmisc_1(X14))&(r2_hidden(esk2_2(X14,X15),X15)|r1_tarski(esk2_2(X14,X15),X14)|X15=k1_zfmisc_1(X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.19/0.39  fof(c_0_12, plain, ![X28, X29]:((~v3_pre_topc(X29,X28)|r2_hidden(X29,u1_pre_topc(X28))|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|~l1_pre_topc(X28))&(~r2_hidden(X29,u1_pre_topc(X28))|v3_pre_topc(X29,X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|~l1_pre_topc(X28))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 0.19/0.39  cnf(c_0_13, plain, (v3_pre_topc(X3,X2)|~v1_tops_2(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0))))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.39  cnf(c_0_15, negated_conjecture, (v1_tops_2(esk8_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.39  cnf(c_0_16, negated_conjecture, (l1_pre_topc(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.39  fof(c_0_17, plain, ![X19, X20]:((~m1_subset_1(X19,k1_zfmisc_1(X20))|r1_tarski(X19,X20))&(~r1_tarski(X19,X20)|m1_subset_1(X19,k1_zfmisc_1(X20)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.39  cnf(c_0_18, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.39  fof(c_0_19, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.39  cnf(c_0_20, plain, (r2_hidden(X1,u1_pre_topc(X2))|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.39  cnf(c_0_21, negated_conjecture, (v3_pre_topc(X1,esk7_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0)))|~r2_hidden(X1,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15]), c_0_16])])).
% 0.19/0.39  cnf(c_0_22, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.39  cnf(c_0_23, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_24, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.39  cnf(c_0_25, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.39  cnf(c_0_26, negated_conjecture, (~v3_pre_topc(k5_setfam_1(u1_struct_0(esk7_0),esk8_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.39  cnf(c_0_27, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.39  fof(c_0_28, plain, ![X17, X18]:(~m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17)))|m1_subset_1(k5_setfam_1(X17,X18),k1_zfmisc_1(X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_setfam_1])])).
% 0.19/0.39  cnf(c_0_29, negated_conjecture, (r2_hidden(X1,u1_pre_topc(esk7_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0)))|~r2_hidden(X1,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_16])])).
% 0.19/0.39  cnf(c_0_30, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.39  cnf(c_0_31, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.39  cnf(c_0_32, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.39  cnf(c_0_33, negated_conjecture, (~m1_subset_1(k5_setfam_1(u1_struct_0(esk7_0),esk8_0),k1_zfmisc_1(u1_struct_0(esk7_0)))|~r2_hidden(k5_setfam_1(u1_struct_0(esk7_0),esk8_0),u1_pre_topc(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_16])])).
% 0.19/0.39  cnf(c_0_34, plain, (m1_subset_1(k5_setfam_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.39  fof(c_0_35, plain, ![X21, X22, X23, X24]:((((r2_hidden(u1_struct_0(X21),u1_pre_topc(X21))|~v2_pre_topc(X21)|~l1_pre_topc(X21))&(~m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X21))))|(~r1_tarski(X22,u1_pre_topc(X21))|r2_hidden(k5_setfam_1(u1_struct_0(X21),X22),u1_pre_topc(X21)))|~v2_pre_topc(X21)|~l1_pre_topc(X21)))&(~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))|(~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X21)))|(~r2_hidden(X23,u1_pre_topc(X21))|~r2_hidden(X24,u1_pre_topc(X21))|r2_hidden(k9_subset_1(u1_struct_0(X21),X23,X24),u1_pre_topc(X21))))|~v2_pre_topc(X21)|~l1_pre_topc(X21)))&(((m1_subset_1(esk4_1(X21),k1_zfmisc_1(u1_struct_0(X21)))|(m1_subset_1(esk3_1(X21),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X21))))|~r2_hidden(u1_struct_0(X21),u1_pre_topc(X21)))|v2_pre_topc(X21)|~l1_pre_topc(X21))&((m1_subset_1(esk5_1(X21),k1_zfmisc_1(u1_struct_0(X21)))|(m1_subset_1(esk3_1(X21),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X21))))|~r2_hidden(u1_struct_0(X21),u1_pre_topc(X21)))|v2_pre_topc(X21)|~l1_pre_topc(X21))&(((r2_hidden(esk4_1(X21),u1_pre_topc(X21))|(m1_subset_1(esk3_1(X21),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X21))))|~r2_hidden(u1_struct_0(X21),u1_pre_topc(X21)))|v2_pre_topc(X21)|~l1_pre_topc(X21))&(r2_hidden(esk5_1(X21),u1_pre_topc(X21))|(m1_subset_1(esk3_1(X21),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X21))))|~r2_hidden(u1_struct_0(X21),u1_pre_topc(X21)))|v2_pre_topc(X21)|~l1_pre_topc(X21)))&(~r2_hidden(k9_subset_1(u1_struct_0(X21),esk4_1(X21),esk5_1(X21)),u1_pre_topc(X21))|(m1_subset_1(esk3_1(X21),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X21))))|~r2_hidden(u1_struct_0(X21),u1_pre_topc(X21)))|v2_pre_topc(X21)|~l1_pre_topc(X21)))))&(((m1_subset_1(esk4_1(X21),k1_zfmisc_1(u1_struct_0(X21)))|(r1_tarski(esk3_1(X21),u1_pre_topc(X21))|~r2_hidden(u1_struct_0(X21),u1_pre_topc(X21)))|v2_pre_topc(X21)|~l1_pre_topc(X21))&((m1_subset_1(esk5_1(X21),k1_zfmisc_1(u1_struct_0(X21)))|(r1_tarski(esk3_1(X21),u1_pre_topc(X21))|~r2_hidden(u1_struct_0(X21),u1_pre_topc(X21)))|v2_pre_topc(X21)|~l1_pre_topc(X21))&(((r2_hidden(esk4_1(X21),u1_pre_topc(X21))|(r1_tarski(esk3_1(X21),u1_pre_topc(X21))|~r2_hidden(u1_struct_0(X21),u1_pre_topc(X21)))|v2_pre_topc(X21)|~l1_pre_topc(X21))&(r2_hidden(esk5_1(X21),u1_pre_topc(X21))|(r1_tarski(esk3_1(X21),u1_pre_topc(X21))|~r2_hidden(u1_struct_0(X21),u1_pre_topc(X21)))|v2_pre_topc(X21)|~l1_pre_topc(X21)))&(~r2_hidden(k9_subset_1(u1_struct_0(X21),esk4_1(X21),esk5_1(X21)),u1_pre_topc(X21))|(r1_tarski(esk3_1(X21),u1_pre_topc(X21))|~r2_hidden(u1_struct_0(X21),u1_pre_topc(X21)))|v2_pre_topc(X21)|~l1_pre_topc(X21)))))&((m1_subset_1(esk4_1(X21),k1_zfmisc_1(u1_struct_0(X21)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X21),esk3_1(X21)),u1_pre_topc(X21))|~r2_hidden(u1_struct_0(X21),u1_pre_topc(X21)))|v2_pre_topc(X21)|~l1_pre_topc(X21))&((m1_subset_1(esk5_1(X21),k1_zfmisc_1(u1_struct_0(X21)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X21),esk3_1(X21)),u1_pre_topc(X21))|~r2_hidden(u1_struct_0(X21),u1_pre_topc(X21)))|v2_pre_topc(X21)|~l1_pre_topc(X21))&(((r2_hidden(esk4_1(X21),u1_pre_topc(X21))|(~r2_hidden(k5_setfam_1(u1_struct_0(X21),esk3_1(X21)),u1_pre_topc(X21))|~r2_hidden(u1_struct_0(X21),u1_pre_topc(X21)))|v2_pre_topc(X21)|~l1_pre_topc(X21))&(r2_hidden(esk5_1(X21),u1_pre_topc(X21))|(~r2_hidden(k5_setfam_1(u1_struct_0(X21),esk3_1(X21)),u1_pre_topc(X21))|~r2_hidden(u1_struct_0(X21),u1_pre_topc(X21)))|v2_pre_topc(X21)|~l1_pre_topc(X21)))&(~r2_hidden(k9_subset_1(u1_struct_0(X21),esk4_1(X21),esk5_1(X21)),u1_pre_topc(X21))|(~r2_hidden(k5_setfam_1(u1_struct_0(X21),esk3_1(X21)),u1_pre_topc(X21))|~r2_hidden(u1_struct_0(X21),u1_pre_topc(X21)))|v2_pre_topc(X21)|~l1_pre_topc(X21)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).
% 0.19/0.39  cnf(c_0_36, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.39  cnf(c_0_37, negated_conjecture, (r2_hidden(X1,u1_pre_topc(esk7_0))|~r2_hidden(X1,k1_zfmisc_1(u1_struct_0(esk7_0)))|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.39  cnf(c_0_38, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.39  cnf(c_0_39, negated_conjecture, (~r2_hidden(k5_setfam_1(u1_struct_0(esk7_0),esk8_0),u1_pre_topc(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_14])])).
% 0.19/0.39  cnf(c_0_40, plain, (r2_hidden(k5_setfam_1(u1_struct_0(X2),X1),u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~r1_tarski(X1,u1_pre_topc(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.39  cnf(c_0_41, negated_conjecture, (v2_pre_topc(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.39  cnf(c_0_42, negated_conjecture, (r1_tarski(X1,u1_pre_topc(esk7_0))|~r2_hidden(esk1_2(X1,u1_pre_topc(esk7_0)),k1_zfmisc_1(u1_struct_0(esk7_0)))|~r2_hidden(esk1_2(X1,u1_pre_topc(esk7_0)),esk8_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.39  cnf(c_0_43, negated_conjecture, (r2_hidden(esk1_2(esk8_0,X1),k1_zfmisc_1(u1_struct_0(esk7_0)))|r1_tarski(esk8_0,X1)), inference(spm,[status(thm)],[c_0_38, c_0_14])).
% 0.19/0.39  cnf(c_0_44, negated_conjecture, (~r1_tarski(esk8_0,u1_pre_topc(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_16]), c_0_14])])).
% 0.19/0.39  cnf(c_0_45, negated_conjecture, (~r2_hidden(esk1_2(esk8_0,u1_pre_topc(esk7_0)),esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])).
% 0.19/0.39  cnf(c_0_46, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_25]), c_0_44]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 47
% 0.19/0.39  # Proof object clause steps            : 30
% 0.19/0.39  # Proof object formula steps           : 17
% 0.19/0.39  # Proof object conjectures             : 18
% 0.19/0.39  # Proof object clause conjectures      : 15
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 16
% 0.19/0.39  # Proof object initial formulas used   : 8
% 0.19/0.39  # Proof object generating inferences   : 13
% 0.19/0.39  # Proof object simplifying inferences  : 16
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 8
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 39
% 0.19/0.39  # Removed in clause preprocessing      : 0
% 0.19/0.39  # Initial clauses in saturation        : 39
% 0.19/0.39  # Processed clauses                    : 210
% 0.19/0.39  # ...of these trivial                  : 1
% 0.19/0.39  # ...subsumed                          : 52
% 0.19/0.39  # ...remaining for further processing  : 157
% 0.19/0.39  # Other redundant clauses eliminated   : 2
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 0
% 0.19/0.39  # Backward-rewritten                   : 0
% 0.19/0.39  # Generated clauses                    : 256
% 0.19/0.39  # ...of the previous two non-trivial   : 196
% 0.19/0.39  # Contextual simplify-reflections      : 2
% 0.19/0.39  # Paramodulations                      : 254
% 0.19/0.39  # Factorizations                       : 0
% 0.19/0.39  # Equation resolutions                 : 2
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 116
% 0.19/0.39  #    Positive orientable unit clauses  : 9
% 0.19/0.39  #    Positive unorientable unit clauses: 0
% 0.19/0.39  #    Negative unit clauses             : 13
% 0.19/0.39  #    Non-unit-clauses                  : 94
% 0.19/0.39  # Current number of unprocessed clauses: 64
% 0.19/0.39  # ...number of literals in the above   : 279
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 39
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 2238
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 1066
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 44
% 0.19/0.39  # Unit Clause-clause subsumption calls : 101
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 13
% 0.19/0.39  # BW rewrite match successes           : 0
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 9281
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.041 s
% 0.19/0.39  # System time              : 0.007 s
% 0.19/0.39  # Total time               : 0.048 s
% 0.19/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
