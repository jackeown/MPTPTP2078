%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:13:13 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   38 (  80 expanded)
%              Number of clauses        :   23 (  30 expanded)
%              Number of leaves         :    7 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :  227 ( 407 expanded)
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

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

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
    ! [X23,X24,X25] :
      ( ( ~ v1_tops_2(X24,X23)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ r2_hidden(X25,X24)
        | v3_pre_topc(X25,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))
        | ~ l1_pre_topc(X23) )
      & ( m1_subset_1(esk5_2(X23,X24),k1_zfmisc_1(u1_struct_0(X23)))
        | v1_tops_2(X24,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))
        | ~ l1_pre_topc(X23) )
      & ( r2_hidden(esk5_2(X23,X24),X24)
        | v1_tops_2(X24,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))
        | ~ l1_pre_topc(X23) )
      & ( ~ v3_pre_topc(esk5_2(X23,X24),X23)
        | v1_tops_2(X24,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))
        | ~ l1_pre_topc(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_2])])])])])).

fof(c_0_8,plain,(
    ! [X10,X11,X12] :
      ( ~ r2_hidden(X10,X11)
      | ~ m1_subset_1(X11,k1_zfmisc_1(X12))
      | m1_subset_1(X10,X12) ) ),
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

fof(c_0_10,plain,(
    ! [X22] :
      ( ~ l1_pre_topc(X22)
      | m1_subset_1(u1_pre_topc(X22),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_11,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tops_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,negated_conjecture,
    ( v2_pre_topc(esk6_0)
    & l1_pre_topc(esk6_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0))))
    & v1_tops_2(esk7_0,esk6_0)
    & ~ v3_pre_topc(k5_setfam_1(u1_struct_0(esk6_0),esk7_0),esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_14,plain,(
    ! [X20,X21] :
      ( ( ~ v3_pre_topc(X21,X20)
        | r2_hidden(X21,u1_pre_topc(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ l1_pre_topc(X20) )
      & ( ~ r2_hidden(X21,u1_pre_topc(X20))
        | v3_pre_topc(X21,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_15,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( v3_pre_topc(X1,X2)
    | ~ v1_tops_2(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ r2_hidden(X1,X3) ),
    inference(csr,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( v1_tops_2(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_15])).

fof(c_0_22,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,negated_conjecture,
    ( v3_pre_topc(X1,esk6_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19])])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( ~ v3_pre_topc(k5_setfam_1(u1_struct_0(esk6_0),esk7_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,plain,
    ( v3_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2)) ),
    inference(csr,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_28,plain,(
    ! [X13,X14,X15,X16] :
      ( ( r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))
        | ~ r1_tarski(X14,u1_pre_topc(X13))
        | r2_hidden(k5_setfam_1(u1_struct_0(X13),X14),u1_pre_topc(X13))
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ r2_hidden(X15,u1_pre_topc(X13))
        | ~ r2_hidden(X16,u1_pre_topc(X13))
        | r2_hidden(k9_subset_1(u1_struct_0(X13),X15,X16),u1_pre_topc(X13))
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(esk3_1(X13),k1_zfmisc_1(u1_struct_0(X13)))
        | m1_subset_1(esk2_1(X13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(esk4_1(X13),k1_zfmisc_1(u1_struct_0(X13)))
        | m1_subset_1(esk2_1(X13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( r2_hidden(esk3_1(X13),u1_pre_topc(X13))
        | m1_subset_1(esk2_1(X13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( r2_hidden(esk4_1(X13),u1_pre_topc(X13))
        | m1_subset_1(esk2_1(X13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X13),esk3_1(X13),esk4_1(X13)),u1_pre_topc(X13))
        | m1_subset_1(esk2_1(X13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(esk3_1(X13),k1_zfmisc_1(u1_struct_0(X13)))
        | r1_tarski(esk2_1(X13),u1_pre_topc(X13))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(esk4_1(X13),k1_zfmisc_1(u1_struct_0(X13)))
        | r1_tarski(esk2_1(X13),u1_pre_topc(X13))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( r2_hidden(esk3_1(X13),u1_pre_topc(X13))
        | r1_tarski(esk2_1(X13),u1_pre_topc(X13))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( r2_hidden(esk4_1(X13),u1_pre_topc(X13))
        | r1_tarski(esk2_1(X13),u1_pre_topc(X13))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X13),esk3_1(X13),esk4_1(X13)),u1_pre_topc(X13))
        | r1_tarski(esk2_1(X13),u1_pre_topc(X13))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(esk3_1(X13),k1_zfmisc_1(u1_struct_0(X13)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X13),esk2_1(X13)),u1_pre_topc(X13))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(esk4_1(X13),k1_zfmisc_1(u1_struct_0(X13)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X13),esk2_1(X13)),u1_pre_topc(X13))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( r2_hidden(esk3_1(X13),u1_pre_topc(X13))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X13),esk2_1(X13)),u1_pre_topc(X13))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( r2_hidden(esk4_1(X13),u1_pre_topc(X13))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X13),esk2_1(X13)),u1_pre_topc(X13))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X13),esk3_1(X13),esk4_1(X13)),u1_pre_topc(X13))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X13),esk2_1(X13)),u1_pre_topc(X13))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(X1,u1_pre_topc(esk6_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_19])]),c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(esk6_0),esk7_0),u1_pre_topc(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_19])])).

cnf(c_0_32,plain,
    ( r2_hidden(k5_setfam_1(u1_struct_0(X2),X1),u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ r1_tarski(X1,u1_pre_topc(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( v2_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(X1,u1_pre_topc(esk6_0))
    | ~ r2_hidden(esk1_2(X1,u1_pre_topc(esk6_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,negated_conjecture,
    ( ~ r1_tarski(esk7_0,u1_pre_topc(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_19]),c_0_17])])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:51:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.029 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(d1_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(v1_tops_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X3,X2)=>v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_2)).
% 0.14/0.38  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.14/0.38  fof(t26_tops_2, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(v1_tops_2(X2,X1)=>v3_pre_topc(k5_setfam_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_tops_2)).
% 0.14/0.38  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.14/0.38  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 0.14/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.14/0.38  fof(d1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(X1)<=>((r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,u1_pre_topc(X1))=>r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,u1_pre_topc(X1))&r2_hidden(X3,u1_pre_topc(X1)))=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 0.14/0.38  fof(c_0_7, plain, ![X23, X24, X25]:((~v1_tops_2(X24,X23)|(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))|(~r2_hidden(X25,X24)|v3_pre_topc(X25,X23)))|~m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))|~l1_pre_topc(X23))&((m1_subset_1(esk5_2(X23,X24),k1_zfmisc_1(u1_struct_0(X23)))|v1_tops_2(X24,X23)|~m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))|~l1_pre_topc(X23))&((r2_hidden(esk5_2(X23,X24),X24)|v1_tops_2(X24,X23)|~m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))|~l1_pre_topc(X23))&(~v3_pre_topc(esk5_2(X23,X24),X23)|v1_tops_2(X24,X23)|~m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))|~l1_pre_topc(X23))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_2])])])])])).
% 0.14/0.38  fof(c_0_8, plain, ![X10, X11, X12]:(~r2_hidden(X10,X11)|~m1_subset_1(X11,k1_zfmisc_1(X12))|m1_subset_1(X10,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.14/0.38  fof(c_0_9, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(v1_tops_2(X2,X1)=>v3_pre_topc(k5_setfam_1(u1_struct_0(X1),X2),X1))))), inference(assume_negation,[status(cth)],[t26_tops_2])).
% 0.14/0.38  fof(c_0_10, plain, ![X22]:(~l1_pre_topc(X22)|m1_subset_1(u1_pre_topc(X22),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.14/0.38  cnf(c_0_11, plain, (v3_pre_topc(X3,X2)|~v1_tops_2(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  cnf(c_0_12, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  fof(c_0_13, negated_conjecture, ((v2_pre_topc(esk6_0)&l1_pre_topc(esk6_0))&(m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0))))&(v1_tops_2(esk7_0,esk6_0)&~v3_pre_topc(k5_setfam_1(u1_struct_0(esk6_0),esk7_0),esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.14/0.38  fof(c_0_14, plain, ![X20, X21]:((~v3_pre_topc(X21,X20)|r2_hidden(X21,u1_pre_topc(X20))|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|~l1_pre_topc(X20))&(~r2_hidden(X21,u1_pre_topc(X20))|v3_pre_topc(X21,X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|~l1_pre_topc(X20))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 0.14/0.38  cnf(c_0_15, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_16, plain, (v3_pre_topc(X1,X2)|~v1_tops_2(X3,X2)|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~r2_hidden(X1,X3)), inference(csr,[status(thm)],[c_0_11, c_0_12])).
% 0.14/0.38  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0))))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_18, negated_conjecture, (v1_tops_2(esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_19, negated_conjecture, (l1_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_20, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.38  cnf(c_0_21, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)|~r2_hidden(X1,u1_pre_topc(X2))), inference(spm,[status(thm)],[c_0_12, c_0_15])).
% 0.14/0.38  fof(c_0_22, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.14/0.38  cnf(c_0_23, plain, (r2_hidden(X1,u1_pre_topc(X2))|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.38  cnf(c_0_24, negated_conjecture, (v3_pre_topc(X1,esk6_0)|~r2_hidden(X1,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19])])).
% 0.14/0.38  cnf(c_0_25, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_12, c_0_17])).
% 0.14/0.38  cnf(c_0_26, negated_conjecture, (~v3_pre_topc(k5_setfam_1(u1_struct_0(esk6_0),esk7_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_27, plain, (v3_pre_topc(X1,X2)|~l1_pre_topc(X2)|~r2_hidden(X1,u1_pre_topc(X2))), inference(csr,[status(thm)],[c_0_20, c_0_21])).
% 0.14/0.38  fof(c_0_28, plain, ![X13, X14, X15, X16]:((((r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))|~v2_pre_topc(X13)|~l1_pre_topc(X13))&(~m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))|(~r1_tarski(X14,u1_pre_topc(X13))|r2_hidden(k5_setfam_1(u1_struct_0(X13),X14),u1_pre_topc(X13)))|~v2_pre_topc(X13)|~l1_pre_topc(X13)))&(~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))|(~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X13)))|(~r2_hidden(X15,u1_pre_topc(X13))|~r2_hidden(X16,u1_pre_topc(X13))|r2_hidden(k9_subset_1(u1_struct_0(X13),X15,X16),u1_pre_topc(X13))))|~v2_pre_topc(X13)|~l1_pre_topc(X13)))&(((m1_subset_1(esk3_1(X13),k1_zfmisc_1(u1_struct_0(X13)))|(m1_subset_1(esk2_1(X13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))|~r2_hidden(u1_struct_0(X13),u1_pre_topc(X13)))|v2_pre_topc(X13)|~l1_pre_topc(X13))&((m1_subset_1(esk4_1(X13),k1_zfmisc_1(u1_struct_0(X13)))|(m1_subset_1(esk2_1(X13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))|~r2_hidden(u1_struct_0(X13),u1_pre_topc(X13)))|v2_pre_topc(X13)|~l1_pre_topc(X13))&(((r2_hidden(esk3_1(X13),u1_pre_topc(X13))|(m1_subset_1(esk2_1(X13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))|~r2_hidden(u1_struct_0(X13),u1_pre_topc(X13)))|v2_pre_topc(X13)|~l1_pre_topc(X13))&(r2_hidden(esk4_1(X13),u1_pre_topc(X13))|(m1_subset_1(esk2_1(X13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))|~r2_hidden(u1_struct_0(X13),u1_pre_topc(X13)))|v2_pre_topc(X13)|~l1_pre_topc(X13)))&(~r2_hidden(k9_subset_1(u1_struct_0(X13),esk3_1(X13),esk4_1(X13)),u1_pre_topc(X13))|(m1_subset_1(esk2_1(X13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))|~r2_hidden(u1_struct_0(X13),u1_pre_topc(X13)))|v2_pre_topc(X13)|~l1_pre_topc(X13)))))&(((m1_subset_1(esk3_1(X13),k1_zfmisc_1(u1_struct_0(X13)))|(r1_tarski(esk2_1(X13),u1_pre_topc(X13))|~r2_hidden(u1_struct_0(X13),u1_pre_topc(X13)))|v2_pre_topc(X13)|~l1_pre_topc(X13))&((m1_subset_1(esk4_1(X13),k1_zfmisc_1(u1_struct_0(X13)))|(r1_tarski(esk2_1(X13),u1_pre_topc(X13))|~r2_hidden(u1_struct_0(X13),u1_pre_topc(X13)))|v2_pre_topc(X13)|~l1_pre_topc(X13))&(((r2_hidden(esk3_1(X13),u1_pre_topc(X13))|(r1_tarski(esk2_1(X13),u1_pre_topc(X13))|~r2_hidden(u1_struct_0(X13),u1_pre_topc(X13)))|v2_pre_topc(X13)|~l1_pre_topc(X13))&(r2_hidden(esk4_1(X13),u1_pre_topc(X13))|(r1_tarski(esk2_1(X13),u1_pre_topc(X13))|~r2_hidden(u1_struct_0(X13),u1_pre_topc(X13)))|v2_pre_topc(X13)|~l1_pre_topc(X13)))&(~r2_hidden(k9_subset_1(u1_struct_0(X13),esk3_1(X13),esk4_1(X13)),u1_pre_topc(X13))|(r1_tarski(esk2_1(X13),u1_pre_topc(X13))|~r2_hidden(u1_struct_0(X13),u1_pre_topc(X13)))|v2_pre_topc(X13)|~l1_pre_topc(X13)))))&((m1_subset_1(esk3_1(X13),k1_zfmisc_1(u1_struct_0(X13)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X13),esk2_1(X13)),u1_pre_topc(X13))|~r2_hidden(u1_struct_0(X13),u1_pre_topc(X13)))|v2_pre_topc(X13)|~l1_pre_topc(X13))&((m1_subset_1(esk4_1(X13),k1_zfmisc_1(u1_struct_0(X13)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X13),esk2_1(X13)),u1_pre_topc(X13))|~r2_hidden(u1_struct_0(X13),u1_pre_topc(X13)))|v2_pre_topc(X13)|~l1_pre_topc(X13))&(((r2_hidden(esk3_1(X13),u1_pre_topc(X13))|(~r2_hidden(k5_setfam_1(u1_struct_0(X13),esk2_1(X13)),u1_pre_topc(X13))|~r2_hidden(u1_struct_0(X13),u1_pre_topc(X13)))|v2_pre_topc(X13)|~l1_pre_topc(X13))&(r2_hidden(esk4_1(X13),u1_pre_topc(X13))|(~r2_hidden(k5_setfam_1(u1_struct_0(X13),esk2_1(X13)),u1_pre_topc(X13))|~r2_hidden(u1_struct_0(X13),u1_pre_topc(X13)))|v2_pre_topc(X13)|~l1_pre_topc(X13)))&(~r2_hidden(k9_subset_1(u1_struct_0(X13),esk3_1(X13),esk4_1(X13)),u1_pre_topc(X13))|(~r2_hidden(k5_setfam_1(u1_struct_0(X13),esk2_1(X13)),u1_pre_topc(X13))|~r2_hidden(u1_struct_0(X13),u1_pre_topc(X13)))|v2_pre_topc(X13)|~l1_pre_topc(X13)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).
% 0.14/0.38  cnf(c_0_29, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.38  cnf(c_0_30, negated_conjecture, (r2_hidden(X1,u1_pre_topc(esk6_0))|~r2_hidden(X1,esk7_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_19])]), c_0_25])).
% 0.14/0.38  cnf(c_0_31, negated_conjecture, (~r2_hidden(k5_setfam_1(u1_struct_0(esk6_0),esk7_0),u1_pre_topc(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_19])])).
% 0.14/0.38  cnf(c_0_32, plain, (r2_hidden(k5_setfam_1(u1_struct_0(X2),X1),u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~r1_tarski(X1,u1_pre_topc(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.14/0.38  cnf(c_0_33, negated_conjecture, (v2_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_34, negated_conjecture, (r1_tarski(X1,u1_pre_topc(esk6_0))|~r2_hidden(esk1_2(X1,u1_pre_topc(esk6_0)),esk7_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.14/0.38  cnf(c_0_35, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.38  cnf(c_0_36, negated_conjecture, (~r1_tarski(esk7_0,u1_pre_topc(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_19]), c_0_17])])).
% 0.14/0.38  cnf(c_0_37, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 38
% 0.14/0.38  # Proof object clause steps            : 23
% 0.14/0.38  # Proof object formula steps           : 15
% 0.14/0.38  # Proof object conjectures             : 15
% 0.14/0.38  # Proof object clause conjectures      : 12
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 13
% 0.14/0.38  # Proof object initial formulas used   : 7
% 0.14/0.38  # Proof object generating inferences   : 8
% 0.14/0.38  # Proof object simplifying inferences  : 15
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 7
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 34
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 34
% 0.14/0.38  # Processed clauses                    : 90
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 4
% 0.14/0.38  # ...remaining for further processing  : 86
% 0.14/0.38  # Other redundant clauses eliminated   : 0
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 0
% 0.14/0.38  # Backward-rewritten                   : 0
% 0.14/0.38  # Generated clauses                    : 63
% 0.14/0.38  # ...of the previous two non-trivial   : 32
% 0.14/0.38  # Contextual simplify-reflections      : 3
% 0.14/0.38  # Paramodulations                      : 63
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 0
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 52
% 0.14/0.38  #    Positive orientable unit clauses  : 5
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 4
% 0.14/0.38  #    Non-unit-clauses                  : 43
% 0.14/0.38  # Current number of unprocessed clauses: 10
% 0.14/0.38  # ...number of literals in the above   : 42
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 34
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 571
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 90
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 6
% 0.14/0.38  # Unit Clause-clause subsumption calls : 6
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 2
% 0.14/0.38  # BW rewrite match successes           : 0
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 5089
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.035 s
% 0.14/0.38  # System time              : 0.004 s
% 0.14/0.38  # Total time               : 0.038 s
% 0.14/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
