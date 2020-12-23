%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:07 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 361 expanded)
%              Number of clauses        :   36 ( 141 expanded)
%              Number of leaves         :    6 (  88 expanded)
%              Depth                    :   12
%              Number of atoms          :  190 (1490 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   18 (   3 average)
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

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(t78_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v1_tops_2(X2,X1)
          <=> r1_tarski(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(t18_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ( ( r1_tarski(X2,X3)
                  & v1_tops_2(X3,X1) )
               => v1_tops_2(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tops_2)).

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

fof(c_0_6,plain,(
    ! [X12,X13,X14] :
      ( ( ~ v1_tops_2(X13,X12)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ r2_hidden(X14,X13)
        | v3_pre_topc(X14,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk2_2(X12,X13),k1_zfmisc_1(u1_struct_0(X12)))
        | v1_tops_2(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | ~ l1_pre_topc(X12) )
      & ( r2_hidden(esk2_2(X12,X13),X13)
        | v1_tops_2(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | ~ l1_pre_topc(X12) )
      & ( ~ v3_pre_topc(esk2_2(X12,X13),X12)
        | v1_tops_2(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | ~ l1_pre_topc(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_2])])])])])).

fof(c_0_7,plain,(
    ! [X11] :
      ( ~ l1_pre_topc(X11)
      | m1_subset_1(u1_pre_topc(X11),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X11)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ( v1_tops_2(X2,X1)
            <=> r1_tarski(X2,u1_pre_topc(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t78_tops_2])).

cnf(c_0_9,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,negated_conjecture,
    ( l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))
    & ( ~ v1_tops_2(esk4_0,esk3_0)
      | ~ r1_tarski(esk4_0,u1_pre_topc(esk3_0)) )
    & ( v1_tops_2(esk4_0,esk3_0)
      | r1_tarski(esk4_0,u1_pre_topc(esk3_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_12,plain,
    ( m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_13,plain,(
    ! [X9,X10] :
      ( ( ~ v3_pre_topc(X10,X9)
        | r2_hidden(X10,u1_pre_topc(X9))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_pre_topc(X9) )
      & ( ~ r2_hidden(X10,u1_pre_topc(X9))
        | v3_pre_topc(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_pre_topc(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_14,plain,
    ( v1_tops_2(u1_pre_topc(X1),X1)
    | r2_hidden(esk2_2(X1,u1_pre_topc(X1)),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( v1_tops_2(u1_pre_topc(X1),X1)
    | m1_subset_1(esk2_2(X1,u1_pre_topc(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_10])).

fof(c_0_17,plain,(
    ! [X16,X17,X18] :
      ( ~ l1_pre_topc(X16)
      | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X16))))
      | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X16))))
      | ~ r1_tarski(X17,X18)
      | ~ v1_tops_2(X18,X16)
      | v1_tops_2(X17,X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_tops_2])])])).

cnf(c_0_18,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( v1_tops_2(u1_pre_topc(esk3_0),esk3_0)
    | r2_hidden(esk2_2(esk3_0,u1_pre_topc(esk3_0)),u1_pre_topc(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( v1_tops_2(u1_pre_topc(esk3_0),esk3_0)
    | m1_subset_1(esk2_2(esk3_0,u1_pre_topc(esk3_0)),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_15])).

cnf(c_0_21,plain,
    ( v1_tops_2(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(X2,X3)
    | ~ v1_tops_2(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( v1_tops_2(X2,X1)
    | ~ v3_pre_topc(esk2_2(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_23,negated_conjecture,
    ( v1_tops_2(u1_pre_topc(esk3_0),esk3_0)
    | v3_pre_topc(esk2_2(esk3_0,u1_pre_topc(esk3_0)),esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_15])]),c_0_20])).

cnf(c_0_24,plain,
    ( v1_tops_2(X1,X2)
    | ~ v1_tops_2(u1_pre_topc(X2),X2)
    | ~ l1_pre_topc(X2)
    | ~ r1_tarski(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_10])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_26,negated_conjecture,
    ( v1_tops_2(esk4_0,esk3_0)
    | r1_tarski(esk4_0,u1_pre_topc(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_27,negated_conjecture,
    ( v1_tops_2(u1_pre_topc(esk3_0),esk3_0)
    | ~ m1_subset_1(u1_pre_topc(esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_15])])).

fof(c_0_28,plain,(
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

cnf(c_0_29,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tops_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_30,negated_conjecture,
    ( v1_tops_2(esk4_0,esk3_0)
    | ~ v1_tops_2(u1_pre_topc(esk3_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_15])]),c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( v1_tops_2(u1_pre_topc(esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_10]),c_0_15])])).

cnf(c_0_32,plain,
    ( r1_tarski(X2,X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_34,negated_conjecture,
    ( v3_pre_topc(X1,esk3_0)
    | ~ v1_tops_2(esk4_0,esk3_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_25]),c_0_15])])).

cnf(c_0_35,negated_conjecture,
    ( v1_tops_2(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31])])).

cnf(c_0_36,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( ~ v1_tops_2(esk4_0,esk3_0)
    | ~ r1_tarski(esk4_0,u1_pre_topc(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_38,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),X1)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(esk1_3(X3,X1,u1_pre_topc(X2)),X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(esk1_3(X3,X1,u1_pre_topc(X2)),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(u1_pre_topc(X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( v3_pre_topc(X1,esk3_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35])])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,u1_pre_topc(X2))
    | r2_hidden(esk1_3(k1_zfmisc_1(u1_struct_0(X2)),X1,u1_pre_topc(X2)),X1)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_10])).

cnf(c_0_42,negated_conjecture,
    ( ~ r1_tarski(esk4_0,u1_pre_topc(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_35])])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,u1_pre_topc(X2))
    | m1_subset_1(esk1_3(k1_zfmisc_1(u1_struct_0(X2)),X1,u1_pre_topc(X2)),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_10])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(X1,u1_pre_topc(esk3_0))
    | ~ r2_hidden(esk1_3(X2,X1,u1_pre_topc(esk3_0)),esk4_0)
    | ~ m1_subset_1(esk1_3(X2,X1,u1_pre_topc(esk3_0)),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(u1_pre_topc(esk3_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_15])])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk1_3(k1_zfmisc_1(u1_struct_0(esk3_0)),esk4_0,u1_pre_topc(esk3_0)),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_25]),c_0_15])]),c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk1_3(k1_zfmisc_1(u1_struct_0(esk3_0)),esk4_0,u1_pre_topc(esk3_0)),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_25]),c_0_15])]),c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( ~ m1_subset_1(u1_pre_topc(esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_25])]),c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_10]),c_0_15])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:32:31 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.028 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(d1_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(v1_tops_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X3,X2)=>v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_2)).
% 0.12/0.37  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.12/0.37  fof(t78_tops_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(v1_tops_2(X2,X1)<=>r1_tarski(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_tops_2)).
% 0.12/0.37  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 0.12/0.37  fof(t18_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>((r1_tarski(X2,X3)&v1_tops_2(X3,X1))=>v1_tops_2(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_tops_2)).
% 0.12/0.37  fof(t7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,X2)=>r2_hidden(X4,X3)))=>r1_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_subset_1)).
% 0.12/0.37  fof(c_0_6, plain, ![X12, X13, X14]:((~v1_tops_2(X13,X12)|(~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|(~r2_hidden(X14,X13)|v3_pre_topc(X14,X12)))|~m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))|~l1_pre_topc(X12))&((m1_subset_1(esk2_2(X12,X13),k1_zfmisc_1(u1_struct_0(X12)))|v1_tops_2(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))|~l1_pre_topc(X12))&((r2_hidden(esk2_2(X12,X13),X13)|v1_tops_2(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))|~l1_pre_topc(X12))&(~v3_pre_topc(esk2_2(X12,X13),X12)|v1_tops_2(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))|~l1_pre_topc(X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_2])])])])])).
% 0.12/0.37  fof(c_0_7, plain, ![X11]:(~l1_pre_topc(X11)|m1_subset_1(u1_pre_topc(X11),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X11))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.12/0.37  fof(c_0_8, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(v1_tops_2(X2,X1)<=>r1_tarski(X2,u1_pre_topc(X1)))))), inference(assume_negation,[status(cth)],[t78_tops_2])).
% 0.12/0.38  cnf(c_0_9, plain, (r2_hidden(esk2_2(X1,X2),X2)|v1_tops_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.38  cnf(c_0_10, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.38  fof(c_0_11, negated_conjecture, (l1_pre_topc(esk3_0)&(m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))&((~v1_tops_2(esk4_0,esk3_0)|~r1_tarski(esk4_0,u1_pre_topc(esk3_0)))&(v1_tops_2(esk4_0,esk3_0)|r1_tarski(esk4_0,u1_pre_topc(esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.12/0.38  cnf(c_0_12, plain, (m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v1_tops_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.38  fof(c_0_13, plain, ![X9, X10]:((~v3_pre_topc(X10,X9)|r2_hidden(X10,u1_pre_topc(X9))|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))|~l1_pre_topc(X9))&(~r2_hidden(X10,u1_pre_topc(X9))|v3_pre_topc(X10,X9)|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))|~l1_pre_topc(X9))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 0.12/0.38  cnf(c_0_14, plain, (v1_tops_2(u1_pre_topc(X1),X1)|r2_hidden(esk2_2(X1,u1_pre_topc(X1)),u1_pre_topc(X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.12/0.38  cnf(c_0_15, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  cnf(c_0_16, plain, (v1_tops_2(u1_pre_topc(X1),X1)|m1_subset_1(esk2_2(X1,u1_pre_topc(X1)),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_12, c_0_10])).
% 0.12/0.38  fof(c_0_17, plain, ![X16, X17, X18]:(~l1_pre_topc(X16)|(~m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X16))))|(~m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X16))))|(~r1_tarski(X17,X18)|~v1_tops_2(X18,X16)|v1_tops_2(X17,X16))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_tops_2])])])).
% 0.12/0.38  cnf(c_0_18, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.38  cnf(c_0_19, negated_conjecture, (v1_tops_2(u1_pre_topc(esk3_0),esk3_0)|r2_hidden(esk2_2(esk3_0,u1_pre_topc(esk3_0)),u1_pre_topc(esk3_0))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.12/0.38  cnf(c_0_20, negated_conjecture, (v1_tops_2(u1_pre_topc(esk3_0),esk3_0)|m1_subset_1(esk2_2(esk3_0,u1_pre_topc(esk3_0)),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_16, c_0_15])).
% 0.12/0.38  cnf(c_0_21, plain, (v1_tops_2(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~r1_tarski(X2,X3)|~v1_tops_2(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.38  cnf(c_0_22, plain, (v1_tops_2(X2,X1)|~v3_pre_topc(esk2_2(X1,X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.38  cnf(c_0_23, negated_conjecture, (v1_tops_2(u1_pre_topc(esk3_0),esk3_0)|v3_pre_topc(esk2_2(esk3_0,u1_pre_topc(esk3_0)),esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_15])]), c_0_20])).
% 0.12/0.38  cnf(c_0_24, plain, (v1_tops_2(X1,X2)|~v1_tops_2(u1_pre_topc(X2),X2)|~l1_pre_topc(X2)|~r1_tarski(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))), inference(spm,[status(thm)],[c_0_21, c_0_10])).
% 0.12/0.38  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  cnf(c_0_26, negated_conjecture, (v1_tops_2(esk4_0,esk3_0)|r1_tarski(esk4_0,u1_pre_topc(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  cnf(c_0_27, negated_conjecture, (v1_tops_2(u1_pre_topc(esk3_0),esk3_0)|~m1_subset_1(u1_pre_topc(esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_15])])).
% 0.12/0.38  fof(c_0_28, plain, ![X5, X6, X7]:((m1_subset_1(esk1_3(X5,X6,X7),X5)|r1_tarski(X6,X7)|~m1_subset_1(X7,k1_zfmisc_1(X5))|~m1_subset_1(X6,k1_zfmisc_1(X5)))&((r2_hidden(esk1_3(X5,X6,X7),X6)|r1_tarski(X6,X7)|~m1_subset_1(X7,k1_zfmisc_1(X5))|~m1_subset_1(X6,k1_zfmisc_1(X5)))&(~r2_hidden(esk1_3(X5,X6,X7),X7)|r1_tarski(X6,X7)|~m1_subset_1(X7,k1_zfmisc_1(X5))|~m1_subset_1(X6,k1_zfmisc_1(X5))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).
% 0.12/0.38  cnf(c_0_29, plain, (v3_pre_topc(X3,X2)|~v1_tops_2(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.38  cnf(c_0_30, negated_conjecture, (v1_tops_2(esk4_0,esk3_0)|~v1_tops_2(u1_pre_topc(esk3_0),esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_15])]), c_0_26])).
% 0.12/0.38  cnf(c_0_31, negated_conjecture, (v1_tops_2(u1_pre_topc(esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_10]), c_0_15])])).
% 0.12/0.38  cnf(c_0_32, plain, (r1_tarski(X2,X3)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.38  cnf(c_0_33, plain, (r2_hidden(X1,u1_pre_topc(X2))|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.38  cnf(c_0_34, negated_conjecture, (v3_pre_topc(X1,esk3_0)|~v1_tops_2(esk4_0,esk3_0)|~r2_hidden(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_25]), c_0_15])])).
% 0.12/0.38  cnf(c_0_35, negated_conjecture, (v1_tops_2(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31])])).
% 0.12/0.38  cnf(c_0_36, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r1_tarski(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.38  cnf(c_0_37, negated_conjecture, (~v1_tops_2(esk4_0,esk3_0)|~r1_tarski(esk4_0,u1_pre_topc(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  cnf(c_0_38, plain, (m1_subset_1(esk1_3(X1,X2,X3),X1)|r1_tarski(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.38  cnf(c_0_39, plain, (r1_tarski(X1,u1_pre_topc(X2))|~v3_pre_topc(esk1_3(X3,X1,u1_pre_topc(X2)),X2)|~l1_pre_topc(X2)|~m1_subset_1(esk1_3(X3,X1,u1_pre_topc(X2)),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(u1_pre_topc(X2),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.12/0.38  cnf(c_0_40, negated_conjecture, (v3_pre_topc(X1,esk3_0)|~r2_hidden(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35])])).
% 0.12/0.38  cnf(c_0_41, plain, (r1_tarski(X1,u1_pre_topc(X2))|r2_hidden(esk1_3(k1_zfmisc_1(u1_struct_0(X2)),X1,u1_pre_topc(X2)),X1)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))), inference(spm,[status(thm)],[c_0_36, c_0_10])).
% 0.12/0.38  cnf(c_0_42, negated_conjecture, (~r1_tarski(esk4_0,u1_pre_topc(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_35])])).
% 0.12/0.38  cnf(c_0_43, plain, (r1_tarski(X1,u1_pre_topc(X2))|m1_subset_1(esk1_3(k1_zfmisc_1(u1_struct_0(X2)),X1,u1_pre_topc(X2)),k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))), inference(spm,[status(thm)],[c_0_38, c_0_10])).
% 0.12/0.38  cnf(c_0_44, negated_conjecture, (r1_tarski(X1,u1_pre_topc(esk3_0))|~r2_hidden(esk1_3(X2,X1,u1_pre_topc(esk3_0)),esk4_0)|~m1_subset_1(esk1_3(X2,X1,u1_pre_topc(esk3_0)),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(u1_pre_topc(esk3_0),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_15])])).
% 0.12/0.38  cnf(c_0_45, negated_conjecture, (r2_hidden(esk1_3(k1_zfmisc_1(u1_struct_0(esk3_0)),esk4_0,u1_pre_topc(esk3_0)),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_25]), c_0_15])]), c_0_42])).
% 0.12/0.38  cnf(c_0_46, negated_conjecture, (m1_subset_1(esk1_3(k1_zfmisc_1(u1_struct_0(esk3_0)),esk4_0,u1_pre_topc(esk3_0)),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_25]), c_0_15])]), c_0_42])).
% 0.12/0.38  cnf(c_0_47, negated_conjecture, (~m1_subset_1(u1_pre_topc(esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_25])]), c_0_42])).
% 0.12/0.38  cnf(c_0_48, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_10]), c_0_15])]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 49
% 0.12/0.38  # Proof object clause steps            : 36
% 0.12/0.38  # Proof object formula steps           : 13
% 0.12/0.38  # Proof object conjectures             : 22
% 0.12/0.38  # Proof object clause conjectures      : 19
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 15
% 0.12/0.38  # Proof object initial formulas used   : 6
% 0.12/0.38  # Proof object generating inferences   : 18
% 0.12/0.38  # Proof object simplifying inferences  : 32
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 6
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 15
% 0.12/0.38  # Removed in clause preprocessing      : 0
% 0.12/0.38  # Initial clauses in saturation        : 15
% 0.12/0.38  # Processed clauses                    : 85
% 0.12/0.38  # ...of these trivial                  : 0
% 0.12/0.38  # ...subsumed                          : 2
% 0.12/0.38  # ...remaining for further processing  : 83
% 0.12/0.38  # Other redundant clauses eliminated   : 0
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 0
% 0.12/0.38  # Backward-rewritten                   : 16
% 0.12/0.38  # Generated clauses                    : 75
% 0.12/0.38  # ...of the previous two non-trivial   : 72
% 0.12/0.38  # Contextual simplify-reflections      : 4
% 0.12/0.38  # Paramodulations                      : 75
% 0.12/0.38  # Factorizations                       : 0
% 0.12/0.38  # Equation resolutions                 : 0
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 52
% 0.12/0.38  #    Positive orientable unit clauses  : 8
% 0.12/0.38  #    Positive unorientable unit clauses: 0
% 0.12/0.38  #    Negative unit clauses             : 2
% 0.12/0.38  #    Non-unit-clauses                  : 42
% 0.12/0.38  # Current number of unprocessed clauses: 9
% 0.12/0.38  # ...number of literals in the above   : 31
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 31
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 231
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 73
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 6
% 0.12/0.38  # Unit Clause-clause subsumption calls : 20
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 4
% 0.12/0.38  # BW rewrite match successes           : 4
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 4214
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.032 s
% 0.12/0.38  # System time              : 0.005 s
% 0.12/0.38  # Total time               : 0.038 s
% 0.12/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
