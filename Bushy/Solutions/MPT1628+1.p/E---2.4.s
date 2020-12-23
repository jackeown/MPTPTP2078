%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : waybel_0__t8_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:02 EDT 2019

% Result     : Theorem 56.04s
% Output     : CNFRefutation 56.04s
% Verified   : 
% Statistics : Number of formulae       :   90 (9433 expanded)
%              Number of clauses        :   71 (3155 expanded)
%              Number of leaves         :    9 (2294 expanded)
%              Depth                    :   23
%              Number of atoms          :  353 (76284 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   35 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t8_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3,X4] :
              ( r1_tarski(X3,X4)
             => ( ( r1_waybel_0(X1,X2,X3)
                 => r1_waybel_0(X1,X2,X4) )
                & ( r2_waybel_0(X1,X2,X3)
                 => r2_waybel_0(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t8_waybel_0.p',t8_waybel_0)).

fof(d12_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( r2_waybel_0(X1,X2,X3)
            <=> ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X2))
                 => ? [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                      & r1_orders_2(X2,X4,X5)
                      & r2_hidden(k2_waybel_0(X1,X2,X5),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t8_waybel_0.p',d12_waybel_0)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t8_waybel_0.p',existence_m1_subset_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t8_waybel_0.p',t4_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t8_waybel_0.p',t3_subset)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t8_waybel_0.p',t5_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t8_waybel_0.p',t2_subset)).

fof(d11_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( r1_waybel_0(X1,X2,X3)
            <=> ? [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X2))
                  & ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                     => ( r1_orders_2(X2,X4,X5)
                       => r2_hidden(k2_waybel_0(X1,X2,X5),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t8_waybel_0.p',d11_waybel_0)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t8_waybel_0.p',t8_boole)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_struct_0(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & l1_waybel_0(X2,X1) )
           => ! [X3,X4] :
                ( r1_tarski(X3,X4)
               => ( ( r1_waybel_0(X1,X2,X3)
                   => r1_waybel_0(X1,X2,X4) )
                  & ( r2_waybel_0(X1,X2,X3)
                   => r2_waybel_0(X1,X2,X4) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t8_waybel_0])).

fof(c_0_10,plain,(
    ! [X21,X22,X23,X24,X26,X28] :
      ( ( m1_subset_1(esk7_4(X21,X22,X23,X24),u1_struct_0(X22))
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ r2_waybel_0(X21,X22,X23)
        | v2_struct_0(X22)
        | ~ l1_waybel_0(X22,X21)
        | v2_struct_0(X21)
        | ~ l1_struct_0(X21) )
      & ( r1_orders_2(X22,X24,esk7_4(X21,X22,X23,X24))
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ r2_waybel_0(X21,X22,X23)
        | v2_struct_0(X22)
        | ~ l1_waybel_0(X22,X21)
        | v2_struct_0(X21)
        | ~ l1_struct_0(X21) )
      & ( r2_hidden(k2_waybel_0(X21,X22,esk7_4(X21,X22,X23,X24)),X23)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ r2_waybel_0(X21,X22,X23)
        | v2_struct_0(X22)
        | ~ l1_waybel_0(X22,X21)
        | v2_struct_0(X21)
        | ~ l1_struct_0(X21) )
      & ( m1_subset_1(esk8_3(X21,X22,X26),u1_struct_0(X22))
        | r2_waybel_0(X21,X22,X26)
        | v2_struct_0(X22)
        | ~ l1_waybel_0(X22,X21)
        | v2_struct_0(X21)
        | ~ l1_struct_0(X21) )
      & ( ~ m1_subset_1(X28,u1_struct_0(X22))
        | ~ r1_orders_2(X22,esk8_3(X21,X22,X26),X28)
        | ~ r2_hidden(k2_waybel_0(X21,X22,X28),X26)
        | r2_waybel_0(X21,X22,X26)
        | v2_struct_0(X22)
        | ~ l1_waybel_0(X22,X21)
        | v2_struct_0(X21)
        | ~ l1_struct_0(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_waybel_0])])])])])])])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & l1_struct_0(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & l1_waybel_0(esk2_0,esk1_0)
    & r1_tarski(esk3_0,esk4_0)
    & ( r2_waybel_0(esk1_0,esk2_0,esk3_0)
      | r1_waybel_0(esk1_0,esk2_0,esk3_0) )
    & ( ~ r2_waybel_0(esk1_0,esk2_0,esk4_0)
      | r1_waybel_0(esk1_0,esk2_0,esk3_0) )
    & ( r2_waybel_0(esk1_0,esk2_0,esk3_0)
      | ~ r1_waybel_0(esk1_0,esk2_0,esk4_0) )
    & ( ~ r2_waybel_0(esk1_0,esk2_0,esk4_0)
      | ~ r1_waybel_0(esk1_0,esk2_0,esk4_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])).

cnf(c_0_12,plain,
    ( r2_hidden(k2_waybel_0(X1,X2,esk7_4(X1,X2,X3,X4)),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_waybel_0(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( r2_waybel_0(esk1_0,esk2_0,esk3_0)
    | r1_waybel_0(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( l1_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( m1_subset_1(esk8_3(X1,X2,X3),u1_struct_0(X2))
    | r2_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_19,plain,(
    ! [X45] : m1_subset_1(esk12_1(X45),X45) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_20,plain,(
    ! [X59,X60,X61] :
      ( ~ r2_hidden(X59,X60)
      | ~ m1_subset_1(X60,k1_zfmisc_1(X61))
      | m1_subset_1(X59,X61) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk1_0,esk2_0,esk7_4(esk1_0,esk2_0,esk3_0,X1)),esk3_0)
    | r1_waybel_0(esk1_0,esk2_0,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15])]),c_0_16]),c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk8_3(esk1_0,esk2_0,X1),u1_struct_0(esk2_0))
    | r2_waybel_0(esk1_0,esk2_0,X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_14]),c_0_15])]),c_0_16]),c_0_17])).

fof(c_0_23,plain,(
    ! [X57,X58] :
      ( ( ~ m1_subset_1(X57,k1_zfmisc_1(X58))
        | r1_tarski(X57,X58) )
      & ( ~ r1_tarski(X57,X58)
        | m1_subset_1(X57,k1_zfmisc_1(X58)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_24,plain,(
    ! [X62,X63,X64] :
      ( ~ r2_hidden(X62,X63)
      | ~ m1_subset_1(X63,k1_zfmisc_1(X64))
      | ~ v1_xboole_0(X64) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_25,plain,
    ( m1_subset_1(esk12_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( r1_orders_2(X1,X2,esk7_4(X3,X1,X4,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_waybel_0(X3,X1,X4)
    | ~ l1_waybel_0(X1,X3)
    | ~ l1_struct_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_27,plain,
    ( m1_subset_1(esk7_4(X1,X2,X3,X4),u1_struct_0(X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_waybel_0(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_28,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk1_0,esk2_0,esk7_4(esk1_0,esk2_0,esk3_0,esk8_3(esk1_0,esk2_0,X1))),esk3_0)
    | r2_waybel_0(esk1_0,esk2_0,X1)
    | r1_waybel_0(esk1_0,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk1_0,esk2_0,esk7_4(esk1_0,esk2_0,esk3_0,esk12_1(u1_struct_0(esk2_0)))),esk3_0)
    | r1_waybel_0(esk1_0,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk7_4(esk1_0,esk2_0,esk3_0,X1))
    | r1_waybel_0(esk1_0,esk2_0,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_13]),c_0_14]),c_0_15])]),c_0_17]),c_0_16])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk7_4(esk1_0,esk2_0,esk3_0,X1),u1_struct_0(esk2_0))
    | r1_waybel_0(esk1_0,esk2_0,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_13]),c_0_14]),c_0_15])]),c_0_16]),c_0_17])).

fof(c_0_36,plain,(
    ! [X55,X56] :
      ( ~ m1_subset_1(X55,X56)
      | v1_xboole_0(X56)
      | r2_hidden(X55,X56) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(k2_waybel_0(esk1_0,esk2_0,esk7_4(esk1_0,esk2_0,esk3_0,esk8_3(esk1_0,esk2_0,X1))),X2)
    | r2_waybel_0(esk1_0,esk2_0,X1)
    | r1_waybel_0(esk1_0,esk2_0,esk3_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( r1_waybel_0(esk1_0,esk2_0,esk3_0)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,plain,
    ( r2_waybel_0(X3,X2,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_orders_2(X2,esk8_3(X3,X2,X4),X1)
    | ~ r2_hidden(k2_waybel_0(X3,X2,X1),X4)
    | ~ l1_waybel_0(X2,X3)
    | ~ l1_struct_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_41,negated_conjecture,
    ( r1_orders_2(esk2_0,esk8_3(esk1_0,esk2_0,X1),esk7_4(esk1_0,esk2_0,esk3_0,esk8_3(esk1_0,esk2_0,X1)))
    | r2_waybel_0(esk1_0,esk2_0,X1)
    | r1_waybel_0(esk1_0,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_22])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk7_4(esk1_0,esk2_0,esk3_0,esk8_3(esk1_0,esk2_0,X1)),u1_struct_0(esk2_0))
    | r2_waybel_0(esk1_0,esk2_0,X1)
    | r1_waybel_0(esk1_0,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_22])).

cnf(c_0_43,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(k2_waybel_0(esk1_0,esk2_0,esk7_4(esk1_0,esk2_0,esk3_0,esk8_3(esk1_0,esk2_0,X1))),esk4_0)
    | r2_waybel_0(esk1_0,esk2_0,X1)
    | r1_waybel_0(esk1_0,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( r1_waybel_0(esk1_0,esk2_0,esk3_0)
    | ~ v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_38])).

fof(c_0_46,plain,(
    ! [X13,X14,X15,X17,X18,X19] :
      ( ( m1_subset_1(esk5_3(X13,X14,X15),u1_struct_0(X14))
        | ~ r1_waybel_0(X13,X14,X15)
        | v2_struct_0(X14)
        | ~ l1_waybel_0(X14,X13)
        | v2_struct_0(X13)
        | ~ l1_struct_0(X13) )
      & ( ~ m1_subset_1(X17,u1_struct_0(X14))
        | ~ r1_orders_2(X14,esk5_3(X13,X14,X15),X17)
        | r2_hidden(k2_waybel_0(X13,X14,X17),X15)
        | ~ r1_waybel_0(X13,X14,X15)
        | v2_struct_0(X14)
        | ~ l1_waybel_0(X14,X13)
        | v2_struct_0(X13)
        | ~ l1_struct_0(X13) )
      & ( m1_subset_1(esk6_4(X13,X14,X18,X19),u1_struct_0(X14))
        | ~ m1_subset_1(X19,u1_struct_0(X14))
        | r1_waybel_0(X13,X14,X18)
        | v2_struct_0(X14)
        | ~ l1_waybel_0(X14,X13)
        | v2_struct_0(X13)
        | ~ l1_struct_0(X13) )
      & ( r1_orders_2(X14,X19,esk6_4(X13,X14,X18,X19))
        | ~ m1_subset_1(X19,u1_struct_0(X14))
        | r1_waybel_0(X13,X14,X18)
        | v2_struct_0(X14)
        | ~ l1_waybel_0(X14,X13)
        | v2_struct_0(X13)
        | ~ l1_struct_0(X13) )
      & ( ~ r2_hidden(k2_waybel_0(X13,X14,esk6_4(X13,X14,X18,X19)),X18)
        | ~ m1_subset_1(X19,u1_struct_0(X14))
        | r1_waybel_0(X13,X14,X18)
        | v2_struct_0(X14)
        | ~ l1_waybel_0(X14,X13)
        | v2_struct_0(X13)
        | ~ l1_struct_0(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_waybel_0])])])])])])])).

cnf(c_0_47,negated_conjecture,
    ( r2_waybel_0(esk1_0,esk2_0,X1)
    | r1_waybel_0(esk1_0,esk2_0,esk3_0)
    | ~ r2_hidden(k2_waybel_0(esk1_0,esk2_0,esk7_4(esk1_0,esk2_0,esk3_0,esk8_3(esk1_0,esk2_0,X1))),X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_14]),c_0_15])]),c_0_17]),c_0_16]),c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk1_0,esk2_0,esk7_4(esk1_0,esk2_0,esk3_0,esk8_3(esk1_0,esk2_0,X1))),esk4_0)
    | r2_waybel_0(esk1_0,esk2_0,X1)
    | r1_waybel_0(esk1_0,esk2_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( r1_waybel_0(esk1_0,esk2_0,esk3_0)
    | ~ r2_waybel_0(esk1_0,esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_50,plain,
    ( r1_orders_2(X1,X2,esk6_4(X3,X1,X4,X2))
    | r1_waybel_0(X3,X1,X4)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_waybel_0(X1,X3)
    | ~ l1_struct_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_51,plain,
    ( m1_subset_1(esk5_3(X1,X2,X3),u1_struct_0(X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_waybel_0(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( r1_waybel_0(esk1_0,esk2_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

cnf(c_0_53,plain,
    ( m1_subset_1(esk6_4(X1,X2,X3,X4),u1_struct_0(X2))
    | r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk6_4(esk1_0,esk2_0,X2,X1))
    | r1_waybel_0(esk1_0,esk2_0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_14]),c_0_15])]),c_0_17]),c_0_16])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk5_3(esk1_0,esk2_0,esk3_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_14]),c_0_15])]),c_0_16]),c_0_17])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk6_4(esk1_0,esk2_0,X1,X2),u1_struct_0(esk2_0))
    | r1_waybel_0(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_14]),c_0_15])]),c_0_16]),c_0_17])).

cnf(c_0_57,plain,
    ( r2_hidden(k2_waybel_0(X3,X2,X1),X4)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_orders_2(X2,esk5_3(X3,X2,X4),X1)
    | ~ r1_waybel_0(X3,X2,X4)
    | ~ l1_waybel_0(X2,X3)
    | ~ l1_struct_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_58,negated_conjecture,
    ( r1_orders_2(esk2_0,esk5_3(esk1_0,esk2_0,esk3_0),esk6_4(esk1_0,esk2_0,X1,esk5_3(esk1_0,esk2_0,esk3_0)))
    | r1_waybel_0(esk1_0,esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk6_4(esk1_0,esk2_0,X1,esk5_3(esk1_0,esk2_0,esk3_0)),u1_struct_0(esk2_0))
    | r1_waybel_0(esk1_0,esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk1_0,esk2_0,esk6_4(esk1_0,esk2_0,X1,esk5_3(esk1_0,esk2_0,esk3_0))),esk3_0)
    | r1_waybel_0(esk1_0,esk2_0,X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_52]),c_0_14]),c_0_15])]),c_0_17]),c_0_16]),c_0_59])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(k2_waybel_0(esk1_0,esk2_0,esk6_4(esk1_0,esk2_0,X1,esk5_3(esk1_0,esk2_0,esk3_0))),X2)
    | r1_waybel_0(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_60])).

cnf(c_0_62,negated_conjecture,
    ( r1_waybel_0(esk1_0,esk2_0,X1)
    | ~ v1_xboole_0(X2)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_60])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(k2_waybel_0(esk1_0,esk2_0,esk6_4(esk1_0,esk2_0,X1,esk5_3(esk1_0,esk2_0,esk3_0))),esk4_0)
    | r1_waybel_0(esk1_0,esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_38])).

cnf(c_0_64,negated_conjecture,
    ( r1_waybel_0(esk1_0,esk2_0,X1)
    | ~ v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_38])).

cnf(c_0_65,plain,
    ( r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(k2_waybel_0(X1,X2,esk6_4(X1,X2,X3,X4)),X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk1_0,esk2_0,esk6_4(esk1_0,esk2_0,X1,esk5_3(esk1_0,esk2_0,esk3_0))),esk4_0)
    | r1_waybel_0(esk1_0,esk2_0,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_63]),c_0_64])).

cnf(c_0_67,negated_conjecture,
    ( r2_waybel_0(esk1_0,esk2_0,esk3_0)
    | ~ r1_waybel_0(esk1_0,esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_68,negated_conjecture,
    ( r1_waybel_0(esk1_0,esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_55]),c_0_14]),c_0_15])]),c_0_16]),c_0_17])).

cnf(c_0_69,negated_conjecture,
    ( r2_waybel_0(esk1_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_68])])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk1_0,esk2_0,esk7_4(esk1_0,esk2_0,esk3_0,X1)),esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_69]),c_0_14]),c_0_15])]),c_0_16]),c_0_17])).

fof(c_0_71,plain,(
    ! [X68,X69] :
      ( ~ v1_xboole_0(X68)
      | X68 = X69
      | ~ v1_xboole_0(X69) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_72,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk12_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_25])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk1_0,esk2_0,esk7_4(esk1_0,esk2_0,esk3_0,esk8_3(esk1_0,esk2_0,X1))),esk3_0)
    | r2_waybel_0(esk1_0,esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_22])).

cnf(c_0_74,negated_conjecture,
    ( ~ r2_waybel_0(esk1_0,esk2_0,esk4_0)
    | ~ r1_waybel_0(esk1_0,esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_75,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_76,plain,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk7_4(esk1_0,esk2_0,esk3_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_69]),c_0_14]),c_0_15])]),c_0_17]),c_0_16])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(esk7_4(esk1_0,esk2_0,esk3_0,X1),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_69]),c_0_14]),c_0_15])]),c_0_16]),c_0_17])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(k2_waybel_0(esk1_0,esk2_0,esk7_4(esk1_0,esk2_0,esk3_0,esk8_3(esk1_0,esk2_0,X1))),X2)
    | r2_waybel_0(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_73])).

cnf(c_0_80,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0)
    | ~ v1_xboole_0(X1)
    | ~ r2_waybel_0(esk1_0,esk2_0,X1)
    | ~ r1_waybel_0(esk1_0,esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_81,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_38])).

cnf(c_0_82,negated_conjecture,
    ( r1_orders_2(esk2_0,esk8_3(esk1_0,esk2_0,X1),esk7_4(esk1_0,esk2_0,esk3_0,esk8_3(esk1_0,esk2_0,X1)))
    | r2_waybel_0(esk1_0,esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_22])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(esk7_4(esk1_0,esk2_0,esk3_0,esk8_3(esk1_0,esk2_0,X1)),u1_struct_0(esk2_0))
    | r2_waybel_0(esk1_0,esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_22])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(k2_waybel_0(esk1_0,esk2_0,esk7_4(esk1_0,esk2_0,esk3_0,esk8_3(esk1_0,esk2_0,X1))),esk4_0)
    | r2_waybel_0(esk1_0,esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_79,c_0_38])).

cnf(c_0_85,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_69]),c_0_52])]),c_0_81])).

cnf(c_0_86,negated_conjecture,
    ( r2_waybel_0(esk1_0,esk2_0,X1)
    | ~ r2_hidden(k2_waybel_0(esk1_0,esk2_0,esk7_4(esk1_0,esk2_0,esk3_0,esk8_3(esk1_0,esk2_0,X1))),X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_82]),c_0_14]),c_0_15])]),c_0_17]),c_0_16]),c_0_83])).

cnf(c_0_87,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk1_0,esk2_0,esk7_4(esk1_0,esk2_0,esk3_0,esk8_3(esk1_0,esk2_0,X1))),esk4_0)
    | r2_waybel_0(esk1_0,esk2_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_84]),c_0_85])).

cnf(c_0_88,negated_conjecture,
    ( ~ r2_waybel_0(esk1_0,esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_68])])).

cnf(c_0_89,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88]),
    [proof]).
%------------------------------------------------------------------------------
