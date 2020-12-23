%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1648+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:31 EST 2020

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 207 expanded)
%              Number of clauses        :   41 (  83 expanded)
%              Number of leaves         :    6 (  50 expanded)
%              Depth                    :   13
%              Number of atoms          :  207 (1032 expanded)
%              Number of equality atoms :   13 (  50 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t28_waybel_0,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r2_hidden(X3,X2)
                 => v13_waybel_0(X3,X1) ) )
           => ( v13_waybel_0(k5_setfam_1(u1_struct_0(X1),X2),X1)
              & m1_subset_1(k5_setfam_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_waybel_0)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(dt_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k5_setfam_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

fof(redefinition_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k5_setfam_1(X1,X2) = k3_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(d20_waybel_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v13_waybel_0(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( ( r2_hidden(X3,X2)
                        & r1_orders_2(X1,X3,X4) )
                     => r2_hidden(X4,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ( ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X3,X2)
                   => v13_waybel_0(X3,X1) ) )
             => ( v13_waybel_0(k5_setfam_1(u1_struct_0(X1),X2),X1)
                & m1_subset_1(k5_setfam_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t28_waybel_0])).

fof(c_0_7,plain,(
    ! [X26,X27,X28] :
      ( ~ r2_hidden(X26,X27)
      | ~ m1_subset_1(X27,k1_zfmisc_1(X28))
      | m1_subset_1(X26,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_8,negated_conjecture,(
    ! [X31] :
      ( l1_orders_2(esk6_0)
      & m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0))))
      & ( ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(esk6_0)))
        | ~ r2_hidden(X31,esk7_0)
        | v13_waybel_0(X31,esk6_0) )
      & ( ~ v13_waybel_0(k5_setfam_1(u1_struct_0(esk6_0),esk7_0),esk6_0)
        | ~ m1_subset_1(k5_setfam_1(u1_struct_0(esk6_0),esk7_0),k1_zfmisc_1(u1_struct_0(esk6_0))) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).

fof(c_0_9,plain,(
    ! [X22,X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(X22)))
      | m1_subset_1(k5_setfam_1(X22,X23),k1_zfmisc_1(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_setfam_1])])).

fof(c_0_10,plain,(
    ! [X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(X24)))
      | k5_setfam_1(X24,X25) = k3_tarski(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).

fof(c_0_11,plain,(
    ! [X5,X6,X7,X8] :
      ( ( ~ v13_waybel_0(X6,X5)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X8,u1_struct_0(X5))
        | ~ r2_hidden(X7,X6)
        | ~ r1_orders_2(X5,X7,X8)
        | r2_hidden(X8,X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ l1_orders_2(X5) )
      & ( m1_subset_1(esk1_2(X5,X6),u1_struct_0(X5))
        | v13_waybel_0(X6,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ l1_orders_2(X5) )
      & ( m1_subset_1(esk2_2(X5,X6),u1_struct_0(X5))
        | v13_waybel_0(X6,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ l1_orders_2(X5) )
      & ( r2_hidden(esk1_2(X5,X6),X6)
        | v13_waybel_0(X6,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ l1_orders_2(X5) )
      & ( r1_orders_2(X5,esk1_2(X5,X6),esk2_2(X5,X6))
        | v13_waybel_0(X6,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ l1_orders_2(X5) )
      & ( ~ r2_hidden(esk2_2(X5,X6),X6)
        | v13_waybel_0(X6,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ l1_orders_2(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).

cnf(c_0_12,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( m1_subset_1(k5_setfam_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k5_setfam_1(X2,X1) = k3_tarski(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( ~ v13_waybel_0(k5_setfam_1(u1_struct_0(esk6_0),esk7_0),esk6_0)
    | ~ m1_subset_1(k5_setfam_1(u1_struct_0(esk6_0),esk7_0),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,plain,
    ( r2_hidden(X4,X1)
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(X3,X1)
    | ~ r1_orders_2(X2,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( v13_waybel_0(X1,esk6_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_20,plain,
    ( m1_subset_1(esk2_2(X1,X2),u1_struct_0(X1))
    | v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,plain,
    ( m1_subset_1(k3_tarski(X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( ~ v13_waybel_0(k5_setfam_1(u1_struct_0(esk6_0),esk7_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_14]),c_0_13])])).

cnf(c_0_23,plain,
    ( r1_orders_2(X1,esk1_2(X1,X2),esk2_2(X1,X2))
    | v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_24,plain,(
    ! [X11,X12,X13,X15,X16,X17,X18,X20] :
      ( ( r2_hidden(X13,esk3_3(X11,X12,X13))
        | ~ r2_hidden(X13,X12)
        | X12 != k3_tarski(X11) )
      & ( r2_hidden(esk3_3(X11,X12,X13),X11)
        | ~ r2_hidden(X13,X12)
        | X12 != k3_tarski(X11) )
      & ( ~ r2_hidden(X15,X16)
        | ~ r2_hidden(X16,X11)
        | r2_hidden(X15,X12)
        | X12 != k3_tarski(X11) )
      & ( ~ r2_hidden(esk4_2(X17,X18),X18)
        | ~ r2_hidden(esk4_2(X17,X18),X20)
        | ~ r2_hidden(X20,X17)
        | X18 = k3_tarski(X17) )
      & ( r2_hidden(esk4_2(X17,X18),esk5_2(X17,X18))
        | r2_hidden(esk4_2(X17,X18),X18)
        | X18 = k3_tarski(X17) )
      & ( r2_hidden(esk5_2(X17,X18),X17)
        | r2_hidden(esk4_2(X17,X18),X18)
        | X18 = k3_tarski(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_orders_2(X3,X4,X1)
    | ~ r2_hidden(X4,X2)
    | ~ v13_waybel_0(X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(csr,[status(thm)],[c_0_17,c_0_12])).

cnf(c_0_26,negated_conjecture,
    ( l1_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_27,negated_conjecture,
    ( v13_waybel_0(X1,esk6_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_28,plain,
    ( v13_waybel_0(k3_tarski(X1),X2)
    | m1_subset_1(esk2_2(X2,k3_tarski(X1)),u1_struct_0(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( ~ v13_waybel_0(k3_tarski(esk7_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_15]),c_0_13])])).

cnf(c_0_30,plain,
    ( r1_orders_2(X1,esk1_2(X1,k5_setfam_1(u1_struct_0(X1),X2)),esk2_2(X1,k5_setfam_1(u1_struct_0(X1),X2)))
    | v13_waybel_0(k5_setfam_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_14])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | X4 != k3_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | X2 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r1_orders_2(esk6_0,X3,X1)
    | ~ r2_hidden(X2,esk7_0)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_19]),c_0_26])]),c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk2_2(esk6_0,k3_tarski(esk7_0)),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_13]),c_0_26])]),c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( r1_orders_2(esk6_0,esk1_2(esk6_0,k5_setfam_1(u1_struct_0(esk6_0),esk7_0)),esk2_2(esk6_0,k5_setfam_1(u1_struct_0(esk6_0),esk7_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_13]),c_0_26])]),c_0_22])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( r2_hidden(esk3_3(X1,k3_tarski(X1),X2),X1)
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk2_2(esk6_0,k3_tarski(esk7_0)),X1)
    | ~ r1_orders_2(esk6_0,X2,esk2_2(esk6_0,k3_tarski(esk7_0)))
    | ~ r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( r1_orders_2(esk6_0,esk1_2(esk6_0,k3_tarski(esk7_0)),esk2_2(esk6_0,k3_tarski(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_15]),c_0_13])])).

cnf(c_0_40,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,esk3_3(X2,k3_tarski(X2),X3))
    | ~ r2_hidden(X3,k3_tarski(X2)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk2_2(esk6_0,k3_tarski(esk7_0)),X1)
    | ~ r2_hidden(esk1_2(esk6_0,k3_tarski(esk7_0)),X1)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,esk3_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k3_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_44,plain,
    ( r2_hidden(esk1_2(X1,k5_setfam_1(u1_struct_0(X1),X2)),k5_setfam_1(u1_struct_0(X1),X2))
    | v13_waybel_0(k5_setfam_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_14])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk2_2(esk6_0,k3_tarski(esk7_0)),k3_tarski(X1))
    | ~ r2_hidden(esk1_2(esk6_0,k3_tarski(esk7_0)),esk3_3(X1,k3_tarski(X1),X2))
    | ~ r2_hidden(esk3_3(X1,k3_tarski(X1),X2),esk7_0)
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,esk3_3(X2,k3_tarski(X2),X1))
    | ~ r2_hidden(X1,k3_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,k5_setfam_1(u1_struct_0(esk6_0),esk7_0)),k5_setfam_1(u1_struct_0(esk6_0),esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_13]),c_0_26])]),c_0_22])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk2_2(esk6_0,k3_tarski(esk7_0)),k3_tarski(X1))
    | ~ r2_hidden(esk3_3(X1,k3_tarski(X1),esk1_2(esk6_0,k3_tarski(esk7_0))),esk7_0)
    | ~ r2_hidden(esk1_2(esk6_0,k3_tarski(esk7_0)),k3_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,k3_tarski(esk7_0)),k3_tarski(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_15]),c_0_13])])).

cnf(c_0_50,plain,
    ( v13_waybel_0(X2,X1)
    | ~ r2_hidden(esk2_2(X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk2_2(esk6_0,k3_tarski(esk7_0)),k3_tarski(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_37]),c_0_49])])).

cnf(c_0_52,negated_conjecture,
    ( ~ m1_subset_1(k3_tarski(esk7_0),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_26])]),c_0_29])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_21]),c_0_13])]),
    [proof]).

%------------------------------------------------------------------------------
