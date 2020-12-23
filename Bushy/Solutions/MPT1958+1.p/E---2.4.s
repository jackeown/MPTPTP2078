%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : waybel_7__t5_waybel_7.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:07 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 492 expanded)
%              Number of clauses        :   46 ( 187 expanded)
%              Number of leaves         :    9 ( 125 expanded)
%              Depth                    :   15
%              Number of atoms          :  226 (2168 expanded)
%              Number of equality atoms :   29 ( 344 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ( v7_struct_0(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => X2 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t5_waybel_7.p',d10_struct_0)).

fof(dt_k3_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t5_waybel_7.p',dt_k3_yellow_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t5_waybel_7.p',dt_l1_orders_2)).

fof(t5_waybel_7,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v3_yellow_0(X1)
        & l1_orders_2(X1) )
     => ( v7_struct_0(X1)
      <=> k4_yellow_0(X1) = k3_yellow_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t5_waybel_7.p',t5_waybel_7)).

fof(dt_k4_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(k4_yellow_0(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t5_waybel_7.p',dt_k4_yellow_0)).

fof(t25_orders_2,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ( r1_orders_2(X1,X2,X3)
                  & r1_orders_2(X1,X3,X2) )
               => X2 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t5_waybel_7.p',t25_orders_2)).

fof(t45_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v2_yellow_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r1_orders_2(X1,X2,k4_yellow_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t5_waybel_7.p',t45_yellow_0)).

fof(cc4_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v3_yellow_0(X1)
       => ( v1_yellow_0(X1)
          & v2_yellow_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t5_waybel_7.p',cc4_yellow_0)).

fof(t44_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v1_yellow_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r1_orders_2(X1,k3_yellow_0(X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t5_waybel_7.p',t44_yellow_0)).

fof(c_0_9,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v7_struct_0(X7)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | X8 = X9
        | ~ l1_struct_0(X7) )
      & ( m1_subset_1(esk2_1(X7),u1_struct_0(X7))
        | v7_struct_0(X7)
        | ~ l1_struct_0(X7) )
      & ( m1_subset_1(esk3_1(X7),u1_struct_0(X7))
        | v7_struct_0(X7)
        | ~ l1_struct_0(X7) )
      & ( esk2_1(X7) != esk3_1(X7)
        | v7_struct_0(X7)
        | ~ l1_struct_0(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_struct_0])])])])])).

fof(c_0_10,plain,(
    ! [X16] :
      ( ~ l1_orders_2(X16)
      | m1_subset_1(k3_yellow_0(X16),u1_struct_0(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_yellow_0])])).

fof(c_0_11,plain,(
    ! [X18] :
      ( ~ l1_orders_2(X18)
      | l1_struct_0(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v5_orders_2(X1)
          & v3_yellow_0(X1)
          & l1_orders_2(X1) )
       => ( v7_struct_0(X1)
        <=> k4_yellow_0(X1) = k3_yellow_0(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t5_waybel_7])).

cnf(c_0_13,plain,
    ( X2 = X3
    | ~ v7_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X17] :
      ( ~ l1_orders_2(X17)
      | m1_subset_1(k4_yellow_0(X17),u1_struct_0(X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_yellow_0])])).

fof(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v5_orders_2(esk1_0)
    & v3_yellow_0(esk1_0)
    & l1_orders_2(esk1_0)
    & ( ~ v7_struct_0(esk1_0)
      | k4_yellow_0(esk1_0) != k3_yellow_0(esk1_0) )
    & ( v7_struct_0(esk1_0)
      | k4_yellow_0(esk1_0) = k3_yellow_0(esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

cnf(c_0_18,plain,
    ( X1 = k3_yellow_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v7_struct_0(X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])).

cnf(c_0_19,plain,
    ( m1_subset_1(k4_yellow_0(X1),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( v7_struct_0(esk1_0)
    | k4_yellow_0(esk1_0) = k3_yellow_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( ~ v7_struct_0(esk1_0)
    | k4_yellow_0(esk1_0) != k3_yellow_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k4_yellow_0(X1) = k3_yellow_0(X1)
    | ~ v7_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_24,plain,(
    ! [X25,X26,X27] :
      ( ~ v5_orders_2(X25)
      | ~ l1_orders_2(X25)
      | ~ m1_subset_1(X26,u1_struct_0(X25))
      | ~ m1_subset_1(X27,u1_struct_0(X25))
      | ~ r1_orders_2(X25,X26,X27)
      | ~ r1_orders_2(X25,X27,X26)
      | X26 = X27 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_orders_2])])])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(k3_yellow_0(esk1_0),u1_struct_0(esk1_0))
    | v7_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_26,negated_conjecture,
    ( ~ v7_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_21])])).

fof(c_0_27,plain,(
    ! [X32,X33] :
      ( v2_struct_0(X32)
      | ~ v5_orders_2(X32)
      | ~ v2_yellow_0(X32)
      | ~ l1_orders_2(X32)
      | ~ m1_subset_1(X33,u1_struct_0(X32))
      | r1_orders_2(X32,X33,k4_yellow_0(X32)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t45_yellow_0])])])])).

cnf(c_0_28,plain,
    ( X2 = X3
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(k3_yellow_0(esk1_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_31,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,X2,k4_yellow_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_yellow_0(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( m1_subset_1(esk3_1(X1),u1_struct_0(X1))
    | v7_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_33,negated_conjecture,
    ( X1 = k3_yellow_0(esk1_0)
    | ~ r1_orders_2(esk1_0,k3_yellow_0(esk1_0),X1)
    | ~ r1_orders_2(esk1_0,X1,k3_yellow_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_21]),c_0_30])])).

cnf(c_0_34,plain,
    ( r1_orders_2(X1,esk3_1(X1),k4_yellow_0(X1))
    | v7_struct_0(X1)
    | v2_struct_0(X1)
    | ~ v2_yellow_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_15])).

cnf(c_0_35,negated_conjecture,
    ( k4_yellow_0(esk1_0) = k3_yellow_0(esk1_0) ),
    inference(sr,[status(thm)],[c_0_20,c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_37,plain,(
    ! [X39] :
      ( ( v1_yellow_0(X39)
        | ~ v3_yellow_0(X39)
        | ~ l1_orders_2(X39) )
      & ( v2_yellow_0(X39)
        | ~ v3_yellow_0(X39)
        | ~ l1_orders_2(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_yellow_0])])])).

cnf(c_0_38,plain,
    ( m1_subset_1(esk2_1(X1),u1_struct_0(X1))
    | v7_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_39,negated_conjecture,
    ( esk3_1(esk1_0) = k3_yellow_0(esk1_0)
    | ~ r1_orders_2(esk1_0,k3_yellow_0(esk1_0),esk3_1(esk1_0))
    | ~ r1_orders_2(esk1_0,esk3_1(esk1_0),k3_yellow_0(esk1_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_32]),c_0_26])).

cnf(c_0_40,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_1(esk1_0),k3_yellow_0(esk1_0))
    | ~ v2_yellow_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_21]),c_0_30])]),c_0_26]),c_0_36])).

cnf(c_0_41,plain,
    ( v2_yellow_0(X1)
    | ~ v3_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( v3_yellow_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_43,plain,(
    ! [X30,X31] :
      ( v2_struct_0(X30)
      | ~ v5_orders_2(X30)
      | ~ v1_yellow_0(X30)
      | ~ l1_orders_2(X30)
      | ~ m1_subset_1(X31,u1_struct_0(X30))
      | r1_orders_2(X30,k3_yellow_0(X30),X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t44_yellow_0])])])])).

cnf(c_0_44,plain,
    ( r1_orders_2(X1,esk2_1(X1),k4_yellow_0(X1))
    | v7_struct_0(X1)
    | v2_struct_0(X1)
    | ~ v2_yellow_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_38]),c_0_15])).

cnf(c_0_45,negated_conjecture,
    ( esk3_1(esk1_0) = k3_yellow_0(esk1_0)
    | ~ r1_orders_2(esk1_0,k3_yellow_0(esk1_0),esk3_1(esk1_0))
    | ~ r1_orders_2(esk1_0,esk3_1(esk1_0),k3_yellow_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_15]),c_0_21])])).

cnf(c_0_46,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_1(esk1_0),k3_yellow_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_21]),c_0_42])])).

cnf(c_0_47,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,k3_yellow_0(X1),X2)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( esk2_1(esk1_0) = k3_yellow_0(esk1_0)
    | ~ r1_orders_2(esk1_0,k3_yellow_0(esk1_0),esk2_1(esk1_0))
    | ~ r1_orders_2(esk1_0,esk2_1(esk1_0),k3_yellow_0(esk1_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_38]),c_0_26])).

cnf(c_0_49,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_1(esk1_0),k3_yellow_0(esk1_0))
    | ~ v2_yellow_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_35]),c_0_21]),c_0_30])]),c_0_26]),c_0_36])).

cnf(c_0_50,negated_conjecture,
    ( esk3_1(esk1_0) = k3_yellow_0(esk1_0)
    | ~ r1_orders_2(esk1_0,k3_yellow_0(esk1_0),esk3_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46])])).

cnf(c_0_51,plain,
    ( r1_orders_2(X1,k3_yellow_0(X1),esk3_1(X1))
    | v7_struct_0(X1)
    | v2_struct_0(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_32]),c_0_15])).

cnf(c_0_52,negated_conjecture,
    ( esk2_1(esk1_0) = k3_yellow_0(esk1_0)
    | ~ r1_orders_2(esk1_0,k3_yellow_0(esk1_0),esk2_1(esk1_0))
    | ~ r1_orders_2(esk1_0,esk2_1(esk1_0),k3_yellow_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_15]),c_0_21])])).

cnf(c_0_53,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_1(esk1_0),k3_yellow_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_41]),c_0_21]),c_0_42])])).

cnf(c_0_54,negated_conjecture,
    ( esk3_1(esk1_0) = k3_yellow_0(esk1_0)
    | ~ v1_yellow_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_21]),c_0_30])]),c_0_26]),c_0_36])).

cnf(c_0_55,plain,
    ( v1_yellow_0(X1)
    | ~ v3_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_56,negated_conjecture,
    ( esk2_1(esk1_0) = k3_yellow_0(esk1_0)
    | ~ r1_orders_2(esk1_0,k3_yellow_0(esk1_0),esk2_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53])])).

cnf(c_0_57,plain,
    ( r1_orders_2(X1,k3_yellow_0(X1),esk2_1(X1))
    | v7_struct_0(X1)
    | v2_struct_0(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_38]),c_0_15])).

cnf(c_0_58,plain,
    ( v7_struct_0(X1)
    | esk2_1(X1) != esk3_1(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_59,negated_conjecture,
    ( esk3_1(esk1_0) = k3_yellow_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_21]),c_0_42])])).

cnf(c_0_60,negated_conjecture,
    ( esk2_1(esk1_0) = k3_yellow_0(esk1_0)
    | ~ v1_yellow_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_21]),c_0_30])]),c_0_26]),c_0_36])).

cnf(c_0_61,negated_conjecture,
    ( esk2_1(esk1_0) != k3_yellow_0(esk1_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_26])).

cnf(c_0_62,negated_conjecture,
    ( esk2_1(esk1_0) = k3_yellow_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_55]),c_0_21]),c_0_42])])).

cnf(c_0_63,negated_conjecture,
    ( ~ l1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62])])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_15]),c_0_21])]),
    [proof]).
%------------------------------------------------------------------------------
