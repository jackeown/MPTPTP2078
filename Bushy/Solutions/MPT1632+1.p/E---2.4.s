%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : waybel_0__t12_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:44 EDT 2019

% Result     : Theorem 227.37s
% Output     : CNFRefutation 227.37s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 819 expanded)
%              Number of clauses        :   31 ( 248 expanded)
%              Number of leaves         :    3 ( 203 expanded)
%              Depth                    :   13
%              Number of atoms          :  238 (9307 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   40 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ( v11_waybel_0(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X2))
               => ? [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X2))
                    & ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X2))
                       => ( r1_orders_2(X2,X4,X5)
                         => r1_orders_2(X1,k2_waybel_0(X1,X2,X5),k2_waybel_0(X1,X2,X3)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t12_waybel_0.p',t12_waybel_0)).

fof(s1_waybel_0__e1_35_1__waybel_0,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1)
        & ~ v2_struct_0(X2)
        & l1_waybel_0(X2,X1)
        & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( r1_waybel_0(X1,X2,a_3_1_waybel_0(X1,X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,u1_struct_0(X2))
            & ! [X5] :
                ( m1_subset_1(X5,u1_struct_0(X2))
               => ( r1_orders_2(X2,X4,X5)
                 => r1_orders_2(X1,k2_waybel_0(X1,X2,X5),k2_waybel_0(X1,X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t12_waybel_0.p',s1_waybel_0__e1_35_1__waybel_0)).

fof(d14_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ( v11_waybel_0(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X2))
               => r1_waybel_0(X1,X2,a_3_1_waybel_0(X1,X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t12_waybel_0.p',d14_waybel_0)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & l1_waybel_0(X2,X1) )
           => ( v11_waybel_0(X2,X1)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X2))
                 => ? [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X2))
                      & ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ( r1_orders_2(X2,X4,X5)
                           => r1_orders_2(X1,k2_waybel_0(X1,X2,X5),k2_waybel_0(X1,X2,X3)) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t12_waybel_0])).

fof(c_0_4,negated_conjecture,(
    ! [X9,X11,X13] :
      ( ~ v2_struct_0(esk1_0)
      & l1_orders_2(esk1_0)
      & ~ v2_struct_0(esk2_0)
      & l1_waybel_0(esk2_0,esk1_0)
      & ( m1_subset_1(esk3_0,u1_struct_0(esk2_0))
        | ~ v11_waybel_0(esk2_0,esk1_0) )
      & ( m1_subset_1(esk4_1(X9),u1_struct_0(esk2_0))
        | ~ m1_subset_1(X9,u1_struct_0(esk2_0))
        | ~ v11_waybel_0(esk2_0,esk1_0) )
      & ( r1_orders_2(esk2_0,X9,esk4_1(X9))
        | ~ m1_subset_1(X9,u1_struct_0(esk2_0))
        | ~ v11_waybel_0(esk2_0,esk1_0) )
      & ( ~ r1_orders_2(esk1_0,k2_waybel_0(esk1_0,esk2_0,esk4_1(X9)),k2_waybel_0(esk1_0,esk2_0,esk3_0))
        | ~ m1_subset_1(X9,u1_struct_0(esk2_0))
        | ~ v11_waybel_0(esk2_0,esk1_0) )
      & ( m1_subset_1(esk5_1(X11),u1_struct_0(esk2_0))
        | ~ m1_subset_1(X11,u1_struct_0(esk2_0))
        | v11_waybel_0(esk2_0,esk1_0) )
      & ( ~ m1_subset_1(X13,u1_struct_0(esk2_0))
        | ~ r1_orders_2(esk2_0,esk5_1(X11),X13)
        | r1_orders_2(esk1_0,k2_waybel_0(esk1_0,esk2_0,X13),k2_waybel_0(esk1_0,esk2_0,X11))
        | ~ m1_subset_1(X11,u1_struct_0(esk2_0))
        | v11_waybel_0(esk2_0,esk1_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])])])).

fof(c_0_5,plain,(
    ! [X50,X51,X52,X54,X55] :
      ( ( m1_subset_1(esk13_3(X50,X51,X52),u1_struct_0(X51))
        | ~ r1_waybel_0(X50,X51,a_3_1_waybel_0(X50,X51,X52))
        | v2_struct_0(X50)
        | ~ l1_orders_2(X50)
        | v2_struct_0(X51)
        | ~ l1_waybel_0(X51,X50)
        | ~ m1_subset_1(X52,u1_struct_0(X51)) )
      & ( ~ m1_subset_1(X54,u1_struct_0(X51))
        | ~ r1_orders_2(X51,esk13_3(X50,X51,X52),X54)
        | r1_orders_2(X50,k2_waybel_0(X50,X51,X54),k2_waybel_0(X50,X51,X52))
        | ~ r1_waybel_0(X50,X51,a_3_1_waybel_0(X50,X51,X52))
        | v2_struct_0(X50)
        | ~ l1_orders_2(X50)
        | v2_struct_0(X51)
        | ~ l1_waybel_0(X51,X50)
        | ~ m1_subset_1(X52,u1_struct_0(X51)) )
      & ( m1_subset_1(esk14_4(X50,X51,X52,X55),u1_struct_0(X51))
        | ~ m1_subset_1(X55,u1_struct_0(X51))
        | r1_waybel_0(X50,X51,a_3_1_waybel_0(X50,X51,X52))
        | v2_struct_0(X50)
        | ~ l1_orders_2(X50)
        | v2_struct_0(X51)
        | ~ l1_waybel_0(X51,X50)
        | ~ m1_subset_1(X52,u1_struct_0(X51)) )
      & ( r1_orders_2(X51,X55,esk14_4(X50,X51,X52,X55))
        | ~ m1_subset_1(X55,u1_struct_0(X51))
        | r1_waybel_0(X50,X51,a_3_1_waybel_0(X50,X51,X52))
        | v2_struct_0(X50)
        | ~ l1_orders_2(X50)
        | v2_struct_0(X51)
        | ~ l1_waybel_0(X51,X50)
        | ~ m1_subset_1(X52,u1_struct_0(X51)) )
      & ( ~ r1_orders_2(X50,k2_waybel_0(X50,X51,esk14_4(X50,X51,X52,X55)),k2_waybel_0(X50,X51,X52))
        | ~ m1_subset_1(X55,u1_struct_0(X51))
        | r1_waybel_0(X50,X51,a_3_1_waybel_0(X50,X51,X52))
        | v2_struct_0(X50)
        | ~ l1_orders_2(X50)
        | v2_struct_0(X51)
        | ~ l1_waybel_0(X51,X50)
        | ~ m1_subset_1(X52,u1_struct_0(X51)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[s1_waybel_0__e1_35_1__waybel_0])])])])])])).

cnf(c_0_6,negated_conjecture,
    ( r1_orders_2(esk1_0,k2_waybel_0(esk1_0,esk2_0,X1),k2_waybel_0(esk1_0,esk2_0,X2))
    | v11_waybel_0(esk2_0,esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r1_orders_2(esk2_0,esk5_1(X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( r1_orders_2(X1,X2,esk14_4(X3,X1,X4,X2))
    | r1_waybel_0(X3,X1,a_3_1_waybel_0(X3,X1,X4))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X3)
    | ~ l1_waybel_0(X1,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,negated_conjecture,
    ( m1_subset_1(esk5_1(X1),u1_struct_0(esk2_0))
    | v11_waybel_0(esk2_0,esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_10,plain,
    ( r1_waybel_0(X1,X2,a_3_1_waybel_0(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_orders_2(X1,k2_waybel_0(X1,X2,esk14_4(X1,X2,X3,X4)),k2_waybel_0(X1,X2,X3))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,negated_conjecture,
    ( r1_waybel_0(X1,esk2_0,a_3_1_waybel_0(X1,esk2_0,X2))
    | r1_orders_2(esk1_0,k2_waybel_0(esk1_0,esk2_0,esk14_4(X1,esk2_0,X2,esk5_1(X3))),k2_waybel_0(esk1_0,esk2_0,X3))
    | v11_waybel_0(esk2_0,esk1_0)
    | v2_struct_0(X1)
    | ~ m1_subset_1(esk14_4(X1,esk2_0,X2,esk5_1(X3)),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ l1_waybel_0(esk2_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_7]),c_0_8]),c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( l1_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_15,plain,(
    ! [X16,X17,X18] :
      ( ( ~ v11_waybel_0(X17,X16)
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | r1_waybel_0(X16,X17,a_3_1_waybel_0(X16,X17,X18))
        | v2_struct_0(X17)
        | ~ l1_waybel_0(X17,X16)
        | v2_struct_0(X16)
        | ~ l1_orders_2(X16) )
      & ( m1_subset_1(esk6_2(X16,X17),u1_struct_0(X17))
        | v11_waybel_0(X17,X16)
        | v2_struct_0(X17)
        | ~ l1_waybel_0(X17,X16)
        | v2_struct_0(X16)
        | ~ l1_orders_2(X16) )
      & ( ~ r1_waybel_0(X16,X17,a_3_1_waybel_0(X16,X17,esk6_2(X16,X17)))
        | v11_waybel_0(X17,X16)
        | v2_struct_0(X17)
        | ~ l1_waybel_0(X17,X16)
        | v2_struct_0(X16)
        | ~ l1_orders_2(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d14_waybel_0])])])])])])).

cnf(c_0_16,negated_conjecture,
    ( r1_waybel_0(esk1_0,esk2_0,a_3_1_waybel_0(esk1_0,esk2_0,X1))
    | v11_waybel_0(esk2_0,esk1_0)
    | ~ m1_subset_1(esk14_4(esk1_0,esk2_0,X1,esk5_1(X1)),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),c_0_13])]),c_0_8]),c_0_14]),c_0_9])).

cnf(c_0_17,plain,
    ( m1_subset_1(esk14_4(X1,X2,X3,X4),u1_struct_0(X2))
    | r1_waybel_0(X1,X2,a_3_1_waybel_0(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_18,plain,
    ( v11_waybel_0(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_waybel_0(X1,X2,a_3_1_waybel_0(X1,X2,esk6_2(X1,X2)))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( r1_waybel_0(esk1_0,esk2_0,a_3_1_waybel_0(esk1_0,esk2_0,X1))
    | v11_waybel_0(esk2_0,esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_12]),c_0_13])]),c_0_8]),c_0_14]),c_0_9])).

cnf(c_0_20,negated_conjecture,
    ( v11_waybel_0(esk2_0,esk1_0)
    | ~ m1_subset_1(esk6_2(esk1_0,esk2_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_12]),c_0_13])]),c_0_8]),c_0_14])).

cnf(c_0_21,plain,
    ( m1_subset_1(esk6_2(X1,X2),u1_struct_0(X2))
    | v11_waybel_0(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_1(X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ v11_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_23,negated_conjecture,
    ( v11_waybel_0(esk2_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_12]),c_0_13])]),c_0_8]),c_0_14])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk4_1(X1),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ v11_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_25,negated_conjecture,
    ( ~ r1_orders_2(esk1_0,k2_waybel_0(esk1_0,esk2_0,esk4_1(X1)),k2_waybel_0(esk1_0,esk2_0,esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ v11_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_26,plain,
    ( r1_orders_2(X3,k2_waybel_0(X3,X2,X1),k2_waybel_0(X3,X2,X4))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_orders_2(X2,esk13_3(X3,X2,X4),X1)
    | ~ r1_waybel_0(X3,X2,a_3_1_waybel_0(X3,X2,X4))
    | ~ l1_orders_2(X3)
    | ~ l1_waybel_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_27,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_1(X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23])])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk4_1(X1),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_23])])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    | ~ v11_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_30,negated_conjecture,
    ( ~ r1_orders_2(esk1_0,k2_waybel_0(esk1_0,esk2_0,esk4_1(X1)),k2_waybel_0(esk1_0,esk2_0,esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_23])])).

cnf(c_0_31,negated_conjecture,
    ( r1_orders_2(X1,k2_waybel_0(X1,esk2_0,esk4_1(esk13_3(X1,esk2_0,X2))),k2_waybel_0(X1,esk2_0,X2))
    | v2_struct_0(X1)
    | ~ r1_waybel_0(X1,esk2_0,a_3_1_waybel_0(X1,esk2_0,X2))
    | ~ m1_subset_1(esk13_3(X1,esk2_0,X2),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ l1_waybel_0(esk2_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_8]),c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_23])])).

cnf(c_0_33,negated_conjecture,
    ( ~ r1_waybel_0(esk1_0,esk2_0,a_3_1_waybel_0(esk1_0,esk2_0,esk3_0))
    | ~ m1_subset_1(esk13_3(esk1_0,esk2_0,esk3_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_34,plain,
    ( m1_subset_1(esk13_3(X1,X2,X3),u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_waybel_0(X1,X2,a_3_1_waybel_0(X1,X2,X3))
    | ~ l1_orders_2(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_35,negated_conjecture,
    ( ~ r1_waybel_0(esk1_0,esk2_0,a_3_1_waybel_0(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_32]),c_0_12]),c_0_13])]),c_0_8]),c_0_14])).

cnf(c_0_36,plain,
    ( r1_waybel_0(X2,X1,a_3_1_waybel_0(X2,X1,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v11_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_waybel_0(X1,X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_32]),c_0_23]),c_0_12]),c_0_13])]),c_0_14]),c_0_8]),
    [proof]).
%------------------------------------------------------------------------------
