%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1632+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:29 EST 2020

% Result     : Theorem 49.70s
% Output     : CNFRefutation 49.70s
% Verified   : 
% Statistics : Number of formulae       :   89 (397801 expanded)
%              Number of clauses        :   82 (127050 expanded)
%              Number of leaves         :    3 (95320 expanded)
%              Depth                    :   39
%              Number of atoms          :  405 (4222350 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   40 (   3 average)
%              Maximal term depth       :    5 (   2 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_waybel_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_waybel_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s1_waybel_0__e1_35_1__waybel_0)).

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

fof(c_0_4,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v11_waybel_0(X7,X6)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | r1_waybel_0(X6,X7,a_3_1_waybel_0(X6,X7,X8))
        | v2_struct_0(X7)
        | ~ l1_waybel_0(X7,X6)
        | v2_struct_0(X6)
        | ~ l1_orders_2(X6) )
      & ( m1_subset_1(esk1_2(X6,X7),u1_struct_0(X7))
        | v11_waybel_0(X7,X6)
        | v2_struct_0(X7)
        | ~ l1_waybel_0(X7,X6)
        | v2_struct_0(X6)
        | ~ l1_orders_2(X6) )
      & ( ~ r1_waybel_0(X6,X7,a_3_1_waybel_0(X6,X7,esk1_2(X6,X7)))
        | v11_waybel_0(X7,X6)
        | v2_struct_0(X7)
        | ~ l1_waybel_0(X7,X6)
        | v2_struct_0(X6)
        | ~ l1_orders_2(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d14_waybel_0])])])])])])).

fof(c_0_5,negated_conjecture,(
    ! [X20,X22,X24] :
      ( ~ v2_struct_0(esk4_0)
      & l1_orders_2(esk4_0)
      & ~ v2_struct_0(esk5_0)
      & l1_waybel_0(esk5_0,esk4_0)
      & ( m1_subset_1(esk6_0,u1_struct_0(esk5_0))
        | ~ v11_waybel_0(esk5_0,esk4_0) )
      & ( m1_subset_1(esk7_1(X20),u1_struct_0(esk5_0))
        | ~ m1_subset_1(X20,u1_struct_0(esk5_0))
        | ~ v11_waybel_0(esk5_0,esk4_0) )
      & ( r1_orders_2(esk5_0,X20,esk7_1(X20))
        | ~ m1_subset_1(X20,u1_struct_0(esk5_0))
        | ~ v11_waybel_0(esk5_0,esk4_0) )
      & ( ~ r1_orders_2(esk4_0,k2_waybel_0(esk4_0,esk5_0,esk7_1(X20)),k2_waybel_0(esk4_0,esk5_0,esk6_0))
        | ~ m1_subset_1(X20,u1_struct_0(esk5_0))
        | ~ v11_waybel_0(esk5_0,esk4_0) )
      & ( m1_subset_1(esk8_1(X22),u1_struct_0(esk5_0))
        | ~ m1_subset_1(X22,u1_struct_0(esk5_0))
        | v11_waybel_0(esk5_0,esk4_0) )
      & ( ~ m1_subset_1(X24,u1_struct_0(esk5_0))
        | ~ r1_orders_2(esk5_0,esk8_1(X22),X24)
        | r1_orders_2(esk4_0,k2_waybel_0(esk4_0,esk5_0,X24),k2_waybel_0(esk4_0,esk5_0,X22))
        | ~ m1_subset_1(X22,u1_struct_0(esk5_0))
        | v11_waybel_0(esk5_0,esk4_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])])])).

cnf(c_0_6,plain,
    ( m1_subset_1(esk1_2(X1,X2),u1_struct_0(X2))
    | v11_waybel_0(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( l1_waybel_0(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0))
    | ~ v11_waybel_0(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk1_2(esk4_0,esk5_0),u1_struct_0(esk5_0))
    | v11_waybel_0(esk5_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_7]),c_0_8])]),c_0_9]),c_0_10])).

fof(c_0_13,plain,(
    ! [X10,X11,X12,X14,X15] :
      ( ( m1_subset_1(esk2_3(X10,X11,X12),u1_struct_0(X11))
        | ~ r1_waybel_0(X10,X11,a_3_1_waybel_0(X10,X11,X12))
        | v2_struct_0(X10)
        | ~ l1_orders_2(X10)
        | v2_struct_0(X11)
        | ~ l1_waybel_0(X11,X10)
        | ~ m1_subset_1(X12,u1_struct_0(X11)) )
      & ( ~ m1_subset_1(X14,u1_struct_0(X11))
        | ~ r1_orders_2(X11,esk2_3(X10,X11,X12),X14)
        | r1_orders_2(X10,k2_waybel_0(X10,X11,X14),k2_waybel_0(X10,X11,X12))
        | ~ r1_waybel_0(X10,X11,a_3_1_waybel_0(X10,X11,X12))
        | v2_struct_0(X10)
        | ~ l1_orders_2(X10)
        | v2_struct_0(X11)
        | ~ l1_waybel_0(X11,X10)
        | ~ m1_subset_1(X12,u1_struct_0(X11)) )
      & ( m1_subset_1(esk3_4(X10,X11,X12,X15),u1_struct_0(X11))
        | ~ m1_subset_1(X15,u1_struct_0(X11))
        | r1_waybel_0(X10,X11,a_3_1_waybel_0(X10,X11,X12))
        | v2_struct_0(X10)
        | ~ l1_orders_2(X10)
        | v2_struct_0(X11)
        | ~ l1_waybel_0(X11,X10)
        | ~ m1_subset_1(X12,u1_struct_0(X11)) )
      & ( r1_orders_2(X11,X15,esk3_4(X10,X11,X12,X15))
        | ~ m1_subset_1(X15,u1_struct_0(X11))
        | r1_waybel_0(X10,X11,a_3_1_waybel_0(X10,X11,X12))
        | v2_struct_0(X10)
        | ~ l1_orders_2(X10)
        | v2_struct_0(X11)
        | ~ l1_waybel_0(X11,X10)
        | ~ m1_subset_1(X12,u1_struct_0(X11)) )
      & ( ~ r1_orders_2(X10,k2_waybel_0(X10,X11,esk3_4(X10,X11,X12,X15)),k2_waybel_0(X10,X11,X12))
        | ~ m1_subset_1(X15,u1_struct_0(X11))
        | r1_waybel_0(X10,X11,a_3_1_waybel_0(X10,X11,X12))
        | v2_struct_0(X10)
        | ~ l1_orders_2(X10)
        | v2_struct_0(X11)
        | ~ l1_waybel_0(X11,X10)
        | ~ m1_subset_1(X12,u1_struct_0(X11)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[s1_waybel_0__e1_35_1__waybel_0])])])])])])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk8_1(X1),u1_struct_0(esk5_0))
    | v11_waybel_0(esk5_0,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk1_2(esk4_0,esk5_0),u1_struct_0(esk5_0))
    | m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,plain,
    ( r1_orders_2(X1,X2,esk3_4(X3,X1,X4,X2))
    | r1_waybel_0(X3,X1,a_3_1_waybel_0(X3,X1,X4))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X3)
    | ~ l1_waybel_0(X1,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( m1_subset_1(esk3_4(X1,X2,X3,X4),u1_struct_0(X2))
    | r1_waybel_0(X1,X2,a_3_1_waybel_0(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk8_1(esk1_2(esk4_0,esk5_0)),u1_struct_0(esk5_0))
    | m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( r1_orders_2(esk5_0,X1,esk3_4(X2,esk5_0,esk1_2(esk4_0,esk5_0),X1))
    | r1_waybel_0(X2,esk5_0,a_3_1_waybel_0(X2,esk5_0,esk1_2(esk4_0,esk5_0)))
    | m1_subset_1(esk6_0,u1_struct_0(esk5_0))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ l1_waybel_0(esk5_0,X2)
    | ~ l1_orders_2(X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_15]),c_0_9])).

cnf(c_0_20,negated_conjecture,
    ( r1_waybel_0(X1,esk5_0,a_3_1_waybel_0(X1,esk5_0,X2))
    | m1_subset_1(esk3_4(X1,esk5_0,X2,esk8_1(esk1_2(esk4_0,esk5_0))),u1_struct_0(esk5_0))
    | m1_subset_1(esk6_0,u1_struct_0(esk5_0))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ l1_waybel_0(esk5_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_9])).

cnf(c_0_21,negated_conjecture,
    ( r1_orders_2(esk5_0,esk8_1(esk1_2(esk4_0,esk5_0)),esk3_4(X1,esk5_0,esk1_2(esk4_0,esk5_0),esk8_1(esk1_2(esk4_0,esk5_0))))
    | r1_waybel_0(X1,esk5_0,a_3_1_waybel_0(X1,esk5_0,esk1_2(esk4_0,esk5_0)))
    | m1_subset_1(esk6_0,u1_struct_0(esk5_0))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(esk5_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( r1_waybel_0(X1,esk5_0,a_3_1_waybel_0(X1,esk5_0,esk1_2(esk4_0,esk5_0)))
    | m1_subset_1(esk3_4(X1,esk5_0,esk1_2(esk4_0,esk5_0),esk8_1(esk1_2(esk4_0,esk5_0))),u1_struct_0(esk5_0))
    | m1_subset_1(esk6_0,u1_struct_0(esk5_0))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(esk5_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_15])).

cnf(c_0_23,plain,
    ( v11_waybel_0(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_waybel_0(X1,X2,a_3_1_waybel_0(X1,X2,esk1_2(X1,X2)))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_24,negated_conjecture,
    ( r1_orders_2(esk5_0,esk8_1(esk1_2(esk4_0,esk5_0)),esk3_4(esk4_0,esk5_0,esk1_2(esk4_0,esk5_0),esk8_1(esk1_2(esk4_0,esk5_0))))
    | r1_waybel_0(esk4_0,esk5_0,a_3_1_waybel_0(esk4_0,esk5_0,esk1_2(esk4_0,esk5_0)))
    | m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_7]),c_0_8])]),c_0_10])).

cnf(c_0_25,negated_conjecture,
    ( r1_waybel_0(esk4_0,esk5_0,a_3_1_waybel_0(esk4_0,esk5_0,esk1_2(esk4_0,esk5_0)))
    | m1_subset_1(esk3_4(esk4_0,esk5_0,esk1_2(esk4_0,esk5_0),esk8_1(esk1_2(esk4_0,esk5_0))),u1_struct_0(esk5_0))
    | m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_7]),c_0_8])]),c_0_10])).

cnf(c_0_26,negated_conjecture,
    ( r1_orders_2(esk4_0,k2_waybel_0(esk4_0,esk5_0,X1),k2_waybel_0(esk4_0,esk5_0,X2))
    | v11_waybel_0(esk5_0,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r1_orders_2(esk5_0,esk8_1(X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_27,negated_conjecture,
    ( r1_orders_2(esk5_0,esk8_1(esk1_2(esk4_0,esk5_0)),esk3_4(esk4_0,esk5_0,esk1_2(esk4_0,esk5_0),esk8_1(esk1_2(esk4_0,esk5_0))))
    | m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_7]),c_0_8])]),c_0_9]),c_0_10]),c_0_11])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk3_4(esk4_0,esk5_0,esk1_2(esk4_0,esk5_0),esk8_1(esk1_2(esk4_0,esk5_0))),u1_struct_0(esk5_0))
    | m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_25]),c_0_7]),c_0_8])]),c_0_9]),c_0_10]),c_0_11])).

cnf(c_0_29,plain,
    ( r1_waybel_0(X1,X2,a_3_1_waybel_0(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_orders_2(X1,k2_waybel_0(X1,X2,esk3_4(X1,X2,X3,X4)),k2_waybel_0(X1,X2,X3))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_30,negated_conjecture,
    ( r1_orders_2(esk4_0,k2_waybel_0(esk4_0,esk5_0,esk3_4(esk4_0,esk5_0,esk1_2(esk4_0,esk5_0),esk8_1(esk1_2(esk4_0,esk5_0)))),k2_waybel_0(esk4_0,esk5_0,esk1_2(esk4_0,esk5_0)))
    | m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_12]),c_0_28]),c_0_11])).

cnf(c_0_31,negated_conjecture,
    ( r1_waybel_0(esk4_0,esk5_0,a_3_1_waybel_0(esk4_0,esk5_0,esk1_2(esk4_0,esk5_0)))
    | m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_7]),c_0_8])]),c_0_9]),c_0_10]),c_0_15]),c_0_18])).

cnf(c_0_32,plain,
    ( r1_waybel_0(X2,X1,a_3_1_waybel_0(X2,X1,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v11_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_waybel_0(X1,X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_31]),c_0_7]),c_0_8])]),c_0_9]),c_0_10]),c_0_11])).

cnf(c_0_34,plain,
    ( r1_orders_2(X3,k2_waybel_0(X3,X2,X1),k2_waybel_0(X3,X2,X4))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_orders_2(X2,esk2_3(X3,X2,X4),X1)
    | ~ r1_waybel_0(X3,X2,a_3_1_waybel_0(X3,X2,X4))
    | ~ l1_orders_2(X3)
    | ~ l1_waybel_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_35,negated_conjecture,
    ( r1_orders_2(esk5_0,X1,esk7_1(X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ v11_waybel_0(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk7_1(X1),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ v11_waybel_0(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_37,negated_conjecture,
    ( r1_waybel_0(X1,esk5_0,a_3_1_waybel_0(X1,esk5_0,esk6_0))
    | v2_struct_0(X1)
    | ~ v11_waybel_0(esk5_0,X1)
    | ~ l1_waybel_0(esk5_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_9])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk8_1(esk6_0),u1_struct_0(esk5_0))
    | v11_waybel_0(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( r1_orders_2(X1,k2_waybel_0(X1,esk5_0,esk7_1(esk2_3(X1,esk5_0,X2))),k2_waybel_0(X1,esk5_0,X2))
    | v2_struct_0(X1)
    | ~ r1_waybel_0(X1,esk5_0,a_3_1_waybel_0(X1,esk5_0,X2))
    | ~ m1_subset_1(esk2_3(X1,esk5_0,X2),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ v11_waybel_0(esk5_0,esk4_0)
    | ~ l1_waybel_0(esk5_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_9]),c_0_36])).

cnf(c_0_40,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_waybel_0(X1,X2,a_3_1_waybel_0(X1,X2,X3))
    | ~ l1_orders_2(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_41,negated_conjecture,
    ( r1_waybel_0(esk4_0,esk5_0,a_3_1_waybel_0(esk4_0,esk5_0,esk6_0))
    | m1_subset_1(esk8_1(esk6_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_7]),c_0_8])]),c_0_10])).

cnf(c_0_42,negated_conjecture,
    ( ~ r1_orders_2(esk4_0,k2_waybel_0(esk4_0,esk5_0,esk7_1(X1)),k2_waybel_0(esk4_0,esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ v11_waybel_0(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_43,negated_conjecture,
    ( r1_orders_2(X1,k2_waybel_0(X1,esk5_0,esk7_1(esk2_3(X1,esk5_0,X2))),k2_waybel_0(X1,esk5_0,X2))
    | m1_subset_1(esk8_1(esk6_0),u1_struct_0(esk5_0))
    | v2_struct_0(X1)
    | ~ r1_waybel_0(X1,esk5_0,a_3_1_waybel_0(X1,esk5_0,X2))
    | ~ m1_subset_1(esk2_3(X1,esk5_0,X2),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ l1_waybel_0(esk5_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk2_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk5_0))
    | m1_subset_1(esk8_1(esk6_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_33]),c_0_7]),c_0_8])]),c_0_9]),c_0_10])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk8_1(esk6_0),u1_struct_0(esk5_0))
    | ~ r1_orders_2(esk4_0,k2_waybel_0(esk4_0,esk5_0,esk7_1(X1)),k2_waybel_0(esk4_0,esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( r1_orders_2(esk4_0,k2_waybel_0(esk4_0,esk5_0,esk7_1(esk2_3(esk4_0,esk5_0,esk6_0))),k2_waybel_0(esk4_0,esk5_0,esk6_0))
    | m1_subset_1(esk8_1(esk6_0),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_33]),c_0_7]),c_0_8])]),c_0_10]),c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk8_1(esk6_0),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( r1_orders_2(esk5_0,X1,esk3_4(X2,esk5_0,esk6_0,X1))
    | r1_waybel_0(X2,esk5_0,a_3_1_waybel_0(X2,esk5_0,esk6_0))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ l1_waybel_0(esk5_0,X2)
    | ~ l1_orders_2(X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_33]),c_0_9])).

cnf(c_0_49,negated_conjecture,
    ( r1_waybel_0(X1,esk5_0,a_3_1_waybel_0(X1,esk5_0,X2))
    | m1_subset_1(esk3_4(X1,esk5_0,X2,esk8_1(esk6_0)),u1_struct_0(esk5_0))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ l1_waybel_0(esk5_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_47]),c_0_9])).

cnf(c_0_50,negated_conjecture,
    ( r1_orders_2(esk5_0,esk8_1(esk6_0),esk3_4(X1,esk5_0,esk6_0,esk8_1(esk6_0)))
    | r1_waybel_0(X1,esk5_0,a_3_1_waybel_0(X1,esk5_0,esk6_0))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(esk5_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( r1_waybel_0(X1,esk5_0,a_3_1_waybel_0(X1,esk5_0,esk6_0))
    | m1_subset_1(esk3_4(X1,esk5_0,esk6_0,esk8_1(esk6_0)),u1_struct_0(esk5_0))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(esk5_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_33])).

cnf(c_0_52,negated_conjecture,
    ( r1_orders_2(esk5_0,esk8_1(esk6_0),esk3_4(esk4_0,esk5_0,esk6_0,esk8_1(esk6_0)))
    | r1_waybel_0(esk4_0,esk5_0,a_3_1_waybel_0(esk4_0,esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_7]),c_0_8])]),c_0_10])).

cnf(c_0_53,negated_conjecture,
    ( r1_waybel_0(esk4_0,esk5_0,a_3_1_waybel_0(esk4_0,esk5_0,esk6_0))
    | m1_subset_1(esk3_4(esk4_0,esk5_0,esk6_0,esk8_1(esk6_0)),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_7]),c_0_8])]),c_0_10])).

cnf(c_0_54,negated_conjecture,
    ( r1_waybel_0(esk4_0,esk5_0,a_3_1_waybel_0(esk4_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_2(esk4_0,esk5_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_12]),c_0_7]),c_0_8])]),c_0_10])).

cnf(c_0_55,negated_conjecture,
    ( r1_orders_2(esk5_0,esk8_1(esk6_0),esk3_4(esk4_0,esk5_0,esk6_0,esk8_1(esk6_0)))
    | m1_subset_1(esk2_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_52]),c_0_33]),c_0_7]),c_0_8])]),c_0_9]),c_0_10])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk3_4(esk4_0,esk5_0,esk6_0,esk8_1(esk6_0)),u1_struct_0(esk5_0))
    | m1_subset_1(esk2_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_53]),c_0_33]),c_0_7]),c_0_8])]),c_0_9]),c_0_10])).

cnf(c_0_57,negated_conjecture,
    ( r1_orders_2(X1,k2_waybel_0(X1,esk5_0,esk7_1(esk2_3(X1,esk5_0,X2))),k2_waybel_0(X1,esk5_0,X2))
    | m1_subset_1(esk1_2(esk4_0,esk5_0),u1_struct_0(esk5_0))
    | v2_struct_0(X1)
    | ~ r1_waybel_0(X1,esk5_0,a_3_1_waybel_0(X1,esk5_0,X2))
    | ~ m1_subset_1(esk2_3(X1,esk5_0,X2),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ l1_waybel_0(esk5_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_12])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk2_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk5_0))
    | m1_subset_1(esk1_2(esk4_0,esk5_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_54]),c_0_33]),c_0_7]),c_0_8])]),c_0_9]),c_0_10])).

cnf(c_0_59,negated_conjecture,
    ( r1_orders_2(esk4_0,k2_waybel_0(esk4_0,esk5_0,esk3_4(esk4_0,esk5_0,esk6_0,esk8_1(esk6_0))),k2_waybel_0(esk4_0,esk5_0,esk6_0))
    | m1_subset_1(esk2_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk5_0))
    | v11_waybel_0(esk5_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_55]),c_0_33])]),c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(esk1_2(esk4_0,esk5_0),u1_struct_0(esk5_0))
    | ~ r1_orders_2(esk4_0,k2_waybel_0(esk4_0,esk5_0,esk7_1(X1)),k2_waybel_0(esk4_0,esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_12])).

cnf(c_0_61,negated_conjecture,
    ( r1_orders_2(esk4_0,k2_waybel_0(esk4_0,esk5_0,esk7_1(esk2_3(esk4_0,esk5_0,esk6_0))),k2_waybel_0(esk4_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_2(esk4_0,esk5_0),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_33]),c_0_7]),c_0_8])]),c_0_10]),c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( r1_waybel_0(esk4_0,esk5_0,a_3_1_waybel_0(esk4_0,esk5_0,esk6_0))
    | m1_subset_1(esk2_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk5_0))
    | v11_waybel_0(esk5_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_59]),c_0_47]),c_0_33]),c_0_7]),c_0_8])]),c_0_9]),c_0_10])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(esk1_2(esk4_0,esk5_0),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk2_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk5_0))
    | v11_waybel_0(esk5_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_62]),c_0_33]),c_0_7]),c_0_8])]),c_0_9]),c_0_10])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(esk8_1(esk1_2(esk4_0,esk5_0)),u1_struct_0(esk5_0))
    | v11_waybel_0(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( r1_waybel_0(esk4_0,esk5_0,a_3_1_waybel_0(esk4_0,esk5_0,esk6_0))
    | m1_subset_1(esk2_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_64]),c_0_7]),c_0_8])]),c_0_10])).

cnf(c_0_67,negated_conjecture,
    ( r1_orders_2(X1,k2_waybel_0(X1,esk5_0,esk7_1(esk2_3(X1,esk5_0,X2))),k2_waybel_0(X1,esk5_0,X2))
    | m1_subset_1(esk8_1(esk1_2(esk4_0,esk5_0)),u1_struct_0(esk5_0))
    | v2_struct_0(X1)
    | ~ r1_waybel_0(X1,esk5_0,a_3_1_waybel_0(X1,esk5_0,X2))
    | ~ m1_subset_1(esk2_3(X1,esk5_0,X2),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ l1_waybel_0(esk5_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk2_3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_66]),c_0_33]),c_0_7]),c_0_8])]),c_0_9]),c_0_10])).

cnf(c_0_69,negated_conjecture,
    ( r1_waybel_0(esk4_0,esk5_0,a_3_1_waybel_0(esk4_0,esk5_0,esk6_0))
    | m1_subset_1(esk8_1(esk1_2(esk4_0,esk5_0)),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_65]),c_0_7]),c_0_8])]),c_0_10])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(esk8_1(esk1_2(esk4_0,esk5_0)),u1_struct_0(esk5_0))
    | ~ r1_orders_2(esk4_0,k2_waybel_0(esk4_0,esk5_0,esk7_1(X1)),k2_waybel_0(esk4_0,esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( r1_orders_2(esk4_0,k2_waybel_0(esk4_0,esk5_0,esk7_1(esk2_3(esk4_0,esk5_0,esk6_0))),k2_waybel_0(esk4_0,esk5_0,esk6_0))
    | m1_subset_1(esk8_1(esk1_2(esk4_0,esk5_0)),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_33]),c_0_7]),c_0_8])]),c_0_10]),c_0_69])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(esk8_1(esk1_2(esk4_0,esk5_0)),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_68])])).

cnf(c_0_73,negated_conjecture,
    ( r1_orders_2(esk5_0,X1,esk3_4(X2,esk5_0,esk1_2(esk4_0,esk5_0),X1))
    | r1_waybel_0(X2,esk5_0,a_3_1_waybel_0(X2,esk5_0,esk1_2(esk4_0,esk5_0)))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ l1_waybel_0(esk5_0,X2)
    | ~ l1_orders_2(X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_63]),c_0_9])).

cnf(c_0_74,negated_conjecture,
    ( r1_waybel_0(X1,esk5_0,a_3_1_waybel_0(X1,esk5_0,X2))
    | m1_subset_1(esk3_4(X1,esk5_0,X2,esk8_1(esk1_2(esk4_0,esk5_0))),u1_struct_0(esk5_0))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ l1_waybel_0(esk5_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_72]),c_0_9])).

cnf(c_0_75,negated_conjecture,
    ( r1_orders_2(esk5_0,esk8_1(esk1_2(esk4_0,esk5_0)),esk3_4(X1,esk5_0,esk1_2(esk4_0,esk5_0),esk8_1(esk1_2(esk4_0,esk5_0))))
    | r1_waybel_0(X1,esk5_0,a_3_1_waybel_0(X1,esk5_0,esk1_2(esk4_0,esk5_0)))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(esk5_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_72])).

cnf(c_0_76,negated_conjecture,
    ( r1_waybel_0(X1,esk5_0,a_3_1_waybel_0(X1,esk5_0,esk1_2(esk4_0,esk5_0)))
    | m1_subset_1(esk3_4(X1,esk5_0,esk1_2(esk4_0,esk5_0),esk8_1(esk1_2(esk4_0,esk5_0))),u1_struct_0(esk5_0))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(esk5_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_63])).

cnf(c_0_77,negated_conjecture,
    ( r1_orders_2(esk5_0,esk8_1(esk1_2(esk4_0,esk5_0)),esk3_4(esk4_0,esk5_0,esk1_2(esk4_0,esk5_0),esk8_1(esk1_2(esk4_0,esk5_0))))
    | r1_waybel_0(esk4_0,esk5_0,a_3_1_waybel_0(esk4_0,esk5_0,esk1_2(esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_7]),c_0_8])]),c_0_10])).

cnf(c_0_78,negated_conjecture,
    ( r1_waybel_0(esk4_0,esk5_0,a_3_1_waybel_0(esk4_0,esk5_0,esk1_2(esk4_0,esk5_0)))
    | m1_subset_1(esk3_4(esk4_0,esk5_0,esk1_2(esk4_0,esk5_0),esk8_1(esk1_2(esk4_0,esk5_0))),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_7]),c_0_8])]),c_0_10])).

cnf(c_0_79,negated_conjecture,
    ( r1_orders_2(esk5_0,esk8_1(esk1_2(esk4_0,esk5_0)),esk3_4(esk4_0,esk5_0,esk1_2(esk4_0,esk5_0),esk8_1(esk1_2(esk4_0,esk5_0))))
    | v11_waybel_0(esk5_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_77]),c_0_7]),c_0_8])]),c_0_9]),c_0_10])).

cnf(c_0_80,negated_conjecture,
    ( m1_subset_1(esk3_4(esk4_0,esk5_0,esk1_2(esk4_0,esk5_0),esk8_1(esk1_2(esk4_0,esk5_0))),u1_struct_0(esk5_0))
    | v11_waybel_0(esk5_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_78]),c_0_7]),c_0_8])]),c_0_9]),c_0_10])).

cnf(c_0_81,negated_conjecture,
    ( r1_orders_2(esk4_0,k2_waybel_0(esk4_0,esk5_0,esk3_4(esk4_0,esk5_0,esk1_2(esk4_0,esk5_0),esk8_1(esk1_2(esk4_0,esk5_0)))),k2_waybel_0(esk4_0,esk5_0,esk1_2(esk4_0,esk5_0)))
    | v11_waybel_0(esk5_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_79]),c_0_63])]),c_0_80])).

cnf(c_0_82,negated_conjecture,
    ( r1_waybel_0(esk4_0,esk5_0,a_3_1_waybel_0(esk4_0,esk5_0,esk1_2(esk4_0,esk5_0)))
    | v11_waybel_0(esk5_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_81]),c_0_72]),c_0_63]),c_0_7]),c_0_8])]),c_0_9]),c_0_10])).

cnf(c_0_83,negated_conjecture,
    ( v11_waybel_0(esk5_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_82]),c_0_7]),c_0_8])]),c_0_9]),c_0_10])).

cnf(c_0_84,negated_conjecture,
    ( r1_orders_2(X1,k2_waybel_0(X1,esk5_0,esk7_1(esk2_3(X1,esk5_0,X2))),k2_waybel_0(X1,esk5_0,X2))
    | v2_struct_0(X1)
    | ~ r1_waybel_0(X1,esk5_0,a_3_1_waybel_0(X1,esk5_0,X2))
    | ~ m1_subset_1(esk2_3(X1,esk5_0,X2),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ l1_waybel_0(esk5_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_83])])).

cnf(c_0_85,negated_conjecture,
    ( r1_waybel_0(esk4_0,esk5_0,a_3_1_waybel_0(esk4_0,esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_83]),c_0_7]),c_0_8])]),c_0_10])).

cnf(c_0_86,negated_conjecture,
    ( ~ r1_orders_2(esk4_0,k2_waybel_0(esk4_0,esk5_0,esk7_1(X1)),k2_waybel_0(esk4_0,esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_83])])).

cnf(c_0_87,negated_conjecture,
    ( r1_orders_2(esk4_0,k2_waybel_0(esk4_0,esk5_0,esk7_1(esk2_3(esk4_0,esk5_0,esk6_0))),k2_waybel_0(esk4_0,esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_68]),c_0_85]),c_0_33]),c_0_7]),c_0_8])]),c_0_10])).

cnf(c_0_88,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_68])]),
    [proof]).

%------------------------------------------------------------------------------
