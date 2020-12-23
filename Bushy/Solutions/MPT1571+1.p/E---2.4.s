%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow_0__t49_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:43 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 297 expanded)
%              Number of clauses        :   30 ( 100 expanded)
%              Number of leaves         :    4 (  72 expanded)
%              Depth                    :   12
%              Number of atoms          :  200 (2009 expanded)
%              Number of equality atoms :   24 ( 204 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   30 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t49_yellow_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2,X3] :
          ( ( r2_yellow_0(X1,X2)
            & ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r1_lattice3(X1,X2,X4)
                <=> r1_lattice3(X1,X3,X4) ) ) )
         => k2_yellow_0(X1,X2) = k2_yellow_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t49_yellow_0.p',t49_yellow_0)).

fof(t48_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2,X3] :
          ( ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r1_lattice3(X1,X2,X4)
                <=> r1_lattice3(X1,X3,X4) ) )
            & r2_yellow_0(X1,X2) )
         => r2_yellow_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t49_yellow_0.p',t48_yellow_0)).

fof(d10_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r2_yellow_0(X1,X2)
           => ( X3 = k2_yellow_0(X1,X2)
            <=> ( r1_lattice3(X1,X2,X3)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r1_lattice3(X1,X2,X4)
                     => r1_orders_2(X1,X4,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t49_yellow_0.p',d10_yellow_0)).

fof(dt_k2_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t49_yellow_0.p',dt_k2_yellow_0)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_orders_2(X1) )
       => ! [X2,X3] :
            ( ( r2_yellow_0(X1,X2)
              & ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r1_lattice3(X1,X2,X4)
                  <=> r1_lattice3(X1,X3,X4) ) ) )
           => k2_yellow_0(X1,X2) = k2_yellow_0(X1,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t49_yellow_0])).

fof(c_0_5,plain,(
    ! [X27,X28,X29] :
      ( ( m1_subset_1(esk8_3(X27,X28,X29),u1_struct_0(X27))
        | ~ r2_yellow_0(X27,X28)
        | r2_yellow_0(X27,X29)
        | v2_struct_0(X27)
        | ~ l1_orders_2(X27) )
      & ( ~ r1_lattice3(X27,X28,esk8_3(X27,X28,X29))
        | ~ r1_lattice3(X27,X29,esk8_3(X27,X28,X29))
        | ~ r2_yellow_0(X27,X28)
        | r2_yellow_0(X27,X29)
        | v2_struct_0(X27)
        | ~ l1_orders_2(X27) )
      & ( r1_lattice3(X27,X28,esk8_3(X27,X28,X29))
        | r1_lattice3(X27,X29,esk8_3(X27,X28,X29))
        | ~ r2_yellow_0(X27,X28)
        | r2_yellow_0(X27,X29)
        | v2_struct_0(X27)
        | ~ l1_orders_2(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_yellow_0])])])])])])).

fof(c_0_6,negated_conjecture,(
    ! [X8] :
      ( ~ v2_struct_0(esk1_0)
      & l1_orders_2(esk1_0)
      & r2_yellow_0(esk1_0,esk2_0)
      & ( ~ r1_lattice3(esk1_0,esk2_0,X8)
        | r1_lattice3(esk1_0,esk3_0,X8)
        | ~ m1_subset_1(X8,u1_struct_0(esk1_0)) )
      & ( ~ r1_lattice3(esk1_0,esk3_0,X8)
        | r1_lattice3(esk1_0,esk2_0,X8)
        | ~ m1_subset_1(X8,u1_struct_0(esk1_0)) )
      & k2_yellow_0(esk1_0,esk2_0) != k2_yellow_0(esk1_0,esk3_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])])])).

cnf(c_0_7,plain,
    ( r1_lattice3(X1,X2,esk8_3(X1,X2,X3))
    | r1_lattice3(X1,X3,esk8_3(X1,X2,X3))
    | r2_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( r2_yellow_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( m1_subset_1(esk8_3(X1,X2,X3),u1_struct_0(X1))
    | r2_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_12,plain,(
    ! [X11,X12,X13,X14] :
      ( ( r1_lattice3(X11,X12,X13)
        | X13 != k2_yellow_0(X11,X12)
        | ~ r2_yellow_0(X11,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ l1_orders_2(X11) )
      & ( ~ m1_subset_1(X14,u1_struct_0(X11))
        | ~ r1_lattice3(X11,X12,X14)
        | r1_orders_2(X11,X14,X13)
        | X13 != k2_yellow_0(X11,X12)
        | ~ r2_yellow_0(X11,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ l1_orders_2(X11) )
      & ( m1_subset_1(esk4_3(X11,X12,X13),u1_struct_0(X11))
        | ~ r1_lattice3(X11,X12,X13)
        | X13 = k2_yellow_0(X11,X12)
        | ~ r2_yellow_0(X11,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ l1_orders_2(X11) )
      & ( r1_lattice3(X11,X12,esk4_3(X11,X12,X13))
        | ~ r1_lattice3(X11,X12,X13)
        | X13 = k2_yellow_0(X11,X12)
        | ~ r2_yellow_0(X11,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ l1_orders_2(X11) )
      & ( ~ r1_orders_2(X11,esk4_3(X11,X12,X13),X13)
        | ~ r1_lattice3(X11,X12,X13)
        | X13 = k2_yellow_0(X11,X12)
        | ~ r2_yellow_0(X11,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ l1_orders_2(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_yellow_0])])])])])).

cnf(c_0_13,plain,
    ( r2_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,esk8_3(X1,X2,X3))
    | ~ r1_lattice3(X1,X3,esk8_3(X1,X2,X3))
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( r1_lattice3(esk1_0,esk3_0,X1)
    | ~ r1_lattice3(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,X1)
    | ~ r1_lattice3(esk1_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk8_3(esk1_0,esk2_0,X1))
    | r1_lattice3(esk1_0,X1,esk8_3(esk1_0,esk2_0,X1))
    | r2_yellow_0(esk1_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9])]),c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk8_3(esk1_0,esk2_0,X1),u1_struct_0(esk1_0))
    | r2_yellow_0(esk1_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_8]),c_0_9])]),c_0_10])).

cnf(c_0_18,plain,
    ( r1_orders_2(X2,X1,X4)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | X4 != k2_yellow_0(X2,X3)
    | ~ r2_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( r2_yellow_0(esk1_0,esk3_0)
    | ~ r1_lattice3(esk1_0,esk2_0,esk8_3(esk1_0,X1,esk3_0))
    | ~ r1_lattice3(esk1_0,X1,esk8_3(esk1_0,X1,esk3_0))
    | ~ m1_subset_1(esk8_3(esk1_0,X1,esk3_0),u1_struct_0(esk1_0))
    | ~ r2_yellow_0(esk1_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_9])]),c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk8_3(esk1_0,esk2_0,esk3_0))
    | r2_yellow_0(esk1_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,X2)
    | X2 != k2_yellow_0(esk1_0,esk3_0)
    | ~ r1_lattice3(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r2_yellow_0(esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_14]),c_0_9])])).

cnf(c_0_22,negated_conjecture,
    ( r2_yellow_0(esk1_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_8])]),c_0_17]),c_0_20])).

fof(c_0_23,plain,(
    ! [X16,X17] :
      ( ~ l1_orders_2(X16)
      | m1_subset_1(k2_yellow_0(X16,X17),u1_struct_0(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_yellow_0])])).

cnf(c_0_24,plain,
    ( X3 = k2_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,esk4_3(X1,X2,X3),X3)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,X2)
    | X2 != k2_yellow_0(esk1_0,esk3_0)
    | ~ r1_lattice3(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22])])).

cnf(c_0_26,plain,
    ( r1_lattice3(X1,X2,X3)
    | X3 != k2_yellow_0(X1,X2)
    | ~ r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,plain,
    ( m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( X1 = k2_yellow_0(esk1_0,X2)
    | X1 != k2_yellow_0(esk1_0,esk3_0)
    | ~ r1_lattice3(esk1_0,esk2_0,esk4_3(esk1_0,X2,X1))
    | ~ r1_lattice3(esk1_0,X2,X1)
    | ~ m1_subset_1(esk4_3(esk1_0,X2,X1),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r2_yellow_0(esk1_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_9])])).

cnf(c_0_29,plain,
    ( r1_lattice3(X1,X2,esk4_3(X1,X2,X3))
    | X3 = k2_yellow_0(X1,X2)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_30,plain,
    ( r1_lattice3(X1,X2,k2_yellow_0(X1,X3))
    | k2_yellow_0(X1,X3) != k2_yellow_0(X1,X2)
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( X1 = k2_yellow_0(esk1_0,esk2_0)
    | X1 != k2_yellow_0(esk1_0,esk3_0)
    | ~ r1_lattice3(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(esk4_3(esk1_0,esk2_0,X1),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_8]),c_0_9])])).

cnf(c_0_32,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))
    | X3 = k2_yellow_0(X1,X2)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_33,plain,
    ( r1_lattice3(X1,X2,k2_yellow_0(X1,X2))
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( X1 = k2_yellow_0(esk1_0,esk2_0)
    | X1 != k2_yellow_0(esk1_0,esk3_0)
    | ~ r1_lattice3(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_8]),c_0_9])])).

cnf(c_0_35,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,k2_yellow_0(esk1_0,esk3_0))
    | ~ m1_subset_1(k2_yellow_0(esk1_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_33]),c_0_22]),c_0_9])])).

cnf(c_0_36,negated_conjecture,
    ( k2_yellow_0(esk1_0,esk2_0) != k2_yellow_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_37,negated_conjecture,
    ( ~ m1_subset_1(k2_yellow_0(esk1_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_27]),c_0_9])]),
    [proof]).
%------------------------------------------------------------------------------
