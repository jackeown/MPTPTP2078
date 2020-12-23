%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1573+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:25 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   68 (15620 expanded)
%              Number of clauses        :   61 (6138 expanded)
%              Number of leaves         :    3 (3443 expanded)
%              Depth                    :   38
%              Number of atoms          :  248 (77051 expanded)
%              Number of equality atoms :   30 (12518 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t51_yellow_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( r1_yellow_0(X1,X2)
            | r1_yellow_0(X1,k3_xboole_0(X2,u1_struct_0(X1))) )
         => k1_yellow_0(X1,X2) = k1_yellow_0(X1,k3_xboole_0(X2,u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_yellow_0)).

fof(t47_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2,X3] :
          ( ( r1_yellow_0(X1,X2)
            & ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_lattice3(X1,X2,X4)
                <=> r2_lattice3(X1,X3,X4) ) ) )
         => k1_yellow_0(X1,X2) = k1_yellow_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_yellow_0)).

fof(t5_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( ( r2_lattice3(X1,X2,X3)
             => r2_lattice3(X1,k3_xboole_0(X2,u1_struct_0(X1)),X3) )
            & ( r2_lattice3(X1,k3_xboole_0(X2,u1_struct_0(X1)),X3)
             => r2_lattice3(X1,X2,X3) )
            & ( r1_lattice3(X1,X2,X3)
             => r1_lattice3(X1,k3_xboole_0(X2,u1_struct_0(X1)),X3) )
            & ( r1_lattice3(X1,k3_xboole_0(X2,u1_struct_0(X1)),X3)
             => r1_lattice3(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_yellow_0)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( r1_yellow_0(X1,X2)
              | r1_yellow_0(X1,k3_xboole_0(X2,u1_struct_0(X1))) )
           => k1_yellow_0(X1,X2) = k1_yellow_0(X1,k3_xboole_0(X2,u1_struct_0(X1))) ) ) ),
    inference(assume_negation,[status(cth)],[t51_yellow_0])).

fof(c_0_4,plain,(
    ! [X7,X8,X9] :
      ( ( m1_subset_1(esk1_3(X7,X8,X9),u1_struct_0(X7))
        | ~ r1_yellow_0(X7,X8)
        | k1_yellow_0(X7,X8) = k1_yellow_0(X7,X9)
        | v2_struct_0(X7)
        | ~ l1_orders_2(X7) )
      & ( ~ r2_lattice3(X7,X8,esk1_3(X7,X8,X9))
        | ~ r2_lattice3(X7,X9,esk1_3(X7,X8,X9))
        | ~ r1_yellow_0(X7,X8)
        | k1_yellow_0(X7,X8) = k1_yellow_0(X7,X9)
        | v2_struct_0(X7)
        | ~ l1_orders_2(X7) )
      & ( r2_lattice3(X7,X8,esk1_3(X7,X8,X9))
        | r2_lattice3(X7,X9,esk1_3(X7,X8,X9))
        | ~ r1_yellow_0(X7,X8)
        | k1_yellow_0(X7,X8) = k1_yellow_0(X7,X9)
        | v2_struct_0(X7)
        | ~ l1_orders_2(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_yellow_0])])])])])])).

fof(c_0_5,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & l1_orders_2(esk2_0)
    & ( r1_yellow_0(esk2_0,esk3_0)
      | r1_yellow_0(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0))) )
    & k1_yellow_0(esk2_0,esk3_0) != k1_yellow_0(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])).

cnf(c_0_6,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | k1_yellow_0(X1,X2) = k1_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( k1_yellow_0(esk2_0,X1) = k1_yellow_0(esk2_0,X2)
    | m1_subset_1(esk1_3(esk2_0,X1,X2),u1_struct_0(esk2_0))
    | ~ r1_yellow_0(esk2_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_7]),c_0_8])).

cnf(c_0_10,negated_conjecture,
    ( r1_yellow_0(esk2_0,esk3_0)
    | r1_yellow_0(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,plain,
    ( r2_lattice3(X1,X2,esk1_3(X1,X2,X3))
    | r2_lattice3(X1,X3,esk1_3(X1,X2,X3))
    | k1_yellow_0(X1,X2) = k1_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_12,plain,(
    ! [X11,X12,X13] :
      ( ( ~ r2_lattice3(X11,X12,X13)
        | r2_lattice3(X11,k3_xboole_0(X12,u1_struct_0(X11)),X13)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | v2_struct_0(X11)
        | ~ l1_orders_2(X11) )
      & ( ~ r2_lattice3(X11,k3_xboole_0(X12,u1_struct_0(X11)),X13)
        | r2_lattice3(X11,X12,X13)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | v2_struct_0(X11)
        | ~ l1_orders_2(X11) )
      & ( ~ r1_lattice3(X11,X12,X13)
        | r1_lattice3(X11,k3_xboole_0(X12,u1_struct_0(X11)),X13)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | v2_struct_0(X11)
        | ~ l1_orders_2(X11) )
      & ( ~ r1_lattice3(X11,k3_xboole_0(X12,u1_struct_0(X11)),X13)
        | r1_lattice3(X11,X12,X13)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | v2_struct_0(X11)
        | ~ l1_orders_2(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_yellow_0])])])])])).

cnf(c_0_13,negated_conjecture,
    ( k1_yellow_0(esk2_0,esk3_0) != k1_yellow_0(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( k1_yellow_0(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0))) = k1_yellow_0(esk2_0,X1)
    | m1_subset_1(esk1_3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),X1),u1_struct_0(esk2_0))
    | r1_yellow_0(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( k1_yellow_0(esk2_0,X1) = k1_yellow_0(esk2_0,X2)
    | r2_lattice3(esk2_0,X1,esk1_3(esk2_0,X1,X2))
    | r2_lattice3(esk2_0,X2,esk1_3(esk2_0,X1,X2))
    | ~ r1_yellow_0(esk2_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_7]),c_0_8])).

cnf(c_0_16,plain,
    ( r2_lattice3(X1,k3_xboole_0(X2,u1_struct_0(X1)),X3)
    | v2_struct_0(X1)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),X1),u1_struct_0(esk2_0))
    | r1_yellow_0(esk2_0,esk3_0)
    | k1_yellow_0(esk2_0,X1) != k1_yellow_0(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( k1_yellow_0(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0))) = k1_yellow_0(esk2_0,X1)
    | r2_lattice3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk1_3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),X1))
    | r2_lattice3(esk2_0,X1,esk1_3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),X1))
    | r1_yellow_0(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( r2_lattice3(esk2_0,k3_xboole_0(X1,u1_struct_0(esk2_0)),X2)
    | ~ r2_lattice3(esk2_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_7]),c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk3_0),u1_struct_0(esk2_0))
    | r1_yellow_0(esk2_0,esk3_0) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( r2_lattice3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk1_3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),X1))
    | r2_lattice3(esk2_0,X1,esk1_3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),X1))
    | r1_yellow_0(esk2_0,esk3_0)
    | k1_yellow_0(esk2_0,X1) != k1_yellow_0(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( r2_lattice3(esk2_0,k3_xboole_0(X1,u1_struct_0(esk2_0)),esk1_3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk3_0))
    | r1_yellow_0(esk2_0,esk3_0)
    | ~ r2_lattice3(esk2_0,X1,esk1_3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( r2_lattice3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk1_3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk3_0))
    | r1_yellow_0(esk2_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_21]),c_0_22])).

cnf(c_0_24,negated_conjecture,
    ( k1_yellow_0(esk2_0,esk3_0) = k1_yellow_0(esk2_0,X1)
    | r2_lattice3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk1_3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk3_0))
    | m1_subset_1(esk1_3(esk2_0,esk3_0,X1),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_23])).

cnf(c_0_25,plain,
    ( r2_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r2_lattice3(X1,k3_xboole_0(X2,u1_struct_0(X1)),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_26,negated_conjecture,
    ( r2_lattice3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk1_3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk3_0))
    | m1_subset_1(esk1_3(esk2_0,esk3_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0))),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( r2_lattice3(esk2_0,X1,X2)
    | ~ r2_lattice3(esk2_0,k3_xboole_0(X1,u1_struct_0(esk2_0)),X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_7]),c_0_8])).

cnf(c_0_28,negated_conjecture,
    ( k1_yellow_0(esk2_0,esk3_0) = k1_yellow_0(esk2_0,X1)
    | r2_lattice3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk1_3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk3_0))
    | r2_lattice3(esk2_0,esk3_0,esk1_3(esk2_0,esk3_0,X1))
    | r2_lattice3(esk2_0,X1,esk1_3(esk2_0,esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( r2_lattice3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk1_3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk3_0))
    | r2_lattice3(esk2_0,k3_xboole_0(X1,u1_struct_0(esk2_0)),esk1_3(esk2_0,esk3_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0))))
    | ~ r2_lattice3(esk2_0,X1,esk1_3(esk2_0,esk3_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( r2_lattice3(esk2_0,X1,esk1_3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk3_0))
    | r1_yellow_0(esk2_0,esk3_0)
    | ~ r2_lattice3(esk2_0,k3_xboole_0(X1,u1_struct_0(esk2_0)),esk1_3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( r2_lattice3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk1_3(esk2_0,esk3_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0))))
    | r2_lattice3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk1_3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_28]),c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( r2_lattice3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk1_3(esk2_0,esk3_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0))))
    | r2_lattice3(esk2_0,esk3_0,esk1_3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk3_0))
    | r1_yellow_0(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_33,negated_conjecture,
    ( k1_yellow_0(esk2_0,esk3_0) = k1_yellow_0(esk2_0,X1)
    | r2_lattice3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk1_3(esk2_0,esk3_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0))))
    | r2_lattice3(esk2_0,esk3_0,esk1_3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk3_0))
    | r2_lattice3(esk2_0,esk3_0,esk1_3(esk2_0,esk3_0,X1))
    | r2_lattice3(esk2_0,X1,esk1_3(esk2_0,esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_32])).

cnf(c_0_34,negated_conjecture,
    ( r2_lattice3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk1_3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk3_0))
    | r2_lattice3(esk2_0,X1,esk1_3(esk2_0,esk3_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0))))
    | ~ r2_lattice3(esk2_0,k3_xboole_0(X1,u1_struct_0(esk2_0)),esk1_3(esk2_0,esk3_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( r2_lattice3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk1_3(esk2_0,esk3_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0))))
    | r2_lattice3(esk2_0,esk3_0,esk1_3(esk2_0,esk3_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0))))
    | r2_lattice3(esk2_0,esk3_0,esk1_3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( r2_lattice3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk1_3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk3_0))
    | r2_lattice3(esk2_0,esk3_0,esk1_3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk3_0))
    | r2_lattice3(esk2_0,esk3_0,esk1_3(esk2_0,esk3_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_37,negated_conjecture,
    ( r2_lattice3(esk2_0,esk3_0,esk1_3(esk2_0,esk3_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0))))
    | r2_lattice3(esk2_0,esk3_0,esk1_3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk3_0))
    | r1_yellow_0(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_36])).

cnf(c_0_38,negated_conjecture,
    ( k1_yellow_0(esk2_0,esk3_0) = k1_yellow_0(esk2_0,X1)
    | r2_lattice3(esk2_0,esk3_0,esk1_3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk3_0))
    | r2_lattice3(esk2_0,esk3_0,esk1_3(esk2_0,esk3_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0))))
    | m1_subset_1(esk1_3(esk2_0,esk3_0,X1),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_37])).

cnf(c_0_39,plain,
    ( k1_yellow_0(X1,X2) = k1_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r2_lattice3(X1,X2,esk1_3(X1,X2,X3))
    | ~ r2_lattice3(X1,X3,esk1_3(X1,X2,X3))
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_40,negated_conjecture,
    ( r2_lattice3(esk2_0,esk3_0,esk1_3(esk2_0,esk3_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0))))
    | r2_lattice3(esk2_0,esk3_0,esk1_3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk3_0))
    | m1_subset_1(esk1_3(esk2_0,esk3_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0))),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( k1_yellow_0(esk2_0,X1) = k1_yellow_0(esk2_0,X2)
    | ~ r2_lattice3(esk2_0,X2,esk1_3(esk2_0,X1,X2))
    | ~ r2_lattice3(esk2_0,X1,esk1_3(esk2_0,X1,X2))
    | ~ r1_yellow_0(esk2_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_7]),c_0_8])).

cnf(c_0_42,negated_conjecture,
    ( r2_lattice3(esk2_0,esk3_0,esk1_3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk3_0))
    | r2_lattice3(esk2_0,esk3_0,esk1_3(esk2_0,esk3_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0))))
    | r2_lattice3(esk2_0,X1,esk1_3(esk2_0,esk3_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0))))
    | ~ r2_lattice3(esk2_0,k3_xboole_0(X1,u1_struct_0(esk2_0)),esk1_3(esk2_0,esk3_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( k1_yellow_0(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0))) = k1_yellow_0(esk2_0,X1)
    | r1_yellow_0(esk2_0,esk3_0)
    | ~ r2_lattice3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk1_3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),X1))
    | ~ r2_lattice3(esk2_0,X1,esk1_3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_10])).

cnf(c_0_44,negated_conjecture,
    ( r2_lattice3(esk2_0,esk3_0,esk1_3(esk2_0,esk3_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0))))
    | r2_lattice3(esk2_0,esk3_0,esk1_3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( r2_lattice3(esk2_0,esk3_0,esk1_3(esk2_0,esk3_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0))))
    | r1_yellow_0(esk2_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_13]),c_0_23])).

cnf(c_0_46,negated_conjecture,
    ( k1_yellow_0(esk2_0,esk3_0) = k1_yellow_0(esk2_0,X1)
    | r2_lattice3(esk2_0,esk3_0,esk1_3(esk2_0,esk3_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0))))
    | m1_subset_1(esk1_3(esk2_0,esk3_0,X1),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_45])).

cnf(c_0_47,negated_conjecture,
    ( k1_yellow_0(esk2_0,esk3_0) = k1_yellow_0(esk2_0,X1)
    | r2_lattice3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk1_3(esk2_0,esk3_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0))))
    | r2_lattice3(esk2_0,esk3_0,esk1_3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk3_0))
    | m1_subset_1(esk1_3(esk2_0,esk3_0,X1),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_32])).

cnf(c_0_48,negated_conjecture,
    ( r2_lattice3(esk2_0,esk3_0,esk1_3(esk2_0,esk3_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0))))
    | m1_subset_1(esk1_3(esk2_0,esk3_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0))),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( k1_yellow_0(esk2_0,esk3_0) = k1_yellow_0(esk2_0,X1)
    | r2_lattice3(esk2_0,esk3_0,esk1_3(esk2_0,esk3_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0))))
    | r2_lattice3(esk2_0,esk3_0,esk1_3(esk2_0,esk3_0,X1))
    | r2_lattice3(esk2_0,X1,esk1_3(esk2_0,esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( r2_lattice3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk1_3(esk2_0,esk3_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0))))
    | r2_lattice3(esk2_0,esk3_0,esk1_3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk3_0))
    | m1_subset_1(esk1_3(esk2_0,esk3_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0))),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( r2_lattice3(esk2_0,esk3_0,esk1_3(esk2_0,esk3_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0))))
    | r2_lattice3(esk2_0,X1,esk1_3(esk2_0,esk3_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0))))
    | ~ r2_lattice3(esk2_0,k3_xboole_0(X1,u1_struct_0(esk2_0)),esk1_3(esk2_0,esk3_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( r2_lattice3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk1_3(esk2_0,esk3_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0))))
    | r2_lattice3(esk2_0,esk3_0,esk1_3(esk2_0,esk3_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_13,c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( r2_lattice3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk1_3(esk2_0,esk3_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0))))
    | r2_lattice3(esk2_0,k3_xboole_0(X1,u1_struct_0(esk2_0)),esk1_3(esk2_0,esk3_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0))))
    | r2_lattice3(esk2_0,esk3_0,esk1_3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk3_0))
    | ~ r2_lattice3(esk2_0,X1,esk1_3(esk2_0,esk3_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( r2_lattice3(esk2_0,esk3_0,esk1_3(esk2_0,esk3_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_55,negated_conjecture,
    ( k1_yellow_0(esk2_0,esk3_0) = k1_yellow_0(esk2_0,X1)
    | r2_lattice3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk1_3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk3_0))
    | ~ r2_lattice3(esk2_0,esk3_0,esk1_3(esk2_0,esk3_0,X1))
    | ~ r2_lattice3(esk2_0,X1,esk1_3(esk2_0,esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_23])).

cnf(c_0_56,negated_conjecture,
    ( r2_lattice3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk1_3(esk2_0,esk3_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0))))
    | r2_lattice3(esk2_0,esk3_0,esk1_3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( r2_lattice3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk1_3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk3_0))
    | r2_lattice3(esk2_0,esk3_0,esk1_3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_54])]),c_0_13])).

cnf(c_0_58,negated_conjecture,
    ( r2_lattice3(esk2_0,esk3_0,esk1_3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk3_0))
    | r1_yellow_0(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_57])).

cnf(c_0_59,negated_conjecture,
    ( k1_yellow_0(esk2_0,esk3_0) = k1_yellow_0(esk2_0,X1)
    | r2_lattice3(esk2_0,esk3_0,esk1_3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk3_0))
    | ~ r2_lattice3(esk2_0,esk3_0,esk1_3(esk2_0,esk3_0,X1))
    | ~ r2_lattice3(esk2_0,X1,esk1_3(esk2_0,esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_58])).

cnf(c_0_60,negated_conjecture,
    ( r2_lattice3(esk2_0,esk3_0,esk1_3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_56]),c_0_54])]),c_0_13])).

cnf(c_0_61,negated_conjecture,
    ( r1_yellow_0(esk2_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_60]),c_0_13]),c_0_23])).

cnf(c_0_62,negated_conjecture,
    ( k1_yellow_0(esk2_0,esk3_0) = k1_yellow_0(esk2_0,X1)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,X1),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_61])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,esk3_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0))),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_62])).

cnf(c_0_64,negated_conjecture,
    ( r2_lattice3(esk2_0,k3_xboole_0(X1,u1_struct_0(esk2_0)),esk1_3(esk2_0,esk3_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0))))
    | ~ r2_lattice3(esk2_0,X1,esk1_3(esk2_0,esk3_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_63])).

cnf(c_0_65,negated_conjecture,
    ( k1_yellow_0(esk2_0,esk3_0) = k1_yellow_0(esk2_0,X1)
    | ~ r2_lattice3(esk2_0,esk3_0,esk1_3(esk2_0,esk3_0,X1))
    | ~ r2_lattice3(esk2_0,X1,esk1_3(esk2_0,esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( r2_lattice3(esk2_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)),esk1_3(esk2_0,esk3_0,k3_xboole_0(esk3_0,u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_54])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_54])]),c_0_13]),
    [proof]).

%------------------------------------------------------------------------------
