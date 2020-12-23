%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:22 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 664 expanded)
%              Number of clauses        :   79 ( 271 expanded)
%              Number of leaves         :    4 ( 190 expanded)
%              Depth                    :    7
%              Number of atoms          :  698 (17635 expanded)
%              Number of equality atoms :   93 (1377 expanded)
%              Maximal formula depth    :   33 (   8 average)
%              Maximal clause size      :  107 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_yellow_0)).

fof(d8_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( r2_yellow_0(X1,X2)
        <=> ? [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
              & r1_lattice3(X1,X2,X3)
              & ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r1_lattice3(X1,X2,X4)
                   => r1_orders_2(X1,X4,X3) ) )
              & ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( ( r1_lattice3(X1,X2,X4)
                      & ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( r1_lattice3(X1,X2,X5)
                           => r1_orders_2(X1,X5,X4) ) ) )
                   => X4 = X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_yellow_0)).

fof(t37_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( r2_yellow_0(X1,X2)
          <=> r2_yellow_0(X1,k4_waybel_0(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_waybel_0)).

fof(t49_yellow_0,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_yellow_0)).

fof(c_0_4,plain,(
    ! [X6,X7,X8,X9] :
      ( ( r1_lattice3(X6,X7,X8)
        | X8 != k2_yellow_0(X6,X7)
        | ~ r2_yellow_0(X6,X7)
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | ~ l1_orders_2(X6) )
      & ( ~ m1_subset_1(X9,u1_struct_0(X6))
        | ~ r1_lattice3(X6,X7,X9)
        | r1_orders_2(X6,X9,X8)
        | X8 != k2_yellow_0(X6,X7)
        | ~ r2_yellow_0(X6,X7)
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | ~ l1_orders_2(X6) )
      & ( m1_subset_1(esk1_3(X6,X7,X8),u1_struct_0(X6))
        | ~ r1_lattice3(X6,X7,X8)
        | X8 = k2_yellow_0(X6,X7)
        | ~ r2_yellow_0(X6,X7)
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | ~ l1_orders_2(X6) )
      & ( r1_lattice3(X6,X7,esk1_3(X6,X7,X8))
        | ~ r1_lattice3(X6,X7,X8)
        | X8 = k2_yellow_0(X6,X7)
        | ~ r2_yellow_0(X6,X7)
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | ~ l1_orders_2(X6) )
      & ( ~ r1_orders_2(X6,esk1_3(X6,X7,X8),X8)
        | ~ r1_lattice3(X6,X7,X8)
        | X8 = k2_yellow_0(X6,X7)
        | ~ r2_yellow_0(X6,X7)
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | ~ l1_orders_2(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_yellow_0])])])])])).

fof(c_0_5,plain,(
    ! [X11,X12,X14,X15,X17,X18,X21] :
      ( ( m1_subset_1(esk2_2(X11,X12),u1_struct_0(X11))
        | ~ r2_yellow_0(X11,X12)
        | ~ l1_orders_2(X11) )
      & ( r1_lattice3(X11,X12,esk2_2(X11,X12))
        | ~ r2_yellow_0(X11,X12)
        | ~ l1_orders_2(X11) )
      & ( ~ m1_subset_1(X14,u1_struct_0(X11))
        | ~ r1_lattice3(X11,X12,X14)
        | r1_orders_2(X11,X14,esk2_2(X11,X12))
        | ~ r2_yellow_0(X11,X12)
        | ~ l1_orders_2(X11) )
      & ( m1_subset_1(esk3_3(X11,X12,X15),u1_struct_0(X11))
        | ~ r1_lattice3(X11,X12,X15)
        | X15 = esk2_2(X11,X12)
        | ~ m1_subset_1(X15,u1_struct_0(X11))
        | ~ r2_yellow_0(X11,X12)
        | ~ l1_orders_2(X11) )
      & ( r1_lattice3(X11,X12,esk3_3(X11,X12,X15))
        | ~ r1_lattice3(X11,X12,X15)
        | X15 = esk2_2(X11,X12)
        | ~ m1_subset_1(X15,u1_struct_0(X11))
        | ~ r2_yellow_0(X11,X12)
        | ~ l1_orders_2(X11) )
      & ( ~ r1_orders_2(X11,esk3_3(X11,X12,X15),X15)
        | ~ r1_lattice3(X11,X12,X15)
        | X15 = esk2_2(X11,X12)
        | ~ m1_subset_1(X15,u1_struct_0(X11))
        | ~ r2_yellow_0(X11,X12)
        | ~ l1_orders_2(X11) )
      & ( m1_subset_1(esk5_3(X11,X17,X18),u1_struct_0(X11))
        | m1_subset_1(esk4_3(X11,X17,X18),u1_struct_0(X11))
        | ~ m1_subset_1(X18,u1_struct_0(X11))
        | ~ r1_lattice3(X11,X17,X18)
        | r2_yellow_0(X11,X17)
        | ~ l1_orders_2(X11) )
      & ( r1_lattice3(X11,X17,esk5_3(X11,X17,X18))
        | m1_subset_1(esk4_3(X11,X17,X18),u1_struct_0(X11))
        | ~ m1_subset_1(X18,u1_struct_0(X11))
        | ~ r1_lattice3(X11,X17,X18)
        | r2_yellow_0(X11,X17)
        | ~ l1_orders_2(X11) )
      & ( ~ m1_subset_1(X21,u1_struct_0(X11))
        | ~ r1_lattice3(X11,X17,X21)
        | r1_orders_2(X11,X21,esk5_3(X11,X17,X18))
        | m1_subset_1(esk4_3(X11,X17,X18),u1_struct_0(X11))
        | ~ m1_subset_1(X18,u1_struct_0(X11))
        | ~ r1_lattice3(X11,X17,X18)
        | r2_yellow_0(X11,X17)
        | ~ l1_orders_2(X11) )
      & ( esk5_3(X11,X17,X18) != X18
        | m1_subset_1(esk4_3(X11,X17,X18),u1_struct_0(X11))
        | ~ m1_subset_1(X18,u1_struct_0(X11))
        | ~ r1_lattice3(X11,X17,X18)
        | r2_yellow_0(X11,X17)
        | ~ l1_orders_2(X11) )
      & ( m1_subset_1(esk5_3(X11,X17,X18),u1_struct_0(X11))
        | r1_lattice3(X11,X17,esk4_3(X11,X17,X18))
        | ~ m1_subset_1(X18,u1_struct_0(X11))
        | ~ r1_lattice3(X11,X17,X18)
        | r2_yellow_0(X11,X17)
        | ~ l1_orders_2(X11) )
      & ( r1_lattice3(X11,X17,esk5_3(X11,X17,X18))
        | r1_lattice3(X11,X17,esk4_3(X11,X17,X18))
        | ~ m1_subset_1(X18,u1_struct_0(X11))
        | ~ r1_lattice3(X11,X17,X18)
        | r2_yellow_0(X11,X17)
        | ~ l1_orders_2(X11) )
      & ( ~ m1_subset_1(X21,u1_struct_0(X11))
        | ~ r1_lattice3(X11,X17,X21)
        | r1_orders_2(X11,X21,esk5_3(X11,X17,X18))
        | r1_lattice3(X11,X17,esk4_3(X11,X17,X18))
        | ~ m1_subset_1(X18,u1_struct_0(X11))
        | ~ r1_lattice3(X11,X17,X18)
        | r2_yellow_0(X11,X17)
        | ~ l1_orders_2(X11) )
      & ( esk5_3(X11,X17,X18) != X18
        | r1_lattice3(X11,X17,esk4_3(X11,X17,X18))
        | ~ m1_subset_1(X18,u1_struct_0(X11))
        | ~ r1_lattice3(X11,X17,X18)
        | r2_yellow_0(X11,X17)
        | ~ l1_orders_2(X11) )
      & ( m1_subset_1(esk5_3(X11,X17,X18),u1_struct_0(X11))
        | ~ r1_orders_2(X11,esk4_3(X11,X17,X18),X18)
        | ~ m1_subset_1(X18,u1_struct_0(X11))
        | ~ r1_lattice3(X11,X17,X18)
        | r2_yellow_0(X11,X17)
        | ~ l1_orders_2(X11) )
      & ( r1_lattice3(X11,X17,esk5_3(X11,X17,X18))
        | ~ r1_orders_2(X11,esk4_3(X11,X17,X18),X18)
        | ~ m1_subset_1(X18,u1_struct_0(X11))
        | ~ r1_lattice3(X11,X17,X18)
        | r2_yellow_0(X11,X17)
        | ~ l1_orders_2(X11) )
      & ( ~ m1_subset_1(X21,u1_struct_0(X11))
        | ~ r1_lattice3(X11,X17,X21)
        | r1_orders_2(X11,X21,esk5_3(X11,X17,X18))
        | ~ r1_orders_2(X11,esk4_3(X11,X17,X18),X18)
        | ~ m1_subset_1(X18,u1_struct_0(X11))
        | ~ r1_lattice3(X11,X17,X18)
        | r2_yellow_0(X11,X17)
        | ~ l1_orders_2(X11) )
      & ( esk5_3(X11,X17,X18) != X18
        | ~ r1_orders_2(X11,esk4_3(X11,X17,X18),X18)
        | ~ m1_subset_1(X18,u1_struct_0(X11))
        | ~ r1_lattice3(X11,X17,X18)
        | r2_yellow_0(X11,X17)
        | ~ l1_orders_2(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_yellow_0])])])])])])).

cnf(c_0_6,plain,
    ( X3 = k2_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,esk1_3(X1,X2,X3),X3)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_7,plain,
    ( r1_orders_2(X2,X1,esk2_2(X2,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | ~ r2_yellow_0(X2,X3)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_8,plain,
    ( m1_subset_1(esk2_2(X1,X2),u1_struct_0(X1))
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_9,plain,
    ( esk2_2(X1,X2) = k2_yellow_0(X1,X3)
    | ~ r1_lattice3(X1,X2,esk1_3(X1,X3,esk2_2(X1,X2)))
    | ~ r1_lattice3(X1,X3,esk2_2(X1,X2))
    | ~ r2_yellow_0(X1,X3)
    | ~ r2_yellow_0(X1,X2)
    | ~ m1_subset_1(esk1_3(X1,X3,esk2_2(X1,X2)),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_7]),c_0_8])).

cnf(c_0_10,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | X3 = k2_yellow_0(X1,X2)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( r2_yellow_0(X1,X2)
            <=> r2_yellow_0(X1,k4_waybel_0(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t37_waybel_0])).

cnf(c_0_12,plain,
    ( r1_orders_2(X2,X1,X4)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | X4 != k2_yellow_0(X2,X3)
    | ~ r2_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_13,plain,
    ( r1_lattice3(X1,X2,esk3_3(X1,X2,X3))
    | X3 = esk2_2(X1,X2)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_14,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | X3 = esk2_2(X1,X2)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_15,plain,
    ( esk2_2(X1,X2) = k2_yellow_0(X1,X3)
    | ~ r1_lattice3(X1,X2,esk1_3(X1,X3,esk2_2(X1,X2)))
    | ~ r1_lattice3(X1,X3,esk2_2(X1,X2))
    | ~ r2_yellow_0(X1,X3)
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_8]),
    [final]).

cnf(c_0_16,plain,
    ( r1_lattice3(X1,X2,esk1_3(X1,X2,X3))
    | X3 = k2_yellow_0(X1,X2)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_17,plain,
    ( r1_lattice3(X1,X2,esk2_2(X1,X2))
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_18,plain,
    ( X3 = esk2_2(X1,X2)
    | ~ r1_orders_2(X1,esk3_3(X1,X2,X3),X3)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

fof(c_0_19,plain,(
    ! [X22,X23,X24] :
      ( ( m1_subset_1(esk6_3(X22,X23,X24),u1_struct_0(X22))
        | ~ r2_yellow_0(X22,X23)
        | k2_yellow_0(X22,X23) = k2_yellow_0(X22,X24)
        | v2_struct_0(X22)
        | ~ l1_orders_2(X22) )
      & ( ~ r1_lattice3(X22,X23,esk6_3(X22,X23,X24))
        | ~ r1_lattice3(X22,X24,esk6_3(X22,X23,X24))
        | ~ r2_yellow_0(X22,X23)
        | k2_yellow_0(X22,X23) = k2_yellow_0(X22,X24)
        | v2_struct_0(X22)
        | ~ l1_orders_2(X22) )
      & ( r1_lattice3(X22,X23,esk6_3(X22,X23,X24))
        | r1_lattice3(X22,X24,esk6_3(X22,X23,X24))
        | ~ r2_yellow_0(X22,X23)
        | k2_yellow_0(X22,X23) = k2_yellow_0(X22,X24)
        | v2_struct_0(X22)
        | ~ l1_orders_2(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_yellow_0])])])])])])).

fof(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk7_0)
    & v3_orders_2(esk7_0)
    & v4_orders_2(esk7_0)
    & l1_orders_2(esk7_0)
    & m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0)))
    & ( ~ r2_yellow_0(esk7_0,esk8_0)
      | ~ r2_yellow_0(esk7_0,k4_waybel_0(esk7_0,esk8_0)) )
    & ( r2_yellow_0(esk7_0,esk8_0)
      | r2_yellow_0(esk7_0,k4_waybel_0(esk7_0,esk8_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

cnf(c_0_21,plain,
    ( r1_orders_2(X2,X1,esk5_3(X2,X3,X4))
    | r1_lattice3(X2,X3,esk4_3(X2,X3,X4))
    | r2_yellow_0(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X4)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_22,plain,
    ( m1_subset_1(esk5_3(X1,X2,X3),u1_struct_0(X1))
    | r1_lattice3(X1,X2,esk4_3(X1,X2,X3))
    | r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_23,plain,
    ( r1_orders_2(X2,X1,esk5_3(X2,X3,X4))
    | m1_subset_1(esk4_3(X2,X3,X4),u1_struct_0(X2))
    | r2_yellow_0(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X4)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_24,plain,
    ( m1_subset_1(esk5_3(X1,X2,X3),u1_struct_0(X1))
    | m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))
    | r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_25,plain,
    ( r1_orders_2(X2,X1,esk5_3(X2,X3,X4))
    | r2_yellow_0(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | ~ r1_orders_2(X2,esk4_3(X2,X3,X4),X4)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X4)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_26,plain,
    ( m1_subset_1(esk5_3(X1,X2,X3),u1_struct_0(X1))
    | r2_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,esk4_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_27,plain,
    ( X1 = esk2_2(X2,X3)
    | r1_orders_2(X2,esk3_3(X2,X3,X1),X4)
    | X4 != k2_yellow_0(X2,X3)
    | ~ r1_lattice3(X2,X3,X1)
    | ~ r2_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),
    [final]).

cnf(c_0_28,plain,
    ( r1_lattice3(X1,X2,X3)
    | X3 != k2_yellow_0(X1,X2)
    | ~ r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_29,plain,
    ( esk2_2(X1,X2) = k2_yellow_0(X1,X2)
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_8]),c_0_17]),
    [final]).

cnf(c_0_30,plain,
    ( esk2_2(X1,X2) = esk2_2(X1,X3)
    | ~ r1_lattice3(X1,X2,esk3_3(X1,X3,esk2_2(X1,X2)))
    | ~ r1_lattice3(X1,X3,esk2_2(X1,X2))
    | ~ r2_yellow_0(X1,X3)
    | ~ r2_yellow_0(X1,X2)
    | ~ m1_subset_1(esk3_3(X1,X3,esk2_2(X1,X2)),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_7]),c_0_8])).

cnf(c_0_31,plain,
    ( r1_lattice3(X1,X2,esk6_3(X1,X2,X3))
    | r1_lattice3(X1,X3,esk6_3(X1,X2,X3))
    | k2_yellow_0(X1,X2) = k2_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19]),
    [final]).

cnf(c_0_32,negated_conjecture,
    ( r2_yellow_0(esk7_0,esk8_0)
    | r2_yellow_0(esk7_0,k4_waybel_0(esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20]),
    [final]).

cnf(c_0_33,negated_conjecture,
    ( l1_orders_2(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20]),
    [final]).

cnf(c_0_34,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20]),
    [final]).

cnf(c_0_35,plain,
    ( esk5_3(X1,X2,X3) = k2_yellow_0(X1,X4)
    | r1_lattice3(X1,X2,esk4_3(X1,X2,X3))
    | r2_yellow_0(X1,X2)
    | ~ r1_lattice3(X1,X2,esk1_3(X1,X4,esk5_3(X1,X2,X3)))
    | ~ r1_lattice3(X1,X4,esk5_3(X1,X2,X3))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ r2_yellow_0(X1,X4)
    | ~ m1_subset_1(esk1_3(X1,X4,esk5_3(X1,X2,X3)),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_21]),c_0_22])).

cnf(c_0_36,plain,
    ( esk5_3(X1,X2,X3) = esk2_2(X1,X4)
    | r1_lattice3(X1,X2,esk4_3(X1,X2,X3))
    | r2_yellow_0(X1,X2)
    | ~ r1_lattice3(X1,X2,esk3_3(X1,X4,esk5_3(X1,X2,X3)))
    | ~ r1_lattice3(X1,X4,esk5_3(X1,X2,X3))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ r2_yellow_0(X1,X4)
    | ~ m1_subset_1(esk3_3(X1,X4,esk5_3(X1,X2,X3)),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_21]),c_0_22])).

cnf(c_0_37,plain,
    ( esk5_3(X1,X2,X3) = k2_yellow_0(X1,X4)
    | r2_yellow_0(X1,X2)
    | m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,esk1_3(X1,X4,esk5_3(X1,X2,X3)))
    | ~ r1_lattice3(X1,X4,esk5_3(X1,X2,X3))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ r2_yellow_0(X1,X4)
    | ~ m1_subset_1(esk1_3(X1,X4,esk5_3(X1,X2,X3)),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_23]),c_0_24])).

cnf(c_0_38,plain,
    ( esk5_3(X1,X2,X3) = k2_yellow_0(X1,X4)
    | r2_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,esk4_3(X1,X2,X3),X3)
    | ~ r1_lattice3(X1,X2,esk1_3(X1,X4,esk5_3(X1,X2,X3)))
    | ~ r1_lattice3(X1,X4,esk5_3(X1,X2,X3))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ r2_yellow_0(X1,X4)
    | ~ m1_subset_1(esk1_3(X1,X4,esk5_3(X1,X2,X3)),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_25]),c_0_26])).

cnf(c_0_39,plain,
    ( esk5_3(X1,X2,X3) = esk2_2(X1,X4)
    | r2_yellow_0(X1,X2)
    | m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,esk3_3(X1,X4,esk5_3(X1,X2,X3)))
    | ~ r1_lattice3(X1,X4,esk5_3(X1,X2,X3))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ r2_yellow_0(X1,X4)
    | ~ m1_subset_1(esk3_3(X1,X4,esk5_3(X1,X2,X3)),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_23]),c_0_24])).

cnf(c_0_40,plain,
    ( esk5_3(X1,X2,X3) = esk2_2(X1,X4)
    | r2_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,esk4_3(X1,X2,X3),X3)
    | ~ r1_lattice3(X1,X2,esk3_3(X1,X4,esk5_3(X1,X2,X3)))
    | ~ r1_lattice3(X1,X4,esk5_3(X1,X2,X3))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ r2_yellow_0(X1,X4)
    | ~ m1_subset_1(esk3_3(X1,X4,esk5_3(X1,X2,X3)),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_25]),c_0_26])).

cnf(c_0_41,plain,
    ( X1 = esk2_2(X2,X3)
    | X1 != k2_yellow_0(X2,X3)
    | ~ r2_yellow_0(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_27]),c_0_28]),
    [final]).

cnf(c_0_42,plain,
    ( m1_subset_1(esk6_3(X1,X2,X3),u1_struct_0(X1))
    | k2_yellow_0(X1,X2) = k2_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19]),
    [final]).

cnf(c_0_43,plain,
    ( m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_29]),
    [final]).

cnf(c_0_44,plain,
    ( esk2_2(X1,X2) = esk2_2(X1,X3)
    | ~ r1_lattice3(X1,X2,esk3_3(X1,X3,esk2_2(X1,X2)))
    | ~ r1_lattice3(X1,X3,esk2_2(X1,X2))
    | ~ r2_yellow_0(X1,X3)
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_14]),c_0_8]),
    [final]).

cnf(c_0_45,plain,
    ( r1_lattice3(X1,X2,esk2_2(X1,X3))
    | esk2_2(X1,X3) != k2_yellow_0(X1,X2)
    | ~ r2_yellow_0(X1,X2)
    | ~ r2_yellow_0(X1,X3)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_8]),
    [final]).

cnf(c_0_46,plain,
    ( r1_orders_2(X1,esk2_2(X1,X2),X3)
    | X3 != k2_yellow_0(X1,X2)
    | ~ r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_17]),c_0_8]),
    [final]).

cnf(c_0_47,negated_conjecture,
    ( k2_yellow_0(esk7_0,k4_waybel_0(esk7_0,esk8_0)) = k2_yellow_0(esk7_0,X1)
    | r1_lattice3(esk7_0,k4_waybel_0(esk7_0,esk8_0),esk6_3(esk7_0,k4_waybel_0(esk7_0,esk8_0),X1))
    | r1_lattice3(esk7_0,X1,esk6_3(esk7_0,k4_waybel_0(esk7_0,esk8_0),X1))
    | r2_yellow_0(esk7_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])]),c_0_34]),
    [final]).

cnf(c_0_48,plain,
    ( esk5_3(X1,X2,X3) = k2_yellow_0(X1,X4)
    | r1_lattice3(X1,X2,esk4_3(X1,X2,X3))
    | r2_yellow_0(X1,X2)
    | ~ r1_lattice3(X1,X2,esk1_3(X1,X4,esk5_3(X1,X2,X3)))
    | ~ r1_lattice3(X1,X4,esk5_3(X1,X2,X3))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ r2_yellow_0(X1,X4)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_10]),c_0_22]),
    [final]).

cnf(c_0_49,plain,
    ( esk5_3(X1,X2,X3) = esk2_2(X1,X4)
    | r1_lattice3(X1,X2,esk4_3(X1,X2,X3))
    | r2_yellow_0(X1,X2)
    | ~ r1_lattice3(X1,X2,esk3_3(X1,X4,esk5_3(X1,X2,X3)))
    | ~ r1_lattice3(X1,X4,esk5_3(X1,X2,X3))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ r2_yellow_0(X1,X4)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_14]),c_0_22]),
    [final]).

cnf(c_0_50,plain,
    ( esk5_3(X1,X2,X3) = k2_yellow_0(X1,X4)
    | r2_yellow_0(X1,X2)
    | m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,esk1_3(X1,X4,esk5_3(X1,X2,X3)))
    | ~ r1_lattice3(X1,X4,esk5_3(X1,X2,X3))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ r2_yellow_0(X1,X4)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_10]),c_0_24]),
    [final]).

cnf(c_0_51,plain,
    ( esk5_3(X1,X2,X3) = k2_yellow_0(X1,X4)
    | r2_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,esk4_3(X1,X2,X3),X3)
    | ~ r1_lattice3(X1,X2,esk1_3(X1,X4,esk5_3(X1,X2,X3)))
    | ~ r1_lattice3(X1,X4,esk5_3(X1,X2,X3))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ r2_yellow_0(X1,X4)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_10]),c_0_26]),
    [final]).

cnf(c_0_52,plain,
    ( esk5_3(X1,X2,X3) = esk2_2(X1,X4)
    | r2_yellow_0(X1,X2)
    | m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,esk3_3(X1,X4,esk5_3(X1,X2,X3)))
    | ~ r1_lattice3(X1,X4,esk5_3(X1,X2,X3))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ r2_yellow_0(X1,X4)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_14]),c_0_24]),
    [final]).

cnf(c_0_53,plain,
    ( esk5_3(X1,X2,X3) = esk2_2(X1,X4)
    | r2_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,esk4_3(X1,X2,X3),X3)
    | ~ r1_lattice3(X1,X2,esk3_3(X1,X4,esk5_3(X1,X2,X3)))
    | ~ r1_lattice3(X1,X4,esk5_3(X1,X2,X3))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ r2_yellow_0(X1,X4)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_14]),c_0_26]),
    [final]).

cnf(c_0_54,plain,
    ( esk5_3(X1,X2,X3) = esk2_2(X1,X4)
    | r1_lattice3(X1,X2,esk4_3(X1,X2,X3))
    | r2_yellow_0(X1,X2)
    | esk5_3(X1,X2,X3) != k2_yellow_0(X1,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ r2_yellow_0(X1,X4)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_22]),
    [final]).

cnf(c_0_55,plain,
    ( r1_lattice3(X1,X2,esk4_3(X1,X2,X3))
    | r1_lattice3(X1,X4,esk5_3(X1,X2,X3))
    | r2_yellow_0(X1,X2)
    | esk5_3(X1,X2,X3) != k2_yellow_0(X1,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ r2_yellow_0(X1,X4)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_22]),
    [final]).

cnf(c_0_56,plain,
    ( esk5_3(X1,X2,X3) = esk2_2(X1,X4)
    | r2_yellow_0(X1,X2)
    | m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))
    | esk5_3(X1,X2,X3) != k2_yellow_0(X1,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ r2_yellow_0(X1,X4)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_24]),
    [final]).

cnf(c_0_57,plain,
    ( esk5_3(X1,X2,X3) = esk2_2(X1,X4)
    | r2_yellow_0(X1,X2)
    | esk5_3(X1,X2,X3) != k2_yellow_0(X1,X4)
    | ~ r1_orders_2(X1,esk4_3(X1,X2,X3),X3)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ r2_yellow_0(X1,X4)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_26]),
    [final]).

cnf(c_0_58,plain,
    ( esk1_3(X1,X2,X3) = esk2_2(X1,X4)
    | X3 = k2_yellow_0(X1,X2)
    | esk1_3(X1,X2,X3) != k2_yellow_0(X1,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ r2_yellow_0(X1,X4)
    | ~ r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_10]),
    [final]).

cnf(c_0_59,plain,
    ( esk3_3(X1,X2,X3) = esk2_2(X1,X4)
    | X3 = esk2_2(X1,X2)
    | esk3_3(X1,X2,X3) != k2_yellow_0(X1,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ r2_yellow_0(X1,X4)
    | ~ r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_14]),
    [final]).

cnf(c_0_60,plain,
    ( esk6_3(X1,X2,X3) = esk2_2(X1,X4)
    | k2_yellow_0(X1,X2) = k2_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | esk6_3(X1,X2,X3) != k2_yellow_0(X1,X4)
    | ~ r2_yellow_0(X1,X4)
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42]),
    [final]).

cnf(c_0_61,plain,
    ( k2_yellow_0(X1,X2) = esk2_2(X1,X3)
    | k2_yellow_0(X1,X2) != k2_yellow_0(X1,X3)
    | ~ r2_yellow_0(X1,X3)
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_43]),
    [final]).

cnf(c_0_62,plain,
    ( esk2_2(X1,X2) = esk2_2(X1,X3)
    | esk2_2(X1,X2) != k2_yellow_0(X1,X3)
    | ~ r2_yellow_0(X1,X3)
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_8]),
    [final]).

cnf(c_0_63,plain,
    ( X1 = k2_yellow_0(X2,X3)
    | r1_orders_2(X2,esk1_3(X2,X3,X1),X4)
    | X4 != k2_yellow_0(X2,X3)
    | ~ r1_lattice3(X2,X3,X1)
    | ~ r2_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_16]),c_0_10]),
    [final]).

cnf(c_0_64,plain,
    ( r1_lattice3(X1,X2,esk5_3(X1,X3,X4))
    | r2_yellow_0(X1,X3)
    | m1_subset_1(esk4_3(X1,X3,X4),u1_struct_0(X1))
    | esk5_3(X1,X3,X4) != k2_yellow_0(X1,X2)
    | ~ r1_lattice3(X1,X3,X4)
    | ~ r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_24]),
    [final]).

cnf(c_0_65,plain,
    ( k2_yellow_0(X1,X2) = esk2_2(X1,X3)
    | ~ r1_lattice3(X1,X2,esk3_3(X1,X3,k2_yellow_0(X1,X2)))
    | ~ r1_lattice3(X1,X3,k2_yellow_0(X1,X2))
    | ~ r2_yellow_0(X1,X3)
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_29]),
    [final]).

cnf(c_0_66,plain,
    ( k2_yellow_0(X1,X2) = k2_yellow_0(X1,X3)
    | ~ r1_lattice3(X1,X2,esk1_3(X1,X3,k2_yellow_0(X1,X2)))
    | ~ r1_lattice3(X1,X3,k2_yellow_0(X1,X2))
    | ~ r2_yellow_0(X1,X3)
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_29]),
    [final]).

cnf(c_0_67,plain,
    ( r1_lattice3(X1,X2,k2_yellow_0(X1,X3))
    | k2_yellow_0(X1,X3) != k2_yellow_0(X1,X2)
    | ~ r2_yellow_0(X1,X2)
    | ~ r2_yellow_0(X1,X3)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_29]),
    [final]).

cnf(c_0_68,plain,
    ( r1_orders_2(X1,X2,k2_yellow_0(X1,X3))
    | ~ r1_lattice3(X1,X3,X2)
    | ~ r2_yellow_0(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_7,c_0_29]),
    [final]).

cnf(c_0_69,plain,
    ( r1_orders_2(X1,k2_yellow_0(X1,X2),X3)
    | X3 != k2_yellow_0(X1,X2)
    | ~ r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_29]),
    [final]).

cnf(c_0_70,plain,
    ( r1_lattice3(X1,X2,k2_yellow_0(X1,X2))
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_29]),
    [final]).

cnf(c_0_71,plain,
    ( r1_lattice3(X1,X2,esk5_3(X1,X3,X4))
    | r2_yellow_0(X1,X3)
    | esk5_3(X1,X3,X4) != k2_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,esk4_3(X1,X3,X4),X4)
    | ~ r1_lattice3(X1,X3,X4)
    | ~ r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_26]),
    [final]).

cnf(c_0_72,plain,
    ( X1 = esk2_2(X2,X3)
    | r1_lattice3(X2,X4,esk3_3(X2,X3,X1))
    | esk3_3(X2,X3,X1) != k2_yellow_0(X2,X4)
    | ~ r1_lattice3(X2,X3,X1)
    | ~ r2_yellow_0(X2,X4)
    | ~ r2_yellow_0(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_14]),
    [final]).

cnf(c_0_73,plain,
    ( X1 = k2_yellow_0(X2,X3)
    | r1_lattice3(X2,X4,esk1_3(X2,X3,X1))
    | esk1_3(X2,X3,X1) != k2_yellow_0(X2,X4)
    | ~ r1_lattice3(X2,X3,X1)
    | ~ r2_yellow_0(X2,X4)
    | ~ r2_yellow_0(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_10]),
    [final]).

cnf(c_0_74,plain,
    ( k2_yellow_0(X1,X2) = k2_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | r1_lattice3(X1,X4,esk6_3(X1,X2,X3))
    | esk6_3(X1,X2,X3) != k2_yellow_0(X1,X4)
    | ~ r2_yellow_0(X1,X4)
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_42]),
    [final]).

cnf(c_0_75,negated_conjecture,
    ( k2_yellow_0(esk7_0,k4_waybel_0(esk7_0,esk8_0)) = k2_yellow_0(esk7_0,X1)
    | r1_orders_2(esk7_0,esk6_3(esk7_0,k4_waybel_0(esk7_0,esk8_0),X1),X2)
    | r1_lattice3(esk7_0,k4_waybel_0(esk7_0,esk8_0),esk6_3(esk7_0,k4_waybel_0(esk7_0,esk8_0),X1))
    | r2_yellow_0(esk7_0,esk8_0)
    | X2 != k2_yellow_0(esk7_0,X1)
    | ~ r2_yellow_0(esk7_0,X1)
    | ~ m1_subset_1(esk6_3(esk7_0,k4_waybel_0(esk7_0,esk8_0),X1),u1_struct_0(esk7_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_47]),c_0_33])]),
    [final]).

cnf(c_0_76,negated_conjecture,
    ( k2_yellow_0(esk7_0,k4_waybel_0(esk7_0,esk8_0)) = k2_yellow_0(esk7_0,X1)
    | r1_orders_2(esk7_0,esk6_3(esk7_0,k4_waybel_0(esk7_0,esk8_0),X1),X2)
    | r1_lattice3(esk7_0,X1,esk6_3(esk7_0,k4_waybel_0(esk7_0,esk8_0),X1))
    | r2_yellow_0(esk7_0,esk8_0)
    | X2 != k2_yellow_0(esk7_0,k4_waybel_0(esk7_0,esk8_0))
    | ~ m1_subset_1(esk6_3(esk7_0,k4_waybel_0(esk7_0,esk8_0),X1),u1_struct_0(esk7_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_47]),c_0_33])]),c_0_32]),
    [final]).

cnf(c_0_77,plain,
    ( k2_yellow_0(X1,X2) = k2_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,esk6_3(X1,X2,X3))
    | ~ r1_lattice3(X1,X3,esk6_3(X1,X2,X3))
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19]),
    [final]).

cnf(c_0_78,plain,
    ( r1_lattice3(X1,X2,esk5_3(X1,X2,X3))
    | r1_lattice3(X1,X2,esk4_3(X1,X2,X3))
    | r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_79,plain,
    ( r1_lattice3(X1,X2,esk5_3(X1,X2,X3))
    | m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))
    | r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_80,plain,
    ( r1_lattice3(X1,X2,esk5_3(X1,X2,X3))
    | r2_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,esk4_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_81,plain,
    ( r1_lattice3(X1,X2,esk4_3(X1,X2,X3))
    | r2_yellow_0(X1,X2)
    | esk5_3(X1,X2,X3) != X3
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_82,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))
    | r2_yellow_0(X1,X2)
    | esk5_3(X1,X2,X3) != X3
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_83,plain,
    ( r2_yellow_0(X1,X2)
    | esk5_3(X1,X2,X3) != X3
    | ~ r1_orders_2(X1,esk4_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_84,negated_conjecture,
    ( ~ r2_yellow_0(esk7_0,esk8_0)
    | ~ r2_yellow_0(esk7_0,k4_waybel_0(esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20]),
    [final]).

cnf(c_0_85,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20]),
    [final]).

cnf(c_0_86,negated_conjecture,
    ( v4_orders_2(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20]),
    [final]).

cnf(c_0_87,negated_conjecture,
    ( v3_orders_2(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:35:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.40  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.21/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.21/0.40  #
% 0.21/0.40  # Preprocessing time       : 0.039 s
% 0.21/0.40  # Presaturation interreduction done
% 0.21/0.40  
% 0.21/0.40  # No proof found!
% 0.21/0.40  # SZS status CounterSatisfiable
% 0.21/0.40  # SZS output start Saturation
% 0.21/0.40  fof(d10_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_yellow_0(X1,X2)=>(X3=k2_yellow_0(X1,X2)<=>(r1_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X4)=>r1_orders_2(X1,X4,X3)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_yellow_0)).
% 0.21/0.40  fof(d8_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(r2_yellow_0(X1,X2)<=>?[X3]:(((m1_subset_1(X3,u1_struct_0(X1))&r1_lattice3(X1,X2,X3))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X4)=>r1_orders_2(X1,X4,X3))))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r1_lattice3(X1,X2,X4)&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X5)=>r1_orders_2(X1,X5,X4))))=>X4=X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_yellow_0)).
% 0.21/0.40  fof(t37_waybel_0, conjecture, ![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_yellow_0(X1,X2)<=>r2_yellow_0(X1,k4_waybel_0(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_waybel_0)).
% 0.21/0.40  fof(t49_yellow_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2, X3]:((r2_yellow_0(X1,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X4)<=>r1_lattice3(X1,X3,X4))))=>k2_yellow_0(X1,X2)=k2_yellow_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_yellow_0)).
% 0.21/0.40  fof(c_0_4, plain, ![X6, X7, X8, X9]:(((r1_lattice3(X6,X7,X8)|X8!=k2_yellow_0(X6,X7)|~r2_yellow_0(X6,X7)|~m1_subset_1(X8,u1_struct_0(X6))|~l1_orders_2(X6))&(~m1_subset_1(X9,u1_struct_0(X6))|(~r1_lattice3(X6,X7,X9)|r1_orders_2(X6,X9,X8))|X8!=k2_yellow_0(X6,X7)|~r2_yellow_0(X6,X7)|~m1_subset_1(X8,u1_struct_0(X6))|~l1_orders_2(X6)))&((m1_subset_1(esk1_3(X6,X7,X8),u1_struct_0(X6))|~r1_lattice3(X6,X7,X8)|X8=k2_yellow_0(X6,X7)|~r2_yellow_0(X6,X7)|~m1_subset_1(X8,u1_struct_0(X6))|~l1_orders_2(X6))&((r1_lattice3(X6,X7,esk1_3(X6,X7,X8))|~r1_lattice3(X6,X7,X8)|X8=k2_yellow_0(X6,X7)|~r2_yellow_0(X6,X7)|~m1_subset_1(X8,u1_struct_0(X6))|~l1_orders_2(X6))&(~r1_orders_2(X6,esk1_3(X6,X7,X8),X8)|~r1_lattice3(X6,X7,X8)|X8=k2_yellow_0(X6,X7)|~r2_yellow_0(X6,X7)|~m1_subset_1(X8,u1_struct_0(X6))|~l1_orders_2(X6))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_yellow_0])])])])])).
% 0.21/0.40  fof(c_0_5, plain, ![X11, X12, X14, X15, X17, X18, X21]:(((((m1_subset_1(esk2_2(X11,X12),u1_struct_0(X11))|~r2_yellow_0(X11,X12)|~l1_orders_2(X11))&(r1_lattice3(X11,X12,esk2_2(X11,X12))|~r2_yellow_0(X11,X12)|~l1_orders_2(X11)))&(~m1_subset_1(X14,u1_struct_0(X11))|(~r1_lattice3(X11,X12,X14)|r1_orders_2(X11,X14,esk2_2(X11,X12)))|~r2_yellow_0(X11,X12)|~l1_orders_2(X11)))&((m1_subset_1(esk3_3(X11,X12,X15),u1_struct_0(X11))|~r1_lattice3(X11,X12,X15)|X15=esk2_2(X11,X12)|~m1_subset_1(X15,u1_struct_0(X11))|~r2_yellow_0(X11,X12)|~l1_orders_2(X11))&((r1_lattice3(X11,X12,esk3_3(X11,X12,X15))|~r1_lattice3(X11,X12,X15)|X15=esk2_2(X11,X12)|~m1_subset_1(X15,u1_struct_0(X11))|~r2_yellow_0(X11,X12)|~l1_orders_2(X11))&(~r1_orders_2(X11,esk3_3(X11,X12,X15),X15)|~r1_lattice3(X11,X12,X15)|X15=esk2_2(X11,X12)|~m1_subset_1(X15,u1_struct_0(X11))|~r2_yellow_0(X11,X12)|~l1_orders_2(X11)))))&(((m1_subset_1(esk5_3(X11,X17,X18),u1_struct_0(X11))|(m1_subset_1(esk4_3(X11,X17,X18),u1_struct_0(X11))|(~m1_subset_1(X18,u1_struct_0(X11))|~r1_lattice3(X11,X17,X18)))|r2_yellow_0(X11,X17)|~l1_orders_2(X11))&(((r1_lattice3(X11,X17,esk5_3(X11,X17,X18))|(m1_subset_1(esk4_3(X11,X17,X18),u1_struct_0(X11))|(~m1_subset_1(X18,u1_struct_0(X11))|~r1_lattice3(X11,X17,X18)))|r2_yellow_0(X11,X17)|~l1_orders_2(X11))&(~m1_subset_1(X21,u1_struct_0(X11))|(~r1_lattice3(X11,X17,X21)|r1_orders_2(X11,X21,esk5_3(X11,X17,X18)))|(m1_subset_1(esk4_3(X11,X17,X18),u1_struct_0(X11))|(~m1_subset_1(X18,u1_struct_0(X11))|~r1_lattice3(X11,X17,X18)))|r2_yellow_0(X11,X17)|~l1_orders_2(X11)))&(esk5_3(X11,X17,X18)!=X18|(m1_subset_1(esk4_3(X11,X17,X18),u1_struct_0(X11))|(~m1_subset_1(X18,u1_struct_0(X11))|~r1_lattice3(X11,X17,X18)))|r2_yellow_0(X11,X17)|~l1_orders_2(X11))))&(((m1_subset_1(esk5_3(X11,X17,X18),u1_struct_0(X11))|(r1_lattice3(X11,X17,esk4_3(X11,X17,X18))|(~m1_subset_1(X18,u1_struct_0(X11))|~r1_lattice3(X11,X17,X18)))|r2_yellow_0(X11,X17)|~l1_orders_2(X11))&(((r1_lattice3(X11,X17,esk5_3(X11,X17,X18))|(r1_lattice3(X11,X17,esk4_3(X11,X17,X18))|(~m1_subset_1(X18,u1_struct_0(X11))|~r1_lattice3(X11,X17,X18)))|r2_yellow_0(X11,X17)|~l1_orders_2(X11))&(~m1_subset_1(X21,u1_struct_0(X11))|(~r1_lattice3(X11,X17,X21)|r1_orders_2(X11,X21,esk5_3(X11,X17,X18)))|(r1_lattice3(X11,X17,esk4_3(X11,X17,X18))|(~m1_subset_1(X18,u1_struct_0(X11))|~r1_lattice3(X11,X17,X18)))|r2_yellow_0(X11,X17)|~l1_orders_2(X11)))&(esk5_3(X11,X17,X18)!=X18|(r1_lattice3(X11,X17,esk4_3(X11,X17,X18))|(~m1_subset_1(X18,u1_struct_0(X11))|~r1_lattice3(X11,X17,X18)))|r2_yellow_0(X11,X17)|~l1_orders_2(X11))))&((m1_subset_1(esk5_3(X11,X17,X18),u1_struct_0(X11))|(~r1_orders_2(X11,esk4_3(X11,X17,X18),X18)|(~m1_subset_1(X18,u1_struct_0(X11))|~r1_lattice3(X11,X17,X18)))|r2_yellow_0(X11,X17)|~l1_orders_2(X11))&(((r1_lattice3(X11,X17,esk5_3(X11,X17,X18))|(~r1_orders_2(X11,esk4_3(X11,X17,X18),X18)|(~m1_subset_1(X18,u1_struct_0(X11))|~r1_lattice3(X11,X17,X18)))|r2_yellow_0(X11,X17)|~l1_orders_2(X11))&(~m1_subset_1(X21,u1_struct_0(X11))|(~r1_lattice3(X11,X17,X21)|r1_orders_2(X11,X21,esk5_3(X11,X17,X18)))|(~r1_orders_2(X11,esk4_3(X11,X17,X18),X18)|(~m1_subset_1(X18,u1_struct_0(X11))|~r1_lattice3(X11,X17,X18)))|r2_yellow_0(X11,X17)|~l1_orders_2(X11)))&(esk5_3(X11,X17,X18)!=X18|(~r1_orders_2(X11,esk4_3(X11,X17,X18),X18)|(~m1_subset_1(X18,u1_struct_0(X11))|~r1_lattice3(X11,X17,X18)))|r2_yellow_0(X11,X17)|~l1_orders_2(X11))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_yellow_0])])])])])])).
% 0.21/0.40  cnf(c_0_6, plain, (X3=k2_yellow_0(X1,X2)|~r1_orders_2(X1,esk1_3(X1,X2,X3),X3)|~r1_lattice3(X1,X2,X3)|~r2_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.21/0.40  cnf(c_0_7, plain, (r1_orders_2(X2,X1,esk2_2(X2,X3))|~m1_subset_1(X1,u1_struct_0(X2))|~r1_lattice3(X2,X3,X1)|~r2_yellow_0(X2,X3)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.21/0.40  cnf(c_0_8, plain, (m1_subset_1(esk2_2(X1,X2),u1_struct_0(X1))|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.21/0.40  cnf(c_0_9, plain, (esk2_2(X1,X2)=k2_yellow_0(X1,X3)|~r1_lattice3(X1,X2,esk1_3(X1,X3,esk2_2(X1,X2)))|~r1_lattice3(X1,X3,esk2_2(X1,X2))|~r2_yellow_0(X1,X3)|~r2_yellow_0(X1,X2)|~m1_subset_1(esk1_3(X1,X3,esk2_2(X1,X2)),u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_6, c_0_7]), c_0_8])).
% 0.21/0.40  cnf(c_0_10, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|X3=k2_yellow_0(X1,X2)|~r1_lattice3(X1,X2,X3)|~r2_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.21/0.40  fof(c_0_11, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_yellow_0(X1,X2)<=>r2_yellow_0(X1,k4_waybel_0(X1,X2)))))), inference(assume_negation,[status(cth)],[t37_waybel_0])).
% 0.21/0.40  cnf(c_0_12, plain, (r1_orders_2(X2,X1,X4)|~m1_subset_1(X1,u1_struct_0(X2))|~r1_lattice3(X2,X3,X1)|X4!=k2_yellow_0(X2,X3)|~r2_yellow_0(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.21/0.40  cnf(c_0_13, plain, (r1_lattice3(X1,X2,esk3_3(X1,X2,X3))|X3=esk2_2(X1,X2)|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.21/0.40  cnf(c_0_14, plain, (m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))|X3=esk2_2(X1,X2)|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.21/0.40  cnf(c_0_15, plain, (esk2_2(X1,X2)=k2_yellow_0(X1,X3)|~r1_lattice3(X1,X2,esk1_3(X1,X3,esk2_2(X1,X2)))|~r1_lattice3(X1,X3,esk2_2(X1,X2))|~r2_yellow_0(X1,X3)|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_8]), ['final']).
% 0.21/0.40  cnf(c_0_16, plain, (r1_lattice3(X1,X2,esk1_3(X1,X2,X3))|X3=k2_yellow_0(X1,X2)|~r1_lattice3(X1,X2,X3)|~r2_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.21/0.40  cnf(c_0_17, plain, (r1_lattice3(X1,X2,esk2_2(X1,X2))|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.21/0.40  cnf(c_0_18, plain, (X3=esk2_2(X1,X2)|~r1_orders_2(X1,esk3_3(X1,X2,X3),X3)|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.21/0.40  fof(c_0_19, plain, ![X22, X23, X24]:((m1_subset_1(esk6_3(X22,X23,X24),u1_struct_0(X22))|~r2_yellow_0(X22,X23)|k2_yellow_0(X22,X23)=k2_yellow_0(X22,X24)|(v2_struct_0(X22)|~l1_orders_2(X22)))&((~r1_lattice3(X22,X23,esk6_3(X22,X23,X24))|~r1_lattice3(X22,X24,esk6_3(X22,X23,X24))|~r2_yellow_0(X22,X23)|k2_yellow_0(X22,X23)=k2_yellow_0(X22,X24)|(v2_struct_0(X22)|~l1_orders_2(X22)))&(r1_lattice3(X22,X23,esk6_3(X22,X23,X24))|r1_lattice3(X22,X24,esk6_3(X22,X23,X24))|~r2_yellow_0(X22,X23)|k2_yellow_0(X22,X23)=k2_yellow_0(X22,X24)|(v2_struct_0(X22)|~l1_orders_2(X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_yellow_0])])])])])])).
% 0.21/0.40  fof(c_0_20, negated_conjecture, ((((~v2_struct_0(esk7_0)&v3_orders_2(esk7_0))&v4_orders_2(esk7_0))&l1_orders_2(esk7_0))&(m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0)))&((~r2_yellow_0(esk7_0,esk8_0)|~r2_yellow_0(esk7_0,k4_waybel_0(esk7_0,esk8_0)))&(r2_yellow_0(esk7_0,esk8_0)|r2_yellow_0(esk7_0,k4_waybel_0(esk7_0,esk8_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).
% 0.21/0.40  cnf(c_0_21, plain, (r1_orders_2(X2,X1,esk5_3(X2,X3,X4))|r1_lattice3(X2,X3,esk4_3(X2,X3,X4))|r2_yellow_0(X2,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~r1_lattice3(X2,X3,X1)|~m1_subset_1(X4,u1_struct_0(X2))|~r1_lattice3(X2,X3,X4)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.21/0.40  cnf(c_0_22, plain, (m1_subset_1(esk5_3(X1,X2,X3),u1_struct_0(X1))|r1_lattice3(X1,X2,esk4_3(X1,X2,X3))|r2_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~r1_lattice3(X1,X2,X3)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.21/0.40  cnf(c_0_23, plain, (r1_orders_2(X2,X1,esk5_3(X2,X3,X4))|m1_subset_1(esk4_3(X2,X3,X4),u1_struct_0(X2))|r2_yellow_0(X2,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~r1_lattice3(X2,X3,X1)|~m1_subset_1(X4,u1_struct_0(X2))|~r1_lattice3(X2,X3,X4)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.21/0.40  cnf(c_0_24, plain, (m1_subset_1(esk5_3(X1,X2,X3),u1_struct_0(X1))|m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))|r2_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~r1_lattice3(X1,X2,X3)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.21/0.40  cnf(c_0_25, plain, (r1_orders_2(X2,X1,esk5_3(X2,X3,X4))|r2_yellow_0(X2,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~r1_lattice3(X2,X3,X1)|~r1_orders_2(X2,esk4_3(X2,X3,X4),X4)|~m1_subset_1(X4,u1_struct_0(X2))|~r1_lattice3(X2,X3,X4)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.21/0.40  cnf(c_0_26, plain, (m1_subset_1(esk5_3(X1,X2,X3),u1_struct_0(X1))|r2_yellow_0(X1,X2)|~r1_orders_2(X1,esk4_3(X1,X2,X3),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~r1_lattice3(X1,X2,X3)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.21/0.40  cnf(c_0_27, plain, (X1=esk2_2(X2,X3)|r1_orders_2(X2,esk3_3(X2,X3,X1),X4)|X4!=k2_yellow_0(X2,X3)|~r1_lattice3(X2,X3,X1)|~r2_yellow_0(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~l1_orders_2(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14]), ['final']).
% 0.21/0.40  cnf(c_0_28, plain, (r1_lattice3(X1,X2,X3)|X3!=k2_yellow_0(X1,X2)|~r2_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.21/0.40  cnf(c_0_29, plain, (esk2_2(X1,X2)=k2_yellow_0(X1,X2)|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_8]), c_0_17]), ['final']).
% 0.21/0.40  cnf(c_0_30, plain, (esk2_2(X1,X2)=esk2_2(X1,X3)|~r1_lattice3(X1,X2,esk3_3(X1,X3,esk2_2(X1,X2)))|~r1_lattice3(X1,X3,esk2_2(X1,X2))|~r2_yellow_0(X1,X3)|~r2_yellow_0(X1,X2)|~m1_subset_1(esk3_3(X1,X3,esk2_2(X1,X2)),u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_7]), c_0_8])).
% 0.21/0.40  cnf(c_0_31, plain, (r1_lattice3(X1,X2,esk6_3(X1,X2,X3))|r1_lattice3(X1,X3,esk6_3(X1,X2,X3))|k2_yellow_0(X1,X2)=k2_yellow_0(X1,X3)|v2_struct_0(X1)|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_19]), ['final']).
% 0.21/0.40  cnf(c_0_32, negated_conjecture, (r2_yellow_0(esk7_0,esk8_0)|r2_yellow_0(esk7_0,k4_waybel_0(esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_20]), ['final']).
% 0.21/0.40  cnf(c_0_33, negated_conjecture, (l1_orders_2(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_20]), ['final']).
% 0.21/0.40  cnf(c_0_34, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_20]), ['final']).
% 0.21/0.40  cnf(c_0_35, plain, (esk5_3(X1,X2,X3)=k2_yellow_0(X1,X4)|r1_lattice3(X1,X2,esk4_3(X1,X2,X3))|r2_yellow_0(X1,X2)|~r1_lattice3(X1,X2,esk1_3(X1,X4,esk5_3(X1,X2,X3)))|~r1_lattice3(X1,X4,esk5_3(X1,X2,X3))|~r1_lattice3(X1,X2,X3)|~r2_yellow_0(X1,X4)|~m1_subset_1(esk1_3(X1,X4,esk5_3(X1,X2,X3)),u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_6, c_0_21]), c_0_22])).
% 0.21/0.40  cnf(c_0_36, plain, (esk5_3(X1,X2,X3)=esk2_2(X1,X4)|r1_lattice3(X1,X2,esk4_3(X1,X2,X3))|r2_yellow_0(X1,X2)|~r1_lattice3(X1,X2,esk3_3(X1,X4,esk5_3(X1,X2,X3)))|~r1_lattice3(X1,X4,esk5_3(X1,X2,X3))|~r1_lattice3(X1,X2,X3)|~r2_yellow_0(X1,X4)|~m1_subset_1(esk3_3(X1,X4,esk5_3(X1,X2,X3)),u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_21]), c_0_22])).
% 0.21/0.40  cnf(c_0_37, plain, (esk5_3(X1,X2,X3)=k2_yellow_0(X1,X4)|r2_yellow_0(X1,X2)|m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))|~r1_lattice3(X1,X2,esk1_3(X1,X4,esk5_3(X1,X2,X3)))|~r1_lattice3(X1,X4,esk5_3(X1,X2,X3))|~r1_lattice3(X1,X2,X3)|~r2_yellow_0(X1,X4)|~m1_subset_1(esk1_3(X1,X4,esk5_3(X1,X2,X3)),u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_6, c_0_23]), c_0_24])).
% 0.21/0.40  cnf(c_0_38, plain, (esk5_3(X1,X2,X3)=k2_yellow_0(X1,X4)|r2_yellow_0(X1,X2)|~r1_orders_2(X1,esk4_3(X1,X2,X3),X3)|~r1_lattice3(X1,X2,esk1_3(X1,X4,esk5_3(X1,X2,X3)))|~r1_lattice3(X1,X4,esk5_3(X1,X2,X3))|~r1_lattice3(X1,X2,X3)|~r2_yellow_0(X1,X4)|~m1_subset_1(esk1_3(X1,X4,esk5_3(X1,X2,X3)),u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_6, c_0_25]), c_0_26])).
% 0.21/0.40  cnf(c_0_39, plain, (esk5_3(X1,X2,X3)=esk2_2(X1,X4)|r2_yellow_0(X1,X2)|m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))|~r1_lattice3(X1,X2,esk3_3(X1,X4,esk5_3(X1,X2,X3)))|~r1_lattice3(X1,X4,esk5_3(X1,X2,X3))|~r1_lattice3(X1,X2,X3)|~r2_yellow_0(X1,X4)|~m1_subset_1(esk3_3(X1,X4,esk5_3(X1,X2,X3)),u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_23]), c_0_24])).
% 0.21/0.40  cnf(c_0_40, plain, (esk5_3(X1,X2,X3)=esk2_2(X1,X4)|r2_yellow_0(X1,X2)|~r1_orders_2(X1,esk4_3(X1,X2,X3),X3)|~r1_lattice3(X1,X2,esk3_3(X1,X4,esk5_3(X1,X2,X3)))|~r1_lattice3(X1,X4,esk5_3(X1,X2,X3))|~r1_lattice3(X1,X2,X3)|~r2_yellow_0(X1,X4)|~m1_subset_1(esk3_3(X1,X4,esk5_3(X1,X2,X3)),u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_25]), c_0_26])).
% 0.21/0.40  cnf(c_0_41, plain, (X1=esk2_2(X2,X3)|X1!=k2_yellow_0(X2,X3)|~r2_yellow_0(X2,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~l1_orders_2(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_27]), c_0_28]), ['final']).
% 0.21/0.40  cnf(c_0_42, plain, (m1_subset_1(esk6_3(X1,X2,X3),u1_struct_0(X1))|k2_yellow_0(X1,X2)=k2_yellow_0(X1,X3)|v2_struct_0(X1)|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_19]), ['final']).
% 0.21/0.40  cnf(c_0_43, plain, (m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1))|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_8, c_0_29]), ['final']).
% 0.21/0.40  cnf(c_0_44, plain, (esk2_2(X1,X2)=esk2_2(X1,X3)|~r1_lattice3(X1,X2,esk3_3(X1,X3,esk2_2(X1,X2)))|~r1_lattice3(X1,X3,esk2_2(X1,X2))|~r2_yellow_0(X1,X3)|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_14]), c_0_8]), ['final']).
% 0.21/0.40  cnf(c_0_45, plain, (r1_lattice3(X1,X2,esk2_2(X1,X3))|esk2_2(X1,X3)!=k2_yellow_0(X1,X2)|~r2_yellow_0(X1,X2)|~r2_yellow_0(X1,X3)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_28, c_0_8]), ['final']).
% 0.21/0.40  cnf(c_0_46, plain, (r1_orders_2(X1,esk2_2(X1,X2),X3)|X3!=k2_yellow_0(X1,X2)|~r2_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_17]), c_0_8]), ['final']).
% 0.21/0.40  cnf(c_0_47, negated_conjecture, (k2_yellow_0(esk7_0,k4_waybel_0(esk7_0,esk8_0))=k2_yellow_0(esk7_0,X1)|r1_lattice3(esk7_0,k4_waybel_0(esk7_0,esk8_0),esk6_3(esk7_0,k4_waybel_0(esk7_0,esk8_0),X1))|r1_lattice3(esk7_0,X1,esk6_3(esk7_0,k4_waybel_0(esk7_0,esk8_0),X1))|r2_yellow_0(esk7_0,esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])]), c_0_34]), ['final']).
% 0.21/0.40  cnf(c_0_48, plain, (esk5_3(X1,X2,X3)=k2_yellow_0(X1,X4)|r1_lattice3(X1,X2,esk4_3(X1,X2,X3))|r2_yellow_0(X1,X2)|~r1_lattice3(X1,X2,esk1_3(X1,X4,esk5_3(X1,X2,X3)))|~r1_lattice3(X1,X4,esk5_3(X1,X2,X3))|~r1_lattice3(X1,X2,X3)|~r2_yellow_0(X1,X4)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_10]), c_0_22]), ['final']).
% 0.21/0.40  cnf(c_0_49, plain, (esk5_3(X1,X2,X3)=esk2_2(X1,X4)|r1_lattice3(X1,X2,esk4_3(X1,X2,X3))|r2_yellow_0(X1,X2)|~r1_lattice3(X1,X2,esk3_3(X1,X4,esk5_3(X1,X2,X3)))|~r1_lattice3(X1,X4,esk5_3(X1,X2,X3))|~r1_lattice3(X1,X2,X3)|~r2_yellow_0(X1,X4)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_14]), c_0_22]), ['final']).
% 0.21/0.40  cnf(c_0_50, plain, (esk5_3(X1,X2,X3)=k2_yellow_0(X1,X4)|r2_yellow_0(X1,X2)|m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))|~r1_lattice3(X1,X2,esk1_3(X1,X4,esk5_3(X1,X2,X3)))|~r1_lattice3(X1,X4,esk5_3(X1,X2,X3))|~r1_lattice3(X1,X2,X3)|~r2_yellow_0(X1,X4)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_10]), c_0_24]), ['final']).
% 0.21/0.40  cnf(c_0_51, plain, (esk5_3(X1,X2,X3)=k2_yellow_0(X1,X4)|r2_yellow_0(X1,X2)|~r1_orders_2(X1,esk4_3(X1,X2,X3),X3)|~r1_lattice3(X1,X2,esk1_3(X1,X4,esk5_3(X1,X2,X3)))|~r1_lattice3(X1,X4,esk5_3(X1,X2,X3))|~r1_lattice3(X1,X2,X3)|~r2_yellow_0(X1,X4)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_10]), c_0_26]), ['final']).
% 0.21/0.40  cnf(c_0_52, plain, (esk5_3(X1,X2,X3)=esk2_2(X1,X4)|r2_yellow_0(X1,X2)|m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))|~r1_lattice3(X1,X2,esk3_3(X1,X4,esk5_3(X1,X2,X3)))|~r1_lattice3(X1,X4,esk5_3(X1,X2,X3))|~r1_lattice3(X1,X2,X3)|~r2_yellow_0(X1,X4)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_14]), c_0_24]), ['final']).
% 0.21/0.40  cnf(c_0_53, plain, (esk5_3(X1,X2,X3)=esk2_2(X1,X4)|r2_yellow_0(X1,X2)|~r1_orders_2(X1,esk4_3(X1,X2,X3),X3)|~r1_lattice3(X1,X2,esk3_3(X1,X4,esk5_3(X1,X2,X3)))|~r1_lattice3(X1,X4,esk5_3(X1,X2,X3))|~r1_lattice3(X1,X2,X3)|~r2_yellow_0(X1,X4)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_14]), c_0_26]), ['final']).
% 0.21/0.40  cnf(c_0_54, plain, (esk5_3(X1,X2,X3)=esk2_2(X1,X4)|r1_lattice3(X1,X2,esk4_3(X1,X2,X3))|r2_yellow_0(X1,X2)|esk5_3(X1,X2,X3)!=k2_yellow_0(X1,X4)|~r1_lattice3(X1,X2,X3)|~r2_yellow_0(X1,X4)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_41, c_0_22]), ['final']).
% 0.21/0.40  cnf(c_0_55, plain, (r1_lattice3(X1,X2,esk4_3(X1,X2,X3))|r1_lattice3(X1,X4,esk5_3(X1,X2,X3))|r2_yellow_0(X1,X2)|esk5_3(X1,X2,X3)!=k2_yellow_0(X1,X4)|~r1_lattice3(X1,X2,X3)|~r2_yellow_0(X1,X4)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_28, c_0_22]), ['final']).
% 0.21/0.40  cnf(c_0_56, plain, (esk5_3(X1,X2,X3)=esk2_2(X1,X4)|r2_yellow_0(X1,X2)|m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))|esk5_3(X1,X2,X3)!=k2_yellow_0(X1,X4)|~r1_lattice3(X1,X2,X3)|~r2_yellow_0(X1,X4)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_41, c_0_24]), ['final']).
% 0.21/0.40  cnf(c_0_57, plain, (esk5_3(X1,X2,X3)=esk2_2(X1,X4)|r2_yellow_0(X1,X2)|esk5_3(X1,X2,X3)!=k2_yellow_0(X1,X4)|~r1_orders_2(X1,esk4_3(X1,X2,X3),X3)|~r1_lattice3(X1,X2,X3)|~r2_yellow_0(X1,X4)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_41, c_0_26]), ['final']).
% 0.21/0.40  cnf(c_0_58, plain, (esk1_3(X1,X2,X3)=esk2_2(X1,X4)|X3=k2_yellow_0(X1,X2)|esk1_3(X1,X2,X3)!=k2_yellow_0(X1,X4)|~r1_lattice3(X1,X2,X3)|~r2_yellow_0(X1,X4)|~r2_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_41, c_0_10]), ['final']).
% 0.21/0.40  cnf(c_0_59, plain, (esk3_3(X1,X2,X3)=esk2_2(X1,X4)|X3=esk2_2(X1,X2)|esk3_3(X1,X2,X3)!=k2_yellow_0(X1,X4)|~r1_lattice3(X1,X2,X3)|~r2_yellow_0(X1,X4)|~r2_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_41, c_0_14]), ['final']).
% 0.21/0.40  cnf(c_0_60, plain, (esk6_3(X1,X2,X3)=esk2_2(X1,X4)|k2_yellow_0(X1,X2)=k2_yellow_0(X1,X3)|v2_struct_0(X1)|esk6_3(X1,X2,X3)!=k2_yellow_0(X1,X4)|~r2_yellow_0(X1,X4)|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_41, c_0_42]), ['final']).
% 0.21/0.40  cnf(c_0_61, plain, (k2_yellow_0(X1,X2)=esk2_2(X1,X3)|k2_yellow_0(X1,X2)!=k2_yellow_0(X1,X3)|~r2_yellow_0(X1,X3)|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_41, c_0_43]), ['final']).
% 0.21/0.40  cnf(c_0_62, plain, (esk2_2(X1,X2)=esk2_2(X1,X3)|esk2_2(X1,X2)!=k2_yellow_0(X1,X3)|~r2_yellow_0(X1,X3)|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_41, c_0_8]), ['final']).
% 0.21/0.40  cnf(c_0_63, plain, (X1=k2_yellow_0(X2,X3)|r1_orders_2(X2,esk1_3(X2,X3,X1),X4)|X4!=k2_yellow_0(X2,X3)|~r1_lattice3(X2,X3,X1)|~r2_yellow_0(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~l1_orders_2(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_16]), c_0_10]), ['final']).
% 0.21/0.40  cnf(c_0_64, plain, (r1_lattice3(X1,X2,esk5_3(X1,X3,X4))|r2_yellow_0(X1,X3)|m1_subset_1(esk4_3(X1,X3,X4),u1_struct_0(X1))|esk5_3(X1,X3,X4)!=k2_yellow_0(X1,X2)|~r1_lattice3(X1,X3,X4)|~r2_yellow_0(X1,X2)|~m1_subset_1(X4,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_28, c_0_24]), ['final']).
% 0.21/0.40  cnf(c_0_65, plain, (k2_yellow_0(X1,X2)=esk2_2(X1,X3)|~r1_lattice3(X1,X2,esk3_3(X1,X3,k2_yellow_0(X1,X2)))|~r1_lattice3(X1,X3,k2_yellow_0(X1,X2))|~r2_yellow_0(X1,X3)|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_44, c_0_29]), ['final']).
% 0.21/0.40  cnf(c_0_66, plain, (k2_yellow_0(X1,X2)=k2_yellow_0(X1,X3)|~r1_lattice3(X1,X2,esk1_3(X1,X3,k2_yellow_0(X1,X2)))|~r1_lattice3(X1,X3,k2_yellow_0(X1,X2))|~r2_yellow_0(X1,X3)|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_15, c_0_29]), ['final']).
% 0.21/0.40  cnf(c_0_67, plain, (r1_lattice3(X1,X2,k2_yellow_0(X1,X3))|k2_yellow_0(X1,X3)!=k2_yellow_0(X1,X2)|~r2_yellow_0(X1,X2)|~r2_yellow_0(X1,X3)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_45, c_0_29]), ['final']).
% 0.21/0.40  cnf(c_0_68, plain, (r1_orders_2(X1,X2,k2_yellow_0(X1,X3))|~r1_lattice3(X1,X3,X2)|~r2_yellow_0(X1,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_7, c_0_29]), ['final']).
% 0.21/0.40  cnf(c_0_69, plain, (r1_orders_2(X1,k2_yellow_0(X1,X2),X3)|X3!=k2_yellow_0(X1,X2)|~r2_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_46, c_0_29]), ['final']).
% 0.21/0.40  cnf(c_0_70, plain, (r1_lattice3(X1,X2,k2_yellow_0(X1,X2))|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_17, c_0_29]), ['final']).
% 0.21/0.40  cnf(c_0_71, plain, (r1_lattice3(X1,X2,esk5_3(X1,X3,X4))|r2_yellow_0(X1,X3)|esk5_3(X1,X3,X4)!=k2_yellow_0(X1,X2)|~r1_orders_2(X1,esk4_3(X1,X3,X4),X4)|~r1_lattice3(X1,X3,X4)|~r2_yellow_0(X1,X2)|~m1_subset_1(X4,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_28, c_0_26]), ['final']).
% 0.21/0.40  cnf(c_0_72, plain, (X1=esk2_2(X2,X3)|r1_lattice3(X2,X4,esk3_3(X2,X3,X1))|esk3_3(X2,X3,X1)!=k2_yellow_0(X2,X4)|~r1_lattice3(X2,X3,X1)|~r2_yellow_0(X2,X4)|~r2_yellow_0(X2,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~l1_orders_2(X2)), inference(spm,[status(thm)],[c_0_28, c_0_14]), ['final']).
% 0.21/0.40  cnf(c_0_73, plain, (X1=k2_yellow_0(X2,X3)|r1_lattice3(X2,X4,esk1_3(X2,X3,X1))|esk1_3(X2,X3,X1)!=k2_yellow_0(X2,X4)|~r1_lattice3(X2,X3,X1)|~r2_yellow_0(X2,X4)|~r2_yellow_0(X2,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~l1_orders_2(X2)), inference(spm,[status(thm)],[c_0_28, c_0_10]), ['final']).
% 0.21/0.40  cnf(c_0_74, plain, (k2_yellow_0(X1,X2)=k2_yellow_0(X1,X3)|v2_struct_0(X1)|r1_lattice3(X1,X4,esk6_3(X1,X2,X3))|esk6_3(X1,X2,X3)!=k2_yellow_0(X1,X4)|~r2_yellow_0(X1,X4)|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_28, c_0_42]), ['final']).
% 0.21/0.40  cnf(c_0_75, negated_conjecture, (k2_yellow_0(esk7_0,k4_waybel_0(esk7_0,esk8_0))=k2_yellow_0(esk7_0,X1)|r1_orders_2(esk7_0,esk6_3(esk7_0,k4_waybel_0(esk7_0,esk8_0),X1),X2)|r1_lattice3(esk7_0,k4_waybel_0(esk7_0,esk8_0),esk6_3(esk7_0,k4_waybel_0(esk7_0,esk8_0),X1))|r2_yellow_0(esk7_0,esk8_0)|X2!=k2_yellow_0(esk7_0,X1)|~r2_yellow_0(esk7_0,X1)|~m1_subset_1(esk6_3(esk7_0,k4_waybel_0(esk7_0,esk8_0),X1),u1_struct_0(esk7_0))|~m1_subset_1(X2,u1_struct_0(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_47]), c_0_33])]), ['final']).
% 0.21/0.40  cnf(c_0_76, negated_conjecture, (k2_yellow_0(esk7_0,k4_waybel_0(esk7_0,esk8_0))=k2_yellow_0(esk7_0,X1)|r1_orders_2(esk7_0,esk6_3(esk7_0,k4_waybel_0(esk7_0,esk8_0),X1),X2)|r1_lattice3(esk7_0,X1,esk6_3(esk7_0,k4_waybel_0(esk7_0,esk8_0),X1))|r2_yellow_0(esk7_0,esk8_0)|X2!=k2_yellow_0(esk7_0,k4_waybel_0(esk7_0,esk8_0))|~m1_subset_1(esk6_3(esk7_0,k4_waybel_0(esk7_0,esk8_0),X1),u1_struct_0(esk7_0))|~m1_subset_1(X2,u1_struct_0(esk7_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_47]), c_0_33])]), c_0_32]), ['final']).
% 0.21/0.40  cnf(c_0_77, plain, (k2_yellow_0(X1,X2)=k2_yellow_0(X1,X3)|v2_struct_0(X1)|~r1_lattice3(X1,X2,esk6_3(X1,X2,X3))|~r1_lattice3(X1,X3,esk6_3(X1,X2,X3))|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_19]), ['final']).
% 0.21/0.40  cnf(c_0_78, plain, (r1_lattice3(X1,X2,esk5_3(X1,X2,X3))|r1_lattice3(X1,X2,esk4_3(X1,X2,X3))|r2_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~r1_lattice3(X1,X2,X3)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.21/0.40  cnf(c_0_79, plain, (r1_lattice3(X1,X2,esk5_3(X1,X2,X3))|m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))|r2_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~r1_lattice3(X1,X2,X3)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.21/0.40  cnf(c_0_80, plain, (r1_lattice3(X1,X2,esk5_3(X1,X2,X3))|r2_yellow_0(X1,X2)|~r1_orders_2(X1,esk4_3(X1,X2,X3),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~r1_lattice3(X1,X2,X3)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.21/0.40  cnf(c_0_81, plain, (r1_lattice3(X1,X2,esk4_3(X1,X2,X3))|r2_yellow_0(X1,X2)|esk5_3(X1,X2,X3)!=X3|~m1_subset_1(X3,u1_struct_0(X1))|~r1_lattice3(X1,X2,X3)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.21/0.40  cnf(c_0_82, plain, (m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))|r2_yellow_0(X1,X2)|esk5_3(X1,X2,X3)!=X3|~m1_subset_1(X3,u1_struct_0(X1))|~r1_lattice3(X1,X2,X3)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.21/0.40  cnf(c_0_83, plain, (r2_yellow_0(X1,X2)|esk5_3(X1,X2,X3)!=X3|~r1_orders_2(X1,esk4_3(X1,X2,X3),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~r1_lattice3(X1,X2,X3)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.21/0.40  cnf(c_0_84, negated_conjecture, (~r2_yellow_0(esk7_0,esk8_0)|~r2_yellow_0(esk7_0,k4_waybel_0(esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_20]), ['final']).
% 0.21/0.40  cnf(c_0_85, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_20]), ['final']).
% 0.21/0.40  cnf(c_0_86, negated_conjecture, (v4_orders_2(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_20]), ['final']).
% 0.21/0.40  cnf(c_0_87, negated_conjecture, (v3_orders_2(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_20]), ['final']).
% 0.21/0.40  # SZS output end Saturation
% 0.21/0.40  # Proof object total steps             : 88
% 0.21/0.40  # Proof object clause steps            : 79
% 0.21/0.40  # Proof object formula steps           : 9
% 0.21/0.40  # Proof object conjectures             : 13
% 0.21/0.40  # Proof object clause conjectures      : 10
% 0.21/0.40  # Proof object formula conjectures     : 3
% 0.21/0.40  # Proof object initial clauses used    : 33
% 0.21/0.40  # Proof object initial formulas used   : 4
% 0.21/0.40  # Proof object generating inferences   : 46
% 0.21/0.40  # Proof object simplifying inferences  : 30
% 0.21/0.40  # Parsed axioms                        : 4
% 0.21/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.40  # Initial clauses                      : 33
% 0.21/0.40  # Removed in clause preprocessing      : 0
% 0.21/0.40  # Initial clauses in saturation        : 33
% 0.21/0.40  # Processed clauses                    : 120
% 0.21/0.40  # ...of these trivial                  : 0
% 0.21/0.40  # ...subsumed                          : 8
% 0.21/0.40  # ...remaining for further processing  : 112
% 0.21/0.40  # Other redundant clauses eliminated   : 0
% 0.21/0.40  # Clauses deleted for lack of memory   : 0
% 0.21/0.40  # Backward-subsumed                    : 8
% 0.21/0.40  # Backward-rewritten                   : 0
% 0.21/0.40  # Generated clauses                    : 69
% 0.21/0.40  # ...of the previous two non-trivial   : 55
% 0.21/0.40  # Contextual simplify-reflections      : 23
% 0.21/0.40  # Paramodulations                      : 65
% 0.21/0.40  # Factorizations                       : 2
% 0.21/0.40  # Equation resolutions                 : 2
% 0.21/0.40  # Propositional unsat checks           : 0
% 0.21/0.40  #    Propositional check models        : 0
% 0.21/0.40  #    Propositional check unsatisfiable : 0
% 0.21/0.40  #    Propositional clauses             : 0
% 0.21/0.40  #    Propositional clauses after purity: 0
% 0.21/0.40  #    Propositional unsat core size     : 0
% 0.21/0.40  #    Propositional preprocessing time  : 0.000
% 0.21/0.40  #    Propositional encoding time       : 0.000
% 0.21/0.40  #    Propositional solver time         : 0.000
% 0.21/0.40  #    Success case prop preproc time    : 0.000
% 0.21/0.40  #    Success case prop encoding time   : 0.000
% 0.21/0.40  #    Success case prop solver time     : 0.000
% 0.21/0.40  # Current number of processed clauses  : 71
% 0.21/0.40  #    Positive orientable unit clauses  : 4
% 0.21/0.40  #    Positive unorientable unit clauses: 0
% 0.21/0.40  #    Negative unit clauses             : 1
% 0.21/0.40  #    Non-unit-clauses                  : 66
% 0.21/0.40  # Current number of unprocessed clauses: 0
% 0.21/0.40  # ...number of literals in the above   : 0
% 0.21/0.40  # Current number of archived formulas  : 0
% 0.21/0.40  # Current number of archived clauses   : 41
% 0.21/0.40  # Clause-clause subsumption calls (NU) : 1644
% 0.21/0.40  # Rec. Clause-clause subsumption calls : 119
% 0.21/0.40  # Non-unit clause-clause subsumptions  : 39
% 0.21/0.40  # Unit Clause-clause subsumption calls : 0
% 0.21/0.40  # Rewrite failures with RHS unbound    : 0
% 0.21/0.40  # BW rewrite match attempts            : 0
% 0.21/0.40  # BW rewrite match successes           : 0
% 0.21/0.40  # Condensation attempts                : 0
% 0.21/0.40  # Condensation successes               : 0
% 0.21/0.40  # Termbank termtop insertions          : 6543
% 0.21/0.40  
% 0.21/0.40  # -------------------------------------------------
% 0.21/0.40  # User time                : 0.052 s
% 0.21/0.40  # System time              : 0.004 s
% 0.21/0.40  # Total time               : 0.056 s
% 0.21/0.40  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
