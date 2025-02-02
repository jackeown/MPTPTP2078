%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:35 EST 2020

% Result     : CounterSatisfiable 0.14s
% Output     : Saturation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 595 expanded)
%              Number of clauses        :   70 ( 241 expanded)
%              Number of leaves         :    3 ( 173 expanded)
%              Depth                    :    7
%              Number of atoms          :  646 (18451 expanded)
%              Number of equality atoms :   56 (1296 expanded)
%              Maximal formula depth    :   33 (   8 average)
%              Maximal clause size      :  107 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t31_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( ( X2 = k2_yellow_0(X1,X3)
                  & r2_yellow_0(X1,X3) )
               => ( r1_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X4,X2) ) ) ) )
              & ( ( r1_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X4,X2) ) ) )
               => ( X2 = k2_yellow_0(X1,X3)
                  & r2_yellow_0(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_yellow_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_yellow_0)).

fof(t76_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ( v25_waybel_0(X1)
      <=> ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => r2_yellow_0(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_waybel_0)).

fof(c_0_3,plain,(
    ! [X17,X18,X19,X20,X21] :
      ( ( r1_lattice3(X17,X19,X18)
        | X18 != k2_yellow_0(X17,X19)
        | ~ r2_yellow_0(X17,X19)
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_lattice3(X17,X19,X20)
        | r1_orders_2(X17,X20,X18)
        | X18 != k2_yellow_0(X17,X19)
        | ~ r2_yellow_0(X17,X19)
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( X18 = k2_yellow_0(X17,X21)
        | m1_subset_1(esk5_3(X17,X18,X21),u1_struct_0(X17))
        | ~ r1_lattice3(X17,X21,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( r2_yellow_0(X17,X21)
        | m1_subset_1(esk5_3(X17,X18,X21),u1_struct_0(X17))
        | ~ r1_lattice3(X17,X21,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( X18 = k2_yellow_0(X17,X21)
        | r1_lattice3(X17,X21,esk5_3(X17,X18,X21))
        | ~ r1_lattice3(X17,X21,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( r2_yellow_0(X17,X21)
        | r1_lattice3(X17,X21,esk5_3(X17,X18,X21))
        | ~ r1_lattice3(X17,X21,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( X18 = k2_yellow_0(X17,X21)
        | ~ r1_orders_2(X17,esk5_3(X17,X18,X21),X18)
        | ~ r1_lattice3(X17,X21,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( r2_yellow_0(X17,X21)
        | ~ r1_orders_2(X17,esk5_3(X17,X18,X21),X18)
        | ~ r1_lattice3(X17,X21,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_yellow_0])])])])])])).

fof(c_0_4,plain,(
    ! [X6,X7,X9,X10,X12,X13,X16] :
      ( ( m1_subset_1(esk1_2(X6,X7),u1_struct_0(X6))
        | ~ r2_yellow_0(X6,X7)
        | ~ l1_orders_2(X6) )
      & ( r1_lattice3(X6,X7,esk1_2(X6,X7))
        | ~ r2_yellow_0(X6,X7)
        | ~ l1_orders_2(X6) )
      & ( ~ m1_subset_1(X9,u1_struct_0(X6))
        | ~ r1_lattice3(X6,X7,X9)
        | r1_orders_2(X6,X9,esk1_2(X6,X7))
        | ~ r2_yellow_0(X6,X7)
        | ~ l1_orders_2(X6) )
      & ( m1_subset_1(esk2_3(X6,X7,X10),u1_struct_0(X6))
        | ~ r1_lattice3(X6,X7,X10)
        | X10 = esk1_2(X6,X7)
        | ~ m1_subset_1(X10,u1_struct_0(X6))
        | ~ r2_yellow_0(X6,X7)
        | ~ l1_orders_2(X6) )
      & ( r1_lattice3(X6,X7,esk2_3(X6,X7,X10))
        | ~ r1_lattice3(X6,X7,X10)
        | X10 = esk1_2(X6,X7)
        | ~ m1_subset_1(X10,u1_struct_0(X6))
        | ~ r2_yellow_0(X6,X7)
        | ~ l1_orders_2(X6) )
      & ( ~ r1_orders_2(X6,esk2_3(X6,X7,X10),X10)
        | ~ r1_lattice3(X6,X7,X10)
        | X10 = esk1_2(X6,X7)
        | ~ m1_subset_1(X10,u1_struct_0(X6))
        | ~ r2_yellow_0(X6,X7)
        | ~ l1_orders_2(X6) )
      & ( m1_subset_1(esk4_3(X6,X12,X13),u1_struct_0(X6))
        | m1_subset_1(esk3_3(X6,X12,X13),u1_struct_0(X6))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r1_lattice3(X6,X12,X13)
        | r2_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) )
      & ( r1_lattice3(X6,X12,esk4_3(X6,X12,X13))
        | m1_subset_1(esk3_3(X6,X12,X13),u1_struct_0(X6))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r1_lattice3(X6,X12,X13)
        | r2_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) )
      & ( ~ m1_subset_1(X16,u1_struct_0(X6))
        | ~ r1_lattice3(X6,X12,X16)
        | r1_orders_2(X6,X16,esk4_3(X6,X12,X13))
        | m1_subset_1(esk3_3(X6,X12,X13),u1_struct_0(X6))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r1_lattice3(X6,X12,X13)
        | r2_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) )
      & ( esk4_3(X6,X12,X13) != X13
        | m1_subset_1(esk3_3(X6,X12,X13),u1_struct_0(X6))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r1_lattice3(X6,X12,X13)
        | r2_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) )
      & ( m1_subset_1(esk4_3(X6,X12,X13),u1_struct_0(X6))
        | r1_lattice3(X6,X12,esk3_3(X6,X12,X13))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r1_lattice3(X6,X12,X13)
        | r2_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) )
      & ( r1_lattice3(X6,X12,esk4_3(X6,X12,X13))
        | r1_lattice3(X6,X12,esk3_3(X6,X12,X13))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r1_lattice3(X6,X12,X13)
        | r2_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) )
      & ( ~ m1_subset_1(X16,u1_struct_0(X6))
        | ~ r1_lattice3(X6,X12,X16)
        | r1_orders_2(X6,X16,esk4_3(X6,X12,X13))
        | r1_lattice3(X6,X12,esk3_3(X6,X12,X13))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r1_lattice3(X6,X12,X13)
        | r2_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) )
      & ( esk4_3(X6,X12,X13) != X13
        | r1_lattice3(X6,X12,esk3_3(X6,X12,X13))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r1_lattice3(X6,X12,X13)
        | r2_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) )
      & ( m1_subset_1(esk4_3(X6,X12,X13),u1_struct_0(X6))
        | ~ r1_orders_2(X6,esk3_3(X6,X12,X13),X13)
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r1_lattice3(X6,X12,X13)
        | r2_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) )
      & ( r1_lattice3(X6,X12,esk4_3(X6,X12,X13))
        | ~ r1_orders_2(X6,esk3_3(X6,X12,X13),X13)
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r1_lattice3(X6,X12,X13)
        | r2_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) )
      & ( ~ m1_subset_1(X16,u1_struct_0(X6))
        | ~ r1_lattice3(X6,X12,X16)
        | r1_orders_2(X6,X16,esk4_3(X6,X12,X13))
        | ~ r1_orders_2(X6,esk3_3(X6,X12,X13),X13)
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r1_lattice3(X6,X12,X13)
        | r2_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) )
      & ( esk4_3(X6,X12,X13) != X13
        | ~ r1_orders_2(X6,esk3_3(X6,X12,X13),X13)
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r1_lattice3(X6,X12,X13)
        | r2_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_yellow_0])])])])])])).

cnf(c_0_5,plain,
    ( r2_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,esk5_3(X1,X3,X2),X3)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_6,plain,
    ( r1_orders_2(X2,X1,esk4_3(X2,X3,X4))
    | r2_yellow_0(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | ~ r1_orders_2(X2,esk3_3(X2,X3,X4),X4)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X4)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_7,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))
    | r2_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,esk3_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_8,plain,
    ( X1 = k2_yellow_0(X2,X3)
    | ~ r1_orders_2(X2,esk5_3(X2,X1,X3),X1)
    | ~ r1_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_9,plain,
    ( r1_orders_2(X2,X1,esk1_2(X2,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | ~ r2_yellow_0(X2,X3)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_10,plain,
    ( m1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_11,plain,
    ( r1_orders_2(X2,X1,esk4_3(X2,X3,X4))
    | m1_subset_1(esk3_3(X2,X3,X4),u1_struct_0(X2))
    | r2_yellow_0(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X4)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_12,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))
    | m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_13,plain,
    ( r2_yellow_0(X1,X2)
    | r2_yellow_0(X1,X3)
    | ~ v5_orders_2(X1)
    | ~ r1_orders_2(X1,esk3_3(X1,X2,X4),X4)
    | ~ r1_lattice3(X1,X2,esk5_3(X1,esk4_3(X1,X2,X4),X3))
    | ~ r1_lattice3(X1,X3,esk4_3(X1,X2,X4))
    | ~ r1_lattice3(X1,X2,X4)
    | ~ m1_subset_1(esk5_3(X1,esk4_3(X1,X2,X4),X3),u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_6]),c_0_7])).

cnf(c_0_14,plain,
    ( r2_yellow_0(X1,X2)
    | r1_lattice3(X1,X2,esk5_3(X1,X3,X2))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_15,plain,
    ( r1_lattice3(X1,X2,esk4_3(X1,X2,X3))
    | r2_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,esk3_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_16,plain,
    ( esk1_2(X1,X2) = k2_yellow_0(X1,X3)
    | ~ v5_orders_2(X1)
    | ~ r1_lattice3(X1,X2,esk5_3(X1,esk1_2(X1,X2),X3))
    | ~ r1_lattice3(X1,X3,esk1_2(X1,X2))
    | ~ m1_subset_1(esk5_3(X1,esk1_2(X1,X2),X3),u1_struct_0(X1))
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10]),
    [final]).

cnf(c_0_17,plain,
    ( X1 = k2_yellow_0(X2,X3)
    | r1_lattice3(X2,X3,esk5_3(X2,X1,X3))
    | ~ r1_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_18,plain,
    ( r1_lattice3(X1,X2,esk1_2(X1,X2))
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_19,plain,
    ( r1_orders_2(X2,X1,esk4_3(X2,X3,X4))
    | r1_lattice3(X2,X3,esk3_3(X2,X3,X4))
    | r2_yellow_0(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X4)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_20,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))
    | r1_lattice3(X1,X2,esk3_3(X1,X2,X3))
    | r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_21,plain,
    ( r1_orders_2(X2,X1,X4)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | X4 != k2_yellow_0(X2,X3)
    | ~ r2_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_22,plain,
    ( r1_lattice3(X1,X2,esk2_3(X1,X2,X3))
    | X3 = esk1_2(X1,X2)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_23,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | X3 = esk1_2(X1,X2)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_24,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | r2_yellow_0(X1,X2)
    | r2_yellow_0(X1,X4)
    | ~ v5_orders_2(X1)
    | ~ r1_lattice3(X1,X2,esk5_3(X1,esk4_3(X1,X2,X3),X4))
    | ~ r1_lattice3(X1,X4,esk4_3(X1,X2,X3))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(esk5_3(X1,esk4_3(X1,X2,X3),X4),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_11]),c_0_12])).

cnf(c_0_25,plain,
    ( r1_lattice3(X1,X2,esk4_3(X1,X2,X3))
    | m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_26,plain,
    ( r2_yellow_0(X1,X2)
    | ~ v5_orders_2(X1)
    | ~ r1_orders_2(X1,esk3_3(X1,X2,X3),X3)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(esk5_3(X1,esk4_3(X1,X2,X3),X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_7]),c_0_15])).

cnf(c_0_27,plain,
    ( r2_yellow_0(X1,X2)
    | m1_subset_1(esk5_3(X1,X3,X2),u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_28,plain,
    ( esk1_2(X1,X2) = k2_yellow_0(X1,X2)
    | ~ v5_orders_2(X1)
    | ~ m1_subset_1(esk5_3(X1,esk1_2(X1,X2),X2),u1_struct_0(X1))
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_10]),c_0_18])).

cnf(c_0_29,plain,
    ( X1 = k2_yellow_0(X2,X3)
    | m1_subset_1(esk5_3(X2,X1,X3),u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_30,plain,
    ( r1_lattice3(X1,X2,esk3_3(X1,X2,X3))
    | r2_yellow_0(X1,X2)
    | r2_yellow_0(X1,X4)
    | ~ v5_orders_2(X1)
    | ~ r1_lattice3(X1,X2,esk5_3(X1,esk4_3(X1,X2,X3),X4))
    | ~ r1_lattice3(X1,X4,esk4_3(X1,X2,X3))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(esk5_3(X1,esk4_3(X1,X2,X3),X4),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_19]),c_0_20])).

cnf(c_0_31,plain,
    ( r1_lattice3(X1,X2,esk4_3(X1,X2,X3))
    | r1_lattice3(X1,X2,esk3_3(X1,X2,X3))
    | r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_32,plain,
    ( X3 = esk1_2(X1,X2)
    | ~ r1_orders_2(X1,esk2_3(X1,X2,X3),X3)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_33,plain,
    ( X1 = esk1_2(X2,X3)
    | r1_orders_2(X2,esk2_3(X2,X3,X1),X4)
    | X4 != k2_yellow_0(X2,X3)
    | ~ v5_orders_2(X2)
    | ~ r1_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_yellow_0(X2,X3)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),
    [final]).

cnf(c_0_34,plain,
    ( r1_lattice3(X1,X2,X3)
    | X3 != k2_yellow_0(X1,X2)
    | ~ r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_35,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | r2_yellow_0(X1,X2)
    | ~ v5_orders_2(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(esk5_3(X1,esk4_3(X1,X2,X3),X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_14]),c_0_12]),c_0_25])).

cnf(c_0_36,plain,
    ( r2_yellow_0(X1,X2)
    | ~ v5_orders_2(X1)
    | ~ r1_orders_2(X1,esk3_3(X1,X2,X3),X3)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_7]),c_0_15]),
    [final]).

cnf(c_0_37,plain,
    ( esk1_2(X1,X2) = k2_yellow_0(X1,X2)
    | ~ v5_orders_2(X1)
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_10]),c_0_18]),
    [final]).

fof(c_0_38,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ( v25_waybel_0(X1)
        <=> ! [X2] :
              ( ( ~ v1_xboole_0(X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
             => r2_yellow_0(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t76_waybel_0])).

cnf(c_0_39,plain,
    ( r1_lattice3(X1,X2,esk3_3(X1,X2,X3))
    | r2_yellow_0(X1,X2)
    | ~ v5_orders_2(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(esk5_3(X1,esk4_3(X1,X2,X3),X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_14]),c_0_20]),c_0_31])).

cnf(c_0_40,plain,
    ( X1 = esk1_2(X2,X3)
    | X1 != k2_yellow_0(X2,X3)
    | ~ v5_orders_2(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_yellow_0(X2,X3)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),
    [final]).

cnf(c_0_41,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | r2_yellow_0(X1,X2)
    | ~ v5_orders_2(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_27]),c_0_12]),c_0_25]),
    [final]).

cnf(c_0_42,plain,
    ( r2_yellow_0(X1,X2)
    | ~ v5_orders_2(X1)
    | ~ r1_lattice3(X1,X3,esk3_3(X1,X2,esk1_2(X1,X3)))
    | ~ r1_lattice3(X1,X2,esk1_2(X1,X3))
    | ~ m1_subset_1(esk3_3(X1,X2,esk1_2(X1,X3)),u1_struct_0(X1))
    | ~ r2_yellow_0(X1,X3)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_9]),c_0_10]),
    [final]).

cnf(c_0_43,plain,
    ( m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_37]),
    [final]).

cnf(c_0_44,plain,
    ( esk1_2(X1,X2) = esk1_2(X1,X3)
    | ~ r1_lattice3(X1,X2,esk2_3(X1,X3,esk1_2(X1,X2)))
    | ~ r1_lattice3(X1,X3,esk1_2(X1,X2))
    | ~ m1_subset_1(esk2_3(X1,X3,esk1_2(X1,X2)),u1_struct_0(X1))
    | ~ r2_yellow_0(X1,X3)
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_9]),c_0_10]),
    [final]).

cnf(c_0_45,plain,
    ( r2_yellow_0(X1,X2)
    | ~ v5_orders_2(X1)
    | ~ r1_lattice3(X1,X3,esk5_3(X1,esk1_2(X1,X3),X2))
    | ~ r1_lattice3(X1,X2,esk1_2(X1,X3))
    | ~ m1_subset_1(esk5_3(X1,esk1_2(X1,X3),X2),u1_struct_0(X1))
    | ~ r2_yellow_0(X1,X3)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_9]),c_0_10]),
    [final]).

cnf(c_0_46,plain,
    ( r1_orders_2(X1,esk1_2(X1,X2),X3)
    | X3 != k2_yellow_0(X1,X2)
    | ~ v5_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_18]),c_0_10]),
    [final]).

fof(c_0_47,negated_conjecture,(
    ! [X25] :
      ( ~ v2_struct_0(esk6_0)
      & v3_orders_2(esk6_0)
      & v5_orders_2(esk6_0)
      & l1_orders_2(esk6_0)
      & ( ~ v1_xboole_0(esk7_0)
        | ~ v25_waybel_0(esk6_0) )
      & ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0)))
        | ~ v25_waybel_0(esk6_0) )
      & ( ~ r2_yellow_0(esk6_0,esk7_0)
        | ~ v25_waybel_0(esk6_0) )
      & ( v25_waybel_0(esk6_0)
        | v1_xboole_0(X25)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(esk6_0)))
        | r2_yellow_0(esk6_0,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_38])])])])])])).

cnf(c_0_48,plain,
    ( esk4_3(X1,X2,X3) = esk1_2(X1,X4)
    | r1_lattice3(X1,X2,esk3_3(X1,X2,X3))
    | r2_yellow_0(X1,X2)
    | ~ r1_lattice3(X1,X2,esk2_3(X1,X4,esk4_3(X1,X2,X3)))
    | ~ r1_lattice3(X1,X4,esk4_3(X1,X2,X3))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(esk2_3(X1,X4,esk4_3(X1,X2,X3)),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(X1,X4)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_19]),c_0_20]),
    [final]).

cnf(c_0_49,plain,
    ( esk4_3(X1,X2,X3) = esk1_2(X1,X4)
    | m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | r2_yellow_0(X1,X2)
    | ~ r1_lattice3(X1,X2,esk2_3(X1,X4,esk4_3(X1,X2,X3)))
    | ~ r1_lattice3(X1,X4,esk4_3(X1,X2,X3))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(esk2_3(X1,X4,esk4_3(X1,X2,X3)),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(X1,X4)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_11]),c_0_12]),
    [final]).

cnf(c_0_50,plain,
    ( r1_lattice3(X1,X2,esk3_3(X1,X2,X3))
    | r2_yellow_0(X1,X2)
    | ~ v5_orders_2(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_27]),c_0_20]),c_0_31]),
    [final]).

cnf(c_0_51,plain,
    ( esk4_3(X1,X2,X3) = esk1_2(X1,X4)
    | r2_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,esk3_3(X1,X2,X3),X3)
    | ~ r1_lattice3(X1,X2,esk2_3(X1,X4,esk4_3(X1,X2,X3)))
    | ~ r1_lattice3(X1,X4,esk4_3(X1,X2,X3))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(esk2_3(X1,X4,esk4_3(X1,X2,X3)),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(X1,X4)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_6]),c_0_7]),
    [final]).

cnf(c_0_52,plain,
    ( esk3_3(X1,X2,X3) = esk1_2(X1,X4)
    | r2_yellow_0(X1,X2)
    | esk3_3(X1,X2,X3) != k2_yellow_0(X1,X4)
    | ~ v5_orders_2(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(X1,X4)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41]),
    [final]).

cnf(c_0_53,plain,
    ( r2_yellow_0(X1,X2)
    | ~ v5_orders_2(X1)
    | ~ r1_lattice3(X1,X3,esk3_3(X1,X2,k2_yellow_0(X1,X3)))
    | ~ r1_lattice3(X1,X2,k2_yellow_0(X1,X3))
    | ~ m1_subset_1(esk3_3(X1,X2,k2_yellow_0(X1,X3)),u1_struct_0(X1))
    | ~ r2_yellow_0(X1,X3)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_37]),
    [final]).

cnf(c_0_54,plain,
    ( esk2_3(X1,X2,X3) = esk1_2(X1,X4)
    | X3 = esk1_2(X1,X2)
    | esk2_3(X1,X2,X3) != k2_yellow_0(X1,X4)
    | ~ v5_orders_2(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(X1,X4)
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_23]),
    [final]).

cnf(c_0_55,plain,
    ( esk5_3(X1,X2,X3) = esk1_2(X1,X4)
    | X2 = k2_yellow_0(X1,X3)
    | esk5_3(X1,X2,X3) != k2_yellow_0(X1,X4)
    | ~ v5_orders_2(X1)
    | ~ r1_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_yellow_0(X1,X4)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_29]),
    [final]).

cnf(c_0_56,plain,
    ( esk5_3(X1,X2,X3) = esk1_2(X1,X4)
    | r2_yellow_0(X1,X3)
    | esk5_3(X1,X2,X3) != k2_yellow_0(X1,X4)
    | ~ v5_orders_2(X1)
    | ~ r1_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_yellow_0(X1,X4)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_27]),
    [final]).

cnf(c_0_57,plain,
    ( k2_yellow_0(X1,X2) = esk1_2(X1,X3)
    | k2_yellow_0(X1,X2) != k2_yellow_0(X1,X3)
    | ~ v5_orders_2(X1)
    | ~ r2_yellow_0(X1,X3)
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_43]),
    [final]).

cnf(c_0_58,plain,
    ( esk1_2(X1,X2) = esk1_2(X1,X3)
    | esk1_2(X1,X2) != k2_yellow_0(X1,X3)
    | ~ v5_orders_2(X1)
    | ~ r2_yellow_0(X1,X3)
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_10]),
    [final]).

cnf(c_0_59,plain,
    ( k2_yellow_0(X1,X2) = esk1_2(X1,X3)
    | ~ v5_orders_2(X1)
    | ~ r1_lattice3(X1,X2,esk2_3(X1,X3,k2_yellow_0(X1,X2)))
    | ~ r1_lattice3(X1,X3,k2_yellow_0(X1,X2))
    | ~ m1_subset_1(esk2_3(X1,X3,k2_yellow_0(X1,X2)),u1_struct_0(X1))
    | ~ r2_yellow_0(X1,X3)
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_37]),
    [final]).

cnf(c_0_60,plain,
    ( k2_yellow_0(X1,X2) = k2_yellow_0(X1,X3)
    | ~ v5_orders_2(X1)
    | ~ r1_lattice3(X1,X2,esk5_3(X1,k2_yellow_0(X1,X2),X3))
    | ~ r1_lattice3(X1,X3,k2_yellow_0(X1,X2))
    | ~ m1_subset_1(esk5_3(X1,k2_yellow_0(X1,X2),X3),u1_struct_0(X1))
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_37]),
    [final]).

cnf(c_0_61,plain,
    ( r2_yellow_0(X1,X2)
    | ~ v5_orders_2(X1)
    | ~ r1_lattice3(X1,X3,esk5_3(X1,k2_yellow_0(X1,X3),X2))
    | ~ r1_lattice3(X1,X2,k2_yellow_0(X1,X3))
    | ~ m1_subset_1(esk5_3(X1,k2_yellow_0(X1,X3),X2),u1_struct_0(X1))
    | ~ r2_yellow_0(X1,X3)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_37]),
    [final]).

cnf(c_0_62,plain,
    ( r1_orders_2(X1,X2,k2_yellow_0(X1,X3))
    | ~ v5_orders_2(X1)
    | ~ r1_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_yellow_0(X1,X3)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_37]),
    [final]).

cnf(c_0_63,plain,
    ( r1_orders_2(X1,k2_yellow_0(X1,X2),X3)
    | X3 != k2_yellow_0(X1,X2)
    | ~ v5_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_37]),
    [final]).

cnf(c_0_64,plain,
    ( r1_lattice3(X1,X2,k2_yellow_0(X1,X2))
    | ~ v5_orders_2(X1)
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_37]),
    [final]).

cnf(c_0_65,plain,
    ( X1 = k2_yellow_0(X2,X3)
    | r1_orders_2(X2,esk5_3(X2,X1,X3),X4)
    | X4 != k2_yellow_0(X2,X3)
    | ~ v5_orders_2(X2)
    | ~ r1_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_yellow_0(X2,X3)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_17]),c_0_29]),
    [final]).

cnf(c_0_66,plain,
    ( r1_lattice3(X1,X2,esk3_3(X1,X2,X3))
    | r2_yellow_0(X1,X2)
    | esk4_3(X1,X2,X3) != X3
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_67,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | r2_yellow_0(X1,X2)
    | esk4_3(X1,X2,X3) != X3
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_68,plain,
    ( r2_yellow_0(X1,X2)
    | esk4_3(X1,X2,X3) != X3
    | ~ r1_orders_2(X1,esk3_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_69,negated_conjecture,
    ( v25_waybel_0(esk6_0)
    | v1_xboole_0(X1)
    | r2_yellow_0(esk6_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_47]),
    [final]).

cnf(c_0_70,negated_conjecture,
    ( ~ r2_yellow_0(esk6_0,esk7_0)
    | ~ v25_waybel_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_47]),
    [final]).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ v25_waybel_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_47]),
    [final]).

cnf(c_0_72,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0)
    | ~ v25_waybel_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_47]),
    [final]).

cnf(c_0_73,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_47]),
    [final]).

cnf(c_0_74,negated_conjecture,
    ( v3_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_47]),
    [final]).

cnf(c_0_75,negated_conjecture,
    ( v5_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_47]),
    [final]).

cnf(c_0_76,negated_conjecture,
    ( l1_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_47]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:52:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.40  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.14/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.40  #
% 0.14/0.40  # Preprocessing time       : 0.039 s
% 0.14/0.40  # Presaturation interreduction done
% 0.14/0.40  
% 0.14/0.40  # No proof found!
% 0.14/0.40  # SZS status CounterSatisfiable
% 0.14/0.40  # SZS output start Saturation
% 0.14/0.40  fof(t31_yellow_0, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(((X2=k2_yellow_0(X1,X3)&r2_yellow_0(X1,X3))=>(r1_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattice3(X1,X3,X4)=>r1_orders_2(X1,X4,X2)))))&((r1_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattice3(X1,X3,X4)=>r1_orders_2(X1,X4,X2))))=>(X2=k2_yellow_0(X1,X3)&r2_yellow_0(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_yellow_0)).
% 0.14/0.40  fof(d8_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(r2_yellow_0(X1,X2)<=>?[X3]:(((m1_subset_1(X3,u1_struct_0(X1))&r1_lattice3(X1,X2,X3))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X4)=>r1_orders_2(X1,X4,X3))))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r1_lattice3(X1,X2,X4)&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X5)=>r1_orders_2(X1,X5,X4))))=>X4=X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_yellow_0)).
% 0.14/0.40  fof(t76_waybel_0, conjecture, ![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>(v25_waybel_0(X1)<=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>r2_yellow_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_waybel_0)).
% 0.14/0.40  fof(c_0_3, plain, ![X17, X18, X19, X20, X21]:(((r1_lattice3(X17,X19,X18)|(X18!=k2_yellow_0(X17,X19)|~r2_yellow_0(X17,X19))|~m1_subset_1(X18,u1_struct_0(X17))|(~v5_orders_2(X17)|~l1_orders_2(X17)))&(~m1_subset_1(X20,u1_struct_0(X17))|(~r1_lattice3(X17,X19,X20)|r1_orders_2(X17,X20,X18))|(X18!=k2_yellow_0(X17,X19)|~r2_yellow_0(X17,X19))|~m1_subset_1(X18,u1_struct_0(X17))|(~v5_orders_2(X17)|~l1_orders_2(X17))))&(((X18=k2_yellow_0(X17,X21)|(m1_subset_1(esk5_3(X17,X18,X21),u1_struct_0(X17))|~r1_lattice3(X17,X21,X18))|~m1_subset_1(X18,u1_struct_0(X17))|(~v5_orders_2(X17)|~l1_orders_2(X17)))&(r2_yellow_0(X17,X21)|(m1_subset_1(esk5_3(X17,X18,X21),u1_struct_0(X17))|~r1_lattice3(X17,X21,X18))|~m1_subset_1(X18,u1_struct_0(X17))|(~v5_orders_2(X17)|~l1_orders_2(X17))))&(((X18=k2_yellow_0(X17,X21)|(r1_lattice3(X17,X21,esk5_3(X17,X18,X21))|~r1_lattice3(X17,X21,X18))|~m1_subset_1(X18,u1_struct_0(X17))|(~v5_orders_2(X17)|~l1_orders_2(X17)))&(r2_yellow_0(X17,X21)|(r1_lattice3(X17,X21,esk5_3(X17,X18,X21))|~r1_lattice3(X17,X21,X18))|~m1_subset_1(X18,u1_struct_0(X17))|(~v5_orders_2(X17)|~l1_orders_2(X17))))&((X18=k2_yellow_0(X17,X21)|(~r1_orders_2(X17,esk5_3(X17,X18,X21),X18)|~r1_lattice3(X17,X21,X18))|~m1_subset_1(X18,u1_struct_0(X17))|(~v5_orders_2(X17)|~l1_orders_2(X17)))&(r2_yellow_0(X17,X21)|(~r1_orders_2(X17,esk5_3(X17,X18,X21),X18)|~r1_lattice3(X17,X21,X18))|~m1_subset_1(X18,u1_struct_0(X17))|(~v5_orders_2(X17)|~l1_orders_2(X17))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_yellow_0])])])])])])).
% 0.14/0.40  fof(c_0_4, plain, ![X6, X7, X9, X10, X12, X13, X16]:(((((m1_subset_1(esk1_2(X6,X7),u1_struct_0(X6))|~r2_yellow_0(X6,X7)|~l1_orders_2(X6))&(r1_lattice3(X6,X7,esk1_2(X6,X7))|~r2_yellow_0(X6,X7)|~l1_orders_2(X6)))&(~m1_subset_1(X9,u1_struct_0(X6))|(~r1_lattice3(X6,X7,X9)|r1_orders_2(X6,X9,esk1_2(X6,X7)))|~r2_yellow_0(X6,X7)|~l1_orders_2(X6)))&((m1_subset_1(esk2_3(X6,X7,X10),u1_struct_0(X6))|~r1_lattice3(X6,X7,X10)|X10=esk1_2(X6,X7)|~m1_subset_1(X10,u1_struct_0(X6))|~r2_yellow_0(X6,X7)|~l1_orders_2(X6))&((r1_lattice3(X6,X7,esk2_3(X6,X7,X10))|~r1_lattice3(X6,X7,X10)|X10=esk1_2(X6,X7)|~m1_subset_1(X10,u1_struct_0(X6))|~r2_yellow_0(X6,X7)|~l1_orders_2(X6))&(~r1_orders_2(X6,esk2_3(X6,X7,X10),X10)|~r1_lattice3(X6,X7,X10)|X10=esk1_2(X6,X7)|~m1_subset_1(X10,u1_struct_0(X6))|~r2_yellow_0(X6,X7)|~l1_orders_2(X6)))))&(((m1_subset_1(esk4_3(X6,X12,X13),u1_struct_0(X6))|(m1_subset_1(esk3_3(X6,X12,X13),u1_struct_0(X6))|(~m1_subset_1(X13,u1_struct_0(X6))|~r1_lattice3(X6,X12,X13)))|r2_yellow_0(X6,X12)|~l1_orders_2(X6))&(((r1_lattice3(X6,X12,esk4_3(X6,X12,X13))|(m1_subset_1(esk3_3(X6,X12,X13),u1_struct_0(X6))|(~m1_subset_1(X13,u1_struct_0(X6))|~r1_lattice3(X6,X12,X13)))|r2_yellow_0(X6,X12)|~l1_orders_2(X6))&(~m1_subset_1(X16,u1_struct_0(X6))|(~r1_lattice3(X6,X12,X16)|r1_orders_2(X6,X16,esk4_3(X6,X12,X13)))|(m1_subset_1(esk3_3(X6,X12,X13),u1_struct_0(X6))|(~m1_subset_1(X13,u1_struct_0(X6))|~r1_lattice3(X6,X12,X13)))|r2_yellow_0(X6,X12)|~l1_orders_2(X6)))&(esk4_3(X6,X12,X13)!=X13|(m1_subset_1(esk3_3(X6,X12,X13),u1_struct_0(X6))|(~m1_subset_1(X13,u1_struct_0(X6))|~r1_lattice3(X6,X12,X13)))|r2_yellow_0(X6,X12)|~l1_orders_2(X6))))&(((m1_subset_1(esk4_3(X6,X12,X13),u1_struct_0(X6))|(r1_lattice3(X6,X12,esk3_3(X6,X12,X13))|(~m1_subset_1(X13,u1_struct_0(X6))|~r1_lattice3(X6,X12,X13)))|r2_yellow_0(X6,X12)|~l1_orders_2(X6))&(((r1_lattice3(X6,X12,esk4_3(X6,X12,X13))|(r1_lattice3(X6,X12,esk3_3(X6,X12,X13))|(~m1_subset_1(X13,u1_struct_0(X6))|~r1_lattice3(X6,X12,X13)))|r2_yellow_0(X6,X12)|~l1_orders_2(X6))&(~m1_subset_1(X16,u1_struct_0(X6))|(~r1_lattice3(X6,X12,X16)|r1_orders_2(X6,X16,esk4_3(X6,X12,X13)))|(r1_lattice3(X6,X12,esk3_3(X6,X12,X13))|(~m1_subset_1(X13,u1_struct_0(X6))|~r1_lattice3(X6,X12,X13)))|r2_yellow_0(X6,X12)|~l1_orders_2(X6)))&(esk4_3(X6,X12,X13)!=X13|(r1_lattice3(X6,X12,esk3_3(X6,X12,X13))|(~m1_subset_1(X13,u1_struct_0(X6))|~r1_lattice3(X6,X12,X13)))|r2_yellow_0(X6,X12)|~l1_orders_2(X6))))&((m1_subset_1(esk4_3(X6,X12,X13),u1_struct_0(X6))|(~r1_orders_2(X6,esk3_3(X6,X12,X13),X13)|(~m1_subset_1(X13,u1_struct_0(X6))|~r1_lattice3(X6,X12,X13)))|r2_yellow_0(X6,X12)|~l1_orders_2(X6))&(((r1_lattice3(X6,X12,esk4_3(X6,X12,X13))|(~r1_orders_2(X6,esk3_3(X6,X12,X13),X13)|(~m1_subset_1(X13,u1_struct_0(X6))|~r1_lattice3(X6,X12,X13)))|r2_yellow_0(X6,X12)|~l1_orders_2(X6))&(~m1_subset_1(X16,u1_struct_0(X6))|(~r1_lattice3(X6,X12,X16)|r1_orders_2(X6,X16,esk4_3(X6,X12,X13)))|(~r1_orders_2(X6,esk3_3(X6,X12,X13),X13)|(~m1_subset_1(X13,u1_struct_0(X6))|~r1_lattice3(X6,X12,X13)))|r2_yellow_0(X6,X12)|~l1_orders_2(X6)))&(esk4_3(X6,X12,X13)!=X13|(~r1_orders_2(X6,esk3_3(X6,X12,X13),X13)|(~m1_subset_1(X13,u1_struct_0(X6))|~r1_lattice3(X6,X12,X13)))|r2_yellow_0(X6,X12)|~l1_orders_2(X6))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_yellow_0])])])])])])).
% 0.14/0.40  cnf(c_0_5, plain, (r2_yellow_0(X1,X2)|~r1_orders_2(X1,esk5_3(X1,X3,X2),X3)|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.14/0.40  cnf(c_0_6, plain, (r1_orders_2(X2,X1,esk4_3(X2,X3,X4))|r2_yellow_0(X2,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~r1_lattice3(X2,X3,X1)|~r1_orders_2(X2,esk3_3(X2,X3,X4),X4)|~m1_subset_1(X4,u1_struct_0(X2))|~r1_lattice3(X2,X3,X4)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.14/0.40  cnf(c_0_7, plain, (m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))|r2_yellow_0(X1,X2)|~r1_orders_2(X1,esk3_3(X1,X2,X3),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~r1_lattice3(X1,X2,X3)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.14/0.40  cnf(c_0_8, plain, (X1=k2_yellow_0(X2,X3)|~r1_orders_2(X2,esk5_3(X2,X1,X3),X1)|~r1_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.14/0.40  cnf(c_0_9, plain, (r1_orders_2(X2,X1,esk1_2(X2,X3))|~m1_subset_1(X1,u1_struct_0(X2))|~r1_lattice3(X2,X3,X1)|~r2_yellow_0(X2,X3)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.14/0.40  cnf(c_0_10, plain, (m1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.14/0.40  cnf(c_0_11, plain, (r1_orders_2(X2,X1,esk4_3(X2,X3,X4))|m1_subset_1(esk3_3(X2,X3,X4),u1_struct_0(X2))|r2_yellow_0(X2,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~r1_lattice3(X2,X3,X1)|~m1_subset_1(X4,u1_struct_0(X2))|~r1_lattice3(X2,X3,X4)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.14/0.40  cnf(c_0_12, plain, (m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))|m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))|r2_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~r1_lattice3(X1,X2,X3)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.14/0.40  cnf(c_0_13, plain, (r2_yellow_0(X1,X2)|r2_yellow_0(X1,X3)|~v5_orders_2(X1)|~r1_orders_2(X1,esk3_3(X1,X2,X4),X4)|~r1_lattice3(X1,X2,esk5_3(X1,esk4_3(X1,X2,X4),X3))|~r1_lattice3(X1,X3,esk4_3(X1,X2,X4))|~r1_lattice3(X1,X2,X4)|~m1_subset_1(esk5_3(X1,esk4_3(X1,X2,X4),X3),u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_5, c_0_6]), c_0_7])).
% 0.14/0.40  cnf(c_0_14, plain, (r2_yellow_0(X1,X2)|r1_lattice3(X1,X2,esk5_3(X1,X3,X2))|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.14/0.40  cnf(c_0_15, plain, (r1_lattice3(X1,X2,esk4_3(X1,X2,X3))|r2_yellow_0(X1,X2)|~r1_orders_2(X1,esk3_3(X1,X2,X3),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~r1_lattice3(X1,X2,X3)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.14/0.40  cnf(c_0_16, plain, (esk1_2(X1,X2)=k2_yellow_0(X1,X3)|~v5_orders_2(X1)|~r1_lattice3(X1,X2,esk5_3(X1,esk1_2(X1,X2),X3))|~r1_lattice3(X1,X3,esk1_2(X1,X2))|~m1_subset_1(esk5_3(X1,esk1_2(X1,X2),X3),u1_struct_0(X1))|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_9]), c_0_10]), ['final']).
% 0.14/0.40  cnf(c_0_17, plain, (X1=k2_yellow_0(X2,X3)|r1_lattice3(X2,X3,esk5_3(X2,X1,X3))|~r1_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.14/0.40  cnf(c_0_18, plain, (r1_lattice3(X1,X2,esk1_2(X1,X2))|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.14/0.40  cnf(c_0_19, plain, (r1_orders_2(X2,X1,esk4_3(X2,X3,X4))|r1_lattice3(X2,X3,esk3_3(X2,X3,X4))|r2_yellow_0(X2,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~r1_lattice3(X2,X3,X1)|~m1_subset_1(X4,u1_struct_0(X2))|~r1_lattice3(X2,X3,X4)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.14/0.40  cnf(c_0_20, plain, (m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))|r1_lattice3(X1,X2,esk3_3(X1,X2,X3))|r2_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~r1_lattice3(X1,X2,X3)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.14/0.40  cnf(c_0_21, plain, (r1_orders_2(X2,X1,X4)|~m1_subset_1(X1,u1_struct_0(X2))|~r1_lattice3(X2,X3,X1)|X4!=k2_yellow_0(X2,X3)|~r2_yellow_0(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.14/0.40  cnf(c_0_22, plain, (r1_lattice3(X1,X2,esk2_3(X1,X2,X3))|X3=esk1_2(X1,X2)|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.14/0.40  cnf(c_0_23, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))|X3=esk1_2(X1,X2)|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.14/0.40  cnf(c_0_24, plain, (m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))|r2_yellow_0(X1,X2)|r2_yellow_0(X1,X4)|~v5_orders_2(X1)|~r1_lattice3(X1,X2,esk5_3(X1,esk4_3(X1,X2,X3),X4))|~r1_lattice3(X1,X4,esk4_3(X1,X2,X3))|~r1_lattice3(X1,X2,X3)|~m1_subset_1(esk5_3(X1,esk4_3(X1,X2,X3),X4),u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_5, c_0_11]), c_0_12])).
% 0.14/0.40  cnf(c_0_25, plain, (r1_lattice3(X1,X2,esk4_3(X1,X2,X3))|m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))|r2_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~r1_lattice3(X1,X2,X3)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.14/0.40  cnf(c_0_26, plain, (r2_yellow_0(X1,X2)|~v5_orders_2(X1)|~r1_orders_2(X1,esk3_3(X1,X2,X3),X3)|~r1_lattice3(X1,X2,X3)|~m1_subset_1(esk5_3(X1,esk4_3(X1,X2,X3),X2),u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_7]), c_0_15])).
% 0.14/0.40  cnf(c_0_27, plain, (r2_yellow_0(X1,X2)|m1_subset_1(esk5_3(X1,X3,X2),u1_struct_0(X1))|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.14/0.40  cnf(c_0_28, plain, (esk1_2(X1,X2)=k2_yellow_0(X1,X2)|~v5_orders_2(X1)|~m1_subset_1(esk5_3(X1,esk1_2(X1,X2),X2),u1_struct_0(X1))|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_10]), c_0_18])).
% 0.14/0.40  cnf(c_0_29, plain, (X1=k2_yellow_0(X2,X3)|m1_subset_1(esk5_3(X2,X1,X3),u1_struct_0(X2))|~r1_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.14/0.40  cnf(c_0_30, plain, (r1_lattice3(X1,X2,esk3_3(X1,X2,X3))|r2_yellow_0(X1,X2)|r2_yellow_0(X1,X4)|~v5_orders_2(X1)|~r1_lattice3(X1,X2,esk5_3(X1,esk4_3(X1,X2,X3),X4))|~r1_lattice3(X1,X4,esk4_3(X1,X2,X3))|~r1_lattice3(X1,X2,X3)|~m1_subset_1(esk5_3(X1,esk4_3(X1,X2,X3),X4),u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_5, c_0_19]), c_0_20])).
% 0.14/0.40  cnf(c_0_31, plain, (r1_lattice3(X1,X2,esk4_3(X1,X2,X3))|r1_lattice3(X1,X2,esk3_3(X1,X2,X3))|r2_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~r1_lattice3(X1,X2,X3)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.14/0.40  cnf(c_0_32, plain, (X3=esk1_2(X1,X2)|~r1_orders_2(X1,esk2_3(X1,X2,X3),X3)|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.14/0.40  cnf(c_0_33, plain, (X1=esk1_2(X2,X3)|r1_orders_2(X2,esk2_3(X2,X3,X1),X4)|X4!=k2_yellow_0(X2,X3)|~v5_orders_2(X2)|~r1_lattice3(X2,X3,X1)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~r2_yellow_0(X2,X3)|~l1_orders_2(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23]), ['final']).
% 0.14/0.40  cnf(c_0_34, plain, (r1_lattice3(X1,X2,X3)|X3!=k2_yellow_0(X1,X2)|~r2_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.14/0.40  cnf(c_0_35, plain, (m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))|r2_yellow_0(X1,X2)|~v5_orders_2(X1)|~r1_lattice3(X1,X2,X3)|~m1_subset_1(esk5_3(X1,esk4_3(X1,X2,X3),X2),u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_14]), c_0_12]), c_0_25])).
% 0.14/0.40  cnf(c_0_36, plain, (r2_yellow_0(X1,X2)|~v5_orders_2(X1)|~r1_orders_2(X1,esk3_3(X1,X2,X3),X3)|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_7]), c_0_15]), ['final']).
% 0.14/0.40  cnf(c_0_37, plain, (esk1_2(X1,X2)=k2_yellow_0(X1,X2)|~v5_orders_2(X1)|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_10]), c_0_18]), ['final']).
% 0.14/0.40  fof(c_0_38, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>(v25_waybel_0(X1)<=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>r2_yellow_0(X1,X2))))), inference(assume_negation,[status(cth)],[t76_waybel_0])).
% 0.14/0.40  cnf(c_0_39, plain, (r1_lattice3(X1,X2,esk3_3(X1,X2,X3))|r2_yellow_0(X1,X2)|~v5_orders_2(X1)|~r1_lattice3(X1,X2,X3)|~m1_subset_1(esk5_3(X1,esk4_3(X1,X2,X3),X2),u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_14]), c_0_20]), c_0_31])).
% 0.14/0.41  cnf(c_0_40, plain, (X1=esk1_2(X2,X3)|X1!=k2_yellow_0(X2,X3)|~v5_orders_2(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_yellow_0(X2,X3)|~l1_orders_2(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), ['final']).
% 0.14/0.41  cnf(c_0_41, plain, (m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))|r2_yellow_0(X1,X2)|~v5_orders_2(X1)|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_27]), c_0_12]), c_0_25]), ['final']).
% 0.14/0.41  cnf(c_0_42, plain, (r2_yellow_0(X1,X2)|~v5_orders_2(X1)|~r1_lattice3(X1,X3,esk3_3(X1,X2,esk1_2(X1,X3)))|~r1_lattice3(X1,X2,esk1_2(X1,X3))|~m1_subset_1(esk3_3(X1,X2,esk1_2(X1,X3)),u1_struct_0(X1))|~r2_yellow_0(X1,X3)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_9]), c_0_10]), ['final']).
% 0.14/0.41  cnf(c_0_43, plain, (m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1))|~v5_orders_2(X1)|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_10, c_0_37]), ['final']).
% 0.14/0.41  cnf(c_0_44, plain, (esk1_2(X1,X2)=esk1_2(X1,X3)|~r1_lattice3(X1,X2,esk2_3(X1,X3,esk1_2(X1,X2)))|~r1_lattice3(X1,X3,esk1_2(X1,X2))|~m1_subset_1(esk2_3(X1,X3,esk1_2(X1,X2)),u1_struct_0(X1))|~r2_yellow_0(X1,X3)|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_9]), c_0_10]), ['final']).
% 0.14/0.41  cnf(c_0_45, plain, (r2_yellow_0(X1,X2)|~v5_orders_2(X1)|~r1_lattice3(X1,X3,esk5_3(X1,esk1_2(X1,X3),X2))|~r1_lattice3(X1,X2,esk1_2(X1,X3))|~m1_subset_1(esk5_3(X1,esk1_2(X1,X3),X2),u1_struct_0(X1))|~r2_yellow_0(X1,X3)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_5, c_0_9]), c_0_10]), ['final']).
% 0.14/0.41  cnf(c_0_46, plain, (r1_orders_2(X1,esk1_2(X1,X2),X3)|X3!=k2_yellow_0(X1,X2)|~v5_orders_2(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_18]), c_0_10]), ['final']).
% 0.14/0.41  fof(c_0_47, negated_conjecture, ![X25]:((((~v2_struct_0(esk6_0)&v3_orders_2(esk6_0))&v5_orders_2(esk6_0))&l1_orders_2(esk6_0))&((((~v1_xboole_0(esk7_0)|~v25_waybel_0(esk6_0))&(m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0)))|~v25_waybel_0(esk6_0)))&(~r2_yellow_0(esk6_0,esk7_0)|~v25_waybel_0(esk6_0)))&(v25_waybel_0(esk6_0)|(v1_xboole_0(X25)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(esk6_0)))|r2_yellow_0(esk6_0,X25))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_38])])])])])])).
% 0.14/0.41  cnf(c_0_48, plain, (esk4_3(X1,X2,X3)=esk1_2(X1,X4)|r1_lattice3(X1,X2,esk3_3(X1,X2,X3))|r2_yellow_0(X1,X2)|~r1_lattice3(X1,X2,esk2_3(X1,X4,esk4_3(X1,X2,X3)))|~r1_lattice3(X1,X4,esk4_3(X1,X2,X3))|~r1_lattice3(X1,X2,X3)|~m1_subset_1(esk2_3(X1,X4,esk4_3(X1,X2,X3)),u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~r2_yellow_0(X1,X4)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_19]), c_0_20]), ['final']).
% 0.14/0.41  cnf(c_0_49, plain, (esk4_3(X1,X2,X3)=esk1_2(X1,X4)|m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))|r2_yellow_0(X1,X2)|~r1_lattice3(X1,X2,esk2_3(X1,X4,esk4_3(X1,X2,X3)))|~r1_lattice3(X1,X4,esk4_3(X1,X2,X3))|~r1_lattice3(X1,X2,X3)|~m1_subset_1(esk2_3(X1,X4,esk4_3(X1,X2,X3)),u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~r2_yellow_0(X1,X4)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_11]), c_0_12]), ['final']).
% 0.14/0.41  cnf(c_0_50, plain, (r1_lattice3(X1,X2,esk3_3(X1,X2,X3))|r2_yellow_0(X1,X2)|~v5_orders_2(X1)|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_27]), c_0_20]), c_0_31]), ['final']).
% 0.14/0.41  cnf(c_0_51, plain, (esk4_3(X1,X2,X3)=esk1_2(X1,X4)|r2_yellow_0(X1,X2)|~r1_orders_2(X1,esk3_3(X1,X2,X3),X3)|~r1_lattice3(X1,X2,esk2_3(X1,X4,esk4_3(X1,X2,X3)))|~r1_lattice3(X1,X4,esk4_3(X1,X2,X3))|~r1_lattice3(X1,X2,X3)|~m1_subset_1(esk2_3(X1,X4,esk4_3(X1,X2,X3)),u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~r2_yellow_0(X1,X4)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_6]), c_0_7]), ['final']).
% 0.14/0.41  cnf(c_0_52, plain, (esk3_3(X1,X2,X3)=esk1_2(X1,X4)|r2_yellow_0(X1,X2)|esk3_3(X1,X2,X3)!=k2_yellow_0(X1,X4)|~v5_orders_2(X1)|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_yellow_0(X1,X4)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_40, c_0_41]), ['final']).
% 0.14/0.41  cnf(c_0_53, plain, (r2_yellow_0(X1,X2)|~v5_orders_2(X1)|~r1_lattice3(X1,X3,esk3_3(X1,X2,k2_yellow_0(X1,X3)))|~r1_lattice3(X1,X2,k2_yellow_0(X1,X3))|~m1_subset_1(esk3_3(X1,X2,k2_yellow_0(X1,X3)),u1_struct_0(X1))|~r2_yellow_0(X1,X3)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_42, c_0_37]), ['final']).
% 0.14/0.41  cnf(c_0_54, plain, (esk2_3(X1,X2,X3)=esk1_2(X1,X4)|X3=esk1_2(X1,X2)|esk2_3(X1,X2,X3)!=k2_yellow_0(X1,X4)|~v5_orders_2(X1)|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_yellow_0(X1,X4)|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_40, c_0_23]), ['final']).
% 0.14/0.41  cnf(c_0_55, plain, (esk5_3(X1,X2,X3)=esk1_2(X1,X4)|X2=k2_yellow_0(X1,X3)|esk5_3(X1,X2,X3)!=k2_yellow_0(X1,X4)|~v5_orders_2(X1)|~r1_lattice3(X1,X3,X2)|~m1_subset_1(X2,u1_struct_0(X1))|~r2_yellow_0(X1,X4)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_40, c_0_29]), ['final']).
% 0.14/0.41  cnf(c_0_56, plain, (esk5_3(X1,X2,X3)=esk1_2(X1,X4)|r2_yellow_0(X1,X3)|esk5_3(X1,X2,X3)!=k2_yellow_0(X1,X4)|~v5_orders_2(X1)|~r1_lattice3(X1,X3,X2)|~m1_subset_1(X2,u1_struct_0(X1))|~r2_yellow_0(X1,X4)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_40, c_0_27]), ['final']).
% 0.14/0.41  cnf(c_0_57, plain, (k2_yellow_0(X1,X2)=esk1_2(X1,X3)|k2_yellow_0(X1,X2)!=k2_yellow_0(X1,X3)|~v5_orders_2(X1)|~r2_yellow_0(X1,X3)|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_40, c_0_43]), ['final']).
% 0.14/0.41  cnf(c_0_58, plain, (esk1_2(X1,X2)=esk1_2(X1,X3)|esk1_2(X1,X2)!=k2_yellow_0(X1,X3)|~v5_orders_2(X1)|~r2_yellow_0(X1,X3)|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_40, c_0_10]), ['final']).
% 0.14/0.41  cnf(c_0_59, plain, (k2_yellow_0(X1,X2)=esk1_2(X1,X3)|~v5_orders_2(X1)|~r1_lattice3(X1,X2,esk2_3(X1,X3,k2_yellow_0(X1,X2)))|~r1_lattice3(X1,X3,k2_yellow_0(X1,X2))|~m1_subset_1(esk2_3(X1,X3,k2_yellow_0(X1,X2)),u1_struct_0(X1))|~r2_yellow_0(X1,X3)|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_44, c_0_37]), ['final']).
% 0.14/0.41  cnf(c_0_60, plain, (k2_yellow_0(X1,X2)=k2_yellow_0(X1,X3)|~v5_orders_2(X1)|~r1_lattice3(X1,X2,esk5_3(X1,k2_yellow_0(X1,X2),X3))|~r1_lattice3(X1,X3,k2_yellow_0(X1,X2))|~m1_subset_1(esk5_3(X1,k2_yellow_0(X1,X2),X3),u1_struct_0(X1))|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_16, c_0_37]), ['final']).
% 0.14/0.41  cnf(c_0_61, plain, (r2_yellow_0(X1,X2)|~v5_orders_2(X1)|~r1_lattice3(X1,X3,esk5_3(X1,k2_yellow_0(X1,X3),X2))|~r1_lattice3(X1,X2,k2_yellow_0(X1,X3))|~m1_subset_1(esk5_3(X1,k2_yellow_0(X1,X3),X2),u1_struct_0(X1))|~r2_yellow_0(X1,X3)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_45, c_0_37]), ['final']).
% 0.14/0.41  cnf(c_0_62, plain, (r1_orders_2(X1,X2,k2_yellow_0(X1,X3))|~v5_orders_2(X1)|~r1_lattice3(X1,X3,X2)|~m1_subset_1(X2,u1_struct_0(X1))|~r2_yellow_0(X1,X3)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_9, c_0_37]), ['final']).
% 0.14/0.41  cnf(c_0_63, plain, (r1_orders_2(X1,k2_yellow_0(X1,X2),X3)|X3!=k2_yellow_0(X1,X2)|~v5_orders_2(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_46, c_0_37]), ['final']).
% 0.14/0.41  cnf(c_0_64, plain, (r1_lattice3(X1,X2,k2_yellow_0(X1,X2))|~v5_orders_2(X1)|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_18, c_0_37]), ['final']).
% 0.14/0.41  cnf(c_0_65, plain, (X1=k2_yellow_0(X2,X3)|r1_orders_2(X2,esk5_3(X2,X1,X3),X4)|X4!=k2_yellow_0(X2,X3)|~v5_orders_2(X2)|~r1_lattice3(X2,X3,X1)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~r2_yellow_0(X2,X3)|~l1_orders_2(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_17]), c_0_29]), ['final']).
% 0.14/0.41  cnf(c_0_66, plain, (r1_lattice3(X1,X2,esk3_3(X1,X2,X3))|r2_yellow_0(X1,X2)|esk4_3(X1,X2,X3)!=X3|~m1_subset_1(X3,u1_struct_0(X1))|~r1_lattice3(X1,X2,X3)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.14/0.41  cnf(c_0_67, plain, (m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))|r2_yellow_0(X1,X2)|esk4_3(X1,X2,X3)!=X3|~m1_subset_1(X3,u1_struct_0(X1))|~r1_lattice3(X1,X2,X3)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.14/0.41  cnf(c_0_68, plain, (r2_yellow_0(X1,X2)|esk4_3(X1,X2,X3)!=X3|~r1_orders_2(X1,esk3_3(X1,X2,X3),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~r1_lattice3(X1,X2,X3)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.14/0.41  cnf(c_0_69, negated_conjecture, (v25_waybel_0(esk6_0)|v1_xboole_0(X1)|r2_yellow_0(esk6_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_47]), ['final']).
% 0.14/0.41  cnf(c_0_70, negated_conjecture, (~r2_yellow_0(esk6_0,esk7_0)|~v25_waybel_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_47]), ['final']).
% 0.14/0.41  cnf(c_0_71, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0)))|~v25_waybel_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_47]), ['final']).
% 0.14/0.41  cnf(c_0_72, negated_conjecture, (~v1_xboole_0(esk7_0)|~v25_waybel_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_47]), ['final']).
% 0.14/0.41  cnf(c_0_73, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_47]), ['final']).
% 0.14/0.41  cnf(c_0_74, negated_conjecture, (v3_orders_2(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_47]), ['final']).
% 0.14/0.41  cnf(c_0_75, negated_conjecture, (v5_orders_2(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_47]), ['final']).
% 0.14/0.41  cnf(c_0_76, negated_conjecture, (l1_orders_2(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_47]), ['final']).
% 0.14/0.41  # SZS output end Saturation
% 0.14/0.41  # Proof object total steps             : 77
% 0.14/0.41  # Proof object clause steps            : 70
% 0.14/0.41  # Proof object formula steps           : 7
% 0.14/0.41  # Proof object conjectures             : 11
% 0.14/0.41  # Proof object clause conjectures      : 8
% 0.14/0.41  # Proof object formula conjectures     : 3
% 0.14/0.41  # Proof object initial clauses used    : 34
% 0.14/0.41  # Proof object initial formulas used   : 3
% 0.14/0.41  # Proof object generating inferences   : 36
% 0.14/0.41  # Proof object simplifying inferences  : 30
% 0.14/0.41  # Parsed axioms                        : 3
% 0.14/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.41  # Initial clauses                      : 34
% 0.14/0.41  # Removed in clause preprocessing      : 0
% 0.14/0.41  # Initial clauses in saturation        : 34
% 0.14/0.41  # Processed clauses                    : 123
% 0.14/0.41  # ...of these trivial                  : 0
% 0.14/0.41  # ...subsumed                          : 15
% 0.14/0.41  # ...remaining for further processing  : 108
% 0.14/0.41  # Other redundant clauses eliminated   : 0
% 0.14/0.41  # Clauses deleted for lack of memory   : 0
% 0.14/0.41  # Backward-subsumed                    : 11
% 0.14/0.41  # Backward-rewritten                   : 0
% 0.14/0.41  # Generated clauses                    : 79
% 0.14/0.41  # ...of the previous two non-trivial   : 61
% 0.14/0.41  # Contextual simplify-reflections      : 30
% 0.14/0.41  # Paramodulations                      : 77
% 0.14/0.41  # Factorizations                       : 0
% 0.14/0.41  # Equation resolutions                 : 2
% 0.14/0.41  # Propositional unsat checks           : 0
% 0.14/0.41  #    Propositional check models        : 0
% 0.14/0.41  #    Propositional check unsatisfiable : 0
% 0.14/0.41  #    Propositional clauses             : 0
% 0.14/0.41  #    Propositional clauses after purity: 0
% 0.14/0.41  #    Propositional unsat core size     : 0
% 0.14/0.41  #    Propositional preprocessing time  : 0.000
% 0.14/0.41  #    Propositional encoding time       : 0.000
% 0.14/0.41  #    Propositional solver time         : 0.000
% 0.14/0.41  #    Success case prop preproc time    : 0.000
% 0.14/0.41  #    Success case prop encoding time   : 0.000
% 0.14/0.41  #    Success case prop solver time     : 0.000
% 0.14/0.41  # Current number of processed clauses  : 63
% 0.14/0.41  #    Positive orientable unit clauses  : 3
% 0.14/0.41  #    Positive unorientable unit clauses: 0
% 0.14/0.41  #    Negative unit clauses             : 1
% 0.14/0.41  #    Non-unit-clauses                  : 59
% 0.14/0.41  # Current number of unprocessed clauses: 0
% 0.14/0.41  # ...number of literals in the above   : 0
% 0.14/0.41  # Current number of archived formulas  : 0
% 0.14/0.41  # Current number of archived clauses   : 45
% 0.14/0.41  # Clause-clause subsumption calls (NU) : 2625
% 0.14/0.41  # Rec. Clause-clause subsumption calls : 124
% 0.14/0.41  # Non-unit clause-clause subsumptions  : 56
% 0.14/0.41  # Unit Clause-clause subsumption calls : 0
% 0.14/0.41  # Rewrite failures with RHS unbound    : 0
% 0.14/0.41  # BW rewrite match attempts            : 0
% 0.14/0.41  # BW rewrite match successes           : 0
% 0.14/0.41  # Condensation attempts                : 0
% 0.14/0.41  # Condensation successes               : 0
% 0.14/0.41  # Termbank termtop insertions          : 6833
% 0.14/0.41  
% 0.14/0.41  # -------------------------------------------------
% 0.14/0.41  # User time                : 0.064 s
% 0.14/0.41  # System time              : 0.002 s
% 0.14/0.41  # Total time               : 0.065 s
% 0.14/0.41  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
