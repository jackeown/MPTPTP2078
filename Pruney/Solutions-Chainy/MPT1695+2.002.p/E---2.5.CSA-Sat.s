%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:35 EST 2020

% Result     : CounterSatisfiable 0.13s
% Output     : Saturation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   38 (  91 expanded)
%              Number of clauses        :   27 (  30 expanded)
%              Number of leaves         :    5 (  26 expanded)
%              Depth                    :    4
%              Number of atoms          :  287 (1161 expanded)
%              Number of equality atoms :   26 (  99 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal clause size      :   50 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d9_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r1_yellow_0(X1,X2)
           => ( X3 = k1_yellow_0(X1,X2)
            <=> ( r2_lattice3(X1,X2,X3)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r2_lattice3(X1,X2,X4)
                     => r1_orders_2(X1,X3,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).

fof(dt_k1_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(t30_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( ( X2 = k1_yellow_0(X1,X3)
                  & r1_yellow_0(X1,X3) )
               => ( r2_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r2_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X2,X4) ) ) ) )
              & ( ( r2_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r2_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X2,X4) ) ) )
               => ( X2 = k1_yellow_0(X1,X3)
                  & r1_yellow_0(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_yellow_0)).

fof(t75_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ( v24_waybel_0(X1)
      <=> ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v1_waybel_0(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => r1_yellow_0(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_waybel_0)).

fof(redefinition_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_orders_2(X1,X2,X3)
      <=> r1_orders_2(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(c_0_5,plain,(
    ! [X8,X9,X10,X11] :
      ( ( r2_lattice3(X8,X9,X10)
        | X10 != k1_yellow_0(X8,X9)
        | ~ r1_yellow_0(X8,X9)
        | ~ m1_subset_1(X10,u1_struct_0(X8))
        | ~ l1_orders_2(X8) )
      & ( ~ m1_subset_1(X11,u1_struct_0(X8))
        | ~ r2_lattice3(X8,X9,X11)
        | r1_orders_2(X8,X10,X11)
        | X10 != k1_yellow_0(X8,X9)
        | ~ r1_yellow_0(X8,X9)
        | ~ m1_subset_1(X10,u1_struct_0(X8))
        | ~ l1_orders_2(X8) )
      & ( m1_subset_1(esk1_3(X8,X9,X10),u1_struct_0(X8))
        | ~ r2_lattice3(X8,X9,X10)
        | X10 = k1_yellow_0(X8,X9)
        | ~ r1_yellow_0(X8,X9)
        | ~ m1_subset_1(X10,u1_struct_0(X8))
        | ~ l1_orders_2(X8) )
      & ( r2_lattice3(X8,X9,esk1_3(X8,X9,X10))
        | ~ r2_lattice3(X8,X9,X10)
        | X10 = k1_yellow_0(X8,X9)
        | ~ r1_yellow_0(X8,X9)
        | ~ m1_subset_1(X10,u1_struct_0(X8))
        | ~ l1_orders_2(X8) )
      & ( ~ r1_orders_2(X8,X10,esk1_3(X8,X9,X10))
        | ~ r2_lattice3(X8,X9,X10)
        | X10 = k1_yellow_0(X8,X9)
        | ~ r1_yellow_0(X8,X9)
        | ~ m1_subset_1(X10,u1_struct_0(X8))
        | ~ l1_orders_2(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).

fof(c_0_6,plain,(
    ! [X13,X14] :
      ( ~ l1_orders_2(X13)
      | m1_subset_1(k1_yellow_0(X13,X14),u1_struct_0(X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

cnf(c_0_7,plain,
    ( r2_lattice3(X1,X2,X3)
    | X3 != k1_yellow_0(X1,X2)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_8,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

fof(c_0_9,plain,(
    ! [X15,X16,X17,X18,X19] :
      ( ( r2_lattice3(X15,X17,X16)
        | X16 != k1_yellow_0(X15,X17)
        | ~ r1_yellow_0(X15,X17)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) )
      & ( ~ m1_subset_1(X18,u1_struct_0(X15))
        | ~ r2_lattice3(X15,X17,X18)
        | r1_orders_2(X15,X16,X18)
        | X16 != k1_yellow_0(X15,X17)
        | ~ r1_yellow_0(X15,X17)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) )
      & ( X16 = k1_yellow_0(X15,X19)
        | m1_subset_1(esk2_3(X15,X16,X19),u1_struct_0(X15))
        | ~ r2_lattice3(X15,X19,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) )
      & ( r1_yellow_0(X15,X19)
        | m1_subset_1(esk2_3(X15,X16,X19),u1_struct_0(X15))
        | ~ r2_lattice3(X15,X19,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) )
      & ( X16 = k1_yellow_0(X15,X19)
        | r2_lattice3(X15,X19,esk2_3(X15,X16,X19))
        | ~ r2_lattice3(X15,X19,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) )
      & ( r1_yellow_0(X15,X19)
        | r2_lattice3(X15,X19,esk2_3(X15,X16,X19))
        | ~ r2_lattice3(X15,X19,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) )
      & ( X16 = k1_yellow_0(X15,X19)
        | ~ r1_orders_2(X15,X16,esk2_3(X15,X16,X19))
        | ~ r2_lattice3(X15,X19,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) )
      & ( r1_yellow_0(X15,X19)
        | ~ r1_orders_2(X15,X16,esk2_3(X15,X16,X19))
        | ~ r2_lattice3(X15,X19,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_yellow_0])])])])])])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ( v24_waybel_0(X1)
        <=> ! [X2] :
              ( ( ~ v1_xboole_0(X2)
                & v1_waybel_0(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
             => r1_yellow_0(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t75_waybel_0])).

cnf(c_0_11,plain,
    ( r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | X4 != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_12,plain,
    ( r2_lattice3(X1,X2,esk1_3(X1,X2,X3))
    | X3 = k1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_13,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | X3 = k1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_14,plain,
    ( r2_lattice3(X1,X2,k1_yellow_0(X1,X2))
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_7]),c_0_8]),
    [final]).

cnf(c_0_15,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | r2_lattice3(X2,X3,esk2_3(X2,X1,X3))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_16,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | m1_subset_1(esk2_3(X2,X1,X3),u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

fof(c_0_17,plain,(
    ! [X5,X6,X7] :
      ( ( ~ r3_orders_2(X5,X6,X7)
        | r1_orders_2(X5,X6,X7)
        | v2_struct_0(X5)
        | ~ v3_orders_2(X5)
        | ~ l1_orders_2(X5)
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ m1_subset_1(X7,u1_struct_0(X5)) )
      & ( ~ r1_orders_2(X5,X6,X7)
        | r3_orders_2(X5,X6,X7)
        | v2_struct_0(X5)
        | ~ v3_orders_2(X5)
        | ~ l1_orders_2(X5)
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ m1_subset_1(X7,u1_struct_0(X5)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

fof(c_0_18,negated_conjecture,(
    ! [X23] :
      ( ~ v2_struct_0(esk3_0)
      & v3_orders_2(esk3_0)
      & v5_orders_2(esk3_0)
      & l1_orders_2(esk3_0)
      & ( ~ v1_xboole_0(esk4_0)
        | ~ v24_waybel_0(esk3_0) )
      & ( v1_waybel_0(esk4_0,esk3_0)
        | ~ v24_waybel_0(esk3_0) )
      & ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
        | ~ v24_waybel_0(esk3_0) )
      & ( ~ r1_yellow_0(esk3_0,esk4_0)
        | ~ v24_waybel_0(esk3_0) )
      & ( v24_waybel_0(esk3_0)
        | v1_xboole_0(X23)
        | ~ v1_waybel_0(X23,esk3_0)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(esk3_0)))
        | r1_yellow_0(esk3_0,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])])).

cnf(c_0_19,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | r1_orders_2(X2,X4,esk1_3(X2,X3,X1))
    | X4 != k1_yellow_0(X2,X3)
    | ~ r2_lattice3(X2,X3,X1)
    | ~ r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),
    [final]).

cnf(c_0_20,plain,
    ( r1_orders_2(X1,X2,k1_yellow_0(X1,X3))
    | X2 != k1_yellow_0(X1,X3)
    | ~ r1_yellow_0(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_14]),c_0_8]),
    [final]).

cnf(c_0_21,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | r1_orders_2(X2,X4,esk2_3(X2,X1,X3))
    | X4 != k1_yellow_0(X2,X3)
    | ~ v5_orders_2(X2)
    | ~ r2_lattice3(X2,X3,X1)
    | ~ r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_15]),c_0_16]),
    [final]).

cnf(c_0_22,plain,
    ( r1_yellow_0(X1,X2)
    | r2_lattice3(X1,X2,esk2_3(X1,X3,X2))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_23,plain,
    ( X2 = k1_yellow_0(X1,X3)
    | ~ r1_orders_2(X1,X2,esk1_3(X1,X3,X2))
    | ~ r2_lattice3(X1,X3,X2)
    | ~ r1_yellow_0(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_24,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | ~ r1_orders_2(X2,X1,esk2_3(X2,X1,X3))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_25,plain,
    ( r1_yellow_0(X1,X2)
    | m1_subset_1(esk2_3(X1,X3,X2),u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_26,plain,
    ( r1_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,X3,esk2_3(X1,X3,X2))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_27,plain,
    ( r3_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_28,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_29,negated_conjecture,
    ( v24_waybel_0(esk3_0)
    | v1_xboole_0(X1)
    | r1_yellow_0(esk3_0,X1)
    | ~ v1_waybel_0(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ v24_waybel_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_31,negated_conjecture,
    ( v1_waybel_0(esk4_0,esk3_0)
    | ~ v24_waybel_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_32,negated_conjecture,
    ( ~ r1_yellow_0(esk3_0,esk4_0)
    | ~ v24_waybel_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_33,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0)
    | ~ v24_waybel_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_34,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_35,negated_conjecture,
    ( v5_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_36,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_37,negated_conjecture,
    ( v3_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:28:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.13/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # No proof found!
% 0.13/0.38  # SZS status CounterSatisfiable
% 0.13/0.38  # SZS output start Saturation
% 0.13/0.38  fof(d9_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_yellow_0(X1,X2)=>(X3=k1_yellow_0(X1,X2)<=>(r2_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)=>r1_orders_2(X1,X3,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_yellow_0)).
% 0.13/0.38  fof(dt_k1_yellow_0, axiom, ![X1, X2]:(l1_orders_2(X1)=>m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 0.13/0.38  fof(t30_yellow_0, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(((X2=k1_yellow_0(X1,X3)&r1_yellow_0(X1,X3))=>(r2_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X3,X4)=>r1_orders_2(X1,X2,X4)))))&((r2_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X3,X4)=>r1_orders_2(X1,X2,X4))))=>(X2=k1_yellow_0(X1,X3)&r1_yellow_0(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_yellow_0)).
% 0.13/0.38  fof(t75_waybel_0, conjecture, ![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>(v24_waybel_0(X1)<=>![X2]:(((~(v1_xboole_0(X2))&v1_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>r1_yellow_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_waybel_0)).
% 0.13/0.38  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 0.13/0.38  fof(c_0_5, plain, ![X8, X9, X10, X11]:(((r2_lattice3(X8,X9,X10)|X10!=k1_yellow_0(X8,X9)|~r1_yellow_0(X8,X9)|~m1_subset_1(X10,u1_struct_0(X8))|~l1_orders_2(X8))&(~m1_subset_1(X11,u1_struct_0(X8))|(~r2_lattice3(X8,X9,X11)|r1_orders_2(X8,X10,X11))|X10!=k1_yellow_0(X8,X9)|~r1_yellow_0(X8,X9)|~m1_subset_1(X10,u1_struct_0(X8))|~l1_orders_2(X8)))&((m1_subset_1(esk1_3(X8,X9,X10),u1_struct_0(X8))|~r2_lattice3(X8,X9,X10)|X10=k1_yellow_0(X8,X9)|~r1_yellow_0(X8,X9)|~m1_subset_1(X10,u1_struct_0(X8))|~l1_orders_2(X8))&((r2_lattice3(X8,X9,esk1_3(X8,X9,X10))|~r2_lattice3(X8,X9,X10)|X10=k1_yellow_0(X8,X9)|~r1_yellow_0(X8,X9)|~m1_subset_1(X10,u1_struct_0(X8))|~l1_orders_2(X8))&(~r1_orders_2(X8,X10,esk1_3(X8,X9,X10))|~r2_lattice3(X8,X9,X10)|X10=k1_yellow_0(X8,X9)|~r1_yellow_0(X8,X9)|~m1_subset_1(X10,u1_struct_0(X8))|~l1_orders_2(X8))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).
% 0.13/0.38  fof(c_0_6, plain, ![X13, X14]:(~l1_orders_2(X13)|m1_subset_1(k1_yellow_0(X13,X14),u1_struct_0(X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).
% 0.13/0.38  cnf(c_0_7, plain, (r2_lattice3(X1,X2,X3)|X3!=k1_yellow_0(X1,X2)|~r1_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.13/0.38  cnf(c_0_8, plain, (m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.13/0.38  fof(c_0_9, plain, ![X15, X16, X17, X18, X19]:(((r2_lattice3(X15,X17,X16)|(X16!=k1_yellow_0(X15,X17)|~r1_yellow_0(X15,X17))|~m1_subset_1(X16,u1_struct_0(X15))|(~v5_orders_2(X15)|~l1_orders_2(X15)))&(~m1_subset_1(X18,u1_struct_0(X15))|(~r2_lattice3(X15,X17,X18)|r1_orders_2(X15,X16,X18))|(X16!=k1_yellow_0(X15,X17)|~r1_yellow_0(X15,X17))|~m1_subset_1(X16,u1_struct_0(X15))|(~v5_orders_2(X15)|~l1_orders_2(X15))))&(((X16=k1_yellow_0(X15,X19)|(m1_subset_1(esk2_3(X15,X16,X19),u1_struct_0(X15))|~r2_lattice3(X15,X19,X16))|~m1_subset_1(X16,u1_struct_0(X15))|(~v5_orders_2(X15)|~l1_orders_2(X15)))&(r1_yellow_0(X15,X19)|(m1_subset_1(esk2_3(X15,X16,X19),u1_struct_0(X15))|~r2_lattice3(X15,X19,X16))|~m1_subset_1(X16,u1_struct_0(X15))|(~v5_orders_2(X15)|~l1_orders_2(X15))))&(((X16=k1_yellow_0(X15,X19)|(r2_lattice3(X15,X19,esk2_3(X15,X16,X19))|~r2_lattice3(X15,X19,X16))|~m1_subset_1(X16,u1_struct_0(X15))|(~v5_orders_2(X15)|~l1_orders_2(X15)))&(r1_yellow_0(X15,X19)|(r2_lattice3(X15,X19,esk2_3(X15,X16,X19))|~r2_lattice3(X15,X19,X16))|~m1_subset_1(X16,u1_struct_0(X15))|(~v5_orders_2(X15)|~l1_orders_2(X15))))&((X16=k1_yellow_0(X15,X19)|(~r1_orders_2(X15,X16,esk2_3(X15,X16,X19))|~r2_lattice3(X15,X19,X16))|~m1_subset_1(X16,u1_struct_0(X15))|(~v5_orders_2(X15)|~l1_orders_2(X15)))&(r1_yellow_0(X15,X19)|(~r1_orders_2(X15,X16,esk2_3(X15,X16,X19))|~r2_lattice3(X15,X19,X16))|~m1_subset_1(X16,u1_struct_0(X15))|(~v5_orders_2(X15)|~l1_orders_2(X15))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_yellow_0])])])])])])).
% 0.13/0.38  fof(c_0_10, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>(v24_waybel_0(X1)<=>![X2]:(((~(v1_xboole_0(X2))&v1_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>r1_yellow_0(X1,X2))))), inference(assume_negation,[status(cth)],[t75_waybel_0])).
% 0.13/0.38  cnf(c_0_11, plain, (r1_orders_2(X2,X4,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|X4!=k1_yellow_0(X2,X3)|~r1_yellow_0(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.13/0.38  cnf(c_0_12, plain, (r2_lattice3(X1,X2,esk1_3(X1,X2,X3))|X3=k1_yellow_0(X1,X2)|~r2_lattice3(X1,X2,X3)|~r1_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.13/0.38  cnf(c_0_13, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|X3=k1_yellow_0(X1,X2)|~r2_lattice3(X1,X2,X3)|~r1_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.13/0.38  cnf(c_0_14, plain, (r2_lattice3(X1,X2,k1_yellow_0(X1,X2))|~r1_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_7]), c_0_8]), ['final']).
% 0.13/0.38  cnf(c_0_15, plain, (X1=k1_yellow_0(X2,X3)|r2_lattice3(X2,X3,esk2_3(X2,X1,X3))|~r2_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.13/0.38  cnf(c_0_16, plain, (X1=k1_yellow_0(X2,X3)|m1_subset_1(esk2_3(X2,X1,X3),u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.13/0.38  fof(c_0_17, plain, ![X5, X6, X7]:((~r3_orders_2(X5,X6,X7)|r1_orders_2(X5,X6,X7)|(v2_struct_0(X5)|~v3_orders_2(X5)|~l1_orders_2(X5)|~m1_subset_1(X6,u1_struct_0(X5))|~m1_subset_1(X7,u1_struct_0(X5))))&(~r1_orders_2(X5,X6,X7)|r3_orders_2(X5,X6,X7)|(v2_struct_0(X5)|~v3_orders_2(X5)|~l1_orders_2(X5)|~m1_subset_1(X6,u1_struct_0(X5))|~m1_subset_1(X7,u1_struct_0(X5))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.13/0.38  fof(c_0_18, negated_conjecture, ![X23]:((((~v2_struct_0(esk3_0)&v3_orders_2(esk3_0))&v5_orders_2(esk3_0))&l1_orders_2(esk3_0))&(((((~v1_xboole_0(esk4_0)|~v24_waybel_0(esk3_0))&(v1_waybel_0(esk4_0,esk3_0)|~v24_waybel_0(esk3_0)))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))|~v24_waybel_0(esk3_0)))&(~r1_yellow_0(esk3_0,esk4_0)|~v24_waybel_0(esk3_0)))&(v24_waybel_0(esk3_0)|(v1_xboole_0(X23)|~v1_waybel_0(X23,esk3_0)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(esk3_0)))|r1_yellow_0(esk3_0,X23))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])])).
% 0.13/0.38  cnf(c_0_19, plain, (X1=k1_yellow_0(X2,X3)|r1_orders_2(X2,X4,esk1_3(X2,X3,X1))|X4!=k1_yellow_0(X2,X3)|~r2_lattice3(X2,X3,X1)|~r1_yellow_0(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~l1_orders_2(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13]), ['final']).
% 0.13/0.38  cnf(c_0_20, plain, (r1_orders_2(X1,X2,k1_yellow_0(X1,X3))|X2!=k1_yellow_0(X1,X3)|~r1_yellow_0(X1,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_14]), c_0_8]), ['final']).
% 0.13/0.38  cnf(c_0_21, plain, (X1=k1_yellow_0(X2,X3)|r1_orders_2(X2,X4,esk2_3(X2,X1,X3))|X4!=k1_yellow_0(X2,X3)|~v5_orders_2(X2)|~r2_lattice3(X2,X3,X1)|~r1_yellow_0(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~l1_orders_2(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_15]), c_0_16]), ['final']).
% 0.13/0.38  cnf(c_0_22, plain, (r1_yellow_0(X1,X2)|r2_lattice3(X1,X2,esk2_3(X1,X3,X2))|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.13/0.38  cnf(c_0_23, plain, (X2=k1_yellow_0(X1,X3)|~r1_orders_2(X1,X2,esk1_3(X1,X3,X2))|~r2_lattice3(X1,X3,X2)|~r1_yellow_0(X1,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.13/0.38  cnf(c_0_24, plain, (X1=k1_yellow_0(X2,X3)|~r1_orders_2(X2,X1,esk2_3(X2,X1,X3))|~r2_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.13/0.38  cnf(c_0_25, plain, (r1_yellow_0(X1,X2)|m1_subset_1(esk2_3(X1,X3,X2),u1_struct_0(X1))|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.13/0.38  cnf(c_0_26, plain, (r1_yellow_0(X1,X2)|~r1_orders_2(X1,X3,esk2_3(X1,X3,X2))|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.13/0.38  cnf(c_0_27, plain, (r3_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.13/0.38  cnf(c_0_28, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r3_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (v24_waybel_0(esk3_0)|v1_xboole_0(X1)|r1_yellow_0(esk3_0,X1)|~v1_waybel_0(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))|~v24_waybel_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (v1_waybel_0(esk4_0,esk3_0)|~v24_waybel_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (~r1_yellow_0(esk3_0,esk4_0)|~v24_waybel_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (~v1_xboole_0(esk4_0)|~v24_waybel_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (v5_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (l1_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (v3_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.13/0.38  # SZS output end Saturation
% 0.13/0.38  # Proof object total steps             : 38
% 0.13/0.38  # Proof object clause steps            : 27
% 0.13/0.38  # Proof object formula steps           : 11
% 0.13/0.38  # Proof object conjectures             : 12
% 0.13/0.38  # Proof object clause conjectures      : 9
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 23
% 0.13/0.38  # Proof object initial formulas used   : 5
% 0.13/0.38  # Proof object generating inferences   : 4
% 0.13/0.38  # Proof object simplifying inferences  : 4
% 0.13/0.38  # Parsed axioms                        : 5
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 25
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 25
% 0.13/0.38  # Processed clauses                    : 52
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 2
% 0.13/0.38  # ...remaining for further processing  : 50
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 0
% 0.13/0.38  # Generated clauses                    : 10
% 0.13/0.38  # ...of the previous two non-trivial   : 4
% 0.13/0.38  # Contextual simplify-reflections      : 4
% 0.13/0.38  # Paramodulations                      : 9
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 1
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 27
% 0.13/0.38  #    Positive orientable unit clauses  : 3
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 1
% 0.13/0.38  #    Non-unit-clauses                  : 23
% 0.13/0.38  # Current number of unprocessed clauses: 0
% 0.13/0.38  # ...number of literals in the above   : 0
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 23
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 153
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 32
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 6
% 0.13/0.38  # Unit Clause-clause subsumption calls : 0
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 0
% 0.13/0.38  # BW rewrite match successes           : 0
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 2898
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.033 s
% 0.13/0.38  # System time              : 0.002 s
% 0.13/0.38  # Total time               : 0.035 s
% 0.13/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
