%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:27 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 404 expanded)
%              Number of clauses        :   48 ( 166 expanded)
%              Number of leaves         :   13 ( 101 expanded)
%              Depth                    :   12
%              Number of atoms          :  320 (2343 expanded)
%              Number of equality atoms :   35 ( 152 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(rc3_subset_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
      & ~ v1_subset_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).

fof(t8_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => ( r2_hidden(X4,X2)
                <=> r2_hidden(X4,X3) ) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).

fof(t8_waybel_7,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_yellow_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v2_waybel_0(X2,X1)
            & v13_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ( v1_subset_1(X2,u1_struct_0(X1))
          <=> ~ r2_hidden(k3_yellow_0(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).

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

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

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

fof(d11_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

fof(t42_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v1_yellow_0(X1)
        & l1_orders_2(X1) )
     => ( r1_yellow_0(X1,k1_xboole_0)
        & r2_yellow_0(X1,u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).

fof(t6_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r2_lattice3(X1,k1_xboole_0,X2)
            & r1_lattice3(X1,k1_xboole_0,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_0)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(c_0_13,plain,(
    ! [X36,X37] :
      ( ( ~ v1_subset_1(X37,X36)
        | X37 != X36
        | ~ m1_subset_1(X37,k1_zfmisc_1(X36)) )
      & ( X37 = X36
        | v1_subset_1(X37,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(X36)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

fof(c_0_14,plain,(
    ! [X12] :
      ( m1_subset_1(esk2_1(X12),k1_zfmisc_1(X12))
      & ~ v1_subset_1(esk2_1(X12),X12) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[rc3_subset_1])])])).

cnf(c_0_15,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,plain,
    ( m1_subset_1(esk2_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_17,plain,
    ( ~ v1_subset_1(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X8,X9,X10] :
      ( ( m1_subset_1(esk1_3(X8,X9,X10),X8)
        | X9 = X10
        | ~ m1_subset_1(X10,k1_zfmisc_1(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(X8)) )
      & ( ~ r2_hidden(esk1_3(X8,X9,X10),X9)
        | ~ r2_hidden(esk1_3(X8,X9,X10),X10)
        | X9 = X10
        | ~ m1_subset_1(X10,k1_zfmisc_1(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(X8)) )
      & ( r2_hidden(esk1_3(X8,X9,X10),X9)
        | r2_hidden(esk1_3(X8,X9,X10),X10)
        | X9 = X10
        | ~ m1_subset_1(X10,k1_zfmisc_1(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(X8)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_subset_1])])])])])).

cnf(c_0_19,plain,
    ( esk2_1(X1) = X1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & v1_yellow_0(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v2_waybel_0(X2,X1)
              & v13_waybel_0(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => ( v1_subset_1(X2,u1_struct_0(X1))
            <=> ~ r2_hidden(k3_yellow_0(X1),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t8_waybel_7])).

fof(c_0_21,plain,(
    ! [X30,X31,X32,X33] :
      ( ( ~ v13_waybel_0(X31,X30)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ m1_subset_1(X33,u1_struct_0(X30))
        | ~ r2_hidden(X32,X31)
        | ~ r1_orders_2(X30,X32,X33)
        | r2_hidden(X33,X31)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ l1_orders_2(X30) )
      & ( m1_subset_1(esk4_2(X30,X31),u1_struct_0(X30))
        | v13_waybel_0(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ l1_orders_2(X30) )
      & ( m1_subset_1(esk5_2(X30,X31),u1_struct_0(X30))
        | v13_waybel_0(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ l1_orders_2(X30) )
      & ( r2_hidden(esk4_2(X30,X31),X31)
        | v13_waybel_0(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ l1_orders_2(X30) )
      & ( r1_orders_2(X30,esk4_2(X30,X31),esk5_2(X30,X31))
        | v13_waybel_0(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ l1_orders_2(X30) )
      & ( ~ r2_hidden(esk5_2(X30,X31),X31)
        | v13_waybel_0(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ l1_orders_2(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).

fof(c_0_22,plain,(
    ! [X16,X17,X18] :
      ( ~ r2_hidden(X16,X17)
      | ~ m1_subset_1(X17,k1_zfmisc_1(X18))
      | m1_subset_1(X16,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_23,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),X1)
    | X2 = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_16,c_0_19])).

fof(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    & v3_orders_2(esk6_0)
    & v4_orders_2(esk6_0)
    & v5_orders_2(esk6_0)
    & v1_yellow_0(esk6_0)
    & l1_orders_2(esk6_0)
    & ~ v1_xboole_0(esk7_0)
    & v2_waybel_0(esk7_0,esk6_0)
    & v13_waybel_0(esk7_0,esk6_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0)))
    & ( ~ v1_subset_1(esk7_0,u1_struct_0(esk6_0))
      | r2_hidden(k3_yellow_0(esk6_0),esk7_0) )
    & ( v1_subset_1(esk7_0,u1_struct_0(esk6_0))
      | ~ r2_hidden(k3_yellow_0(esk6_0),esk7_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).

cnf(c_0_26,plain,
    ( r2_hidden(X4,X1)
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(X3,X1)
    | ~ r1_orders_2(X2,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( X1 = X2
    | m1_subset_1(esk1_3(X2,X1,X2),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_30,plain,(
    ! [X20,X21,X22,X23] :
      ( ( r2_lattice3(X20,X21,X22)
        | X22 != k1_yellow_0(X20,X21)
        | ~ r1_yellow_0(X20,X21)
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | ~ l1_orders_2(X20) )
      & ( ~ m1_subset_1(X23,u1_struct_0(X20))
        | ~ r2_lattice3(X20,X21,X23)
        | r1_orders_2(X20,X22,X23)
        | X22 != k1_yellow_0(X20,X21)
        | ~ r1_yellow_0(X20,X21)
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | ~ l1_orders_2(X20) )
      & ( m1_subset_1(esk3_3(X20,X21,X22),u1_struct_0(X20))
        | ~ r2_lattice3(X20,X21,X22)
        | X22 = k1_yellow_0(X20,X21)
        | ~ r1_yellow_0(X20,X21)
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | ~ l1_orders_2(X20) )
      & ( r2_lattice3(X20,X21,esk3_3(X20,X21,X22))
        | ~ r2_lattice3(X20,X21,X22)
        | X22 = k1_yellow_0(X20,X21)
        | ~ r1_yellow_0(X20,X21)
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | ~ l1_orders_2(X20) )
      & ( ~ r1_orders_2(X20,X22,esk3_3(X20,X21,X22))
        | ~ r2_lattice3(X20,X21,X22)
        | X22 = k1_yellow_0(X20,X21)
        | ~ r1_yellow_0(X20,X21)
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | ~ l1_orders_2(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).

fof(c_0_31,plain,(
    ! [X25,X26] :
      ( ~ l1_orders_2(X25)
      | m1_subset_1(k1_yellow_0(X25,X26),u1_struct_0(X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X2)
    | ~ v13_waybel_0(X2,X3)
    | ~ r1_orders_2(X3,X4,X1)
    | ~ l1_orders_2(X3)
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3)) ),
    inference(csr,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk6_0)),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( l1_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(k3_yellow_0(esk6_0),esk7_0)
    | ~ v1_subset_1(esk7_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | v1_subset_1(esk7_0,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_29])).

fof(c_0_37,plain,(
    ! [X19] :
      ( ~ l1_orders_2(X19)
      | k3_yellow_0(X19) = k1_yellow_0(X19,k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).

cnf(c_0_38,plain,
    ( r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | X4 != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_40,plain,(
    ! [X27] :
      ( ( r1_yellow_0(X27,k1_xboole_0)
        | v2_struct_0(X27)
        | ~ v5_orders_2(X27)
        | ~ v1_yellow_0(X27)
        | ~ l1_orders_2(X27) )
      & ( r2_yellow_0(X27,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ v5_orders_2(X27)
        | ~ v1_yellow_0(X27)
        | ~ l1_orders_2(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_0])])])])).

fof(c_0_41,plain,(
    ! [X28,X29] :
      ( ( r2_lattice3(X28,k1_xboole_0,X29)
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | ~ l1_orders_2(X28) )
      & ( r1_lattice3(X28,k1_xboole_0,X29)
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | ~ l1_orders_2(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_yellow_0])])])])).

fof(c_0_42,plain,(
    ! [X5,X6,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(X5))
      | ~ r2_hidden(X7,X6)
      | r2_hidden(X7,X5) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_43,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | r2_hidden(esk1_3(u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk6_0)),X1)
    | ~ v13_waybel_0(X1,esk6_0)
    | ~ r1_orders_2(esk6_0,X2,esk1_3(u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk6_0)))
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

cnf(c_0_44,negated_conjecture,
    ( v13_waybel_0(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_45,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | r2_hidden(k3_yellow_0(esk6_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_46,plain,
    ( k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_38]),c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_49,plain,
    ( r1_yellow_0(X1,k1_xboole_0)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( v1_yellow_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_51,negated_conjecture,
    ( v5_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_52,plain,
    ( r2_lattice3(X1,k1_xboole_0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_53,plain,
    ( X2 = X3
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_54,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_55,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | r2_hidden(esk1_3(u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk6_0)),esk7_0)
    | ~ r1_orders_2(esk6_0,X1,esk1_3(u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk6_0)))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_29])])).

cnf(c_0_56,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | r2_hidden(k1_yellow_0(esk6_0,k1_xboole_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_34])])).

cnf(c_0_57,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X1),esk1_3(u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk6_0)))
    | ~ r2_lattice3(esk6_0,X1,esk1_3(u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk6_0)))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_33]),c_0_34])])).

cnf(c_0_58,negated_conjecture,
    ( r1_yellow_0(esk6_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_51]),c_0_34])])).

cnf(c_0_59,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | r2_lattice3(esk6_0,k1_xboole_0,esk1_3(u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_33]),c_0_34])])).

cnf(c_0_60,plain,
    ( X1 = X2
    | ~ r2_hidden(esk1_3(X2,X1,X2),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_24]),c_0_54])).

fof(c_0_61,plain,(
    ! [X14,X15] :
      ( ~ m1_subset_1(X14,X15)
      | v1_xboole_0(X15)
      | r2_hidden(X14,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_62,negated_conjecture,
    ( v1_subset_1(esk7_0,u1_struct_0(esk6_0))
    | ~ r2_hidden(k3_yellow_0(esk6_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_63,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | r2_hidden(esk1_3(u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk6_0)),esk7_0)
    | ~ r1_orders_2(esk6_0,k1_yellow_0(esk6_0,k1_xboole_0),esk1_3(u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_64,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,k1_xboole_0),esk1_3(u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | ~ r2_hidden(esk1_3(u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk6_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_29])).

cnf(c_0_66,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( v1_subset_1(esk7_0,u1_struct_0(esk6_0))
    | ~ r2_hidden(k1_yellow_0(esk6_0,k1_xboole_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_46]),c_0_34])])).

cnf(c_0_68,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])).

cnf(c_0_69,plain,
    ( ~ v1_subset_1(X1,X1) ),
    inference(rw,[status(thm)],[c_0_17,c_0_19])).

cnf(c_0_70,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | r2_hidden(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_39])).

cnf(c_0_71,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_72,negated_conjecture,
    ( ~ r2_hidden(k1_yellow_0(esk6_0,k1_xboole_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_68]),c_0_69])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(k1_yellow_0(esk6_0,X1),esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_68]),c_0_34])]),c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_73])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:09:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___008_C18_F1_PI_SE_CS_SP_CO_S4S
% 0.19/0.38  # and selection function SelectNewComplexAHPNS.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.029 s
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 0.19/0.38  fof(rc3_subset_1, axiom, ![X1]:?[X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))&~(v1_subset_1(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_subset_1)).
% 0.19/0.38  fof(t8_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,X2)<=>r2_hidden(X4,X3)))=>X2=X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_subset_1)).
% 0.19/0.38  fof(t8_waybel_7, conjecture, ![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_7)).
% 0.19/0.38  fof(d20_waybel_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v13_waybel_0(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r2_hidden(X3,X2)&r1_orders_2(X1,X3,X4))=>r2_hidden(X4,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_waybel_0)).
% 0.19/0.38  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.19/0.38  fof(d9_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_yellow_0(X1,X2)=>(X3=k1_yellow_0(X1,X2)<=>(r2_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)=>r1_orders_2(X1,X3,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_yellow_0)).
% 0.19/0.38  fof(dt_k1_yellow_0, axiom, ![X1, X2]:(l1_orders_2(X1)=>m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 0.19/0.38  fof(d11_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_yellow_0)).
% 0.19/0.38  fof(t42_yellow_0, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>(r1_yellow_0(X1,k1_xboole_0)&r2_yellow_0(X1,u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_yellow_0)).
% 0.19/0.38  fof(t6_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(r2_lattice3(X1,k1_xboole_0,X2)&r1_lattice3(X1,k1_xboole_0,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_yellow_0)).
% 0.19/0.38  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.19/0.38  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.19/0.38  fof(c_0_13, plain, ![X36, X37]:((~v1_subset_1(X37,X36)|X37!=X36|~m1_subset_1(X37,k1_zfmisc_1(X36)))&(X37=X36|v1_subset_1(X37,X36)|~m1_subset_1(X37,k1_zfmisc_1(X36)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.19/0.38  fof(c_0_14, plain, ![X12]:(m1_subset_1(esk2_1(X12),k1_zfmisc_1(X12))&~v1_subset_1(esk2_1(X12),X12)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[rc3_subset_1])])])).
% 0.19/0.38  cnf(c_0_15, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_16, plain, (m1_subset_1(esk2_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_17, plain, (~v1_subset_1(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  fof(c_0_18, plain, ![X8, X9, X10]:((m1_subset_1(esk1_3(X8,X9,X10),X8)|X9=X10|~m1_subset_1(X10,k1_zfmisc_1(X8))|~m1_subset_1(X9,k1_zfmisc_1(X8)))&((~r2_hidden(esk1_3(X8,X9,X10),X9)|~r2_hidden(esk1_3(X8,X9,X10),X10)|X9=X10|~m1_subset_1(X10,k1_zfmisc_1(X8))|~m1_subset_1(X9,k1_zfmisc_1(X8)))&(r2_hidden(esk1_3(X8,X9,X10),X9)|r2_hidden(esk1_3(X8,X9,X10),X10)|X9=X10|~m1_subset_1(X10,k1_zfmisc_1(X8))|~m1_subset_1(X9,k1_zfmisc_1(X8))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_subset_1])])])])])).
% 0.19/0.38  cnf(c_0_19, plain, (esk2_1(X1)=X1), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])).
% 0.19/0.38  fof(c_0_20, negated_conjecture, ~(![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2)))))), inference(assume_negation,[status(cth)],[t8_waybel_7])).
% 0.19/0.38  fof(c_0_21, plain, ![X30, X31, X32, X33]:((~v13_waybel_0(X31,X30)|(~m1_subset_1(X32,u1_struct_0(X30))|(~m1_subset_1(X33,u1_struct_0(X30))|(~r2_hidden(X32,X31)|~r1_orders_2(X30,X32,X33)|r2_hidden(X33,X31))))|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|~l1_orders_2(X30))&((m1_subset_1(esk4_2(X30,X31),u1_struct_0(X30))|v13_waybel_0(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|~l1_orders_2(X30))&((m1_subset_1(esk5_2(X30,X31),u1_struct_0(X30))|v13_waybel_0(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|~l1_orders_2(X30))&(((r2_hidden(esk4_2(X30,X31),X31)|v13_waybel_0(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|~l1_orders_2(X30))&(r1_orders_2(X30,esk4_2(X30,X31),esk5_2(X30,X31))|v13_waybel_0(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|~l1_orders_2(X30)))&(~r2_hidden(esk5_2(X30,X31),X31)|v13_waybel_0(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|~l1_orders_2(X30)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).
% 0.19/0.38  fof(c_0_22, plain, ![X16, X17, X18]:(~r2_hidden(X16,X17)|~m1_subset_1(X17,k1_zfmisc_1(X18))|m1_subset_1(X16,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.19/0.38  cnf(c_0_23, plain, (m1_subset_1(esk1_3(X1,X2,X3),X1)|X2=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.38  cnf(c_0_24, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_16, c_0_19])).
% 0.19/0.38  fof(c_0_25, negated_conjecture, ((((((~v2_struct_0(esk6_0)&v3_orders_2(esk6_0))&v4_orders_2(esk6_0))&v5_orders_2(esk6_0))&v1_yellow_0(esk6_0))&l1_orders_2(esk6_0))&((((~v1_xboole_0(esk7_0)&v2_waybel_0(esk7_0,esk6_0))&v13_waybel_0(esk7_0,esk6_0))&m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0))))&((~v1_subset_1(esk7_0,u1_struct_0(esk6_0))|r2_hidden(k3_yellow_0(esk6_0),esk7_0))&(v1_subset_1(esk7_0,u1_struct_0(esk6_0))|~r2_hidden(k3_yellow_0(esk6_0),esk7_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).
% 0.19/0.38  cnf(c_0_26, plain, (r2_hidden(X4,X1)|~v13_waybel_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~r2_hidden(X3,X1)|~r1_orders_2(X2,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.38  cnf(c_0_27, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.38  cnf(c_0_28, plain, (X1=X2|m1_subset_1(esk1_3(X2,X1,X2),X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.38  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.38  fof(c_0_30, plain, ![X20, X21, X22, X23]:(((r2_lattice3(X20,X21,X22)|X22!=k1_yellow_0(X20,X21)|~r1_yellow_0(X20,X21)|~m1_subset_1(X22,u1_struct_0(X20))|~l1_orders_2(X20))&(~m1_subset_1(X23,u1_struct_0(X20))|(~r2_lattice3(X20,X21,X23)|r1_orders_2(X20,X22,X23))|X22!=k1_yellow_0(X20,X21)|~r1_yellow_0(X20,X21)|~m1_subset_1(X22,u1_struct_0(X20))|~l1_orders_2(X20)))&((m1_subset_1(esk3_3(X20,X21,X22),u1_struct_0(X20))|~r2_lattice3(X20,X21,X22)|X22=k1_yellow_0(X20,X21)|~r1_yellow_0(X20,X21)|~m1_subset_1(X22,u1_struct_0(X20))|~l1_orders_2(X20))&((r2_lattice3(X20,X21,esk3_3(X20,X21,X22))|~r2_lattice3(X20,X21,X22)|X22=k1_yellow_0(X20,X21)|~r1_yellow_0(X20,X21)|~m1_subset_1(X22,u1_struct_0(X20))|~l1_orders_2(X20))&(~r1_orders_2(X20,X22,esk3_3(X20,X21,X22))|~r2_lattice3(X20,X21,X22)|X22=k1_yellow_0(X20,X21)|~r1_yellow_0(X20,X21)|~m1_subset_1(X22,u1_struct_0(X20))|~l1_orders_2(X20))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).
% 0.19/0.38  fof(c_0_31, plain, ![X25, X26]:(~l1_orders_2(X25)|m1_subset_1(k1_yellow_0(X25,X26),u1_struct_0(X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).
% 0.19/0.38  cnf(c_0_32, plain, (r2_hidden(X1,X2)|~v13_waybel_0(X2,X3)|~r1_orders_2(X3,X4,X1)|~l1_orders_2(X3)|~r2_hidden(X4,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X1,u1_struct_0(X3))), inference(csr,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.38  cnf(c_0_33, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|m1_subset_1(esk1_3(u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk6_0)),u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.38  cnf(c_0_34, negated_conjecture, (l1_orders_2(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.38  cnf(c_0_35, negated_conjecture, (r2_hidden(k3_yellow_0(esk6_0),esk7_0)|~v1_subset_1(esk7_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.38  cnf(c_0_36, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|v1_subset_1(esk7_0,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_15, c_0_29])).
% 0.19/0.38  fof(c_0_37, plain, ![X19]:(~l1_orders_2(X19)|k3_yellow_0(X19)=k1_yellow_0(X19,k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).
% 0.19/0.38  cnf(c_0_38, plain, (r1_orders_2(X2,X4,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|X4!=k1_yellow_0(X2,X3)|~r1_yellow_0(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.38  cnf(c_0_39, plain, (m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.38  fof(c_0_40, plain, ![X27]:((r1_yellow_0(X27,k1_xboole_0)|(v2_struct_0(X27)|~v5_orders_2(X27)|~v1_yellow_0(X27)|~l1_orders_2(X27)))&(r2_yellow_0(X27,u1_struct_0(X27))|(v2_struct_0(X27)|~v5_orders_2(X27)|~v1_yellow_0(X27)|~l1_orders_2(X27)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_0])])])])).
% 0.19/0.38  fof(c_0_41, plain, ![X28, X29]:((r2_lattice3(X28,k1_xboole_0,X29)|~m1_subset_1(X29,u1_struct_0(X28))|~l1_orders_2(X28))&(r1_lattice3(X28,k1_xboole_0,X29)|~m1_subset_1(X29,u1_struct_0(X28))|~l1_orders_2(X28))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_yellow_0])])])])).
% 0.19/0.38  fof(c_0_42, plain, ![X5, X6, X7]:(~m1_subset_1(X6,k1_zfmisc_1(X5))|(~r2_hidden(X7,X6)|r2_hidden(X7,X5))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.19/0.38  cnf(c_0_43, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|r2_hidden(esk1_3(u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk6_0)),X1)|~v13_waybel_0(X1,esk6_0)|~r1_orders_2(esk6_0,X2,esk1_3(u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk6_0)))|~r2_hidden(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])])).
% 0.19/0.38  cnf(c_0_44, negated_conjecture, (v13_waybel_0(esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.38  cnf(c_0_45, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|r2_hidden(k3_yellow_0(esk6_0),esk7_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.38  cnf(c_0_46, plain, (k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.38  cnf(c_0_47, plain, (r1_orders_2(X1,k1_yellow_0(X1,X2),X3)|~r2_lattice3(X1,X2,X3)|~r1_yellow_0(X1,X2)|~l1_orders_2(X1)|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_38]), c_0_39])).
% 0.19/0.38  cnf(c_0_48, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.38  cnf(c_0_49, plain, (r1_yellow_0(X1,k1_xboole_0)|v2_struct_0(X1)|~v5_orders_2(X1)|~v1_yellow_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.38  cnf(c_0_50, negated_conjecture, (v1_yellow_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.38  cnf(c_0_51, negated_conjecture, (v5_orders_2(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.38  cnf(c_0_52, plain, (r2_lattice3(X1,k1_xboole_0,X2)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.38  cnf(c_0_53, plain, (X2=X3|~r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.38  cnf(c_0_54, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.38  cnf(c_0_55, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|r2_hidden(esk1_3(u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk6_0)),esk7_0)|~r1_orders_2(esk6_0,X1,esk1_3(u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk6_0)))|~r2_hidden(X1,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_29])])).
% 0.19/0.38  cnf(c_0_56, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|r2_hidden(k1_yellow_0(esk6_0,k1_xboole_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_34])])).
% 0.19/0.38  cnf(c_0_57, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X1),esk1_3(u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk6_0)))|~r2_lattice3(esk6_0,X1,esk1_3(u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk6_0)))|~r1_yellow_0(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_33]), c_0_34])])).
% 0.19/0.38  cnf(c_0_58, negated_conjecture, (r1_yellow_0(esk6_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_51]), c_0_34])])).
% 0.19/0.38  cnf(c_0_59, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|r2_lattice3(esk6_0,k1_xboole_0,esk1_3(u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_33]), c_0_34])])).
% 0.19/0.38  cnf(c_0_60, plain, (X1=X2|~r2_hidden(esk1_3(X2,X1,X2),X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_24]), c_0_54])).
% 0.19/0.38  fof(c_0_61, plain, ![X14, X15]:(~m1_subset_1(X14,X15)|(v1_xboole_0(X15)|r2_hidden(X14,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.19/0.38  cnf(c_0_62, negated_conjecture, (v1_subset_1(esk7_0,u1_struct_0(esk6_0))|~r2_hidden(k3_yellow_0(esk6_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.38  cnf(c_0_63, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|r2_hidden(esk1_3(u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk6_0)),esk7_0)|~r1_orders_2(esk6_0,k1_yellow_0(esk6_0,k1_xboole_0),esk1_3(u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk6_0)))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.19/0.38  cnf(c_0_64, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|r1_orders_2(esk6_0,k1_yellow_0(esk6_0,k1_xboole_0),esk1_3(u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])).
% 0.19/0.38  cnf(c_0_65, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|~r2_hidden(esk1_3(u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk6_0)),esk7_0)), inference(spm,[status(thm)],[c_0_60, c_0_29])).
% 0.19/0.38  cnf(c_0_66, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.38  cnf(c_0_67, negated_conjecture, (v1_subset_1(esk7_0,u1_struct_0(esk6_0))|~r2_hidden(k1_yellow_0(esk6_0,k1_xboole_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_46]), c_0_34])])).
% 0.19/0.38  cnf(c_0_68, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65])).
% 0.19/0.38  cnf(c_0_69, plain, (~v1_subset_1(X1,X1)), inference(rw,[status(thm)],[c_0_17, c_0_19])).
% 0.19/0.38  cnf(c_0_70, plain, (v1_xboole_0(u1_struct_0(X1))|r2_hidden(k1_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_66, c_0_39])).
% 0.19/0.38  cnf(c_0_71, negated_conjecture, (~v1_xboole_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.38  cnf(c_0_72, negated_conjecture, (~r2_hidden(k1_yellow_0(esk6_0,k1_xboole_0),esk7_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_68]), c_0_69])).
% 0.19/0.38  cnf(c_0_73, negated_conjecture, (r2_hidden(k1_yellow_0(esk6_0,X1),esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_68]), c_0_34])]), c_0_71])).
% 0.19/0.38  cnf(c_0_74, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_73])]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 75
% 0.19/0.38  # Proof object clause steps            : 48
% 0.19/0.38  # Proof object formula steps           : 27
% 0.19/0.38  # Proof object conjectures             : 29
% 0.19/0.38  # Proof object clause conjectures      : 26
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 23
% 0.19/0.38  # Proof object initial formulas used   : 13
% 0.19/0.38  # Proof object generating inferences   : 19
% 0.19/0.38  # Proof object simplifying inferences  : 32
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 13
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 39
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 39
% 0.19/0.38  # Processed clauses                    : 160
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 32
% 0.19/0.38  # ...remaining for further processing  : 128
% 0.19/0.38  # Other redundant clauses eliminated   : 3
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 4
% 0.19/0.38  # Backward-rewritten                   : 63
% 0.19/0.38  # Generated clauses                    : 184
% 0.19/0.38  # ...of the previous two non-trivial   : 185
% 0.19/0.38  # Contextual simplify-reflections      : 12
% 0.19/0.38  # Paramodulations                      : 181
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 3
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 58
% 0.19/0.38  #    Positive orientable unit clauses  : 15
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 4
% 0.19/0.38  #    Non-unit-clauses                  : 39
% 0.19/0.38  # Current number of unprocessed clauses: 53
% 0.19/0.38  # ...number of literals in the above   : 241
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 67
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 1064
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 375
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 44
% 0.19/0.38  # Unit Clause-clause subsumption calls : 95
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 15
% 0.19/0.38  # BW rewrite match successes           : 6
% 0.19/0.38  # Condensation attempts                : 161
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 7267
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.041 s
% 0.19/0.38  # System time              : 0.004 s
% 0.19/0.38  # Total time               : 0.044 s
% 0.19/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
