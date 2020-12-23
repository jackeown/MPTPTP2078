%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:25 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 426 expanded)
%              Number of clauses        :   52 ( 176 expanded)
%              Number of leaves         :   15 ( 107 expanded)
%              Depth                    :   12
%              Number of atoms          :  350 (2481 expanded)
%              Number of equality atoms :   36 ( 154 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

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

fof(d9_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r2_lattice3(X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r1_orders_2(X1,X4,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_15,negated_conjecture,(
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

fof(c_0_16,plain,(
    ! [X43,X44] :
      ( ( ~ v1_subset_1(X44,X43)
        | X44 != X43
        | ~ m1_subset_1(X44,k1_zfmisc_1(X43)) )
      & ( X44 = X43
        | v1_subset_1(X44,X43)
        | ~ m1_subset_1(X44,k1_zfmisc_1(X43)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

fof(c_0_17,plain,(
    ! [X16] :
      ( m1_subset_1(esk3_1(X16),k1_zfmisc_1(X16))
      & ~ v1_subset_1(esk3_1(X16),X16) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[rc3_subset_1])])])).

fof(c_0_18,plain,(
    ! [X12,X13,X14] :
      ( ( m1_subset_1(esk2_3(X12,X13,X14),X12)
        | X13 = X14
        | ~ m1_subset_1(X14,k1_zfmisc_1(X12))
        | ~ m1_subset_1(X13,k1_zfmisc_1(X12)) )
      & ( ~ r2_hidden(esk2_3(X12,X13,X14),X13)
        | ~ r2_hidden(esk2_3(X12,X13,X14),X14)
        | X13 = X14
        | ~ m1_subset_1(X14,k1_zfmisc_1(X12))
        | ~ m1_subset_1(X13,k1_zfmisc_1(X12)) )
      & ( r2_hidden(esk2_3(X12,X13,X14),X13)
        | r2_hidden(esk2_3(X12,X13,X14),X14)
        | X13 = X14
        | ~ m1_subset_1(X14,k1_zfmisc_1(X12))
        | ~ m1_subset_1(X13,k1_zfmisc_1(X12)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_subset_1])])])])])).

fof(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk8_0)
    & v3_orders_2(esk8_0)
    & v4_orders_2(esk8_0)
    & v5_orders_2(esk8_0)
    & v1_yellow_0(esk8_0)
    & l1_orders_2(esk8_0)
    & ~ v1_xboole_0(esk9_0)
    & v2_waybel_0(esk9_0,esk8_0)
    & v13_waybel_0(esk9_0,esk8_0)
    & m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(esk8_0)))
    & ( ~ v1_subset_1(esk9_0,u1_struct_0(esk8_0))
      | r2_hidden(k3_yellow_0(esk8_0),esk9_0) )
    & ( v1_subset_1(esk9_0,u1_struct_0(esk8_0))
      | ~ r2_hidden(k3_yellow_0(esk8_0),esk9_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

cnf(c_0_20,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( m1_subset_1(esk3_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( ~ v1_subset_1(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X37,X38,X39,X40] :
      ( ( ~ v13_waybel_0(X38,X37)
        | ~ m1_subset_1(X39,u1_struct_0(X37))
        | ~ m1_subset_1(X40,u1_struct_0(X37))
        | ~ r2_hidden(X39,X38)
        | ~ r1_orders_2(X37,X39,X40)
        | r2_hidden(X40,X38)
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))
        | ~ l1_orders_2(X37) )
      & ( m1_subset_1(esk6_2(X37,X38),u1_struct_0(X37))
        | v13_waybel_0(X38,X37)
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))
        | ~ l1_orders_2(X37) )
      & ( m1_subset_1(esk7_2(X37,X38),u1_struct_0(X37))
        | v13_waybel_0(X38,X37)
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))
        | ~ l1_orders_2(X37) )
      & ( r2_hidden(esk6_2(X37,X38),X38)
        | v13_waybel_0(X38,X37)
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))
        | ~ l1_orders_2(X37) )
      & ( r1_orders_2(X37,esk6_2(X37,X38),esk7_2(X37,X38))
        | v13_waybel_0(X38,X37)
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))
        | ~ l1_orders_2(X37) )
      & ( ~ r2_hidden(esk7_2(X37,X38),X38)
        | v13_waybel_0(X38,X37)
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))
        | ~ l1_orders_2(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).

fof(c_0_24,plain,(
    ! [X20,X21,X22] :
      ( ~ r2_hidden(X20,X21)
      | ~ m1_subset_1(X21,k1_zfmisc_1(X22))
      | m1_subset_1(X20,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_25,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),X1)
    | X2 = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( esk3_1(X1) = X1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

fof(c_0_28,plain,(
    ! [X9,X10,X11] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | ~ r2_hidden(X11,X10)
      | r2_hidden(X11,X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_29,plain,
    ( r2_hidden(X4,X1)
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(X3,X1)
    | ~ r1_orders_2(X2,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( X1 = esk9_0
    | m1_subset_1(esk2_3(u1_struct_0(esk8_0),X1,esk9_0),u1_struct_0(esk8_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_21,c_0_27])).

cnf(c_0_33,plain,
    ( X2 = X3
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_34,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_35,plain,(
    ! [X29,X30,X31,X32] :
      ( ( r2_lattice3(X29,X30,X31)
        | X31 != k1_yellow_0(X29,X30)
        | ~ r1_yellow_0(X29,X30)
        | ~ m1_subset_1(X31,u1_struct_0(X29))
        | ~ l1_orders_2(X29) )
      & ( ~ m1_subset_1(X32,u1_struct_0(X29))
        | ~ r2_lattice3(X29,X30,X32)
        | r1_orders_2(X29,X31,X32)
        | X31 != k1_yellow_0(X29,X30)
        | ~ r1_yellow_0(X29,X30)
        | ~ m1_subset_1(X31,u1_struct_0(X29))
        | ~ l1_orders_2(X29) )
      & ( m1_subset_1(esk5_3(X29,X30,X31),u1_struct_0(X29))
        | ~ r2_lattice3(X29,X30,X31)
        | X31 = k1_yellow_0(X29,X30)
        | ~ r1_yellow_0(X29,X30)
        | ~ m1_subset_1(X31,u1_struct_0(X29))
        | ~ l1_orders_2(X29) )
      & ( r2_lattice3(X29,X30,esk5_3(X29,X30,X31))
        | ~ r2_lattice3(X29,X30,X31)
        | X31 = k1_yellow_0(X29,X30)
        | ~ r1_yellow_0(X29,X30)
        | ~ m1_subset_1(X31,u1_struct_0(X29))
        | ~ l1_orders_2(X29) )
      & ( ~ r1_orders_2(X29,X31,esk5_3(X29,X30,X31))
        | ~ r2_lattice3(X29,X30,X31)
        | X31 = k1_yellow_0(X29,X30)
        | ~ r1_yellow_0(X29,X30)
        | ~ m1_subset_1(X31,u1_struct_0(X29))
        | ~ l1_orders_2(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).

fof(c_0_36,plain,(
    ! [X34,X35] :
      ( ~ l1_orders_2(X34)
      | m1_subset_1(k1_yellow_0(X34,X35),u1_struct_0(X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X2)
    | ~ v13_waybel_0(X2,X3)
    | ~ r1_orders_2(X3,X4,X1)
    | ~ l1_orders_2(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ r2_hidden(X4,X2) ),
    inference(csr,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( u1_struct_0(esk8_0) = esk9_0
    | m1_subset_1(esk2_3(u1_struct_0(esk8_0),u1_struct_0(esk8_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( l1_orders_2(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_40,negated_conjecture,
    ( X1 = esk9_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ r2_hidden(esk2_3(u1_struct_0(esk8_0),X1,esk9_0),esk9_0)
    | ~ r2_hidden(esk2_3(u1_struct_0(esk8_0),X1,esk9_0),X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_26])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk8_0))
    | ~ r2_hidden(X1,esk9_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_26])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(k3_yellow_0(esk8_0),esk9_0)
    | ~ v1_subset_1(esk9_0,u1_struct_0(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_43,negated_conjecture,
    ( u1_struct_0(esk8_0) = esk9_0
    | v1_subset_1(esk9_0,u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_26])).

fof(c_0_44,plain,(
    ! [X28] :
      ( ~ l1_orders_2(X28)
      | k3_yellow_0(X28) = k1_yellow_0(X28,k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).

cnf(c_0_45,plain,
    ( r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | X4 != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_47,plain,(
    ! [X36] :
      ( ( r1_yellow_0(X36,k1_xboole_0)
        | v2_struct_0(X36)
        | ~ v5_orders_2(X36)
        | ~ v1_yellow_0(X36)
        | ~ l1_orders_2(X36) )
      & ( r2_yellow_0(X36,u1_struct_0(X36))
        | v2_struct_0(X36)
        | ~ v5_orders_2(X36)
        | ~ v1_yellow_0(X36)
        | ~ l1_orders_2(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_0])])])])).

cnf(c_0_48,negated_conjecture,
    ( u1_struct_0(esk8_0) = esk9_0
    | r2_hidden(esk2_3(u1_struct_0(esk8_0),u1_struct_0(esk8_0),esk9_0),X1)
    | ~ v13_waybel_0(X1,esk8_0)
    | ~ r1_orders_2(esk8_0,X2,esk2_3(u1_struct_0(esk8_0),u1_struct_0(esk8_0),esk9_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])])).

cnf(c_0_49,negated_conjecture,
    ( v13_waybel_0(esk9_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_50,negated_conjecture,
    ( u1_struct_0(esk8_0) = esk9_0
    | ~ r2_hidden(esk2_3(u1_struct_0(esk8_0),u1_struct_0(esk8_0),esk9_0),esk9_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_32]),c_0_41])).

cnf(c_0_51,negated_conjecture,
    ( u1_struct_0(esk8_0) = esk9_0
    | r2_hidden(k3_yellow_0(esk8_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_52,plain,
    ( k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_53,plain,(
    ! [X23,X24,X25,X26] :
      ( ( ~ r2_lattice3(X23,X24,X25)
        | ~ m1_subset_1(X26,u1_struct_0(X23))
        | ~ r2_hidden(X26,X24)
        | r1_orders_2(X23,X26,X25)
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ l1_orders_2(X23) )
      & ( m1_subset_1(esk4_3(X23,X24,X25),u1_struct_0(X23))
        | r2_lattice3(X23,X24,X25)
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ l1_orders_2(X23) )
      & ( r2_hidden(esk4_3(X23,X24,X25),X24)
        | r2_lattice3(X23,X24,X25)
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ l1_orders_2(X23) )
      & ( ~ r1_orders_2(X23,esk4_3(X23,X24,X25),X25)
        | r2_lattice3(X23,X24,X25)
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ l1_orders_2(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

cnf(c_0_54,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_45]),c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( ~ v2_struct_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_56,plain,
    ( r1_yellow_0(X1,k1_xboole_0)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_57,negated_conjecture,
    ( v1_yellow_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_58,negated_conjecture,
    ( v5_orders_2(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_59,negated_conjecture,
    ( u1_struct_0(esk8_0) = esk9_0
    | ~ r1_orders_2(esk8_0,X1,esk2_3(u1_struct_0(esk8_0),u1_struct_0(esk8_0),esk9_0))
    | ~ r2_hidden(X1,esk9_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_26])]),c_0_50])).

cnf(c_0_60,negated_conjecture,
    ( u1_struct_0(esk8_0) = esk9_0
    | r2_hidden(k1_yellow_0(esk8_0,k1_xboole_0),esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_39])])).

fof(c_0_61,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_62,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_63,negated_conjecture,
    ( u1_struct_0(esk8_0) = esk9_0
    | r1_orders_2(esk8_0,k1_yellow_0(esk8_0,X1),esk2_3(u1_struct_0(esk8_0),u1_struct_0(esk8_0),esk9_0))
    | ~ r1_yellow_0(esk8_0,X1)
    | ~ r2_lattice3(esk8_0,X1,esk2_3(u1_struct_0(esk8_0),u1_struct_0(esk8_0),esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_38]),c_0_39])])).

cnf(c_0_64,negated_conjecture,
    ( r1_yellow_0(esk8_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57]),c_0_58]),c_0_39])])).

cnf(c_0_65,negated_conjecture,
    ( u1_struct_0(esk8_0) = esk9_0
    | ~ r1_orders_2(esk8_0,k1_yellow_0(esk8_0,k1_xboole_0),esk2_3(u1_struct_0(esk8_0),u1_struct_0(esk8_0),esk9_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_66,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( u1_struct_0(esk8_0) = esk9_0
    | r2_lattice3(esk8_0,X1,esk2_3(u1_struct_0(esk8_0),u1_struct_0(esk8_0),esk9_0))
    | r2_hidden(esk4_3(esk8_0,X1,esk2_3(u1_struct_0(esk8_0),u1_struct_0(esk8_0),esk9_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_38]),c_0_39])])).

fof(c_0_68,plain,(
    ! [X18,X19] :
      ( ~ m1_subset_1(X18,X19)
      | v1_xboole_0(X19)
      | r2_hidden(X18,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_69,negated_conjecture,
    ( v1_subset_1(esk9_0,u1_struct_0(esk8_0))
    | ~ r2_hidden(k3_yellow_0(esk8_0),esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_70,negated_conjecture,
    ( u1_struct_0(esk8_0) = esk9_0
    | ~ r2_lattice3(esk8_0,k1_xboole_0,esk2_3(u1_struct_0(esk8_0),u1_struct_0(esk8_0),esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( u1_struct_0(esk8_0) = esk9_0
    | r2_lattice3(esk8_0,X1,esk2_3(u1_struct_0(esk8_0),u1_struct_0(esk8_0),esk9_0))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_72,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_73,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( v1_subset_1(esk9_0,u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_yellow_0(esk8_0,k1_xboole_0),esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_52]),c_0_39])])).

cnf(c_0_75,negated_conjecture,
    ( u1_struct_0(esk8_0) = esk9_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72])])).

cnf(c_0_76,plain,
    ( ~ v1_subset_1(X1,X1) ),
    inference(rw,[status(thm)],[c_0_22,c_0_27])).

cnf(c_0_77,plain,
    ( r2_hidden(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | v1_xboole_0(u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_46])).

cnf(c_0_78,negated_conjecture,
    ( ~ v1_xboole_0(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_79,negated_conjecture,
    ( ~ r2_hidden(k1_yellow_0(esk8_0,k1_xboole_0),esk9_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_75]),c_0_76])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(k1_yellow_0(esk8_0,X1),esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_75]),c_0_39])]),c_0_78])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_80])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n001.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 10:55:29 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  # Version: 2.5pre002
% 0.12/0.32  # No SInE strategy applied
% 0.12/0.32  # Trying AutoSched0 for 299 seconds
% 0.12/0.39  # AutoSched0-Mode selected heuristic G_E___008_C18_F1_PI_SE_CS_SP_CO_S4S
% 0.12/0.39  # and selection function SelectNewComplexAHPNS.
% 0.12/0.39  #
% 0.12/0.39  # Preprocessing time       : 0.029 s
% 0.12/0.39  
% 0.12/0.39  # Proof found!
% 0.12/0.39  # SZS status Theorem
% 0.12/0.39  # SZS output start CNFRefutation
% 0.12/0.39  fof(t8_waybel_7, conjecture, ![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_7)).
% 0.12/0.39  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 0.12/0.39  fof(rc3_subset_1, axiom, ![X1]:?[X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))&~(v1_subset_1(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_subset_1)).
% 0.12/0.39  fof(t8_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,X2)<=>r2_hidden(X4,X3)))=>X2=X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_subset_1)).
% 0.12/0.39  fof(d20_waybel_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v13_waybel_0(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r2_hidden(X3,X2)&r1_orders_2(X1,X3,X4))=>r2_hidden(X4,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_waybel_0)).
% 0.12/0.39  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.12/0.39  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.12/0.39  fof(d9_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_yellow_0(X1,X2)=>(X3=k1_yellow_0(X1,X2)<=>(r2_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)=>r1_orders_2(X1,X3,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_yellow_0)).
% 0.12/0.39  fof(dt_k1_yellow_0, axiom, ![X1, X2]:(l1_orders_2(X1)=>m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 0.12/0.39  fof(d11_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_yellow_0)).
% 0.12/0.39  fof(t42_yellow_0, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>(r1_yellow_0(X1,k1_xboole_0)&r2_yellow_0(X1,u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_yellow_0)).
% 0.12/0.39  fof(d9_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 0.12/0.39  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.12/0.39  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.12/0.39  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.12/0.39  fof(c_0_15, negated_conjecture, ~(![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2)))))), inference(assume_negation,[status(cth)],[t8_waybel_7])).
% 0.12/0.39  fof(c_0_16, plain, ![X43, X44]:((~v1_subset_1(X44,X43)|X44!=X43|~m1_subset_1(X44,k1_zfmisc_1(X43)))&(X44=X43|v1_subset_1(X44,X43)|~m1_subset_1(X44,k1_zfmisc_1(X43)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.12/0.39  fof(c_0_17, plain, ![X16]:(m1_subset_1(esk3_1(X16),k1_zfmisc_1(X16))&~v1_subset_1(esk3_1(X16),X16)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[rc3_subset_1])])])).
% 0.12/0.39  fof(c_0_18, plain, ![X12, X13, X14]:((m1_subset_1(esk2_3(X12,X13,X14),X12)|X13=X14|~m1_subset_1(X14,k1_zfmisc_1(X12))|~m1_subset_1(X13,k1_zfmisc_1(X12)))&((~r2_hidden(esk2_3(X12,X13,X14),X13)|~r2_hidden(esk2_3(X12,X13,X14),X14)|X13=X14|~m1_subset_1(X14,k1_zfmisc_1(X12))|~m1_subset_1(X13,k1_zfmisc_1(X12)))&(r2_hidden(esk2_3(X12,X13,X14),X13)|r2_hidden(esk2_3(X12,X13,X14),X14)|X13=X14|~m1_subset_1(X14,k1_zfmisc_1(X12))|~m1_subset_1(X13,k1_zfmisc_1(X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_subset_1])])])])])).
% 0.12/0.39  fof(c_0_19, negated_conjecture, ((((((~v2_struct_0(esk8_0)&v3_orders_2(esk8_0))&v4_orders_2(esk8_0))&v5_orders_2(esk8_0))&v1_yellow_0(esk8_0))&l1_orders_2(esk8_0))&((((~v1_xboole_0(esk9_0)&v2_waybel_0(esk9_0,esk8_0))&v13_waybel_0(esk9_0,esk8_0))&m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(esk8_0))))&((~v1_subset_1(esk9_0,u1_struct_0(esk8_0))|r2_hidden(k3_yellow_0(esk8_0),esk9_0))&(v1_subset_1(esk9_0,u1_struct_0(esk8_0))|~r2_hidden(k3_yellow_0(esk8_0),esk9_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).
% 0.12/0.39  cnf(c_0_20, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.39  cnf(c_0_21, plain, (m1_subset_1(esk3_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.39  cnf(c_0_22, plain, (~v1_subset_1(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.39  fof(c_0_23, plain, ![X37, X38, X39, X40]:((~v13_waybel_0(X38,X37)|(~m1_subset_1(X39,u1_struct_0(X37))|(~m1_subset_1(X40,u1_struct_0(X37))|(~r2_hidden(X39,X38)|~r1_orders_2(X37,X39,X40)|r2_hidden(X40,X38))))|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))|~l1_orders_2(X37))&((m1_subset_1(esk6_2(X37,X38),u1_struct_0(X37))|v13_waybel_0(X38,X37)|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))|~l1_orders_2(X37))&((m1_subset_1(esk7_2(X37,X38),u1_struct_0(X37))|v13_waybel_0(X38,X37)|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))|~l1_orders_2(X37))&(((r2_hidden(esk6_2(X37,X38),X38)|v13_waybel_0(X38,X37)|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))|~l1_orders_2(X37))&(r1_orders_2(X37,esk6_2(X37,X38),esk7_2(X37,X38))|v13_waybel_0(X38,X37)|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))|~l1_orders_2(X37)))&(~r2_hidden(esk7_2(X37,X38),X38)|v13_waybel_0(X38,X37)|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))|~l1_orders_2(X37)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).
% 0.12/0.39  fof(c_0_24, plain, ![X20, X21, X22]:(~r2_hidden(X20,X21)|~m1_subset_1(X21,k1_zfmisc_1(X22))|m1_subset_1(X20,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.12/0.39  cnf(c_0_25, plain, (m1_subset_1(esk2_3(X1,X2,X3),X1)|X2=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.39  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(esk8_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.39  cnf(c_0_27, plain, (esk3_1(X1)=X1), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])).
% 0.12/0.39  fof(c_0_28, plain, ![X9, X10, X11]:(~m1_subset_1(X10,k1_zfmisc_1(X9))|(~r2_hidden(X11,X10)|r2_hidden(X11,X9))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.12/0.39  cnf(c_0_29, plain, (r2_hidden(X4,X1)|~v13_waybel_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~r2_hidden(X3,X1)|~r1_orders_2(X2,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.39  cnf(c_0_30, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.39  cnf(c_0_31, negated_conjecture, (X1=esk9_0|m1_subset_1(esk2_3(u1_struct_0(esk8_0),X1,esk9_0),u1_struct_0(esk8_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0)))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.12/0.39  cnf(c_0_32, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_21, c_0_27])).
% 0.12/0.39  cnf(c_0_33, plain, (X2=X3|~r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.39  cnf(c_0_34, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.39  fof(c_0_35, plain, ![X29, X30, X31, X32]:(((r2_lattice3(X29,X30,X31)|X31!=k1_yellow_0(X29,X30)|~r1_yellow_0(X29,X30)|~m1_subset_1(X31,u1_struct_0(X29))|~l1_orders_2(X29))&(~m1_subset_1(X32,u1_struct_0(X29))|(~r2_lattice3(X29,X30,X32)|r1_orders_2(X29,X31,X32))|X31!=k1_yellow_0(X29,X30)|~r1_yellow_0(X29,X30)|~m1_subset_1(X31,u1_struct_0(X29))|~l1_orders_2(X29)))&((m1_subset_1(esk5_3(X29,X30,X31),u1_struct_0(X29))|~r2_lattice3(X29,X30,X31)|X31=k1_yellow_0(X29,X30)|~r1_yellow_0(X29,X30)|~m1_subset_1(X31,u1_struct_0(X29))|~l1_orders_2(X29))&((r2_lattice3(X29,X30,esk5_3(X29,X30,X31))|~r2_lattice3(X29,X30,X31)|X31=k1_yellow_0(X29,X30)|~r1_yellow_0(X29,X30)|~m1_subset_1(X31,u1_struct_0(X29))|~l1_orders_2(X29))&(~r1_orders_2(X29,X31,esk5_3(X29,X30,X31))|~r2_lattice3(X29,X30,X31)|X31=k1_yellow_0(X29,X30)|~r1_yellow_0(X29,X30)|~m1_subset_1(X31,u1_struct_0(X29))|~l1_orders_2(X29))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).
% 0.12/0.39  fof(c_0_36, plain, ![X34, X35]:(~l1_orders_2(X34)|m1_subset_1(k1_yellow_0(X34,X35),u1_struct_0(X34))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).
% 0.12/0.39  cnf(c_0_37, plain, (r2_hidden(X1,X2)|~v13_waybel_0(X2,X3)|~r1_orders_2(X3,X4,X1)|~l1_orders_2(X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X1,u1_struct_0(X3))|~r2_hidden(X4,X2)), inference(csr,[status(thm)],[c_0_29, c_0_30])).
% 0.12/0.39  cnf(c_0_38, negated_conjecture, (u1_struct_0(esk8_0)=esk9_0|m1_subset_1(esk2_3(u1_struct_0(esk8_0),u1_struct_0(esk8_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.12/0.39  cnf(c_0_39, negated_conjecture, (l1_orders_2(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.39  cnf(c_0_40, negated_conjecture, (X1=esk9_0|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0)))|~r2_hidden(esk2_3(u1_struct_0(esk8_0),X1,esk9_0),esk9_0)|~r2_hidden(esk2_3(u1_struct_0(esk8_0),X1,esk9_0),X1)), inference(spm,[status(thm)],[c_0_33, c_0_26])).
% 0.12/0.39  cnf(c_0_41, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk8_0))|~r2_hidden(X1,esk9_0)), inference(spm,[status(thm)],[c_0_34, c_0_26])).
% 0.12/0.39  cnf(c_0_42, negated_conjecture, (r2_hidden(k3_yellow_0(esk8_0),esk9_0)|~v1_subset_1(esk9_0,u1_struct_0(esk8_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.39  cnf(c_0_43, negated_conjecture, (u1_struct_0(esk8_0)=esk9_0|v1_subset_1(esk9_0,u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_20, c_0_26])).
% 0.12/0.39  fof(c_0_44, plain, ![X28]:(~l1_orders_2(X28)|k3_yellow_0(X28)=k1_yellow_0(X28,k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).
% 0.12/0.39  cnf(c_0_45, plain, (r1_orders_2(X2,X4,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|X4!=k1_yellow_0(X2,X3)|~r1_yellow_0(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.12/0.39  cnf(c_0_46, plain, (m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.12/0.39  fof(c_0_47, plain, ![X36]:((r1_yellow_0(X36,k1_xboole_0)|(v2_struct_0(X36)|~v5_orders_2(X36)|~v1_yellow_0(X36)|~l1_orders_2(X36)))&(r2_yellow_0(X36,u1_struct_0(X36))|(v2_struct_0(X36)|~v5_orders_2(X36)|~v1_yellow_0(X36)|~l1_orders_2(X36)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_0])])])])).
% 0.12/0.39  cnf(c_0_48, negated_conjecture, (u1_struct_0(esk8_0)=esk9_0|r2_hidden(esk2_3(u1_struct_0(esk8_0),u1_struct_0(esk8_0),esk9_0),X1)|~v13_waybel_0(X1,esk8_0)|~r1_orders_2(esk8_0,X2,esk2_3(u1_struct_0(esk8_0),u1_struct_0(esk8_0),esk9_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0)))|~r2_hidden(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])])).
% 0.12/0.39  cnf(c_0_49, negated_conjecture, (v13_waybel_0(esk9_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.39  cnf(c_0_50, negated_conjecture, (u1_struct_0(esk8_0)=esk9_0|~r2_hidden(esk2_3(u1_struct_0(esk8_0),u1_struct_0(esk8_0),esk9_0),esk9_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_32]), c_0_41])).
% 0.12/0.39  cnf(c_0_51, negated_conjecture, (u1_struct_0(esk8_0)=esk9_0|r2_hidden(k3_yellow_0(esk8_0),esk9_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.12/0.39  cnf(c_0_52, plain, (k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.12/0.39  fof(c_0_53, plain, ![X23, X24, X25, X26]:((~r2_lattice3(X23,X24,X25)|(~m1_subset_1(X26,u1_struct_0(X23))|(~r2_hidden(X26,X24)|r1_orders_2(X23,X26,X25)))|~m1_subset_1(X25,u1_struct_0(X23))|~l1_orders_2(X23))&((m1_subset_1(esk4_3(X23,X24,X25),u1_struct_0(X23))|r2_lattice3(X23,X24,X25)|~m1_subset_1(X25,u1_struct_0(X23))|~l1_orders_2(X23))&((r2_hidden(esk4_3(X23,X24,X25),X24)|r2_lattice3(X23,X24,X25)|~m1_subset_1(X25,u1_struct_0(X23))|~l1_orders_2(X23))&(~r1_orders_2(X23,esk4_3(X23,X24,X25),X25)|r2_lattice3(X23,X24,X25)|~m1_subset_1(X25,u1_struct_0(X23))|~l1_orders_2(X23))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).
% 0.12/0.39  cnf(c_0_54, plain, (r1_orders_2(X1,k1_yellow_0(X1,X2),X3)|~r1_yellow_0(X1,X2)|~r2_lattice3(X1,X2,X3)|~l1_orders_2(X1)|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_45]), c_0_46])).
% 0.12/0.39  cnf(c_0_55, negated_conjecture, (~v2_struct_0(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.39  cnf(c_0_56, plain, (r1_yellow_0(X1,k1_xboole_0)|v2_struct_0(X1)|~v5_orders_2(X1)|~v1_yellow_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.12/0.39  cnf(c_0_57, negated_conjecture, (v1_yellow_0(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.39  cnf(c_0_58, negated_conjecture, (v5_orders_2(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.39  cnf(c_0_59, negated_conjecture, (u1_struct_0(esk8_0)=esk9_0|~r1_orders_2(esk8_0,X1,esk2_3(u1_struct_0(esk8_0),u1_struct_0(esk8_0),esk9_0))|~r2_hidden(X1,esk9_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_26])]), c_0_50])).
% 0.12/0.39  cnf(c_0_60, negated_conjecture, (u1_struct_0(esk8_0)=esk9_0|r2_hidden(k1_yellow_0(esk8_0,k1_xboole_0),esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_39])])).
% 0.12/0.39  fof(c_0_61, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.12/0.39  cnf(c_0_62, plain, (r2_hidden(esk4_3(X1,X2,X3),X2)|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.12/0.39  cnf(c_0_63, negated_conjecture, (u1_struct_0(esk8_0)=esk9_0|r1_orders_2(esk8_0,k1_yellow_0(esk8_0,X1),esk2_3(u1_struct_0(esk8_0),u1_struct_0(esk8_0),esk9_0))|~r1_yellow_0(esk8_0,X1)|~r2_lattice3(esk8_0,X1,esk2_3(u1_struct_0(esk8_0),u1_struct_0(esk8_0),esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_38]), c_0_39])])).
% 0.12/0.39  cnf(c_0_64, negated_conjecture, (r1_yellow_0(esk8_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57]), c_0_58]), c_0_39])])).
% 0.12/0.39  cnf(c_0_65, negated_conjecture, (u1_struct_0(esk8_0)=esk9_0|~r1_orders_2(esk8_0,k1_yellow_0(esk8_0,k1_xboole_0),esk2_3(u1_struct_0(esk8_0),u1_struct_0(esk8_0),esk9_0))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.12/0.39  cnf(c_0_66, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.12/0.39  cnf(c_0_67, negated_conjecture, (u1_struct_0(esk8_0)=esk9_0|r2_lattice3(esk8_0,X1,esk2_3(u1_struct_0(esk8_0),u1_struct_0(esk8_0),esk9_0))|r2_hidden(esk4_3(esk8_0,X1,esk2_3(u1_struct_0(esk8_0),u1_struct_0(esk8_0),esk9_0)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_38]), c_0_39])])).
% 0.12/0.39  fof(c_0_68, plain, ![X18, X19]:(~m1_subset_1(X18,X19)|(v1_xboole_0(X19)|r2_hidden(X18,X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.12/0.39  cnf(c_0_69, negated_conjecture, (v1_subset_1(esk9_0,u1_struct_0(esk8_0))|~r2_hidden(k3_yellow_0(esk8_0),esk9_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.39  cnf(c_0_70, negated_conjecture, (u1_struct_0(esk8_0)=esk9_0|~r2_lattice3(esk8_0,k1_xboole_0,esk2_3(u1_struct_0(esk8_0),u1_struct_0(esk8_0),esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65])).
% 0.12/0.39  cnf(c_0_71, negated_conjecture, (u1_struct_0(esk8_0)=esk9_0|r2_lattice3(esk8_0,X1,esk2_3(u1_struct_0(esk8_0),u1_struct_0(esk8_0),esk9_0))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.12/0.39  cnf(c_0_72, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.12/0.39  cnf(c_0_73, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.12/0.39  cnf(c_0_74, negated_conjecture, (v1_subset_1(esk9_0,u1_struct_0(esk8_0))|~r2_hidden(k1_yellow_0(esk8_0,k1_xboole_0),esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_52]), c_0_39])])).
% 0.12/0.39  cnf(c_0_75, negated_conjecture, (u1_struct_0(esk8_0)=esk9_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72])])).
% 0.12/0.39  cnf(c_0_76, plain, (~v1_subset_1(X1,X1)), inference(rw,[status(thm)],[c_0_22, c_0_27])).
% 0.12/0.39  cnf(c_0_77, plain, (r2_hidden(k1_yellow_0(X1,X2),u1_struct_0(X1))|v1_xboole_0(u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_73, c_0_46])).
% 0.12/0.39  cnf(c_0_78, negated_conjecture, (~v1_xboole_0(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.39  cnf(c_0_79, negated_conjecture, (~r2_hidden(k1_yellow_0(esk8_0,k1_xboole_0),esk9_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_75]), c_0_76])).
% 0.12/0.39  cnf(c_0_80, negated_conjecture, (r2_hidden(k1_yellow_0(esk8_0,X1),esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_75]), c_0_39])]), c_0_78])).
% 0.12/0.39  cnf(c_0_81, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_80])]), ['proof']).
% 0.12/0.39  # SZS output end CNFRefutation
% 0.12/0.39  # Proof object total steps             : 82
% 0.12/0.39  # Proof object clause steps            : 52
% 0.12/0.39  # Proof object formula steps           : 30
% 0.12/0.39  # Proof object conjectures             : 33
% 0.12/0.39  # Proof object clause conjectures      : 30
% 0.12/0.39  # Proof object formula conjectures     : 3
% 0.12/0.39  # Proof object initial clauses used    : 25
% 0.12/0.39  # Proof object initial formulas used   : 15
% 0.12/0.39  # Proof object generating inferences   : 21
% 0.12/0.39  # Proof object simplifying inferences  : 34
% 0.12/0.39  # Training examples: 0 positive, 0 negative
% 0.12/0.39  # Parsed axioms                        : 15
% 0.12/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.39  # Initial clauses                      : 44
% 0.12/0.39  # Removed in clause preprocessing      : 0
% 0.12/0.39  # Initial clauses in saturation        : 44
% 0.12/0.39  # Processed clauses                    : 360
% 0.12/0.39  # ...of these trivial                  : 1
% 0.12/0.39  # ...subsumed                          : 111
% 0.12/0.39  # ...remaining for further processing  : 248
% 0.12/0.39  # Other redundant clauses eliminated   : 3
% 0.12/0.39  # Clauses deleted for lack of memory   : 0
% 0.12/0.39  # Backward-subsumed                    : 16
% 0.12/0.39  # Backward-rewritten                   : 142
% 0.12/0.39  # Generated clauses                    : 721
% 0.12/0.39  # ...of the previous two non-trivial   : 734
% 0.12/0.39  # Contextual simplify-reflections      : 17
% 0.12/0.39  # Paramodulations                      : 718
% 0.12/0.39  # Factorizations                       : 0
% 0.12/0.39  # Equation resolutions                 : 3
% 0.12/0.39  # Propositional unsat checks           : 0
% 0.12/0.39  #    Propositional check models        : 0
% 0.12/0.39  #    Propositional check unsatisfiable : 0
% 0.12/0.39  #    Propositional clauses             : 0
% 0.12/0.39  #    Propositional clauses after purity: 0
% 0.12/0.39  #    Propositional unsat core size     : 0
% 0.12/0.39  #    Propositional preprocessing time  : 0.000
% 0.12/0.39  #    Propositional encoding time       : 0.000
% 0.12/0.39  #    Propositional solver time         : 0.000
% 0.12/0.39  #    Success case prop preproc time    : 0.000
% 0.12/0.39  #    Success case prop encoding time   : 0.000
% 0.12/0.39  #    Success case prop solver time     : 0.000
% 0.12/0.39  # Current number of processed clauses  : 87
% 0.12/0.39  #    Positive orientable unit clauses  : 19
% 0.12/0.39  #    Positive unorientable unit clauses: 0
% 0.12/0.39  #    Negative unit clauses             : 4
% 0.12/0.39  #    Non-unit-clauses                  : 64
% 0.12/0.39  # Current number of unprocessed clauses: 405
% 0.12/0.39  # ...number of literals in the above   : 1910
% 0.12/0.39  # Current number of archived formulas  : 0
% 0.12/0.39  # Current number of archived clauses   : 158
% 0.12/0.39  # Clause-clause subsumption calls (NU) : 5805
% 0.12/0.39  # Rec. Clause-clause subsumption calls : 1949
% 0.12/0.39  # Non-unit clause-clause subsumptions  : 121
% 0.12/0.39  # Unit Clause-clause subsumption calls : 249
% 0.12/0.39  # Rewrite failures with RHS unbound    : 0
% 0.12/0.39  # BW rewrite match attempts            : 19
% 0.12/0.39  # BW rewrite match successes           : 7
% 0.12/0.39  # Condensation attempts                : 361
% 0.12/0.39  # Condensation successes               : 0
% 0.12/0.39  # Termbank termtop insertions          : 22354
% 0.12/0.39  
% 0.12/0.39  # -------------------------------------------------
% 0.12/0.39  # User time                : 0.069 s
% 0.12/0.39  # System time              : 0.001 s
% 0.12/0.39  # Total time               : 0.070 s
% 0.12/0.39  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
