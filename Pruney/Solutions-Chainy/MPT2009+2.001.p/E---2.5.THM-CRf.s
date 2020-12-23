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
% DateTime   : Thu Dec  3 11:21:32 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 408 expanded)
%              Number of clauses        :   57 ( 146 expanded)
%              Number of leaves         :   13 ( 104 expanded)
%              Depth                    :   17
%              Number of atoms          :  397 (2097 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   35 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t29_yellow_6,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & l1_waybel_0(X2,X1) )
         => r1_waybel_0(X1,X2,u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_yellow_6)).

fof(rc5_waybel_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ? [X2] :
          ( l1_waybel_0(X2,X1)
          & ~ v2_struct_0(X2)
          & v3_orders_2(X2)
          & v4_orders_2(X2)
          & v5_orders_2(X2)
          & v6_waybel_0(X2,X1)
          & v7_waybel_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc5_waybel_0)).

fof(t8_waybel_9,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => r1_waybel_0(X1,X2,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_9)).

fof(t28_yellow_6,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( r1_waybel_0(X1,X2,X3)
             => r2_waybel_0(X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_yellow_6)).

fof(dt_o_2_4_waybel_9,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X2)
        & l1_waybel_0(X2,X1) )
     => m1_subset_1(o_2_4_waybel_9(X1,X2),u1_struct_0(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_2_4_waybel_9)).

fof(d12_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( r2_waybel_0(X1,X2,X3)
            <=> ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X2))
                 => ? [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                      & r1_orders_2(X2,X4,X5)
                      & r2_hidden(k2_waybel_0(X1,X2,X5),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_waybel_0)).

fof(d11_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( r1_waybel_0(X1,X2,X3)
            <=> ? [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X2))
                  & ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                     => ( r1_orders_2(X2,X4,X5)
                       => r2_hidden(k2_waybel_0(X1,X2,X5),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_waybel_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(dt_l1_waybel_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => l1_orders_2(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(t189_funct_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( m1_subset_1(X3,X1)
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,X1,X2)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
                 => r2_hidden(k3_funct_2(X1,X2,X4,X3),k2_relset_1(X1,X2,X4)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_funct_2)).

fof(dt_u1_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( l1_struct_0(X1)
        & l1_waybel_0(X2,X1) )
     => ( v1_funct_1(u1_waybel_0(X1,X2))
        & v1_funct_2(u1_waybel_0(X1,X2),u1_struct_0(X2),u1_struct_0(X1))
        & m1_subset_1(u1_waybel_0(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_waybel_0)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d8_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => k2_waybel_0(X1,X2,X3) = k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_waybel_0)).

fof(c_0_13,plain,(
    ! [X43,X44] :
      ( v2_struct_0(X43)
      | ~ l1_struct_0(X43)
      | v2_struct_0(X44)
      | ~ v4_orders_2(X44)
      | ~ v7_waybel_0(X44)
      | ~ l1_waybel_0(X44,X43)
      | r1_waybel_0(X43,X44,u1_struct_0(X43)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t29_yellow_6])])])])).

fof(c_0_14,plain,(
    ! [X38] :
      ( ( l1_waybel_0(esk6_1(X38),X38)
        | ~ l1_struct_0(X38) )
      & ( ~ v2_struct_0(esk6_1(X38))
        | ~ l1_struct_0(X38) )
      & ( v3_orders_2(esk6_1(X38))
        | ~ l1_struct_0(X38) )
      & ( v4_orders_2(esk6_1(X38))
        | ~ l1_struct_0(X38) )
      & ( v5_orders_2(esk6_1(X38))
        | ~ l1_struct_0(X38) )
      & ( v6_waybel_0(esk6_1(X38),X38)
        | ~ l1_struct_0(X38) )
      & ( v7_waybel_0(esk6_1(X38))
        | ~ l1_struct_0(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc5_waybel_0])])])])])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_struct_0(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & l1_waybel_0(X2,X1) )
           => r1_waybel_0(X1,X2,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t8_waybel_9])).

cnf(c_0_16,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r1_waybel_0(X1,X2,u1_struct_0(X1))
    | ~ l1_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( l1_waybel_0(esk6_1(X1),X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( v4_orders_2(esk6_1(X1))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( v7_waybel_0(esk6_1(X1))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( ~ v2_struct_0(esk6_1(X1))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk7_0)
    & l1_struct_0(esk7_0)
    & ~ v2_struct_0(esk8_0)
    & l1_waybel_0(esk8_0,esk7_0)
    & ~ r1_waybel_0(esk7_0,esk8_0,k2_relset_1(u1_struct_0(esk8_0),u1_struct_0(esk7_0),u1_waybel_0(esk7_0,esk8_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

fof(c_0_22,plain,(
    ! [X40,X41,X42] :
      ( v2_struct_0(X40)
      | ~ l1_struct_0(X40)
      | v2_struct_0(X41)
      | ~ v4_orders_2(X41)
      | ~ v7_waybel_0(X41)
      | ~ l1_waybel_0(X41,X40)
      | ~ r1_waybel_0(X40,X41,X42)
      | r2_waybel_0(X40,X41,X42) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t28_yellow_6])])])])).

cnf(c_0_23,plain,
    ( r1_waybel_0(X1,esk6_1(X1),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( l1_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_26,plain,(
    ! [X45,X46] :
      ( v2_struct_0(X45)
      | ~ l1_struct_0(X45)
      | v2_struct_0(X46)
      | ~ l1_waybel_0(X46,X45)
      | m1_subset_1(o_2_4_waybel_9(X45,X46),u1_struct_0(X46)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_o_2_4_waybel_9])])])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r2_waybel_0(X1,X2,X3)
    | ~ l1_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ r1_waybel_0(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( r1_waybel_0(esk7_0,esk6_1(esk7_0),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_29,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(o_2_4_waybel_9(X1,X2),u1_struct_0(X2))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( r2_waybel_0(esk7_0,esk6_1(esk7_0),u1_struct_0(esk7_0))
    | v2_struct_0(esk6_1(esk7_0))
    | ~ v7_waybel_0(esk6_1(esk7_0))
    | ~ v4_orders_2(esk6_1(esk7_0))
    | ~ l1_waybel_0(esk6_1(esk7_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_24])]),c_0_25])).

fof(c_0_31,plain,(
    ! [X23,X24,X25,X26,X28,X30] :
      ( ( m1_subset_1(esk4_4(X23,X24,X25,X26),u1_struct_0(X24))
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | ~ r2_waybel_0(X23,X24,X25)
        | v2_struct_0(X24)
        | ~ l1_waybel_0(X24,X23)
        | v2_struct_0(X23)
        | ~ l1_struct_0(X23) )
      & ( r1_orders_2(X24,X26,esk4_4(X23,X24,X25,X26))
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | ~ r2_waybel_0(X23,X24,X25)
        | v2_struct_0(X24)
        | ~ l1_waybel_0(X24,X23)
        | v2_struct_0(X23)
        | ~ l1_struct_0(X23) )
      & ( r2_hidden(k2_waybel_0(X23,X24,esk4_4(X23,X24,X25,X26)),X25)
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | ~ r2_waybel_0(X23,X24,X25)
        | v2_struct_0(X24)
        | ~ l1_waybel_0(X24,X23)
        | v2_struct_0(X23)
        | ~ l1_struct_0(X23) )
      & ( m1_subset_1(esk5_3(X23,X24,X28),u1_struct_0(X24))
        | r2_waybel_0(X23,X24,X28)
        | v2_struct_0(X24)
        | ~ l1_waybel_0(X24,X23)
        | v2_struct_0(X23)
        | ~ l1_struct_0(X23) )
      & ( ~ m1_subset_1(X30,u1_struct_0(X24))
        | ~ r1_orders_2(X24,esk5_3(X23,X24,X28),X30)
        | ~ r2_hidden(k2_waybel_0(X23,X24,X30),X28)
        | r2_waybel_0(X23,X24,X28)
        | v2_struct_0(X24)
        | ~ l1_waybel_0(X24,X23)
        | v2_struct_0(X23)
        | ~ l1_struct_0(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_waybel_0])])])])])])])).

cnf(c_0_32,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(o_2_4_waybel_9(X1,esk6_1(X1)),u1_struct_0(esk6_1(X1)))
    | ~ l1_struct_0(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_17]),c_0_20])).

cnf(c_0_33,negated_conjecture,
    ( r2_waybel_0(esk7_0,esk6_1(esk7_0),u1_struct_0(esk7_0))
    | v2_struct_0(esk6_1(esk7_0))
    | ~ v4_orders_2(esk6_1(esk7_0))
    | ~ l1_waybel_0(esk6_1(esk7_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_19]),c_0_24])])).

cnf(c_0_34,plain,
    ( r2_hidden(k2_waybel_0(X1,X2,esk4_4(X1,X2,X3,X4)),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_waybel_0(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(o_2_4_waybel_9(esk7_0,esk6_1(esk7_0)),u1_struct_0(esk6_1(esk7_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_24]),c_0_25])).

cnf(c_0_36,negated_conjecture,
    ( r2_waybel_0(esk7_0,esk6_1(esk7_0),u1_struct_0(esk7_0))
    | v2_struct_0(esk6_1(esk7_0))
    | ~ l1_waybel_0(esk6_1(esk7_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_18]),c_0_24])])).

fof(c_0_37,plain,(
    ! [X15,X16,X17,X19,X20,X21] :
      ( ( m1_subset_1(esk2_3(X15,X16,X17),u1_struct_0(X16))
        | ~ r1_waybel_0(X15,X16,X17)
        | v2_struct_0(X16)
        | ~ l1_waybel_0(X16,X15)
        | v2_struct_0(X15)
        | ~ l1_struct_0(X15) )
      & ( ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ r1_orders_2(X16,esk2_3(X15,X16,X17),X19)
        | r2_hidden(k2_waybel_0(X15,X16,X19),X17)
        | ~ r1_waybel_0(X15,X16,X17)
        | v2_struct_0(X16)
        | ~ l1_waybel_0(X16,X15)
        | v2_struct_0(X15)
        | ~ l1_struct_0(X15) )
      & ( m1_subset_1(esk3_4(X15,X16,X20,X21),u1_struct_0(X16))
        | ~ m1_subset_1(X21,u1_struct_0(X16))
        | r1_waybel_0(X15,X16,X20)
        | v2_struct_0(X16)
        | ~ l1_waybel_0(X16,X15)
        | v2_struct_0(X15)
        | ~ l1_struct_0(X15) )
      & ( r1_orders_2(X16,X21,esk3_4(X15,X16,X20,X21))
        | ~ m1_subset_1(X21,u1_struct_0(X16))
        | r1_waybel_0(X15,X16,X20)
        | v2_struct_0(X16)
        | ~ l1_waybel_0(X16,X15)
        | v2_struct_0(X15)
        | ~ l1_struct_0(X15) )
      & ( ~ r2_hidden(k2_waybel_0(X15,X16,esk3_4(X15,X16,X20,X21)),X20)
        | ~ m1_subset_1(X21,u1_struct_0(X16))
        | r1_waybel_0(X15,X16,X20)
        | v2_struct_0(X16)
        | ~ l1_waybel_0(X16,X15)
        | v2_struct_0(X15)
        | ~ l1_struct_0(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_waybel_0])])])])])])])).

cnf(c_0_38,negated_conjecture,
    ( l1_waybel_0(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_39,negated_conjecture,
    ( ~ v2_struct_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_40,negated_conjecture,
    ( v2_struct_0(esk6_1(esk7_0))
    | v2_struct_0(X1)
    | r2_hidden(k2_waybel_0(X1,esk6_1(esk7_0),esk4_4(X1,esk6_1(esk7_0),X2,o_2_4_waybel_9(esk7_0,esk6_1(esk7_0)))),X2)
    | ~ r2_waybel_0(X1,esk6_1(esk7_0),X2)
    | ~ l1_waybel_0(esk6_1(esk7_0),X1)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( r2_waybel_0(esk7_0,esk6_1(esk7_0),u1_struct_0(esk7_0))
    | v2_struct_0(esk6_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_17]),c_0_24])])).

fof(c_0_42,plain,(
    ! [X14] :
      ( ~ l1_orders_2(X14)
      | l1_struct_0(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_43,plain,(
    ! [X34,X35] :
      ( ~ l1_struct_0(X34)
      | ~ l1_waybel_0(X35,X34)
      | l1_orders_2(X35) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).

fof(c_0_44,plain,(
    ! [X10,X11,X12,X13] :
      ( v1_xboole_0(X10)
      | v1_xboole_0(X11)
      | ~ m1_subset_1(X12,X10)
      | ~ v1_funct_1(X13)
      | ~ v1_funct_2(X13,X10,X11)
      | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | r2_hidden(k3_funct_2(X10,X11,X13,X12),k2_relset_1(X10,X11,X13)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t189_funct_2])])])])).

fof(c_0_45,plain,(
    ! [X36,X37] :
      ( ( v1_funct_1(u1_waybel_0(X36,X37))
        | ~ l1_struct_0(X36)
        | ~ l1_waybel_0(X37,X36) )
      & ( v1_funct_2(u1_waybel_0(X36,X37),u1_struct_0(X37),u1_struct_0(X36))
        | ~ l1_struct_0(X36)
        | ~ l1_waybel_0(X37,X36) )
      & ( m1_subset_1(u1_waybel_0(X36,X37),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X36))))
        | ~ l1_struct_0(X36)
        | ~ l1_waybel_0(X37,X36) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_waybel_0])])])).

cnf(c_0_46,plain,
    ( m1_subset_1(esk3_4(X1,X2,X3,X4),u1_struct_0(X2))
    | r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(o_2_4_waybel_9(esk7_0,esk8_0),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_38]),c_0_24])]),c_0_39]),c_0_25])).

fof(c_0_48,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_49,negated_conjecture,
    ( v2_struct_0(esk6_1(esk7_0))
    | r2_hidden(k2_waybel_0(esk7_0,esk6_1(esk7_0),esk4_4(esk7_0,esk6_1(esk7_0),u1_struct_0(esk7_0),o_2_4_waybel_9(esk7_0,esk6_1(esk7_0)))),u1_struct_0(esk7_0))
    | ~ l1_waybel_0(esk6_1(esk7_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_24])]),c_0_25])).

cnf(c_0_50,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_51,plain,
    ( l1_orders_2(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | r2_hidden(k3_funct_2(X1,X2,X4,X3),k2_relset_1(X1,X2,X4))
    | ~ m1_subset_1(X3,X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_53,plain,
    ( m1_subset_1(u1_waybel_0(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,plain,
    ( v1_funct_1(u1_waybel_0(X1,X2))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_55,plain,
    ( v1_funct_2(u1_waybel_0(X1,X2),u1_struct_0(X2),u1_struct_0(X1))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,negated_conjecture,
    ( r1_waybel_0(X1,esk8_0,X2)
    | v2_struct_0(X1)
    | m1_subset_1(esk3_4(X1,esk8_0,X2,o_2_4_waybel_9(esk7_0,esk8_0)),u1_struct_0(esk8_0))
    | ~ l1_waybel_0(esk8_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_39])).

cnf(c_0_57,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_58,negated_conjecture,
    ( v2_struct_0(esk6_1(esk7_0))
    | r2_hidden(k2_waybel_0(esk7_0,esk6_1(esk7_0),esk4_4(esk7_0,esk6_1(esk7_0),u1_struct_0(esk7_0),o_2_4_waybel_9(esk7_0,esk6_1(esk7_0)))),u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_17]),c_0_24])])).

fof(c_0_59,plain,(
    ! [X31,X32,X33] :
      ( v2_struct_0(X31)
      | ~ l1_struct_0(X31)
      | v2_struct_0(X32)
      | ~ l1_waybel_0(X32,X31)
      | ~ m1_subset_1(X33,u1_struct_0(X32))
      | k2_waybel_0(X31,X32,X33) = k3_funct_2(u1_struct_0(X32),u1_struct_0(X31),u1_waybel_0(X31,X32),X33) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_waybel_0])])])])).

cnf(c_0_60,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(o_2_4_waybel_9(X1,esk6_1(X1)),u1_struct_0(esk6_1(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_50])).

cnf(c_0_61,negated_conjecture,
    ( l1_orders_2(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_38]),c_0_24])])).

cnf(c_0_62,plain,
    ( r1_waybel_0(X1,esk6_1(X1),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_50])).

cnf(c_0_63,plain,
    ( r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),X3),k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1)))
    | v1_xboole_0(u1_struct_0(X1))
    | v1_xboole_0(u1_struct_0(X2))
    | ~ l1_waybel_0(X1,X2)
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_55])).

cnf(c_0_64,negated_conjecture,
    ( r1_waybel_0(esk7_0,esk8_0,X1)
    | m1_subset_1(esk3_4(esk7_0,esk8_0,X1,o_2_4_waybel_9(esk7_0,esk8_0)),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_38]),c_0_24])]),c_0_25])).

cnf(c_0_65,negated_conjecture,
    ( v2_struct_0(esk6_1(esk7_0))
    | ~ v1_xboole_0(u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_66,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k2_waybel_0(X1,X2,X3) = k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),X3)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(o_2_4_waybel_9(esk8_0,esk6_1(esk8_0)),u1_struct_0(esk6_1(esk8_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_39])).

cnf(c_0_68,negated_conjecture,
    ( r1_waybel_0(esk8_0,esk6_1(esk8_0),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_61]),c_0_39])).

cnf(c_0_69,negated_conjecture,
    ( r1_waybel_0(esk7_0,esk8_0,X1)
    | r2_hidden(k3_funct_2(u1_struct_0(esk8_0),u1_struct_0(X2),u1_waybel_0(X2,esk8_0),esk3_4(esk7_0,esk8_0,X1,o_2_4_waybel_9(esk7_0,esk8_0))),k2_relset_1(u1_struct_0(esk8_0),u1_struct_0(X2),u1_waybel_0(X2,esk8_0)))
    | v1_xboole_0(u1_struct_0(esk8_0))
    | v1_xboole_0(u1_struct_0(X2))
    | ~ l1_waybel_0(esk8_0,X2)
    | ~ l1_struct_0(X2) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_65]),c_0_24])])).

cnf(c_0_71,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk8_0),u1_struct_0(X1),u1_waybel_0(X1,esk8_0),esk3_4(esk7_0,esk8_0,X2,o_2_4_waybel_9(esk7_0,esk8_0))) = k2_waybel_0(X1,esk8_0,esk3_4(esk7_0,esk8_0,X2,o_2_4_waybel_9(esk7_0,esk8_0)))
    | r1_waybel_0(esk7_0,esk8_0,X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(esk8_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_64]),c_0_39])).

cnf(c_0_72,negated_conjecture,
    ( v2_struct_0(esk6_1(esk8_0))
    | v2_struct_0(X1)
    | r2_hidden(k2_waybel_0(X1,esk6_1(esk8_0),esk4_4(X1,esk6_1(esk8_0),X2,o_2_4_waybel_9(esk8_0,esk6_1(esk8_0)))),X2)
    | ~ r2_waybel_0(X1,esk6_1(esk8_0),X2)
    | ~ l1_waybel_0(esk6_1(esk8_0),X1)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_67])).

cnf(c_0_73,negated_conjecture,
    ( r2_waybel_0(esk8_0,esk6_1(esk8_0),u1_struct_0(esk8_0))
    | ~ l1_struct_0(esk8_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_68]),c_0_39]),c_0_17]),c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_74,negated_conjecture,
    ( r1_waybel_0(esk7_0,esk8_0,X1)
    | r2_hidden(k3_funct_2(u1_struct_0(esk8_0),u1_struct_0(esk7_0),u1_waybel_0(esk7_0,esk8_0),esk3_4(esk7_0,esk8_0,X1,o_2_4_waybel_9(esk7_0,esk8_0))),k2_relset_1(u1_struct_0(esk8_0),u1_struct_0(esk7_0),u1_waybel_0(esk7_0,esk8_0)))
    | v1_xboole_0(u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_38]),c_0_24])]),c_0_70])).

cnf(c_0_75,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk8_0),u1_struct_0(esk7_0),u1_waybel_0(esk7_0,esk8_0),esk3_4(esk7_0,esk8_0,X1,o_2_4_waybel_9(esk7_0,esk8_0))) = k2_waybel_0(esk7_0,esk8_0,esk3_4(esk7_0,esk8_0,X1,o_2_4_waybel_9(esk7_0,esk8_0)))
    | r1_waybel_0(esk7_0,esk8_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_38]),c_0_24])]),c_0_25])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk8_0,esk6_1(esk8_0),esk4_4(esk8_0,esk6_1(esk8_0),u1_struct_0(esk8_0),o_2_4_waybel_9(esk8_0,esk6_1(esk8_0)))),u1_struct_0(esk8_0))
    | ~ l1_struct_0(esk8_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_39]),c_0_17]),c_0_20])).

cnf(c_0_77,plain,
    ( r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(k2_waybel_0(X1,X2,esk3_4(X1,X2,X3,X4)),X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_78,negated_conjecture,
    ( r1_waybel_0(esk7_0,esk8_0,X1)
    | r2_hidden(k2_waybel_0(esk7_0,esk8_0,esk3_4(esk7_0,esk8_0,X1,o_2_4_waybel_9(esk7_0,esk8_0))),k2_relset_1(u1_struct_0(esk8_0),u1_struct_0(esk7_0),u1_waybel_0(esk7_0,esk8_0)))
    | v1_xboole_0(u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_79,negated_conjecture,
    ( ~ r1_waybel_0(esk7_0,esk8_0,k2_relset_1(u1_struct_0(esk8_0),u1_struct_0(esk7_0),u1_waybel_0(esk7_0,esk8_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_80,negated_conjecture,
    ( ~ l1_struct_0(esk8_0)
    | ~ v1_xboole_0(u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_76])).

cnf(c_0_81,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_38]),c_0_24]),c_0_47])]),c_0_79]),c_0_39]),c_0_25])).

cnf(c_0_82,negated_conjecture,
    ( ~ l1_struct_0(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_81])])).

cnf(c_0_83,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_50]),c_0_61])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:40:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.43  # AutoSched0-Mode selected heuristic G_E___208_C02CMA_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.43  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.43  #
% 0.19/0.43  # Preprocessing time       : 0.029 s
% 0.19/0.43  # Presaturation interreduction done
% 0.19/0.43  
% 0.19/0.43  # Proof found!
% 0.19/0.43  # SZS status Theorem
% 0.19/0.43  # SZS output start CNFRefutation
% 0.19/0.43  fof(t29_yellow_6, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>r1_waybel_0(X1,X2,u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_yellow_6)).
% 0.19/0.43  fof(rc5_waybel_0, axiom, ![X1]:(l1_struct_0(X1)=>?[X2]:((((((l1_waybel_0(X2,X1)&~(v2_struct_0(X2)))&v3_orders_2(X2))&v4_orders_2(X2))&v5_orders_2(X2))&v6_waybel_0(X2,X1))&v7_waybel_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc5_waybel_0)).
% 0.19/0.43  fof(t8_waybel_9, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>r1_waybel_0(X1,X2,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_9)).
% 0.19/0.43  fof(t28_yellow_6, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r1_waybel_0(X1,X2,X3)=>r2_waybel_0(X1,X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_yellow_6)).
% 0.19/0.43  fof(dt_o_2_4_waybel_9, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v2_struct_0(X2)))&l1_waybel_0(X2,X1))=>m1_subset_1(o_2_4_waybel_9(X1,X2),u1_struct_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_o_2_4_waybel_9)).
% 0.19/0.43  fof(d12_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r2_waybel_0(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X2))=>?[X5]:((m1_subset_1(X5,u1_struct_0(X2))&r1_orders_2(X2,X4,X5))&r2_hidden(k2_waybel_0(X1,X2,X5),X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_waybel_0)).
% 0.19/0.43  fof(d11_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r1_waybel_0(X1,X2,X3)<=>?[X4]:(m1_subset_1(X4,u1_struct_0(X2))&![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>(r1_orders_2(X2,X4,X5)=>r2_hidden(k2_waybel_0(X1,X2,X5),X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_waybel_0)).
% 0.19/0.43  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.19/0.43  fof(dt_l1_waybel_0, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_waybel_0(X2,X1)=>l1_orders_2(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 0.19/0.43  fof(t189_funct_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,X1)=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>r2_hidden(k3_funct_2(X1,X2,X4,X3),k2_relset_1(X1,X2,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t189_funct_2)).
% 0.19/0.43  fof(dt_u1_waybel_0, axiom, ![X1, X2]:((l1_struct_0(X1)&l1_waybel_0(X2,X1))=>((v1_funct_1(u1_waybel_0(X1,X2))&v1_funct_2(u1_waybel_0(X1,X2),u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(u1_waybel_0(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_waybel_0)).
% 0.19/0.43  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.43  fof(d8_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>k2_waybel_0(X1,X2,X3)=k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_waybel_0)).
% 0.19/0.43  fof(c_0_13, plain, ![X43, X44]:(v2_struct_0(X43)|~l1_struct_0(X43)|(v2_struct_0(X44)|~v4_orders_2(X44)|~v7_waybel_0(X44)|~l1_waybel_0(X44,X43)|r1_waybel_0(X43,X44,u1_struct_0(X43)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t29_yellow_6])])])])).
% 0.19/0.43  fof(c_0_14, plain, ![X38]:(((((((l1_waybel_0(esk6_1(X38),X38)|~l1_struct_0(X38))&(~v2_struct_0(esk6_1(X38))|~l1_struct_0(X38)))&(v3_orders_2(esk6_1(X38))|~l1_struct_0(X38)))&(v4_orders_2(esk6_1(X38))|~l1_struct_0(X38)))&(v5_orders_2(esk6_1(X38))|~l1_struct_0(X38)))&(v6_waybel_0(esk6_1(X38),X38)|~l1_struct_0(X38)))&(v7_waybel_0(esk6_1(X38))|~l1_struct_0(X38))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc5_waybel_0])])])])])).
% 0.19/0.43  fof(c_0_15, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>r1_waybel_0(X1,X2,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)))))), inference(assume_negation,[status(cth)],[t8_waybel_9])).
% 0.19/0.43  cnf(c_0_16, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r1_waybel_0(X1,X2,u1_struct_0(X1))|~l1_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.43  cnf(c_0_17, plain, (l1_waybel_0(esk6_1(X1),X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.43  cnf(c_0_18, plain, (v4_orders_2(esk6_1(X1))|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.43  cnf(c_0_19, plain, (v7_waybel_0(esk6_1(X1))|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.43  cnf(c_0_20, plain, (~v2_struct_0(esk6_1(X1))|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.43  fof(c_0_21, negated_conjecture, ((~v2_struct_0(esk7_0)&l1_struct_0(esk7_0))&((~v2_struct_0(esk8_0)&l1_waybel_0(esk8_0,esk7_0))&~r1_waybel_0(esk7_0,esk8_0,k2_relset_1(u1_struct_0(esk8_0),u1_struct_0(esk7_0),u1_waybel_0(esk7_0,esk8_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).
% 0.19/0.43  fof(c_0_22, plain, ![X40, X41, X42]:(v2_struct_0(X40)|~l1_struct_0(X40)|(v2_struct_0(X41)|~v4_orders_2(X41)|~v7_waybel_0(X41)|~l1_waybel_0(X41,X40)|(~r1_waybel_0(X40,X41,X42)|r2_waybel_0(X40,X41,X42)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t28_yellow_6])])])])).
% 0.19/0.43  cnf(c_0_23, plain, (r1_waybel_0(X1,esk6_1(X1),u1_struct_0(X1))|v2_struct_0(X1)|~l1_struct_0(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19]), c_0_20])).
% 0.19/0.43  cnf(c_0_24, negated_conjecture, (l1_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.43  cnf(c_0_25, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.43  fof(c_0_26, plain, ![X45, X46]:(v2_struct_0(X45)|~l1_struct_0(X45)|v2_struct_0(X46)|~l1_waybel_0(X46,X45)|m1_subset_1(o_2_4_waybel_9(X45,X46),u1_struct_0(X46))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_o_2_4_waybel_9])])])).
% 0.19/0.43  cnf(c_0_27, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r2_waybel_0(X1,X2,X3)|~l1_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~r1_waybel_0(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.43  cnf(c_0_28, negated_conjecture, (r1_waybel_0(esk7_0,esk6_1(esk7_0),u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])).
% 0.19/0.43  cnf(c_0_29, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(o_2_4_waybel_9(X1,X2),u1_struct_0(X2))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.43  cnf(c_0_30, negated_conjecture, (r2_waybel_0(esk7_0,esk6_1(esk7_0),u1_struct_0(esk7_0))|v2_struct_0(esk6_1(esk7_0))|~v7_waybel_0(esk6_1(esk7_0))|~v4_orders_2(esk6_1(esk7_0))|~l1_waybel_0(esk6_1(esk7_0),esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_24])]), c_0_25])).
% 0.19/0.43  fof(c_0_31, plain, ![X23, X24, X25, X26, X28, X30]:((((m1_subset_1(esk4_4(X23,X24,X25,X26),u1_struct_0(X24))|~m1_subset_1(X26,u1_struct_0(X24))|~r2_waybel_0(X23,X24,X25)|(v2_struct_0(X24)|~l1_waybel_0(X24,X23))|(v2_struct_0(X23)|~l1_struct_0(X23)))&(r1_orders_2(X24,X26,esk4_4(X23,X24,X25,X26))|~m1_subset_1(X26,u1_struct_0(X24))|~r2_waybel_0(X23,X24,X25)|(v2_struct_0(X24)|~l1_waybel_0(X24,X23))|(v2_struct_0(X23)|~l1_struct_0(X23))))&(r2_hidden(k2_waybel_0(X23,X24,esk4_4(X23,X24,X25,X26)),X25)|~m1_subset_1(X26,u1_struct_0(X24))|~r2_waybel_0(X23,X24,X25)|(v2_struct_0(X24)|~l1_waybel_0(X24,X23))|(v2_struct_0(X23)|~l1_struct_0(X23))))&((m1_subset_1(esk5_3(X23,X24,X28),u1_struct_0(X24))|r2_waybel_0(X23,X24,X28)|(v2_struct_0(X24)|~l1_waybel_0(X24,X23))|(v2_struct_0(X23)|~l1_struct_0(X23)))&(~m1_subset_1(X30,u1_struct_0(X24))|~r1_orders_2(X24,esk5_3(X23,X24,X28),X30)|~r2_hidden(k2_waybel_0(X23,X24,X30),X28)|r2_waybel_0(X23,X24,X28)|(v2_struct_0(X24)|~l1_waybel_0(X24,X23))|(v2_struct_0(X23)|~l1_struct_0(X23))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_waybel_0])])])])])])])).
% 0.19/0.43  cnf(c_0_32, plain, (v2_struct_0(X1)|m1_subset_1(o_2_4_waybel_9(X1,esk6_1(X1)),u1_struct_0(esk6_1(X1)))|~l1_struct_0(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_17]), c_0_20])).
% 0.19/0.43  cnf(c_0_33, negated_conjecture, (r2_waybel_0(esk7_0,esk6_1(esk7_0),u1_struct_0(esk7_0))|v2_struct_0(esk6_1(esk7_0))|~v4_orders_2(esk6_1(esk7_0))|~l1_waybel_0(esk6_1(esk7_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_19]), c_0_24])])).
% 0.19/0.43  cnf(c_0_34, plain, (r2_hidden(k2_waybel_0(X1,X2,esk4_4(X1,X2,X3,X4)),X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X4,u1_struct_0(X2))|~r2_waybel_0(X1,X2,X3)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.43  cnf(c_0_35, negated_conjecture, (m1_subset_1(o_2_4_waybel_9(esk7_0,esk6_1(esk7_0)),u1_struct_0(esk6_1(esk7_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_24]), c_0_25])).
% 0.19/0.43  cnf(c_0_36, negated_conjecture, (r2_waybel_0(esk7_0,esk6_1(esk7_0),u1_struct_0(esk7_0))|v2_struct_0(esk6_1(esk7_0))|~l1_waybel_0(esk6_1(esk7_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_18]), c_0_24])])).
% 0.19/0.43  fof(c_0_37, plain, ![X15, X16, X17, X19, X20, X21]:(((m1_subset_1(esk2_3(X15,X16,X17),u1_struct_0(X16))|~r1_waybel_0(X15,X16,X17)|(v2_struct_0(X16)|~l1_waybel_0(X16,X15))|(v2_struct_0(X15)|~l1_struct_0(X15)))&(~m1_subset_1(X19,u1_struct_0(X16))|(~r1_orders_2(X16,esk2_3(X15,X16,X17),X19)|r2_hidden(k2_waybel_0(X15,X16,X19),X17))|~r1_waybel_0(X15,X16,X17)|(v2_struct_0(X16)|~l1_waybel_0(X16,X15))|(v2_struct_0(X15)|~l1_struct_0(X15))))&((m1_subset_1(esk3_4(X15,X16,X20,X21),u1_struct_0(X16))|~m1_subset_1(X21,u1_struct_0(X16))|r1_waybel_0(X15,X16,X20)|(v2_struct_0(X16)|~l1_waybel_0(X16,X15))|(v2_struct_0(X15)|~l1_struct_0(X15)))&((r1_orders_2(X16,X21,esk3_4(X15,X16,X20,X21))|~m1_subset_1(X21,u1_struct_0(X16))|r1_waybel_0(X15,X16,X20)|(v2_struct_0(X16)|~l1_waybel_0(X16,X15))|(v2_struct_0(X15)|~l1_struct_0(X15)))&(~r2_hidden(k2_waybel_0(X15,X16,esk3_4(X15,X16,X20,X21)),X20)|~m1_subset_1(X21,u1_struct_0(X16))|r1_waybel_0(X15,X16,X20)|(v2_struct_0(X16)|~l1_waybel_0(X16,X15))|(v2_struct_0(X15)|~l1_struct_0(X15)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_waybel_0])])])])])])])).
% 0.19/0.43  cnf(c_0_38, negated_conjecture, (l1_waybel_0(esk8_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.43  cnf(c_0_39, negated_conjecture, (~v2_struct_0(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.43  cnf(c_0_40, negated_conjecture, (v2_struct_0(esk6_1(esk7_0))|v2_struct_0(X1)|r2_hidden(k2_waybel_0(X1,esk6_1(esk7_0),esk4_4(X1,esk6_1(esk7_0),X2,o_2_4_waybel_9(esk7_0,esk6_1(esk7_0)))),X2)|~r2_waybel_0(X1,esk6_1(esk7_0),X2)|~l1_waybel_0(esk6_1(esk7_0),X1)|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.43  cnf(c_0_41, negated_conjecture, (r2_waybel_0(esk7_0,esk6_1(esk7_0),u1_struct_0(esk7_0))|v2_struct_0(esk6_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_17]), c_0_24])])).
% 0.19/0.43  fof(c_0_42, plain, ![X14]:(~l1_orders_2(X14)|l1_struct_0(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.19/0.43  fof(c_0_43, plain, ![X34, X35]:(~l1_struct_0(X34)|(~l1_waybel_0(X35,X34)|l1_orders_2(X35))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).
% 0.19/0.43  fof(c_0_44, plain, ![X10, X11, X12, X13]:(v1_xboole_0(X10)|(v1_xboole_0(X11)|(~m1_subset_1(X12,X10)|(~v1_funct_1(X13)|~v1_funct_2(X13,X10,X11)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))|r2_hidden(k3_funct_2(X10,X11,X13,X12),k2_relset_1(X10,X11,X13)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t189_funct_2])])])])).
% 0.19/0.43  fof(c_0_45, plain, ![X36, X37]:(((v1_funct_1(u1_waybel_0(X36,X37))|(~l1_struct_0(X36)|~l1_waybel_0(X37,X36)))&(v1_funct_2(u1_waybel_0(X36,X37),u1_struct_0(X37),u1_struct_0(X36))|(~l1_struct_0(X36)|~l1_waybel_0(X37,X36))))&(m1_subset_1(u1_waybel_0(X36,X37),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X36))))|(~l1_struct_0(X36)|~l1_waybel_0(X37,X36)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_waybel_0])])])).
% 0.19/0.43  cnf(c_0_46, plain, (m1_subset_1(esk3_4(X1,X2,X3,X4),u1_struct_0(X2))|r1_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.43  cnf(c_0_47, negated_conjecture, (m1_subset_1(o_2_4_waybel_9(esk7_0,esk8_0),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_38]), c_0_24])]), c_0_39]), c_0_25])).
% 0.19/0.43  fof(c_0_48, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.43  cnf(c_0_49, negated_conjecture, (v2_struct_0(esk6_1(esk7_0))|r2_hidden(k2_waybel_0(esk7_0,esk6_1(esk7_0),esk4_4(esk7_0,esk6_1(esk7_0),u1_struct_0(esk7_0),o_2_4_waybel_9(esk7_0,esk6_1(esk7_0)))),u1_struct_0(esk7_0))|~l1_waybel_0(esk6_1(esk7_0),esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_24])]), c_0_25])).
% 0.19/0.43  cnf(c_0_50, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.43  cnf(c_0_51, plain, (l1_orders_2(X2)|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.43  cnf(c_0_52, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|r2_hidden(k3_funct_2(X1,X2,X4,X3),k2_relset_1(X1,X2,X4))|~m1_subset_1(X3,X1)|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.43  cnf(c_0_53, plain, (m1_subset_1(u1_waybel_0(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.43  cnf(c_0_54, plain, (v1_funct_1(u1_waybel_0(X1,X2))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.43  cnf(c_0_55, plain, (v1_funct_2(u1_waybel_0(X1,X2),u1_struct_0(X2),u1_struct_0(X1))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.43  cnf(c_0_56, negated_conjecture, (r1_waybel_0(X1,esk8_0,X2)|v2_struct_0(X1)|m1_subset_1(esk3_4(X1,esk8_0,X2,o_2_4_waybel_9(esk7_0,esk8_0)),u1_struct_0(esk8_0))|~l1_waybel_0(esk8_0,X1)|~l1_struct_0(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_39])).
% 0.19/0.43  cnf(c_0_57, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.43  cnf(c_0_58, negated_conjecture, (v2_struct_0(esk6_1(esk7_0))|r2_hidden(k2_waybel_0(esk7_0,esk6_1(esk7_0),esk4_4(esk7_0,esk6_1(esk7_0),u1_struct_0(esk7_0),o_2_4_waybel_9(esk7_0,esk6_1(esk7_0)))),u1_struct_0(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_17]), c_0_24])])).
% 0.19/0.43  fof(c_0_59, plain, ![X31, X32, X33]:(v2_struct_0(X31)|~l1_struct_0(X31)|(v2_struct_0(X32)|~l1_waybel_0(X32,X31)|(~m1_subset_1(X33,u1_struct_0(X32))|k2_waybel_0(X31,X32,X33)=k3_funct_2(u1_struct_0(X32),u1_struct_0(X31),u1_waybel_0(X31,X32),X33)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_waybel_0])])])])).
% 0.19/0.43  cnf(c_0_60, plain, (v2_struct_0(X1)|m1_subset_1(o_2_4_waybel_9(X1,esk6_1(X1)),u1_struct_0(esk6_1(X1)))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_32, c_0_50])).
% 0.19/0.43  cnf(c_0_61, negated_conjecture, (l1_orders_2(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_38]), c_0_24])])).
% 0.19/0.43  cnf(c_0_62, plain, (r1_waybel_0(X1,esk6_1(X1),u1_struct_0(X1))|v2_struct_0(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_23, c_0_50])).
% 0.19/0.43  cnf(c_0_63, plain, (r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),X3),k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1)))|v1_xboole_0(u1_struct_0(X1))|v1_xboole_0(u1_struct_0(X2))|~l1_waybel_0(X1,X2)|~l1_struct_0(X2)|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), c_0_55])).
% 0.19/0.43  cnf(c_0_64, negated_conjecture, (r1_waybel_0(esk7_0,esk8_0,X1)|m1_subset_1(esk3_4(esk7_0,esk8_0,X1,o_2_4_waybel_9(esk7_0,esk8_0)),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_38]), c_0_24])]), c_0_25])).
% 0.19/0.43  cnf(c_0_65, negated_conjecture, (v2_struct_0(esk6_1(esk7_0))|~v1_xboole_0(u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.19/0.43  cnf(c_0_66, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_waybel_0(X1,X2,X3)=k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),X3)|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.19/0.43  cnf(c_0_67, negated_conjecture, (m1_subset_1(o_2_4_waybel_9(esk8_0,esk6_1(esk8_0)),u1_struct_0(esk6_1(esk8_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_39])).
% 0.19/0.43  cnf(c_0_68, negated_conjecture, (r1_waybel_0(esk8_0,esk6_1(esk8_0),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_61]), c_0_39])).
% 0.19/0.43  cnf(c_0_69, negated_conjecture, (r1_waybel_0(esk7_0,esk8_0,X1)|r2_hidden(k3_funct_2(u1_struct_0(esk8_0),u1_struct_0(X2),u1_waybel_0(X2,esk8_0),esk3_4(esk7_0,esk8_0,X1,o_2_4_waybel_9(esk7_0,esk8_0))),k2_relset_1(u1_struct_0(esk8_0),u1_struct_0(X2),u1_waybel_0(X2,esk8_0)))|v1_xboole_0(u1_struct_0(esk8_0))|v1_xboole_0(u1_struct_0(X2))|~l1_waybel_0(esk8_0,X2)|~l1_struct_0(X2)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.19/0.43  cnf(c_0_70, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_65]), c_0_24])])).
% 0.19/0.43  cnf(c_0_71, negated_conjecture, (k3_funct_2(u1_struct_0(esk8_0),u1_struct_0(X1),u1_waybel_0(X1,esk8_0),esk3_4(esk7_0,esk8_0,X2,o_2_4_waybel_9(esk7_0,esk8_0)))=k2_waybel_0(X1,esk8_0,esk3_4(esk7_0,esk8_0,X2,o_2_4_waybel_9(esk7_0,esk8_0)))|r1_waybel_0(esk7_0,esk8_0,X2)|v2_struct_0(X1)|~l1_waybel_0(esk8_0,X1)|~l1_struct_0(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_64]), c_0_39])).
% 0.19/0.43  cnf(c_0_72, negated_conjecture, (v2_struct_0(esk6_1(esk8_0))|v2_struct_0(X1)|r2_hidden(k2_waybel_0(X1,esk6_1(esk8_0),esk4_4(X1,esk6_1(esk8_0),X2,o_2_4_waybel_9(esk8_0,esk6_1(esk8_0)))),X2)|~r2_waybel_0(X1,esk6_1(esk8_0),X2)|~l1_waybel_0(esk6_1(esk8_0),X1)|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_34, c_0_67])).
% 0.19/0.43  cnf(c_0_73, negated_conjecture, (r2_waybel_0(esk8_0,esk6_1(esk8_0),u1_struct_0(esk8_0))|~l1_struct_0(esk8_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_68]), c_0_39]), c_0_17]), c_0_18]), c_0_19]), c_0_20])).
% 0.19/0.43  cnf(c_0_74, negated_conjecture, (r1_waybel_0(esk7_0,esk8_0,X1)|r2_hidden(k3_funct_2(u1_struct_0(esk8_0),u1_struct_0(esk7_0),u1_waybel_0(esk7_0,esk8_0),esk3_4(esk7_0,esk8_0,X1,o_2_4_waybel_9(esk7_0,esk8_0))),k2_relset_1(u1_struct_0(esk8_0),u1_struct_0(esk7_0),u1_waybel_0(esk7_0,esk8_0)))|v1_xboole_0(u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_38]), c_0_24])]), c_0_70])).
% 0.19/0.43  cnf(c_0_75, negated_conjecture, (k3_funct_2(u1_struct_0(esk8_0),u1_struct_0(esk7_0),u1_waybel_0(esk7_0,esk8_0),esk3_4(esk7_0,esk8_0,X1,o_2_4_waybel_9(esk7_0,esk8_0)))=k2_waybel_0(esk7_0,esk8_0,esk3_4(esk7_0,esk8_0,X1,o_2_4_waybel_9(esk7_0,esk8_0)))|r1_waybel_0(esk7_0,esk8_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_38]), c_0_24])]), c_0_25])).
% 0.19/0.43  cnf(c_0_76, negated_conjecture, (r2_hidden(k2_waybel_0(esk8_0,esk6_1(esk8_0),esk4_4(esk8_0,esk6_1(esk8_0),u1_struct_0(esk8_0),o_2_4_waybel_9(esk8_0,esk6_1(esk8_0)))),u1_struct_0(esk8_0))|~l1_struct_0(esk8_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_39]), c_0_17]), c_0_20])).
% 0.19/0.43  cnf(c_0_77, plain, (r1_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r2_hidden(k2_waybel_0(X1,X2,esk3_4(X1,X2,X3,X4)),X3)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.43  cnf(c_0_78, negated_conjecture, (r1_waybel_0(esk7_0,esk8_0,X1)|r2_hidden(k2_waybel_0(esk7_0,esk8_0,esk3_4(esk7_0,esk8_0,X1,o_2_4_waybel_9(esk7_0,esk8_0))),k2_relset_1(u1_struct_0(esk8_0),u1_struct_0(esk7_0),u1_waybel_0(esk7_0,esk8_0)))|v1_xboole_0(u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.19/0.43  cnf(c_0_79, negated_conjecture, (~r1_waybel_0(esk7_0,esk8_0,k2_relset_1(u1_struct_0(esk8_0),u1_struct_0(esk7_0),u1_waybel_0(esk7_0,esk8_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.43  cnf(c_0_80, negated_conjecture, (~l1_struct_0(esk8_0)|~v1_xboole_0(u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_57, c_0_76])).
% 0.19/0.43  cnf(c_0_81, negated_conjecture, (v1_xboole_0(u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_38]), c_0_24]), c_0_47])]), c_0_79]), c_0_39]), c_0_25])).
% 0.19/0.43  cnf(c_0_82, negated_conjecture, (~l1_struct_0(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_81])])).
% 0.19/0.43  cnf(c_0_83, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_50]), c_0_61])]), ['proof']).
% 0.19/0.43  # SZS output end CNFRefutation
% 0.19/0.43  # Proof object total steps             : 84
% 0.19/0.43  # Proof object clause steps            : 57
% 0.19/0.43  # Proof object formula steps           : 27
% 0.19/0.43  # Proof object conjectures             : 37
% 0.19/0.43  # Proof object clause conjectures      : 34
% 0.19/0.43  # Proof object formula conjectures     : 3
% 0.19/0.43  # Proof object initial clauses used    : 23
% 0.19/0.43  # Proof object initial formulas used   : 13
% 0.19/0.43  # Proof object generating inferences   : 33
% 0.19/0.43  # Proof object simplifying inferences  : 62
% 0.19/0.43  # Training examples: 0 positive, 0 negative
% 0.19/0.43  # Parsed axioms                        : 13
% 0.19/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.43  # Initial clauses                      : 34
% 0.19/0.43  # Removed in clause preprocessing      : 0
% 0.19/0.43  # Initial clauses in saturation        : 34
% 0.19/0.43  # Processed clauses                    : 360
% 0.19/0.43  # ...of these trivial                  : 0
% 0.19/0.43  # ...subsumed                          : 25
% 0.19/0.43  # ...remaining for further processing  : 335
% 0.19/0.43  # Other redundant clauses eliminated   : 0
% 0.19/0.43  # Clauses deleted for lack of memory   : 0
% 0.19/0.43  # Backward-subsumed                    : 40
% 0.19/0.43  # Backward-rewritten                   : 14
% 0.19/0.43  # Generated clauses                    : 519
% 0.19/0.43  # ...of the previous two non-trivial   : 518
% 0.19/0.43  # Contextual simplify-reflections      : 77
% 0.19/0.43  # Paramodulations                      : 519
% 0.19/0.43  # Factorizations                       : 0
% 0.19/0.43  # Equation resolutions                 : 0
% 0.19/0.43  # Propositional unsat checks           : 0
% 0.19/0.43  #    Propositional check models        : 0
% 0.19/0.43  #    Propositional check unsatisfiable : 0
% 0.19/0.43  #    Propositional clauses             : 0
% 0.19/0.43  #    Propositional clauses after purity: 0
% 0.19/0.43  #    Propositional unsat core size     : 0
% 0.19/0.43  #    Propositional preprocessing time  : 0.000
% 0.19/0.43  #    Propositional encoding time       : 0.000
% 0.19/0.43  #    Propositional solver time         : 0.000
% 0.19/0.43  #    Success case prop preproc time    : 0.000
% 0.19/0.43  #    Success case prop encoding time   : 0.000
% 0.19/0.43  #    Success case prop solver time     : 0.000
% 0.19/0.43  # Current number of processed clauses  : 247
% 0.19/0.43  #    Positive orientable unit clauses  : 10
% 0.19/0.43  #    Positive unorientable unit clauses: 0
% 0.19/0.43  #    Negative unit clauses             : 5
% 0.19/0.43  #    Non-unit-clauses                  : 232
% 0.19/0.43  # Current number of unprocessed clauses: 226
% 0.19/0.43  # ...number of literals in the above   : 1475
% 0.19/0.43  # Current number of archived formulas  : 0
% 0.19/0.43  # Current number of archived clauses   : 88
% 0.19/0.43  # Clause-clause subsumption calls (NU) : 15826
% 0.19/0.43  # Rec. Clause-clause subsumption calls : 1725
% 0.19/0.43  # Non-unit clause-clause subsumptions  : 138
% 0.19/0.43  # Unit Clause-clause subsumption calls : 158
% 0.19/0.43  # Rewrite failures with RHS unbound    : 0
% 0.19/0.43  # BW rewrite match attempts            : 1
% 0.19/0.43  # BW rewrite match successes           : 1
% 0.19/0.43  # Condensation attempts                : 0
% 0.19/0.43  # Condensation successes               : 0
% 0.19/0.43  # Termbank termtop insertions          : 29726
% 0.19/0.43  
% 0.19/0.43  # -------------------------------------------------
% 0.19/0.43  # User time                : 0.076 s
% 0.19/0.43  # System time              : 0.009 s
% 0.19/0.43  # Total time               : 0.086 s
% 0.19/0.43  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
