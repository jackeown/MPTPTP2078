%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:27 EST 2020

% Result     : Theorem 0.17s
% Output     : CNFRefutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 475 expanded)
%              Number of clauses        :   54 ( 194 expanded)
%              Number of leaves         :   15 ( 117 expanded)
%              Depth                    :   14
%              Number of atoms          :  340 (3090 expanded)
%              Number of equality atoms :   38 ( 157 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   30 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(t10_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ~ ( X2 != k1_xboole_0
          & ! [X3] :
              ( m1_subset_1(X3,X1)
             => ~ r2_hidden(X3,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

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

fof(t49_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( ! [X3] :
            ( m1_subset_1(X3,X1)
           => r2_hidden(X3,X2) )
       => X1 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

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

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

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

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(c_0_15,plain,(
    ! [X19,X20,X21] :
      ( ~ r2_hidden(X19,X20)
      | ~ m1_subset_1(X20,k1_zfmisc_1(X21))
      | ~ v1_xboole_0(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_16,plain,(
    ! [X5] : m1_subset_1(k2_subset_1(X5),k1_zfmisc_1(X5)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_17,plain,(
    ! [X6,X7] :
      ( ( m1_subset_1(esk1_2(X6,X7),X6)
        | X7 = k1_xboole_0
        | ~ m1_subset_1(X7,k1_zfmisc_1(X6)) )
      & ( r2_hidden(esk1_2(X6,X7),X7)
        | X7 = k1_xboole_0
        | ~ m1_subset_1(X7,k1_zfmisc_1(X6)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_subset_1])])])])])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | X2 = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,negated_conjecture,(
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

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,k2_subset_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,plain,
    ( k2_subset_1(X1) = k1_xboole_0
    | r2_hidden(esk1_2(X1,k2_subset_1(X1)),k2_subset_1(X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_19])).

fof(c_0_24,plain,(
    ! [X36,X37,X38,X39] :
      ( ( ~ v13_waybel_0(X37,X36)
        | ~ m1_subset_1(X38,u1_struct_0(X36))
        | ~ m1_subset_1(X39,u1_struct_0(X36))
        | ~ r2_hidden(X38,X37)
        | ~ r1_orders_2(X36,X38,X39)
        | r2_hidden(X39,X37)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ l1_orders_2(X36) )
      & ( m1_subset_1(esk5_2(X36,X37),u1_struct_0(X36))
        | v13_waybel_0(X37,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ l1_orders_2(X36) )
      & ( m1_subset_1(esk6_2(X36,X37),u1_struct_0(X36))
        | v13_waybel_0(X37,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ l1_orders_2(X36) )
      & ( r2_hidden(esk5_2(X36,X37),X37)
        | v13_waybel_0(X37,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ l1_orders_2(X36) )
      & ( r1_orders_2(X36,esk5_2(X36,X37),esk6_2(X36,X37))
        | v13_waybel_0(X37,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ l1_orders_2(X36) )
      & ( ~ r2_hidden(esk6_2(X36,X37),X37)
        | v13_waybel_0(X37,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ l1_orders_2(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).

fof(c_0_25,plain,(
    ! [X16,X17,X18] :
      ( ~ r2_hidden(X16,X17)
      | ~ m1_subset_1(X17,k1_zfmisc_1(X18))
      | m1_subset_1(X16,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_26,plain,(
    ! [X9,X10] :
      ( ( m1_subset_1(esk2_2(X9,X10),X9)
        | X9 = X10
        | ~ m1_subset_1(X10,k1_zfmisc_1(X9)) )
      & ( ~ r2_hidden(esk2_2(X9,X10),X10)
        | X9 = X10
        | ~ m1_subset_1(X10,k1_zfmisc_1(X9)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_subset_1])])])])).

fof(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk7_0)
    & v3_orders_2(esk7_0)
    & v4_orders_2(esk7_0)
    & v5_orders_2(esk7_0)
    & v1_yellow_0(esk7_0)
    & l1_orders_2(esk7_0)
    & ~ v1_xboole_0(esk8_0)
    & v2_waybel_0(esk8_0,esk7_0)
    & v13_waybel_0(esk8_0,esk7_0)
    & m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0)))
    & ( ~ v1_subset_1(esk8_0,u1_struct_0(esk7_0))
      | r2_hidden(k3_yellow_0(esk7_0),esk8_0) )
    & ( v1_subset_1(esk8_0,u1_struct_0(esk7_0))
      | ~ r2_hidden(k3_yellow_0(esk7_0),esk8_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).

fof(c_0_28,plain,(
    ! [X42,X43] :
      ( ( ~ v1_subset_1(X43,X42)
        | X43 != X42
        | ~ m1_subset_1(X43,k1_zfmisc_1(X42)) )
      & ( X43 = X42
        | v1_subset_1(X43,X42)
        | ~ m1_subset_1(X43,k1_zfmisc_1(X42)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

cnf(c_0_29,plain,
    ( k2_subset_1(X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,plain,
    ( r2_hidden(X4,X1)
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(X3,X1)
    | ~ r1_orders_2(X2,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( m1_subset_1(esk2_2(X1,X2),X1)
    | X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_35,plain,(
    ! [X28,X29,X30,X31] :
      ( ( r2_lattice3(X28,X29,X30)
        | X30 != k1_yellow_0(X28,X29)
        | ~ r1_yellow_0(X28,X29)
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | ~ l1_orders_2(X28) )
      & ( ~ m1_subset_1(X31,u1_struct_0(X28))
        | ~ r2_lattice3(X28,X29,X31)
        | r1_orders_2(X28,X30,X31)
        | X30 != k1_yellow_0(X28,X29)
        | ~ r1_yellow_0(X28,X29)
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | ~ l1_orders_2(X28) )
      & ( m1_subset_1(esk4_3(X28,X29,X30),u1_struct_0(X28))
        | ~ r2_lattice3(X28,X29,X30)
        | X30 = k1_yellow_0(X28,X29)
        | ~ r1_yellow_0(X28,X29)
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | ~ l1_orders_2(X28) )
      & ( r2_lattice3(X28,X29,esk4_3(X28,X29,X30))
        | ~ r2_lattice3(X28,X29,X30)
        | X30 = k1_yellow_0(X28,X29)
        | ~ r1_yellow_0(X28,X29)
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | ~ l1_orders_2(X28) )
      & ( ~ r1_orders_2(X28,X30,esk4_3(X28,X29,X30))
        | ~ r2_lattice3(X28,X29,X30)
        | X30 = k1_yellow_0(X28,X29)
        | ~ r1_yellow_0(X28,X29)
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | ~ l1_orders_2(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).

fof(c_0_36,plain,(
    ! [X33,X34] :
      ( ~ l1_orders_2(X33)
      | m1_subset_1(k1_yellow_0(X33,X34),u1_struct_0(X33)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

cnf(c_0_37,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_29])).

cnf(c_0_38,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_39,plain,(
    ! [X22,X23,X24,X25] :
      ( ( ~ r2_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ r2_hidden(X25,X23)
        | r1_orders_2(X22,X25,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ l1_orders_2(X22) )
      & ( m1_subset_1(esk3_3(X22,X23,X24),u1_struct_0(X22))
        | r2_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ l1_orders_2(X22) )
      & ( r2_hidden(esk3_3(X22,X23,X24),X23)
        | r2_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ l1_orders_2(X22) )
      & ( ~ r1_orders_2(X22,esk3_3(X22,X23,X24),X24)
        | r2_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ l1_orders_2(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X2)
    | ~ v13_waybel_0(X2,X3)
    | ~ r1_orders_2(X3,X4,X1)
    | ~ l1_orders_2(X3)
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3)) ),
    inference(csr,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | m1_subset_1(esk2_2(u1_struct_0(esk7_0),esk8_0),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( l1_orders_2(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_43,plain,
    ( X1 = X2
    | ~ r2_hidden(esk2_2(X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(k3_yellow_0(esk7_0),esk8_0)
    | ~ v1_subset_1(esk8_0,u1_struct_0(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_45,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | v1_subset_1(esk8_0,u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_33])).

fof(c_0_46,plain,(
    ! [X27] :
      ( ~ l1_orders_2(X27)
      | k3_yellow_0(X27) = k1_yellow_0(X27,k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).

cnf(c_0_47,plain,
    ( r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | X4 != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_49,plain,(
    ! [X35] :
      ( ( r1_yellow_0(X35,k1_xboole_0)
        | v2_struct_0(X35)
        | ~ v5_orders_2(X35)
        | ~ v1_yellow_0(X35)
        | ~ l1_orders_2(X35) )
      & ( r2_yellow_0(X35,u1_struct_0(X35))
        | v2_struct_0(X35)
        | ~ v5_orders_2(X35)
        | ~ v1_yellow_0(X35)
        | ~ l1_orders_2(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_0])])])])).

cnf(c_0_50,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_51,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_52,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | r2_hidden(esk2_2(u1_struct_0(esk7_0),esk8_0),X1)
    | ~ v13_waybel_0(X1,esk7_0)
    | ~ r1_orders_2(esk7_0,X2,esk2_2(u1_struct_0(esk7_0),esk8_0))
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])])).

cnf(c_0_53,negated_conjecture,
    ( v13_waybel_0(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_54,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | ~ r2_hidden(esk2_2(u1_struct_0(esk7_0),esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_33])).

cnf(c_0_55,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | r2_hidden(k3_yellow_0(esk7_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_56,plain,
    ( k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_57,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_47]),c_0_48])).

cnf(c_0_58,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_59,plain,
    ( r1_yellow_0(X1,k1_xboole_0)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_60,negated_conjecture,
    ( v1_yellow_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_61,negated_conjecture,
    ( v5_orders_2(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_62,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_50]),c_0_38])])).

cnf(c_0_63,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | r2_lattice3(esk7_0,X1,esk2_2(u1_struct_0(esk7_0),esk8_0))
    | r2_hidden(esk3_3(esk7_0,X1,esk2_2(u1_struct_0(esk7_0),esk8_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_41]),c_0_42])])).

cnf(c_0_64,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | ~ r1_orders_2(esk7_0,X1,esk2_2(u1_struct_0(esk7_0),esk8_0))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_33])]),c_0_54])).

cnf(c_0_65,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | r2_hidden(k1_yellow_0(esk7_0,k1_xboole_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_42])])).

cnf(c_0_66,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | r1_orders_2(esk7_0,k1_yellow_0(esk7_0,X1),esk2_2(u1_struct_0(esk7_0),esk8_0))
    | ~ r1_yellow_0(esk7_0,X1)
    | ~ r2_lattice3(esk7_0,X1,esk2_2(u1_struct_0(esk7_0),esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_41]),c_0_42])])).

cnf(c_0_67,negated_conjecture,
    ( r1_yellow_0(esk7_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60]),c_0_61]),c_0_42])])).

cnf(c_0_68,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | r2_lattice3(esk7_0,k1_xboole_0,esk2_2(u1_struct_0(esk7_0),esk8_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0
    | ~ r1_orders_2(esk7_0,k1_yellow_0(esk7_0,k1_xboole_0),esk2_2(u1_struct_0(esk7_0),esk8_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_70,plain,
    ( ~ v1_subset_1(X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_71,negated_conjecture,
    ( u1_struct_0(esk7_0) = esk8_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68]),c_0_69])).

cnf(c_0_72,plain,
    ( ~ v1_subset_1(X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(er,[status(thm)],[c_0_70])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(esk8_0)) ),
    inference(rw,[status(thm)],[c_0_33,c_0_71])).

fof(c_0_74,plain,(
    ! [X14,X15] :
      ( ~ m1_subset_1(X14,X15)
      | v1_xboole_0(X15)
      | r2_hidden(X14,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_75,negated_conjecture,
    ( v1_subset_1(esk8_0,u1_struct_0(esk7_0))
    | ~ r2_hidden(k3_yellow_0(esk7_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_76,negated_conjecture,
    ( ~ v1_subset_1(esk8_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_77,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_78,negated_conjecture,
    ( ~ r2_hidden(k3_yellow_0(esk7_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_71]),c_0_76])).

cnf(c_0_79,plain,
    ( r2_hidden(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | v1_xboole_0(u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_48])).

cnf(c_0_80,negated_conjecture,
    ( ~ v1_xboole_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_81,negated_conjecture,
    ( ~ r2_hidden(k1_yellow_0(esk7_0,k1_xboole_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_56]),c_0_42])])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(k1_yellow_0(esk7_0,X1),esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_71]),c_0_42])]),c_0_80])).

cnf(c_0_83,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_82])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:02:53 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.17/0.39  # AutoSched0-Mode selected heuristic G_E___008_C18_F1_PI_SE_CS_SP_CO_S4S
% 0.17/0.39  # and selection function SelectNewComplexAHPNS.
% 0.17/0.39  #
% 0.17/0.39  # Preprocessing time       : 0.029 s
% 0.17/0.39  
% 0.17/0.39  # Proof found!
% 0.17/0.39  # SZS status Theorem
% 0.17/0.39  # SZS output start CNFRefutation
% 0.17/0.39  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.17/0.39  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.17/0.39  fof(t10_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>~((X2!=k1_xboole_0&![X3]:(m1_subset_1(X3,X1)=>~(r2_hidden(X3,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_subset_1)).
% 0.17/0.39  fof(t8_waybel_7, conjecture, ![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_7)).
% 0.17/0.39  fof(d20_waybel_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v13_waybel_0(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r2_hidden(X3,X2)&r1_orders_2(X1,X3,X4))=>r2_hidden(X4,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_waybel_0)).
% 0.17/0.39  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.17/0.39  fof(t49_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(![X3]:(m1_subset_1(X3,X1)=>r2_hidden(X3,X2))=>X1=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_subset_1)).
% 0.17/0.39  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 0.17/0.39  fof(d9_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_yellow_0(X1,X2)=>(X3=k1_yellow_0(X1,X2)<=>(r2_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)=>r1_orders_2(X1,X3,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_yellow_0)).
% 0.17/0.39  fof(dt_k1_yellow_0, axiom, ![X1, X2]:(l1_orders_2(X1)=>m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 0.17/0.39  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.17/0.39  fof(d9_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 0.17/0.39  fof(d11_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_yellow_0)).
% 0.17/0.39  fof(t42_yellow_0, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>(r1_yellow_0(X1,k1_xboole_0)&r2_yellow_0(X1,u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_yellow_0)).
% 0.17/0.39  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.17/0.39  fof(c_0_15, plain, ![X19, X20, X21]:(~r2_hidden(X19,X20)|~m1_subset_1(X20,k1_zfmisc_1(X21))|~v1_xboole_0(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.17/0.39  fof(c_0_16, plain, ![X5]:m1_subset_1(k2_subset_1(X5),k1_zfmisc_1(X5)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.17/0.39  fof(c_0_17, plain, ![X6, X7]:((m1_subset_1(esk1_2(X6,X7),X6)|X7=k1_xboole_0|~m1_subset_1(X7,k1_zfmisc_1(X6)))&(r2_hidden(esk1_2(X6,X7),X7)|X7=k1_xboole_0|~m1_subset_1(X7,k1_zfmisc_1(X6)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_subset_1])])])])])).
% 0.17/0.39  cnf(c_0_18, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.17/0.39  cnf(c_0_19, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.17/0.39  cnf(c_0_20, plain, (r2_hidden(esk1_2(X1,X2),X2)|X2=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.17/0.39  fof(c_0_21, negated_conjecture, ~(![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2)))))), inference(assume_negation,[status(cth)],[t8_waybel_7])).
% 0.17/0.39  cnf(c_0_22, plain, (~r2_hidden(X1,k2_subset_1(X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.17/0.39  cnf(c_0_23, plain, (k2_subset_1(X1)=k1_xboole_0|r2_hidden(esk1_2(X1,k2_subset_1(X1)),k2_subset_1(X1))), inference(spm,[status(thm)],[c_0_20, c_0_19])).
% 0.17/0.39  fof(c_0_24, plain, ![X36, X37, X38, X39]:((~v13_waybel_0(X37,X36)|(~m1_subset_1(X38,u1_struct_0(X36))|(~m1_subset_1(X39,u1_struct_0(X36))|(~r2_hidden(X38,X37)|~r1_orders_2(X36,X38,X39)|r2_hidden(X39,X37))))|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))|~l1_orders_2(X36))&((m1_subset_1(esk5_2(X36,X37),u1_struct_0(X36))|v13_waybel_0(X37,X36)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))|~l1_orders_2(X36))&((m1_subset_1(esk6_2(X36,X37),u1_struct_0(X36))|v13_waybel_0(X37,X36)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))|~l1_orders_2(X36))&(((r2_hidden(esk5_2(X36,X37),X37)|v13_waybel_0(X37,X36)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))|~l1_orders_2(X36))&(r1_orders_2(X36,esk5_2(X36,X37),esk6_2(X36,X37))|v13_waybel_0(X37,X36)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))|~l1_orders_2(X36)))&(~r2_hidden(esk6_2(X36,X37),X37)|v13_waybel_0(X37,X36)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))|~l1_orders_2(X36)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).
% 0.17/0.39  fof(c_0_25, plain, ![X16, X17, X18]:(~r2_hidden(X16,X17)|~m1_subset_1(X17,k1_zfmisc_1(X18))|m1_subset_1(X16,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.17/0.39  fof(c_0_26, plain, ![X9, X10]:((m1_subset_1(esk2_2(X9,X10),X9)|X9=X10|~m1_subset_1(X10,k1_zfmisc_1(X9)))&(~r2_hidden(esk2_2(X9,X10),X10)|X9=X10|~m1_subset_1(X10,k1_zfmisc_1(X9)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_subset_1])])])])).
% 0.17/0.39  fof(c_0_27, negated_conjecture, ((((((~v2_struct_0(esk7_0)&v3_orders_2(esk7_0))&v4_orders_2(esk7_0))&v5_orders_2(esk7_0))&v1_yellow_0(esk7_0))&l1_orders_2(esk7_0))&((((~v1_xboole_0(esk8_0)&v2_waybel_0(esk8_0,esk7_0))&v13_waybel_0(esk8_0,esk7_0))&m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0))))&((~v1_subset_1(esk8_0,u1_struct_0(esk7_0))|r2_hidden(k3_yellow_0(esk7_0),esk8_0))&(v1_subset_1(esk8_0,u1_struct_0(esk7_0))|~r2_hidden(k3_yellow_0(esk7_0),esk8_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).
% 0.17/0.39  fof(c_0_28, plain, ![X42, X43]:((~v1_subset_1(X43,X42)|X43!=X42|~m1_subset_1(X43,k1_zfmisc_1(X42)))&(X43=X42|v1_subset_1(X43,X42)|~m1_subset_1(X43,k1_zfmisc_1(X42)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.17/0.39  cnf(c_0_29, plain, (k2_subset_1(X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.17/0.39  cnf(c_0_30, plain, (r2_hidden(X4,X1)|~v13_waybel_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~r2_hidden(X3,X1)|~r1_orders_2(X2,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.17/0.39  cnf(c_0_31, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.17/0.39  cnf(c_0_32, plain, (m1_subset_1(esk2_2(X1,X2),X1)|X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.17/0.39  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.17/0.39  cnf(c_0_34, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.17/0.39  fof(c_0_35, plain, ![X28, X29, X30, X31]:(((r2_lattice3(X28,X29,X30)|X30!=k1_yellow_0(X28,X29)|~r1_yellow_0(X28,X29)|~m1_subset_1(X30,u1_struct_0(X28))|~l1_orders_2(X28))&(~m1_subset_1(X31,u1_struct_0(X28))|(~r2_lattice3(X28,X29,X31)|r1_orders_2(X28,X30,X31))|X30!=k1_yellow_0(X28,X29)|~r1_yellow_0(X28,X29)|~m1_subset_1(X30,u1_struct_0(X28))|~l1_orders_2(X28)))&((m1_subset_1(esk4_3(X28,X29,X30),u1_struct_0(X28))|~r2_lattice3(X28,X29,X30)|X30=k1_yellow_0(X28,X29)|~r1_yellow_0(X28,X29)|~m1_subset_1(X30,u1_struct_0(X28))|~l1_orders_2(X28))&((r2_lattice3(X28,X29,esk4_3(X28,X29,X30))|~r2_lattice3(X28,X29,X30)|X30=k1_yellow_0(X28,X29)|~r1_yellow_0(X28,X29)|~m1_subset_1(X30,u1_struct_0(X28))|~l1_orders_2(X28))&(~r1_orders_2(X28,X30,esk4_3(X28,X29,X30))|~r2_lattice3(X28,X29,X30)|X30=k1_yellow_0(X28,X29)|~r1_yellow_0(X28,X29)|~m1_subset_1(X30,u1_struct_0(X28))|~l1_orders_2(X28))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).
% 0.17/0.39  fof(c_0_36, plain, ![X33, X34]:(~l1_orders_2(X33)|m1_subset_1(k1_yellow_0(X33,X34),u1_struct_0(X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).
% 0.17/0.39  cnf(c_0_37, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_19, c_0_29])).
% 0.17/0.39  cnf(c_0_38, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.17/0.39  fof(c_0_39, plain, ![X22, X23, X24, X25]:((~r2_lattice3(X22,X23,X24)|(~m1_subset_1(X25,u1_struct_0(X22))|(~r2_hidden(X25,X23)|r1_orders_2(X22,X25,X24)))|~m1_subset_1(X24,u1_struct_0(X22))|~l1_orders_2(X22))&((m1_subset_1(esk3_3(X22,X23,X24),u1_struct_0(X22))|r2_lattice3(X22,X23,X24)|~m1_subset_1(X24,u1_struct_0(X22))|~l1_orders_2(X22))&((r2_hidden(esk3_3(X22,X23,X24),X23)|r2_lattice3(X22,X23,X24)|~m1_subset_1(X24,u1_struct_0(X22))|~l1_orders_2(X22))&(~r1_orders_2(X22,esk3_3(X22,X23,X24),X24)|r2_lattice3(X22,X23,X24)|~m1_subset_1(X24,u1_struct_0(X22))|~l1_orders_2(X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).
% 0.17/0.39  cnf(c_0_40, plain, (r2_hidden(X1,X2)|~v13_waybel_0(X2,X3)|~r1_orders_2(X3,X4,X1)|~l1_orders_2(X3)|~r2_hidden(X4,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X1,u1_struct_0(X3))), inference(csr,[status(thm)],[c_0_30, c_0_31])).
% 0.17/0.39  cnf(c_0_41, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|m1_subset_1(esk2_2(u1_struct_0(esk7_0),esk8_0),u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.17/0.39  cnf(c_0_42, negated_conjecture, (l1_orders_2(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.17/0.39  cnf(c_0_43, plain, (X1=X2|~r2_hidden(esk2_2(X1,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.17/0.39  cnf(c_0_44, negated_conjecture, (r2_hidden(k3_yellow_0(esk7_0),esk8_0)|~v1_subset_1(esk8_0,u1_struct_0(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.17/0.39  cnf(c_0_45, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|v1_subset_1(esk8_0,u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_34, c_0_33])).
% 0.17/0.39  fof(c_0_46, plain, ![X27]:(~l1_orders_2(X27)|k3_yellow_0(X27)=k1_yellow_0(X27,k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).
% 0.17/0.39  cnf(c_0_47, plain, (r1_orders_2(X2,X4,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|X4!=k1_yellow_0(X2,X3)|~r1_yellow_0(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.17/0.39  cnf(c_0_48, plain, (m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.17/0.39  fof(c_0_49, plain, ![X35]:((r1_yellow_0(X35,k1_xboole_0)|(v2_struct_0(X35)|~v5_orders_2(X35)|~v1_yellow_0(X35)|~l1_orders_2(X35)))&(r2_yellow_0(X35,u1_struct_0(X35))|(v2_struct_0(X35)|~v5_orders_2(X35)|~v1_yellow_0(X35)|~l1_orders_2(X35)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_0])])])])).
% 0.17/0.39  cnf(c_0_50, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.17/0.39  cnf(c_0_51, plain, (r2_hidden(esk3_3(X1,X2,X3),X2)|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.17/0.39  cnf(c_0_52, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|r2_hidden(esk2_2(u1_struct_0(esk7_0),esk8_0),X1)|~v13_waybel_0(X1,esk7_0)|~r1_orders_2(esk7_0,X2,esk2_2(u1_struct_0(esk7_0),esk8_0))|~r2_hidden(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])])).
% 0.17/0.39  cnf(c_0_53, negated_conjecture, (v13_waybel_0(esk8_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.17/0.39  cnf(c_0_54, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|~r2_hidden(esk2_2(u1_struct_0(esk7_0),esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_43, c_0_33])).
% 0.17/0.39  cnf(c_0_55, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|r2_hidden(k3_yellow_0(esk7_0),esk8_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.17/0.39  cnf(c_0_56, plain, (k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.17/0.39  cnf(c_0_57, plain, (r1_orders_2(X1,k1_yellow_0(X1,X2),X3)|~r1_yellow_0(X1,X2)|~r2_lattice3(X1,X2,X3)|~l1_orders_2(X1)|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_47]), c_0_48])).
% 0.17/0.39  cnf(c_0_58, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.17/0.39  cnf(c_0_59, plain, (r1_yellow_0(X1,k1_xboole_0)|v2_struct_0(X1)|~v5_orders_2(X1)|~v1_yellow_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.17/0.39  cnf(c_0_60, negated_conjecture, (v1_yellow_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.17/0.39  cnf(c_0_61, negated_conjecture, (v5_orders_2(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.17/0.39  cnf(c_0_62, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_50]), c_0_38])])).
% 0.17/0.39  cnf(c_0_63, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|r2_lattice3(esk7_0,X1,esk2_2(u1_struct_0(esk7_0),esk8_0))|r2_hidden(esk3_3(esk7_0,X1,esk2_2(u1_struct_0(esk7_0),esk8_0)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_41]), c_0_42])])).
% 0.17/0.39  cnf(c_0_64, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|~r1_orders_2(esk7_0,X1,esk2_2(u1_struct_0(esk7_0),esk8_0))|~r2_hidden(X1,esk8_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_33])]), c_0_54])).
% 0.17/0.39  cnf(c_0_65, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|r2_hidden(k1_yellow_0(esk7_0,k1_xboole_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_42])])).
% 0.17/0.39  cnf(c_0_66, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|r1_orders_2(esk7_0,k1_yellow_0(esk7_0,X1),esk2_2(u1_struct_0(esk7_0),esk8_0))|~r1_yellow_0(esk7_0,X1)|~r2_lattice3(esk7_0,X1,esk2_2(u1_struct_0(esk7_0),esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_41]), c_0_42])])).
% 0.17/0.39  cnf(c_0_67, negated_conjecture, (r1_yellow_0(esk7_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60]), c_0_61]), c_0_42])])).
% 0.17/0.39  cnf(c_0_68, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|r2_lattice3(esk7_0,k1_xboole_0,esk2_2(u1_struct_0(esk7_0),esk8_0))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.17/0.39  cnf(c_0_69, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0|~r1_orders_2(esk7_0,k1_yellow_0(esk7_0,k1_xboole_0),esk2_2(u1_struct_0(esk7_0),esk8_0))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.17/0.39  cnf(c_0_70, plain, (~v1_subset_1(X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.17/0.39  cnf(c_0_71, negated_conjecture, (u1_struct_0(esk7_0)=esk8_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68]), c_0_69])).
% 0.17/0.39  cnf(c_0_72, plain, (~v1_subset_1(X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(X1))), inference(er,[status(thm)],[c_0_70])).
% 0.17/0.39  cnf(c_0_73, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(esk8_0))), inference(rw,[status(thm)],[c_0_33, c_0_71])).
% 0.17/0.39  fof(c_0_74, plain, ![X14, X15]:(~m1_subset_1(X14,X15)|(v1_xboole_0(X15)|r2_hidden(X14,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.17/0.39  cnf(c_0_75, negated_conjecture, (v1_subset_1(esk8_0,u1_struct_0(esk7_0))|~r2_hidden(k3_yellow_0(esk7_0),esk8_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.17/0.39  cnf(c_0_76, negated_conjecture, (~v1_subset_1(esk8_0,esk8_0)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.17/0.39  cnf(c_0_77, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.17/0.39  cnf(c_0_78, negated_conjecture, (~r2_hidden(k3_yellow_0(esk7_0),esk8_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_71]), c_0_76])).
% 0.17/0.39  cnf(c_0_79, plain, (r2_hidden(k1_yellow_0(X1,X2),u1_struct_0(X1))|v1_xboole_0(u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_77, c_0_48])).
% 0.17/0.39  cnf(c_0_80, negated_conjecture, (~v1_xboole_0(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.17/0.39  cnf(c_0_81, negated_conjecture, (~r2_hidden(k1_yellow_0(esk7_0,k1_xboole_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_56]), c_0_42])])).
% 0.17/0.39  cnf(c_0_82, negated_conjecture, (r2_hidden(k1_yellow_0(esk7_0,X1),esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_71]), c_0_42])]), c_0_80])).
% 0.17/0.39  cnf(c_0_83, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_82])]), ['proof']).
% 0.17/0.39  # SZS output end CNFRefutation
% 0.17/0.39  # Proof object total steps             : 84
% 0.17/0.39  # Proof object clause steps            : 54
% 0.17/0.39  # Proof object formula steps           : 30
% 0.17/0.39  # Proof object conjectures             : 31
% 0.17/0.39  # Proof object clause conjectures      : 28
% 0.17/0.39  # Proof object formula conjectures     : 3
% 0.17/0.39  # Proof object initial clauses used    : 25
% 0.17/0.39  # Proof object initial formulas used   : 15
% 0.17/0.39  # Proof object generating inferences   : 23
% 0.17/0.39  # Proof object simplifying inferences  : 33
% 0.17/0.39  # Training examples: 0 positive, 0 negative
% 0.17/0.39  # Parsed axioms                        : 16
% 0.17/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.17/0.39  # Initial clauses                      : 43
% 0.17/0.39  # Removed in clause preprocessing      : 0
% 0.17/0.39  # Initial clauses in saturation        : 43
% 0.17/0.39  # Processed clauses                    : 311
% 0.17/0.39  # ...of these trivial                  : 0
% 0.17/0.39  # ...subsumed                          : 107
% 0.17/0.39  # ...remaining for further processing  : 204
% 0.17/0.39  # Other redundant clauses eliminated   : 3
% 0.17/0.39  # Clauses deleted for lack of memory   : 0
% 0.17/0.39  # Backward-subsumed                    : 3
% 0.17/0.39  # Backward-rewritten                   : 96
% 0.17/0.39  # Generated clauses                    : 620
% 0.17/0.39  # ...of the previous two non-trivial   : 634
% 0.17/0.39  # Contextual simplify-reflections      : 10
% 0.17/0.39  # Paramodulations                      : 617
% 0.17/0.39  # Factorizations                       : 0
% 0.17/0.39  # Equation resolutions                 : 3
% 0.17/0.39  # Propositional unsat checks           : 0
% 0.17/0.39  #    Propositional check models        : 0
% 0.17/0.39  #    Propositional check unsatisfiable : 0
% 0.17/0.39  #    Propositional clauses             : 0
% 0.17/0.39  #    Propositional clauses after purity: 0
% 0.17/0.39  #    Propositional unsat core size     : 0
% 0.17/0.39  #    Propositional preprocessing time  : 0.000
% 0.17/0.39  #    Propositional encoding time       : 0.000
% 0.17/0.39  #    Propositional solver time         : 0.000
% 0.17/0.39  #    Success case prop preproc time    : 0.000
% 0.17/0.39  #    Success case prop encoding time   : 0.000
% 0.17/0.39  #    Success case prop solver time     : 0.000
% 0.17/0.39  # Current number of processed clauses  : 102
% 0.17/0.39  #    Positive orientable unit clauses  : 17
% 0.17/0.39  #    Positive unorientable unit clauses: 0
% 0.17/0.39  #    Negative unit clauses             : 6
% 0.17/0.39  #    Non-unit-clauses                  : 79
% 0.17/0.39  # Current number of unprocessed clauses: 319
% 0.17/0.39  # ...number of literals in the above   : 1507
% 0.17/0.39  # Current number of archived formulas  : 0
% 0.17/0.39  # Current number of archived clauses   : 99
% 0.17/0.39  # Clause-clause subsumption calls (NU) : 3099
% 0.17/0.39  # Rec. Clause-clause subsumption calls : 1016
% 0.17/0.39  # Non-unit clause-clause subsumptions  : 90
% 0.17/0.39  # Unit Clause-clause subsumption calls : 214
% 0.17/0.39  # Rewrite failures with RHS unbound    : 0
% 0.17/0.39  # BW rewrite match attempts            : 5
% 0.17/0.39  # BW rewrite match successes           : 4
% 0.17/0.39  # Condensation attempts                : 313
% 0.17/0.39  # Condensation successes               : 0
% 0.17/0.39  # Termbank termtop insertions          : 18376
% 0.17/0.39  
% 0.17/0.39  # -------------------------------------------------
% 0.17/0.39  # User time                : 0.056 s
% 0.17/0.39  # System time              : 0.005 s
% 0.17/0.39  # Total time               : 0.062 s
% 0.17/0.39  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
