%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:25 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 443 expanded)
%              Number of clauses        :   55 ( 184 expanded)
%              Number of leaves         :   16 ( 107 expanded)
%              Depth                    :   12
%              Number of atoms          :  333 (2653 expanded)
%              Number of equality atoms :   39 ( 159 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   30 (   2 average)
%              Maximal term depth       :    3 (   1 average)

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

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

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

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(dt_k1_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

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

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(t6_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r2_lattice3(X1,k1_xboole_0,X2)
            & r1_lattice3(X1,k1_xboole_0,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_0)).

fof(t42_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v1_yellow_0(X1)
        & l1_orders_2(X1) )
     => ( r1_yellow_0(X1,k1_xboole_0)
        & r2_yellow_0(X1,u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).

fof(d11_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(fc14_subset_1,axiom,(
    ! [X1] : ~ v1_subset_1(k2_subset_1(X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

fof(c_0_16,negated_conjecture,(
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

fof(c_0_17,plain,(
    ! [X10] : m1_subset_1(k2_subset_1(X10),k1_zfmisc_1(X10)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_18,plain,(
    ! [X9] : k2_subset_1(X9) = X9 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_19,plain,(
    ! [X11,X12,X13] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | ~ r2_hidden(X13,X12)
      | r2_hidden(X13,X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_20,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).

fof(c_0_21,plain,(
    ! [X14,X15,X16] :
      ( ( m1_subset_1(esk2_3(X14,X15,X16),X14)
        | X15 = X16
        | ~ m1_subset_1(X16,k1_zfmisc_1(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(X14)) )
      & ( ~ r2_hidden(esk2_3(X14,X15,X16),X15)
        | ~ r2_hidden(esk2_3(X14,X15,X16),X16)
        | X15 = X16
        | ~ m1_subset_1(X16,k1_zfmisc_1(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(X14)) )
      & ( r2_hidden(esk2_3(X14,X15,X16),X15)
        | r2_hidden(esk2_3(X14,X15,X16),X16)
        | X15 = X16
        | ~ m1_subset_1(X16,k1_zfmisc_1(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(X14)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_subset_1])])])])])).

cnf(c_0_22,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_27,plain,(
    ! [X30,X31] :
      ( ~ l1_orders_2(X30)
      | m1_subset_1(k1_yellow_0(X30,X31),u1_struct_0(X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

cnf(c_0_28,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),X1)
    | X2 = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk6_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_33,plain,(
    ! [X25,X26,X27,X28] :
      ( ( r2_lattice3(X25,X26,X27)
        | X27 != k1_yellow_0(X25,X26)
        | ~ r1_yellow_0(X25,X26)
        | ~ m1_subset_1(X27,u1_struct_0(X25))
        | ~ l1_orders_2(X25) )
      & ( ~ m1_subset_1(X28,u1_struct_0(X25))
        | ~ r2_lattice3(X25,X26,X28)
        | r1_orders_2(X25,X27,X28)
        | X27 != k1_yellow_0(X25,X26)
        | ~ r1_yellow_0(X25,X26)
        | ~ m1_subset_1(X27,u1_struct_0(X25))
        | ~ l1_orders_2(X25) )
      & ( m1_subset_1(esk3_3(X25,X26,X27),u1_struct_0(X25))
        | ~ r2_lattice3(X25,X26,X27)
        | X27 = k1_yellow_0(X25,X26)
        | ~ r1_yellow_0(X25,X26)
        | ~ m1_subset_1(X27,u1_struct_0(X25))
        | ~ l1_orders_2(X25) )
      & ( r2_lattice3(X25,X26,esk3_3(X25,X26,X27))
        | ~ r2_lattice3(X25,X26,X27)
        | X27 = k1_yellow_0(X25,X26)
        | ~ r1_yellow_0(X25,X26)
        | ~ m1_subset_1(X27,u1_struct_0(X25))
        | ~ l1_orders_2(X25) )
      & ( ~ r1_orders_2(X25,X27,esk3_3(X25,X26,X27))
        | ~ r2_lattice3(X25,X26,X27)
        | X27 = k1_yellow_0(X25,X26)
        | ~ r1_yellow_0(X25,X26)
        | ~ m1_subset_1(X27,u1_struct_0(X25))
        | ~ l1_orders_2(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).

cnf(c_0_34,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( l1_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_36,plain,(
    ! [X35,X36,X37,X38] :
      ( ( ~ v13_waybel_0(X36,X35)
        | ~ m1_subset_1(X37,u1_struct_0(X35))
        | ~ m1_subset_1(X38,u1_struct_0(X35))
        | ~ r2_hidden(X37,X36)
        | ~ r1_orders_2(X35,X37,X38)
        | r2_hidden(X38,X36)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ l1_orders_2(X35) )
      & ( m1_subset_1(esk4_2(X35,X36),u1_struct_0(X35))
        | v13_waybel_0(X36,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ l1_orders_2(X35) )
      & ( m1_subset_1(esk5_2(X35,X36),u1_struct_0(X35))
        | v13_waybel_0(X36,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ l1_orders_2(X35) )
      & ( r2_hidden(esk4_2(X35,X36),X36)
        | v13_waybel_0(X36,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ l1_orders_2(X35) )
      & ( r1_orders_2(X35,esk4_2(X35,X36),esk5_2(X35,X36))
        | v13_waybel_0(X36,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ l1_orders_2(X35) )
      & ( ~ r2_hidden(esk5_2(X35,X36),X36)
        | v13_waybel_0(X36,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ l1_orders_2(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).

fof(c_0_37,plain,(
    ! [X21,X22,X23] :
      ( ~ r2_hidden(X21,X22)
      | ~ m1_subset_1(X22,k1_zfmisc_1(X23))
      | m1_subset_1(X21,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_38,plain,(
    ! [X19,X20] :
      ( ~ m1_subset_1(X19,X20)
      | v1_xboole_0(X20)
      | r2_hidden(X19,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_39,plain,
    ( X1 = X2
    | m1_subset_1(esk2_3(X2,X1,X2),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_40,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk1_1(esk7_0),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_42,plain,
    ( r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | X4 != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(k1_yellow_0(esk6_0,X1),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

fof(c_0_44,plain,(
    ! [X33,X34] :
      ( ( r2_lattice3(X33,k1_xboole_0,X34)
        | ~ m1_subset_1(X34,u1_struct_0(X33))
        | ~ l1_orders_2(X33) )
      & ( r1_lattice3(X33,k1_xboole_0,X34)
        | ~ m1_subset_1(X34,u1_struct_0(X33))
        | ~ l1_orders_2(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_yellow_0])])])])).

fof(c_0_45,plain,(
    ! [X32] :
      ( ( r1_yellow_0(X32,k1_xboole_0)
        | v2_struct_0(X32)
        | ~ v5_orders_2(X32)
        | ~ v1_yellow_0(X32)
        | ~ l1_orders_2(X32) )
      & ( r2_yellow_0(X32,u1_struct_0(X32))
        | v2_struct_0(X32)
        | ~ v5_orders_2(X32)
        | ~ v1_yellow_0(X32)
        | ~ l1_orders_2(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_0])])])])).

fof(c_0_46,plain,(
    ! [X24] :
      ( ~ l1_orders_2(X24)
      | k3_yellow_0(X24) = k1_yellow_0(X24,k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).

cnf(c_0_47,plain,
    ( r2_hidden(X4,X1)
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(X3,X1)
    | ~ r1_orders_2(X2,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_48,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_49,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_50,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | m1_subset_1(esk2_3(u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk6_0)),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_25])).

cnf(c_0_51,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_52,negated_conjecture,
    ( r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X1),X2)
    | k1_yellow_0(esk6_0,X1) != k1_yellow_0(esk6_0,X3)
    | ~ r2_lattice3(esk6_0,X3,X2)
    | ~ r1_yellow_0(esk6_0,X3)
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_35])])).

cnf(c_0_53,plain,
    ( r2_lattice3(X1,k1_xboole_0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_54,plain,
    ( r1_yellow_0(X1,k1_xboole_0)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_55,negated_conjecture,
    ( v1_yellow_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_56,negated_conjecture,
    ( v5_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_57,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_58,plain,
    ( k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_59,plain,(
    ! [X41,X42] :
      ( ( ~ v1_subset_1(X42,X41)
        | X42 != X41
        | ~ m1_subset_1(X42,k1_zfmisc_1(X41)) )
      & ( X42 = X41
        | v1_subset_1(X42,X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(X41)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,X2)
    | ~ v13_waybel_0(X2,X3)
    | ~ r1_orders_2(X3,X4,X1)
    | ~ l1_orders_2(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ r2_hidden(X4,X2) ),
    inference(csr,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_61,negated_conjecture,
    ( v13_waybel_0(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_62,plain,
    ( X2 = X3
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_63,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | r2_hidden(esk2_3(u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk6_0)),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_64,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X1),esk2_3(u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk6_0)))
    | k1_yellow_0(esk6_0,X1) != k1_yellow_0(esk6_0,X2)
    | ~ r2_lattice3(esk6_0,X2,esk2_3(u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk6_0)))
    | ~ r1_yellow_0(esk6_0,X2) ),
    inference(spm,[status(thm)],[c_0_52,c_0_50])).

cnf(c_0_65,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | r2_lattice3(esk6_0,k1_xboole_0,esk2_3(u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_50]),c_0_35])])).

cnf(c_0_66,negated_conjecture,
    ( r1_yellow_0(esk6_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_35])]),c_0_57])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(k3_yellow_0(esk6_0),esk7_0)
    | ~ v1_subset_1(esk7_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_68,negated_conjecture,
    ( k3_yellow_0(esk6_0) = k1_yellow_0(esk6_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_35])).

cnf(c_0_69,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r1_orders_2(esk6_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ r2_hidden(X2,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_25]),c_0_61]),c_0_35])])).

cnf(c_0_71,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | ~ r2_hidden(esk2_3(u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk6_0)),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_29]),c_0_25])])).

cnf(c_0_72,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X1),esk2_3(u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk6_0)))
    | k1_yellow_0(esk6_0,X1) != k1_yellow_0(esk6_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66])])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(k1_yellow_0(esk6_0,k1_xboole_0),esk7_0)
    | ~ v1_subset_1(esk7_0,u1_struct_0(esk6_0)) ),
    inference(rw,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | v1_subset_1(esk7_0,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_25])).

fof(c_0_75,plain,(
    ! [X18] : ~ v1_subset_1(k2_subset_1(X18),X18) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc14_subset_1])])).

cnf(c_0_76,negated_conjecture,
    ( v1_subset_1(esk7_0,u1_struct_0(esk6_0))
    | ~ r2_hidden(k3_yellow_0(esk6_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_77,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | ~ r1_orders_2(esk6_0,X1,esk2_3(u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk6_0)))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_50]),c_0_71])).

cnf(c_0_78,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,k1_xboole_0),esk2_3(u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk6_0))) ),
    inference(er,[status(thm)],[c_0_72])).

cnf(c_0_79,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0
    | r2_hidden(k1_yellow_0(esk6_0,k1_xboole_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_80,plain,
    ( ~ v1_subset_1(k2_subset_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_81,negated_conjecture,
    ( v1_subset_1(esk7_0,u1_struct_0(esk6_0))
    | ~ r2_hidden(k1_yellow_0(esk6_0,k1_xboole_0),esk7_0) ),
    inference(rw,[status(thm)],[c_0_76,c_0_68])).

cnf(c_0_82,negated_conjecture,
    ( u1_struct_0(esk6_0) = esk7_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79])).

cnf(c_0_83,plain,
    ( ~ v1_subset_1(X1,X1) ),
    inference(rw,[status(thm)],[c_0_80,c_0_23])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(k1_yellow_0(esk6_0,X1),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_43]),c_0_51])).

cnf(c_0_85,negated_conjecture,
    ( ~ r2_hidden(k1_yellow_0(esk6_0,k1_xboole_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_82]),c_0_83])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(k1_yellow_0(esk6_0,X1),esk7_0) ),
    inference(rw,[status(thm)],[c_0_84,c_0_82])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_86])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:21:06 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.45  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0S
% 0.20/0.45  # and selection function SelectComplexG.
% 0.20/0.45  #
% 0.20/0.45  # Preprocessing time       : 0.029 s
% 0.20/0.45  # Presaturation interreduction done
% 0.20/0.45  
% 0.20/0.45  # Proof found!
% 0.20/0.45  # SZS status Theorem
% 0.20/0.45  # SZS output start CNFRefutation
% 0.20/0.45  fof(t8_waybel_7, conjecture, ![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_7)).
% 0.20/0.45  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.20/0.45  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.20/0.45  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.20/0.45  fof(t8_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,X2)<=>r2_hidden(X4,X3)))=>X2=X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_subset_1)).
% 0.20/0.45  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.45  fof(dt_k1_yellow_0, axiom, ![X1, X2]:(l1_orders_2(X1)=>m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 0.20/0.45  fof(d9_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_yellow_0(X1,X2)=>(X3=k1_yellow_0(X1,X2)<=>(r2_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)=>r1_orders_2(X1,X3,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_yellow_0)).
% 0.20/0.45  fof(d20_waybel_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v13_waybel_0(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r2_hidden(X3,X2)&r1_orders_2(X1,X3,X4))=>r2_hidden(X4,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_waybel_0)).
% 0.20/0.45  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.20/0.45  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.20/0.45  fof(t6_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(r2_lattice3(X1,k1_xboole_0,X2)&r1_lattice3(X1,k1_xboole_0,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_yellow_0)).
% 0.20/0.45  fof(t42_yellow_0, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>(r1_yellow_0(X1,k1_xboole_0)&r2_yellow_0(X1,u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_yellow_0)).
% 0.20/0.45  fof(d11_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_yellow_0)).
% 0.20/0.45  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 0.20/0.45  fof(fc14_subset_1, axiom, ![X1]:~(v1_subset_1(k2_subset_1(X1),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_subset_1)).
% 0.20/0.45  fof(c_0_16, negated_conjecture, ~(![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2)))))), inference(assume_negation,[status(cth)],[t8_waybel_7])).
% 0.20/0.45  fof(c_0_17, plain, ![X10]:m1_subset_1(k2_subset_1(X10),k1_zfmisc_1(X10)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.20/0.45  fof(c_0_18, plain, ![X9]:k2_subset_1(X9)=X9, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.20/0.45  fof(c_0_19, plain, ![X11, X12, X13]:(~m1_subset_1(X12,k1_zfmisc_1(X11))|(~r2_hidden(X13,X12)|r2_hidden(X13,X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.20/0.45  fof(c_0_20, negated_conjecture, ((((((~v2_struct_0(esk6_0)&v3_orders_2(esk6_0))&v4_orders_2(esk6_0))&v5_orders_2(esk6_0))&v1_yellow_0(esk6_0))&l1_orders_2(esk6_0))&((((~v1_xboole_0(esk7_0)&v2_waybel_0(esk7_0,esk6_0))&v13_waybel_0(esk7_0,esk6_0))&m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0))))&((~v1_subset_1(esk7_0,u1_struct_0(esk6_0))|r2_hidden(k3_yellow_0(esk6_0),esk7_0))&(v1_subset_1(esk7_0,u1_struct_0(esk6_0))|~r2_hidden(k3_yellow_0(esk6_0),esk7_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).
% 0.20/0.45  fof(c_0_21, plain, ![X14, X15, X16]:((m1_subset_1(esk2_3(X14,X15,X16),X14)|X15=X16|~m1_subset_1(X16,k1_zfmisc_1(X14))|~m1_subset_1(X15,k1_zfmisc_1(X14)))&((~r2_hidden(esk2_3(X14,X15,X16),X15)|~r2_hidden(esk2_3(X14,X15,X16),X16)|X15=X16|~m1_subset_1(X16,k1_zfmisc_1(X14))|~m1_subset_1(X15,k1_zfmisc_1(X14)))&(r2_hidden(esk2_3(X14,X15,X16),X15)|r2_hidden(esk2_3(X14,X15,X16),X16)|X15=X16|~m1_subset_1(X16,k1_zfmisc_1(X14))|~m1_subset_1(X15,k1_zfmisc_1(X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_subset_1])])])])])).
% 0.20/0.45  cnf(c_0_22, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.45  cnf(c_0_23, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.45  cnf(c_0_24, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.45  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.45  fof(c_0_26, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.45  fof(c_0_27, plain, ![X30, X31]:(~l1_orders_2(X30)|m1_subset_1(k1_yellow_0(X30,X31),u1_struct_0(X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).
% 0.20/0.45  cnf(c_0_28, plain, (m1_subset_1(esk2_3(X1,X2,X3),X1)|X2=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.45  cnf(c_0_29, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.45  cnf(c_0_30, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk6_0))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.45  cnf(c_0_31, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.45  cnf(c_0_32, negated_conjecture, (~v1_xboole_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.45  fof(c_0_33, plain, ![X25, X26, X27, X28]:(((r2_lattice3(X25,X26,X27)|X27!=k1_yellow_0(X25,X26)|~r1_yellow_0(X25,X26)|~m1_subset_1(X27,u1_struct_0(X25))|~l1_orders_2(X25))&(~m1_subset_1(X28,u1_struct_0(X25))|(~r2_lattice3(X25,X26,X28)|r1_orders_2(X25,X27,X28))|X27!=k1_yellow_0(X25,X26)|~r1_yellow_0(X25,X26)|~m1_subset_1(X27,u1_struct_0(X25))|~l1_orders_2(X25)))&((m1_subset_1(esk3_3(X25,X26,X27),u1_struct_0(X25))|~r2_lattice3(X25,X26,X27)|X27=k1_yellow_0(X25,X26)|~r1_yellow_0(X25,X26)|~m1_subset_1(X27,u1_struct_0(X25))|~l1_orders_2(X25))&((r2_lattice3(X25,X26,esk3_3(X25,X26,X27))|~r2_lattice3(X25,X26,X27)|X27=k1_yellow_0(X25,X26)|~r1_yellow_0(X25,X26)|~m1_subset_1(X27,u1_struct_0(X25))|~l1_orders_2(X25))&(~r1_orders_2(X25,X27,esk3_3(X25,X26,X27))|~r2_lattice3(X25,X26,X27)|X27=k1_yellow_0(X25,X26)|~r1_yellow_0(X25,X26)|~m1_subset_1(X27,u1_struct_0(X25))|~l1_orders_2(X25))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).
% 0.20/0.45  cnf(c_0_34, plain, (m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.45  cnf(c_0_35, negated_conjecture, (l1_orders_2(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.45  fof(c_0_36, plain, ![X35, X36, X37, X38]:((~v13_waybel_0(X36,X35)|(~m1_subset_1(X37,u1_struct_0(X35))|(~m1_subset_1(X38,u1_struct_0(X35))|(~r2_hidden(X37,X36)|~r1_orders_2(X35,X37,X38)|r2_hidden(X38,X36))))|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))|~l1_orders_2(X35))&((m1_subset_1(esk4_2(X35,X36),u1_struct_0(X35))|v13_waybel_0(X36,X35)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))|~l1_orders_2(X35))&((m1_subset_1(esk5_2(X35,X36),u1_struct_0(X35))|v13_waybel_0(X36,X35)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))|~l1_orders_2(X35))&(((r2_hidden(esk4_2(X35,X36),X36)|v13_waybel_0(X36,X35)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))|~l1_orders_2(X35))&(r1_orders_2(X35,esk4_2(X35,X36),esk5_2(X35,X36))|v13_waybel_0(X36,X35)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))|~l1_orders_2(X35)))&(~r2_hidden(esk5_2(X35,X36),X36)|v13_waybel_0(X36,X35)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))|~l1_orders_2(X35)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).
% 0.20/0.45  fof(c_0_37, plain, ![X21, X22, X23]:(~r2_hidden(X21,X22)|~m1_subset_1(X22,k1_zfmisc_1(X23))|m1_subset_1(X21,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.20/0.45  fof(c_0_38, plain, ![X19, X20]:(~m1_subset_1(X19,X20)|(v1_xboole_0(X20)|r2_hidden(X19,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.20/0.45  cnf(c_0_39, plain, (X1=X2|m1_subset_1(esk2_3(X2,X1,X2),X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.45  cnf(c_0_40, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.45  cnf(c_0_41, negated_conjecture, (r2_hidden(esk1_1(esk7_0),u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 0.20/0.45  cnf(c_0_42, plain, (r1_orders_2(X2,X4,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|X4!=k1_yellow_0(X2,X3)|~r1_yellow_0(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.45  cnf(c_0_43, negated_conjecture, (m1_subset_1(k1_yellow_0(esk6_0,X1),u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.45  fof(c_0_44, plain, ![X33, X34]:((r2_lattice3(X33,k1_xboole_0,X34)|~m1_subset_1(X34,u1_struct_0(X33))|~l1_orders_2(X33))&(r1_lattice3(X33,k1_xboole_0,X34)|~m1_subset_1(X34,u1_struct_0(X33))|~l1_orders_2(X33))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_yellow_0])])])])).
% 0.20/0.45  fof(c_0_45, plain, ![X32]:((r1_yellow_0(X32,k1_xboole_0)|(v2_struct_0(X32)|~v5_orders_2(X32)|~v1_yellow_0(X32)|~l1_orders_2(X32)))&(r2_yellow_0(X32,u1_struct_0(X32))|(v2_struct_0(X32)|~v5_orders_2(X32)|~v1_yellow_0(X32)|~l1_orders_2(X32)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_0])])])])).
% 0.20/0.45  fof(c_0_46, plain, ![X24]:(~l1_orders_2(X24)|k3_yellow_0(X24)=k1_yellow_0(X24,k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).
% 0.20/0.45  cnf(c_0_47, plain, (r2_hidden(X4,X1)|~v13_waybel_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~r2_hidden(X3,X1)|~r1_orders_2(X2,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.45  cnf(c_0_48, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.45  cnf(c_0_49, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.45  cnf(c_0_50, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|m1_subset_1(esk2_3(u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk6_0)),u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_39, c_0_25])).
% 0.20/0.45  cnf(c_0_51, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.45  cnf(c_0_52, negated_conjecture, (r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X1),X2)|k1_yellow_0(esk6_0,X1)!=k1_yellow_0(esk6_0,X3)|~r2_lattice3(esk6_0,X3,X2)|~r1_yellow_0(esk6_0,X3)|~m1_subset_1(X2,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_35])])).
% 0.20/0.45  cnf(c_0_53, plain, (r2_lattice3(X1,k1_xboole_0,X2)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.45  cnf(c_0_54, plain, (r1_yellow_0(X1,k1_xboole_0)|v2_struct_0(X1)|~v5_orders_2(X1)|~v1_yellow_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.45  cnf(c_0_55, negated_conjecture, (v1_yellow_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.45  cnf(c_0_56, negated_conjecture, (v5_orders_2(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.45  cnf(c_0_57, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.45  cnf(c_0_58, plain, (k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.45  fof(c_0_59, plain, ![X41, X42]:((~v1_subset_1(X42,X41)|X42!=X41|~m1_subset_1(X42,k1_zfmisc_1(X41)))&(X42=X41|v1_subset_1(X42,X41)|~m1_subset_1(X42,k1_zfmisc_1(X41)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.20/0.45  cnf(c_0_60, plain, (r2_hidden(X1,X2)|~v13_waybel_0(X2,X3)|~r1_orders_2(X3,X4,X1)|~l1_orders_2(X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X1,u1_struct_0(X3))|~r2_hidden(X4,X2)), inference(csr,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.45  cnf(c_0_61, negated_conjecture, (v13_waybel_0(esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.45  cnf(c_0_62, plain, (X2=X3|~r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.45  cnf(c_0_63, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|r2_hidden(esk2_3(u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk6_0)),u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])).
% 0.20/0.45  cnf(c_0_64, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X1),esk2_3(u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk6_0)))|k1_yellow_0(esk6_0,X1)!=k1_yellow_0(esk6_0,X2)|~r2_lattice3(esk6_0,X2,esk2_3(u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk6_0)))|~r1_yellow_0(esk6_0,X2)), inference(spm,[status(thm)],[c_0_52, c_0_50])).
% 0.20/0.45  cnf(c_0_65, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|r2_lattice3(esk6_0,k1_xboole_0,esk2_3(u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_50]), c_0_35])])).
% 0.20/0.45  cnf(c_0_66, negated_conjecture, (r1_yellow_0(esk6_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), c_0_35])]), c_0_57])).
% 0.20/0.45  cnf(c_0_67, negated_conjecture, (r2_hidden(k3_yellow_0(esk6_0),esk7_0)|~v1_subset_1(esk7_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.45  cnf(c_0_68, negated_conjecture, (k3_yellow_0(esk6_0)=k1_yellow_0(esk6_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_58, c_0_35])).
% 0.20/0.45  cnf(c_0_69, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.45  cnf(c_0_70, negated_conjecture, (r2_hidden(X1,esk7_0)|~r1_orders_2(esk6_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))|~r2_hidden(X2,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_25]), c_0_61]), c_0_35])])).
% 0.20/0.45  cnf(c_0_71, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|~r2_hidden(esk2_3(u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk6_0)),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_29]), c_0_25])])).
% 0.20/0.45  cnf(c_0_72, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X1),esk2_3(u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk6_0)))|k1_yellow_0(esk6_0,X1)!=k1_yellow_0(esk6_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66])])).
% 0.20/0.45  cnf(c_0_73, negated_conjecture, (r2_hidden(k1_yellow_0(esk6_0,k1_xboole_0),esk7_0)|~v1_subset_1(esk7_0,u1_struct_0(esk6_0))), inference(rw,[status(thm)],[c_0_67, c_0_68])).
% 0.20/0.45  cnf(c_0_74, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|v1_subset_1(esk7_0,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_69, c_0_25])).
% 0.20/0.45  fof(c_0_75, plain, ![X18]:~v1_subset_1(k2_subset_1(X18),X18), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc14_subset_1])])).
% 0.20/0.45  cnf(c_0_76, negated_conjecture, (v1_subset_1(esk7_0,u1_struct_0(esk6_0))|~r2_hidden(k3_yellow_0(esk6_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.45  cnf(c_0_77, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|~r1_orders_2(esk6_0,X1,esk2_3(u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk6_0)))|~r2_hidden(X1,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_50]), c_0_71])).
% 0.20/0.45  cnf(c_0_78, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|r1_orders_2(esk6_0,k1_yellow_0(esk6_0,k1_xboole_0),esk2_3(u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk6_0)))), inference(er,[status(thm)],[c_0_72])).
% 0.20/0.45  cnf(c_0_79, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0|r2_hidden(k1_yellow_0(esk6_0,k1_xboole_0),esk7_0)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.20/0.45  cnf(c_0_80, plain, (~v1_subset_1(k2_subset_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.20/0.45  cnf(c_0_81, negated_conjecture, (v1_subset_1(esk7_0,u1_struct_0(esk6_0))|~r2_hidden(k1_yellow_0(esk6_0,k1_xboole_0),esk7_0)), inference(rw,[status(thm)],[c_0_76, c_0_68])).
% 0.20/0.45  cnf(c_0_82, negated_conjecture, (u1_struct_0(esk6_0)=esk7_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_79])).
% 0.20/0.45  cnf(c_0_83, plain, (~v1_subset_1(X1,X1)), inference(rw,[status(thm)],[c_0_80, c_0_23])).
% 0.20/0.45  cnf(c_0_84, negated_conjecture, (r2_hidden(k1_yellow_0(esk6_0,X1),u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_43]), c_0_51])).
% 0.20/0.45  cnf(c_0_85, negated_conjecture, (~r2_hidden(k1_yellow_0(esk6_0,k1_xboole_0),esk7_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_82]), c_0_83])).
% 0.20/0.45  cnf(c_0_86, negated_conjecture, (r2_hidden(k1_yellow_0(esk6_0,X1),esk7_0)), inference(rw,[status(thm)],[c_0_84, c_0_82])).
% 0.20/0.45  cnf(c_0_87, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_86])]), ['proof']).
% 0.20/0.45  # SZS output end CNFRefutation
% 0.20/0.45  # Proof object total steps             : 88
% 0.20/0.45  # Proof object clause steps            : 55
% 0.20/0.45  # Proof object formula steps           : 33
% 0.20/0.45  # Proof object conjectures             : 37
% 0.20/0.45  # Proof object clause conjectures      : 34
% 0.20/0.45  # Proof object formula conjectures     : 3
% 0.20/0.45  # Proof object initial clauses used    : 26
% 0.20/0.45  # Proof object initial formulas used   : 16
% 0.20/0.45  # Proof object generating inferences   : 21
% 0.20/0.45  # Proof object simplifying inferences  : 31
% 0.20/0.45  # Training examples: 0 positive, 0 negative
% 0.20/0.45  # Parsed axioms                        : 16
% 0.20/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.46  # Initial clauses                      : 42
% 0.20/0.46  # Removed in clause preprocessing      : 1
% 0.20/0.46  # Initial clauses in saturation        : 41
% 0.20/0.46  # Processed clauses                    : 628
% 0.20/0.46  # ...of these trivial                  : 3
% 0.20/0.46  # ...subsumed                          : 195
% 0.20/0.46  # ...remaining for further processing  : 430
% 0.20/0.46  # Other redundant clauses eliminated   : 1
% 0.20/0.46  # Clauses deleted for lack of memory   : 0
% 0.20/0.46  # Backward-subsumed                    : 3
% 0.20/0.46  # Backward-rewritten                   : 222
% 0.20/0.46  # Generated clauses                    : 900
% 0.20/0.46  # ...of the previous two non-trivial   : 997
% 0.20/0.46  # Contextual simplify-reflections      : 7
% 0.20/0.46  # Paramodulations                      : 891
% 0.20/0.46  # Factorizations                       : 0
% 0.20/0.46  # Equation resolutions                 : 9
% 0.20/0.46  # Propositional unsat checks           : 0
% 0.20/0.46  #    Propositional check models        : 0
% 0.20/0.46  #    Propositional check unsatisfiable : 0
% 0.20/0.46  #    Propositional clauses             : 0
% 0.20/0.46  #    Propositional clauses after purity: 0
% 0.20/0.46  #    Propositional unsat core size     : 0
% 0.20/0.46  #    Propositional preprocessing time  : 0.000
% 0.20/0.46  #    Propositional encoding time       : 0.000
% 0.20/0.46  #    Propositional solver time         : 0.000
% 0.20/0.46  #    Success case prop preproc time    : 0.000
% 0.20/0.46  #    Success case prop encoding time   : 0.000
% 0.20/0.46  #    Success case prop solver time     : 0.000
% 0.20/0.46  # Current number of processed clauses  : 164
% 0.20/0.46  #    Positive orientable unit clauses  : 20
% 0.20/0.46  #    Positive unorientable unit clauses: 0
% 0.20/0.46  #    Negative unit clauses             : 3
% 0.20/0.46  #    Non-unit-clauses                  : 141
% 0.20/0.46  # Current number of unprocessed clauses: 435
% 0.20/0.46  # ...number of literals in the above   : 2278
% 0.20/0.46  # Current number of archived formulas  : 0
% 0.20/0.46  # Current number of archived clauses   : 266
% 0.20/0.46  # Clause-clause subsumption calls (NU) : 14309
% 0.20/0.46  # Rec. Clause-clause subsumption calls : 1836
% 0.20/0.46  # Non-unit clause-clause subsumptions  : 173
% 0.20/0.46  # Unit Clause-clause subsumption calls : 273
% 0.20/0.46  # Rewrite failures with RHS unbound    : 0
% 0.20/0.46  # BW rewrite match attempts            : 25
% 0.20/0.46  # BW rewrite match successes           : 7
% 0.20/0.46  # Condensation attempts                : 0
% 0.20/0.46  # Condensation successes               : 0
% 0.20/0.46  # Termbank termtop insertions          : 33394
% 0.20/0.46  
% 0.20/0.46  # -------------------------------------------------
% 0.20/0.46  # User time                : 0.102 s
% 0.20/0.46  # System time              : 0.007 s
% 0.20/0.46  # Total time               : 0.109 s
% 0.20/0.46  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
