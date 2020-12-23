%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow_0__t43_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:42 EDT 2019

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 130 expanded)
%              Number of clauses        :   33 (  51 expanded)
%              Number of leaves         :   10 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :  289 ( 757 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/yellow_0__t43_yellow_0.p',d9_lattice3)).

fof(d5_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v2_yellow_0(X1)
      <=> ? [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
            & r2_lattice3(X1,u1_struct_0(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t43_yellow_0.p',d5_yellow_0)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t43_yellow_0.p',t1_subset)).

fof(t16_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( r2_yellow_0(X1,X2)
        <=> ? [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
              & r1_lattice3(X1,X2,X3)
              & ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r1_lattice3(X1,X2,X4)
                   => r1_orders_2(X1,X4,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t43_yellow_0.p',t16_yellow_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t43_yellow_0.p',t2_subset)).

fof(t43_yellow_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v2_yellow_0(X1)
        & l1_orders_2(X1) )
     => ( r2_yellow_0(X1,k1_xboole_0)
        & r1_yellow_0(X1,u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t43_yellow_0.p',t43_yellow_0)).

fof(t15_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( r1_yellow_0(X1,X2)
        <=> ? [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
              & r2_lattice3(X1,X2,X3)
              & ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r2_lattice3(X1,X2,X4)
                   => r1_orders_2(X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t43_yellow_0.p',t15_yellow_0)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t43_yellow_0.p',fc2_struct_0)).

fof(t6_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r2_lattice3(X1,k1_xboole_0,X2)
            & r1_lattice3(X1,k1_xboole_0,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t43_yellow_0.p',t6_yellow_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t43_yellow_0.p',dt_l1_orders_2)).

fof(c_0_10,plain,(
    ! [X11,X12,X13,X14] :
      ( ( ~ r2_lattice3(X11,X12,X13)
        | ~ m1_subset_1(X14,u1_struct_0(X11))
        | ~ r2_hidden(X14,X12)
        | r1_orders_2(X11,X14,X13)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ l1_orders_2(X11) )
      & ( m1_subset_1(esk3_3(X11,X12,X13),u1_struct_0(X11))
        | r2_lattice3(X11,X12,X13)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ l1_orders_2(X11) )
      & ( r2_hidden(esk3_3(X11,X12,X13),X12)
        | r2_lattice3(X11,X12,X13)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ l1_orders_2(X11) )
      & ( ~ r1_orders_2(X11,esk3_3(X11,X12,X13),X13)
        | r2_lattice3(X11,X12,X13)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ l1_orders_2(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

fof(c_0_11,plain,(
    ! [X8,X10] :
      ( ( m1_subset_1(esk2_1(X8),u1_struct_0(X8))
        | ~ v2_yellow_0(X8)
        | ~ l1_orders_2(X8) )
      & ( r2_lattice3(X8,u1_struct_0(X8),esk2_1(X8))
        | ~ v2_yellow_0(X8)
        | ~ l1_orders_2(X8) )
      & ( ~ m1_subset_1(X10,u1_struct_0(X8))
        | ~ r2_lattice3(X8,u1_struct_0(X8),X10)
        | v2_yellow_0(X8)
        | ~ l1_orders_2(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_yellow_0])])])])])).

fof(c_0_12,plain,(
    ! [X35,X36] :
      ( ~ r2_hidden(X35,X36)
      | m1_subset_1(X35,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

fof(c_0_13,plain,(
    ! [X28,X29,X31,X32,X33] :
      ( ( m1_subset_1(esk9_2(X28,X29),u1_struct_0(X28))
        | ~ r2_yellow_0(X28,X29)
        | ~ v5_orders_2(X28)
        | ~ l1_orders_2(X28) )
      & ( r1_lattice3(X28,X29,esk9_2(X28,X29))
        | ~ r2_yellow_0(X28,X29)
        | ~ v5_orders_2(X28)
        | ~ l1_orders_2(X28) )
      & ( ~ m1_subset_1(X31,u1_struct_0(X28))
        | ~ r1_lattice3(X28,X29,X31)
        | r1_orders_2(X28,X31,esk9_2(X28,X29))
        | ~ r2_yellow_0(X28,X29)
        | ~ v5_orders_2(X28)
        | ~ l1_orders_2(X28) )
      & ( m1_subset_1(esk10_3(X28,X32,X33),u1_struct_0(X28))
        | ~ m1_subset_1(X33,u1_struct_0(X28))
        | ~ r1_lattice3(X28,X32,X33)
        | r2_yellow_0(X28,X32)
        | ~ v5_orders_2(X28)
        | ~ l1_orders_2(X28) )
      & ( r1_lattice3(X28,X32,esk10_3(X28,X32,X33))
        | ~ m1_subset_1(X33,u1_struct_0(X28))
        | ~ r1_lattice3(X28,X32,X33)
        | r2_yellow_0(X28,X32)
        | ~ v5_orders_2(X28)
        | ~ l1_orders_2(X28) )
      & ( ~ r1_orders_2(X28,esk10_3(X28,X32,X33),X33)
        | ~ m1_subset_1(X33,u1_struct_0(X28))
        | ~ r1_lattice3(X28,X32,X33)
        | r2_yellow_0(X28,X32)
        | ~ v5_orders_2(X28)
        | ~ l1_orders_2(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_yellow_0])])])])])])).

cnf(c_0_14,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r2_lattice3(X1,u1_struct_0(X1),esk2_1(X1))
    | ~ v2_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( m1_subset_1(esk2_1(X1),u1_struct_0(X1))
    | ~ v2_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_18,plain,(
    ! [X37,X38] :
      ( ~ m1_subset_1(X37,X38)
      | v1_xboole_0(X38)
      | r2_hidden(X37,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v5_orders_2(X1)
          & v2_yellow_0(X1)
          & l1_orders_2(X1) )
       => ( r2_yellow_0(X1,k1_xboole_0)
          & r1_yellow_0(X1,u1_struct_0(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t43_yellow_0])).

fof(c_0_20,plain,(
    ! [X21,X22,X24,X25,X26] :
      ( ( m1_subset_1(esk7_2(X21,X22),u1_struct_0(X21))
        | ~ r1_yellow_0(X21,X22)
        | ~ v5_orders_2(X21)
        | ~ l1_orders_2(X21) )
      & ( r2_lattice3(X21,X22,esk7_2(X21,X22))
        | ~ r1_yellow_0(X21,X22)
        | ~ v5_orders_2(X21)
        | ~ l1_orders_2(X21) )
      & ( ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ r2_lattice3(X21,X22,X24)
        | r1_orders_2(X21,esk7_2(X21,X22),X24)
        | ~ r1_yellow_0(X21,X22)
        | ~ v5_orders_2(X21)
        | ~ l1_orders_2(X21) )
      & ( m1_subset_1(esk8_3(X21,X25,X26),u1_struct_0(X21))
        | ~ m1_subset_1(X26,u1_struct_0(X21))
        | ~ r2_lattice3(X21,X25,X26)
        | r1_yellow_0(X21,X25)
        | ~ v5_orders_2(X21)
        | ~ l1_orders_2(X21) )
      & ( r2_lattice3(X21,X25,esk8_3(X21,X25,X26))
        | ~ m1_subset_1(X26,u1_struct_0(X21))
        | ~ r2_lattice3(X21,X25,X26)
        | r1_yellow_0(X21,X25)
        | ~ v5_orders_2(X21)
        | ~ l1_orders_2(X21) )
      & ( ~ r1_orders_2(X21,X26,esk8_3(X21,X25,X26))
        | ~ m1_subset_1(X26,u1_struct_0(X21))
        | ~ r2_lattice3(X21,X25,X26)
        | r1_yellow_0(X21,X25)
        | ~ v5_orders_2(X21)
        | ~ l1_orders_2(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_yellow_0])])])])])])).

cnf(c_0_21,plain,
    ( r2_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,esk10_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( r1_orders_2(X1,X2,esk2_1(X1))
    | ~ r2_hidden(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v2_yellow_0(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17])).

cnf(c_0_23,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( m1_subset_1(esk10_3(X1,X2,X3),u1_struct_0(X1))
    | r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v5_orders_2(esk1_0)
    & v2_yellow_0(esk1_0)
    & l1_orders_2(esk1_0)
    & ( ~ r2_yellow_0(esk1_0,k1_xboole_0)
      | ~ r1_yellow_0(esk1_0,u1_struct_0(esk1_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).

fof(c_0_26,plain,(
    ! [X46] :
      ( v2_struct_0(X46)
      | ~ l1_struct_0(X46)
      | ~ v1_xboole_0(u1_struct_0(X46)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_27,plain,
    ( r2_lattice3(X1,X2,esk8_3(X1,X2,X3))
    | r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( m1_subset_1(esk8_3(X1,X2,X3),u1_struct_0(X1))
    | r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( r2_yellow_0(X1,X2)
    | ~ r1_lattice3(X1,X2,esk2_1(X1))
    | ~ r2_hidden(esk10_3(X1,X2,esk2_1(X1)),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v2_yellow_0(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_17])).

cnf(c_0_30,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | r2_hidden(esk10_3(X1,X2,X3),u1_struct_0(X1))
    | r2_yellow_0(X1,X2)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_31,plain,(
    ! [X40,X41] :
      ( ( r2_lattice3(X40,k1_xboole_0,X41)
        | ~ m1_subset_1(X41,u1_struct_0(X40))
        | ~ l1_orders_2(X40) )
      & ( r1_lattice3(X40,k1_xboole_0,X41)
        | ~ m1_subset_1(X41,u1_struct_0(X40))
        | ~ l1_orders_2(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_yellow_0])])])])).

cnf(c_0_32,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_34,plain,(
    ! [X16] :
      ( ~ l1_orders_2(X16)
      | l1_struct_0(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_35,plain,
    ( r1_yellow_0(X1,X3)
    | ~ r1_orders_2(X1,X2,esk8_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X3,X2)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_36,plain,
    ( r1_orders_2(X1,X2,esk8_3(X1,X3,X4))
    | r1_yellow_0(X1,X3)
    | ~ r2_lattice3(X1,X3,X4)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X2,X3)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_27]),c_0_28])).

cnf(c_0_37,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | r2_yellow_0(X1,X2)
    | ~ r1_lattice3(X1,X2,esk2_1(X1))
    | ~ l1_orders_2(X1)
    | ~ v2_yellow_0(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_17])).

cnf(c_0_38,plain,
    ( r1_lattice3(X1,k1_xboole_0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk1_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_42,plain,
    ( r1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X3,X2)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | r2_yellow_0(X1,k1_xboole_0)
    | ~ l1_orders_2(X1)
    | ~ v2_yellow_0(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_17])).

cnf(c_0_44,negated_conjecture,
    ( v2_yellow_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_45,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_46,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])])).

cnf(c_0_47,plain,
    ( r1_yellow_0(X1,u1_struct_0(X1))
    | ~ r2_hidden(esk2_1(X1),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v2_yellow_0(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_15]),c_0_16])).

cnf(c_0_48,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | r2_hidden(esk2_1(X1),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v2_yellow_0(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_17])).

cnf(c_0_49,negated_conjecture,
    ( ~ r2_yellow_0(esk1_0,k1_xboole_0)
    | ~ r1_yellow_0(esk1_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_50,negated_conjecture,
    ( r2_yellow_0(esk1_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_41]),c_0_45])]),c_0_46])).

cnf(c_0_51,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | r1_yellow_0(X1,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v2_yellow_0(X1)
    | ~ v5_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( ~ r1_yellow_0(esk1_0,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50])])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_44]),c_0_41]),c_0_45])]),c_0_46]),c_0_52]),
    [proof]).
%------------------------------------------------------------------------------
