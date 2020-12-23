%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow_0__t17_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:37 EDT 2019

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 152 expanded)
%              Number of clauses        :   46 (  62 expanded)
%              Number of leaves         :    7 (  41 expanded)
%              Depth                    :   13
%              Number of atoms          :  444 (1501 expanded)
%              Number of equality atoms :    5 (  14 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal clause size      :   32 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d8_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r1_lattice3(X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r1_orders_2(X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t17_yellow_0.p',d8_lattice3)).

fof(fraenkel_a_2_0_yellow_0,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & v5_orders_2(X2)
        & v3_lattice3(X2)
        & l1_orders_2(X2) )
     => ( r2_hidden(X1,a_2_0_yellow_0(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,u1_struct_0(X2))
            & X1 = X4
            & r1_lattice3(X2,X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t17_yellow_0.p',fraenkel_a_2_0_yellow_0)).

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
    file('/export/starexec/sandbox/benchmark/yellow_0__t17_yellow_0.p',d9_lattice3)).

fof(d12_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v3_lattice3(X1)
      <=> ! [X2] :
          ? [X3] :
            ( m1_subset_1(X3,u1_struct_0(X1))
            & r2_lattice3(X1,X2,X3)
            & ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_lattice3(X1,X2,X4)
                 => r1_orders_2(X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t17_yellow_0.p',d12_lattice3)).

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
    file('/export/starexec/sandbox/benchmark/yellow_0__t17_yellow_0.p',t16_yellow_0)).

fof(t17_yellow_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v3_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( r1_yellow_0(X1,X2)
          & r2_yellow_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t17_yellow_0.p',t17_yellow_0)).

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
    file('/export/starexec/sandbox/benchmark/yellow_0__t17_yellow_0.p',t15_yellow_0)).

fof(c_0_7,plain,(
    ! [X16,X17,X18,X19] :
      ( ( ~ r1_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ r2_hidden(X19,X17)
        | r1_orders_2(X16,X18,X19)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ l1_orders_2(X16) )
      & ( m1_subset_1(esk6_3(X16,X17,X18),u1_struct_0(X16))
        | r1_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ l1_orders_2(X16) )
      & ( r2_hidden(esk6_3(X16,X17,X18),X17)
        | r1_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ l1_orders_2(X16) )
      & ( ~ r1_orders_2(X16,X18,esk6_3(X16,X17,X18))
        | r1_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ l1_orders_2(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).

fof(c_0_8,plain,(
    ! [X31,X32,X33,X35,X36] :
      ( ( m1_subset_1(esk11_3(X31,X32,X33),u1_struct_0(X32))
        | ~ r2_hidden(X31,a_2_0_yellow_0(X32,X33))
        | v2_struct_0(X32)
        | ~ v5_orders_2(X32)
        | ~ v3_lattice3(X32)
        | ~ l1_orders_2(X32) )
      & ( X31 = esk11_3(X31,X32,X33)
        | ~ r2_hidden(X31,a_2_0_yellow_0(X32,X33))
        | v2_struct_0(X32)
        | ~ v5_orders_2(X32)
        | ~ v3_lattice3(X32)
        | ~ l1_orders_2(X32) )
      & ( r1_lattice3(X32,X33,esk11_3(X31,X32,X33))
        | ~ r2_hidden(X31,a_2_0_yellow_0(X32,X33))
        | v2_struct_0(X32)
        | ~ v5_orders_2(X32)
        | ~ v3_lattice3(X32)
        | ~ l1_orders_2(X32) )
      & ( ~ m1_subset_1(X36,u1_struct_0(X32))
        | X31 != X36
        | ~ r1_lattice3(X32,X35,X36)
        | r2_hidden(X31,a_2_0_yellow_0(X32,X35))
        | v2_struct_0(X32)
        | ~ v5_orders_2(X32)
        | ~ v3_lattice3(X32)
        | ~ l1_orders_2(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_yellow_0])])])])])])])).

cnf(c_0_9,plain,
    ( r1_orders_2(X1,X3,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( r1_lattice3(X1,X2,esk11_3(X3,X1,X2))
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,a_2_0_yellow_0(X1,X2))
    | ~ v5_orders_2(X1)
    | ~ v3_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( m1_subset_1(esk11_3(X1,X2,X3),u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_0_yellow_0(X2,X3))
    | ~ v5_orders_2(X2)
    | ~ v3_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( r1_orders_2(X1,esk11_3(X2,X1,X3),X4)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X2,a_2_0_yellow_0(X1,X3))
    | ~ r2_hidden(X4,X3)
    | ~ l1_orders_2(X1)
    | ~ v3_lattice3(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])).

cnf(c_0_13,plain,
    ( X1 = esk11_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_0_yellow_0(X2,X3))
    | ~ v5_orders_2(X2)
    | ~ v3_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_14,plain,(
    ! [X21,X22,X23,X24] :
      ( ( ~ r2_lattice3(X21,X22,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ r2_hidden(X24,X22)
        | r1_orders_2(X21,X24,X23)
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ l1_orders_2(X21) )
      & ( m1_subset_1(esk7_3(X21,X22,X23),u1_struct_0(X21))
        | r2_lattice3(X21,X22,X23)
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ l1_orders_2(X21) )
      & ( r2_hidden(esk7_3(X21,X22,X23),X22)
        | r2_lattice3(X21,X22,X23)
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ l1_orders_2(X21) )
      & ( ~ r1_orders_2(X21,esk7_3(X21,X22,X23),X23)
        | r2_lattice3(X21,X22,X23)
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ l1_orders_2(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

fof(c_0_15,plain,(
    ! [X9,X10,X12,X14] :
      ( ( m1_subset_1(esk3_2(X9,X10),u1_struct_0(X9))
        | ~ v3_lattice3(X9)
        | ~ l1_orders_2(X9) )
      & ( r2_lattice3(X9,X10,esk3_2(X9,X10))
        | ~ v3_lattice3(X9)
        | ~ l1_orders_2(X9) )
      & ( ~ m1_subset_1(X12,u1_struct_0(X9))
        | ~ r2_lattice3(X9,X10,X12)
        | r1_orders_2(X9,esk3_2(X9,X10),X12)
        | ~ v3_lattice3(X9)
        | ~ l1_orders_2(X9) )
      & ( m1_subset_1(esk5_2(X9,X14),u1_struct_0(X9))
        | ~ m1_subset_1(X14,u1_struct_0(X9))
        | ~ r2_lattice3(X9,esk4_1(X9),X14)
        | v3_lattice3(X9)
        | ~ l1_orders_2(X9) )
      & ( r2_lattice3(X9,esk4_1(X9),esk5_2(X9,X14))
        | ~ m1_subset_1(X14,u1_struct_0(X9))
        | ~ r2_lattice3(X9,esk4_1(X9),X14)
        | v3_lattice3(X9)
        | ~ l1_orders_2(X9) )
      & ( ~ r1_orders_2(X9,X14,esk5_2(X9,X14))
        | ~ m1_subset_1(X14,u1_struct_0(X9))
        | ~ r2_lattice3(X9,esk4_1(X9),X14)
        | v3_lattice3(X9)
        | ~ l1_orders_2(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_lattice3])])])])])).

cnf(c_0_16,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X2,a_2_0_yellow_0(X1,X4))
    | ~ r2_hidden(X3,X4)
    | ~ l1_orders_2(X1)
    | ~ v3_lattice3(X1)
    | ~ v5_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( r2_hidden(esk7_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X44,X45,X47,X48,X49] :
      ( ( m1_subset_1(esk14_2(X44,X45),u1_struct_0(X44))
        | ~ r2_yellow_0(X44,X45)
        | ~ v5_orders_2(X44)
        | ~ l1_orders_2(X44) )
      & ( r1_lattice3(X44,X45,esk14_2(X44,X45))
        | ~ r2_yellow_0(X44,X45)
        | ~ v5_orders_2(X44)
        | ~ l1_orders_2(X44) )
      & ( ~ m1_subset_1(X47,u1_struct_0(X44))
        | ~ r1_lattice3(X44,X45,X47)
        | r1_orders_2(X44,X47,esk14_2(X44,X45))
        | ~ r2_yellow_0(X44,X45)
        | ~ v5_orders_2(X44)
        | ~ l1_orders_2(X44) )
      & ( m1_subset_1(esk15_3(X44,X48,X49),u1_struct_0(X44))
        | ~ m1_subset_1(X49,u1_struct_0(X44))
        | ~ r1_lattice3(X44,X48,X49)
        | r2_yellow_0(X44,X48)
        | ~ v5_orders_2(X44)
        | ~ l1_orders_2(X44) )
      & ( r1_lattice3(X44,X48,esk15_3(X44,X48,X49))
        | ~ m1_subset_1(X49,u1_struct_0(X44))
        | ~ r1_lattice3(X44,X48,X49)
        | r2_yellow_0(X44,X48)
        | ~ v5_orders_2(X44)
        | ~ l1_orders_2(X44) )
      & ( ~ r1_orders_2(X44,esk15_3(X44,X48,X49),X49)
        | ~ m1_subset_1(X49,u1_struct_0(X44))
        | ~ r1_lattice3(X44,X48,X49)
        | r2_yellow_0(X44,X48)
        | ~ v5_orders_2(X44)
        | ~ l1_orders_2(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_yellow_0])])])])])])).

cnf(c_0_19,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( r2_lattice3(X1,X2,esk3_2(X1,X2))
    | ~ v3_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | ~ v3_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( r2_hidden(X3,a_2_0_yellow_0(X2,X4))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ r1_lattice3(X2,X4,X1)
    | ~ v5_orders_2(X2)
    | ~ v3_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,plain,
    ( r1_lattice3(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,esk6_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_24,plain,
    ( r1_orders_2(X2,esk3_2(X2,X3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ v3_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk7_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,plain,
    ( r1_orders_2(X1,esk7_3(X2,a_2_0_yellow_0(X1,X3),X4),X5)
    | r2_lattice3(X2,a_2_0_yellow_0(X1,X3),X4)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(X5,X3)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2)
    | ~ v3_lattice3(X1)
    | ~ v5_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_27,plain,
    ( r2_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,esk15_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( r1_orders_2(X1,X2,esk3_2(X1,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,X3)
    | ~ l1_orders_2(X1)
    | ~ v3_lattice3(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,a_2_0_yellow_0(X2,X3))
    | v2_struct_0(X2)
    | ~ r1_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | ~ v3_lattice3(X2)
    | ~ v5_orders_2(X2) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( r1_lattice3(X1,X2,esk15_3(X1,X2,X3))
    | r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_31,plain,
    ( m1_subset_1(esk15_3(X1,X2,X3),u1_struct_0(X1))
    | r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_32,plain,
    ( r1_lattice3(X1,X2,esk3_2(X1,X3))
    | ~ r2_lattice3(X1,X3,esk6_3(X1,X2,esk3_2(X1,X3)))
    | ~ m1_subset_1(esk6_3(X1,X2,esk3_2(X1,X3)),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_lattice3(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_21])).

cnf(c_0_33,plain,
    ( r2_lattice3(X1,a_2_0_yellow_0(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X3,X2)
    | ~ l1_orders_2(X1)
    | ~ v3_lattice3(X1)
    | ~ v5_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,plain,
    ( r2_yellow_0(X1,X2)
    | ~ r1_lattice3(X1,X2,esk3_2(X1,X3))
    | ~ m1_subset_1(esk15_3(X1,X2,esk3_2(X1,X3)),u1_struct_0(X1))
    | ~ r2_hidden(esk15_3(X1,X2,esk3_2(X1,X3)),X3)
    | ~ l1_orders_2(X1)
    | ~ v3_lattice3(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_21])).

cnf(c_0_35,plain,
    ( r2_hidden(esk15_3(X1,X2,X3),a_2_0_yellow_0(X1,X2))
    | r2_yellow_0(X1,X2)
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_lattice3(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_36,plain,
    ( r1_lattice3(X1,X2,esk3_2(X1,a_2_0_yellow_0(X1,X3)))
    | v2_struct_0(X1)
    | ~ m1_subset_1(esk6_3(X1,X2,esk3_2(X1,a_2_0_yellow_0(X1,X3))),u1_struct_0(X1))
    | ~ r2_hidden(esk6_3(X1,X2,esk3_2(X1,a_2_0_yellow_0(X1,X3))),X3)
    | ~ l1_orders_2(X1)
    | ~ v3_lattice3(X1)
    | ~ v5_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X2)
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_38,plain,
    ( r2_yellow_0(X1,X2)
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,esk3_2(X1,a_2_0_yellow_0(X1,X2)))
    | ~ m1_subset_1(esk15_3(X1,X2,esk3_2(X1,a_2_0_yellow_0(X1,X2))),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_lattice3(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_21])).

cnf(c_0_39,plain,
    ( r1_lattice3(X1,X2,esk3_2(X1,a_2_0_yellow_0(X1,X2)))
    | v2_struct_0(X1)
    | ~ m1_subset_1(esk6_3(X1,X2,esk3_2(X1,a_2_0_yellow_0(X1,X2))),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_lattice3(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_21])).

cnf(c_0_40,plain,
    ( m1_subset_1(esk6_3(X1,X2,X3),u1_struct_0(X1))
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_41,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v5_orders_2(X1)
          & v3_lattice3(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( r1_yellow_0(X1,X2)
            & r2_yellow_0(X1,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t17_yellow_0])).

fof(c_0_42,plain,(
    ! [X37,X38,X40,X41,X42] :
      ( ( m1_subset_1(esk12_2(X37,X38),u1_struct_0(X37))
        | ~ r1_yellow_0(X37,X38)
        | ~ v5_orders_2(X37)
        | ~ l1_orders_2(X37) )
      & ( r2_lattice3(X37,X38,esk12_2(X37,X38))
        | ~ r1_yellow_0(X37,X38)
        | ~ v5_orders_2(X37)
        | ~ l1_orders_2(X37) )
      & ( ~ m1_subset_1(X40,u1_struct_0(X37))
        | ~ r2_lattice3(X37,X38,X40)
        | r1_orders_2(X37,esk12_2(X37,X38),X40)
        | ~ r1_yellow_0(X37,X38)
        | ~ v5_orders_2(X37)
        | ~ l1_orders_2(X37) )
      & ( m1_subset_1(esk13_3(X37,X41,X42),u1_struct_0(X37))
        | ~ m1_subset_1(X42,u1_struct_0(X37))
        | ~ r2_lattice3(X37,X41,X42)
        | r1_yellow_0(X37,X41)
        | ~ v5_orders_2(X37)
        | ~ l1_orders_2(X37) )
      & ( r2_lattice3(X37,X41,esk13_3(X37,X41,X42))
        | ~ m1_subset_1(X42,u1_struct_0(X37))
        | ~ r2_lattice3(X37,X41,X42)
        | r1_yellow_0(X37,X41)
        | ~ v5_orders_2(X37)
        | ~ l1_orders_2(X37) )
      & ( ~ r1_orders_2(X37,X42,esk13_3(X37,X41,X42))
        | ~ m1_subset_1(X42,u1_struct_0(X37))
        | ~ r2_lattice3(X37,X41,X42)
        | r1_yellow_0(X37,X41)
        | ~ v5_orders_2(X37)
        | ~ l1_orders_2(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_yellow_0])])])])])])).

cnf(c_0_43,plain,
    ( r2_yellow_0(X1,X2)
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,esk3_2(X1,a_2_0_yellow_0(X1,X2)))
    | ~ l1_orders_2(X1)
    | ~ v3_lattice3(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_31]),c_0_21])).

cnf(c_0_44,plain,
    ( r1_lattice3(X1,X2,esk3_2(X1,a_2_0_yellow_0(X1,X2)))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_lattice3(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_21])).

fof(c_0_45,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v5_orders_2(esk1_0)
    & v3_lattice3(esk1_0)
    & l1_orders_2(esk1_0)
    & ( ~ r1_yellow_0(esk1_0,esk2_0)
      | ~ r2_yellow_0(esk1_0,esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_41])])])])).

cnf(c_0_46,plain,
    ( r1_yellow_0(X1,X3)
    | ~ r1_orders_2(X1,X2,esk13_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X3,X2)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_47,plain,
    ( r2_yellow_0(X1,X2)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_lattice3(X1)
    | ~ v5_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( v3_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,plain,
    ( r1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X3,esk13_3(X1,X2,esk3_2(X1,X3)))
    | ~ r2_lattice3(X1,X2,esk3_2(X1,X3))
    | ~ m1_subset_1(esk13_3(X1,X2,esk3_2(X1,X3)),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_lattice3(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_24]),c_0_21])).

cnf(c_0_53,plain,
    ( r2_lattice3(X1,X2,esk13_3(X1,X2,X3))
    | r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_54,negated_conjecture,
    ( ~ r1_yellow_0(esk1_0,esk2_0)
    | ~ r2_yellow_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_55,negated_conjecture,
    ( r2_yellow_0(esk1_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_50])]),c_0_51])).

cnf(c_0_56,plain,
    ( r1_yellow_0(X1,X2)
    | ~ m1_subset_1(esk13_3(X1,X2,esk3_2(X1,X2)),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_lattice3(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_21]),c_0_20])).

cnf(c_0_57,plain,
    ( m1_subset_1(esk13_3(X1,X2,X3),u1_struct_0(X1))
    | r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_58,negated_conjecture,
    ( ~ r1_yellow_0(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55])])).

cnf(c_0_59,plain,
    ( r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1)
    | ~ v3_lattice3(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_21]),c_0_20])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_48]),c_0_49]),c_0_50])]),
    [proof]).
%------------------------------------------------------------------------------
