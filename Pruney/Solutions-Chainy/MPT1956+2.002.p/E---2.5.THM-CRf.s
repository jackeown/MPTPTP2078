%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:21 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 244 expanded)
%              Number of clauses        :   41 (  90 expanded)
%              Number of leaves         :   10 (  59 expanded)
%              Depth                    :   10
%              Number of atoms          :  357 (1595 expanded)
%              Number of equality atoms :   22 (  28 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   40 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_waybel_7,conjecture,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & v3_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2,X3] :
          ( r1_tarski(X2,X3)
         => ( r3_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3))
            & r1_orders_2(X1,k2_yellow_0(X1,X3),k2_yellow_0(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_waybel_7)).

fof(dt_k2_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_0)).

fof(t33_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v3_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( X2 = k2_yellow_0(X1,X3)
            <=> ( r1_lattice3(X1,X3,X2)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r1_lattice3(X1,X3,X4)
                     => r1_orders_2(X1,X4,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_yellow_0)).

fof(cc1_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

fof(dt_k1_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_yellow_0)).

fof(t9_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( r1_tarski(X2,X3)
         => ! [X4] :
              ( m1_subset_1(X4,u1_struct_0(X1))
             => ( ( r1_lattice3(X1,X3,X4)
                 => r1_lattice3(X1,X2,X4) )
                & ( r2_lattice3(X1,X3,X4)
                 => r2_lattice3(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_0)).

fof(t32_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v3_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( X2 = k1_yellow_0(X1,X3)
            <=> ( r2_lattice3(X1,X3,X2)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r2_lattice3(X1,X3,X4)
                     => r1_orders_2(X1,X2,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_yellow_0)).

fof(t17_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v3_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( r1_yellow_0(X1,X2)
          & r2_yellow_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow_0)).

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

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & v1_lattice3(X1)
          & v2_lattice3(X1)
          & v3_lattice3(X1)
          & l1_orders_2(X1) )
       => ! [X2,X3] :
            ( r1_tarski(X2,X3)
           => ( r3_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3))
              & r1_orders_2(X1,k2_yellow_0(X1,X3),k2_yellow_0(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t3_waybel_7])).

fof(c_0_11,plain,(
    ! [X16,X17] :
      ( ~ l1_orders_2(X16)
      | m1_subset_1(k2_yellow_0(X16,X17),u1_struct_0(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_yellow_0])])).

fof(c_0_12,negated_conjecture,
    ( v3_orders_2(esk4_0)
    & v4_orders_2(esk4_0)
    & v5_orders_2(esk4_0)
    & v1_lattice3(esk4_0)
    & v2_lattice3(esk4_0)
    & v3_lattice3(esk4_0)
    & l1_orders_2(esk4_0)
    & r1_tarski(esk5_0,esk6_0)
    & ( ~ r3_orders_2(esk4_0,k1_yellow_0(esk4_0,esk5_0),k1_yellow_0(esk4_0,esk6_0))
      | ~ r1_orders_2(esk4_0,k2_yellow_0(esk4_0,esk6_0),k2_yellow_0(esk4_0,esk5_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_13,plain,(
    ! [X26,X27,X28,X29,X30] :
      ( ( r1_lattice3(X26,X28,X27)
        | X27 != k2_yellow_0(X26,X28)
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | v2_struct_0(X26)
        | ~ v5_orders_2(X26)
        | ~ v3_lattice3(X26)
        | ~ l1_orders_2(X26) )
      & ( ~ m1_subset_1(X29,u1_struct_0(X26))
        | ~ r1_lattice3(X26,X28,X29)
        | r1_orders_2(X26,X29,X27)
        | X27 != k2_yellow_0(X26,X28)
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | v2_struct_0(X26)
        | ~ v5_orders_2(X26)
        | ~ v3_lattice3(X26)
        | ~ l1_orders_2(X26) )
      & ( m1_subset_1(esk3_3(X26,X27,X30),u1_struct_0(X26))
        | ~ r1_lattice3(X26,X30,X27)
        | X27 = k2_yellow_0(X26,X30)
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | v2_struct_0(X26)
        | ~ v5_orders_2(X26)
        | ~ v3_lattice3(X26)
        | ~ l1_orders_2(X26) )
      & ( r1_lattice3(X26,X30,esk3_3(X26,X27,X30))
        | ~ r1_lattice3(X26,X30,X27)
        | X27 = k2_yellow_0(X26,X30)
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | v2_struct_0(X26)
        | ~ v5_orders_2(X26)
        | ~ v3_lattice3(X26)
        | ~ l1_orders_2(X26) )
      & ( ~ r1_orders_2(X26,esk3_3(X26,X27,X30),X27)
        | ~ r1_lattice3(X26,X30,X27)
        | X27 = k2_yellow_0(X26,X30)
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | v2_struct_0(X26)
        | ~ v5_orders_2(X26)
        | ~ v3_lattice3(X26)
        | ~ l1_orders_2(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t33_yellow_0])])])])])])])).

fof(c_0_14,plain,(
    ! [X8] :
      ( ~ l1_orders_2(X8)
      | ~ v1_lattice3(X8)
      | ~ v2_struct_0(X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).

fof(c_0_15,plain,(
    ! [X14,X15] :
      ( ~ l1_orders_2(X14)
      | m1_subset_1(k1_yellow_0(X14,X15),u1_struct_0(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

fof(c_0_16,plain,(
    ! [X9,X10,X11,X12] :
      ( ( r1_lattice3(X9,X10,X11)
        | X11 != k2_yellow_0(X9,X10)
        | ~ r2_yellow_0(X9,X10)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ l1_orders_2(X9) )
      & ( ~ m1_subset_1(X12,u1_struct_0(X9))
        | ~ r1_lattice3(X9,X10,X12)
        | r1_orders_2(X9,X12,X11)
        | X11 != k2_yellow_0(X9,X10)
        | ~ r2_yellow_0(X9,X10)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ l1_orders_2(X9) )
      & ( m1_subset_1(esk1_3(X9,X10,X11),u1_struct_0(X9))
        | ~ r1_lattice3(X9,X10,X11)
        | X11 = k2_yellow_0(X9,X10)
        | ~ r2_yellow_0(X9,X10)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ l1_orders_2(X9) )
      & ( r1_lattice3(X9,X10,esk1_3(X9,X10,X11))
        | ~ r1_lattice3(X9,X10,X11)
        | X11 = k2_yellow_0(X9,X10)
        | ~ r2_yellow_0(X9,X10)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ l1_orders_2(X9) )
      & ( ~ r1_orders_2(X9,esk1_3(X9,X10,X11),X11)
        | ~ r1_lattice3(X9,X10,X11)
        | X11 = k2_yellow_0(X9,X10)
        | ~ r2_yellow_0(X9,X10)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ l1_orders_2(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_yellow_0])])])])])).

fof(c_0_17,plain,(
    ! [X32,X33,X34,X35] :
      ( ( ~ r1_lattice3(X32,X34,X35)
        | r1_lattice3(X32,X33,X35)
        | ~ m1_subset_1(X35,u1_struct_0(X32))
        | ~ r1_tarski(X33,X34)
        | ~ l1_orders_2(X32) )
      & ( ~ r2_lattice3(X32,X34,X35)
        | r2_lattice3(X32,X33,X35)
        | ~ m1_subset_1(X35,u1_struct_0(X32))
        | ~ r1_tarski(X33,X34)
        | ~ l1_orders_2(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_yellow_0])])])])).

cnf(c_0_18,plain,
    ( m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( r1_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | X3 != k2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v3_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( v1_lattice3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_24,plain,(
    ! [X20,X21,X22,X23,X24] :
      ( ( r2_lattice3(X20,X22,X21)
        | X21 != k1_yellow_0(X20,X22)
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | v2_struct_0(X20)
        | ~ v5_orders_2(X20)
        | ~ v3_lattice3(X20)
        | ~ l1_orders_2(X20) )
      & ( ~ m1_subset_1(X23,u1_struct_0(X20))
        | ~ r2_lattice3(X20,X22,X23)
        | r1_orders_2(X20,X21,X23)
        | X21 != k1_yellow_0(X20,X22)
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | v2_struct_0(X20)
        | ~ v5_orders_2(X20)
        | ~ v3_lattice3(X20)
        | ~ l1_orders_2(X20) )
      & ( m1_subset_1(esk2_3(X20,X21,X24),u1_struct_0(X20))
        | ~ r2_lattice3(X20,X24,X21)
        | X21 = k1_yellow_0(X20,X24)
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | v2_struct_0(X20)
        | ~ v5_orders_2(X20)
        | ~ v3_lattice3(X20)
        | ~ l1_orders_2(X20) )
      & ( r2_lattice3(X20,X24,esk2_3(X20,X21,X24))
        | ~ r2_lattice3(X20,X24,X21)
        | X21 = k1_yellow_0(X20,X24)
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | v2_struct_0(X20)
        | ~ v5_orders_2(X20)
        | ~ v3_lattice3(X20)
        | ~ l1_orders_2(X20) )
      & ( ~ r1_orders_2(X20,X21,esk2_3(X20,X21,X24))
        | ~ r2_lattice3(X20,X24,X21)
        | X21 = k1_yellow_0(X20,X24)
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | v2_struct_0(X20)
        | ~ v5_orders_2(X20)
        | ~ v3_lattice3(X20)
        | ~ l1_orders_2(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_yellow_0])])])])])])])).

cnf(c_0_25,plain,
    ( r1_orders_2(X2,X1,X4)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | X4 != k2_yellow_0(X2,X3)
    | ~ r2_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( r1_lattice3(X1,X4,X3)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_tarski(X4,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(k2_yellow_0(esk4_0,X1),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_28,plain,
    ( r1_lattice3(X1,X2,k2_yellow_0(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_20]),c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( v3_lattice3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_30,negated_conjecture,
    ( v5_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_31,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_19])])).

cnf(c_0_32,plain,
    ( r2_lattice3(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_tarski(X4,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(k1_yellow_0(esk4_0,X1),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_19])).

cnf(c_0_34,plain,
    ( r2_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | X3 != k1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v3_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( r1_orders_2(X1,X2,k2_yellow_0(X1,X3))
    | ~ r1_lattice3(X1,X3,X2)
    | ~ r2_yellow_0(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_25]),c_0_18])).

fof(c_0_36,plain,(
    ! [X18,X19] :
      ( ( r1_yellow_0(X18,X19)
        | v2_struct_0(X18)
        | ~ v5_orders_2(X18)
        | ~ v3_lattice3(X18)
        | ~ l1_orders_2(X18) )
      & ( r2_yellow_0(X18,X19)
        | v2_struct_0(X18)
        | ~ v5_orders_2(X18)
        | ~ v3_lattice3(X18)
        | ~ l1_orders_2(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t17_yellow_0])])])])])).

cnf(c_0_37,negated_conjecture,
    ( r1_lattice3(esk4_0,X1,k2_yellow_0(esk4_0,X2))
    | ~ r1_tarski(X1,X3)
    | ~ r1_lattice3(esk4_0,X3,k2_yellow_0(esk4_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_19])])).

cnf(c_0_38,negated_conjecture,
    ( r1_lattice3(esk4_0,X1,k2_yellow_0(esk4_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_19])]),c_0_31])).

fof(c_0_39,plain,(
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

cnf(c_0_40,plain,
    ( r1_orders_2(X2,X4,X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | X4 != k1_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ v3_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_41,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,k1_yellow_0(esk4_0,X2))
    | ~ r1_tarski(X1,X3)
    | ~ r2_lattice3(esk4_0,X3,k1_yellow_0(esk4_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_19])])).

cnf(c_0_42,plain,
    ( r2_lattice3(X1,X2,k1_yellow_0(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_34]),c_0_23])).

cnf(c_0_43,negated_conjecture,
    ( r1_orders_2(esk4_0,k2_yellow_0(esk4_0,X1),k2_yellow_0(esk4_0,X2))
    | ~ r1_lattice3(esk4_0,X2,k2_yellow_0(esk4_0,X1))
    | ~ r2_yellow_0(esk4_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_27]),c_0_19])])).

cnf(c_0_44,plain,
    ( r2_yellow_0(X1,X2)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v3_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( r1_lattice3(esk4_0,X1,k2_yellow_0(esk4_0,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_47,plain,
    ( r3_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( v3_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_49,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ v3_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_40]),c_0_23])).

cnf(c_0_50,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,k1_yellow_0(esk4_0,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_29]),c_0_30]),c_0_19])]),c_0_31])).

cnf(c_0_51,negated_conjecture,
    ( r1_orders_2(esk4_0,k2_yellow_0(esk4_0,X1),k2_yellow_0(esk4_0,X2))
    | ~ r1_lattice3(esk4_0,X2,k2_yellow_0(esk4_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_29]),c_0_30]),c_0_19])]),c_0_31])).

cnf(c_0_52,negated_conjecture,
    ( r1_lattice3(esk4_0,esk5_0,k2_yellow_0(esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( r3_orders_2(esk4_0,X1,k1_yellow_0(esk4_0,X2))
    | ~ r1_orders_2(esk4_0,X1,k1_yellow_0(esk4_0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_33]),c_0_19]),c_0_48])]),c_0_31])).

cnf(c_0_54,negated_conjecture,
    ( r1_orders_2(esk4_0,k1_yellow_0(esk4_0,X1),k1_yellow_0(esk4_0,X2))
    | ~ r2_lattice3(esk4_0,X1,k1_yellow_0(esk4_0,X2)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_33]),c_0_29]),c_0_30]),c_0_19])]),c_0_31])).

cnf(c_0_55,negated_conjecture,
    ( r2_lattice3(esk4_0,esk5_0,k1_yellow_0(esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_46])).

cnf(c_0_56,negated_conjecture,
    ( ~ r3_orders_2(esk4_0,k1_yellow_0(esk4_0,esk5_0),k1_yellow_0(esk4_0,esk6_0))
    | ~ r1_orders_2(esk4_0,k2_yellow_0(esk4_0,esk6_0),k2_yellow_0(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_57,negated_conjecture,
    ( r1_orders_2(esk4_0,k2_yellow_0(esk4_0,esk6_0),k2_yellow_0(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( r3_orders_2(esk4_0,k1_yellow_0(esk4_0,X1),k1_yellow_0(esk4_0,X2))
    | ~ r1_orders_2(esk4_0,k1_yellow_0(esk4_0,X1),k1_yellow_0(esk4_0,X2)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_33])).

cnf(c_0_59,negated_conjecture,
    ( r1_orders_2(esk4_0,k1_yellow_0(esk4_0,esk5_0),k1_yellow_0(esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( ~ r3_orders_2(esk4_0,k1_yellow_0(esk4_0,esk5_0),k1_yellow_0(esk4_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57])])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:11:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.20/0.38  # and selection function SelectNewComplexAHP.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.029 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t3_waybel_7, conjecture, ![X1]:(((((((v3_orders_2(X1)&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&v3_lattice3(X1))&l1_orders_2(X1))=>![X2, X3]:(r1_tarski(X2,X3)=>(r3_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3))&r1_orders_2(X1,k2_yellow_0(X1,X3),k2_yellow_0(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_waybel_7)).
% 0.20/0.38  fof(dt_k2_yellow_0, axiom, ![X1, X2]:(l1_orders_2(X1)=>m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_0)).
% 0.20/0.38  fof(t33_yellow_0, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v3_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(X2=k2_yellow_0(X1,X3)<=>(r1_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattice3(X1,X3,X4)=>r1_orders_2(X1,X4,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_yellow_0)).
% 0.20/0.38  fof(cc1_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v1_lattice3(X1)=>~(v2_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattice3)).
% 0.20/0.38  fof(dt_k1_yellow_0, axiom, ![X1, X2]:(l1_orders_2(X1)=>m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 0.20/0.38  fof(d10_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_yellow_0(X1,X2)=>(X3=k2_yellow_0(X1,X2)<=>(r1_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X4)=>r1_orders_2(X1,X4,X3)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_yellow_0)).
% 0.20/0.38  fof(t9_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r1_lattice3(X1,X3,X4)=>r1_lattice3(X1,X2,X4))&(r2_lattice3(X1,X3,X4)=>r2_lattice3(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_yellow_0)).
% 0.20/0.38  fof(t32_yellow_0, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v3_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(X2=k1_yellow_0(X1,X3)<=>(r2_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X3,X4)=>r1_orders_2(X1,X2,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_yellow_0)).
% 0.20/0.38  fof(t17_yellow_0, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v3_lattice3(X1))&l1_orders_2(X1))=>![X2]:(r1_yellow_0(X1,X2)&r2_yellow_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_yellow_0)).
% 0.20/0.38  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 0.20/0.38  fof(c_0_10, negated_conjecture, ~(![X1]:(((((((v3_orders_2(X1)&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&v3_lattice3(X1))&l1_orders_2(X1))=>![X2, X3]:(r1_tarski(X2,X3)=>(r3_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3))&r1_orders_2(X1,k2_yellow_0(X1,X3),k2_yellow_0(X1,X2)))))), inference(assume_negation,[status(cth)],[t3_waybel_7])).
% 0.20/0.38  fof(c_0_11, plain, ![X16, X17]:(~l1_orders_2(X16)|m1_subset_1(k2_yellow_0(X16,X17),u1_struct_0(X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_yellow_0])])).
% 0.20/0.38  fof(c_0_12, negated_conjecture, (((((((v3_orders_2(esk4_0)&v4_orders_2(esk4_0))&v5_orders_2(esk4_0))&v1_lattice3(esk4_0))&v2_lattice3(esk4_0))&v3_lattice3(esk4_0))&l1_orders_2(esk4_0))&(r1_tarski(esk5_0,esk6_0)&(~r3_orders_2(esk4_0,k1_yellow_0(esk4_0,esk5_0),k1_yellow_0(esk4_0,esk6_0))|~r1_orders_2(esk4_0,k2_yellow_0(esk4_0,esk6_0),k2_yellow_0(esk4_0,esk5_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.20/0.38  fof(c_0_13, plain, ![X26, X27, X28, X29, X30]:(((r1_lattice3(X26,X28,X27)|X27!=k2_yellow_0(X26,X28)|~m1_subset_1(X27,u1_struct_0(X26))|(v2_struct_0(X26)|~v5_orders_2(X26)|~v3_lattice3(X26)|~l1_orders_2(X26)))&(~m1_subset_1(X29,u1_struct_0(X26))|(~r1_lattice3(X26,X28,X29)|r1_orders_2(X26,X29,X27))|X27!=k2_yellow_0(X26,X28)|~m1_subset_1(X27,u1_struct_0(X26))|(v2_struct_0(X26)|~v5_orders_2(X26)|~v3_lattice3(X26)|~l1_orders_2(X26))))&((m1_subset_1(esk3_3(X26,X27,X30),u1_struct_0(X26))|~r1_lattice3(X26,X30,X27)|X27=k2_yellow_0(X26,X30)|~m1_subset_1(X27,u1_struct_0(X26))|(v2_struct_0(X26)|~v5_orders_2(X26)|~v3_lattice3(X26)|~l1_orders_2(X26)))&((r1_lattice3(X26,X30,esk3_3(X26,X27,X30))|~r1_lattice3(X26,X30,X27)|X27=k2_yellow_0(X26,X30)|~m1_subset_1(X27,u1_struct_0(X26))|(v2_struct_0(X26)|~v5_orders_2(X26)|~v3_lattice3(X26)|~l1_orders_2(X26)))&(~r1_orders_2(X26,esk3_3(X26,X27,X30),X27)|~r1_lattice3(X26,X30,X27)|X27=k2_yellow_0(X26,X30)|~m1_subset_1(X27,u1_struct_0(X26))|(v2_struct_0(X26)|~v5_orders_2(X26)|~v3_lattice3(X26)|~l1_orders_2(X26)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t33_yellow_0])])])])])])])).
% 0.20/0.38  fof(c_0_14, plain, ![X8]:(~l1_orders_2(X8)|(~v1_lattice3(X8)|~v2_struct_0(X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).
% 0.20/0.38  fof(c_0_15, plain, ![X14, X15]:(~l1_orders_2(X14)|m1_subset_1(k1_yellow_0(X14,X15),u1_struct_0(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).
% 0.20/0.38  fof(c_0_16, plain, ![X9, X10, X11, X12]:(((r1_lattice3(X9,X10,X11)|X11!=k2_yellow_0(X9,X10)|~r2_yellow_0(X9,X10)|~m1_subset_1(X11,u1_struct_0(X9))|~l1_orders_2(X9))&(~m1_subset_1(X12,u1_struct_0(X9))|(~r1_lattice3(X9,X10,X12)|r1_orders_2(X9,X12,X11))|X11!=k2_yellow_0(X9,X10)|~r2_yellow_0(X9,X10)|~m1_subset_1(X11,u1_struct_0(X9))|~l1_orders_2(X9)))&((m1_subset_1(esk1_3(X9,X10,X11),u1_struct_0(X9))|~r1_lattice3(X9,X10,X11)|X11=k2_yellow_0(X9,X10)|~r2_yellow_0(X9,X10)|~m1_subset_1(X11,u1_struct_0(X9))|~l1_orders_2(X9))&((r1_lattice3(X9,X10,esk1_3(X9,X10,X11))|~r1_lattice3(X9,X10,X11)|X11=k2_yellow_0(X9,X10)|~r2_yellow_0(X9,X10)|~m1_subset_1(X11,u1_struct_0(X9))|~l1_orders_2(X9))&(~r1_orders_2(X9,esk1_3(X9,X10,X11),X11)|~r1_lattice3(X9,X10,X11)|X11=k2_yellow_0(X9,X10)|~r2_yellow_0(X9,X10)|~m1_subset_1(X11,u1_struct_0(X9))|~l1_orders_2(X9))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_yellow_0])])])])])).
% 0.20/0.38  fof(c_0_17, plain, ![X32, X33, X34, X35]:((~r1_lattice3(X32,X34,X35)|r1_lattice3(X32,X33,X35)|~m1_subset_1(X35,u1_struct_0(X32))|~r1_tarski(X33,X34)|~l1_orders_2(X32))&(~r2_lattice3(X32,X34,X35)|r2_lattice3(X32,X33,X35)|~m1_subset_1(X35,u1_struct_0(X32))|~r1_tarski(X33,X34)|~l1_orders_2(X32))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_yellow_0])])])])).
% 0.20/0.38  cnf(c_0_18, plain, (m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  cnf(c_0_19, negated_conjecture, (l1_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_20, plain, (r1_lattice3(X1,X2,X3)|v2_struct_0(X1)|X3!=k2_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~v3_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_21, plain, (~l1_orders_2(X1)|~v1_lattice3(X1)|~v2_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  cnf(c_0_22, negated_conjecture, (v1_lattice3(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_23, plain, (m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  fof(c_0_24, plain, ![X20, X21, X22, X23, X24]:(((r2_lattice3(X20,X22,X21)|X21!=k1_yellow_0(X20,X22)|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~v5_orders_2(X20)|~v3_lattice3(X20)|~l1_orders_2(X20)))&(~m1_subset_1(X23,u1_struct_0(X20))|(~r2_lattice3(X20,X22,X23)|r1_orders_2(X20,X21,X23))|X21!=k1_yellow_0(X20,X22)|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~v5_orders_2(X20)|~v3_lattice3(X20)|~l1_orders_2(X20))))&((m1_subset_1(esk2_3(X20,X21,X24),u1_struct_0(X20))|~r2_lattice3(X20,X24,X21)|X21=k1_yellow_0(X20,X24)|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~v5_orders_2(X20)|~v3_lattice3(X20)|~l1_orders_2(X20)))&((r2_lattice3(X20,X24,esk2_3(X20,X21,X24))|~r2_lattice3(X20,X24,X21)|X21=k1_yellow_0(X20,X24)|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~v5_orders_2(X20)|~v3_lattice3(X20)|~l1_orders_2(X20)))&(~r1_orders_2(X20,X21,esk2_3(X20,X21,X24))|~r2_lattice3(X20,X24,X21)|X21=k1_yellow_0(X20,X24)|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~v5_orders_2(X20)|~v3_lattice3(X20)|~l1_orders_2(X20)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_yellow_0])])])])])])])).
% 0.20/0.38  cnf(c_0_25, plain, (r1_orders_2(X2,X1,X4)|~m1_subset_1(X1,u1_struct_0(X2))|~r1_lattice3(X2,X3,X1)|X4!=k2_yellow_0(X2,X3)|~r2_yellow_0(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  cnf(c_0_26, plain, (r1_lattice3(X1,X4,X3)|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~r1_tarski(X4,X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_27, negated_conjecture, (m1_subset_1(k2_yellow_0(esk4_0,X1),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.38  cnf(c_0_28, plain, (r1_lattice3(X1,X2,k2_yellow_0(X1,X2))|v2_struct_0(X1)|~v3_lattice3(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_20]), c_0_18])).
% 0.20/0.38  cnf(c_0_29, negated_conjecture, (v3_lattice3(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_30, negated_conjecture, (v5_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_31, negated_conjecture, (~v2_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_19])])).
% 0.20/0.38  cnf(c_0_32, plain, (r2_lattice3(X1,X4,X3)|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~r1_tarski(X4,X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_33, negated_conjecture, (m1_subset_1(k1_yellow_0(esk4_0,X1),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_23, c_0_19])).
% 0.20/0.38  cnf(c_0_34, plain, (r2_lattice3(X1,X2,X3)|v2_struct_0(X1)|X3!=k1_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~v3_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.38  cnf(c_0_35, plain, (r1_orders_2(X1,X2,k2_yellow_0(X1,X3))|~r1_lattice3(X1,X3,X2)|~r2_yellow_0(X1,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_25]), c_0_18])).
% 0.20/0.38  fof(c_0_36, plain, ![X18, X19]:((r1_yellow_0(X18,X19)|(v2_struct_0(X18)|~v5_orders_2(X18)|~v3_lattice3(X18)|~l1_orders_2(X18)))&(r2_yellow_0(X18,X19)|(v2_struct_0(X18)|~v5_orders_2(X18)|~v3_lattice3(X18)|~l1_orders_2(X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t17_yellow_0])])])])])).
% 0.20/0.38  cnf(c_0_37, negated_conjecture, (r1_lattice3(esk4_0,X1,k2_yellow_0(esk4_0,X2))|~r1_tarski(X1,X3)|~r1_lattice3(esk4_0,X3,k2_yellow_0(esk4_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_19])])).
% 0.20/0.38  cnf(c_0_38, negated_conjecture, (r1_lattice3(esk4_0,X1,k2_yellow_0(esk4_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_19])]), c_0_31])).
% 0.20/0.38  fof(c_0_39, plain, ![X5, X6, X7]:((~r3_orders_2(X5,X6,X7)|r1_orders_2(X5,X6,X7)|(v2_struct_0(X5)|~v3_orders_2(X5)|~l1_orders_2(X5)|~m1_subset_1(X6,u1_struct_0(X5))|~m1_subset_1(X7,u1_struct_0(X5))))&(~r1_orders_2(X5,X6,X7)|r3_orders_2(X5,X6,X7)|(v2_struct_0(X5)|~v3_orders_2(X5)|~l1_orders_2(X5)|~m1_subset_1(X6,u1_struct_0(X5))|~m1_subset_1(X7,u1_struct_0(X5))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.20/0.38  cnf(c_0_40, plain, (r1_orders_2(X2,X4,X1)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|X4!=k1_yellow_0(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~v5_orders_2(X2)|~v3_lattice3(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.38  cnf(c_0_41, negated_conjecture, (r2_lattice3(esk4_0,X1,k1_yellow_0(esk4_0,X2))|~r1_tarski(X1,X3)|~r2_lattice3(esk4_0,X3,k1_yellow_0(esk4_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_19])])).
% 0.20/0.38  cnf(c_0_42, plain, (r2_lattice3(X1,X2,k1_yellow_0(X1,X2))|v2_struct_0(X1)|~v3_lattice3(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_34]), c_0_23])).
% 0.20/0.38  cnf(c_0_43, negated_conjecture, (r1_orders_2(esk4_0,k2_yellow_0(esk4_0,X1),k2_yellow_0(esk4_0,X2))|~r1_lattice3(esk4_0,X2,k2_yellow_0(esk4_0,X1))|~r2_yellow_0(esk4_0,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_27]), c_0_19])])).
% 0.20/0.38  cnf(c_0_44, plain, (r2_yellow_0(X1,X2)|v2_struct_0(X1)|~v5_orders_2(X1)|~v3_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.38  cnf(c_0_45, negated_conjecture, (r1_lattice3(esk4_0,X1,k2_yellow_0(esk4_0,X2))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.38  cnf(c_0_46, negated_conjecture, (r1_tarski(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_47, plain, (r3_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.38  cnf(c_0_48, negated_conjecture, (v3_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_49, plain, (r1_orders_2(X1,k1_yellow_0(X1,X2),X3)|v2_struct_0(X1)|~r2_lattice3(X1,X2,X3)|~v3_lattice3(X1)|~v5_orders_2(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_40]), c_0_23])).
% 0.20/0.38  cnf(c_0_50, negated_conjecture, (r2_lattice3(esk4_0,X1,k1_yellow_0(esk4_0,X2))|~r1_tarski(X1,X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_29]), c_0_30]), c_0_19])]), c_0_31])).
% 0.20/0.38  cnf(c_0_51, negated_conjecture, (r1_orders_2(esk4_0,k2_yellow_0(esk4_0,X1),k2_yellow_0(esk4_0,X2))|~r1_lattice3(esk4_0,X2,k2_yellow_0(esk4_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_29]), c_0_30]), c_0_19])]), c_0_31])).
% 0.20/0.38  cnf(c_0_52, negated_conjecture, (r1_lattice3(esk4_0,esk5_0,k2_yellow_0(esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.38  cnf(c_0_53, negated_conjecture, (r3_orders_2(esk4_0,X1,k1_yellow_0(esk4_0,X2))|~r1_orders_2(esk4_0,X1,k1_yellow_0(esk4_0,X2))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_33]), c_0_19]), c_0_48])]), c_0_31])).
% 0.20/0.38  cnf(c_0_54, negated_conjecture, (r1_orders_2(esk4_0,k1_yellow_0(esk4_0,X1),k1_yellow_0(esk4_0,X2))|~r2_lattice3(esk4_0,X1,k1_yellow_0(esk4_0,X2))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_33]), c_0_29]), c_0_30]), c_0_19])]), c_0_31])).
% 0.20/0.38  cnf(c_0_55, negated_conjecture, (r2_lattice3(esk4_0,esk5_0,k1_yellow_0(esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_50, c_0_46])).
% 0.20/0.38  cnf(c_0_56, negated_conjecture, (~r3_orders_2(esk4_0,k1_yellow_0(esk4_0,esk5_0),k1_yellow_0(esk4_0,esk6_0))|~r1_orders_2(esk4_0,k2_yellow_0(esk4_0,esk6_0),k2_yellow_0(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_57, negated_conjecture, (r1_orders_2(esk4_0,k2_yellow_0(esk4_0,esk6_0),k2_yellow_0(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.20/0.38  cnf(c_0_58, negated_conjecture, (r3_orders_2(esk4_0,k1_yellow_0(esk4_0,X1),k1_yellow_0(esk4_0,X2))|~r1_orders_2(esk4_0,k1_yellow_0(esk4_0,X1),k1_yellow_0(esk4_0,X2))), inference(spm,[status(thm)],[c_0_53, c_0_33])).
% 0.20/0.38  cnf(c_0_59, negated_conjecture, (r1_orders_2(esk4_0,k1_yellow_0(esk4_0,esk5_0),k1_yellow_0(esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.20/0.38  cnf(c_0_60, negated_conjecture, (~r3_orders_2(esk4_0,k1_yellow_0(esk4_0,esk5_0),k1_yellow_0(esk4_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57])])).
% 0.20/0.38  cnf(c_0_61, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 62
% 0.20/0.38  # Proof object clause steps            : 41
% 0.20/0.38  # Proof object formula steps           : 21
% 0.20/0.38  # Proof object conjectures             : 29
% 0.20/0.38  # Proof object clause conjectures      : 26
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 18
% 0.20/0.38  # Proof object initial formulas used   : 10
% 0.20/0.38  # Proof object generating inferences   : 18
% 0.20/0.38  # Proof object simplifying inferences  : 42
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 10
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 33
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 33
% 0.20/0.38  # Processed clauses                    : 114
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 3
% 0.20/0.38  # ...remaining for further processing  : 111
% 0.20/0.38  # Other redundant clauses eliminated   : 6
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 1
% 0.20/0.38  # Backward-rewritten                   : 1
% 0.20/0.38  # Generated clauses                    : 66
% 0.20/0.38  # ...of the previous two non-trivial   : 65
% 0.20/0.38  # Contextual simplify-reflections      : 6
% 0.20/0.38  # Paramodulations                      : 60
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 6
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 70
% 0.20/0.38  #    Positive orientable unit clauses  : 18
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 2
% 0.20/0.38  #    Non-unit-clauses                  : 50
% 0.20/0.38  # Current number of unprocessed clauses: 17
% 0.20/0.38  # ...number of literals in the above   : 60
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 35
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 1402
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 176
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 10
% 0.20/0.38  # Unit Clause-clause subsumption calls : 289
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 8
% 0.20/0.38  # BW rewrite match successes           : 1
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 5627
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.036 s
% 0.20/0.38  # System time              : 0.005 s
% 0.20/0.38  # Total time               : 0.040 s
% 0.20/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
