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
% DateTime   : Thu Dec  3 11:15:44 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 861 expanded)
%              Number of clauses        :   57 ( 333 expanded)
%              Number of leaves         :   15 ( 239 expanded)
%              Depth                    :   14
%              Number of atoms          :  347 (2828 expanded)
%              Number of equality atoms :   36 ( 465 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_yellow_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( v2_lattice3(k2_yellow_1(X1))
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
               => r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),k3_xboole_0(X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_1)).

fof(t24_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r1_orders_2(X1,X2,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

fof(t1_yellow_1,axiom,(
    ! [X1] :
      ( u1_struct_0(k2_yellow_1(X1)) = X1
      & u1_orders_2(k2_yellow_1(X1)) = k1_yellow_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

fof(dt_k2_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & l1_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(fc5_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & v3_orders_2(k2_yellow_1(X1))
      & v4_orders_2(k2_yellow_1(X1))
      & v5_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

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

fof(redefinition_k12_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(t25_yellow_0,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( X2 = k12_lattice3(X1,X2,X3)
              <=> r3_orders_2(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_yellow_0)).

fof(cc2_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v2_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

fof(t15_lattice3,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => k11_lattice3(X1,X2,X3) = k11_lattice3(X1,X3,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_lattice3)).

fof(dt_k11_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_lattice3)).

fof(t3_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
             => ( r3_orders_2(k2_yellow_1(X1),X2,X3)
              <=> r1_tarski(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

fof(t16_lattice3,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( v4_orders_2(X1)
                   => k11_lattice3(X1,k11_lattice3(X1,X2,X3),X4) = k11_lattice3(X1,X2,k11_lattice3(X1,X3,X4)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_lattice3)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ( v2_lattice3(k2_yellow_1(X1))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),k3_xboole_0(X2,X3)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t7_yellow_1])).

fof(c_0_16,plain,(
    ! [X13,X14] :
      ( v2_struct_0(X13)
      | ~ v3_orders_2(X13)
      | ~ l1_orders_2(X13)
      | ~ m1_subset_1(X14,u1_struct_0(X13))
      | r1_orders_2(X13,X14,X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_orders_2])])])])).

fof(c_0_17,plain,(
    ! [X34] :
      ( u1_struct_0(k2_yellow_1(X34)) = X34
      & u1_orders_2(k2_yellow_1(X34)) = k1_yellow_1(X34) ) ),
    inference(variable_rename,[status(thm)],[t1_yellow_1])).

fof(c_0_18,plain,(
    ! [X32] :
      ( v1_orders_2(k2_yellow_1(X32))
      & l1_orders_2(k2_yellow_1(X32)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

fof(c_0_19,plain,(
    ! [X33] :
      ( v1_orders_2(k2_yellow_1(X33))
      & v3_orders_2(k2_yellow_1(X33))
      & v4_orders_2(k2_yellow_1(X33))
      & v5_orders_2(k2_yellow_1(X33)) ) ),
    inference(variable_rename,[status(thm)],[fc5_yellow_1])).

fof(c_0_20,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    & v2_lattice3(k2_yellow_1(esk1_0))
    & m1_subset_1(esk2_0,u1_struct_0(k2_yellow_1(esk1_0)))
    & m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk1_0)))
    & ~ r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),k3_xboole_0(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

fof(c_0_21,plain,(
    ! [X10,X11,X12] :
      ( ( ~ r3_orders_2(X10,X11,X12)
        | r1_orders_2(X10,X11,X12)
        | v2_struct_0(X10)
        | ~ v3_orders_2(X10)
        | ~ l1_orders_2(X10)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ m1_subset_1(X12,u1_struct_0(X10)) )
      & ( ~ r1_orders_2(X10,X11,X12)
        | r3_orders_2(X10,X11,X12)
        | v2_struct_0(X10)
        | ~ v3_orders_2(X10)
        | ~ l1_orders_2(X10)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ m1_subset_1(X12,u1_struct_0(X10)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_22,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( u1_struct_0(k2_yellow_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( l1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( v3_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(k2_yellow_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( r3_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( r1_orders_2(k2_yellow_1(X1),X2,X2)
    | v2_struct_0(k2_yellow_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25])])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk3_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_26,c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_27,c_0_23])).

fof(c_0_32,plain,(
    ! [X19,X20,X21] :
      ( ~ v5_orders_2(X19)
      | ~ v2_lattice3(X19)
      | ~ l1_orders_2(X19)
      | ~ m1_subset_1(X20,u1_struct_0(X19))
      | ~ m1_subset_1(X21,u1_struct_0(X19))
      | k12_lattice3(X19,X20,X21) = k11_lattice3(X19,X20,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).

fof(c_0_33,plain,(
    ! [X29,X30,X31] :
      ( ( X30 != k12_lattice3(X29,X30,X31)
        | r3_orders_2(X29,X30,X31)
        | ~ m1_subset_1(X31,u1_struct_0(X29))
        | ~ m1_subset_1(X30,u1_struct_0(X29))
        | ~ v3_orders_2(X29)
        | ~ v5_orders_2(X29)
        | ~ v2_lattice3(X29)
        | ~ l1_orders_2(X29) )
      & ( ~ r3_orders_2(X29,X30,X31)
        | X30 = k12_lattice3(X29,X30,X31)
        | ~ m1_subset_1(X31,u1_struct_0(X29))
        | ~ m1_subset_1(X30,u1_struct_0(X29))
        | ~ v3_orders_2(X29)
        | ~ v5_orders_2(X29)
        | ~ v2_lattice3(X29)
        | ~ l1_orders_2(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_yellow_0])])])])).

fof(c_0_34,plain,(
    ! [X15] :
      ( ~ l1_orders_2(X15)
      | ~ v2_lattice3(X15)
      | ~ v2_struct_0(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).

cnf(c_0_35,plain,
    ( r3_orders_2(k2_yellow_1(X1),X2,X3)
    | v2_struct_0(k2_yellow_1(X1))
    | ~ r1_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_23]),c_0_24]),c_0_25])])).

cnf(c_0_36,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk1_0),esk3_0,esk3_0)
    | v2_struct_0(k2_yellow_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk1_0),esk2_0,esk2_0)
    | v2_struct_0(k2_yellow_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_31])).

cnf(c_0_38,plain,
    ( k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( X2 = k12_lattice3(X1,X2,X3)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,plain,
    ( ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk1_0),esk3_0,esk3_0)
    | v2_struct_0(k2_yellow_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_30])])).

cnf(c_0_42,negated_conjecture,
    ( v2_lattice3(k2_yellow_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_43,plain,(
    ! [X22,X23,X24] :
      ( ~ v5_orders_2(X22)
      | ~ v2_lattice3(X22)
      | ~ l1_orders_2(X22)
      | ~ m1_subset_1(X23,u1_struct_0(X22))
      | ~ m1_subset_1(X24,u1_struct_0(X22))
      | k11_lattice3(X22,X23,X24) = k11_lattice3(X22,X24,X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_lattice3])])])).

fof(c_0_44,plain,(
    ! [X16,X17,X18] :
      ( ~ l1_orders_2(X16)
      | ~ m1_subset_1(X17,u1_struct_0(X16))
      | ~ m1_subset_1(X18,u1_struct_0(X16))
      | m1_subset_1(k11_lattice3(X16,X17,X18),u1_struct_0(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_lattice3])])).

cnf(c_0_45,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk1_0),esk2_0,esk2_0)
    | v2_struct_0(k2_yellow_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_37]),c_0_31])])).

fof(c_0_46,plain,(
    ! [X35,X36,X37] :
      ( ( ~ r3_orders_2(k2_yellow_1(X35),X36,X37)
        | r1_tarski(X36,X37)
        | ~ m1_subset_1(X37,u1_struct_0(k2_yellow_1(X35)))
        | ~ m1_subset_1(X36,u1_struct_0(k2_yellow_1(X35)))
        | v1_xboole_0(X35) )
      & ( ~ r1_tarski(X36,X37)
        | r3_orders_2(k2_yellow_1(X35),X36,X37)
        | ~ m1_subset_1(X37,u1_struct_0(k2_yellow_1(X35)))
        | ~ m1_subset_1(X36,u1_struct_0(k2_yellow_1(X35)))
        | v1_xboole_0(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).

fof(c_0_47,plain,(
    ! [X25,X26,X27,X28] :
      ( ~ v5_orders_2(X25)
      | ~ v2_lattice3(X25)
      | ~ l1_orders_2(X25)
      | ~ m1_subset_1(X26,u1_struct_0(X25))
      | ~ m1_subset_1(X27,u1_struct_0(X25))
      | ~ m1_subset_1(X28,u1_struct_0(X25))
      | ~ v4_orders_2(X25)
      | k11_lattice3(X25,k11_lattice3(X25,X26,X27),X28) = k11_lattice3(X25,X26,k11_lattice3(X25,X27,X28)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_lattice3])])])).

cnf(c_0_48,plain,
    ( k11_lattice3(X1,X2,X3) = X2
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_49,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk1_0),esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_24])])).

cnf(c_0_50,plain,
    ( v5_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_51,plain,
    ( k11_lattice3(X1,X2,X3) = k11_lattice3(X1,X3,X2)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,plain,
    ( m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk1_0),esk2_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_45]),c_0_42]),c_0_24])])).

cnf(c_0_54,plain,
    ( r1_tarski(X2,X3)
    | v1_xboole_0(X1)
    | ~ r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_55,plain,
    ( r3_orders_2(X2,X1,X3)
    | X1 != k12_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v3_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_56,plain,
    ( k11_lattice3(X1,k11_lattice3(X1,X2,X3),X4) = k11_lattice3(X1,X2,k11_lattice3(X1,X3,X4))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v4_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_57,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk1_0),esk3_0,esk3_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_42]),c_0_23]),c_0_30]),c_0_24]),c_0_25])])).

cnf(c_0_58,plain,
    ( v4_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_59,plain,
    ( k11_lattice3(X1,X2,k11_lattice3(X1,X3,X4)) = k11_lattice3(X1,k11_lattice3(X1,X3,X4),X2)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk2_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_53]),c_0_50]),c_0_42]),c_0_23]),c_0_31]),c_0_24]),c_0_25])])).

fof(c_0_61,plain,(
    ! [X8,X9] : k1_setfam_1(k2_tarski(X8,X9)) = k3_xboole_0(X8,X9) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_62,plain,(
    ! [X5,X6,X7] :
      ( ~ r1_tarski(X5,X6)
      | ~ r1_tarski(X5,X7)
      | r1_tarski(X5,k3_xboole_0(X6,X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_63,plain,
    ( v1_xboole_0(X1)
    | r1_tarski(X2,X3)
    | ~ r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_23]),c_0_23])).

cnf(c_0_64,plain,
    ( r3_orders_2(X1,X2,X3)
    | k11_lattice3(X1,X2,X3) != X2
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_38])).

cnf(c_0_65,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk1_0),esk3_0,k11_lattice3(k2_yellow_1(esk1_0),esk3_0,X1)) = k11_lattice3(k2_yellow_1(esk1_0),esk3_0,X1)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58]),c_0_50]),c_0_42]),c_0_23]),c_0_23]),c_0_30]),c_0_24])])).

cnf(c_0_66,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk1_0),X1,esk2_0) = k11_lattice3(k2_yellow_1(esk1_0),esk2_0,X1)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_50]),c_0_42]),c_0_23]),c_0_23]),c_0_31]),c_0_24])])).

cnf(c_0_67,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),k3_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_68,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_70,plain,
    ( v1_xboole_0(X1)
    | r1_tarski(X2,X3)
    | k11_lattice3(k2_yellow_1(X1),X2,X3) != X2
    | ~ v2_lattice3(k2_yellow_1(X1))
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_50]),c_0_23]),c_0_23]),c_0_24]),c_0_25])])).

cnf(c_0_71,plain,
    ( k11_lattice3(k2_yellow_1(X1),X2,X3) = k11_lattice3(k2_yellow_1(X1),X3,X2)
    | ~ v2_lattice3(k2_yellow_1(X1))
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_23]),c_0_50]),c_0_24])])).

cnf(c_0_72,plain,
    ( m1_subset_1(k11_lattice3(X1,X2,k11_lattice3(X1,X3,X4)),u1_struct_0(X1))
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_56]),c_0_52])).

cnf(c_0_73,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk1_0),esk3_0,k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0)) = k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_31]),c_0_30])])).

cnf(c_0_74,plain,
    ( m1_subset_1(k11_lattice3(k2_yellow_1(X1),X2,X3),X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_23]),c_0_24])])).

cnf(c_0_75,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),k1_setfam_1(k2_tarski(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_76,plain,
    ( r1_tarski(X1,k1_setfam_1(k2_tarski(X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_69,c_0_68])).

cnf(c_0_77,plain,
    ( v1_xboole_0(X1)
    | r1_tarski(X2,X3)
    | k11_lattice3(k2_yellow_1(X1),X3,X2) != X2
    | ~ v2_lattice3(k2_yellow_1(X1))
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_78,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_23]),c_0_58]),c_0_50]),c_0_42]),c_0_23]),c_0_30]),c_0_23]),c_0_31]),c_0_24])])).

cnf(c_0_80,plain,
    ( v1_xboole_0(X1)
    | r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),X4)
    | k11_lattice3(k2_yellow_1(X1),X2,k11_lattice3(k2_yellow_1(X1),X3,X4)) != k11_lattice3(k2_yellow_1(X1),X2,X3)
    | ~ v2_lattice3(k2_yellow_1(X1))
    | ~ m1_subset_1(X4,X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_56]),c_0_58]),c_0_50]),c_0_23]),c_0_23]),c_0_23]),c_0_24])]),c_0_74])).

cnf(c_0_81,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),esk3_0)
    | ~ r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_82,negated_conjecture,
    ( r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_73]),c_0_42]),c_0_30])]),c_0_78]),c_0_79])])).

cnf(c_0_83,plain,
    ( v1_xboole_0(X1)
    | r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),X4)
    | k11_lattice3(k2_yellow_1(X1),X2,k11_lattice3(k2_yellow_1(X1),X4,X3)) != k11_lattice3(k2_yellow_1(X1),X2,X3)
    | ~ v2_lattice3(k2_yellow_1(X1))
    | ~ m1_subset_1(X4,X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_71])).

cnf(c_0_84,negated_conjecture,
    ( k11_lattice3(k2_yellow_1(esk1_0),esk2_0,k11_lattice3(k2_yellow_1(esk1_0),esk2_0,X1)) = k11_lattice3(k2_yellow_1(esk1_0),esk2_0,X1)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_60]),c_0_58]),c_0_50]),c_0_42]),c_0_23]),c_0_23]),c_0_31]),c_0_24])])).

cnf(c_0_85,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_82])])).

cnf(c_0_86,negated_conjecture,
    ( r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,X1),esk2_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_42]),c_0_31])]),c_0_78])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_30])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:05:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.47  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.19/0.47  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.19/0.47  #
% 0.19/0.47  # Preprocessing time       : 0.054 s
% 0.19/0.47  
% 0.19/0.47  # Proof found!
% 0.19/0.47  # SZS status Theorem
% 0.19/0.47  # SZS output start CNFRefutation
% 0.19/0.47  fof(t7_yellow_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>(v2_lattice3(k2_yellow_1(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),k3_xboole_0(X2,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_yellow_1)).
% 0.19/0.47  fof(t24_orders_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r1_orders_2(X1,X2,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_orders_2)).
% 0.19/0.47  fof(t1_yellow_1, axiom, ![X1]:(u1_struct_0(k2_yellow_1(X1))=X1&u1_orders_2(k2_yellow_1(X1))=k1_yellow_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 0.19/0.47  fof(dt_k2_yellow_1, axiom, ![X1]:(v1_orders_2(k2_yellow_1(X1))&l1_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 0.19/0.47  fof(fc5_yellow_1, axiom, ![X1]:(((v1_orders_2(k2_yellow_1(X1))&v3_orders_2(k2_yellow_1(X1)))&v4_orders_2(k2_yellow_1(X1)))&v5_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow_1)).
% 0.19/0.47  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 0.19/0.47  fof(redefinition_k12_lattice3, axiom, ![X1, X2, X3]:(((((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k12_lattice3(X1,X2,X3)=k11_lattice3(X1,X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 0.19/0.47  fof(t25_yellow_0, axiom, ![X1]:((((v3_orders_2(X1)&v5_orders_2(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X2=k12_lattice3(X1,X2,X3)<=>r3_orders_2(X1,X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_yellow_0)).
% 0.19/0.47  fof(cc2_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v2_lattice3(X1)=>~(v2_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_lattice3)).
% 0.19/0.47  fof(t15_lattice3, axiom, ![X1]:(((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k11_lattice3(X1,X2,X3)=k11_lattice3(X1,X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_lattice3)).
% 0.19/0.47  fof(dt_k11_lattice3, axiom, ![X1, X2, X3]:(((l1_orders_2(X1)&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k11_lattice3)).
% 0.19/0.47  fof(t3_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>(r3_orders_2(k2_yellow_1(X1),X2,X3)<=>r1_tarski(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_yellow_1)).
% 0.19/0.47  fof(t16_lattice3, axiom, ![X1]:(((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(v4_orders_2(X1)=>k11_lattice3(X1,k11_lattice3(X1,X2,X3),X4)=k11_lattice3(X1,X2,k11_lattice3(X1,X3,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_lattice3)).
% 0.19/0.47  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.19/0.47  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.19/0.47  fof(c_0_15, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>(v2_lattice3(k2_yellow_1(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),k3_xboole_0(X2,X3))))))), inference(assume_negation,[status(cth)],[t7_yellow_1])).
% 0.19/0.47  fof(c_0_16, plain, ![X13, X14]:(v2_struct_0(X13)|~v3_orders_2(X13)|~l1_orders_2(X13)|(~m1_subset_1(X14,u1_struct_0(X13))|r1_orders_2(X13,X14,X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_orders_2])])])])).
% 0.19/0.47  fof(c_0_17, plain, ![X34]:(u1_struct_0(k2_yellow_1(X34))=X34&u1_orders_2(k2_yellow_1(X34))=k1_yellow_1(X34)), inference(variable_rename,[status(thm)],[t1_yellow_1])).
% 0.19/0.47  fof(c_0_18, plain, ![X32]:(v1_orders_2(k2_yellow_1(X32))&l1_orders_2(k2_yellow_1(X32))), inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).
% 0.19/0.47  fof(c_0_19, plain, ![X33]:(((v1_orders_2(k2_yellow_1(X33))&v3_orders_2(k2_yellow_1(X33)))&v4_orders_2(k2_yellow_1(X33)))&v5_orders_2(k2_yellow_1(X33))), inference(variable_rename,[status(thm)],[fc5_yellow_1])).
% 0.19/0.47  fof(c_0_20, negated_conjecture, (~v1_xboole_0(esk1_0)&(v2_lattice3(k2_yellow_1(esk1_0))&(m1_subset_1(esk2_0,u1_struct_0(k2_yellow_1(esk1_0)))&(m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk1_0)))&~r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),k3_xboole_0(esk2_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).
% 0.19/0.47  fof(c_0_21, plain, ![X10, X11, X12]:((~r3_orders_2(X10,X11,X12)|r1_orders_2(X10,X11,X12)|(v2_struct_0(X10)|~v3_orders_2(X10)|~l1_orders_2(X10)|~m1_subset_1(X11,u1_struct_0(X10))|~m1_subset_1(X12,u1_struct_0(X10))))&(~r1_orders_2(X10,X11,X12)|r3_orders_2(X10,X11,X12)|(v2_struct_0(X10)|~v3_orders_2(X10)|~l1_orders_2(X10)|~m1_subset_1(X11,u1_struct_0(X10))|~m1_subset_1(X12,u1_struct_0(X10))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.19/0.47  cnf(c_0_22, plain, (v2_struct_0(X1)|r1_orders_2(X1,X2,X2)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.47  cnf(c_0_23, plain, (u1_struct_0(k2_yellow_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.47  cnf(c_0_24, plain, (l1_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.47  cnf(c_0_25, plain, (v3_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.47  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.47  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(k2_yellow_1(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.47  cnf(c_0_28, plain, (r3_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.47  cnf(c_0_29, plain, (r1_orders_2(k2_yellow_1(X1),X2,X2)|v2_struct_0(k2_yellow_1(X1))|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25])])).
% 0.19/0.47  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk3_0,esk1_0)), inference(rw,[status(thm)],[c_0_26, c_0_23])).
% 0.19/0.47  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk2_0,esk1_0)), inference(rw,[status(thm)],[c_0_27, c_0_23])).
% 0.19/0.47  fof(c_0_32, plain, ![X19, X20, X21]:(~v5_orders_2(X19)|~v2_lattice3(X19)|~l1_orders_2(X19)|~m1_subset_1(X20,u1_struct_0(X19))|~m1_subset_1(X21,u1_struct_0(X19))|k12_lattice3(X19,X20,X21)=k11_lattice3(X19,X20,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).
% 0.19/0.47  fof(c_0_33, plain, ![X29, X30, X31]:((X30!=k12_lattice3(X29,X30,X31)|r3_orders_2(X29,X30,X31)|~m1_subset_1(X31,u1_struct_0(X29))|~m1_subset_1(X30,u1_struct_0(X29))|(~v3_orders_2(X29)|~v5_orders_2(X29)|~v2_lattice3(X29)|~l1_orders_2(X29)))&(~r3_orders_2(X29,X30,X31)|X30=k12_lattice3(X29,X30,X31)|~m1_subset_1(X31,u1_struct_0(X29))|~m1_subset_1(X30,u1_struct_0(X29))|(~v3_orders_2(X29)|~v5_orders_2(X29)|~v2_lattice3(X29)|~l1_orders_2(X29)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_yellow_0])])])])).
% 0.19/0.47  fof(c_0_34, plain, ![X15]:(~l1_orders_2(X15)|(~v2_lattice3(X15)|~v2_struct_0(X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).
% 0.19/0.47  cnf(c_0_35, plain, (r3_orders_2(k2_yellow_1(X1),X2,X3)|v2_struct_0(k2_yellow_1(X1))|~r1_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_23]), c_0_24]), c_0_25])])).
% 0.19/0.47  cnf(c_0_36, negated_conjecture, (r1_orders_2(k2_yellow_1(esk1_0),esk3_0,esk3_0)|v2_struct_0(k2_yellow_1(esk1_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.47  cnf(c_0_37, negated_conjecture, (r1_orders_2(k2_yellow_1(esk1_0),esk2_0,esk2_0)|v2_struct_0(k2_yellow_1(esk1_0))), inference(spm,[status(thm)],[c_0_29, c_0_31])).
% 0.19/0.47  cnf(c_0_38, plain, (k12_lattice3(X1,X2,X3)=k11_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.47  cnf(c_0_39, plain, (X2=k12_lattice3(X1,X2,X3)|~r3_orders_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.47  cnf(c_0_40, plain, (~l1_orders_2(X1)|~v2_lattice3(X1)|~v2_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.47  cnf(c_0_41, negated_conjecture, (r3_orders_2(k2_yellow_1(esk1_0),esk3_0,esk3_0)|v2_struct_0(k2_yellow_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_30])])).
% 0.19/0.47  cnf(c_0_42, negated_conjecture, (v2_lattice3(k2_yellow_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.47  fof(c_0_43, plain, ![X22, X23, X24]:(~v5_orders_2(X22)|~v2_lattice3(X22)|~l1_orders_2(X22)|(~m1_subset_1(X23,u1_struct_0(X22))|(~m1_subset_1(X24,u1_struct_0(X22))|k11_lattice3(X22,X23,X24)=k11_lattice3(X22,X24,X23)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_lattice3])])])).
% 0.19/0.47  fof(c_0_44, plain, ![X16, X17, X18]:(~l1_orders_2(X16)|~m1_subset_1(X17,u1_struct_0(X16))|~m1_subset_1(X18,u1_struct_0(X16))|m1_subset_1(k11_lattice3(X16,X17,X18),u1_struct_0(X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_lattice3])])).
% 0.19/0.47  cnf(c_0_45, negated_conjecture, (r3_orders_2(k2_yellow_1(esk1_0),esk2_0,esk2_0)|v2_struct_0(k2_yellow_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_37]), c_0_31])])).
% 0.19/0.47  fof(c_0_46, plain, ![X35, X36, X37]:((~r3_orders_2(k2_yellow_1(X35),X36,X37)|r1_tarski(X36,X37)|~m1_subset_1(X37,u1_struct_0(k2_yellow_1(X35)))|~m1_subset_1(X36,u1_struct_0(k2_yellow_1(X35)))|v1_xboole_0(X35))&(~r1_tarski(X36,X37)|r3_orders_2(k2_yellow_1(X35),X36,X37)|~m1_subset_1(X37,u1_struct_0(k2_yellow_1(X35)))|~m1_subset_1(X36,u1_struct_0(k2_yellow_1(X35)))|v1_xboole_0(X35))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).
% 0.19/0.47  fof(c_0_47, plain, ![X25, X26, X27, X28]:(~v5_orders_2(X25)|~v2_lattice3(X25)|~l1_orders_2(X25)|(~m1_subset_1(X26,u1_struct_0(X25))|(~m1_subset_1(X27,u1_struct_0(X25))|(~m1_subset_1(X28,u1_struct_0(X25))|(~v4_orders_2(X25)|k11_lattice3(X25,k11_lattice3(X25,X26,X27),X28)=k11_lattice3(X25,X26,k11_lattice3(X25,X27,X28))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_lattice3])])])).
% 0.19/0.47  cnf(c_0_48, plain, (k11_lattice3(X1,X2,X3)=X2|~v5_orders_2(X1)|~v2_lattice3(X1)|~r3_orders_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)|~v3_orders_2(X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.47  cnf(c_0_49, negated_conjecture, (r3_orders_2(k2_yellow_1(esk1_0),esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42]), c_0_24])])).
% 0.19/0.47  cnf(c_0_50, plain, (v5_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.47  cnf(c_0_51, plain, (k11_lattice3(X1,X2,X3)=k11_lattice3(X1,X3,X2)|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.47  cnf(c_0_52, plain, (m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.47  cnf(c_0_53, negated_conjecture, (r3_orders_2(k2_yellow_1(esk1_0),esk2_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_45]), c_0_42]), c_0_24])])).
% 0.19/0.47  cnf(c_0_54, plain, (r1_tarski(X2,X3)|v1_xboole_0(X1)|~r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.47  cnf(c_0_55, plain, (r3_orders_2(X2,X1,X3)|X1!=k12_lattice3(X2,X1,X3)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~v3_orders_2(X2)|~v5_orders_2(X2)|~v2_lattice3(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.47  cnf(c_0_56, plain, (k11_lattice3(X1,k11_lattice3(X1,X2,X3),X4)=k11_lattice3(X1,X2,k11_lattice3(X1,X3,X4))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~v4_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.47  cnf(c_0_57, negated_conjecture, (k11_lattice3(k2_yellow_1(esk1_0),esk3_0,esk3_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_42]), c_0_23]), c_0_30]), c_0_24]), c_0_25])])).
% 0.19/0.47  cnf(c_0_58, plain, (v4_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.47  cnf(c_0_59, plain, (k11_lattice3(X1,X2,k11_lattice3(X1,X3,X4))=k11_lattice3(X1,k11_lattice3(X1,X3,X4),X2)|~v5_orders_2(X1)|~v2_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.47  cnf(c_0_60, negated_conjecture, (k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk2_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_53]), c_0_50]), c_0_42]), c_0_23]), c_0_31]), c_0_24]), c_0_25])])).
% 0.19/0.47  fof(c_0_61, plain, ![X8, X9]:k1_setfam_1(k2_tarski(X8,X9))=k3_xboole_0(X8,X9), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.19/0.47  fof(c_0_62, plain, ![X5, X6, X7]:(~r1_tarski(X5,X6)|~r1_tarski(X5,X7)|r1_tarski(X5,k3_xboole_0(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.19/0.47  cnf(c_0_63, plain, (v1_xboole_0(X1)|r1_tarski(X2,X3)|~r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_23]), c_0_23])).
% 0.19/0.47  cnf(c_0_64, plain, (r3_orders_2(X1,X2,X3)|k11_lattice3(X1,X2,X3)!=X2|~v5_orders_2(X1)|~v2_lattice3(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)|~v3_orders_2(X1)), inference(spm,[status(thm)],[c_0_55, c_0_38])).
% 0.19/0.47  cnf(c_0_65, negated_conjecture, (k11_lattice3(k2_yellow_1(esk1_0),esk3_0,k11_lattice3(k2_yellow_1(esk1_0),esk3_0,X1))=k11_lattice3(k2_yellow_1(esk1_0),esk3_0,X1)|~m1_subset_1(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58]), c_0_50]), c_0_42]), c_0_23]), c_0_23]), c_0_30]), c_0_24])])).
% 0.19/0.47  cnf(c_0_66, negated_conjecture, (k11_lattice3(k2_yellow_1(esk1_0),X1,esk2_0)=k11_lattice3(k2_yellow_1(esk1_0),esk2_0,X1)|~m1_subset_1(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_50]), c_0_42]), c_0_23]), c_0_23]), c_0_31]), c_0_24])])).
% 0.19/0.47  cnf(c_0_67, negated_conjecture, (~r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),k3_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.47  cnf(c_0_68, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.47  cnf(c_0_69, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.19/0.47  cnf(c_0_70, plain, (v1_xboole_0(X1)|r1_tarski(X2,X3)|k11_lattice3(k2_yellow_1(X1),X2,X3)!=X2|~v2_lattice3(k2_yellow_1(X1))|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_50]), c_0_23]), c_0_23]), c_0_24]), c_0_25])])).
% 0.19/0.47  cnf(c_0_71, plain, (k11_lattice3(k2_yellow_1(X1),X2,X3)=k11_lattice3(k2_yellow_1(X1),X3,X2)|~v2_lattice3(k2_yellow_1(X1))|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_23]), c_0_50]), c_0_24])])).
% 0.19/0.47  cnf(c_0_72, plain, (m1_subset_1(k11_lattice3(X1,X2,k11_lattice3(X1,X3,X4)),u1_struct_0(X1))|~v4_orders_2(X1)|~v5_orders_2(X1)|~v2_lattice3(X1)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_56]), c_0_52])).
% 0.19/0.47  cnf(c_0_73, negated_conjecture, (k11_lattice3(k2_yellow_1(esk1_0),esk3_0,k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0))=k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_31]), c_0_30])])).
% 0.19/0.47  cnf(c_0_74, plain, (m1_subset_1(k11_lattice3(k2_yellow_1(X1),X2,X3),X1)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_23]), c_0_24])])).
% 0.19/0.47  cnf(c_0_75, negated_conjecture, (~r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),k1_setfam_1(k2_tarski(esk2_0,esk3_0)))), inference(rw,[status(thm)],[c_0_67, c_0_68])).
% 0.19/0.47  cnf(c_0_76, plain, (r1_tarski(X1,k1_setfam_1(k2_tarski(X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_69, c_0_68])).
% 0.19/0.47  cnf(c_0_77, plain, (v1_xboole_0(X1)|r1_tarski(X2,X3)|k11_lattice3(k2_yellow_1(X1),X3,X2)!=X2|~v2_lattice3(k2_yellow_1(X1))|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.19/0.47  cnf(c_0_78, negated_conjecture, (~v1_xboole_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.47  cnf(c_0_79, negated_conjecture, (m1_subset_1(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_23]), c_0_58]), c_0_50]), c_0_42]), c_0_23]), c_0_30]), c_0_23]), c_0_31]), c_0_24])])).
% 0.19/0.47  cnf(c_0_80, plain, (v1_xboole_0(X1)|r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),X4)|k11_lattice3(k2_yellow_1(X1),X2,k11_lattice3(k2_yellow_1(X1),X3,X4))!=k11_lattice3(k2_yellow_1(X1),X2,X3)|~v2_lattice3(k2_yellow_1(X1))|~m1_subset_1(X4,X1)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_56]), c_0_58]), c_0_50]), c_0_23]), c_0_23]), c_0_23]), c_0_24])]), c_0_74])).
% 0.19/0.47  cnf(c_0_81, negated_conjecture, (~r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),esk3_0)|~r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),esk2_0)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.19/0.47  cnf(c_0_82, negated_conjecture, (r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_73]), c_0_42]), c_0_30])]), c_0_78]), c_0_79])])).
% 0.19/0.47  cnf(c_0_83, plain, (v1_xboole_0(X1)|r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),X4)|k11_lattice3(k2_yellow_1(X1),X2,k11_lattice3(k2_yellow_1(X1),X4,X3))!=k11_lattice3(k2_yellow_1(X1),X2,X3)|~v2_lattice3(k2_yellow_1(X1))|~m1_subset_1(X4,X1)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(spm,[status(thm)],[c_0_80, c_0_71])).
% 0.19/0.47  cnf(c_0_84, negated_conjecture, (k11_lattice3(k2_yellow_1(esk1_0),esk2_0,k11_lattice3(k2_yellow_1(esk1_0),esk2_0,X1))=k11_lattice3(k2_yellow_1(esk1_0),esk2_0,X1)|~m1_subset_1(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_60]), c_0_58]), c_0_50]), c_0_42]), c_0_23]), c_0_23]), c_0_31]), c_0_24])])).
% 0.19/0.47  cnf(c_0_85, negated_conjecture, (~r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_82])])).
% 0.19/0.47  cnf(c_0_86, negated_conjecture, (r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,X1),esk2_0)|~m1_subset_1(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_42]), c_0_31])]), c_0_78])).
% 0.19/0.47  cnf(c_0_87, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_30])]), ['proof']).
% 0.19/0.47  # SZS output end CNFRefutation
% 0.19/0.47  # Proof object total steps             : 88
% 0.19/0.47  # Proof object clause steps            : 57
% 0.19/0.47  # Proof object formula steps           : 31
% 0.19/0.47  # Proof object conjectures             : 29
% 0.19/0.47  # Proof object clause conjectures      : 26
% 0.19/0.47  # Proof object formula conjectures     : 3
% 0.19/0.47  # Proof object initial clauses used    : 22
% 0.19/0.47  # Proof object initial formulas used   : 15
% 0.19/0.47  # Proof object generating inferences   : 29
% 0.19/0.47  # Proof object simplifying inferences  : 106
% 0.19/0.47  # Training examples: 0 positive, 0 negative
% 0.19/0.47  # Parsed axioms                        : 15
% 0.19/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.47  # Initial clauses                      : 27
% 0.19/0.47  # Removed in clause preprocessing      : 2
% 0.19/0.47  # Initial clauses in saturation        : 25
% 0.19/0.47  # Processed clauses                    : 205
% 0.19/0.47  # ...of these trivial                  : 5
% 0.19/0.47  # ...subsumed                          : 96
% 0.19/0.47  # ...remaining for further processing  : 104
% 0.19/0.47  # Other redundant clauses eliminated   : 0
% 0.19/0.47  # Clauses deleted for lack of memory   : 0
% 0.19/0.47  # Backward-subsumed                    : 0
% 0.19/0.47  # Backward-rewritten                   : 5
% 0.19/0.47  # Generated clauses                    : 1472
% 0.19/0.47  # ...of the previous two non-trivial   : 1358
% 0.19/0.47  # Contextual simplify-reflections      : 7
% 0.19/0.47  # Paramodulations                      : 1472
% 0.19/0.47  # Factorizations                       : 0
% 0.19/0.47  # Equation resolutions                 : 0
% 0.19/0.47  # Propositional unsat checks           : 0
% 0.19/0.47  #    Propositional check models        : 0
% 0.19/0.47  #    Propositional check unsatisfiable : 0
% 0.19/0.47  #    Propositional clauses             : 0
% 0.19/0.47  #    Propositional clauses after purity: 0
% 0.19/0.47  #    Propositional unsat core size     : 0
% 0.19/0.47  #    Propositional preprocessing time  : 0.000
% 0.19/0.47  #    Propositional encoding time       : 0.000
% 0.19/0.47  #    Propositional solver time         : 0.000
% 0.19/0.47  #    Success case prop preproc time    : 0.000
% 0.19/0.47  #    Success case prop encoding time   : 0.000
% 0.19/0.47  #    Success case prop solver time     : 0.000
% 0.19/0.47  # Current number of processed clauses  : 99
% 0.19/0.47  #    Positive orientable unit clauses  : 18
% 0.19/0.47  #    Positive unorientable unit clauses: 0
% 0.19/0.47  #    Negative unit clauses             : 7
% 0.19/0.47  #    Non-unit-clauses                  : 74
% 0.19/0.47  # Current number of unprocessed clauses: 1178
% 0.19/0.47  # ...number of literals in the above   : 7827
% 0.19/0.47  # Current number of archived formulas  : 0
% 0.19/0.47  # Current number of archived clauses   : 7
% 0.19/0.47  # Clause-clause subsumption calls (NU) : 857
% 0.19/0.47  # Rec. Clause-clause subsumption calls : 251
% 0.19/0.47  # Non-unit clause-clause subsumptions  : 70
% 0.19/0.47  # Unit Clause-clause subsumption calls : 38
% 0.19/0.47  # Rewrite failures with RHS unbound    : 0
% 0.19/0.47  # BW rewrite match attempts            : 8
% 0.19/0.47  # BW rewrite match successes           : 4
% 0.19/0.47  # Condensation attempts                : 0
% 0.19/0.47  # Condensation successes               : 0
% 0.19/0.47  # Termbank termtop insertions          : 56622
% 0.19/0.48  
% 0.19/0.48  # -------------------------------------------------
% 0.19/0.48  # User time                : 0.121 s
% 0.19/0.48  # System time              : 0.009 s
% 0.19/0.48  # Total time               : 0.131 s
% 0.19/0.48  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
