%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : lattice3__t43_lattice3.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:55 EDT 2019

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 503 expanded)
%              Number of clauses        :   56 ( 174 expanded)
%              Number of leaves         :   16 ( 123 expanded)
%              Depth                    :   12
%              Number of atoms          :  397 (2905 expanded)
%              Number of equality atoms :   44 ( 575 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_l1_lattices,axiom,(
    ! [X1] :
      ( l1_lattices(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t43_lattice3.p',dt_l1_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t43_lattice3.p',dt_l3_lattices)).

fof(t43_lattice3,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( k15_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2
            & k16_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t43_lattice3.p',t43_lattice3)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t43_lattice3.p',fc2_struct_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t43_lattice3.p',t2_subset)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t43_lattice3.p',t7_boole)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t43_lattice3.p',redefinition_k6_domain_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t43_lattice3.p',d1_tarski)).

fof(d17_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( r4_lattice3(X1,X2,X3)
            <=> ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r2_hidden(X4,X3)
                   => r1_lattices(X1,X4,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t43_lattice3.p',d17_lattice3)).

fof(t42_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( r2_hidden(X2,X3)
                & r3_lattice3(X1,X2,X3) )
             => k16_lattice3(X1,X3) = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t43_lattice3.p',t42_lattice3)).

fof(cc1_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1) )
       => ( ~ v2_struct_0(X1)
          & v4_lattices(X1)
          & v5_lattices(X1)
          & v6_lattices(X1)
          & v7_lattices(X1)
          & v8_lattices(X1)
          & v9_lattices(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t43_lattice3.p',cc1_lattices)).

fof(dt_k15_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t43_lattice3.p',dt_k15_lattice3)).

fof(d16_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( r3_lattice3(X1,X2,X3)
            <=> ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r2_hidden(X4,X3)
                   => r1_lattices(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t43_lattice3.p',d16_lattice3)).

fof(t41_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( r2_hidden(X2,X3)
                & r4_lattice3(X1,X2,X3) )
             => k15_lattice3(X1,X3) = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t43_lattice3.p',t41_lattice3)).

fof(redefinition_r3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & v8_lattices(X1)
        & v9_lattices(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_lattices(X1,X2,X3)
      <=> r1_lattices(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t43_lattice3.p',redefinition_r3_lattices)).

fof(reflexivity_r3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & v8_lattices(X1)
        & v9_lattices(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => r3_lattices(X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t43_lattice3.p',reflexivity_r3_lattices)).

fof(c_0_16,plain,(
    ! [X34] :
      ( ~ l1_lattices(X34)
      | l1_struct_0(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_lattices])])).

fof(c_0_17,plain,(
    ! [X36] :
      ( ( l1_lattices(X36)
        | ~ l3_lattices(X36) )
      & ( l2_lattices(X36)
        | ~ l3_lattices(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v4_lattice3(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( k15_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2
              & k16_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t43_lattice3])).

fof(c_0_19,plain,(
    ! [X84] :
      ( v2_struct_0(X84)
      | ~ l1_struct_0(X84)
      | ~ v1_xboole_0(u1_struct_0(X84)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_20,plain,
    ( l1_struct_0(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X59,X60] :
      ( ~ m1_subset_1(X59,X60)
      | v1_xboole_0(X60)
      | r2_hidden(X59,X60) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v10_lattices(esk1_0)
    & v4_lattice3(esk1_0)
    & l3_lattices(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & ( k15_lattice3(esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0)) != esk2_0
      | k16_lattice3(esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0)) != esk2_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).

cnf(c_0_24,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( l1_struct_0(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_28,plain,(
    ! [X79,X80] :
      ( ~ r2_hidden(X79,X80)
      | ~ v1_xboole_0(X80) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_29,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | r2_hidden(esk2_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( l3_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_33,plain,(
    ! [X49,X50] :
      ( v1_xboole_0(X49)
      | ~ m1_subset_1(X50,X49)
      | k6_domain_1(X49,X50) = k1_tarski(X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

cnf(c_0_34,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk2_0,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])]),c_0_32])).

fof(c_0_36,plain,(
    ! [X21,X22,X23,X24,X25,X26] :
      ( ( ~ r2_hidden(X23,X22)
        | X23 = X21
        | X22 != k1_tarski(X21) )
      & ( X24 != X21
        | r2_hidden(X24,X22)
        | X22 != k1_tarski(X21) )
      & ( ~ r2_hidden(esk5_2(X25,X26),X26)
        | esk5_2(X25,X26) != X25
        | X26 = k1_tarski(X25) )
      & ( r2_hidden(esk5_2(X25,X26),X26)
        | esk5_2(X25,X26) = X25
        | X26 = k1_tarski(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_37,plain,(
    ! [X15,X16,X17,X18,X19] :
      ( ( ~ r4_lattice3(X15,X16,X17)
        | ~ m1_subset_1(X18,u1_struct_0(X15))
        | ~ r2_hidden(X18,X17)
        | r1_lattices(X15,X18,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ l3_lattices(X15) )
      & ( m1_subset_1(esk4_3(X15,X16,X19),u1_struct_0(X15))
        | r4_lattice3(X15,X16,X19)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ l3_lattices(X15) )
      & ( r2_hidden(esk4_3(X15,X16,X19),X19)
        | r4_lattice3(X15,X16,X19)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ l3_lattices(X15) )
      & ( ~ r1_lattices(X15,esk4_3(X15,X16,X19),X16)
        | r4_lattice3(X15,X16,X19)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ l3_lattices(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).

cnf(c_0_38,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

fof(c_0_40,plain,(
    ! [X69,X70,X71] :
      ( v2_struct_0(X69)
      | ~ v10_lattices(X69)
      | ~ v4_lattice3(X69)
      | ~ l3_lattices(X69)
      | ~ m1_subset_1(X70,u1_struct_0(X69))
      | ~ r2_hidden(X70,X71)
      | ~ r3_lattice3(X69,X70,X71)
      | k16_lattice3(X69,X71) = X70 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_lattice3])])])])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X3)
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_43,plain,(
    ! [X83] :
      ( ( ~ v2_struct_0(X83)
        | v2_struct_0(X83)
        | ~ v10_lattices(X83)
        | ~ l3_lattices(X83) )
      & ( v4_lattices(X83)
        | v2_struct_0(X83)
        | ~ v10_lattices(X83)
        | ~ l3_lattices(X83) )
      & ( v5_lattices(X83)
        | v2_struct_0(X83)
        | ~ v10_lattices(X83)
        | ~ l3_lattices(X83) )
      & ( v6_lattices(X83)
        | v2_struct_0(X83)
        | ~ v10_lattices(X83)
        | ~ l3_lattices(X83) )
      & ( v7_lattices(X83)
        | v2_struct_0(X83)
        | ~ v10_lattices(X83)
        | ~ l3_lattices(X83) )
      & ( v8_lattices(X83)
        | v2_struct_0(X83)
        | ~ v10_lattices(X83)
        | ~ l3_lattices(X83) )
      & ( v9_lattices(X83)
        | v2_struct_0(X83)
        | ~ v10_lattices(X83)
        | ~ l3_lattices(X83) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

fof(c_0_44,plain,(
    ! [X28,X29] :
      ( v2_struct_0(X28)
      | ~ l3_lattices(X28)
      | m1_subset_1(k15_lattice3(X28,X29),u1_struct_0(X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).

fof(c_0_45,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r3_lattice3(X9,X10,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X9))
        | ~ r2_hidden(X12,X11)
        | r1_lattices(X9,X10,X12)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | v2_struct_0(X9)
        | ~ l3_lattices(X9) )
      & ( m1_subset_1(esk3_3(X9,X10,X13),u1_struct_0(X9))
        | r3_lattice3(X9,X10,X13)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | v2_struct_0(X9)
        | ~ l3_lattices(X9) )
      & ( r2_hidden(esk3_3(X9,X10,X13),X13)
        | r3_lattice3(X9,X10,X13)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | v2_struct_0(X9)
        | ~ l3_lattices(X9) )
      & ( ~ r1_lattices(X9,X10,esk3_3(X9,X10,X13))
        | r3_lattice3(X9,X10,X13)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | v2_struct_0(X9)
        | ~ l3_lattices(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).

cnf(c_0_46,negated_conjecture,
    ( k15_lattice3(esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0)) != esk2_0
    | k16_lattice3(esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0)) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_47,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk1_0),esk2_0) = k1_tarski(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_27]),c_0_39])).

cnf(c_0_48,plain,
    ( v2_struct_0(X1)
    | k16_lattice3(X1,X3) = X2
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,X3)
    | ~ r3_lattice3(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( v4_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_50,negated_conjecture,
    ( v10_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,X2)
    | X2 != k1_tarski(X1) ),
    inference(er,[status(thm)],[c_0_41])).

fof(c_0_52,plain,(
    ! [X66,X67,X68] :
      ( v2_struct_0(X66)
      | ~ v10_lattices(X66)
      | ~ v4_lattice3(X66)
      | ~ l3_lattices(X66)
      | ~ m1_subset_1(X67,u1_struct_0(X66))
      | ~ r2_hidden(X67,X68)
      | ~ r4_lattice3(X66,X67,X68)
      | k15_lattice3(X66,X68) = X67 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t41_lattice3])])])])).

cnf(c_0_53,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_54,negated_conjecture,
    ( r4_lattice3(esk1_0,esk2_0,X1)
    | r2_hidden(esk4_3(esk1_0,esk2_0,X1),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_27]),c_0_31])]),c_0_32])).

fof(c_0_55,plain,(
    ! [X51,X52,X53] :
      ( ( ~ r3_lattices(X51,X52,X53)
        | r1_lattices(X51,X52,X53)
        | v2_struct_0(X51)
        | ~ v6_lattices(X51)
        | ~ v8_lattices(X51)
        | ~ v9_lattices(X51)
        | ~ l3_lattices(X51)
        | ~ m1_subset_1(X52,u1_struct_0(X51))
        | ~ m1_subset_1(X53,u1_struct_0(X51)) )
      & ( ~ r1_lattices(X51,X52,X53)
        | r3_lattices(X51,X52,X53)
        | v2_struct_0(X51)
        | ~ v6_lattices(X51)
        | ~ v8_lattices(X51)
        | ~ v9_lattices(X51)
        | ~ l3_lattices(X51)
        | ~ m1_subset_1(X52,u1_struct_0(X51))
        | ~ m1_subset_1(X53,u1_struct_0(X51)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

cnf(c_0_56,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_57,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_58,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_59,plain,(
    ! [X54,X55,X56] :
      ( v2_struct_0(X54)
      | ~ v6_lattices(X54)
      | ~ v8_lattices(X54)
      | ~ v9_lattices(X54)
      | ~ l3_lattices(X54)
      | ~ m1_subset_1(X55,u1_struct_0(X54))
      | ~ m1_subset_1(X56,u1_struct_0(X54))
      | r3_lattices(X54,X55,X55) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_lattices])])])).

cnf(c_0_60,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_61,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X3)
    | r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_62,negated_conjecture,
    ( k15_lattice3(esk1_0,k1_tarski(esk2_0)) != esk2_0
    | k16_lattice3(esk1_0,k1_tarski(esk2_0)) != esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47]),c_0_47])).

cnf(c_0_63,negated_conjecture,
    ( k16_lattice3(esk1_0,X1) = esk2_0
    | ~ r3_lattice3(esk1_0,esk2_0,X1)
    | ~ r2_hidden(esk2_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_27]),c_0_31]),c_0_49]),c_0_50])]),c_0_32])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_65,plain,
    ( v2_struct_0(X1)
    | k15_lattice3(X1,X3) = X2
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,X3)
    | ~ r4_lattice3(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_66,negated_conjecture,
    ( esk4_3(esk1_0,esk2_0,X1) = X2
    | r4_lattice3(esk1_0,esk2_0,X1)
    | X1 != k1_tarski(X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_67,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_68,negated_conjecture,
    ( v9_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_31]),c_0_50])]),c_0_32])).

cnf(c_0_69,negated_conjecture,
    ( v8_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_31]),c_0_50])]),c_0_32])).

cnf(c_0_70,negated_conjecture,
    ( v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_31]),c_0_50])]),c_0_32])).

cnf(c_0_71,plain,
    ( v2_struct_0(X1)
    | r3_lattices(X1,X2,X2)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(k15_lattice3(esk1_0,X1),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_31]),c_0_32])).

cnf(c_0_73,negated_conjecture,
    ( r3_lattice3(esk1_0,esk2_0,X1)
    | r2_hidden(esk3_3(esk1_0,esk2_0,X1),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_27]),c_0_31])]),c_0_32])).

cnf(c_0_74,negated_conjecture,
    ( k15_lattice3(esk1_0,k1_tarski(esk2_0)) != esk2_0
    | ~ r3_lattice3(esk1_0,esk2_0,k1_tarski(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])])).

cnf(c_0_75,negated_conjecture,
    ( k15_lattice3(esk1_0,X1) = esk2_0
    | ~ r4_lattice3(esk1_0,esk2_0,X1)
    | ~ r2_hidden(esk2_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_27]),c_0_31]),c_0_49]),c_0_50])]),c_0_32])).

cnf(c_0_76,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,esk4_3(X1,X2,X3),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_77,negated_conjecture,
    ( esk4_3(esk1_0,esk2_0,k1_tarski(X1)) = X1
    | r4_lattice3(esk1_0,esk2_0,k1_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_66])).

cnf(c_0_78,negated_conjecture,
    ( r1_lattices(esk1_0,X1,esk2_0)
    | ~ r3_lattices(esk1_0,X1,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_27]),c_0_31])]),c_0_32]),c_0_68]),c_0_69]),c_0_70])])).

cnf(c_0_79,negated_conjecture,
    ( r3_lattices(esk1_0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_68]),c_0_69]),c_0_70]),c_0_31])]),c_0_32])).

cnf(c_0_80,negated_conjecture,
    ( esk3_3(esk1_0,esk2_0,X1) = X2
    | r3_lattice3(esk1_0,esk2_0,X1)
    | X1 != k1_tarski(X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_73])).

cnf(c_0_81,negated_conjecture,
    ( ~ r4_lattice3(esk1_0,esk2_0,k1_tarski(esk2_0))
    | ~ r3_lattice3(esk1_0,esk2_0,k1_tarski(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_64])])).

cnf(c_0_82,negated_conjecture,
    ( r4_lattice3(esk1_0,esk2_0,k1_tarski(X1))
    | ~ r1_lattices(esk1_0,X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_27]),c_0_31])]),c_0_32])).

cnf(c_0_83,negated_conjecture,
    ( r1_lattices(esk1_0,esk2_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_27])])).

cnf(c_0_84,plain,
    ( r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,esk3_3(X1,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_85,negated_conjecture,
    ( esk3_3(esk1_0,esk2_0,k1_tarski(X1)) = X1
    | r3_lattice3(esk1_0,esk2_0,k1_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_80])).

cnf(c_0_86,negated_conjecture,
    ( ~ r3_lattice3(esk1_0,esk2_0,k1_tarski(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_83])])).

cnf(c_0_87,negated_conjecture,
    ( r3_lattice3(esk1_0,esk2_0,k1_tarski(X1))
    | ~ r1_lattices(esk1_0,esk2_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_27]),c_0_31])]),c_0_32])).

cnf(c_0_88,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_83])]),
    [proof]).
%------------------------------------------------------------------------------
