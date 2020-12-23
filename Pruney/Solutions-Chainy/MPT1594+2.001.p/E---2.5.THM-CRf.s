%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:40 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   87 (1486 expanded)
%              Number of clauses        :   56 ( 607 expanded)
%              Number of leaves         :   15 ( 426 expanded)
%              Depth                    :   15
%              Number of atoms          :  359 (4665 expanded)
%              Number of equality atoms :   27 ( 561 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t2_yellow_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,u1_struct_0(k3_yellow_1(X1)))
         => ( r3_orders_2(k3_yellow_1(X1),X2,X3)
          <=> r1_tarski(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow_1)).

fof(free_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ! [X3,X4] :
          ( g1_orders_2(X1,X2) = g1_orders_2(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(abstractness_v1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_orders_2(X1)
       => X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(d2_yellow_1,axiom,(
    ! [X1] : k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).

fof(dt_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ( v1_orders_2(g1_orders_2(X1,X2))
        & l1_orders_2(g1_orders_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_orders_2)).

fof(d2_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => k3_lattice3(X1) = g1_orders_2(u1_struct_0(X1),k2_lattice3(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_lattice3)).

fof(fc2_lattice3,axiom,(
    ! [X1] :
      ( v3_lattices(k1_lattice3(X1))
      & v10_lattices(k1_lattice3(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_lattice3)).

fof(dt_k1_lattice3,axiom,(
    ! [X1] :
      ( v3_lattices(k1_lattice3(X1))
      & l3_lattices(k1_lattice3(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_lattice3)).

fof(fc1_lattice3,axiom,(
    ! [X1] :
      ( ~ v2_struct_0(k1_lattice3(X1))
      & v3_lattices(k1_lattice3(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_lattice3)).

fof(dt_k2_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ( v1_partfun1(k2_lattice3(X1),u1_struct_0(X1))
        & v1_relat_2(k2_lattice3(X1))
        & v4_relat_2(k2_lattice3(X1))
        & v8_relat_2(k2_lattice3(X1))
        & m1_subset_1(k2_lattice3(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_lattice3)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(d3_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k4_lattice3(X1,X2) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattice3)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

fof(t7_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r3_lattices(X1,X2,X3)
              <=> r3_orders_2(k3_lattice3(X1),k4_lattice3(X1,X2),k4_lattice3(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_lattice3)).

fof(t2_lattice3,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,u1_struct_0(k1_lattice3(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,u1_struct_0(k1_lattice3(X1)))
         => ( r1_lattices(k1_lattice3(X1),X2,X3)
          <=> r1_tarski(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_lattice3)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
       => ! [X3] :
            ( m1_subset_1(X3,u1_struct_0(k3_yellow_1(X1)))
           => ( r3_orders_2(k3_yellow_1(X1),X2,X3)
            <=> r1_tarski(X2,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t2_yellow_1])).

fof(c_0_16,plain,(
    ! [X8,X9,X10,X11] :
      ( ( X8 = X10
        | g1_orders_2(X8,X9) != g1_orders_2(X10,X11)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X8,X8))) )
      & ( X9 = X11
        | g1_orders_2(X8,X9) != g1_orders_2(X10,X11)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X8,X8))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

fof(c_0_17,plain,(
    ! [X5] :
      ( ~ l1_orders_2(X5)
      | ~ v1_orders_2(X5)
      | X5 = g1_orders_2(u1_struct_0(X5),u1_orders_2(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_orders_2])])).

fof(c_0_18,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(k3_yellow_1(esk1_0)))
    & m1_subset_1(esk3_0,u1_struct_0(k3_yellow_1(esk1_0)))
    & ( ~ r3_orders_2(k3_yellow_1(esk1_0),esk2_0,esk3_0)
      | ~ r1_tarski(esk2_0,esk3_0) )
    & ( r3_orders_2(k3_yellow_1(esk1_0),esk2_0,esk3_0)
      | r1_tarski(esk2_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_19,plain,(
    ! [X29] : k3_yellow_1(X29) = k3_lattice3(k1_lattice3(X29)) ),
    inference(variable_rename,[status(thm)],[d2_yellow_1])).

cnf(c_0_20,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ v1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X6,X7] :
      ( ( v1_orders_2(g1_orders_2(X6,X7))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X6))) )
      & ( l1_orders_2(g1_orders_2(X6,X7))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X6))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_orders_2])])])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(k3_yellow_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X16] :
      ( v2_struct_0(X16)
      | ~ v10_lattices(X16)
      | ~ l3_lattices(X16)
      | k3_lattice3(X16) = g1_orders_2(u1_struct_0(X16),k2_lattice3(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_lattice3])])])).

fof(c_0_26,plain,(
    ! [X22] :
      ( v3_lattices(k1_lattice3(X22))
      & v10_lattices(k1_lattice3(X22)) ) ),
    inference(variable_rename,[status(thm)],[fc2_lattice3])).

fof(c_0_27,plain,(
    ! [X19] :
      ( v3_lattices(k1_lattice3(X19))
      & l3_lattices(k1_lattice3(X19)) ) ),
    inference(variable_rename,[status(thm)],[dt_k1_lattice3])).

fof(c_0_28,plain,(
    ! [X21] :
      ( ~ v2_struct_0(k1_lattice3(X21))
      & v3_lattices(k1_lattice3(X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_lattice3])])).

cnf(c_0_29,plain,
    ( X1 = u1_struct_0(X2)
    | g1_orders_2(X1,X3) != X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_30,plain,
    ( l1_orders_2(g1_orders_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( v1_orders_2(g1_orders_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_32,plain,(
    ! [X20] :
      ( ( v1_partfun1(k2_lattice3(X20),u1_struct_0(X20))
        | v2_struct_0(X20)
        | ~ v10_lattices(X20)
        | ~ l3_lattices(X20) )
      & ( v1_relat_2(k2_lattice3(X20))
        | v2_struct_0(X20)
        | ~ v10_lattices(X20)
        | ~ l3_lattices(X20) )
      & ( v4_relat_2(k2_lattice3(X20))
        | v2_struct_0(X20)
        | ~ v10_lattices(X20)
        | ~ l3_lattices(X20) )
      & ( v8_relat_2(k2_lattice3(X20))
        | v2_struct_0(X20)
        | ~ v10_lattices(X20)
        | ~ l3_lattices(X20) )
      & ( m1_subset_1(k2_lattice3(X20),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X20))))
        | v2_struct_0(X20)
        | ~ v10_lattices(X20)
        | ~ l3_lattices(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_lattice3])])])])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(k3_lattice3(k1_lattice3(esk1_0)))) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_34,plain,
    ( v2_struct_0(X1)
    | k3_lattice3(X1) = g1_orders_2(u1_struct_0(X1),k2_lattice3(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( v10_lattices(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( l3_lattices(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( ~ v2_struct_0(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( u1_struct_0(g1_orders_2(X1,X2)) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_29]),c_0_30]),c_0_31])).

cnf(c_0_39,plain,
    ( m1_subset_1(k2_lattice3(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(k3_yellow_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_41,plain,(
    ! [X13,X14,X15] :
      ( ( ~ r3_lattices(X13,X14,X15)
        | r1_lattices(X13,X14,X15)
        | v2_struct_0(X13)
        | ~ v6_lattices(X13)
        | ~ v8_lattices(X13)
        | ~ v9_lattices(X13)
        | ~ l3_lattices(X13)
        | ~ m1_subset_1(X14,u1_struct_0(X13))
        | ~ m1_subset_1(X15,u1_struct_0(X13)) )
      & ( ~ r1_lattices(X13,X14,X15)
        | r3_lattices(X13,X14,X15)
        | v2_struct_0(X13)
        | ~ v6_lattices(X13)
        | ~ v8_lattices(X13)
        | ~ v9_lattices(X13)
        | ~ l3_lattices(X13)
        | ~ m1_subset_1(X14,u1_struct_0(X13))
        | ~ m1_subset_1(X15,u1_struct_0(X13)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(g1_orders_2(u1_struct_0(k1_lattice3(esk1_0)),k2_lattice3(k1_lattice3(esk1_0))))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_43,plain,
    ( u1_struct_0(g1_orders_2(u1_struct_0(X1),k2_lattice3(X1))) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

fof(c_0_44,plain,(
    ! [X17,X18] :
      ( v2_struct_0(X17)
      | ~ v10_lattices(X17)
      | ~ l3_lattices(X17)
      | ~ m1_subset_1(X18,u1_struct_0(X17))
      | k4_lattice3(X17,X18) = X18 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattice3])])])])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(k3_lattice3(k1_lattice3(esk1_0)))) ),
    inference(rw,[status(thm)],[c_0_40,c_0_24])).

cnf(c_0_46,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(k1_lattice3(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_35]),c_0_36])]),c_0_37])).

fof(c_0_48,plain,(
    ! [X12] :
      ( ( ~ v2_struct_0(X12)
        | v2_struct_0(X12)
        | ~ v10_lattices(X12)
        | ~ l3_lattices(X12) )
      & ( v4_lattices(X12)
        | v2_struct_0(X12)
        | ~ v10_lattices(X12)
        | ~ l3_lattices(X12) )
      & ( v5_lattices(X12)
        | v2_struct_0(X12)
        | ~ v10_lattices(X12)
        | ~ l3_lattices(X12) )
      & ( v6_lattices(X12)
        | v2_struct_0(X12)
        | ~ v10_lattices(X12)
        | ~ l3_lattices(X12) )
      & ( v7_lattices(X12)
        | v2_struct_0(X12)
        | ~ v10_lattices(X12)
        | ~ l3_lattices(X12) )
      & ( v8_lattices(X12)
        | v2_struct_0(X12)
        | ~ v10_lattices(X12)
        | ~ l3_lattices(X12) )
      & ( v9_lattices(X12)
        | v2_struct_0(X12)
        | ~ v10_lattices(X12)
        | ~ l3_lattices(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

fof(c_0_49,plain,(
    ! [X26,X27,X28] :
      ( ( ~ r3_lattices(X26,X27,X28)
        | r3_orders_2(k3_lattice3(X26),k4_lattice3(X26,X27),k4_lattice3(X26,X28))
        | ~ m1_subset_1(X28,u1_struct_0(X26))
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | v2_struct_0(X26)
        | ~ v10_lattices(X26)
        | ~ l3_lattices(X26) )
      & ( ~ r3_orders_2(k3_lattice3(X26),k4_lattice3(X26,X27),k4_lattice3(X26,X28))
        | r3_lattices(X26,X27,X28)
        | ~ m1_subset_1(X28,u1_struct_0(X26))
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | v2_struct_0(X26)
        | ~ v10_lattices(X26)
        | ~ l3_lattices(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_lattice3])])])])])).

cnf(c_0_50,plain,
    ( v2_struct_0(X1)
    | k4_lattice3(X1,X2) = X2
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(g1_orders_2(u1_struct_0(k1_lattice3(esk1_0)),k2_lattice3(k1_lattice3(esk1_0))))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_34]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_52,negated_conjecture,
    ( r1_lattices(k1_lattice3(esk1_0),X1,esk3_0)
    | ~ r3_lattices(k1_lattice3(esk1_0),X1,esk3_0)
    | ~ v9_lattices(k1_lattice3(esk1_0))
    | ~ v8_lattices(k1_lattice3(esk1_0))
    | ~ v6_lattices(k1_lattice3(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_36])]),c_0_37])).

cnf(c_0_53,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_54,plain,
    ( r3_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(k3_lattice3(X1),k4_lattice3(X1,X2),k4_lattice3(X1,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( k4_lattice3(k1_lattice3(esk1_0),esk3_0) = esk3_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_47]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(k1_lattice3(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_43]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_57,negated_conjecture,
    ( r1_lattices(k1_lattice3(esk1_0),X1,esk3_0)
    | ~ r3_lattices(k1_lattice3(esk1_0),X1,esk3_0)
    | ~ v8_lattices(k1_lattice3(esk1_0))
    | ~ v6_lattices(k1_lattice3(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_58,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_59,negated_conjecture,
    ( r3_lattices(k1_lattice3(esk1_0),X1,esk3_0)
    | ~ r3_orders_2(k3_lattice3(k1_lattice3(esk1_0)),k4_lattice3(k1_lattice3(esk1_0),X1),esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(esk1_0))) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_47]),c_0_35]),c_0_36])]),c_0_37]),c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( k4_lattice3(k1_lattice3(esk1_0),esk2_0) = esk2_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_56]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_61,negated_conjecture,
    ( r3_orders_2(k3_yellow_1(esk1_0),esk2_0,esk3_0)
    | r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_62,plain,
    ( r3_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_63,negated_conjecture,
    ( r1_lattices(k1_lattice3(esk1_0),X1,esk3_0)
    | ~ r3_lattices(k1_lattice3(esk1_0),X1,esk3_0)
    | ~ v6_lattices(k1_lattice3(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_64,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_65,negated_conjecture,
    ( r3_lattices(k1_lattice3(esk1_0),esk2_0,esk3_0)
    | ~ r3_orders_2(k3_lattice3(k1_lattice3(esk1_0)),esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_56]),c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0)
    | r3_orders_2(k3_lattice3(k1_lattice3(esk1_0)),esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_61,c_0_24])).

cnf(c_0_67,negated_conjecture,
    ( r3_lattices(k1_lattice3(esk1_0),X1,esk3_0)
    | ~ r1_lattices(k1_lattice3(esk1_0),X1,esk3_0)
    | ~ v9_lattices(k1_lattice3(esk1_0))
    | ~ v8_lattices(k1_lattice3(esk1_0))
    | ~ v6_lattices(k1_lattice3(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_47]),c_0_36])]),c_0_37])).

fof(c_0_68,plain,(
    ! [X23,X24,X25] :
      ( ( ~ r1_lattices(k1_lattice3(X23),X24,X25)
        | r1_tarski(X24,X25)
        | ~ m1_subset_1(X25,u1_struct_0(k1_lattice3(X23)))
        | ~ m1_subset_1(X24,u1_struct_0(k1_lattice3(X23))) )
      & ( ~ r1_tarski(X24,X25)
        | r1_lattices(k1_lattice3(X23),X24,X25)
        | ~ m1_subset_1(X25,u1_struct_0(k1_lattice3(X23)))
        | ~ m1_subset_1(X24,u1_struct_0(k1_lattice3(X23))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_lattice3])])])])).

cnf(c_0_69,negated_conjecture,
    ( r1_lattices(k1_lattice3(esk1_0),X1,esk3_0)
    | ~ r3_lattices(k1_lattice3(esk1_0),X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0)
    | r3_lattices(k1_lattice3(esk1_0),esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( r3_lattices(k1_lattice3(esk1_0),X1,esk3_0)
    | ~ r1_lattices(k1_lattice3(esk1_0),X1,esk3_0)
    | ~ v8_lattices(k1_lattice3(esk1_0))
    | ~ v6_lattices(k1_lattice3(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_53]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_72,plain,
    ( r1_lattices(k1_lattice3(X3),X1,X2)
    | ~ r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_73,plain,
    ( r1_tarski(X2,X3)
    | ~ r1_lattices(k1_lattice3(X1),X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(k1_lattice3(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0)
    | r1_lattices(k1_lattice3(esk1_0),esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_56])])).

cnf(c_0_75,negated_conjecture,
    ( r3_lattices(k1_lattice3(esk1_0),X1,esk3_0)
    | ~ r1_lattices(k1_lattice3(esk1_0),X1,esk3_0)
    | ~ v6_lattices(k1_lattice3(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_58]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_76,negated_conjecture,
    ( r1_lattices(k1_lattice3(esk1_0),X1,esk3_0)
    | ~ r1_tarski(X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_72,c_0_47])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_47]),c_0_56])])).

cnf(c_0_78,negated_conjecture,
    ( ~ r3_orders_2(k3_yellow_1(esk1_0),esk2_0,esk3_0)
    | ~ r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_79,plain,
    ( r3_orders_2(k3_lattice3(X1),k4_lattice3(X1,X2),k4_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_80,negated_conjecture,
    ( r3_lattices(k1_lattice3(esk1_0),X1,esk3_0)
    | ~ r1_lattices(k1_lattice3(esk1_0),X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_64]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_81,negated_conjecture,
    ( r1_lattices(k1_lattice3(esk1_0),esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_56])])).

cnf(c_0_82,negated_conjecture,
    ( ~ r1_tarski(esk2_0,esk3_0)
    | ~ r3_orders_2(k3_lattice3(k1_lattice3(esk1_0)),esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_78,c_0_24])).

cnf(c_0_83,negated_conjecture,
    ( r3_orders_2(k3_lattice3(k1_lattice3(esk1_0)),k4_lattice3(k1_lattice3(esk1_0),X1),esk3_0)
    | ~ r3_lattices(k1_lattice3(esk1_0),X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(esk1_0))) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_47]),c_0_35]),c_0_36])]),c_0_37]),c_0_55])).

cnf(c_0_84,negated_conjecture,
    ( r3_lattices(k1_lattice3(esk1_0),esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_56])])).

cnf(c_0_85,negated_conjecture,
    ( ~ r3_orders_2(k3_lattice3(k1_lattice3(esk1_0)),esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_77])])).

cnf(c_0_86,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_60]),c_0_56])]),c_0_85]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:15:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___024_B31_F1_PI_AE_Q4_CS_SP_S2S
% 0.19/0.39  # and selection function SelectNewComplexAHP.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.028 s
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(t2_yellow_1, conjecture, ![X1, X2]:(m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k3_yellow_1(X1)))=>(r3_orders_2(k3_yellow_1(X1),X2,X3)<=>r1_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_yellow_1)).
% 0.19/0.39  fof(free_g1_orders_2, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))=>![X3, X4]:(g1_orders_2(X1,X2)=g1_orders_2(X3,X4)=>(X1=X3&X2=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_orders_2)).
% 0.19/0.39  fof(abstractness_v1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>(v1_orders_2(X1)=>X1=g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_orders_2)).
% 0.19/0.39  fof(d2_yellow_1, axiom, ![X1]:k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_yellow_1)).
% 0.19/0.39  fof(dt_g1_orders_2, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))=>(v1_orders_2(g1_orders_2(X1,X2))&l1_orders_2(g1_orders_2(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_g1_orders_2)).
% 0.19/0.39  fof(d2_lattice3, axiom, ![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>k3_lattice3(X1)=g1_orders_2(u1_struct_0(X1),k2_lattice3(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_lattice3)).
% 0.19/0.39  fof(fc2_lattice3, axiom, ![X1]:(v3_lattices(k1_lattice3(X1))&v10_lattices(k1_lattice3(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_lattice3)).
% 0.19/0.39  fof(dt_k1_lattice3, axiom, ![X1]:(v3_lattices(k1_lattice3(X1))&l3_lattices(k1_lattice3(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_lattice3)).
% 0.19/0.39  fof(fc1_lattice3, axiom, ![X1]:(~(v2_struct_0(k1_lattice3(X1)))&v3_lattices(k1_lattice3(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_lattice3)).
% 0.19/0.39  fof(dt_k2_lattice3, axiom, ![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>((((v1_partfun1(k2_lattice3(X1),u1_struct_0(X1))&v1_relat_2(k2_lattice3(X1)))&v4_relat_2(k2_lattice3(X1)))&v8_relat_2(k2_lattice3(X1)))&m1_subset_1(k2_lattice3(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_lattice3)).
% 0.19/0.39  fof(redefinition_r3_lattices, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_lattices(X1,X2,X3)<=>r1_lattices(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 0.19/0.39  fof(d3_lattice3, axiom, ![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k4_lattice3(X1,X2)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_lattice3)).
% 0.19/0.39  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 0.19/0.39  fof(t7_lattice3, axiom, ![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_lattices(X1,X2,X3)<=>r3_orders_2(k3_lattice3(X1),k4_lattice3(X1,X2),k4_lattice3(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_lattice3)).
% 0.19/0.39  fof(t2_lattice3, axiom, ![X1, X2]:(m1_subset_1(X2,u1_struct_0(k1_lattice3(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k1_lattice3(X1)))=>(r1_lattices(k1_lattice3(X1),X2,X3)<=>r1_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_lattice3)).
% 0.19/0.39  fof(c_0_15, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k3_yellow_1(X1)))=>(r3_orders_2(k3_yellow_1(X1),X2,X3)<=>r1_tarski(X2,X3))))), inference(assume_negation,[status(cth)],[t2_yellow_1])).
% 0.19/0.39  fof(c_0_16, plain, ![X8, X9, X10, X11]:((X8=X10|g1_orders_2(X8,X9)!=g1_orders_2(X10,X11)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X8,X8))))&(X9=X11|g1_orders_2(X8,X9)!=g1_orders_2(X10,X11)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X8,X8))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).
% 0.19/0.39  fof(c_0_17, plain, ![X5]:(~l1_orders_2(X5)|(~v1_orders_2(X5)|X5=g1_orders_2(u1_struct_0(X5),u1_orders_2(X5)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_orders_2])])).
% 0.19/0.39  fof(c_0_18, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(k3_yellow_1(esk1_0)))&(m1_subset_1(esk3_0,u1_struct_0(k3_yellow_1(esk1_0)))&((~r3_orders_2(k3_yellow_1(esk1_0),esk2_0,esk3_0)|~r1_tarski(esk2_0,esk3_0))&(r3_orders_2(k3_yellow_1(esk1_0),esk2_0,esk3_0)|r1_tarski(esk2_0,esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.19/0.39  fof(c_0_19, plain, ![X29]:k3_yellow_1(X29)=k3_lattice3(k1_lattice3(X29)), inference(variable_rename,[status(thm)],[d2_yellow_1])).
% 0.19/0.39  cnf(c_0_20, plain, (X1=X2|g1_orders_2(X1,X3)!=g1_orders_2(X2,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.39  cnf(c_0_21, plain, (X1=g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))|~l1_orders_2(X1)|~v1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.39  fof(c_0_22, plain, ![X6, X7]:((v1_orders_2(g1_orders_2(X6,X7))|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X6))))&(l1_orders_2(g1_orders_2(X6,X7))|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X6))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_orders_2])])])).
% 0.19/0.39  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(k3_yellow_1(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_24, plain, (k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.39  fof(c_0_25, plain, ![X16]:(v2_struct_0(X16)|~v10_lattices(X16)|~l3_lattices(X16)|k3_lattice3(X16)=g1_orders_2(u1_struct_0(X16),k2_lattice3(X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_lattice3])])])).
% 0.19/0.39  fof(c_0_26, plain, ![X22]:(v3_lattices(k1_lattice3(X22))&v10_lattices(k1_lattice3(X22))), inference(variable_rename,[status(thm)],[fc2_lattice3])).
% 0.19/0.39  fof(c_0_27, plain, ![X19]:(v3_lattices(k1_lattice3(X19))&l3_lattices(k1_lattice3(X19))), inference(variable_rename,[status(thm)],[dt_k1_lattice3])).
% 0.19/0.39  fof(c_0_28, plain, ![X21]:(~v2_struct_0(k1_lattice3(X21))&v3_lattices(k1_lattice3(X21))), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_lattice3])])).
% 0.19/0.39  cnf(c_0_29, plain, (X1=u1_struct_0(X2)|g1_orders_2(X1,X3)!=X2|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))|~v1_orders_2(X2)|~l1_orders_2(X2)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.39  cnf(c_0_30, plain, (l1_orders_2(g1_orders_2(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.39  cnf(c_0_31, plain, (v1_orders_2(g1_orders_2(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.39  fof(c_0_32, plain, ![X20]:(((((v1_partfun1(k2_lattice3(X20),u1_struct_0(X20))|(v2_struct_0(X20)|~v10_lattices(X20)|~l3_lattices(X20)))&(v1_relat_2(k2_lattice3(X20))|(v2_struct_0(X20)|~v10_lattices(X20)|~l3_lattices(X20))))&(v4_relat_2(k2_lattice3(X20))|(v2_struct_0(X20)|~v10_lattices(X20)|~l3_lattices(X20))))&(v8_relat_2(k2_lattice3(X20))|(v2_struct_0(X20)|~v10_lattices(X20)|~l3_lattices(X20))))&(m1_subset_1(k2_lattice3(X20),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X20))))|(v2_struct_0(X20)|~v10_lattices(X20)|~l3_lattices(X20)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_lattice3])])])])).
% 0.19/0.39  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(k3_lattice3(k1_lattice3(esk1_0))))), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.39  cnf(c_0_34, plain, (v2_struct_0(X1)|k3_lattice3(X1)=g1_orders_2(u1_struct_0(X1),k2_lattice3(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.39  cnf(c_0_35, plain, (v10_lattices(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.39  cnf(c_0_36, plain, (l3_lattices(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.39  cnf(c_0_37, plain, (~v2_struct_0(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.39  cnf(c_0_38, plain, (u1_struct_0(g1_orders_2(X1,X2))=X1|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_29]), c_0_30]), c_0_31])).
% 0.19/0.39  cnf(c_0_39, plain, (m1_subset_1(k2_lattice3(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.39  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(k3_yellow_1(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  fof(c_0_41, plain, ![X13, X14, X15]:((~r3_lattices(X13,X14,X15)|r1_lattices(X13,X14,X15)|(v2_struct_0(X13)|~v6_lattices(X13)|~v8_lattices(X13)|~v9_lattices(X13)|~l3_lattices(X13)|~m1_subset_1(X14,u1_struct_0(X13))|~m1_subset_1(X15,u1_struct_0(X13))))&(~r1_lattices(X13,X14,X15)|r3_lattices(X13,X14,X15)|(v2_struct_0(X13)|~v6_lattices(X13)|~v8_lattices(X13)|~v9_lattices(X13)|~l3_lattices(X13)|~m1_subset_1(X14,u1_struct_0(X13))|~m1_subset_1(X15,u1_struct_0(X13))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).
% 0.19/0.39  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(g1_orders_2(u1_struct_0(k1_lattice3(esk1_0)),k2_lattice3(k1_lattice3(esk1_0)))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36])]), c_0_37])).
% 0.19/0.39  cnf(c_0_43, plain, (u1_struct_0(g1_orders_2(u1_struct_0(X1),k2_lattice3(X1)))=u1_struct_0(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.39  fof(c_0_44, plain, ![X17, X18]:(v2_struct_0(X17)|~v10_lattices(X17)|~l3_lattices(X17)|(~m1_subset_1(X18,u1_struct_0(X17))|k4_lattice3(X17,X18)=X18)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattice3])])])])).
% 0.19/0.39  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(k3_lattice3(k1_lattice3(esk1_0))))), inference(rw,[status(thm)],[c_0_40, c_0_24])).
% 0.19/0.39  cnf(c_0_46, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|~r3_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.39  cnf(c_0_47, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(k1_lattice3(esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_35]), c_0_36])]), c_0_37])).
% 0.19/0.39  fof(c_0_48, plain, ![X12]:(((((((~v2_struct_0(X12)|(v2_struct_0(X12)|~v10_lattices(X12))|~l3_lattices(X12))&(v4_lattices(X12)|(v2_struct_0(X12)|~v10_lattices(X12))|~l3_lattices(X12)))&(v5_lattices(X12)|(v2_struct_0(X12)|~v10_lattices(X12))|~l3_lattices(X12)))&(v6_lattices(X12)|(v2_struct_0(X12)|~v10_lattices(X12))|~l3_lattices(X12)))&(v7_lattices(X12)|(v2_struct_0(X12)|~v10_lattices(X12))|~l3_lattices(X12)))&(v8_lattices(X12)|(v2_struct_0(X12)|~v10_lattices(X12))|~l3_lattices(X12)))&(v9_lattices(X12)|(v2_struct_0(X12)|~v10_lattices(X12))|~l3_lattices(X12))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.19/0.39  fof(c_0_49, plain, ![X26, X27, X28]:((~r3_lattices(X26,X27,X28)|r3_orders_2(k3_lattice3(X26),k4_lattice3(X26,X27),k4_lattice3(X26,X28))|~m1_subset_1(X28,u1_struct_0(X26))|~m1_subset_1(X27,u1_struct_0(X26))|(v2_struct_0(X26)|~v10_lattices(X26)|~l3_lattices(X26)))&(~r3_orders_2(k3_lattice3(X26),k4_lattice3(X26,X27),k4_lattice3(X26,X28))|r3_lattices(X26,X27,X28)|~m1_subset_1(X28,u1_struct_0(X26))|~m1_subset_1(X27,u1_struct_0(X26))|(v2_struct_0(X26)|~v10_lattices(X26)|~l3_lattices(X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_lattice3])])])])])).
% 0.19/0.39  cnf(c_0_50, plain, (v2_struct_0(X1)|k4_lattice3(X1,X2)=X2|~v10_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.39  cnf(c_0_51, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(g1_orders_2(u1_struct_0(k1_lattice3(esk1_0)),k2_lattice3(k1_lattice3(esk1_0)))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_34]), c_0_35]), c_0_36])]), c_0_37])).
% 0.19/0.39  cnf(c_0_52, negated_conjecture, (r1_lattices(k1_lattice3(esk1_0),X1,esk3_0)|~r3_lattices(k1_lattice3(esk1_0),X1,esk3_0)|~v9_lattices(k1_lattice3(esk1_0))|~v8_lattices(k1_lattice3(esk1_0))|~v6_lattices(k1_lattice3(esk1_0))|~m1_subset_1(X1,u1_struct_0(k1_lattice3(esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_36])]), c_0_37])).
% 0.19/0.39  cnf(c_0_53, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.39  cnf(c_0_54, plain, (r3_lattices(X1,X2,X3)|v2_struct_0(X1)|~r3_orders_2(k3_lattice3(X1),k4_lattice3(X1,X2),k4_lattice3(X1,X3))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.39  cnf(c_0_55, negated_conjecture, (k4_lattice3(k1_lattice3(esk1_0),esk3_0)=esk3_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_47]), c_0_35]), c_0_36])]), c_0_37])).
% 0.19/0.39  cnf(c_0_56, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(k1_lattice3(esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_43]), c_0_35]), c_0_36])]), c_0_37])).
% 0.19/0.39  cnf(c_0_57, negated_conjecture, (r1_lattices(k1_lattice3(esk1_0),X1,esk3_0)|~r3_lattices(k1_lattice3(esk1_0),X1,esk3_0)|~v8_lattices(k1_lattice3(esk1_0))|~v6_lattices(k1_lattice3(esk1_0))|~m1_subset_1(X1,u1_struct_0(k1_lattice3(esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_35]), c_0_36])]), c_0_37])).
% 0.19/0.39  cnf(c_0_58, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.39  cnf(c_0_59, negated_conjecture, (r3_lattices(k1_lattice3(esk1_0),X1,esk3_0)|~r3_orders_2(k3_lattice3(k1_lattice3(esk1_0)),k4_lattice3(k1_lattice3(esk1_0),X1),esk3_0)|~m1_subset_1(X1,u1_struct_0(k1_lattice3(esk1_0)))), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_47]), c_0_35]), c_0_36])]), c_0_37]), c_0_55])).
% 0.19/0.39  cnf(c_0_60, negated_conjecture, (k4_lattice3(k1_lattice3(esk1_0),esk2_0)=esk2_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_56]), c_0_35]), c_0_36])]), c_0_37])).
% 0.19/0.39  cnf(c_0_61, negated_conjecture, (r3_orders_2(k3_yellow_1(esk1_0),esk2_0,esk3_0)|r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_62, plain, (r3_lattices(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.39  cnf(c_0_63, negated_conjecture, (r1_lattices(k1_lattice3(esk1_0),X1,esk3_0)|~r3_lattices(k1_lattice3(esk1_0),X1,esk3_0)|~v6_lattices(k1_lattice3(esk1_0))|~m1_subset_1(X1,u1_struct_0(k1_lattice3(esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_35]), c_0_36])]), c_0_37])).
% 0.19/0.39  cnf(c_0_64, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.39  cnf(c_0_65, negated_conjecture, (r3_lattices(k1_lattice3(esk1_0),esk2_0,esk3_0)|~r3_orders_2(k3_lattice3(k1_lattice3(esk1_0)),esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_56]), c_0_60])).
% 0.19/0.39  cnf(c_0_66, negated_conjecture, (r1_tarski(esk2_0,esk3_0)|r3_orders_2(k3_lattice3(k1_lattice3(esk1_0)),esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_61, c_0_24])).
% 0.19/0.39  cnf(c_0_67, negated_conjecture, (r3_lattices(k1_lattice3(esk1_0),X1,esk3_0)|~r1_lattices(k1_lattice3(esk1_0),X1,esk3_0)|~v9_lattices(k1_lattice3(esk1_0))|~v8_lattices(k1_lattice3(esk1_0))|~v6_lattices(k1_lattice3(esk1_0))|~m1_subset_1(X1,u1_struct_0(k1_lattice3(esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_47]), c_0_36])]), c_0_37])).
% 0.19/0.39  fof(c_0_68, plain, ![X23, X24, X25]:((~r1_lattices(k1_lattice3(X23),X24,X25)|r1_tarski(X24,X25)|~m1_subset_1(X25,u1_struct_0(k1_lattice3(X23)))|~m1_subset_1(X24,u1_struct_0(k1_lattice3(X23))))&(~r1_tarski(X24,X25)|r1_lattices(k1_lattice3(X23),X24,X25)|~m1_subset_1(X25,u1_struct_0(k1_lattice3(X23)))|~m1_subset_1(X24,u1_struct_0(k1_lattice3(X23))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_lattice3])])])])).
% 0.19/0.39  cnf(c_0_69, negated_conjecture, (r1_lattices(k1_lattice3(esk1_0),X1,esk3_0)|~r3_lattices(k1_lattice3(esk1_0),X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(k1_lattice3(esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_35]), c_0_36])]), c_0_37])).
% 0.19/0.39  cnf(c_0_70, negated_conjecture, (r1_tarski(esk2_0,esk3_0)|r3_lattices(k1_lattice3(esk1_0),esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.19/0.39  cnf(c_0_71, negated_conjecture, (r3_lattices(k1_lattice3(esk1_0),X1,esk3_0)|~r1_lattices(k1_lattice3(esk1_0),X1,esk3_0)|~v8_lattices(k1_lattice3(esk1_0))|~v6_lattices(k1_lattice3(esk1_0))|~m1_subset_1(X1,u1_struct_0(k1_lattice3(esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_53]), c_0_35]), c_0_36])]), c_0_37])).
% 0.19/0.39  cnf(c_0_72, plain, (r1_lattices(k1_lattice3(X3),X1,X2)|~r1_tarski(X1,X2)|~m1_subset_1(X2,u1_struct_0(k1_lattice3(X3)))|~m1_subset_1(X1,u1_struct_0(k1_lattice3(X3)))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.19/0.39  cnf(c_0_73, plain, (r1_tarski(X2,X3)|~r1_lattices(k1_lattice3(X1),X2,X3)|~m1_subset_1(X3,u1_struct_0(k1_lattice3(X1)))|~m1_subset_1(X2,u1_struct_0(k1_lattice3(X1)))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.19/0.39  cnf(c_0_74, negated_conjecture, (r1_tarski(esk2_0,esk3_0)|r1_lattices(k1_lattice3(esk1_0),esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_56])])).
% 0.19/0.39  cnf(c_0_75, negated_conjecture, (r3_lattices(k1_lattice3(esk1_0),X1,esk3_0)|~r1_lattices(k1_lattice3(esk1_0),X1,esk3_0)|~v6_lattices(k1_lattice3(esk1_0))|~m1_subset_1(X1,u1_struct_0(k1_lattice3(esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_58]), c_0_35]), c_0_36])]), c_0_37])).
% 0.19/0.39  cnf(c_0_76, negated_conjecture, (r1_lattices(k1_lattice3(esk1_0),X1,esk3_0)|~r1_tarski(X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(k1_lattice3(esk1_0)))), inference(spm,[status(thm)],[c_0_72, c_0_47])).
% 0.19/0.39  cnf(c_0_77, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_47]), c_0_56])])).
% 0.19/0.39  cnf(c_0_78, negated_conjecture, (~r3_orders_2(k3_yellow_1(esk1_0),esk2_0,esk3_0)|~r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_79, plain, (r3_orders_2(k3_lattice3(X1),k4_lattice3(X1,X2),k4_lattice3(X1,X3))|v2_struct_0(X1)|~r3_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.39  cnf(c_0_80, negated_conjecture, (r3_lattices(k1_lattice3(esk1_0),X1,esk3_0)|~r1_lattices(k1_lattice3(esk1_0),X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(k1_lattice3(esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_64]), c_0_35]), c_0_36])]), c_0_37])).
% 0.19/0.39  cnf(c_0_81, negated_conjecture, (r1_lattices(k1_lattice3(esk1_0),esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_56])])).
% 0.19/0.39  cnf(c_0_82, negated_conjecture, (~r1_tarski(esk2_0,esk3_0)|~r3_orders_2(k3_lattice3(k1_lattice3(esk1_0)),esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_78, c_0_24])).
% 0.19/0.39  cnf(c_0_83, negated_conjecture, (r3_orders_2(k3_lattice3(k1_lattice3(esk1_0)),k4_lattice3(k1_lattice3(esk1_0),X1),esk3_0)|~r3_lattices(k1_lattice3(esk1_0),X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(k1_lattice3(esk1_0)))), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_47]), c_0_35]), c_0_36])]), c_0_37]), c_0_55])).
% 0.19/0.39  cnf(c_0_84, negated_conjecture, (r3_lattices(k1_lattice3(esk1_0),esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_56])])).
% 0.19/0.39  cnf(c_0_85, negated_conjecture, (~r3_orders_2(k3_lattice3(k1_lattice3(esk1_0)),esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_77])])).
% 0.19/0.39  cnf(c_0_86, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_60]), c_0_56])]), c_0_85]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 87
% 0.19/0.39  # Proof object clause steps            : 56
% 0.19/0.39  # Proof object formula steps           : 31
% 0.19/0.39  # Proof object conjectures             : 36
% 0.19/0.39  # Proof object clause conjectures      : 33
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 24
% 0.19/0.39  # Proof object initial formulas used   : 15
% 0.19/0.39  # Proof object generating inferences   : 27
% 0.19/0.39  # Proof object simplifying inferences  : 86
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 15
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 36
% 0.19/0.39  # Removed in clause preprocessing      : 2
% 0.19/0.39  # Initial clauses in saturation        : 34
% 0.19/0.39  # Processed clauses                    : 103
% 0.19/0.39  # ...of these trivial                  : 2
% 0.19/0.39  # ...subsumed                          : 5
% 0.19/0.39  # ...remaining for further processing  : 96
% 0.19/0.39  # Other redundant clauses eliminated   : 4
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 6
% 0.19/0.39  # Backward-rewritten                   : 7
% 0.19/0.39  # Generated clauses                    : 122
% 0.19/0.39  # ...of the previous two non-trivial   : 110
% 0.19/0.39  # Contextual simplify-reflections      : 6
% 0.19/0.39  # Paramodulations                      : 112
% 0.19/0.39  # Factorizations                       : 0
% 0.19/0.39  # Equation resolutions                 : 10
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 83
% 0.19/0.39  #    Positive orientable unit clauses  : 14
% 0.19/0.39  #    Positive unorientable unit clauses: 0
% 0.19/0.39  #    Negative unit clauses             : 2
% 0.19/0.39  #    Non-unit-clauses                  : 67
% 0.19/0.39  # Current number of unprocessed clauses: 41
% 0.19/0.39  # ...number of literals in the above   : 295
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 14
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 1210
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 186
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 17
% 0.19/0.39  # Unit Clause-clause subsumption calls : 36
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 3
% 0.19/0.39  # BW rewrite match successes           : 2
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 7670
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.039 s
% 0.19/0.39  # System time              : 0.002 s
% 0.19/0.39  # Total time               : 0.041 s
% 0.19/0.39  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
