%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:54 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  103 (1441 expanded)
%              Number of clauses        :   70 ( 535 expanded)
%              Number of leaves         :   16 ( 374 expanded)
%              Depth                    :   27
%              Number of atoms          :  518 (9177 expanded)
%              Number of equality atoms :   53 ( 669 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(free_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ! [X3,X4] :
          ( g1_orders_2(X1,X2) = g1_orders_2(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

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

fof(d2_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => k3_lattice3(X1) = g1_orders_2(u1_struct_0(X1),k2_lattice3(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_lattice3)).

fof(abstractness_v1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_orders_2(X1)
       => X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(dt_k3_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ( v1_orders_2(k3_lattice3(X1))
        & v3_orders_2(k3_lattice3(X1))
        & v4_orders_2(k3_lattice3(X1))
        & v5_orders_2(k3_lattice3(X1))
        & l1_orders_2(k3_lattice3(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_lattice3)).

fof(t7_lattice3,conjecture,(
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

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(rc14_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ? [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
          & ~ v1_xboole_0(X2)
          & v18_lattices(X2,X1)
          & v19_lattices(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc14_lattices)).

fof(d9_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_orders_2(X1,X2,X3)
              <=> r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

fof(dt_k4_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k4_lattice3(X1,X2),u1_struct_0(k3_lattice3(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_lattice3)).

fof(d3_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k4_lattice3(X1,X2) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattice3)).

fof(t32_filter_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_hidden(k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3),k8_filter_1(X1))
              <=> r3_lattices(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_filter_1)).

fof(redefinition_k1_domain_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X3,X1)
        & m1_subset_1(X4,X2) )
     => k1_domain_1(X1,X2,X3,X4) = k4_tarski(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_domain_1)).

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

fof(fc4_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ( ~ v2_struct_0(k3_lattice3(X1))
        & v1_orders_2(k3_lattice3(X1))
        & v3_orders_2(k3_lattice3(X1))
        & v4_orders_2(k3_lattice3(X1))
        & v5_orders_2(k3_lattice3(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_lattice3)).

fof(redefinition_k2_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => k2_lattice3(X1) = k8_filter_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_lattice3)).

fof(c_0_16,plain,(
    ! [X11,X12,X13,X14] :
      ( ( X11 = X13
        | g1_orders_2(X11,X12) != g1_orders_2(X13,X14)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X11,X11))) )
      & ( X12 = X14
        | g1_orders_2(X11,X12) != g1_orders_2(X13,X14)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X11,X11))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

fof(c_0_17,plain,(
    ! [X30] :
      ( ( v1_partfun1(k2_lattice3(X30),u1_struct_0(X30))
        | v2_struct_0(X30)
        | ~ v10_lattices(X30)
        | ~ l3_lattices(X30) )
      & ( v1_relat_2(k2_lattice3(X30))
        | v2_struct_0(X30)
        | ~ v10_lattices(X30)
        | ~ l3_lattices(X30) )
      & ( v4_relat_2(k2_lattice3(X30))
        | v2_struct_0(X30)
        | ~ v10_lattices(X30)
        | ~ l3_lattices(X30) )
      & ( v8_relat_2(k2_lattice3(X30))
        | v2_struct_0(X30)
        | ~ v10_lattices(X30)
        | ~ l3_lattices(X30) )
      & ( m1_subset_1(k2_lattice3(X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X30))))
        | v2_struct_0(X30)
        | ~ v10_lattices(X30)
        | ~ l3_lattices(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_lattice3])])])])).

cnf(c_0_18,plain,
    ( X1 = X2
    | g1_orders_2(X3,X1) != g1_orders_2(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,plain,
    ( m1_subset_1(k2_lattice3(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_20,plain,(
    ! [X27] :
      ( v2_struct_0(X27)
      | ~ v10_lattices(X27)
      | ~ l3_lattices(X27)
      | k3_lattice3(X27) = g1_orders_2(u1_struct_0(X27),k2_lattice3(X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_lattice3])])])).

cnf(c_0_21,plain,
    ( k2_lattice3(X1) = X2
    | v2_struct_0(X1)
    | g1_orders_2(u1_struct_0(X1),k2_lattice3(X1)) != g1_orders_2(X3,X2)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_22,plain,
    ( v2_struct_0(X1)
    | k3_lattice3(X1) = g1_orders_2(u1_struct_0(X1),k2_lattice3(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_23,plain,(
    ! [X7] :
      ( ~ l1_orders_2(X7)
      | ~ v1_orders_2(X7)
      | X7 = g1_orders_2(u1_struct_0(X7),u1_orders_2(X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_orders_2])])).

fof(c_0_24,plain,(
    ! [X31] :
      ( ( v1_orders_2(k3_lattice3(X31))
        | v2_struct_0(X31)
        | ~ v10_lattices(X31)
        | ~ l3_lattices(X31) )
      & ( v3_orders_2(k3_lattice3(X31))
        | v2_struct_0(X31)
        | ~ v10_lattices(X31)
        | ~ l3_lattices(X31) )
      & ( v4_orders_2(k3_lattice3(X31))
        | v2_struct_0(X31)
        | ~ v10_lattices(X31)
        | ~ l3_lattices(X31) )
      & ( v5_orders_2(k3_lattice3(X31))
        | v2_struct_0(X31)
        | ~ v10_lattices(X31)
        | ~ l3_lattices(X31) )
      & ( l1_orders_2(k3_lattice3(X31))
        | v2_struct_0(X31)
        | ~ v10_lattices(X31)
        | ~ l3_lattices(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_lattice3])])])])).

cnf(c_0_25,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k2_lattice3(X1) = X2
    | v2_struct_0(X1)
    | k3_lattice3(X1) != g1_orders_2(X3,X2)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,plain,
    ( X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ v1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( l1_orders_2(k3_lattice3(X1))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( v1_orders_2(k3_lattice3(X1))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( u1_struct_0(X1) = X2
    | v2_struct_0(X1)
    | g1_orders_2(u1_struct_0(X1),k2_lattice3(X1)) != g1_orders_2(X2,X3)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_19])).

cnf(c_0_31,plain,
    ( u1_orders_2(k3_lattice3(X1)) = k2_lattice3(X1)
    | v2_struct_0(X1)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27])]),c_0_28]),c_0_29])).

fof(c_0_32,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r3_lattices(X1,X2,X3)
                <=> r3_orders_2(k3_lattice3(X1),k4_lattice3(X1,X2),k4_lattice3(X1,X3)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t7_lattice3])).

cnf(c_0_33,plain,
    ( u1_struct_0(X1) = X2
    | v2_struct_0(X1)
    | k3_lattice3(X1) != g1_orders_2(X2,X3)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_22])).

cnf(c_0_34,plain,
    ( g1_orders_2(u1_struct_0(k3_lattice3(X1)),k2_lattice3(X1)) = k3_lattice3(X1)
    | v2_struct_0(X1)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_31]),c_0_28]),c_0_29])).

fof(c_0_35,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v10_lattices(esk2_0)
    & l3_lattices(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk4_0,u1_struct_0(esk2_0))
    & ( ~ r3_lattices(esk2_0,esk3_0,esk4_0)
      | ~ r3_orders_2(k3_lattice3(esk2_0),k4_lattice3(esk2_0,esk3_0),k4_lattice3(esk2_0,esk4_0)) )
    & ( r3_lattices(esk2_0,esk3_0,esk4_0)
      | r3_orders_2(k3_lattice3(esk2_0),k4_lattice3(esk2_0,esk3_0),k4_lattice3(esk2_0,esk4_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_32])])])])).

cnf(c_0_36,plain,
    ( u1_struct_0(X1) = u1_struct_0(k3_lattice3(X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | k3_lattice3(X1) != k3_lattice3(X2)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X2)
    | ~ v10_lattices(X1)
    | ~ v10_lattices(X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( l3_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( v10_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( u1_struct_0(k3_lattice3(X1)) = u1_struct_0(esk2_0)
    | v2_struct_0(X1)
    | k3_lattice3(esk2_0) != k3_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])]),c_0_39])).

cnf(c_0_41,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk2_0),k2_lattice3(X1)) = k3_lattice3(X1)
    | v2_struct_0(X1)
    | k3_lattice3(esk2_0) != k3_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_40])).

cnf(c_0_42,negated_conjecture,
    ( k2_lattice3(esk2_0) = X1
    | g1_orders_2(X2,X1) != k3_lattice3(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_41]),c_0_37]),c_0_38])]),c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( u1_orders_2(k3_lattice3(esk2_0)) = k2_lattice3(esk2_0)
    | ~ v1_orders_2(k3_lattice3(esk2_0))
    | ~ l1_orders_2(k3_lattice3(esk2_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_27])])).

cnf(c_0_44,negated_conjecture,
    ( g1_orders_2(u1_struct_0(k3_lattice3(esk2_0)),k2_lattice3(esk2_0)) = k3_lattice3(esk2_0)
    | ~ v1_orders_2(k3_lattice3(esk2_0))
    | ~ l1_orders_2(k3_lattice3(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_43])).

fof(c_0_45,plain,(
    ! [X5,X6] :
      ( ~ v1_xboole_0(X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X5))
      | v1_xboole_0(X6) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

fof(c_0_46,plain,(
    ! [X22] :
      ( ( m1_subset_1(esk1_1(X22),k1_zfmisc_1(u1_struct_0(X22)))
        | v2_struct_0(X22)
        | ~ v10_lattices(X22)
        | ~ l3_lattices(X22) )
      & ( ~ v1_xboole_0(esk1_1(X22))
        | v2_struct_0(X22)
        | ~ v10_lattices(X22)
        | ~ l3_lattices(X22) )
      & ( v18_lattices(esk1_1(X22),X22)
        | v2_struct_0(X22)
        | ~ v10_lattices(X22)
        | ~ l3_lattices(X22) )
      & ( v19_lattices(esk1_1(X22),X22)
        | v2_struct_0(X22)
        | ~ v10_lattices(X22)
        | ~ l3_lattices(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc14_lattices])])])])])).

fof(c_0_47,plain,(
    ! [X8,X9,X10] :
      ( ( ~ r1_orders_2(X8,X9,X10)
        | r2_hidden(k4_tarski(X9,X10),u1_orders_2(X8))
        | ~ m1_subset_1(X10,u1_struct_0(X8))
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ l1_orders_2(X8) )
      & ( ~ r2_hidden(k4_tarski(X9,X10),u1_orders_2(X8))
        | r1_orders_2(X8,X9,X10)
        | ~ m1_subset_1(X10,u1_struct_0(X8))
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ l1_orders_2(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).

fof(c_0_48,plain,(
    ! [X32,X33] :
      ( v2_struct_0(X32)
      | ~ v10_lattices(X32)
      | ~ l3_lattices(X32)
      | ~ m1_subset_1(X33,u1_struct_0(X32))
      | m1_subset_1(k4_lattice3(X32,X33),u1_struct_0(k3_lattice3(X32))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_lattice3])])])).

cnf(c_0_49,negated_conjecture,
    ( u1_struct_0(X1) = u1_struct_0(k3_lattice3(esk2_0))
    | v2_struct_0(X1)
    | k3_lattice3(X1) != k3_lattice3(esk2_0)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v1_orders_2(k3_lattice3(esk2_0))
    | ~ l1_orders_2(k3_lattice3(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_44])).

fof(c_0_50,plain,(
    ! [X28,X29] :
      ( v2_struct_0(X28)
      | ~ v10_lattices(X28)
      | ~ l3_lattices(X28)
      | ~ m1_subset_1(X29,u1_struct_0(X28))
      | k4_lattice3(X28,X29) = X29 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattice3])])])])).

fof(c_0_51,plain,(
    ! [X24,X25,X26] :
      ( ( ~ r2_hidden(k1_domain_1(u1_struct_0(X24),u1_struct_0(X24),X25,X26),k8_filter_1(X24))
        | r3_lattices(X24,X25,X26)
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | v2_struct_0(X24)
        | ~ v10_lattices(X24)
        | ~ l3_lattices(X24) )
      & ( ~ r3_lattices(X24,X25,X26)
        | r2_hidden(k1_domain_1(u1_struct_0(X24),u1_struct_0(X24),X25,X26),k8_filter_1(X24))
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | v2_struct_0(X24)
        | ~ v10_lattices(X24)
        | ~ l3_lattices(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_filter_1])])])])])).

fof(c_0_52,plain,(
    ! [X15,X16,X17,X18] :
      ( v1_xboole_0(X15)
      | v1_xboole_0(X16)
      | ~ m1_subset_1(X17,X15)
      | ~ m1_subset_1(X18,X16)
      | k1_domain_1(X15,X16,X17,X18) = k4_tarski(X17,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k1_domain_1])])])).

cnf(c_0_53,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,plain,
    ( m1_subset_1(esk1_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_55,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(esk1_1(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_56,plain,
    ( r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_57,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k4_lattice3(X1,X2),u1_struct_0(k3_lattice3(X1)))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_58,plain,(
    ! [X19,X20,X21] :
      ( ( ~ r3_orders_2(X19,X20,X21)
        | r1_orders_2(X19,X20,X21)
        | v2_struct_0(X19)
        | ~ v3_orders_2(X19)
        | ~ l1_orders_2(X19)
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | ~ m1_subset_1(X21,u1_struct_0(X19)) )
      & ( ~ r1_orders_2(X19,X20,X21)
        | r3_orders_2(X19,X20,X21)
        | v2_struct_0(X19)
        | ~ v3_orders_2(X19)
        | ~ l1_orders_2(X19)
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | ~ m1_subset_1(X21,u1_struct_0(X19)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

fof(c_0_59,plain,(
    ! [X34] :
      ( ( ~ v2_struct_0(k3_lattice3(X34))
        | v2_struct_0(X34)
        | ~ v10_lattices(X34)
        | ~ l3_lattices(X34) )
      & ( v1_orders_2(k3_lattice3(X34))
        | v2_struct_0(X34)
        | ~ v10_lattices(X34)
        | ~ l3_lattices(X34) )
      & ( v3_orders_2(k3_lattice3(X34))
        | v2_struct_0(X34)
        | ~ v10_lattices(X34)
        | ~ l3_lattices(X34) )
      & ( v4_orders_2(k3_lattice3(X34))
        | v2_struct_0(X34)
        | ~ v10_lattices(X34)
        | ~ l3_lattices(X34) )
      & ( v5_orders_2(k3_lattice3(X34))
        | v2_struct_0(X34)
        | ~ v10_lattices(X34)
        | ~ l3_lattices(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_lattice3])])])])).

cnf(c_0_60,negated_conjecture,
    ( u1_struct_0(X1) = u1_struct_0(k3_lattice3(esk2_0))
    | v2_struct_0(X1)
    | k3_lattice3(X1) != k3_lattice3(esk2_0)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ l1_orders_2(k3_lattice3(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_29]),c_0_37]),c_0_38])]),c_0_39])).

cnf(c_0_61,plain,
    ( v2_struct_0(X1)
    | k4_lattice3(X1,X2) = X2
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_62,plain,
    ( r2_hidden(k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3),k8_filter_1(X1))
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_63,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | k1_domain_1(X1,X2,X3,X4) = k4_tarski(X3,X4)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_64,plain,
    ( v2_struct_0(X1)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])).

cnf(c_0_65,plain,
    ( v2_struct_0(X1)
    | r2_hidden(k4_tarski(X2,k4_lattice3(X1,X3)),u1_orders_2(k3_lattice3(X1)))
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ r1_orders_2(k3_lattice3(X1),X2,k4_lattice3(X1,X3))
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_28])).

cnf(c_0_66,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_67,plain,
    ( v3_orders_2(k3_lattice3(X1))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_68,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k3_lattice3(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_69,negated_conjecture,
    ( r3_lattices(esk2_0,esk3_0,esk4_0)
    | r3_orders_2(k3_lattice3(esk2_0),k4_lattice3(esk2_0,esk3_0),k4_lattice3(esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_71,negated_conjecture,
    ( u1_struct_0(X1) = u1_struct_0(k3_lattice3(esk2_0))
    | v2_struct_0(X1)
    | k3_lattice3(X1) != k3_lattice3(esk2_0)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_28]),c_0_37]),c_0_38])]),c_0_39])).

cnf(c_0_72,plain,
    ( r3_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_73,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X2,u1_struct_0(k3_lattice3(X1)))
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_61])).

cnf(c_0_74,plain,
    ( v2_struct_0(X1)
    | r2_hidden(k4_tarski(X2,X3),k8_filter_1(X1))
    | ~ r3_lattices(X1,X2,X3)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_76,plain,
    ( v2_struct_0(X1)
    | r2_hidden(k4_tarski(X2,k4_lattice3(X1,X3)),u1_orders_2(k3_lattice3(X1)))
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ r3_orders_2(k3_lattice3(X1),X2,k4_lattice3(X1,X3))
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_57]),c_0_28]),c_0_67]),c_0_68])).

cnf(c_0_77,negated_conjecture,
    ( r3_lattices(esk2_0,esk3_0,esk4_0)
    | r3_orders_2(k3_lattice3(esk2_0),esk3_0,k4_lattice3(esk2_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_61]),c_0_37]),c_0_38]),c_0_70])]),c_0_39])).

cnf(c_0_78,negated_conjecture,
    ( u1_struct_0(k3_lattice3(esk2_0)) = u1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_71]),c_0_37]),c_0_38])]),c_0_39])).

cnf(c_0_79,negated_conjecture,
    ( ~ r3_lattices(esk2_0,esk3_0,esk4_0)
    | ~ r3_orders_2(k3_lattice3(esk2_0),k4_lattice3(esk2_0,esk3_0),k4_lattice3(esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_80,plain,
    ( r3_orders_2(k3_lattice3(X1),X2,X3)
    | v2_struct_0(X1)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ r1_orders_2(k3_lattice3(X1),X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_28]),c_0_67]),c_0_68])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk4_0),k8_filter_1(esk2_0))
    | ~ r3_lattices(esk2_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_37]),c_0_38])]),c_0_39])).

cnf(c_0_82,negated_conjecture,
    ( r3_lattices(esk2_0,esk3_0,esk4_0)
    | r2_hidden(k4_tarski(esk3_0,k4_lattice3(esk2_0,esk4_0)),u1_orders_2(k3_lattice3(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_37]),c_0_38]),c_0_78]),c_0_70]),c_0_75])]),c_0_39])).

cnf(c_0_83,negated_conjecture,
    ( ~ r3_lattices(esk2_0,esk3_0,esk4_0)
    | ~ r3_orders_2(k3_lattice3(esk2_0),k4_lattice3(esk2_0,esk3_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_61]),c_0_37]),c_0_38]),c_0_75])]),c_0_39])).

cnf(c_0_84,negated_conjecture,
    ( r3_orders_2(k3_lattice3(esk2_0),X1,X2)
    | ~ r1_orders_2(k3_lattice3(esk2_0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_78]),c_0_37]),c_0_38])]),c_0_39])).

cnf(c_0_85,plain,
    ( r1_orders_2(X3,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_0,k4_lattice3(esk2_0,esk4_0)),u1_orders_2(k3_lattice3(esk2_0)))
    | r2_hidden(k4_tarski(esk3_0,esk4_0),k8_filter_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_70])])).

cnf(c_0_87,negated_conjecture,
    ( ~ r3_lattices(esk2_0,esk3_0,esk4_0)
    | ~ r3_orders_2(k3_lattice3(esk2_0),esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_61]),c_0_37]),c_0_38]),c_0_70])]),c_0_39])).

cnf(c_0_88,negated_conjecture,
    ( r3_orders_2(k3_lattice3(esk2_0),X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(k3_lattice3(esk2_0)))
    | ~ l1_orders_2(k3_lattice3(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_78]),c_0_78])])).

cnf(c_0_89,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_0,esk4_0),u1_orders_2(k3_lattice3(esk2_0)))
    | r2_hidden(k4_tarski(esk3_0,esk4_0),k8_filter_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_61]),c_0_37]),c_0_38]),c_0_75])]),c_0_39])).

fof(c_0_90,plain,(
    ! [X35] :
      ( v2_struct_0(X35)
      | ~ v10_lattices(X35)
      | ~ l3_lattices(X35)
      | k2_lattice3(X35) = k8_filter_1(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k2_lattice3])])])).

cnf(c_0_91,negated_conjecture,
    ( ~ r3_lattices(esk2_0,esk3_0,esk4_0)
    | ~ r2_hidden(k4_tarski(esk3_0,esk4_0),u1_orders_2(k3_lattice3(esk2_0)))
    | ~ l1_orders_2(k3_lattice3(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_70]),c_0_75])])).

cnf(c_0_92,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_0,esk4_0),k8_filter_1(esk2_0))
    | r2_hidden(k4_tarski(esk3_0,esk4_0),k2_lattice3(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_31]),c_0_37]),c_0_38])]),c_0_39])).

cnf(c_0_93,plain,
    ( v2_struct_0(X1)
    | k2_lattice3(X1) = k8_filter_1(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_94,negated_conjecture,
    ( ~ r3_lattices(esk2_0,esk3_0,esk4_0)
    | ~ r2_hidden(k4_tarski(esk3_0,esk4_0),k2_lattice3(esk2_0))
    | ~ l1_orders_2(k3_lattice3(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_31]),c_0_37]),c_0_38])]),c_0_39])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_0,esk4_0),k2_lattice3(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_37]),c_0_38])]),c_0_39])).

cnf(c_0_96,negated_conjecture,
    ( ~ r3_lattices(esk2_0,esk3_0,esk4_0)
    | ~ l1_orders_2(k3_lattice3(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_95])])).

cnf(c_0_97,plain,
    ( r3_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3),k8_filter_1(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_98,negated_conjecture,
    ( ~ r2_hidden(k1_domain_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),esk3_0,esk4_0),k8_filter_1(esk2_0))
    | ~ l1_orders_2(k3_lattice3(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_37]),c_0_38]),c_0_75]),c_0_70])]),c_0_39])).

cnf(c_0_99,negated_conjecture,
    ( ~ r2_hidden(k1_domain_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),esk3_0,esk4_0),k2_lattice3(esk2_0))
    | ~ l1_orders_2(k3_lattice3(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_93]),c_0_37]),c_0_38])]),c_0_39])).

cnf(c_0_100,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | ~ l1_orders_2(k3_lattice3(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_63]),c_0_95]),c_0_75]),c_0_70])])).

cnf(c_0_101,negated_conjecture,
    ( ~ l1_orders_2(k3_lattice3(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_100]),c_0_37]),c_0_38])]),c_0_39])).

cnf(c_0_102,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_28]),c_0_37]),c_0_38])]),c_0_39]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:33:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 0.19/0.41  # and selection function PSelectUnlessUniqMaxPos.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.029 s
% 0.19/0.41  # Presaturation interreduction done
% 0.19/0.41  
% 0.19/0.41  # Proof found!
% 0.19/0.41  # SZS status Theorem
% 0.19/0.41  # SZS output start CNFRefutation
% 0.19/0.41  fof(free_g1_orders_2, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))=>![X3, X4]:(g1_orders_2(X1,X2)=g1_orders_2(X3,X4)=>(X1=X3&X2=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_orders_2)).
% 0.19/0.41  fof(dt_k2_lattice3, axiom, ![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>((((v1_partfun1(k2_lattice3(X1),u1_struct_0(X1))&v1_relat_2(k2_lattice3(X1)))&v4_relat_2(k2_lattice3(X1)))&v8_relat_2(k2_lattice3(X1)))&m1_subset_1(k2_lattice3(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_lattice3)).
% 0.19/0.41  fof(d2_lattice3, axiom, ![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>k3_lattice3(X1)=g1_orders_2(u1_struct_0(X1),k2_lattice3(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_lattice3)).
% 0.19/0.41  fof(abstractness_v1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>(v1_orders_2(X1)=>X1=g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_orders_2)).
% 0.19/0.41  fof(dt_k3_lattice3, axiom, ![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>((((v1_orders_2(k3_lattice3(X1))&v3_orders_2(k3_lattice3(X1)))&v4_orders_2(k3_lattice3(X1)))&v5_orders_2(k3_lattice3(X1)))&l1_orders_2(k3_lattice3(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_lattice3)).
% 0.19/0.41  fof(t7_lattice3, conjecture, ![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_lattices(X1,X2,X3)<=>r3_orders_2(k3_lattice3(X1),k4_lattice3(X1,X2),k4_lattice3(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_lattice3)).
% 0.19/0.41  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.19/0.41  fof(rc14_lattices, axiom, ![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>?[X2]:(((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))&~(v1_xboole_0(X2)))&v18_lattices(X2,X1))&v19_lattices(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc14_lattices)).
% 0.19/0.41  fof(d9_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_orders_2(X1,X2,X3)<=>r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_orders_2)).
% 0.19/0.41  fof(dt_k4_lattice3, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>m1_subset_1(k4_lattice3(X1,X2),u1_struct_0(k3_lattice3(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_lattice3)).
% 0.19/0.41  fof(d3_lattice3, axiom, ![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k4_lattice3(X1,X2)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_lattice3)).
% 0.19/0.41  fof(t32_filter_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3),k8_filter_1(X1))<=>r3_lattices(X1,X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_filter_1)).
% 0.19/0.41  fof(redefinition_k1_domain_1, axiom, ![X1, X2, X3, X4]:((((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))&m1_subset_1(X3,X1))&m1_subset_1(X4,X2))=>k1_domain_1(X1,X2,X3,X4)=k4_tarski(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_domain_1)).
% 0.19/0.41  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 0.19/0.41  fof(fc4_lattice3, axiom, ![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>((((~(v2_struct_0(k3_lattice3(X1)))&v1_orders_2(k3_lattice3(X1)))&v3_orders_2(k3_lattice3(X1)))&v4_orders_2(k3_lattice3(X1)))&v5_orders_2(k3_lattice3(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_lattice3)).
% 0.19/0.41  fof(redefinition_k2_lattice3, axiom, ![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>k2_lattice3(X1)=k8_filter_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_lattice3)).
% 0.19/0.41  fof(c_0_16, plain, ![X11, X12, X13, X14]:((X11=X13|g1_orders_2(X11,X12)!=g1_orders_2(X13,X14)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X11,X11))))&(X12=X14|g1_orders_2(X11,X12)!=g1_orders_2(X13,X14)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X11,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).
% 0.19/0.41  fof(c_0_17, plain, ![X30]:(((((v1_partfun1(k2_lattice3(X30),u1_struct_0(X30))|(v2_struct_0(X30)|~v10_lattices(X30)|~l3_lattices(X30)))&(v1_relat_2(k2_lattice3(X30))|(v2_struct_0(X30)|~v10_lattices(X30)|~l3_lattices(X30))))&(v4_relat_2(k2_lattice3(X30))|(v2_struct_0(X30)|~v10_lattices(X30)|~l3_lattices(X30))))&(v8_relat_2(k2_lattice3(X30))|(v2_struct_0(X30)|~v10_lattices(X30)|~l3_lattices(X30))))&(m1_subset_1(k2_lattice3(X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X30))))|(v2_struct_0(X30)|~v10_lattices(X30)|~l3_lattices(X30)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_lattice3])])])])).
% 0.19/0.41  cnf(c_0_18, plain, (X1=X2|g1_orders_2(X3,X1)!=g1_orders_2(X4,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.41  cnf(c_0_19, plain, (m1_subset_1(k2_lattice3(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.41  fof(c_0_20, plain, ![X27]:(v2_struct_0(X27)|~v10_lattices(X27)|~l3_lattices(X27)|k3_lattice3(X27)=g1_orders_2(u1_struct_0(X27),k2_lattice3(X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_lattice3])])])).
% 0.19/0.41  cnf(c_0_21, plain, (k2_lattice3(X1)=X2|v2_struct_0(X1)|g1_orders_2(u1_struct_0(X1),k2_lattice3(X1))!=g1_orders_2(X3,X2)|~l3_lattices(X1)|~v10_lattices(X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.19/0.41  cnf(c_0_22, plain, (v2_struct_0(X1)|k3_lattice3(X1)=g1_orders_2(u1_struct_0(X1),k2_lattice3(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.41  fof(c_0_23, plain, ![X7]:(~l1_orders_2(X7)|(~v1_orders_2(X7)|X7=g1_orders_2(u1_struct_0(X7),u1_orders_2(X7)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_orders_2])])).
% 0.19/0.41  fof(c_0_24, plain, ![X31]:(((((v1_orders_2(k3_lattice3(X31))|(v2_struct_0(X31)|~v10_lattices(X31)|~l3_lattices(X31)))&(v3_orders_2(k3_lattice3(X31))|(v2_struct_0(X31)|~v10_lattices(X31)|~l3_lattices(X31))))&(v4_orders_2(k3_lattice3(X31))|(v2_struct_0(X31)|~v10_lattices(X31)|~l3_lattices(X31))))&(v5_orders_2(k3_lattice3(X31))|(v2_struct_0(X31)|~v10_lattices(X31)|~l3_lattices(X31))))&(l1_orders_2(k3_lattice3(X31))|(v2_struct_0(X31)|~v10_lattices(X31)|~l3_lattices(X31)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_lattice3])])])])).
% 0.19/0.41  cnf(c_0_25, plain, (X1=X2|g1_orders_2(X1,X3)!=g1_orders_2(X2,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.41  cnf(c_0_26, plain, (k2_lattice3(X1)=X2|v2_struct_0(X1)|k3_lattice3(X1)!=g1_orders_2(X3,X2)|~l3_lattices(X1)|~v10_lattices(X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.41  cnf(c_0_27, plain, (X1=g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))|~l1_orders_2(X1)|~v1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.41  cnf(c_0_28, plain, (l1_orders_2(k3_lattice3(X1))|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.41  cnf(c_0_29, plain, (v1_orders_2(k3_lattice3(X1))|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.41  cnf(c_0_30, plain, (u1_struct_0(X1)=X2|v2_struct_0(X1)|g1_orders_2(u1_struct_0(X1),k2_lattice3(X1))!=g1_orders_2(X2,X3)|~l3_lattices(X1)|~v10_lattices(X1)), inference(spm,[status(thm)],[c_0_25, c_0_19])).
% 0.19/0.41  cnf(c_0_31, plain, (u1_orders_2(k3_lattice3(X1))=k2_lattice3(X1)|v2_struct_0(X1)|~l3_lattices(X1)|~v10_lattices(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27])]), c_0_28]), c_0_29])).
% 0.19/0.41  fof(c_0_32, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_lattices(X1,X2,X3)<=>r3_orders_2(k3_lattice3(X1),k4_lattice3(X1,X2),k4_lattice3(X1,X3))))))), inference(assume_negation,[status(cth)],[t7_lattice3])).
% 0.19/0.41  cnf(c_0_33, plain, (u1_struct_0(X1)=X2|v2_struct_0(X1)|k3_lattice3(X1)!=g1_orders_2(X2,X3)|~l3_lattices(X1)|~v10_lattices(X1)), inference(spm,[status(thm)],[c_0_30, c_0_22])).
% 0.19/0.41  cnf(c_0_34, plain, (g1_orders_2(u1_struct_0(k3_lattice3(X1)),k2_lattice3(X1))=k3_lattice3(X1)|v2_struct_0(X1)|~l3_lattices(X1)|~v10_lattices(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_31]), c_0_28]), c_0_29])).
% 0.19/0.41  fof(c_0_35, negated_conjecture, (((~v2_struct_0(esk2_0)&v10_lattices(esk2_0))&l3_lattices(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&(m1_subset_1(esk4_0,u1_struct_0(esk2_0))&((~r3_lattices(esk2_0,esk3_0,esk4_0)|~r3_orders_2(k3_lattice3(esk2_0),k4_lattice3(esk2_0,esk3_0),k4_lattice3(esk2_0,esk4_0)))&(r3_lattices(esk2_0,esk3_0,esk4_0)|r3_orders_2(k3_lattice3(esk2_0),k4_lattice3(esk2_0,esk3_0),k4_lattice3(esk2_0,esk4_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_32])])])])).
% 0.19/0.41  cnf(c_0_36, plain, (u1_struct_0(X1)=u1_struct_0(k3_lattice3(X2))|v2_struct_0(X2)|v2_struct_0(X1)|k3_lattice3(X1)!=k3_lattice3(X2)|~l3_lattices(X1)|~l3_lattices(X2)|~v10_lattices(X1)|~v10_lattices(X2)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.41  cnf(c_0_37, negated_conjecture, (l3_lattices(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.41  cnf(c_0_38, negated_conjecture, (v10_lattices(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.41  cnf(c_0_39, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.41  cnf(c_0_40, negated_conjecture, (u1_struct_0(k3_lattice3(X1))=u1_struct_0(esk2_0)|v2_struct_0(X1)|k3_lattice3(esk2_0)!=k3_lattice3(X1)|~l3_lattices(X1)|~v10_lattices(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])]), c_0_39])).
% 0.19/0.41  cnf(c_0_41, negated_conjecture, (g1_orders_2(u1_struct_0(esk2_0),k2_lattice3(X1))=k3_lattice3(X1)|v2_struct_0(X1)|k3_lattice3(esk2_0)!=k3_lattice3(X1)|~l3_lattices(X1)|~v10_lattices(X1)), inference(spm,[status(thm)],[c_0_34, c_0_40])).
% 0.19/0.41  cnf(c_0_42, negated_conjecture, (k2_lattice3(esk2_0)=X1|g1_orders_2(X2,X1)!=k3_lattice3(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_41]), c_0_37]), c_0_38])]), c_0_39])).
% 0.19/0.41  cnf(c_0_43, negated_conjecture, (u1_orders_2(k3_lattice3(esk2_0))=k2_lattice3(esk2_0)|~v1_orders_2(k3_lattice3(esk2_0))|~l1_orders_2(k3_lattice3(esk2_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_27])])).
% 0.19/0.41  cnf(c_0_44, negated_conjecture, (g1_orders_2(u1_struct_0(k3_lattice3(esk2_0)),k2_lattice3(esk2_0))=k3_lattice3(esk2_0)|~v1_orders_2(k3_lattice3(esk2_0))|~l1_orders_2(k3_lattice3(esk2_0))), inference(spm,[status(thm)],[c_0_27, c_0_43])).
% 0.19/0.42  fof(c_0_45, plain, ![X5, X6]:(~v1_xboole_0(X5)|(~m1_subset_1(X6,k1_zfmisc_1(X5))|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.19/0.42  fof(c_0_46, plain, ![X22]:((((m1_subset_1(esk1_1(X22),k1_zfmisc_1(u1_struct_0(X22)))|(v2_struct_0(X22)|~v10_lattices(X22)|~l3_lattices(X22)))&(~v1_xboole_0(esk1_1(X22))|(v2_struct_0(X22)|~v10_lattices(X22)|~l3_lattices(X22))))&(v18_lattices(esk1_1(X22),X22)|(v2_struct_0(X22)|~v10_lattices(X22)|~l3_lattices(X22))))&(v19_lattices(esk1_1(X22),X22)|(v2_struct_0(X22)|~v10_lattices(X22)|~l3_lattices(X22)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc14_lattices])])])])])).
% 0.19/0.42  fof(c_0_47, plain, ![X8, X9, X10]:((~r1_orders_2(X8,X9,X10)|r2_hidden(k4_tarski(X9,X10),u1_orders_2(X8))|~m1_subset_1(X10,u1_struct_0(X8))|~m1_subset_1(X9,u1_struct_0(X8))|~l1_orders_2(X8))&(~r2_hidden(k4_tarski(X9,X10),u1_orders_2(X8))|r1_orders_2(X8,X9,X10)|~m1_subset_1(X10,u1_struct_0(X8))|~m1_subset_1(X9,u1_struct_0(X8))|~l1_orders_2(X8))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).
% 0.19/0.42  fof(c_0_48, plain, ![X32, X33]:(v2_struct_0(X32)|~v10_lattices(X32)|~l3_lattices(X32)|~m1_subset_1(X33,u1_struct_0(X32))|m1_subset_1(k4_lattice3(X32,X33),u1_struct_0(k3_lattice3(X32)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_lattice3])])])).
% 0.19/0.42  cnf(c_0_49, negated_conjecture, (u1_struct_0(X1)=u1_struct_0(k3_lattice3(esk2_0))|v2_struct_0(X1)|k3_lattice3(X1)!=k3_lattice3(esk2_0)|~l3_lattices(X1)|~v10_lattices(X1)|~v1_orders_2(k3_lattice3(esk2_0))|~l1_orders_2(k3_lattice3(esk2_0))), inference(spm,[status(thm)],[c_0_33, c_0_44])).
% 0.19/0.42  fof(c_0_50, plain, ![X28, X29]:(v2_struct_0(X28)|~v10_lattices(X28)|~l3_lattices(X28)|(~m1_subset_1(X29,u1_struct_0(X28))|k4_lattice3(X28,X29)=X29)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattice3])])])])).
% 0.19/0.42  fof(c_0_51, plain, ![X24, X25, X26]:((~r2_hidden(k1_domain_1(u1_struct_0(X24),u1_struct_0(X24),X25,X26),k8_filter_1(X24))|r3_lattices(X24,X25,X26)|~m1_subset_1(X26,u1_struct_0(X24))|~m1_subset_1(X25,u1_struct_0(X24))|(v2_struct_0(X24)|~v10_lattices(X24)|~l3_lattices(X24)))&(~r3_lattices(X24,X25,X26)|r2_hidden(k1_domain_1(u1_struct_0(X24),u1_struct_0(X24),X25,X26),k8_filter_1(X24))|~m1_subset_1(X26,u1_struct_0(X24))|~m1_subset_1(X25,u1_struct_0(X24))|(v2_struct_0(X24)|~v10_lattices(X24)|~l3_lattices(X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_filter_1])])])])])).
% 0.19/0.42  fof(c_0_52, plain, ![X15, X16, X17, X18]:(v1_xboole_0(X15)|v1_xboole_0(X16)|~m1_subset_1(X17,X15)|~m1_subset_1(X18,X16)|k1_domain_1(X15,X16,X17,X18)=k4_tarski(X17,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k1_domain_1])])])).
% 0.19/0.42  cnf(c_0_53, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.42  cnf(c_0_54, plain, (m1_subset_1(esk1_1(X1),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.42  cnf(c_0_55, plain, (v2_struct_0(X1)|~v1_xboole_0(esk1_1(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.42  cnf(c_0_56, plain, (r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))|~r1_orders_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.42  cnf(c_0_57, plain, (v2_struct_0(X1)|m1_subset_1(k4_lattice3(X1,X2),u1_struct_0(k3_lattice3(X1)))|~v10_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.42  fof(c_0_58, plain, ![X19, X20, X21]:((~r3_orders_2(X19,X20,X21)|r1_orders_2(X19,X20,X21)|(v2_struct_0(X19)|~v3_orders_2(X19)|~l1_orders_2(X19)|~m1_subset_1(X20,u1_struct_0(X19))|~m1_subset_1(X21,u1_struct_0(X19))))&(~r1_orders_2(X19,X20,X21)|r3_orders_2(X19,X20,X21)|(v2_struct_0(X19)|~v3_orders_2(X19)|~l1_orders_2(X19)|~m1_subset_1(X20,u1_struct_0(X19))|~m1_subset_1(X21,u1_struct_0(X19))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.19/0.42  fof(c_0_59, plain, ![X34]:(((((~v2_struct_0(k3_lattice3(X34))|(v2_struct_0(X34)|~v10_lattices(X34)|~l3_lattices(X34)))&(v1_orders_2(k3_lattice3(X34))|(v2_struct_0(X34)|~v10_lattices(X34)|~l3_lattices(X34))))&(v3_orders_2(k3_lattice3(X34))|(v2_struct_0(X34)|~v10_lattices(X34)|~l3_lattices(X34))))&(v4_orders_2(k3_lattice3(X34))|(v2_struct_0(X34)|~v10_lattices(X34)|~l3_lattices(X34))))&(v5_orders_2(k3_lattice3(X34))|(v2_struct_0(X34)|~v10_lattices(X34)|~l3_lattices(X34)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_lattice3])])])])).
% 0.19/0.42  cnf(c_0_60, negated_conjecture, (u1_struct_0(X1)=u1_struct_0(k3_lattice3(esk2_0))|v2_struct_0(X1)|k3_lattice3(X1)!=k3_lattice3(esk2_0)|~l3_lattices(X1)|~v10_lattices(X1)|~l1_orders_2(k3_lattice3(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_29]), c_0_37]), c_0_38])]), c_0_39])).
% 0.19/0.42  cnf(c_0_61, plain, (v2_struct_0(X1)|k4_lattice3(X1,X2)=X2|~v10_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.42  cnf(c_0_62, plain, (r2_hidden(k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3),k8_filter_1(X1))|v2_struct_0(X1)|~r3_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.42  cnf(c_0_63, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|k1_domain_1(X1,X2,X3,X4)=k4_tarski(X3,X4)|~m1_subset_1(X3,X1)|~m1_subset_1(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.42  cnf(c_0_64, plain, (v2_struct_0(X1)|~l3_lattices(X1)|~v10_lattices(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])).
% 0.19/0.42  cnf(c_0_65, plain, (v2_struct_0(X1)|r2_hidden(k4_tarski(X2,k4_lattice3(X1,X3)),u1_orders_2(k3_lattice3(X1)))|~l3_lattices(X1)|~v10_lattices(X1)|~r1_orders_2(k3_lattice3(X1),X2,k4_lattice3(X1,X3))|~m1_subset_1(X2,u1_struct_0(k3_lattice3(X1)))|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_28])).
% 0.19/0.42  cnf(c_0_66, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r3_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.42  cnf(c_0_67, plain, (v3_orders_2(k3_lattice3(X1))|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.42  cnf(c_0_68, plain, (v2_struct_0(X1)|~v2_struct_0(k3_lattice3(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.19/0.42  cnf(c_0_69, negated_conjecture, (r3_lattices(esk2_0,esk3_0,esk4_0)|r3_orders_2(k3_lattice3(esk2_0),k4_lattice3(esk2_0,esk3_0),k4_lattice3(esk2_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.42  cnf(c_0_70, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.42  cnf(c_0_71, negated_conjecture, (u1_struct_0(X1)=u1_struct_0(k3_lattice3(esk2_0))|v2_struct_0(X1)|k3_lattice3(X1)!=k3_lattice3(esk2_0)|~l3_lattices(X1)|~v10_lattices(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_28]), c_0_37]), c_0_38])]), c_0_39])).
% 0.19/0.42  cnf(c_0_72, plain, (r3_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.42  cnf(c_0_73, plain, (v2_struct_0(X1)|m1_subset_1(X2,u1_struct_0(k3_lattice3(X1)))|~l3_lattices(X1)|~v10_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_57, c_0_61])).
% 0.19/0.42  cnf(c_0_74, plain, (v2_struct_0(X1)|r2_hidden(k4_tarski(X2,X3),k8_filter_1(X1))|~r3_lattices(X1,X2,X3)|~l3_lattices(X1)|~v10_lattices(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])).
% 0.19/0.42  cnf(c_0_75, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.42  cnf(c_0_76, plain, (v2_struct_0(X1)|r2_hidden(k4_tarski(X2,k4_lattice3(X1,X3)),u1_orders_2(k3_lattice3(X1)))|~l3_lattices(X1)|~v10_lattices(X1)|~r3_orders_2(k3_lattice3(X1),X2,k4_lattice3(X1,X3))|~m1_subset_1(X2,u1_struct_0(k3_lattice3(X1)))|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_57]), c_0_28]), c_0_67]), c_0_68])).
% 0.19/0.42  cnf(c_0_77, negated_conjecture, (r3_lattices(esk2_0,esk3_0,esk4_0)|r3_orders_2(k3_lattice3(esk2_0),esk3_0,k4_lattice3(esk2_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_61]), c_0_37]), c_0_38]), c_0_70])]), c_0_39])).
% 0.19/0.42  cnf(c_0_78, negated_conjecture, (u1_struct_0(k3_lattice3(esk2_0))=u1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_71]), c_0_37]), c_0_38])]), c_0_39])).
% 0.19/0.42  cnf(c_0_79, negated_conjecture, (~r3_lattices(esk2_0,esk3_0,esk4_0)|~r3_orders_2(k3_lattice3(esk2_0),k4_lattice3(esk2_0,esk3_0),k4_lattice3(esk2_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.42  cnf(c_0_80, plain, (r3_orders_2(k3_lattice3(X1),X2,X3)|v2_struct_0(X1)|~l3_lattices(X1)|~v10_lattices(X1)|~r1_orders_2(k3_lattice3(X1),X2,X3)|~m1_subset_1(X2,u1_struct_0(k3_lattice3(X1)))|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_28]), c_0_67]), c_0_68])).
% 0.19/0.42  cnf(c_0_81, negated_conjecture, (r2_hidden(k4_tarski(X1,esk4_0),k8_filter_1(esk2_0))|~r3_lattices(esk2_0,X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_37]), c_0_38])]), c_0_39])).
% 0.19/0.42  cnf(c_0_82, negated_conjecture, (r3_lattices(esk2_0,esk3_0,esk4_0)|r2_hidden(k4_tarski(esk3_0,k4_lattice3(esk2_0,esk4_0)),u1_orders_2(k3_lattice3(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_37]), c_0_38]), c_0_78]), c_0_70]), c_0_75])]), c_0_39])).
% 0.19/0.42  cnf(c_0_83, negated_conjecture, (~r3_lattices(esk2_0,esk3_0,esk4_0)|~r3_orders_2(k3_lattice3(esk2_0),k4_lattice3(esk2_0,esk3_0),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_61]), c_0_37]), c_0_38]), c_0_75])]), c_0_39])).
% 0.19/0.42  cnf(c_0_84, negated_conjecture, (r3_orders_2(k3_lattice3(esk2_0),X1,X2)|~r1_orders_2(k3_lattice3(esk2_0),X1,X2)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_subset_1(X2,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_78]), c_0_37]), c_0_38])]), c_0_39])).
% 0.19/0.42  cnf(c_0_85, plain, (r1_orders_2(X3,X1,X2)|~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.42  cnf(c_0_86, negated_conjecture, (r2_hidden(k4_tarski(esk3_0,k4_lattice3(esk2_0,esk4_0)),u1_orders_2(k3_lattice3(esk2_0)))|r2_hidden(k4_tarski(esk3_0,esk4_0),k8_filter_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_70])])).
% 0.19/0.42  cnf(c_0_87, negated_conjecture, (~r3_lattices(esk2_0,esk3_0,esk4_0)|~r3_orders_2(k3_lattice3(esk2_0),esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_61]), c_0_37]), c_0_38]), c_0_70])]), c_0_39])).
% 0.19/0.42  cnf(c_0_88, negated_conjecture, (r3_orders_2(k3_lattice3(esk2_0),X1,X2)|~r2_hidden(k4_tarski(X1,X2),u1_orders_2(k3_lattice3(esk2_0)))|~l1_orders_2(k3_lattice3(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_subset_1(X2,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_78]), c_0_78])])).
% 0.19/0.42  cnf(c_0_89, negated_conjecture, (r2_hidden(k4_tarski(esk3_0,esk4_0),u1_orders_2(k3_lattice3(esk2_0)))|r2_hidden(k4_tarski(esk3_0,esk4_0),k8_filter_1(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_61]), c_0_37]), c_0_38]), c_0_75])]), c_0_39])).
% 0.19/0.42  fof(c_0_90, plain, ![X35]:(v2_struct_0(X35)|~v10_lattices(X35)|~l3_lattices(X35)|k2_lattice3(X35)=k8_filter_1(X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k2_lattice3])])])).
% 0.19/0.42  cnf(c_0_91, negated_conjecture, (~r3_lattices(esk2_0,esk3_0,esk4_0)|~r2_hidden(k4_tarski(esk3_0,esk4_0),u1_orders_2(k3_lattice3(esk2_0)))|~l1_orders_2(k3_lattice3(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_70]), c_0_75])])).
% 0.19/0.42  cnf(c_0_92, negated_conjecture, (r2_hidden(k4_tarski(esk3_0,esk4_0),k8_filter_1(esk2_0))|r2_hidden(k4_tarski(esk3_0,esk4_0),k2_lattice3(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_31]), c_0_37]), c_0_38])]), c_0_39])).
% 0.19/0.42  cnf(c_0_93, plain, (v2_struct_0(X1)|k2_lattice3(X1)=k8_filter_1(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.19/0.42  cnf(c_0_94, negated_conjecture, (~r3_lattices(esk2_0,esk3_0,esk4_0)|~r2_hidden(k4_tarski(esk3_0,esk4_0),k2_lattice3(esk2_0))|~l1_orders_2(k3_lattice3(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_31]), c_0_37]), c_0_38])]), c_0_39])).
% 0.19/0.42  cnf(c_0_95, negated_conjecture, (r2_hidden(k4_tarski(esk3_0,esk4_0),k2_lattice3(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_37]), c_0_38])]), c_0_39])).
% 0.19/0.42  cnf(c_0_96, negated_conjecture, (~r3_lattices(esk2_0,esk3_0,esk4_0)|~l1_orders_2(k3_lattice3(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_95])])).
% 0.19/0.42  cnf(c_0_97, plain, (r3_lattices(X1,X2,X3)|v2_struct_0(X1)|~r2_hidden(k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3),k8_filter_1(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.42  cnf(c_0_98, negated_conjecture, (~r2_hidden(k1_domain_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),esk3_0,esk4_0),k8_filter_1(esk2_0))|~l1_orders_2(k3_lattice3(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_37]), c_0_38]), c_0_75]), c_0_70])]), c_0_39])).
% 0.19/0.42  cnf(c_0_99, negated_conjecture, (~r2_hidden(k1_domain_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),esk3_0,esk4_0),k2_lattice3(esk2_0))|~l1_orders_2(k3_lattice3(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_93]), c_0_37]), c_0_38])]), c_0_39])).
% 0.19/0.42  cnf(c_0_100, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))|~l1_orders_2(k3_lattice3(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_63]), c_0_95]), c_0_75]), c_0_70])])).
% 0.19/0.42  cnf(c_0_101, negated_conjecture, (~l1_orders_2(k3_lattice3(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_100]), c_0_37]), c_0_38])]), c_0_39])).
% 0.19/0.42  cnf(c_0_102, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_28]), c_0_37]), c_0_38])]), c_0_39]), ['proof']).
% 0.19/0.42  # SZS output end CNFRefutation
% 0.19/0.42  # Proof object total steps             : 103
% 0.19/0.42  # Proof object clause steps            : 70
% 0.19/0.42  # Proof object formula steps           : 33
% 0.19/0.42  # Proof object conjectures             : 38
% 0.19/0.42  # Proof object clause conjectures      : 35
% 0.19/0.42  # Proof object formula conjectures     : 3
% 0.19/0.42  # Proof object initial clauses used    : 29
% 0.19/0.42  # Proof object initial formulas used   : 16
% 0.19/0.42  # Proof object generating inferences   : 40
% 0.19/0.42  # Proof object simplifying inferences  : 114
% 0.19/0.42  # Training examples: 0 positive, 0 negative
% 0.19/0.42  # Parsed axioms                        : 16
% 0.19/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.42  # Initial clauses                      : 41
% 0.19/0.42  # Removed in clause preprocessing      : 0
% 0.19/0.42  # Initial clauses in saturation        : 41
% 0.19/0.42  # Processed clauses                    : 445
% 0.19/0.42  # ...of these trivial                  : 2
% 0.19/0.42  # ...subsumed                          : 178
% 0.19/0.42  # ...remaining for further processing  : 265
% 0.19/0.42  # Other redundant clauses eliminated   : 11
% 0.19/0.42  # Clauses deleted for lack of memory   : 0
% 0.19/0.42  # Backward-subsumed                    : 40
% 0.19/0.42  # Backward-rewritten                   : 5
% 0.19/0.42  # Generated clauses                    : 998
% 0.19/0.42  # ...of the previous two non-trivial   : 901
% 0.19/0.42  # Contextual simplify-reflections      : 40
% 0.19/0.42  # Paramodulations                      : 972
% 0.19/0.42  # Factorizations                       : 0
% 0.19/0.42  # Equation resolutions                 : 26
% 0.19/0.42  # Propositional unsat checks           : 0
% 0.19/0.42  #    Propositional check models        : 0
% 0.19/0.42  #    Propositional check unsatisfiable : 0
% 0.19/0.42  #    Propositional clauses             : 0
% 0.19/0.42  #    Propositional clauses after purity: 0
% 0.19/0.42  #    Propositional unsat core size     : 0
% 0.19/0.42  #    Propositional preprocessing time  : 0.000
% 0.19/0.42  #    Propositional encoding time       : 0.000
% 0.19/0.42  #    Propositional solver time         : 0.000
% 0.19/0.42  #    Success case prop preproc time    : 0.000
% 0.19/0.42  #    Success case prop encoding time   : 0.000
% 0.19/0.42  #    Success case prop solver time     : 0.000
% 0.19/0.42  # Current number of processed clauses  : 183
% 0.19/0.42  #    Positive orientable unit clauses  : 11
% 0.19/0.42  #    Positive unorientable unit clauses: 0
% 0.19/0.42  #    Negative unit clauses             : 2
% 0.19/0.42  #    Non-unit-clauses                  : 170
% 0.19/0.42  # Current number of unprocessed clauses: 518
% 0.19/0.42  # ...number of literals in the above   : 4450
% 0.19/0.42  # Current number of archived formulas  : 0
% 0.19/0.42  # Current number of archived clauses   : 82
% 0.19/0.42  # Clause-clause subsumption calls (NU) : 9378
% 0.19/0.42  # Rec. Clause-clause subsumption calls : 869
% 0.19/0.42  # Non-unit clause-clause subsumptions  : 252
% 0.19/0.42  # Unit Clause-clause subsumption calls : 183
% 0.19/0.42  # Rewrite failures with RHS unbound    : 0
% 0.19/0.42  # BW rewrite match attempts            : 7
% 0.19/0.42  # BW rewrite match successes           : 7
% 0.19/0.42  # Condensation attempts                : 0
% 0.19/0.42  # Condensation successes               : 0
% 0.19/0.42  # Termbank termtop insertions          : 31862
% 0.19/0.42  
% 0.19/0.42  # -------------------------------------------------
% 0.19/0.42  # User time                : 0.076 s
% 0.19/0.42  # System time              : 0.005 s
% 0.19/0.42  # Total time               : 0.081 s
% 0.19/0.42  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
