%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:34 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 210 expanded)
%              Number of clauses        :   33 (  71 expanded)
%              Number of leaves         :    8 (  51 expanded)
%              Depth                    :   11
%              Number of atoms          :  275 (1619 expanded)
%              Number of equality atoms :   22 (  22 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal clause size      :   61 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t10_waybel_9,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & v4_orders_2(X3)
                & v7_waybel_0(X3)
                & l1_waybel_0(X3,X1) )
             => ( ~ v2_struct_0(k3_waybel_2(X1,X2,X3))
                & v4_orders_2(k3_waybel_2(X1,X2,X3))
                & v7_waybel_0(k3_waybel_2(X1,X2,X3))
                & l1_waybel_0(k3_waybel_2(X1,X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_waybel_9)).

fof(dt_k3_waybel_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & ~ v2_struct_0(X3)
        & l1_waybel_0(X3,X1) )
     => ( v6_waybel_0(k3_waybel_2(X1,X2,X3),X1)
        & l1_waybel_0(k3_waybel_2(X1,X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_waybel_2)).

fof(d3_waybel_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & l1_waybel_0(X3,X1) )
             => ! [X4] :
                  ( ( v6_waybel_0(X4,X1)
                    & l1_waybel_0(X4,X1) )
                 => ( X4 = k3_waybel_2(X1,X2,X3)
                  <=> ( g1_orders_2(u1_struct_0(X4),u1_orders_2(X4)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                      & ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X4))
                         => ? [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X1))
                              & X6 = k1_funct_1(u1_waybel_0(X1,X3),X5)
                              & k1_funct_1(u1_waybel_0(X1,X4),X5) = k11_lattice3(X1,X2,X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_waybel_2)).

fof(dt_l1_waybel_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => l1_orders_2(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(fc5_waybel_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & ~ v2_struct_0(X3)
        & l1_waybel_0(X3,X1) )
     => ( ~ v2_struct_0(k3_waybel_2(X1,X2,X3))
        & v6_waybel_0(k3_waybel_2(X1,X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_waybel_2)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(l16_yellow_6,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ( v4_orders_2(X1)
      <=> v4_orders_2(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l16_yellow_6)).

fof(fc6_waybel_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & ~ v2_struct_0(X3)
        & v7_waybel_0(X3)
        & l1_waybel_0(X3,X1) )
     => ( v6_waybel_0(k3_waybel_2(X1,X2,X3),X1)
        & v7_waybel_0(k3_waybel_2(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_waybel_2)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & v4_orders_2(X3)
                  & v7_waybel_0(X3)
                  & l1_waybel_0(X3,X1) )
               => ( ~ v2_struct_0(k3_waybel_2(X1,X2,X3))
                  & v4_orders_2(k3_waybel_2(X1,X2,X3))
                  & v7_waybel_0(k3_waybel_2(X1,X2,X3))
                  & l1_waybel_0(k3_waybel_2(X1,X2,X3),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t10_waybel_9])).

fof(c_0_9,plain,(
    ! [X19,X20,X21] :
      ( ( v6_waybel_0(k3_waybel_2(X19,X20,X21),X19)
        | v2_struct_0(X19)
        | ~ l1_orders_2(X19)
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | v2_struct_0(X21)
        | ~ l1_waybel_0(X21,X19) )
      & ( l1_waybel_0(k3_waybel_2(X19,X20,X21),X19)
        | v2_struct_0(X19)
        | ~ l1_orders_2(X19)
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | v2_struct_0(X21)
        | ~ l1_waybel_0(X21,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_waybel_2])])])])).

fof(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & l1_orders_2(esk3_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    & ~ v2_struct_0(esk5_0)
    & v4_orders_2(esk5_0)
    & v7_waybel_0(esk5_0)
    & l1_waybel_0(esk5_0,esk3_0)
    & ( v2_struct_0(k3_waybel_2(esk3_0,esk4_0,esk5_0))
      | ~ v4_orders_2(k3_waybel_2(esk3_0,esk4_0,esk5_0))
      | ~ v7_waybel_0(k3_waybel_2(esk3_0,esk4_0,esk5_0))
      | ~ l1_waybel_0(k3_waybel_2(esk3_0,esk4_0,esk5_0),esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

fof(c_0_11,plain,(
    ! [X11,X12,X13,X14,X15,X18] :
      ( ( g1_orders_2(u1_struct_0(X14),u1_orders_2(X14)) = g1_orders_2(u1_struct_0(X13),u1_orders_2(X13))
        | X14 != k3_waybel_2(X11,X12,X13)
        | ~ v6_waybel_0(X14,X11)
        | ~ l1_waybel_0(X14,X11)
        | v2_struct_0(X13)
        | ~ l1_waybel_0(X13,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X11))
        | v2_struct_0(X11)
        | ~ l1_orders_2(X11) )
      & ( m1_subset_1(esk1_5(X11,X12,X13,X14,X15),u1_struct_0(X11))
        | ~ m1_subset_1(X15,u1_struct_0(X14))
        | X14 != k3_waybel_2(X11,X12,X13)
        | ~ v6_waybel_0(X14,X11)
        | ~ l1_waybel_0(X14,X11)
        | v2_struct_0(X13)
        | ~ l1_waybel_0(X13,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X11))
        | v2_struct_0(X11)
        | ~ l1_orders_2(X11) )
      & ( esk1_5(X11,X12,X13,X14,X15) = k1_funct_1(u1_waybel_0(X11,X13),X15)
        | ~ m1_subset_1(X15,u1_struct_0(X14))
        | X14 != k3_waybel_2(X11,X12,X13)
        | ~ v6_waybel_0(X14,X11)
        | ~ l1_waybel_0(X14,X11)
        | v2_struct_0(X13)
        | ~ l1_waybel_0(X13,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X11))
        | v2_struct_0(X11)
        | ~ l1_orders_2(X11) )
      & ( k1_funct_1(u1_waybel_0(X11,X14),X15) = k11_lattice3(X11,X12,esk1_5(X11,X12,X13,X14,X15))
        | ~ m1_subset_1(X15,u1_struct_0(X14))
        | X14 != k3_waybel_2(X11,X12,X13)
        | ~ v6_waybel_0(X14,X11)
        | ~ l1_waybel_0(X14,X11)
        | v2_struct_0(X13)
        | ~ l1_waybel_0(X13,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X11))
        | v2_struct_0(X11)
        | ~ l1_orders_2(X11) )
      & ( m1_subset_1(esk2_4(X11,X12,X13,X14),u1_struct_0(X14))
        | g1_orders_2(u1_struct_0(X14),u1_orders_2(X14)) != g1_orders_2(u1_struct_0(X13),u1_orders_2(X13))
        | X14 = k3_waybel_2(X11,X12,X13)
        | ~ v6_waybel_0(X14,X11)
        | ~ l1_waybel_0(X14,X11)
        | v2_struct_0(X13)
        | ~ l1_waybel_0(X13,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X11))
        | v2_struct_0(X11)
        | ~ l1_orders_2(X11) )
      & ( ~ m1_subset_1(X18,u1_struct_0(X11))
        | X18 != k1_funct_1(u1_waybel_0(X11,X13),esk2_4(X11,X12,X13,X14))
        | k1_funct_1(u1_waybel_0(X11,X14),esk2_4(X11,X12,X13,X14)) != k11_lattice3(X11,X12,X18)
        | g1_orders_2(u1_struct_0(X14),u1_orders_2(X14)) != g1_orders_2(u1_struct_0(X13),u1_orders_2(X13))
        | X14 = k3_waybel_2(X11,X12,X13)
        | ~ v6_waybel_0(X14,X11)
        | ~ l1_waybel_0(X14,X11)
        | v2_struct_0(X13)
        | ~ l1_waybel_0(X13,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X11))
        | v2_struct_0(X11)
        | ~ l1_orders_2(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_waybel_2])])])])])])).

cnf(c_0_12,plain,
    ( l1_waybel_0(k3_waybel_2(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_waybel_0(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( l1_waybel_0(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | X1 != k3_waybel_2(X3,X4,X2)
    | ~ v6_waybel_0(X1,X3)
    | ~ l1_waybel_0(X1,X3)
    | ~ l1_waybel_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( v6_waybel_0(k3_waybel_2(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_waybel_0(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_19,plain,(
    ! [X8,X9] :
      ( ~ l1_struct_0(X8)
      | ~ l1_waybel_0(X9,X8)
      | l1_orders_2(X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).

cnf(c_0_20,negated_conjecture,
    ( l1_waybel_0(k3_waybel_2(esk3_0,X1,esk5_0),esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])]),c_0_15]),c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_22,plain,(
    ! [X22,X23,X24] :
      ( ( ~ v2_struct_0(k3_waybel_2(X22,X23,X24))
        | v2_struct_0(X22)
        | ~ l1_orders_2(X22)
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | v2_struct_0(X24)
        | ~ l1_waybel_0(X24,X22) )
      & ( v6_waybel_0(k3_waybel_2(X22,X23,X24),X22)
        | v2_struct_0(X22)
        | ~ l1_orders_2(X22)
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | v2_struct_0(X24)
        | ~ l1_waybel_0(X24,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_waybel_2])])])])).

cnf(c_0_23,plain,
    ( g1_orders_2(u1_struct_0(k3_waybel_2(X1,X2,X3)),u1_orders_2(k3_waybel_2(X1,X2,X3))) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_waybel_0(X3,X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_17]),c_0_12]),c_0_18])).

cnf(c_0_24,plain,
    ( l1_orders_2(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( l1_waybel_0(k3_waybel_2(esk3_0,esk4_0,esk5_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_26,plain,(
    ! [X7] :
      ( ~ l1_orders_2(X7)
      | l1_struct_0(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k3_waybel_2(X1,X2,X3))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_waybel_0(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_28,plain,(
    ! [X10] :
      ( ( ~ v4_orders_2(X10)
        | v4_orders_2(g1_orders_2(u1_struct_0(X10),u1_orders_2(X10)))
        | v2_struct_0(X10)
        | ~ l1_orders_2(X10) )
      & ( ~ v4_orders_2(g1_orders_2(u1_struct_0(X10),u1_orders_2(X10)))
        | v4_orders_2(X10)
        | v2_struct_0(X10)
        | ~ l1_orders_2(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l16_yellow_6])])])])).

cnf(c_0_29,negated_conjecture,
    ( g1_orders_2(u1_struct_0(k3_waybel_2(esk3_0,X1,esk5_0)),u1_orders_2(k3_waybel_2(esk3_0,X1,esk5_0))) = g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_13]),c_0_14])]),c_0_15]),c_0_16])).

cnf(c_0_30,negated_conjecture,
    ( l1_orders_2(k3_waybel_2(esk3_0,esk4_0,esk5_0))
    | ~ l1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ v2_struct_0(k3_waybel_2(esk3_0,X1,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_13]),c_0_14])]),c_0_15]),c_0_16])).

cnf(c_0_33,plain,
    ( v4_orders_2(X1)
    | v2_struct_0(X1)
    | ~ v4_orders_2(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( g1_orders_2(u1_struct_0(k3_waybel_2(esk3_0,esk4_0,esk5_0)),u1_orders_2(k3_waybel_2(esk3_0,esk4_0,esk5_0))) = g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_21])).

cnf(c_0_35,negated_conjecture,
    ( l1_orders_2(k3_waybel_2(esk3_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_14])])).

cnf(c_0_36,negated_conjecture,
    ( ~ v2_struct_0(k3_waybel_2(esk3_0,esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_21])).

cnf(c_0_37,negated_conjecture,
    ( l1_orders_2(esk5_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_13])).

cnf(c_0_38,negated_conjecture,
    ( v2_struct_0(k3_waybel_2(esk3_0,esk4_0,esk5_0))
    | ~ v4_orders_2(k3_waybel_2(esk3_0,esk4_0,esk5_0))
    | ~ v7_waybel_0(k3_waybel_2(esk3_0,esk4_0,esk5_0))
    | ~ l1_waybel_0(k3_waybel_2(esk3_0,esk4_0,esk5_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_39,negated_conjecture,
    ( v4_orders_2(k3_waybel_2(esk3_0,esk4_0,esk5_0))
    | ~ v4_orders_2(g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_40,plain,
    ( v4_orders_2(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)))
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,negated_conjecture,
    ( v4_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_42,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_31]),c_0_14])])).

cnf(c_0_43,negated_conjecture,
    ( ~ v7_waybel_0(k3_waybel_2(esk3_0,esk4_0,esk5_0))
    | ~ v4_orders_2(k3_waybel_2(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_25])]),c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( v4_orders_2(k3_waybel_2(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_42])]),c_0_15])).

fof(c_0_45,plain,(
    ! [X25,X26,X27] :
      ( ( v6_waybel_0(k3_waybel_2(X25,X26,X27),X25)
        | v2_struct_0(X25)
        | ~ l1_orders_2(X25)
        | ~ m1_subset_1(X26,u1_struct_0(X25))
        | v2_struct_0(X27)
        | ~ v7_waybel_0(X27)
        | ~ l1_waybel_0(X27,X25) )
      & ( v7_waybel_0(k3_waybel_2(X25,X26,X27))
        | v2_struct_0(X25)
        | ~ l1_orders_2(X25)
        | ~ m1_subset_1(X26,u1_struct_0(X25))
        | v2_struct_0(X27)
        | ~ v7_waybel_0(X27)
        | ~ l1_waybel_0(X27,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_waybel_2])])])])).

cnf(c_0_46,negated_conjecture,
    ( ~ v7_waybel_0(k3_waybel_2(esk3_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44])])).

cnf(c_0_47,plain,
    ( v7_waybel_0(k3_waybel_2(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_48,negated_conjecture,
    ( v7_waybel_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_21]),c_0_13]),c_0_14])]),c_0_15]),c_0_16]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:25:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.13/0.38  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t10_waybel_9, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:((((~(v2_struct_0(X3))&v4_orders_2(X3))&v7_waybel_0(X3))&l1_waybel_0(X3,X1))=>(((~(v2_struct_0(k3_waybel_2(X1,X2,X3)))&v4_orders_2(k3_waybel_2(X1,X2,X3)))&v7_waybel_0(k3_waybel_2(X1,X2,X3)))&l1_waybel_0(k3_waybel_2(X1,X2,X3),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_waybel_9)).
% 0.13/0.38  fof(dt_k3_waybel_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&~(v2_struct_0(X3)))&l1_waybel_0(X3,X1))=>(v6_waybel_0(k3_waybel_2(X1,X2,X3),X1)&l1_waybel_0(k3_waybel_2(X1,X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_waybel_2)).
% 0.13/0.38  fof(d3_waybel_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:((~(v2_struct_0(X3))&l1_waybel_0(X3,X1))=>![X4]:((v6_waybel_0(X4,X1)&l1_waybel_0(X4,X1))=>(X4=k3_waybel_2(X1,X2,X3)<=>(g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))=g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))&![X5]:(m1_subset_1(X5,u1_struct_0(X4))=>?[X6]:((m1_subset_1(X6,u1_struct_0(X1))&X6=k1_funct_1(u1_waybel_0(X1,X3),X5))&k1_funct_1(u1_waybel_0(X1,X4),X5)=k11_lattice3(X1,X2,X6))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_waybel_2)).
% 0.13/0.38  fof(dt_l1_waybel_0, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_waybel_0(X2,X1)=>l1_orders_2(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 0.13/0.38  fof(fc5_waybel_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&~(v2_struct_0(X3)))&l1_waybel_0(X3,X1))=>(~(v2_struct_0(k3_waybel_2(X1,X2,X3)))&v6_waybel_0(k3_waybel_2(X1,X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_waybel_2)).
% 0.13/0.38  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.13/0.38  fof(l16_yellow_6, axiom, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>(v4_orders_2(X1)<=>v4_orders_2(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l16_yellow_6)).
% 0.13/0.38  fof(fc6_waybel_2, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&~(v2_struct_0(X3)))&v7_waybel_0(X3))&l1_waybel_0(X3,X1))=>(v6_waybel_0(k3_waybel_2(X1,X2,X3),X1)&v7_waybel_0(k3_waybel_2(X1,X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_waybel_2)).
% 0.13/0.38  fof(c_0_8, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:((((~(v2_struct_0(X3))&v4_orders_2(X3))&v7_waybel_0(X3))&l1_waybel_0(X3,X1))=>(((~(v2_struct_0(k3_waybel_2(X1,X2,X3)))&v4_orders_2(k3_waybel_2(X1,X2,X3)))&v7_waybel_0(k3_waybel_2(X1,X2,X3)))&l1_waybel_0(k3_waybel_2(X1,X2,X3),X1)))))), inference(assume_negation,[status(cth)],[t10_waybel_9])).
% 0.13/0.38  fof(c_0_9, plain, ![X19, X20, X21]:((v6_waybel_0(k3_waybel_2(X19,X20,X21),X19)|(v2_struct_0(X19)|~l1_orders_2(X19)|~m1_subset_1(X20,u1_struct_0(X19))|v2_struct_0(X21)|~l1_waybel_0(X21,X19)))&(l1_waybel_0(k3_waybel_2(X19,X20,X21),X19)|(v2_struct_0(X19)|~l1_orders_2(X19)|~m1_subset_1(X20,u1_struct_0(X19))|v2_struct_0(X21)|~l1_waybel_0(X21,X19)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_waybel_2])])])])).
% 0.13/0.38  fof(c_0_10, negated_conjecture, ((~v2_struct_0(esk3_0)&l1_orders_2(esk3_0))&(m1_subset_1(esk4_0,u1_struct_0(esk3_0))&((((~v2_struct_0(esk5_0)&v4_orders_2(esk5_0))&v7_waybel_0(esk5_0))&l1_waybel_0(esk5_0,esk3_0))&(v2_struct_0(k3_waybel_2(esk3_0,esk4_0,esk5_0))|~v4_orders_2(k3_waybel_2(esk3_0,esk4_0,esk5_0))|~v7_waybel_0(k3_waybel_2(esk3_0,esk4_0,esk5_0))|~l1_waybel_0(k3_waybel_2(esk3_0,esk4_0,esk5_0),esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).
% 0.13/0.38  fof(c_0_11, plain, ![X11, X12, X13, X14, X15, X18]:(((g1_orders_2(u1_struct_0(X14),u1_orders_2(X14))=g1_orders_2(u1_struct_0(X13),u1_orders_2(X13))|X14!=k3_waybel_2(X11,X12,X13)|(~v6_waybel_0(X14,X11)|~l1_waybel_0(X14,X11))|(v2_struct_0(X13)|~l1_waybel_0(X13,X11))|~m1_subset_1(X12,u1_struct_0(X11))|(v2_struct_0(X11)|~l1_orders_2(X11)))&(((m1_subset_1(esk1_5(X11,X12,X13,X14,X15),u1_struct_0(X11))|~m1_subset_1(X15,u1_struct_0(X14))|X14!=k3_waybel_2(X11,X12,X13)|(~v6_waybel_0(X14,X11)|~l1_waybel_0(X14,X11))|(v2_struct_0(X13)|~l1_waybel_0(X13,X11))|~m1_subset_1(X12,u1_struct_0(X11))|(v2_struct_0(X11)|~l1_orders_2(X11)))&(esk1_5(X11,X12,X13,X14,X15)=k1_funct_1(u1_waybel_0(X11,X13),X15)|~m1_subset_1(X15,u1_struct_0(X14))|X14!=k3_waybel_2(X11,X12,X13)|(~v6_waybel_0(X14,X11)|~l1_waybel_0(X14,X11))|(v2_struct_0(X13)|~l1_waybel_0(X13,X11))|~m1_subset_1(X12,u1_struct_0(X11))|(v2_struct_0(X11)|~l1_orders_2(X11))))&(k1_funct_1(u1_waybel_0(X11,X14),X15)=k11_lattice3(X11,X12,esk1_5(X11,X12,X13,X14,X15))|~m1_subset_1(X15,u1_struct_0(X14))|X14!=k3_waybel_2(X11,X12,X13)|(~v6_waybel_0(X14,X11)|~l1_waybel_0(X14,X11))|(v2_struct_0(X13)|~l1_waybel_0(X13,X11))|~m1_subset_1(X12,u1_struct_0(X11))|(v2_struct_0(X11)|~l1_orders_2(X11)))))&((m1_subset_1(esk2_4(X11,X12,X13,X14),u1_struct_0(X14))|g1_orders_2(u1_struct_0(X14),u1_orders_2(X14))!=g1_orders_2(u1_struct_0(X13),u1_orders_2(X13))|X14=k3_waybel_2(X11,X12,X13)|(~v6_waybel_0(X14,X11)|~l1_waybel_0(X14,X11))|(v2_struct_0(X13)|~l1_waybel_0(X13,X11))|~m1_subset_1(X12,u1_struct_0(X11))|(v2_struct_0(X11)|~l1_orders_2(X11)))&(~m1_subset_1(X18,u1_struct_0(X11))|X18!=k1_funct_1(u1_waybel_0(X11,X13),esk2_4(X11,X12,X13,X14))|k1_funct_1(u1_waybel_0(X11,X14),esk2_4(X11,X12,X13,X14))!=k11_lattice3(X11,X12,X18)|g1_orders_2(u1_struct_0(X14),u1_orders_2(X14))!=g1_orders_2(u1_struct_0(X13),u1_orders_2(X13))|X14=k3_waybel_2(X11,X12,X13)|(~v6_waybel_0(X14,X11)|~l1_waybel_0(X14,X11))|(v2_struct_0(X13)|~l1_waybel_0(X13,X11))|~m1_subset_1(X12,u1_struct_0(X11))|(v2_struct_0(X11)|~l1_orders_2(X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_waybel_2])])])])])])).
% 0.13/0.38  cnf(c_0_12, plain, (l1_waybel_0(k3_waybel_2(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X3)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_waybel_0(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_13, negated_conjecture, (l1_waybel_0(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_14, negated_conjecture, (l1_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_15, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_16, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_17, plain, (g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))=g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))|v2_struct_0(X2)|v2_struct_0(X3)|X1!=k3_waybel_2(X3,X4,X2)|~v6_waybel_0(X1,X3)|~l1_waybel_0(X1,X3)|~l1_waybel_0(X2,X3)|~m1_subset_1(X4,u1_struct_0(X3))|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_18, plain, (v6_waybel_0(k3_waybel_2(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X3)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_waybel_0(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  fof(c_0_19, plain, ![X8, X9]:(~l1_struct_0(X8)|(~l1_waybel_0(X9,X8)|l1_orders_2(X9))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).
% 0.13/0.38  cnf(c_0_20, negated_conjecture, (l1_waybel_0(k3_waybel_2(esk3_0,X1,esk5_0),esk3_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])]), c_0_15]), c_0_16])).
% 0.13/0.38  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  fof(c_0_22, plain, ![X22, X23, X24]:((~v2_struct_0(k3_waybel_2(X22,X23,X24))|(v2_struct_0(X22)|~l1_orders_2(X22)|~m1_subset_1(X23,u1_struct_0(X22))|v2_struct_0(X24)|~l1_waybel_0(X24,X22)))&(v6_waybel_0(k3_waybel_2(X22,X23,X24),X22)|(v2_struct_0(X22)|~l1_orders_2(X22)|~m1_subset_1(X23,u1_struct_0(X22))|v2_struct_0(X24)|~l1_waybel_0(X24,X22)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_waybel_2])])])])).
% 0.13/0.38  cnf(c_0_23, plain, (g1_orders_2(u1_struct_0(k3_waybel_2(X1,X2,X3)),u1_orders_2(k3_waybel_2(X1,X2,X3)))=g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))|v2_struct_0(X1)|v2_struct_0(X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_waybel_0(X3,X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_17]), c_0_12]), c_0_18])).
% 0.13/0.38  cnf(c_0_24, plain, (l1_orders_2(X2)|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (l1_waybel_0(k3_waybel_2(esk3_0,esk4_0,esk5_0),esk3_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.38  fof(c_0_26, plain, ![X7]:(~l1_orders_2(X7)|l1_struct_0(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.13/0.38  cnf(c_0_27, plain, (v2_struct_0(X1)|v2_struct_0(X3)|~v2_struct_0(k3_waybel_2(X1,X2,X3))|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_waybel_0(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  fof(c_0_28, plain, ![X10]:((~v4_orders_2(X10)|v4_orders_2(g1_orders_2(u1_struct_0(X10),u1_orders_2(X10)))|(v2_struct_0(X10)|~l1_orders_2(X10)))&(~v4_orders_2(g1_orders_2(u1_struct_0(X10),u1_orders_2(X10)))|v4_orders_2(X10)|(v2_struct_0(X10)|~l1_orders_2(X10)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l16_yellow_6])])])])).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (g1_orders_2(u1_struct_0(k3_waybel_2(esk3_0,X1,esk5_0)),u1_orders_2(k3_waybel_2(esk3_0,X1,esk5_0)))=g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_13]), c_0_14])]), c_0_15]), c_0_16])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (l1_orders_2(k3_waybel_2(esk3_0,esk4_0,esk5_0))|~l1_struct_0(esk3_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.13/0.38  cnf(c_0_31, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (~m1_subset_1(X1,u1_struct_0(esk3_0))|~v2_struct_0(k3_waybel_2(esk3_0,X1,esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_13]), c_0_14])]), c_0_15]), c_0_16])).
% 0.13/0.38  cnf(c_0_33, plain, (v4_orders_2(X1)|v2_struct_0(X1)|~v4_orders_2(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, (g1_orders_2(u1_struct_0(k3_waybel_2(esk3_0,esk4_0,esk5_0)),u1_orders_2(k3_waybel_2(esk3_0,esk4_0,esk5_0)))=g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0))), inference(spm,[status(thm)],[c_0_29, c_0_21])).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (l1_orders_2(k3_waybel_2(esk3_0,esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_14])])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (~v2_struct_0(k3_waybel_2(esk3_0,esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_32, c_0_21])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (l1_orders_2(esk5_0)|~l1_struct_0(esk3_0)), inference(spm,[status(thm)],[c_0_24, c_0_13])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (v2_struct_0(k3_waybel_2(esk3_0,esk4_0,esk5_0))|~v4_orders_2(k3_waybel_2(esk3_0,esk4_0,esk5_0))|~v7_waybel_0(k3_waybel_2(esk3_0,esk4_0,esk5_0))|~l1_waybel_0(k3_waybel_2(esk3_0,esk4_0,esk5_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, (v4_orders_2(k3_waybel_2(esk3_0,esk4_0,esk5_0))|~v4_orders_2(g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])]), c_0_36])).
% 0.13/0.38  cnf(c_0_40, plain, (v4_orders_2(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)))|v2_struct_0(X1)|~v4_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (v4_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (l1_orders_2(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_31]), c_0_14])])).
% 0.13/0.38  cnf(c_0_43, negated_conjecture, (~v7_waybel_0(k3_waybel_2(esk3_0,esk4_0,esk5_0))|~v4_orders_2(k3_waybel_2(esk3_0,esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_25])]), c_0_36])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (v4_orders_2(k3_waybel_2(esk3_0,esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_42])]), c_0_15])).
% 0.13/0.38  fof(c_0_45, plain, ![X25, X26, X27]:((v6_waybel_0(k3_waybel_2(X25,X26,X27),X25)|(v2_struct_0(X25)|~l1_orders_2(X25)|~m1_subset_1(X26,u1_struct_0(X25))|v2_struct_0(X27)|~v7_waybel_0(X27)|~l1_waybel_0(X27,X25)))&(v7_waybel_0(k3_waybel_2(X25,X26,X27))|(v2_struct_0(X25)|~l1_orders_2(X25)|~m1_subset_1(X26,u1_struct_0(X25))|v2_struct_0(X27)|~v7_waybel_0(X27)|~l1_waybel_0(X27,X25)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_waybel_2])])])])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (~v7_waybel_0(k3_waybel_2(esk3_0,esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44])])).
% 0.13/0.38  cnf(c_0_47, plain, (v7_waybel_0(k3_waybel_2(X1,X2,X3))|v2_struct_0(X1)|v2_struct_0(X3)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v7_waybel_0(X3)|~l1_waybel_0(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.13/0.38  cnf(c_0_48, negated_conjecture, (v7_waybel_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_49, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_21]), c_0_13]), c_0_14])]), c_0_15]), c_0_16]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 50
% 0.13/0.38  # Proof object clause steps            : 33
% 0.13/0.38  # Proof object formula steps           : 17
% 0.13/0.38  # Proof object conjectures             : 26
% 0.13/0.38  # Proof object clause conjectures      : 23
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 17
% 0.13/0.38  # Proof object initial formulas used   : 8
% 0.13/0.38  # Proof object generating inferences   : 13
% 0.13/0.38  # Proof object simplifying inferences  : 38
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 8
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 24
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 24
% 0.13/0.38  # Processed clauses                    : 91
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 1
% 0.13/0.38  # ...remaining for further processing  : 90
% 0.13/0.38  # Other redundant clauses eliminated   : 5
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 1
% 0.13/0.38  # Backward-rewritten                   : 8
% 0.13/0.38  # Generated clauses                    : 61
% 0.13/0.38  # ...of the previous two non-trivial   : 61
% 0.13/0.38  # Contextual simplify-reflections      : 8
% 0.13/0.38  # Paramodulations                      : 56
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 5
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 54
% 0.13/0.38  #    Positive orientable unit clauses  : 20
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 8
% 0.13/0.38  #    Non-unit-clauses                  : 26
% 0.13/0.38  # Current number of unprocessed clauses: 16
% 0.13/0.38  # ...number of literals in the above   : 62
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 31
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 550
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 122
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 10
% 0.13/0.38  # Unit Clause-clause subsumption calls : 32
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 27
% 0.13/0.38  # BW rewrite match successes           : 7
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 4876
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.030 s
% 0.13/0.38  # System time              : 0.007 s
% 0.13/0.38  # Total time               : 0.038 s
% 0.13/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
