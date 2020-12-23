%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1535+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:21 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   69 (5907 expanded)
%              Number of clauses        :   56 (2555 expanded)
%              Number of leaves         :    6 (1327 expanded)
%              Depth                    :   19
%              Number of atoms          :  228 (27177 expanded)
%              Number of equality atoms :   36 (5885 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t13_yellow_0,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
           => ( ( v1_yellow_0(X1)
               => v1_yellow_0(X2) )
              & ( v2_yellow_0(X1)
               => v2_yellow_0(X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_0)).

fof(free_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ! [X3,X4] :
          ( g1_orders_2(X1,X2) = g1_orders_2(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(t2_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
           => ! [X3,X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ! [X5] :
                    ( m1_subset_1(X5,u1_struct_0(X2))
                   => ( X4 = X5
                     => ( ( r2_lattice3(X1,X3,X4)
                         => r2_lattice3(X2,X3,X5) )
                        & ( r1_lattice3(X1,X3,X4)
                         => r1_lattice3(X2,X3,X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow_0)).

fof(d5_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v2_yellow_0(X1)
      <=> ? [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
            & r2_lattice3(X1,u1_struct_0(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_yellow_0)).

fof(d4_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_yellow_0(X1)
      <=> ? [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
            & r1_lattice3(X1,u1_struct_0(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_yellow_0)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2] :
            ( l1_orders_2(X2)
           => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
             => ( ( v1_yellow_0(X1)
                 => v1_yellow_0(X2) )
                & ( v2_yellow_0(X1)
                 => v2_yellow_0(X2) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t13_yellow_0])).

fof(c_0_7,plain,(
    ! [X13,X14,X15,X16] :
      ( ( X13 = X15
        | g1_orders_2(X13,X14) != g1_orders_2(X15,X16)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X13,X13))) )
      & ( X14 = X16
        | g1_orders_2(X13,X14) != g1_orders_2(X15,X16)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X13,X13))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

fof(c_0_8,negated_conjecture,
    ( l1_orders_2(esk3_0)
    & l1_orders_2(esk4_0)
    & g1_orders_2(u1_struct_0(esk3_0),u1_orders_2(esk3_0)) = g1_orders_2(u1_struct_0(esk4_0),u1_orders_2(esk4_0))
    & ( v2_yellow_0(esk3_0)
      | v1_yellow_0(esk3_0) )
    & ( ~ v2_yellow_0(esk4_0)
      | v1_yellow_0(esk3_0) )
    & ( v2_yellow_0(esk3_0)
      | ~ v1_yellow_0(esk4_0) )
    & ( ~ v2_yellow_0(esk4_0)
      | ~ v1_yellow_0(esk4_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).

fof(c_0_9,plain,(
    ! [X12] :
      ( ~ l1_orders_2(X12)
      | m1_subset_1(u1_orders_2(X12),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(X12)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

cnf(c_0_10,plain,
    ( X1 = X2
    | g1_orders_2(X3,X1) != g1_orders_2(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk3_0),u1_orders_2(esk3_0)) = g1_orders_2(u1_struct_0(esk4_0),u1_orders_2(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( X1 = u1_orders_2(esk3_0)
    | g1_orders_2(X2,X1) != g1_orders_2(u1_struct_0(esk4_0),u1_orders_2(esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(u1_orders_2(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,negated_conjecture,
    ( u1_orders_2(esk3_0) = u1_orders_2(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_14]),c_0_15])])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(u1_orders_2(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_12,c_0_16])).

fof(c_0_19,plain,(
    ! [X17,X18,X19,X20,X21] :
      ( ( ~ r2_lattice3(X17,X19,X20)
        | r2_lattice3(X18,X19,X21)
        | X20 != X21
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | g1_orders_2(u1_struct_0(X17),u1_orders_2(X17)) != g1_orders_2(u1_struct_0(X18),u1_orders_2(X18))
        | ~ l1_orders_2(X18)
        | ~ l1_orders_2(X17) )
      & ( ~ r1_lattice3(X17,X19,X20)
        | r1_lattice3(X18,X19,X21)
        | X20 != X21
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | g1_orders_2(u1_struct_0(X17),u1_orders_2(X17)) != g1_orders_2(u1_struct_0(X18),u1_orders_2(X18))
        | ~ l1_orders_2(X18)
        | ~ l1_orders_2(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_yellow_0])])])])).

cnf(c_0_20,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_21,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk3_0),u1_orders_2(esk4_0)) = g1_orders_2(u1_struct_0(esk4_0),u1_orders_2(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_11,c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(u1_orders_2(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0)))) ),
    inference(rw,[status(thm)],[c_0_18,c_0_17])).

fof(c_0_23,plain,(
    ! [X9,X11] :
      ( ( m1_subset_1(esk2_1(X9),u1_struct_0(X9))
        | ~ v2_yellow_0(X9)
        | ~ l1_orders_2(X9) )
      & ( r2_lattice3(X9,u1_struct_0(X9),esk2_1(X9))
        | ~ v2_yellow_0(X9)
        | ~ l1_orders_2(X9) )
      & ( ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ r2_lattice3(X9,u1_struct_0(X9),X11)
        | v2_yellow_0(X9)
        | ~ l1_orders_2(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_yellow_0])])])])])).

cnf(c_0_24,plain,
    ( r2_lattice3(X4,X2,X5)
    | ~ r2_lattice3(X1,X2,X3)
    | X3 != X5
    | ~ m1_subset_1(X5,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))
    | ~ l1_orders_2(X4)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( u1_struct_0(esk3_0) = X1
    | g1_orders_2(u1_struct_0(esk4_0),u1_orders_2(esk4_0)) != g1_orders_2(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_26,plain,
    ( r2_lattice3(X1,u1_struct_0(X1),esk2_1(X1))
    | ~ v2_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,plain,
    ( m1_subset_1(esk2_1(X1),u1_struct_0(X1))
    | ~ v2_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( r2_lattice3(X1,X2,X3)
    | g1_orders_2(u1_struct_0(X4),u1_orders_2(X4)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ r2_lattice3(X4,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X4) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( u1_struct_0(esk3_0) = u1_struct_0(esk4_0) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( r2_lattice3(esk3_0,u1_struct_0(esk3_0),esk2_1(esk3_0))
    | ~ v2_yellow_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_16])).

cnf(c_0_31,negated_conjecture,
    ( v2_yellow_0(esk3_0)
    | v1_yellow_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk2_1(esk3_0),u1_struct_0(esk3_0))
    | ~ v2_yellow_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_16])).

fof(c_0_33,plain,(
    ! [X6,X8] :
      ( ( m1_subset_1(esk1_1(X6),u1_struct_0(X6))
        | ~ v1_yellow_0(X6)
        | ~ l1_orders_2(X6) )
      & ( r1_lattice3(X6,u1_struct_0(X6),esk1_1(X6))
        | ~ v1_yellow_0(X6)
        | ~ l1_orders_2(X6) )
      & ( ~ m1_subset_1(X8,u1_struct_0(X6))
        | ~ r1_lattice3(X6,u1_struct_0(X6),X8)
        | v1_yellow_0(X6)
        | ~ l1_orders_2(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_yellow_0])])])])])).

cnf(c_0_34,negated_conjecture,
    ( r2_lattice3(X1,X2,X3)
    | g1_orders_2(u1_struct_0(esk4_0),u1_orders_2(esk4_0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ r2_lattice3(esk3_0,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_17]),c_0_16])]),c_0_29]),c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( r2_lattice3(esk3_0,u1_struct_0(esk3_0),esk2_1(esk3_0))
    | v1_yellow_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk2_1(esk3_0),u1_struct_0(esk3_0))
    | v1_yellow_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_31])).

cnf(c_0_37,plain,
    ( r1_lattice3(X4,X2,X5)
    | ~ r1_lattice3(X1,X2,X3)
    | X3 != X5
    | ~ m1_subset_1(X5,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))
    | ~ l1_orders_2(X4)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_38,plain,
    ( r1_lattice3(X1,u1_struct_0(X1),esk1_1(X1))
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,X2)
    | ~ r2_lattice3(esk3_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_34]),c_0_13])])).

cnf(c_0_40,negated_conjecture,
    ( r2_lattice3(esk3_0,u1_struct_0(esk4_0),esk2_1(esk3_0))
    | v1_yellow_0(esk3_0) ),
    inference(rw,[status(thm)],[c_0_35,c_0_29])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk2_1(esk3_0),u1_struct_0(esk4_0))
    | v1_yellow_0(esk3_0) ),
    inference(rw,[status(thm)],[c_0_36,c_0_29])).

cnf(c_0_42,plain,
    ( m1_subset_1(esk1_1(X1),u1_struct_0(X1))
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,plain,
    ( r1_lattice3(X1,X2,X3)
    | g1_orders_2(u1_struct_0(X4),u1_orders_2(X4)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ r1_lattice3(X4,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X4) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( r1_lattice3(esk3_0,u1_struct_0(esk3_0),esk1_1(esk3_0))
    | ~ v1_yellow_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_16])).

cnf(c_0_45,plain,
    ( v2_yellow_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,u1_struct_0(X2),X1)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_46,negated_conjecture,
    ( r2_lattice3(esk4_0,u1_struct_0(esk4_0),esk2_1(esk3_0))
    | v1_yellow_0(esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( v1_yellow_0(esk3_0)
    | ~ v2_yellow_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk1_1(esk3_0),u1_struct_0(esk3_0))
    | ~ v1_yellow_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_16])).

cnf(c_0_49,negated_conjecture,
    ( r1_lattice3(X1,X2,X3)
    | g1_orders_2(u1_struct_0(esk4_0),u1_orders_2(esk4_0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ r1_lattice3(esk3_0,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_17]),c_0_16])]),c_0_29]),c_0_29])).

cnf(c_0_50,negated_conjecture,
    ( r1_lattice3(esk3_0,u1_struct_0(esk4_0),esk1_1(esk3_0))
    | ~ v1_yellow_0(esk3_0) ),
    inference(rw,[status(thm)],[c_0_44,c_0_29])).

cnf(c_0_51,negated_conjecture,
    ( v1_yellow_0(esk3_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_13])]),c_0_41]),c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk1_1(esk3_0),u1_struct_0(esk4_0))
    | ~ v1_yellow_0(esk3_0) ),
    inference(rw,[status(thm)],[c_0_48,c_0_29])).

cnf(c_0_53,negated_conjecture,
    ( r1_lattice3(esk4_0,X1,X2)
    | ~ r1_lattice3(esk3_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_49]),c_0_13])])).

cnf(c_0_54,negated_conjecture,
    ( r1_lattice3(esk3_0,u1_struct_0(esk4_0),esk1_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_51])])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk1_1(esk3_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_51])])).

cnf(c_0_56,plain,
    ( v1_yellow_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,u1_struct_0(X2),X1)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_57,negated_conjecture,
    ( r1_lattice3(esk4_0,u1_struct_0(esk4_0),esk1_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])])).

cnf(c_0_58,negated_conjecture,
    ( v2_yellow_0(esk3_0)
    | ~ v1_yellow_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_59,negated_conjecture,
    ( v1_yellow_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_55]),c_0_13])])).

cnf(c_0_60,negated_conjecture,
    ( r2_lattice3(esk3_0,u1_struct_0(esk4_0),esk2_1(esk3_0))
    | ~ v2_yellow_0(esk3_0) ),
    inference(rw,[status(thm)],[c_0_30,c_0_29])).

cnf(c_0_61,negated_conjecture,
    ( v2_yellow_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59])])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(esk2_1(esk3_0),u1_struct_0(esk4_0))
    | ~ v2_yellow_0(esk3_0) ),
    inference(rw,[status(thm)],[c_0_32,c_0_29])).

cnf(c_0_63,negated_conjecture,
    ( r2_lattice3(esk3_0,u1_struct_0(esk4_0),esk2_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61])])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk2_1(esk3_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_61])])).

cnf(c_0_65,negated_conjecture,
    ( ~ v2_yellow_0(esk4_0)
    | ~ v1_yellow_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_66,negated_conjecture,
    ( r2_lattice3(esk4_0,u1_struct_0(esk4_0),esk2_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_63]),c_0_64])])).

cnf(c_0_67,negated_conjecture,
    ( ~ v2_yellow_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_59])])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_66]),c_0_64]),c_0_13])]),c_0_67]),
    [proof]).

%------------------------------------------------------------------------------
