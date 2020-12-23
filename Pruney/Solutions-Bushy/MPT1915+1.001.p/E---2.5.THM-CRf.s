%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1915+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:02 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   27 (  41 expanded)
%              Number of clauses        :   16 (  16 expanded)
%              Number of leaves         :    5 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :  124 ( 200 expanded)
%              Number of equality atoms :   29 (  41 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   25 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d7_yellow_6,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_struct_0(X2) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => ! [X4] :
                  ( ( v6_waybel_0(X4,X2)
                    & l1_waybel_0(X4,X2) )
                 => ( X4 = k3_yellow_6(X1,X2,X3)
                  <=> ( g1_orders_2(u1_struct_0(X4),u1_orders_2(X4)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
                      & r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),u1_waybel_0(X2,X4),k8_funcop_1(u1_struct_0(X2),u1_struct_0(X4),X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_yellow_6)).

fof(dt_k3_yellow_6,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_orders_2(X1)
        & ~ v2_struct_0(X2)
        & l1_struct_0(X2)
        & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( v6_waybel_0(k3_yellow_6(X1,X2,X3),X2)
        & l1_waybel_0(k3_yellow_6(X1,X2,X3),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_6)).

fof(t13_yellow_6,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_struct_0(X2) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => u1_struct_0(k3_yellow_6(X1,X2,X3)) = u1_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_6)).

fof(free_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ! [X3,X4] :
          ( g1_orders_2(X1,X2) = g1_orders_2(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(c_0_5,plain,(
    ! [X5,X6,X7,X8] :
      ( ( g1_orders_2(u1_struct_0(X8),u1_orders_2(X8)) = g1_orders_2(u1_struct_0(X5),u1_orders_2(X5))
        | X8 != k3_yellow_6(X5,X6,X7)
        | ~ v6_waybel_0(X8,X6)
        | ~ l1_waybel_0(X8,X6)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | v2_struct_0(X6)
        | ~ l1_struct_0(X6)
        | ~ l1_orders_2(X5) )
      & ( r2_funct_2(u1_struct_0(X8),u1_struct_0(X6),u1_waybel_0(X6,X8),k8_funcop_1(u1_struct_0(X6),u1_struct_0(X8),X7))
        | X8 != k3_yellow_6(X5,X6,X7)
        | ~ v6_waybel_0(X8,X6)
        | ~ l1_waybel_0(X8,X6)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | v2_struct_0(X6)
        | ~ l1_struct_0(X6)
        | ~ l1_orders_2(X5) )
      & ( g1_orders_2(u1_struct_0(X8),u1_orders_2(X8)) != g1_orders_2(u1_struct_0(X5),u1_orders_2(X5))
        | ~ r2_funct_2(u1_struct_0(X8),u1_struct_0(X6),u1_waybel_0(X6,X8),k8_funcop_1(u1_struct_0(X6),u1_struct_0(X8),X7))
        | X8 = k3_yellow_6(X5,X6,X7)
        | ~ v6_waybel_0(X8,X6)
        | ~ l1_waybel_0(X8,X6)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | v2_struct_0(X6)
        | ~ l1_struct_0(X6)
        | ~ l1_orders_2(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_yellow_6])])])])])).

fof(c_0_6,plain,(
    ! [X9,X10,X11] :
      ( ( v6_waybel_0(k3_yellow_6(X9,X10,X11),X10)
        | ~ l1_orders_2(X9)
        | v2_struct_0(X10)
        | ~ l1_struct_0(X10)
        | ~ m1_subset_1(X11,u1_struct_0(X10)) )
      & ( l1_waybel_0(k3_yellow_6(X9,X10,X11),X10)
        | ~ l1_orders_2(X9)
        | v2_struct_0(X10)
        | ~ l1_struct_0(X10)
        | ~ m1_subset_1(X11,u1_struct_0(X10)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_yellow_6])])])])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & l1_struct_0(X2) )
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X2))
               => u1_struct_0(k3_yellow_6(X1,X2,X3)) = u1_struct_0(X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t13_yellow_6])).

fof(c_0_8,plain,(
    ! [X13,X14,X15,X16] :
      ( ( X13 = X15
        | g1_orders_2(X13,X14) != g1_orders_2(X15,X16)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X13,X13))) )
      & ( X14 = X16
        | g1_orders_2(X13,X14) != g1_orders_2(X15,X16)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X13,X13))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

fof(c_0_9,plain,(
    ! [X12] :
      ( ~ l1_orders_2(X12)
      | m1_subset_1(u1_orders_2(X12),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(X12)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

cnf(c_0_10,plain,
    ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
    | v2_struct_0(X3)
    | X1 != k3_yellow_6(X2,X3,X4)
    | ~ v6_waybel_0(X1,X3)
    | ~ l1_waybel_0(X1,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ l1_struct_0(X3)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,plain,
    ( v6_waybel_0(k3_yellow_6(X1,X2,X3),X2)
    | v2_struct_0(X2)
    | ~ l1_orders_2(X1)
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( l1_waybel_0(k3_yellow_6(X1,X2,X3),X2)
    | v2_struct_0(X2)
    | ~ l1_orders_2(X1)
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_13,negated_conjecture,
    ( l1_orders_2(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & l1_struct_0(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & u1_struct_0(k3_yellow_6(esk1_0,esk2_0,esk3_0)) != u1_struct_0(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).

cnf(c_0_14,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( g1_orders_2(u1_struct_0(k3_yellow_6(X1,X2,X3)),u1_orders_2(k3_yellow_6(X1,X2,X3))) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_struct_0(X2)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_10]),c_0_11]),c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( u1_struct_0(X1) = X2
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( g1_orders_2(u1_struct_0(k3_yellow_6(X1,esk2_0,esk3_0)),u1_orders_2(k3_yellow_6(X1,esk2_0,esk3_0))) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( u1_struct_0(X1) = u1_struct_0(k3_yellow_6(X2,esk2_0,esk3_0))
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_23,negated_conjecture,
    ( u1_struct_0(k3_yellow_6(esk1_0,esk2_0,esk3_0)) != u1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( u1_struct_0(k3_yellow_6(X1,esk2_0,esk3_0)) = u1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])]),
    [proof]).

%------------------------------------------------------------------------------
