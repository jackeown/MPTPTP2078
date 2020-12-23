%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1589+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:27 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   22 (  60 expanded)
%              Number of clauses        :   15 (  17 expanded)
%              Number of leaves         :    3 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :  111 ( 545 expanded)
%              Number of equality atoms :    7 (  43 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t68_yellow_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v3_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_yellow_0(X2,X1)
            & m1_yellow_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => ( r2_hidden(k2_yellow_0(X1,X3),u1_struct_0(X2))
               => k2_yellow_0(X2,X3) = k2_yellow_0(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_yellow_0)).

fof(t17_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v3_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( r1_yellow_0(X1,X2)
          & r2_yellow_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_yellow_0)).

fof(t64_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_yellow_0(X2,X1)
            & m1_yellow_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => ( ( r2_yellow_0(X1,X3)
                  & r2_hidden(k2_yellow_0(X1,X3),u1_struct_0(X2)) )
               => ( r2_yellow_0(X2,X3)
                  & k2_yellow_0(X2,X3) = k2_yellow_0(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_yellow_0)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & v3_lattice3(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v4_yellow_0(X2,X1)
              & m1_yellow_0(X2,X1) )
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
               => ( r2_hidden(k2_yellow_0(X1,X3),u1_struct_0(X2))
                 => k2_yellow_0(X2,X3) = k2_yellow_0(X1,X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t68_yellow_0])).

fof(c_0_4,plain,(
    ! [X4,X5] :
      ( ( r1_yellow_0(X4,X5)
        | v2_struct_0(X4)
        | ~ v5_orders_2(X4)
        | ~ v3_lattice3(X4)
        | ~ l1_orders_2(X4) )
      & ( r2_yellow_0(X4,X5)
        | v2_struct_0(X4)
        | ~ v5_orders_2(X4)
        | ~ v3_lattice3(X4)
        | ~ l1_orders_2(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t17_yellow_0])])])])])).

fof(c_0_5,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v3_orders_2(esk1_0)
    & v4_orders_2(esk1_0)
    & v5_orders_2(esk1_0)
    & v3_lattice3(esk1_0)
    & l1_orders_2(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v4_yellow_0(esk2_0,esk1_0)
    & m1_yellow_0(esk2_0,esk1_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & r2_hidden(k2_yellow_0(esk1_0,esk3_0),u1_struct_0(esk2_0))
    & k2_yellow_0(esk2_0,esk3_0) != k2_yellow_0(esk1_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])).

fof(c_0_6,plain,(
    ! [X6,X7,X8] :
      ( ( r2_yellow_0(X7,X8)
        | ~ r2_yellow_0(X6,X8)
        | ~ r2_hidden(k2_yellow_0(X6,X8),u1_struct_0(X7))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | v2_struct_0(X7)
        | ~ v4_yellow_0(X7,X6)
        | ~ m1_yellow_0(X7,X6)
        | v2_struct_0(X6)
        | ~ v4_orders_2(X6)
        | ~ l1_orders_2(X6) )
      & ( k2_yellow_0(X7,X8) = k2_yellow_0(X6,X8)
        | ~ r2_yellow_0(X6,X8)
        | ~ r2_hidden(k2_yellow_0(X6,X8),u1_struct_0(X7))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | v2_struct_0(X7)
        | ~ v4_yellow_0(X7,X6)
        | ~ m1_yellow_0(X7,X6)
        | v2_struct_0(X6)
        | ~ v4_orders_2(X6)
        | ~ l1_orders_2(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t64_yellow_0])])])])])).

cnf(c_0_7,plain,
    ( r2_yellow_0(X1,X2)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v3_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( v3_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,plain,
    ( k2_yellow_0(X1,X2) = k2_yellow_0(X3,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ r2_yellow_0(X3,X2)
    | ~ r2_hidden(k2_yellow_0(X3,X2),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_yellow_0(X1,X3)
    | ~ m1_yellow_0(X1,X3)
    | ~ v4_orders_2(X3)
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(k2_yellow_0(esk1_0,esk3_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( m1_yellow_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,negated_conjecture,
    ( v4_yellow_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,negated_conjecture,
    ( v4_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_18,negated_conjecture,
    ( r2_yellow_0(esk1_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9]),c_0_10])]),c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( k2_yellow_0(esk2_0,esk3_0) != k2_yellow_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_21,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18]),c_0_8])]),c_0_19]),c_0_11]),c_0_20]),
    [proof]).

%------------------------------------------------------------------------------
