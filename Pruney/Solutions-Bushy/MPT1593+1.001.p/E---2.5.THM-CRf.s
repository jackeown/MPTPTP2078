%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1593+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   34 (  83 expanded)
%              Number of clauses        :   21 (  40 expanded)
%              Number of leaves         :    6 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :   68 ( 144 expanded)
%              Number of equality atoms :   38 (  70 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k2_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & l1_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(d1_yellow_1,axiom,(
    ! [X1] : k2_yellow_1(X1) = g1_orders_2(X1,k1_yellow_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_yellow_1)).

fof(abstractness_v1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_orders_2(X1)
       => X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(free_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ! [X3,X4] :
          ( g1_orders_2(X1,X2) = g1_orders_2(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(t1_yellow_1,conjecture,(
    ! [X1] :
      ( u1_struct_0(k2_yellow_1(X1)) = X1
      & u1_orders_2(k2_yellow_1(X1)) = k1_yellow_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(c_0_6,plain,(
    ! [X7] :
      ( v1_orders_2(k2_yellow_1(X7))
      & l1_orders_2(k2_yellow_1(X7)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

fof(c_0_7,plain,(
    ! [X6] : k2_yellow_1(X6) = g1_orders_2(X6,k1_yellow_1(X6)) ),
    inference(variable_rename,[status(thm)],[d1_yellow_1])).

fof(c_0_8,plain,(
    ! [X5] :
      ( ~ l1_orders_2(X5)
      | ~ v1_orders_2(X5)
      | X5 = g1_orders_2(u1_struct_0(X5),u1_orders_2(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_orders_2])])).

cnf(c_0_9,plain,
    ( v1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k2_yellow_1(X1) = g1_orders_2(X1,k1_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( l1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_12,plain,(
    ! [X9,X10,X11,X12] :
      ( ( X9 = X11
        | g1_orders_2(X9,X10) != g1_orders_2(X11,X12)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X9,X9))) )
      & ( X10 = X12
        | g1_orders_2(X9,X10) != g1_orders_2(X11,X12)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X9,X9))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

cnf(c_0_13,plain,
    ( X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ v1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( v1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) ),
    inference(rw,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_15,plain,
    ( l1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) ),
    inference(rw,[status(thm)],[c_0_11,c_0_10])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( u1_struct_0(k2_yellow_1(X1)) = X1
        & u1_orders_2(k2_yellow_1(X1)) = k1_yellow_1(X1) ) ),
    inference(assume_negation,[status(cth)],[t1_yellow_1])).

cnf(c_0_17,plain,
    ( X1 = X2
    | g1_orders_2(X3,X1) != g1_orders_2(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( g1_orders_2(u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))),u1_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))) = g1_orders_2(X1,k1_yellow_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])])).

fof(c_0_19,plain,(
    ! [X8] :
      ( ~ l1_orders_2(X8)
      | m1_subset_1(u1_orders_2(X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X8)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_20,negated_conjecture,
    ( u1_struct_0(k2_yellow_1(esk1_0)) != esk1_0
    | u1_orders_2(k2_yellow_1(esk1_0)) != k1_yellow_1(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

cnf(c_0_21,plain,
    ( u1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) = X2
    | g1_orders_2(X1,k1_yellow_1(X1)) != g1_orders_2(X3,X2)
    | ~ m1_subset_1(u1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))),u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1)))))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,negated_conjecture,
    ( u1_struct_0(k2_yellow_1(esk1_0)) != esk1_0
    | u1_orders_2(k2_yellow_1(esk1_0)) != k1_yellow_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( u1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) = k1_yellow_1(X1)
    | ~ m1_subset_1(u1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))),u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1)))))) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( m1_subset_1(u1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))),u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1)))))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_15])).

cnf(c_0_27,plain,
    ( u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))) = X2
    | g1_orders_2(X1,k1_yellow_1(X1)) != g1_orders_2(X2,X3)
    | ~ m1_subset_1(u1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))),u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1)))))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0))) != esk1_0
    | u1_orders_2(g1_orders_2(esk1_0,k1_yellow_1(esk1_0))) != k1_yellow_1(esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_10]),c_0_10])).

cnf(c_0_29,plain,
    ( u1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) = k1_yellow_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26])])).

cnf(c_0_30,plain,
    ( u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))) = X2
    | g1_orders_2(X1,k1_yellow_1(X1)) != g1_orders_2(X2,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_26])])).

cnf(c_0_31,negated_conjecture,
    ( u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0))) != esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29])])).

cnf(c_0_32,plain,
    ( u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))) = X1 ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32])]),
    [proof]).

%------------------------------------------------------------------------------
