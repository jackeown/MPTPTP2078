%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1645+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:31 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   56 (1159 expanded)
%              Number of clauses        :   43 ( 470 expanded)
%              Number of leaves         :    6 ( 268 expanded)
%              Depth                    :   16
%              Number of atoms          :  197 (6993 expanded)
%              Number of equality atoms :   54 (1750 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t25_waybel_0,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X3 = X4
                     => ( ( v12_waybel_0(X3,X1)
                         => v12_waybel_0(X4,X2) )
                        & ( v13_waybel_0(X3,X1)
                         => v13_waybel_0(X4,X2) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_waybel_0)).

fof(t13_waybel_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X3 = X4
                     => ( k3_waybel_0(X1,X3) = k3_waybel_0(X2,X4)
                        & k4_waybel_0(X1,X3) = k4_waybel_0(X2,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_waybel_0)).

fof(t24_waybel_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v13_waybel_0(X2,X1)
          <=> r1_tarski(k4_waybel_0(X1,X2),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_waybel_0)).

fof(t23_waybel_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v12_waybel_0(X2,X1)
          <=> r1_tarski(k3_waybel_0(X1,X2),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_waybel_0)).

fof(c_0_6,plain,(
    ! [X6,X7,X8,X9] :
      ( ( X6 = X8
        | g1_orders_2(X6,X7) != g1_orders_2(X8,X9)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X6))) )
      & ( X7 = X9
        | g1_orders_2(X6,X7) != g1_orders_2(X8,X9)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X6))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

fof(c_0_7,plain,(
    ! [X5] :
      ( ~ l1_orders_2(X5)
      | m1_subset_1(u1_orders_2(X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X5)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2] :
            ( l1_orders_2(X2)
           => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( X3 = X4
                       => ( ( v12_waybel_0(X3,X1)
                           => v12_waybel_0(X4,X2) )
                          & ( v13_waybel_0(X3,X1)
                           => v13_waybel_0(X4,X2) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t25_waybel_0])).

cnf(c_0_9,plain,
    ( X1 = X2
    | g1_orders_2(X3,X1) != g1_orders_2(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,negated_conjecture,
    ( l1_orders_2(esk1_0)
    & l1_orders_2(esk2_0)
    & g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) = g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & esk3_0 = esk4_0
    & ( v13_waybel_0(esk3_0,esk1_0)
      | v12_waybel_0(esk3_0,esk1_0) )
    & ( ~ v13_waybel_0(esk4_0,esk2_0)
      | v12_waybel_0(esk3_0,esk1_0) )
    & ( v13_waybel_0(esk3_0,esk1_0)
      | ~ v12_waybel_0(esk4_0,esk2_0) )
    & ( ~ v13_waybel_0(esk4_0,esk2_0)
      | ~ v12_waybel_0(esk4_0,esk2_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).

cnf(c_0_12,plain,
    ( u1_orders_2(X1) = X2
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(X3,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) = g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( u1_orders_2(esk2_0) = X1
    | g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) != g1_orders_2(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])])).

fof(c_0_16,plain,(
    ! [X10,X11,X12,X13] :
      ( ( k3_waybel_0(X10,X12) = k3_waybel_0(X11,X13)
        | X12 != X13
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10)))
        | g1_orders_2(u1_struct_0(X10),u1_orders_2(X10)) != g1_orders_2(u1_struct_0(X11),u1_orders_2(X11))
        | ~ l1_orders_2(X11)
        | ~ l1_orders_2(X10) )
      & ( k4_waybel_0(X10,X12) = k4_waybel_0(X11,X13)
        | X12 != X13
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10)))
        | g1_orders_2(u1_struct_0(X10),u1_orders_2(X10)) != g1_orders_2(u1_struct_0(X11),u1_orders_2(X11))
        | ~ l1_orders_2(X11)
        | ~ l1_orders_2(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_waybel_0])])])])).

cnf(c_0_17,negated_conjecture,
    ( u1_orders_2(esk2_0) = u1_orders_2(esk1_0) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_18,plain,
    ( k4_waybel_0(X1,X2) = k4_waybel_0(X3,X4)
    | X2 != X4
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
    | ~ l1_orders_2(X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(u1_orders_2(esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_17]),c_0_14])])).

cnf(c_0_21,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk1_0)) = g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_13,c_0_17])).

cnf(c_0_22,plain,
    ( k4_waybel_0(X1,X2) = k4_waybel_0(X3,X2)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X3)
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_25,negated_conjecture,
    ( u1_struct_0(esk2_0) = X1
    | g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) != g1_orders_2(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

cnf(c_0_26,plain,
    ( k3_waybel_0(X1,X2) = k3_waybel_0(X3,X4)
    | X2 != X4
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
    | ~ l1_orders_2(X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_27,plain,(
    ! [X16,X17] :
      ( ( ~ v13_waybel_0(X17,X16)
        | r1_tarski(k4_waybel_0(X16,X17),X17)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ l1_orders_2(X16) )
      & ( ~ r1_tarski(k4_waybel_0(X16,X17),X17)
        | v13_waybel_0(X17,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ l1_orders_2(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_waybel_0])])])])).

cnf(c_0_28,negated_conjecture,
    ( k4_waybel_0(X1,esk3_0) = k4_waybel_0(esk1_0,esk3_0)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_29,negated_conjecture,
    ( u1_struct_0(esk2_0) = u1_struct_0(esk1_0) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( k3_waybel_0(X1,X2) = k3_waybel_0(X3,X2)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X3)
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( v13_waybel_0(X2,X1)
    | ~ r1_tarski(k4_waybel_0(X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( k4_waybel_0(esk2_0,esk3_0) = k4_waybel_0(esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_17]),c_0_29]),c_0_29]),c_0_23]),c_0_14])])).

fof(c_0_33,plain,(
    ! [X14,X15] :
      ( ( ~ v12_waybel_0(X15,X14)
        | r1_tarski(k3_waybel_0(X14,X15),X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_orders_2(X14) )
      & ( ~ r1_tarski(k3_waybel_0(X14,X15),X15)
        | v12_waybel_0(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_orders_2(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_waybel_0])])])])).

cnf(c_0_34,negated_conjecture,
    ( k3_waybel_0(X1,esk3_0) = k3_waybel_0(esk1_0,esk3_0)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_23]),c_0_24])])).

cnf(c_0_35,negated_conjecture,
    ( ~ v13_waybel_0(esk4_0,esk2_0)
    | ~ v12_waybel_0(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_36,negated_conjecture,
    ( esk3_0 = esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_37,negated_conjecture,
    ( v13_waybel_0(esk3_0,esk2_0)
    | ~ r1_tarski(k4_waybel_0(esk1_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_29]),c_0_23]),c_0_14])])).

cnf(c_0_38,plain,
    ( r1_tarski(k4_waybel_0(X2,X1),X1)
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,negated_conjecture,
    ( v13_waybel_0(esk3_0,esk1_0)
    | ~ v12_waybel_0(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_40,plain,
    ( v12_waybel_0(X2,X1)
    | ~ r1_tarski(k3_waybel_0(X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( k3_waybel_0(esk2_0,esk3_0) = k3_waybel_0(esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_17]),c_0_29]),c_0_29]),c_0_23]),c_0_14])])).

cnf(c_0_42,negated_conjecture,
    ( ~ v13_waybel_0(esk3_0,esk2_0)
    | ~ v12_waybel_0(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( v13_waybel_0(esk3_0,esk2_0)
    | ~ v13_waybel_0(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_23]),c_0_24])])).

cnf(c_0_44,negated_conjecture,
    ( v13_waybel_0(esk3_0,esk1_0)
    | ~ v12_waybel_0(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_39,c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( v12_waybel_0(esk3_0,esk2_0)
    | ~ r1_tarski(k3_waybel_0(esk1_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_29]),c_0_23]),c_0_14])])).

cnf(c_0_46,plain,
    ( r1_tarski(k3_waybel_0(X2,X1),X1)
    | ~ v12_waybel_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_47,negated_conjecture,
    ( ~ v12_waybel_0(esk3_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( v12_waybel_0(esk3_0,esk2_0)
    | ~ v12_waybel_0(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_23]),c_0_24])])).

cnf(c_0_49,negated_conjecture,
    ( v13_waybel_0(esk3_0,esk1_0)
    | v12_waybel_0(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_50,negated_conjecture,
    ( ~ v12_waybel_0(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( v12_waybel_0(esk3_0,esk1_0)
    | ~ v13_waybel_0(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_52,negated_conjecture,
    ( v13_waybel_0(esk3_0,esk1_0) ),
    inference(sr,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( v12_waybel_0(esk3_0,esk1_0)
    | ~ v13_waybel_0(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_51,c_0_36])).

cnf(c_0_54,negated_conjecture,
    ( v13_waybel_0(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_52])])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_54])]),c_0_50]),
    [proof]).

%------------------------------------------------------------------------------
