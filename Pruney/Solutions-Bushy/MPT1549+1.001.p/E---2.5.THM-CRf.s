%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1549+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:23 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   66 (1461 expanded)
%              Number of clauses        :   49 ( 599 expanded)
%              Number of leaves         :    8 ( 341 expanded)
%              Depth                    :   16
%              Number of atoms          :  319 (5449 expanded)
%              Number of equality atoms :   75 (2141 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   30 (   3 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(t27_yellow_0,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
           => ! [X3] :
                ( r2_yellow_0(X1,X3)
               => k2_yellow_0(X1,X3) = k2_yellow_0(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow_0)).

fof(dt_k2_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_0)).

fof(d10_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r2_yellow_0(X1,X2)
           => ( X3 = k2_yellow_0(X1,X2)
            <=> ( r1_lattice3(X1,X2,X3)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r1_lattice3(X1,X2,X4)
                     => r1_orders_2(X1,X4,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_yellow_0)).

fof(t1_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X2))
                       => ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X2))
                           => ( ( X3 = X5
                                & X4 = X6 )
                             => ( ( r1_orders_2(X1,X3,X4)
                                 => r1_orders_2(X2,X5,X6) )
                                & ( r2_orders_2(X1,X3,X4)
                                 => r2_orders_2(X2,X5,X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_0)).

fof(t14_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
           => ! [X3] :
                ( ( r1_yellow_0(X1,X3)
                 => r1_yellow_0(X2,X3) )
                & ( r2_yellow_0(X1,X3)
                 => r2_yellow_0(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_0)).

fof(c_0_8,plain,(
    ! [X15,X16,X17,X18] :
      ( ( X15 = X17
        | g1_orders_2(X15,X16) != g1_orders_2(X17,X18)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X15,X15))) )
      & ( X16 = X18
        | g1_orders_2(X15,X16) != g1_orders_2(X17,X18)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X15,X15))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

fof(c_0_9,plain,(
    ! [X14] :
      ( ~ l1_orders_2(X14)
      | m1_subset_1(u1_orders_2(X14),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X14)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2] :
            ( l1_orders_2(X2)
           => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
             => ! [X3] :
                  ( r2_yellow_0(X1,X3)
                 => k2_yellow_0(X1,X3) = k2_yellow_0(X2,X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t27_yellow_0])).

cnf(c_0_11,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,negated_conjecture,
    ( l1_orders_2(esk2_0)
    & l1_orders_2(esk3_0)
    & g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) = g1_orders_2(u1_struct_0(esk3_0),u1_orders_2(esk3_0))
    & r2_yellow_0(esk2_0,esk4_0)
    & k2_yellow_0(esk2_0,esk4_0) != k2_yellow_0(esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_14,plain,
    ( u1_struct_0(X1) = X2
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) = g1_orders_2(u1_struct_0(esk3_0),u1_orders_2(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( u1_struct_0(esk3_0) = X1
    | g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) != g1_orders_2(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])])).

fof(c_0_18,plain,(
    ! [X28,X29,X30,X31,X32] :
      ( ( ~ r2_lattice3(X28,X30,X31)
        | r2_lattice3(X29,X30,X32)
        | X31 != X32
        | ~ m1_subset_1(X32,u1_struct_0(X29))
        | ~ m1_subset_1(X31,u1_struct_0(X28))
        | g1_orders_2(u1_struct_0(X28),u1_orders_2(X28)) != g1_orders_2(u1_struct_0(X29),u1_orders_2(X29))
        | ~ l1_orders_2(X29)
        | ~ l1_orders_2(X28) )
      & ( ~ r1_lattice3(X28,X30,X31)
        | r1_lattice3(X29,X30,X32)
        | X31 != X32
        | ~ m1_subset_1(X32,u1_struct_0(X29))
        | ~ m1_subset_1(X31,u1_struct_0(X28))
        | g1_orders_2(u1_struct_0(X28),u1_orders_2(X28)) != g1_orders_2(u1_struct_0(X29),u1_orders_2(X29))
        | ~ l1_orders_2(X29)
        | ~ l1_orders_2(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_yellow_0])])])])).

fof(c_0_19,plain,(
    ! [X12,X13] :
      ( ~ l1_orders_2(X12)
      | m1_subset_1(k2_yellow_0(X12,X13),u1_struct_0(X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_yellow_0])])).

cnf(c_0_20,negated_conjecture,
    ( u1_struct_0(esk3_0) = u1_struct_0(esk2_0) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( r1_lattice3(X4,X2,X5)
    | ~ r1_lattice3(X1,X2,X3)
    | X3 != X5
    | ~ m1_subset_1(X5,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))
    | ~ l1_orders_2(X4)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( X1 = X2
    | g1_orders_2(X3,X1) != g1_orders_2(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(u1_orders_2(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_20]),c_0_16])])).

cnf(c_0_25,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk3_0)) = g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_15,c_0_20])).

cnf(c_0_26,plain,
    ( r1_lattice3(X1,X2,X3)
    | g1_orders_2(u1_struct_0(X4),u1_orders_2(X4)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ r1_lattice3(X4,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X4) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(k2_yellow_0(esk3_0,X1),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_20]),c_0_16])])).

cnf(c_0_28,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,negated_conjecture,
    ( u1_orders_2(esk3_0) = X1
    | g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) != g1_orders_2(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

fof(c_0_30,plain,(
    ! [X7,X8,X9,X10] :
      ( ( r1_lattice3(X7,X8,X9)
        | X9 != k2_yellow_0(X7,X8)
        | ~ r2_yellow_0(X7,X8)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ l1_orders_2(X7) )
      & ( ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r1_lattice3(X7,X8,X10)
        | r1_orders_2(X7,X10,X9)
        | X9 != k2_yellow_0(X7,X8)
        | ~ r2_yellow_0(X7,X8)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ l1_orders_2(X7) )
      & ( m1_subset_1(esk1_3(X7,X8,X9),u1_struct_0(X7))
        | ~ r1_lattice3(X7,X8,X9)
        | X9 = k2_yellow_0(X7,X8)
        | ~ r2_yellow_0(X7,X8)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ l1_orders_2(X7) )
      & ( r1_lattice3(X7,X8,esk1_3(X7,X8,X9))
        | ~ r1_lattice3(X7,X8,X9)
        | X9 = k2_yellow_0(X7,X8)
        | ~ r2_yellow_0(X7,X8)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ l1_orders_2(X7) )
      & ( ~ r1_orders_2(X7,esk1_3(X7,X8,X9),X9)
        | ~ r1_lattice3(X7,X8,X9)
        | X9 = k2_yellow_0(X7,X8)
        | ~ r2_yellow_0(X7,X8)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ l1_orders_2(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_yellow_0])])])])])).

fof(c_0_31,plain,(
    ! [X22,X23,X24,X25,X26,X27] :
      ( ( ~ r1_orders_2(X22,X24,X25)
        | r1_orders_2(X23,X26,X27)
        | X24 != X26
        | X25 != X27
        | ~ m1_subset_1(X27,u1_struct_0(X23))
        | ~ m1_subset_1(X26,u1_struct_0(X23))
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | g1_orders_2(u1_struct_0(X22),u1_orders_2(X22)) != g1_orders_2(u1_struct_0(X23),u1_orders_2(X23))
        | ~ l1_orders_2(X23)
        | ~ l1_orders_2(X22) )
      & ( ~ r2_orders_2(X22,X24,X25)
        | r2_orders_2(X23,X26,X27)
        | X24 != X26
        | X25 != X27
        | ~ m1_subset_1(X27,u1_struct_0(X23))
        | ~ m1_subset_1(X26,u1_struct_0(X23))
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | g1_orders_2(u1_struct_0(X22),u1_orders_2(X22)) != g1_orders_2(u1_struct_0(X23),u1_orders_2(X23))
        | ~ l1_orders_2(X23)
        | ~ l1_orders_2(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_yellow_0])])])])).

cnf(c_0_32,negated_conjecture,
    ( r1_lattice3(esk2_0,X1,k2_yellow_0(esk3_0,X2))
    | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0))
    | ~ r1_lattice3(X3,X1,k2_yellow_0(esk3_0,X2))
    | ~ m1_subset_1(k2_yellow_0(esk3_0,X2),u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

cnf(c_0_33,negated_conjecture,
    ( u1_orders_2(esk3_0) = u1_orders_2(esk2_0) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_34,plain,
    ( r1_lattice3(X1,X2,X3)
    | X3 != k2_yellow_0(X1,X2)
    | ~ r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_35,plain,(
    ! [X19,X20,X21] :
      ( ( ~ r1_yellow_0(X19,X21)
        | r1_yellow_0(X20,X21)
        | g1_orders_2(u1_struct_0(X19),u1_orders_2(X19)) != g1_orders_2(u1_struct_0(X20),u1_orders_2(X20))
        | ~ l1_orders_2(X20)
        | ~ l1_orders_2(X19) )
      & ( ~ r2_yellow_0(X19,X21)
        | r2_yellow_0(X20,X21)
        | g1_orders_2(u1_struct_0(X19),u1_orders_2(X19)) != g1_orders_2(u1_struct_0(X20),u1_orders_2(X20))
        | ~ l1_orders_2(X20)
        | ~ l1_orders_2(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_yellow_0])])])])).

cnf(c_0_36,plain,
    ( r1_orders_2(X4,X5,X6)
    | ~ r1_orders_2(X1,X2,X3)
    | X2 != X5
    | X3 != X6
    | ~ m1_subset_1(X6,u1_struct_0(X4))
    | ~ m1_subset_1(X5,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))
    | ~ l1_orders_2(X4)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | X3 = k2_yellow_0(X1,X2)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( r1_lattice3(esk2_0,X1,k2_yellow_0(esk3_0,X2))
    | ~ r1_lattice3(esk3_0,X1,k2_yellow_0(esk3_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_20]),c_0_33]),c_0_27]),c_0_16])])).

cnf(c_0_39,plain,
    ( r1_lattice3(X1,X2,k2_yellow_0(X1,X2))
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_34]),c_0_22])).

cnf(c_0_40,plain,
    ( r2_yellow_0(X3,X2)
    | ~ r2_yellow_0(X1,X2)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
    | ~ l1_orders_2(X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( r2_yellow_0(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_42,plain,
    ( r1_orders_2(X1,X2,X3)
    | g1_orders_2(u1_struct_0(X4),u1_orders_2(X4)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ r1_orders_2(X4,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X2,u1_struct_0(X4))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X4) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_36])])).

cnf(c_0_43,negated_conjecture,
    ( k2_yellow_0(esk3_0,X1) = k2_yellow_0(esk2_0,X2)
    | m1_subset_1(esk1_3(esk2_0,X2,k2_yellow_0(esk3_0,X1)),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,X2,k2_yellow_0(esk3_0,X1))
    | ~ r2_yellow_0(esk2_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_27]),c_0_28])])).

cnf(c_0_44,negated_conjecture,
    ( r1_lattice3(esk2_0,X1,k2_yellow_0(esk3_0,X1))
    | ~ r2_yellow_0(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_16])])).

cnf(c_0_45,negated_conjecture,
    ( r2_yellow_0(X1,esk4_0)
    | g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_28])])).

cnf(c_0_46,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,k2_yellow_0(esk3_0,X2))
    | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0))
    | ~ r1_orders_2(X3,X1,k2_yellow_0(esk3_0,X2))
    | ~ m1_subset_1(k2_yellow_0(esk3_0,X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_27]),c_0_28])])).

cnf(c_0_47,plain,
    ( r1_orders_2(X2,X1,X4)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | X4 != k2_yellow_0(X2,X3)
    | ~ r2_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_48,negated_conjecture,
    ( k2_yellow_0(esk3_0,X1) = k2_yellow_0(esk2_0,X1)
    | m1_subset_1(esk1_3(esk2_0,X1,k2_yellow_0(esk3_0,X1)),u1_struct_0(esk2_0))
    | ~ r2_yellow_0(esk2_0,X1)
    | ~ r2_yellow_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( r2_yellow_0(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_33]),c_0_20]),c_0_16])])).

cnf(c_0_50,negated_conjecture,
    ( k2_yellow_0(esk2_0,esk4_0) != k2_yellow_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_51,plain,
    ( r1_lattice3(X1,X2,esk1_3(X1,X2,X3))
    | X3 = k2_yellow_0(X1,X2)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_52,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,k2_yellow_0(esk3_0,X2))
    | ~ r1_orders_2(esk3_0,X1,k2_yellow_0(esk3_0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_20]),c_0_33]),c_0_27]),c_0_16])])).

cnf(c_0_53,plain,
    ( r1_orders_2(X1,X2,k2_yellow_0(X1,X3))
    | ~ r1_lattice3(X1,X3,X2)
    | ~ r2_yellow_0(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_47]),c_0_22])).

cnf(c_0_54,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,X2)
    | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0))
    | ~ r1_lattice3(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_20]),c_0_16])]),c_0_33])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,esk4_0,k2_yellow_0(esk3_0,esk4_0)),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_41]),c_0_49])]),c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( k2_yellow_0(esk3_0,X1) = k2_yellow_0(esk2_0,X2)
    | r1_lattice3(esk2_0,X2,esk1_3(esk2_0,X2,k2_yellow_0(esk3_0,X1)))
    | ~ r1_lattice3(esk2_0,X2,k2_yellow_0(esk3_0,X1))
    | ~ r2_yellow_0(esk2_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_27]),c_0_28])])).

cnf(c_0_57,plain,
    ( X3 = k2_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,esk1_3(X1,X2,X3),X3)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_58,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,k2_yellow_0(esk3_0,X2))
    | ~ r1_lattice3(esk3_0,X2,X1)
    | ~ r2_yellow_0(esk3_0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_20]),c_0_16])])).

cnf(c_0_59,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk1_3(esk2_0,esk4_0,k2_yellow_0(esk3_0,esk4_0)))
    | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0))
    | ~ r1_lattice3(X2,X1,esk1_3(esk2_0,esk4_0,k2_yellow_0(esk3_0,esk4_0)))
    | ~ m1_subset_1(esk1_3(esk2_0,esk4_0,k2_yellow_0(esk3_0,esk4_0)),u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( k2_yellow_0(esk3_0,X1) = k2_yellow_0(esk2_0,X1)
    | r1_lattice3(esk2_0,X1,esk1_3(esk2_0,X1,k2_yellow_0(esk3_0,X1)))
    | ~ r2_yellow_0(esk2_0,X1)
    | ~ r2_yellow_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_44])).

cnf(c_0_61,negated_conjecture,
    ( k2_yellow_0(esk3_0,X1) = k2_yellow_0(esk2_0,X2)
    | ~ r1_lattice3(esk3_0,X1,esk1_3(esk2_0,X2,k2_yellow_0(esk3_0,X1)))
    | ~ r1_lattice3(esk2_0,X2,k2_yellow_0(esk3_0,X1))
    | ~ r2_yellow_0(esk2_0,X2)
    | ~ r2_yellow_0(esk3_0,X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_27]),c_0_28])]),c_0_43])).

cnf(c_0_62,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk1_3(esk2_0,esk4_0,k2_yellow_0(esk3_0,esk4_0)))
    | ~ r1_lattice3(esk2_0,X1,esk1_3(esk2_0,esk4_0,k2_yellow_0(esk3_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_55]),c_0_28])])).

cnf(c_0_63,negated_conjecture,
    ( r1_lattice3(esk2_0,esk4_0,esk1_3(esk2_0,esk4_0,k2_yellow_0(esk3_0,esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_41]),c_0_49])]),c_0_50])).

cnf(c_0_64,negated_conjecture,
    ( ~ r1_lattice3(esk2_0,esk4_0,k2_yellow_0(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_41]),c_0_49]),c_0_63])]),c_0_50])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_44]),c_0_49])]),
    [proof]).

%------------------------------------------------------------------------------
