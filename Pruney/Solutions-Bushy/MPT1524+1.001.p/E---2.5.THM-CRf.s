%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1524+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:19 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   74 (2283 expanded)
%              Number of clauses        :   61 ( 933 expanded)
%              Number of leaves         :    6 ( 523 expanded)
%              Depth                    :   19
%              Number of atoms          :  316 (14434 expanded)
%              Number of equality atoms :   45 (3279 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   22 (   3 average)
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

fof(t2_yellow_0,conjecture,(
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

fof(d9_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r2_lattice3(X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r1_orders_2(X1,X4,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

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

fof(d8_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r1_lattice3(X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r1_orders_2(X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).

fof(c_0_6,plain,(
    ! [X18,X19,X20,X21] :
      ( ( X18 = X20
        | g1_orders_2(X18,X19) != g1_orders_2(X20,X21)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X18,X18))) )
      & ( X19 = X21
        | g1_orders_2(X18,X19) != g1_orders_2(X20,X21)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X18,X18))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

fof(c_0_7,plain,(
    ! [X17] :
      ( ~ l1_orders_2(X17)
      | m1_subset_1(u1_orders_2(X17),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X17)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
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
    inference(assume_negation,[status(cth)],[t2_yellow_0])).

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
    ( l1_orders_2(esk3_0)
    & l1_orders_2(esk4_0)
    & g1_orders_2(u1_struct_0(esk3_0),u1_orders_2(esk3_0)) = g1_orders_2(u1_struct_0(esk4_0),u1_orders_2(esk4_0))
    & m1_subset_1(esk6_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk7_0,u1_struct_0(esk4_0))
    & esk6_0 = esk7_0
    & ( r1_lattice3(esk3_0,esk5_0,esk6_0)
      | r2_lattice3(esk3_0,esk5_0,esk6_0) )
    & ( ~ r1_lattice3(esk4_0,esk5_0,esk7_0)
      | r2_lattice3(esk3_0,esk5_0,esk6_0) )
    & ( r1_lattice3(esk3_0,esk5_0,esk6_0)
      | ~ r2_lattice3(esk4_0,esk5_0,esk7_0) )
    & ( ~ r1_lattice3(esk4_0,esk5_0,esk7_0)
      | ~ r2_lattice3(esk4_0,esk5_0,esk7_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).

cnf(c_0_12,plain,
    ( u1_orders_2(X1) = X2
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(X3,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk3_0),u1_orders_2(esk3_0)) = g1_orders_2(u1_struct_0(esk4_0),u1_orders_2(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( u1_orders_2(X1) = u1_orders_2(esk4_0)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(esk3_0),u1_orders_2(esk3_0))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_15,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( u1_orders_2(esk4_0) = u1_orders_2(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_14]),c_0_15])])).

cnf(c_0_17,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(u1_orders_2(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_16]),c_0_17])])).

cnf(c_0_20,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk4_0),u1_orders_2(esk3_0)) = g1_orders_2(u1_struct_0(esk3_0),u1_orders_2(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_13,c_0_16])).

fof(c_0_21,plain,(
    ! [X12,X13,X14,X15] :
      ( ( ~ r2_lattice3(X12,X13,X14)
        | ~ m1_subset_1(X15,u1_struct_0(X12))
        | ~ r2_hidden(X15,X13)
        | r1_orders_2(X12,X15,X14)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ l1_orders_2(X12) )
      & ( m1_subset_1(esk2_3(X12,X13,X14),u1_struct_0(X12))
        | r2_lattice3(X12,X13,X14)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ l1_orders_2(X12) )
      & ( r2_hidden(esk2_3(X12,X13,X14),X13)
        | r2_lattice3(X12,X13,X14)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ l1_orders_2(X12) )
      & ( ~ r1_orders_2(X12,esk2_3(X12,X13,X14),X14)
        | r2_lattice3(X12,X13,X14)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ l1_orders_2(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

cnf(c_0_22,negated_conjecture,
    ( u1_struct_0(esk4_0) = X1
    | g1_orders_2(u1_struct_0(esk3_0),u1_orders_2(esk3_0)) != g1_orders_2(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_23,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_24,negated_conjecture,
    ( u1_struct_0(esk4_0) = u1_struct_0(esk3_0) ),
    inference(er,[status(thm)],[c_0_22])).

fof(c_0_25,plain,(
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

cnf(c_0_26,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,X2)
    | m1_subset_1(esk2_3(esk4_0,X1,X2),u1_struct_0(esk3_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_17])])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_29,plain,(
    ! [X7,X8,X9,X10] :
      ( ( ~ r1_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r2_hidden(X10,X8)
        | r1_orders_2(X7,X9,X10)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ l1_orders_2(X7) )
      & ( m1_subset_1(esk1_3(X7,X8,X9),u1_struct_0(X7))
        | r1_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ l1_orders_2(X7) )
      & ( r2_hidden(esk1_3(X7,X8,X9),X8)
        | r1_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ l1_orders_2(X7) )
      & ( ~ r1_orders_2(X7,X9,esk1_3(X7,X8,X9))
        | r1_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ l1_orders_2(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).

cnf(c_0_30,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk6_0)
    | m1_subset_1(esk2_3(esk4_0,X1,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,X2)
    | r2_hidden(esk2_3(esk4_0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_24]),c_0_17])])).

cnf(c_0_34,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( r1_orders_2(X1,X2,X3)
    | g1_orders_2(u1_struct_0(X4),u1_orders_2(X4)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ r1_orders_2(X4,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X2,u1_struct_0(X4))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X4) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_30])])).

cnf(c_0_36,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk6_0)
    | r1_orders_2(esk3_0,esk2_3(esk4_0,X1,esk6_0),X2)
    | ~ r2_lattice3(esk3_0,X3,X2)
    | ~ r2_hidden(esk2_3(esk4_0,X1,esk6_0),X3)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_15])])).

cnf(c_0_37,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk6_0)
    | r2_hidden(esk2_3(esk4_0,X1,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_27])).

cnf(c_0_38,negated_conjecture,
    ( r1_lattice3(esk4_0,X1,X2)
    | m1_subset_1(esk1_3(esk4_0,X1,X2),u1_struct_0(esk3_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_24]),c_0_17])])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_40,negated_conjecture,
    ( esk6_0 = esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_41,negated_conjecture,
    ( r1_orders_2(esk4_0,X1,X2)
    | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(esk3_0),u1_orders_2(esk3_0))
    | ~ r1_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_24]),c_0_16]),c_0_17])])).

cnf(c_0_42,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk6_0)
    | r1_orders_2(esk3_0,esk2_3(esk4_0,X1,esk6_0),X2)
    | ~ r2_lattice3(esk3_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( r1_lattice3(esk3_0,esk5_0,esk6_0)
    | ~ r2_lattice3(esk4_0,esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_44,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0)
    | ~ r1_lattice3(esk4_0,esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_45,negated_conjecture,
    ( ~ r1_lattice3(esk4_0,esk5_0,esk7_0)
    | ~ r2_lattice3(esk4_0,esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_46,plain,
    ( r1_orders_2(X1,X3,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_47,negated_conjecture,
    ( r1_lattice3(esk4_0,X1,esk6_0)
    | m1_subset_1(esk1_3(esk4_0,X1,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_27])).

cnf(c_0_48,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( r1_orders_2(esk4_0,X1,esk6_0)
    | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(esk3_0),u1_orders_2(esk3_0))
    | ~ r1_orders_2(X2,X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ m1_subset_1(esk6_0,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_27])).

cnf(c_0_51,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk6_0)
    | r1_orders_2(esk3_0,esk2_3(esk4_0,X1,esk6_0),esk6_0)
    | ~ r2_lattice3(esk3_0,X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_27])).

cnf(c_0_52,negated_conjecture,
    ( r1_lattice3(esk3_0,esk5_0,esk6_0)
    | r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_53,negated_conjecture,
    ( r1_lattice3(esk3_0,esk5_0,esk6_0)
    | ~ r2_lattice3(esk4_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_43,c_0_40])).

cnf(c_0_54,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0)
    | ~ r1_lattice3(esk4_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_44,c_0_40])).

cnf(c_0_55,negated_conjecture,
    ( ~ r2_lattice3(esk4_0,esk5_0,esk6_0)
    | ~ r1_lattice3(esk4_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_40]),c_0_40])).

cnf(c_0_56,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk1_3(esk4_0,X2,esk6_0))
    | r1_lattice3(esk4_0,X2,esk6_0)
    | ~ r2_hidden(esk1_3(esk4_0,X2,esk6_0),X3)
    | ~ r1_lattice3(esk3_0,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_15])])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk1_3(esk4_0,X1,esk6_0),X1)
    | r1_lattice3(esk4_0,X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_17])])).

cnf(c_0_58,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk6_0)
    | r1_orders_2(esk4_0,esk2_3(esk4_0,X1,esk6_0),esk6_0)
    | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(esk3_0),u1_orders_2(esk3_0))
    | ~ r1_orders_2(X2,esk2_3(esk4_0,X1,esk6_0),esk6_0)
    | ~ m1_subset_1(esk2_3(esk4_0,X1,esk6_0),u1_struct_0(X2))
    | ~ m1_subset_1(esk6_0,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_32])).

cnf(c_0_59,negated_conjecture,
    ( r1_orders_2(esk3_0,esk2_3(esk4_0,esk5_0,esk6_0),esk6_0)
    | r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( r1_orders_2(esk3_0,esk2_3(esk4_0,esk5_0,esk6_0),esk6_0)
    | ~ r1_lattice3(esk4_0,esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_54]),c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk1_3(esk4_0,X2,esk6_0))
    | r1_lattice3(esk4_0,X2,esk6_0)
    | ~ r1_lattice3(esk3_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk2_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_63,negated_conjecture,
    ( r1_orders_2(esk4_0,esk2_3(esk4_0,esk5_0,esk6_0),esk6_0)
    | r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_27]),c_0_15])]),c_0_32]),c_0_53])).

cnf(c_0_64,negated_conjecture,
    ( r1_orders_2(esk4_0,esk2_3(esk4_0,esk5_0,esk6_0),esk6_0)
    | ~ r1_lattice3(esk4_0,esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_60]),c_0_27]),c_0_15])]),c_0_32]),c_0_55])).

cnf(c_0_65,negated_conjecture,
    ( r1_orders_2(esk4_0,X1,esk1_3(esk4_0,X2,esk6_0))
    | r1_lattice3(esk4_0,X2,esk6_0)
    | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(esk3_0),u1_orders_2(esk3_0))
    | ~ r1_orders_2(X3,X1,esk1_3(esk4_0,X2,esk6_0))
    | ~ m1_subset_1(esk1_3(esk4_0,X2,esk6_0),u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(spm,[status(thm)],[c_0_41,c_0_47])).

cnf(c_0_66,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk1_3(esk4_0,X1,esk6_0))
    | r1_lattice3(esk4_0,X1,esk6_0)
    | ~ r1_lattice3(esk3_0,X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_27])).

cnf(c_0_67,negated_conjecture,
    ( r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_24]),c_0_27]),c_0_17])]),c_0_53])).

cnf(c_0_68,negated_conjecture,
    ( ~ r1_lattice3(esk4_0,esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_64]),c_0_24]),c_0_27]),c_0_17])]),c_0_55])).

cnf(c_0_69,negated_conjecture,
    ( r1_orders_2(esk4_0,X1,esk1_3(esk4_0,X2,esk6_0))
    | r1_lattice3(esk4_0,X2,esk6_0)
    | ~ r1_orders_2(esk3_0,X1,esk1_3(esk4_0,X2,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_47]),c_0_15])])).

cnf(c_0_70,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk1_3(esk4_0,esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68])).

cnf(c_0_71,plain,
    ( r1_lattice3(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,esk1_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_72,negated_conjecture,
    ( r1_orders_2(esk4_0,esk6_0,esk1_3(esk4_0,esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_27])]),c_0_68])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_24]),c_0_27]),c_0_17])]),c_0_68]),
    [proof]).

%------------------------------------------------------------------------------
