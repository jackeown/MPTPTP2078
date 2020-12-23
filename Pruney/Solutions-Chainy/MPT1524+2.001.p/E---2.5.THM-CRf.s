%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:10 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 (1687 expanded)
%              Number of clauses        :   57 ( 694 expanded)
%              Number of leaves         :    6 ( 389 expanded)
%              Depth                    :   17
%              Number of atoms          :  262 (10292 expanded)
%              Number of equality atoms :   28 (2375 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   18 (   3 average)
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

fof(d9_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_orders_2(X1,X2,X3)
              <=> r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

fof(c_0_6,plain,(
    ! [X10,X11,X12,X13] :
      ( ( X10 = X12
        | g1_orders_2(X10,X11) != g1_orders_2(X12,X13)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,X10))) )
      & ( X11 = X13
        | g1_orders_2(X10,X11) != g1_orders_2(X12,X13)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,X10))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

fof(c_0_7,plain,(
    ! [X9] :
      ( ~ l1_orders_2(X9)
      | m1_subset_1(u1_orders_2(X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X9)))) ) ),
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
    ! [X19,X20,X21,X22] :
      ( ( ~ r2_lattice3(X19,X20,X21)
        | ~ m1_subset_1(X22,u1_struct_0(X19))
        | ~ r2_hidden(X22,X20)
        | r1_orders_2(X19,X22,X21)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ l1_orders_2(X19) )
      & ( m1_subset_1(esk2_3(X19,X20,X21),u1_struct_0(X19))
        | r2_lattice3(X19,X20,X21)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ l1_orders_2(X19) )
      & ( r2_hidden(esk2_3(X19,X20,X21),X20)
        | r2_lattice3(X19,X20,X21)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ l1_orders_2(X19) )
      & ( ~ r1_orders_2(X19,esk2_3(X19,X20,X21),X21)
        | r2_lattice3(X19,X20,X21)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ l1_orders_2(X19) ) ) ),
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
    ! [X14,X15,X16,X17] :
      ( ( ~ r1_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X17,u1_struct_0(X14))
        | ~ r2_hidden(X17,X15)
        | r1_orders_2(X14,X16,X17)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) )
      & ( m1_subset_1(esk1_3(X14,X15,X16),u1_struct_0(X14))
        | r1_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) )
      & ( r2_hidden(esk1_3(X14,X15,X16),X15)
        | r1_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) )
      & ( ~ r1_orders_2(X14,X16,esk1_3(X14,X15,X16))
        | r1_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).

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

cnf(c_0_29,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_30,plain,(
    ! [X6,X7,X8] :
      ( ( ~ r1_orders_2(X6,X7,X8)
        | r2_hidden(k4_tarski(X7,X8),u1_orders_2(X6))
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ l1_orders_2(X6) )
      & ( ~ r2_hidden(k4_tarski(X7,X8),u1_orders_2(X6))
        | r1_orders_2(X6,X7,X8)
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ l1_orders_2(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).

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

cnf(c_0_34,negated_conjecture,
    ( r1_lattice3(esk4_0,X1,X2)
    | m1_subset_1(esk1_3(esk4_0,X1,X2),u1_struct_0(esk3_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_24]),c_0_17])])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_36,negated_conjecture,
    ( esk6_0 = esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_37,plain,
    ( r1_orders_2(X3,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk6_0)
    | r1_orders_2(esk3_0,esk2_3(esk4_0,X1,esk6_0),X2)
    | ~ r2_lattice3(esk3_0,X3,X2)
    | ~ r2_hidden(esk2_3(esk4_0,X1,esk6_0),X3)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_15])])).

cnf(c_0_39,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk6_0)
    | r2_hidden(esk2_3(esk4_0,X1,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_27])).

cnf(c_0_40,plain,
    ( r1_orders_2(X1,X3,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_41,negated_conjecture,
    ( r1_lattice3(esk4_0,X1,esk6_0)
    | m1_subset_1(esk1_3(esk4_0,X1,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_27])).

cnf(c_0_42,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( r1_orders_2(esk4_0,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(esk3_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_16]),c_0_17])]),c_0_24]),c_0_24])).

cnf(c_0_45,plain,
    ( r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_46,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk6_0)
    | r1_orders_2(esk3_0,esk2_3(esk4_0,X1,esk6_0),X2)
    | ~ r2_lattice3(esk3_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( r1_lattice3(esk3_0,esk5_0,esk6_0)
    | ~ r2_lattice3(esk4_0,esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_48,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0)
    | ~ r1_lattice3(esk4_0,esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_49,negated_conjecture,
    ( ~ r1_lattice3(esk4_0,esk5_0,esk7_0)
    | ~ r2_lattice3(esk4_0,esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_50,negated_conjecture,
    ( r1_lattice3(esk4_0,X1,esk6_0)
    | r1_orders_2(esk3_0,X2,esk1_3(esk4_0,X1,esk6_0))
    | ~ r1_lattice3(esk3_0,X3,X2)
    | ~ r2_hidden(esk1_3(esk4_0,X1,esk6_0),X3)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_15])])).

cnf(c_0_51,negated_conjecture,
    ( r1_lattice3(esk4_0,X1,esk6_0)
    | r2_hidden(esk1_3(esk4_0,X1,esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_17])])).

cnf(c_0_52,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk2_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_53,negated_conjecture,
    ( r1_orders_2(esk4_0,X1,X2)
    | ~ r1_orders_2(esk3_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_15])])).

cnf(c_0_54,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk6_0)
    | r1_orders_2(esk3_0,esk2_3(esk4_0,X1,esk6_0),esk6_0)
    | ~ r2_lattice3(esk3_0,X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_27])).

cnf(c_0_55,negated_conjecture,
    ( r1_lattice3(esk3_0,esk5_0,esk6_0)
    | r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_56,negated_conjecture,
    ( r1_lattice3(esk3_0,esk5_0,esk6_0)
    | ~ r2_lattice3(esk4_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_47,c_0_36])).

cnf(c_0_57,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0)
    | ~ r1_lattice3(esk4_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_48,c_0_36])).

cnf(c_0_58,negated_conjecture,
    ( ~ r2_lattice3(esk4_0,esk5_0,esk6_0)
    | ~ r1_lattice3(esk4_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_36]),c_0_36])).

cnf(c_0_59,negated_conjecture,
    ( r1_lattice3(esk4_0,X1,esk6_0)
    | r1_orders_2(esk3_0,X2,esk1_3(esk4_0,X1,esk6_0))
    | ~ r1_lattice3(esk3_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_60,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,X2)
    | ~ r1_orders_2(esk3_0,esk2_3(esk4_0,X1,X2),X2)
    | ~ m1_subset_1(esk2_3(esk4_0,X1,X2),u1_struct_0(esk3_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_24]),c_0_17])])).

cnf(c_0_61,negated_conjecture,
    ( r1_lattice3(esk3_0,esk5_0,esk6_0)
    | r1_orders_2(esk3_0,esk2_3(esk4_0,esk5_0,esk6_0),esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( r1_orders_2(esk3_0,esk2_3(esk4_0,esk5_0,esk6_0),esk6_0)
    | ~ r1_lattice3(esk4_0,esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_57]),c_0_58])).

cnf(c_0_63,plain,
    ( r1_lattice3(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,esk1_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_64,negated_conjecture,
    ( r1_lattice3(esk4_0,X1,esk6_0)
    | r1_orders_2(esk3_0,esk6_0,esk1_3(esk4_0,X1,esk6_0))
    | ~ r1_lattice3(esk3_0,X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_27])).

cnf(c_0_65,negated_conjecture,
    ( r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_27])]),c_0_32]),c_0_56])).

cnf(c_0_66,negated_conjecture,
    ( ~ r1_lattice3(esk4_0,esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_62]),c_0_27])]),c_0_32]),c_0_58])).

cnf(c_0_67,negated_conjecture,
    ( r1_lattice3(esk4_0,X1,X2)
    | ~ r1_orders_2(esk3_0,X2,esk1_3(esk4_0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_53]),c_0_24]),c_0_17])]),c_0_34])).

cnf(c_0_68,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk1_3(esk4_0,esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_27])]),c_0_66]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:10:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.20/0.40  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.028 s
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(free_g1_orders_2, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))=>![X3, X4]:(g1_orders_2(X1,X2)=g1_orders_2(X3,X4)=>(X1=X3&X2=X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_orders_2)).
% 0.20/0.40  fof(dt_u1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 0.20/0.40  fof(t2_yellow_0, conjecture, ![X1]:(l1_orders_2(X1)=>![X2]:(l1_orders_2(X2)=>(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))=g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))=>![X3, X4]:(m1_subset_1(X4,u1_struct_0(X1))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>(X4=X5=>((r2_lattice3(X1,X3,X4)=>r2_lattice3(X2,X3,X5))&(r1_lattice3(X1,X3,X4)=>r1_lattice3(X2,X3,X5))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_yellow_0)).
% 0.20/0.40  fof(d9_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattice3)).
% 0.20/0.40  fof(d8_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_lattice3)).
% 0.20/0.40  fof(d9_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_orders_2(X1,X2,X3)<=>r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_orders_2)).
% 0.20/0.40  fof(c_0_6, plain, ![X10, X11, X12, X13]:((X10=X12|g1_orders_2(X10,X11)!=g1_orders_2(X12,X13)|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,X10))))&(X11=X13|g1_orders_2(X10,X11)!=g1_orders_2(X12,X13)|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,X10))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).
% 0.20/0.40  fof(c_0_7, plain, ![X9]:(~l1_orders_2(X9)|m1_subset_1(u1_orders_2(X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X9))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).
% 0.20/0.40  fof(c_0_8, negated_conjecture, ~(![X1]:(l1_orders_2(X1)=>![X2]:(l1_orders_2(X2)=>(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))=g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))=>![X3, X4]:(m1_subset_1(X4,u1_struct_0(X1))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>(X4=X5=>((r2_lattice3(X1,X3,X4)=>r2_lattice3(X2,X3,X5))&(r1_lattice3(X1,X3,X4)=>r1_lattice3(X2,X3,X5)))))))))), inference(assume_negation,[status(cth)],[t2_yellow_0])).
% 0.20/0.40  cnf(c_0_9, plain, (X1=X2|g1_orders_2(X3,X1)!=g1_orders_2(X4,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.40  cnf(c_0_10, plain, (m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.40  fof(c_0_11, negated_conjecture, (l1_orders_2(esk3_0)&(l1_orders_2(esk4_0)&(g1_orders_2(u1_struct_0(esk3_0),u1_orders_2(esk3_0))=g1_orders_2(u1_struct_0(esk4_0),u1_orders_2(esk4_0))&(m1_subset_1(esk6_0,u1_struct_0(esk3_0))&(m1_subset_1(esk7_0,u1_struct_0(esk4_0))&(esk6_0=esk7_0&(((r1_lattice3(esk3_0,esk5_0,esk6_0)|r2_lattice3(esk3_0,esk5_0,esk6_0))&(~r1_lattice3(esk4_0,esk5_0,esk7_0)|r2_lattice3(esk3_0,esk5_0,esk6_0)))&((r1_lattice3(esk3_0,esk5_0,esk6_0)|~r2_lattice3(esk4_0,esk5_0,esk7_0))&(~r1_lattice3(esk4_0,esk5_0,esk7_0)|~r2_lattice3(esk4_0,esk5_0,esk7_0)))))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).
% 0.20/0.40  cnf(c_0_12, plain, (u1_orders_2(X1)=X2|g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))!=g1_orders_2(X3,X2)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.20/0.40  cnf(c_0_13, negated_conjecture, (g1_orders_2(u1_struct_0(esk3_0),u1_orders_2(esk3_0))=g1_orders_2(u1_struct_0(esk4_0),u1_orders_2(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_14, negated_conjecture, (u1_orders_2(X1)=u1_orders_2(esk4_0)|g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))!=g1_orders_2(u1_struct_0(esk3_0),u1_orders_2(esk3_0))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.20/0.40  cnf(c_0_15, negated_conjecture, (l1_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_16, negated_conjecture, (u1_orders_2(esk4_0)=u1_orders_2(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_14]), c_0_15])])).
% 0.20/0.40  cnf(c_0_17, negated_conjecture, (l1_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_18, plain, (X1=X2|g1_orders_2(X1,X3)!=g1_orders_2(X2,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.40  cnf(c_0_19, negated_conjecture, (m1_subset_1(u1_orders_2(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_16]), c_0_17])])).
% 0.20/0.40  cnf(c_0_20, negated_conjecture, (g1_orders_2(u1_struct_0(esk4_0),u1_orders_2(esk3_0))=g1_orders_2(u1_struct_0(esk3_0),u1_orders_2(esk3_0))), inference(rw,[status(thm)],[c_0_13, c_0_16])).
% 0.20/0.40  fof(c_0_21, plain, ![X19, X20, X21, X22]:((~r2_lattice3(X19,X20,X21)|(~m1_subset_1(X22,u1_struct_0(X19))|(~r2_hidden(X22,X20)|r1_orders_2(X19,X22,X21)))|~m1_subset_1(X21,u1_struct_0(X19))|~l1_orders_2(X19))&((m1_subset_1(esk2_3(X19,X20,X21),u1_struct_0(X19))|r2_lattice3(X19,X20,X21)|~m1_subset_1(X21,u1_struct_0(X19))|~l1_orders_2(X19))&((r2_hidden(esk2_3(X19,X20,X21),X20)|r2_lattice3(X19,X20,X21)|~m1_subset_1(X21,u1_struct_0(X19))|~l1_orders_2(X19))&(~r1_orders_2(X19,esk2_3(X19,X20,X21),X21)|r2_lattice3(X19,X20,X21)|~m1_subset_1(X21,u1_struct_0(X19))|~l1_orders_2(X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).
% 0.20/0.40  cnf(c_0_22, negated_conjecture, (u1_struct_0(esk4_0)=X1|g1_orders_2(u1_struct_0(esk3_0),u1_orders_2(esk3_0))!=g1_orders_2(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 0.20/0.40  cnf(c_0_23, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.40  cnf(c_0_24, negated_conjecture, (u1_struct_0(esk4_0)=u1_struct_0(esk3_0)), inference(er,[status(thm)],[c_0_22])).
% 0.20/0.40  fof(c_0_25, plain, ![X14, X15, X16, X17]:((~r1_lattice3(X14,X15,X16)|(~m1_subset_1(X17,u1_struct_0(X14))|(~r2_hidden(X17,X15)|r1_orders_2(X14,X16,X17)))|~m1_subset_1(X16,u1_struct_0(X14))|~l1_orders_2(X14))&((m1_subset_1(esk1_3(X14,X15,X16),u1_struct_0(X14))|r1_lattice3(X14,X15,X16)|~m1_subset_1(X16,u1_struct_0(X14))|~l1_orders_2(X14))&((r2_hidden(esk1_3(X14,X15,X16),X15)|r1_lattice3(X14,X15,X16)|~m1_subset_1(X16,u1_struct_0(X14))|~l1_orders_2(X14))&(~r1_orders_2(X14,X16,esk1_3(X14,X15,X16))|r1_lattice3(X14,X15,X16)|~m1_subset_1(X16,u1_struct_0(X14))|~l1_orders_2(X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).
% 0.20/0.40  cnf(c_0_26, negated_conjecture, (r2_lattice3(esk4_0,X1,X2)|m1_subset_1(esk2_3(esk4_0,X1,X2),u1_struct_0(esk3_0))|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_17])])).
% 0.20/0.40  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_28, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.40  cnf(c_0_29, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.40  fof(c_0_30, plain, ![X6, X7, X8]:((~r1_orders_2(X6,X7,X8)|r2_hidden(k4_tarski(X7,X8),u1_orders_2(X6))|~m1_subset_1(X8,u1_struct_0(X6))|~m1_subset_1(X7,u1_struct_0(X6))|~l1_orders_2(X6))&(~r2_hidden(k4_tarski(X7,X8),u1_orders_2(X6))|r1_orders_2(X6,X7,X8)|~m1_subset_1(X8,u1_struct_0(X6))|~m1_subset_1(X7,u1_struct_0(X6))|~l1_orders_2(X6))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).
% 0.20/0.40  cnf(c_0_31, plain, (r1_orders_2(X1,X4,X3)|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.40  cnf(c_0_32, negated_conjecture, (r2_lattice3(esk4_0,X1,esk6_0)|m1_subset_1(esk2_3(esk4_0,X1,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.40  cnf(c_0_33, negated_conjecture, (r2_lattice3(esk4_0,X1,X2)|r2_hidden(esk2_3(esk4_0,X1,X2),X1)|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_24]), c_0_17])])).
% 0.20/0.40  cnf(c_0_34, negated_conjecture, (r1_lattice3(esk4_0,X1,X2)|m1_subset_1(esk1_3(esk4_0,X1,X2),u1_struct_0(esk3_0))|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_24]), c_0_17])])).
% 0.20/0.40  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_36, negated_conjecture, (esk6_0=esk7_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_37, plain, (r1_orders_2(X3,X1,X2)|~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.40  cnf(c_0_38, negated_conjecture, (r2_lattice3(esk4_0,X1,esk6_0)|r1_orders_2(esk3_0,esk2_3(esk4_0,X1,esk6_0),X2)|~r2_lattice3(esk3_0,X3,X2)|~r2_hidden(esk2_3(esk4_0,X1,esk6_0),X3)|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_15])])).
% 0.20/0.40  cnf(c_0_39, negated_conjecture, (r2_lattice3(esk4_0,X1,esk6_0)|r2_hidden(esk2_3(esk4_0,X1,esk6_0),X1)), inference(spm,[status(thm)],[c_0_33, c_0_27])).
% 0.20/0.40  cnf(c_0_40, plain, (r1_orders_2(X1,X3,X4)|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.40  cnf(c_0_41, negated_conjecture, (r1_lattice3(esk4_0,X1,esk6_0)|m1_subset_1(esk1_3(esk4_0,X1,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_34, c_0_27])).
% 0.20/0.40  cnf(c_0_42, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.40  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk4_0))), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.40  cnf(c_0_44, negated_conjecture, (r1_orders_2(esk4_0,X1,X2)|~r2_hidden(k4_tarski(X1,X2),u1_orders_2(esk3_0))|~m1_subset_1(X2,u1_struct_0(esk3_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_16]), c_0_17])]), c_0_24]), c_0_24])).
% 0.20/0.40  cnf(c_0_45, plain, (r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))|~r1_orders_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.40  cnf(c_0_46, negated_conjecture, (r2_lattice3(esk4_0,X1,esk6_0)|r1_orders_2(esk3_0,esk2_3(esk4_0,X1,esk6_0),X2)|~r2_lattice3(esk3_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.40  cnf(c_0_47, negated_conjecture, (r1_lattice3(esk3_0,esk5_0,esk6_0)|~r2_lattice3(esk4_0,esk5_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_48, negated_conjecture, (r2_lattice3(esk3_0,esk5_0,esk6_0)|~r1_lattice3(esk4_0,esk5_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_49, negated_conjecture, (~r1_lattice3(esk4_0,esk5_0,esk7_0)|~r2_lattice3(esk4_0,esk5_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_50, negated_conjecture, (r1_lattice3(esk4_0,X1,esk6_0)|r1_orders_2(esk3_0,X2,esk1_3(esk4_0,X1,esk6_0))|~r1_lattice3(esk3_0,X3,X2)|~r2_hidden(esk1_3(esk4_0,X1,esk6_0),X3)|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_15])])).
% 0.20/0.40  cnf(c_0_51, negated_conjecture, (r1_lattice3(esk4_0,X1,esk6_0)|r2_hidden(esk1_3(esk4_0,X1,esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_17])])).
% 0.20/0.40  cnf(c_0_52, plain, (r2_lattice3(X1,X2,X3)|~r1_orders_2(X1,esk2_3(X1,X2,X3),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.40  cnf(c_0_53, negated_conjecture, (r1_orders_2(esk4_0,X1,X2)|~r1_orders_2(esk3_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk3_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_15])])).
% 0.20/0.40  cnf(c_0_54, negated_conjecture, (r2_lattice3(esk4_0,X1,esk6_0)|r1_orders_2(esk3_0,esk2_3(esk4_0,X1,esk6_0),esk6_0)|~r2_lattice3(esk3_0,X1,esk6_0)), inference(spm,[status(thm)],[c_0_46, c_0_27])).
% 0.20/0.40  cnf(c_0_55, negated_conjecture, (r1_lattice3(esk3_0,esk5_0,esk6_0)|r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_56, negated_conjecture, (r1_lattice3(esk3_0,esk5_0,esk6_0)|~r2_lattice3(esk4_0,esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_47, c_0_36])).
% 0.20/0.40  cnf(c_0_57, negated_conjecture, (r2_lattice3(esk3_0,esk5_0,esk6_0)|~r1_lattice3(esk4_0,esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_48, c_0_36])).
% 0.20/0.40  cnf(c_0_58, negated_conjecture, (~r2_lattice3(esk4_0,esk5_0,esk6_0)|~r1_lattice3(esk4_0,esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_36]), c_0_36])).
% 0.20/0.40  cnf(c_0_59, negated_conjecture, (r1_lattice3(esk4_0,X1,esk6_0)|r1_orders_2(esk3_0,X2,esk1_3(esk4_0,X1,esk6_0))|~r1_lattice3(esk3_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.40  cnf(c_0_60, negated_conjecture, (r2_lattice3(esk4_0,X1,X2)|~r1_orders_2(esk3_0,esk2_3(esk4_0,X1,X2),X2)|~m1_subset_1(esk2_3(esk4_0,X1,X2),u1_struct_0(esk3_0))|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_24]), c_0_17])])).
% 0.20/0.40  cnf(c_0_61, negated_conjecture, (r1_lattice3(esk3_0,esk5_0,esk6_0)|r1_orders_2(esk3_0,esk2_3(esk4_0,esk5_0,esk6_0),esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])).
% 0.20/0.40  cnf(c_0_62, negated_conjecture, (r1_orders_2(esk3_0,esk2_3(esk4_0,esk5_0,esk6_0),esk6_0)|~r1_lattice3(esk4_0,esk5_0,esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_57]), c_0_58])).
% 0.20/0.40  cnf(c_0_63, plain, (r1_lattice3(X1,X3,X2)|~r1_orders_2(X1,X2,esk1_3(X1,X3,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.40  cnf(c_0_64, negated_conjecture, (r1_lattice3(esk4_0,X1,esk6_0)|r1_orders_2(esk3_0,esk6_0,esk1_3(esk4_0,X1,esk6_0))|~r1_lattice3(esk3_0,X1,esk6_0)), inference(spm,[status(thm)],[c_0_59, c_0_27])).
% 0.20/0.40  cnf(c_0_65, negated_conjecture, (r1_lattice3(esk3_0,esk5_0,esk6_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_27])]), c_0_32]), c_0_56])).
% 0.20/0.40  cnf(c_0_66, negated_conjecture, (~r1_lattice3(esk4_0,esk5_0,esk6_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_62]), c_0_27])]), c_0_32]), c_0_58])).
% 0.20/0.40  cnf(c_0_67, negated_conjecture, (r1_lattice3(esk4_0,X1,X2)|~r1_orders_2(esk3_0,X2,esk1_3(esk4_0,X1,X2))|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_53]), c_0_24]), c_0_17])]), c_0_34])).
% 0.20/0.40  cnf(c_0_68, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,esk1_3(esk4_0,esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66])).
% 0.20/0.40  cnf(c_0_69, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_27])]), c_0_66]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 70
% 0.20/0.40  # Proof object clause steps            : 57
% 0.20/0.40  # Proof object formula steps           : 13
% 0.20/0.40  # Proof object conjectures             : 46
% 0.20/0.40  # Proof object clause conjectures      : 43
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 23
% 0.20/0.40  # Proof object initial formulas used   : 6
% 0.20/0.40  # Proof object generating inferences   : 29
% 0.20/0.40  # Proof object simplifying inferences  : 50
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 6
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 23
% 0.20/0.40  # Removed in clause preprocessing      : 0
% 0.20/0.40  # Initial clauses in saturation        : 23
% 0.20/0.40  # Processed clauses                    : 177
% 0.20/0.40  # ...of these trivial                  : 1
% 0.20/0.40  # ...subsumed                          : 11
% 0.20/0.40  # ...remaining for further processing  : 165
% 0.20/0.40  # Other redundant clauses eliminated   : 0
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 0
% 0.20/0.40  # Backward-rewritten                   : 14
% 0.20/0.40  # Generated clauses                    : 689
% 0.20/0.40  # ...of the previous two non-trivial   : 684
% 0.20/0.40  # Contextual simplify-reflections      : 7
% 0.20/0.40  # Paramodulations                      : 682
% 0.20/0.40  # Factorizations                       : 0
% 0.20/0.40  # Equation resolutions                 : 6
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 150
% 0.20/0.40  #    Positive orientable unit clauses  : 9
% 0.20/0.40  #    Positive unorientable unit clauses: 0
% 0.20/0.40  #    Negative unit clauses             : 1
% 0.20/0.40  #    Non-unit-clauses                  : 140
% 0.20/0.40  # Current number of unprocessed clauses: 524
% 0.20/0.40  # ...number of literals in the above   : 2553
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 15
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 2560
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 640
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 18
% 0.20/0.40  # Unit Clause-clause subsumption calls : 6
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 11
% 0.20/0.40  # BW rewrite match successes           : 4
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 21689
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.053 s
% 0.20/0.40  # System time              : 0.004 s
% 0.20/0.40  # Total time               : 0.057 s
% 0.20/0.40  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
