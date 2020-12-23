%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1523+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:19 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   55 (1554 expanded)
%              Number of clauses        :   44 ( 618 expanded)
%              Number of leaves         :    5 ( 359 expanded)
%              Depth                    :   17
%              Number of atoms          :  196 (11807 expanded)
%              Number of equality atoms :   45 (2939 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   17 (   2 average)
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

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(t1_yellow_0,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_0)).

fof(d10_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_orders_2(X1,X2,X3)
              <=> ( r1_orders_2(X1,X2,X3)
                  & X2 != X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

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

fof(c_0_5,plain,(
    ! [X14,X15,X16,X17] :
      ( ( X14 = X16
        | g1_orders_2(X14,X15) != g1_orders_2(X16,X17)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X14,X14))) )
      & ( X15 = X17
        | g1_orders_2(X14,X15) != g1_orders_2(X16,X17)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X14,X14))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

fof(c_0_6,plain,(
    ! [X13] :
      ( ~ l1_orders_2(X13)
      | m1_subset_1(u1_orders_2(X13),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X13)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
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
    inference(assume_negation,[status(cth)],[t1_yellow_0])).

cnf(c_0_8,plain,
    ( X1 = X2
    | g1_orders_2(X3,X1) != g1_orders_2(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,negated_conjecture,
    ( l1_orders_2(esk1_0)
    & l1_orders_2(esk2_0)
    & g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) = g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0))
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk4_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk5_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk6_0,u1_struct_0(esk2_0))
    & esk3_0 = esk5_0
    & esk4_0 = esk6_0
    & ( r2_orders_2(esk1_0,esk3_0,esk4_0)
      | r1_orders_2(esk1_0,esk3_0,esk4_0) )
    & ( ~ r2_orders_2(esk2_0,esk5_0,esk6_0)
      | r1_orders_2(esk1_0,esk3_0,esk4_0) )
    & ( r2_orders_2(esk1_0,esk3_0,esk4_0)
      | ~ r1_orders_2(esk2_0,esk5_0,esk6_0) )
    & ( ~ r2_orders_2(esk2_0,esk5_0,esk6_0)
      | ~ r1_orders_2(esk2_0,esk5_0,esk6_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).

cnf(c_0_11,plain,
    ( u1_orders_2(X1) = X2
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(X3,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) = g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( u1_orders_2(esk2_0) = X1
    | g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) != g1_orders_2(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])])).

cnf(c_0_15,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,negated_conjecture,
    ( u1_orders_2(esk2_0) = u1_orders_2(esk1_0) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_17,plain,
    ( u1_struct_0(X1) = X2
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_9])).

cnf(c_0_18,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk1_0)) = g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_12,c_0_16])).

fof(c_0_19,plain,(
    ! [X7,X8,X9] :
      ( ( r1_orders_2(X7,X8,X9)
        | ~ r2_orders_2(X7,X8,X9)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ l1_orders_2(X7) )
      & ( X8 != X9
        | ~ r2_orders_2(X7,X8,X9)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ l1_orders_2(X7) )
      & ( ~ r1_orders_2(X7,X8,X9)
        | X8 = X9
        | r2_orders_2(X7,X8,X9)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ l1_orders_2(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_orders_2])])])])).

fof(c_0_20,plain,(
    ! [X10,X11,X12] :
      ( ( ~ r1_orders_2(X10,X11,X12)
        | r2_hidden(k4_tarski(X11,X12),u1_orders_2(X10))
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ l1_orders_2(X10) )
      & ( ~ r2_hidden(k4_tarski(X11,X12),u1_orders_2(X10))
        | r1_orders_2(X10,X11,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ l1_orders_2(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).

cnf(c_0_21,negated_conjecture,
    ( u1_struct_0(esk2_0) = X1
    | g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) != g1_orders_2(X1,X2) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_16]),c_0_13])]),c_0_18])).

cnf(c_0_22,plain,
    ( X2 = X3
    | r2_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_24,plain,
    ( r1_orders_2(X3,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( u1_struct_0(esk2_0) = u1_struct_0(esk1_0) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( X1 = esk6_0
    | r2_orders_2(esk2_0,X1,esk6_0)
    | ~ r1_orders_2(esk2_0,X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_13])])).

cnf(c_0_27,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_16]),c_0_13])]),c_0_25]),c_0_25])).

cnf(c_0_28,plain,
    ( r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_31,negated_conjecture,
    ( esk4_0 = esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_32,negated_conjecture,
    ( r2_orders_2(esk1_0,esk3_0,esk4_0)
    | r1_orders_2(esk1_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_33,negated_conjecture,
    ( X1 = esk6_0
    | r2_orders_2(esk2_0,X1,esk6_0)
    | ~ r1_orders_2(esk2_0,X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_26,c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,X2)
    | ~ r1_orders_2(esk1_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,plain,
    ( r1_orders_2(X1,X2,X3)
    | ~ r2_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_37,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk6_0)
    | r2_orders_2(esk1_0,esk3_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_31]),c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_39,negated_conjecture,
    ( ~ r2_orders_2(esk2_0,esk5_0,esk6_0)
    | ~ r1_orders_2(esk2_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_40,negated_conjecture,
    ( esk3_0 = esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_41,negated_conjecture,
    ( X1 = esk6_0
    | r2_orders_2(esk2_0,X1,esk6_0)
    | ~ r1_orders_2(esk1_0,X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

cnf(c_0_42,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_35]),c_0_38]),c_0_29])])).

cnf(c_0_43,negated_conjecture,
    ( ~ r1_orders_2(esk2_0,esk3_0,esk6_0)
    | ~ r2_orders_2(esk2_0,esk3_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40]),c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( esk6_0 = esk3_0
    | r2_orders_2(esk2_0,esk3_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_38])])).

cnf(c_0_45,negated_conjecture,
    ( r2_orders_2(esk1_0,esk3_0,esk4_0)
    | ~ r1_orders_2(esk2_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_46,negated_conjecture,
    ( esk6_0 = esk3_0
    | ~ r1_orders_2(esk2_0,esk3_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_47,plain,
    ( X1 != X2
    | ~ r2_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_48,negated_conjecture,
    ( r2_orders_2(esk1_0,esk3_0,esk6_0)
    | ~ r1_orders_2(esk2_0,esk3_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_31]),c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( esk6_0 = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_34]),c_0_42]),c_0_35]),c_0_38])])).

cnf(c_0_50,plain,
    ( ~ r2_orders_2(X1,X2,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( r2_orders_2(esk1_0,esk3_0,esk3_0)
    | ~ r1_orders_2(esk2_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49]),c_0_49])).

cnf(c_0_52,negated_conjecture,
    ( ~ r1_orders_2(esk2_0,esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_38]),c_0_29])])).

cnf(c_0_53,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_42,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_34]),c_0_53]),c_0_38])]),
    [proof]).

%------------------------------------------------------------------------------
