%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1623+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:28 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   54 (1131 expanded)
%              Number of clauses        :   43 ( 469 expanded)
%              Number of leaves         :    5 ( 264 expanded)
%              Depth                    :   18
%              Number of atoms          :  333 (6493 expanded)
%              Number of equality atoms :   43 (1613 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal clause size      :   55 (   5 average)
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

fof(t3_waybel_0,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( ( X3 = X4
                        & v1_waybel_0(X3,X1) )
                     => v1_waybel_0(X4,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_waybel_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_0)).

fof(d1_waybel_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_waybel_0(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ~ ( r2_hidden(X3,X2)
                        & r2_hidden(X4,X2)
                        & ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ~ ( r2_hidden(X5,X2)
                                & r1_orders_2(X1,X3,X5)
                                & r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_waybel_0)).

fof(c_0_5,plain,(
    ! [X16,X17,X18,X19] :
      ( ( X16 = X18
        | g1_orders_2(X16,X17) != g1_orders_2(X18,X19)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X16,X16))) )
      & ( X17 = X19
        | g1_orders_2(X16,X17) != g1_orders_2(X18,X19)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X16,X16))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

fof(c_0_6,plain,(
    ! [X15] :
      ( ~ l1_orders_2(X15)
      | m1_subset_1(u1_orders_2(X15),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X15)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2] :
            ( l1_orders_2(X2)
           => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( ( X3 = X4
                          & v1_waybel_0(X3,X1) )
                       => v1_waybel_0(X4,X2) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t3_waybel_0])).

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
    ( l1_orders_2(esk4_0)
    & l1_orders_2(esk5_0)
    & g1_orders_2(u1_struct_0(esk4_0),u1_orders_2(esk4_0)) = g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    & esk6_0 = esk7_0
    & v1_waybel_0(esk6_0,esk4_0)
    & ~ v1_waybel_0(esk7_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_11,plain,
    ( u1_orders_2(X1) = X2
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(X3,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk4_0),u1_orders_2(esk4_0)) = g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( u1_orders_2(esk5_0) = X1
    | g1_orders_2(u1_struct_0(esk4_0),u1_orders_2(esk4_0)) != g1_orders_2(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])])).

cnf(c_0_15,negated_conjecture,
    ( u1_orders_2(esk5_0) = u1_orders_2(esk4_0) ),
    inference(er,[status(thm)],[c_0_14])).

fof(c_0_16,plain,(
    ! [X20,X21,X22,X23,X24,X25] :
      ( ( ~ r1_orders_2(X20,X22,X23)
        | r1_orders_2(X21,X24,X25)
        | X22 != X24
        | X23 != X25
        | ~ m1_subset_1(X25,u1_struct_0(X21))
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X20))
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | g1_orders_2(u1_struct_0(X20),u1_orders_2(X20)) != g1_orders_2(u1_struct_0(X21),u1_orders_2(X21))
        | ~ l1_orders_2(X21)
        | ~ l1_orders_2(X20) )
      & ( ~ r2_orders_2(X20,X22,X23)
        | r2_orders_2(X21,X24,X25)
        | X22 != X24
        | X23 != X25
        | ~ m1_subset_1(X25,u1_struct_0(X21))
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X20))
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | g1_orders_2(u1_struct_0(X20),u1_orders_2(X20)) != g1_orders_2(u1_struct_0(X21),u1_orders_2(X21))
        | ~ l1_orders_2(X21)
        | ~ l1_orders_2(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_yellow_0])])])])).

cnf(c_0_17,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(u1_orders_2(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_15]),c_0_13])])).

cnf(c_0_19,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk4_0)) = g1_orders_2(u1_struct_0(esk4_0),u1_orders_2(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_12,c_0_15])).

cnf(c_0_20,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( u1_struct_0(esk5_0) = X1
    | g1_orders_2(u1_struct_0(esk4_0),u1_orders_2(esk4_0)) != g1_orders_2(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_22,plain,
    ( r1_orders_2(X1,X2,X3)
    | g1_orders_2(u1_struct_0(X4),u1_orders_2(X4)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ r1_orders_2(X4,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X2,u1_struct_0(X4))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X4) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_20])])).

cnf(c_0_23,negated_conjecture,
    ( u1_struct_0(esk5_0) = u1_struct_0(esk4_0) ),
    inference(er,[status(thm)],[c_0_21])).

fof(c_0_24,plain,(
    ! [X7,X8,X9,X10,X14] :
      ( ( m1_subset_1(esk1_4(X7,X8,X9,X10),u1_struct_0(X7))
        | ~ r2_hidden(X9,X8)
        | ~ r2_hidden(X10,X8)
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ v1_waybel_0(X8,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_orders_2(X7) )
      & ( r2_hidden(esk1_4(X7,X8,X9,X10),X8)
        | ~ r2_hidden(X9,X8)
        | ~ r2_hidden(X10,X8)
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ v1_waybel_0(X8,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_orders_2(X7) )
      & ( r1_orders_2(X7,X9,esk1_4(X7,X8,X9,X10))
        | ~ r2_hidden(X9,X8)
        | ~ r2_hidden(X10,X8)
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ v1_waybel_0(X8,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_orders_2(X7) )
      & ( r1_orders_2(X7,X10,esk1_4(X7,X8,X9,X10))
        | ~ r2_hidden(X9,X8)
        | ~ r2_hidden(X10,X8)
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ v1_waybel_0(X8,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_orders_2(X7) )
      & ( m1_subset_1(esk2_2(X7,X8),u1_struct_0(X7))
        | v1_waybel_0(X8,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_orders_2(X7) )
      & ( m1_subset_1(esk3_2(X7,X8),u1_struct_0(X7))
        | v1_waybel_0(X8,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_orders_2(X7) )
      & ( r2_hidden(esk2_2(X7,X8),X8)
        | v1_waybel_0(X8,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_orders_2(X7) )
      & ( r2_hidden(esk3_2(X7,X8),X8)
        | v1_waybel_0(X8,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_orders_2(X7) )
      & ( ~ m1_subset_1(X14,u1_struct_0(X7))
        | ~ r2_hidden(X14,X8)
        | ~ r1_orders_2(X7,esk2_2(X7,X8),X14)
        | ~ r1_orders_2(X7,esk3_2(X7,X8),X14)
        | v1_waybel_0(X8,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_orders_2(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_waybel_0])])])])])).

cnf(c_0_25,negated_conjecture,
    ( r1_orders_2(esk5_0,X1,X2)
    | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(esk4_0),u1_orders_2(esk4_0))
    | ~ r1_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_15]),c_0_13])])).

cnf(c_0_26,plain,
    ( m1_subset_1(esk1_4(X1,X2,X3,X4),u1_struct_0(X1))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_28,negated_conjecture,
    ( r1_orders_2(esk5_0,X1,esk1_4(esk4_0,X2,X3,X4))
    | g1_orders_2(u1_struct_0(X5),u1_orders_2(X5)) != g1_orders_2(u1_struct_0(esk4_0),u1_orders_2(esk4_0))
    | ~ r1_orders_2(X5,X1,esk1_4(esk4_0,X2,X3,X4))
    | ~ r2_hidden(X4,X2)
    | ~ r2_hidden(X3,X2)
    | ~ v1_waybel_0(X2,esk4_0)
    | ~ m1_subset_1(esk1_4(esk4_0,X2,X3,X4),u1_struct_0(X5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X4,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(X5))
    | ~ l1_orders_2(X5) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

cnf(c_0_29,plain,
    ( m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | v1_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( v1_waybel_0(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_hidden(X1,X3)
    | ~ r1_orders_2(X2,esk2_2(X2,X3),X1)
    | ~ r1_orders_2(X2,esk3_2(X2,X3),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( r1_orders_2(esk5_0,X1,esk1_4(esk4_0,X2,X3,X4))
    | ~ r1_orders_2(esk4_0,X1,esk1_4(esk4_0,X2,X3,X4))
    | ~ r2_hidden(X4,X2)
    | ~ r2_hidden(X3,X2)
    | ~ v1_waybel_0(X2,esk4_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X4,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_26]),c_0_27])])).

cnf(c_0_32,negated_conjecture,
    ( v1_waybel_0(X1,esk5_0)
    | m1_subset_1(esk3_2(esk5_0,X1),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_23]),c_0_13])])).

cnf(c_0_33,plain,
    ( m1_subset_1(esk2_2(X1,X2),u1_struct_0(X1))
    | v1_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( v1_waybel_0(X1,esk5_0)
    | ~ r1_orders_2(esk5_0,esk2_2(esk5_0,X1),esk1_4(esk4_0,X2,X3,X4))
    | ~ r1_orders_2(esk4_0,esk3_2(esk5_0,X1),esk1_4(esk4_0,X2,X3,X4))
    | ~ r2_hidden(esk1_4(esk4_0,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X2)
    | ~ r2_hidden(X3,X2)
    | ~ v1_waybel_0(X2,esk4_0)
    | ~ m1_subset_1(esk1_4(esk4_0,X2,X3,X4),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X4,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_23]),c_0_23]),c_0_13])]),c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( v1_waybel_0(X1,esk5_0)
    | m1_subset_1(esk2_2(esk5_0,X1),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_23]),c_0_13])])).

cnf(c_0_36,negated_conjecture,
    ( v1_waybel_0(X1,esk5_0)
    | ~ r1_orders_2(esk4_0,esk3_2(esk5_0,X1),esk1_4(esk4_0,X2,X3,X4))
    | ~ r1_orders_2(esk4_0,esk2_2(esk5_0,X1),esk1_4(esk4_0,X2,X3,X4))
    | ~ r2_hidden(esk1_4(esk4_0,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X2)
    | ~ r2_hidden(X3,X2)
    | ~ v1_waybel_0(X2,esk4_0)
    | ~ m1_subset_1(esk1_4(esk4_0,X2,X3,X4),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X4,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_31]),c_0_35])).

cnf(c_0_37,plain,
    ( r1_orders_2(X1,X2,esk1_4(X1,X3,X4,X2))
    | ~ r2_hidden(X4,X3)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v1_waybel_0(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_38,negated_conjecture,
    ( v1_waybel_0(X1,esk5_0)
    | ~ r1_orders_2(esk4_0,esk2_2(esk5_0,X1),esk1_4(esk4_0,X2,X3,esk3_2(esk5_0,X1)))
    | ~ r2_hidden(esk1_4(esk4_0,X2,X3,esk3_2(esk5_0,X1)),X1)
    | ~ r2_hidden(esk3_2(esk5_0,X1),X2)
    | ~ r2_hidden(X3,X2)
    | ~ v1_waybel_0(X2,esk4_0)
    | ~ m1_subset_1(esk1_4(esk4_0,X2,X3,esk3_2(esk5_0,X1)),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X3,u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_27])]),c_0_32])).

cnf(c_0_39,plain,
    ( r1_orders_2(X1,X2,esk1_4(X1,X3,X2,X4))
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_waybel_0(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_40,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | v1_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_41,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | v1_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_42,negated_conjecture,
    ( v1_waybel_0(X1,esk5_0)
    | ~ r2_hidden(esk1_4(esk4_0,X2,esk2_2(esk5_0,X1),esk3_2(esk5_0,X1)),X1)
    | ~ r2_hidden(esk3_2(esk5_0,X1),X2)
    | ~ r2_hidden(esk2_2(esk5_0,X1),X2)
    | ~ v1_waybel_0(X2,esk4_0)
    | ~ m1_subset_1(esk1_4(esk4_0,X2,esk2_2(esk5_0,X1),esk3_2(esk5_0,X1)),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_27])]),c_0_32]),c_0_35])).

cnf(c_0_43,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk2_2(esk5_0,X1),X1)
    | v1_waybel_0(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_23]),c_0_13])])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk3_2(esk5_0,X1),X1)
    | v1_waybel_0(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_23]),c_0_13])])).

cnf(c_0_46,negated_conjecture,
    ( v1_waybel_0(X1,esk5_0)
    | ~ v1_waybel_0(X1,esk4_0)
    | ~ m1_subset_1(esk1_4(esk4_0,X1,esk2_2(esk5_0,X1),esk3_2(esk5_0,X1)),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_27])]),c_0_35]),c_0_32]),c_0_44]),c_0_45])).

cnf(c_0_47,negated_conjecture,
    ( ~ v1_waybel_0(esk7_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_48,negated_conjecture,
    ( esk6_0 = esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_49,negated_conjecture,
    ( v1_waybel_0(X1,esk5_0)
    | ~ v1_waybel_0(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_26]),c_0_27])]),c_0_35]),c_0_32]),c_0_44]),c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_51,negated_conjecture,
    ( v1_waybel_0(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_52,negated_conjecture,
    ( ~ v1_waybel_0(esk6_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])]),c_0_52]),
    [proof]).

%------------------------------------------------------------------------------
