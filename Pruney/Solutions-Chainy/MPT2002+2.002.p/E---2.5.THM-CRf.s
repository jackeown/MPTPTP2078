%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:32 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 876 expanded)
%              Number of clauses        :   64 ( 317 expanded)
%              Number of leaves         :    5 ( 201 expanded)
%              Depth                    :   18
%              Number of atoms          :  395 (10013 expanded)
%              Number of equality atoms :   76 (1785 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal clause size      :   70 (   4 average)
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

fof(t1_waybel_9,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & l1_orders_2(X3) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & l1_orders_2(X4) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                     => ! [X6] :
                          ( ( v1_funct_1(X6)
                            & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X4))
                            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4)))) )
                         => ( ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                              & g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))
                              & X5 = X6
                              & v5_orders_3(X5,X1,X2) )
                           => v5_orders_3(X6,X3,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_waybel_9)).

fof(d5_orders_3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( v5_orders_3(X3,X1,X2)
              <=> ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X1))
                       => ( r1_orders_2(X1,X4,X5)
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X2))
                             => ! [X7] :
                                  ( m1_subset_1(X7,u1_struct_0(X2))
                                 => ( ( X6 = k1_funct_1(X3,X4)
                                      & X7 = k1_funct_1(X3,X5) )
                                   => r1_orders_2(X2,X6,X7) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_orders_3)).

fof(l20_yellow_6,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X2))
                         => ( ( X3 = X5
                              & X4 = X6
                              & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
                              & r1_orders_2(X1,X3,X4) )
                           => r1_orders_2(X2,X5,X6) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l20_yellow_6)).

fof(c_0_5,plain,(
    ! [X9,X10,X11,X12] :
      ( ( X9 = X11
        | g1_orders_2(X9,X10) != g1_orders_2(X11,X12)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X9,X9))) )
      & ( X10 = X12
        | g1_orders_2(X9,X10) != g1_orders_2(X11,X12)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X9,X9))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

fof(c_0_6,plain,(
    ! [X8] :
      ( ~ l1_orders_2(X8)
      | m1_subset_1(u1_orders_2(X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X8)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2] :
            ( l1_orders_2(X2)
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & l1_orders_2(X3) )
               => ! [X4] :
                    ( ( ~ v2_struct_0(X4)
                      & l1_orders_2(X4) )
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                       => ! [X6] :
                            ( ( v1_funct_1(X6)
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X4))
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4)))) )
                           => ( ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                                & g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))
                                & X5 = X6
                                & v5_orders_3(X5,X1,X2) )
                             => v5_orders_3(X6,X3,X4) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t1_waybel_9])).

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
    ( l1_orders_2(esk5_0)
    & l1_orders_2(esk6_0)
    & ~ v2_struct_0(esk7_0)
    & l1_orders_2(esk7_0)
    & ~ v2_struct_0(esk8_0)
    & l1_orders_2(esk8_0)
    & v1_funct_1(esk9_0)
    & v1_funct_2(esk9_0,u1_struct_0(esk5_0),u1_struct_0(esk6_0))
    & m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk6_0))))
    & v1_funct_1(esk10_0)
    & v1_funct_2(esk10_0,u1_struct_0(esk7_0),u1_struct_0(esk8_0))
    & m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0))))
    & g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0)) = g1_orders_2(u1_struct_0(esk7_0),u1_orders_2(esk7_0))
    & g1_orders_2(u1_struct_0(esk6_0),u1_orders_2(esk6_0)) = g1_orders_2(u1_struct_0(esk8_0),u1_orders_2(esk8_0))
    & esk9_0 = esk10_0
    & v5_orders_3(esk9_0,esk5_0,esk6_0)
    & ~ v5_orders_3(esk10_0,esk7_0,esk8_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).

cnf(c_0_11,plain,
    ( u1_orders_2(X1) = X2
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(X3,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk6_0),u1_orders_2(esk6_0)) = g1_orders_2(u1_struct_0(esk8_0),u1_orders_2(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( l1_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( u1_orders_2(esk6_0) = X1
    | g1_orders_2(u1_struct_0(esk8_0),u1_orders_2(esk8_0)) != g1_orders_2(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])])).

cnf(c_0_15,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0)) = g1_orders_2(u1_struct_0(esk7_0),u1_orders_2(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( u1_orders_2(esk6_0) = u1_orders_2(esk8_0) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( u1_orders_2(esk5_0) = X1
    | g1_orders_2(u1_struct_0(esk7_0),u1_orders_2(esk7_0)) != g1_orders_2(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_15]),c_0_16])])).

cnf(c_0_19,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(u1_orders_2(esk8_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_17]),c_0_13])])).

cnf(c_0_21,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk6_0),u1_orders_2(esk8_0)) = g1_orders_2(u1_struct_0(esk8_0),u1_orders_2(esk8_0)) ),
    inference(rw,[status(thm)],[c_0_12,c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( u1_orders_2(esk5_0) = u1_orders_2(esk7_0) ),
    inference(er,[status(thm)],[c_0_18])).

fof(c_0_23,plain,(
    ! [X14,X15,X16,X17,X18,X19,X20] :
      ( ( ~ v5_orders_3(X16,X14,X15)
        | ~ m1_subset_1(X17,u1_struct_0(X14))
        | ~ m1_subset_1(X18,u1_struct_0(X14))
        | ~ r1_orders_2(X14,X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X15))
        | ~ m1_subset_1(X20,u1_struct_0(X15))
        | X19 != k1_funct_1(X16,X17)
        | X20 != k1_funct_1(X16,X18)
        | r1_orders_2(X15,X19,X20)
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15))))
        | ~ l1_orders_2(X15)
        | ~ l1_orders_2(X14) )
      & ( m1_subset_1(esk1_3(X14,X15,X16),u1_struct_0(X14))
        | v5_orders_3(X16,X14,X15)
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15))))
        | ~ l1_orders_2(X15)
        | ~ l1_orders_2(X14) )
      & ( m1_subset_1(esk2_3(X14,X15,X16),u1_struct_0(X14))
        | v5_orders_3(X16,X14,X15)
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15))))
        | ~ l1_orders_2(X15)
        | ~ l1_orders_2(X14) )
      & ( r1_orders_2(X14,esk1_3(X14,X15,X16),esk2_3(X14,X15,X16))
        | v5_orders_3(X16,X14,X15)
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15))))
        | ~ l1_orders_2(X15)
        | ~ l1_orders_2(X14) )
      & ( m1_subset_1(esk3_3(X14,X15,X16),u1_struct_0(X15))
        | v5_orders_3(X16,X14,X15)
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15))))
        | ~ l1_orders_2(X15)
        | ~ l1_orders_2(X14) )
      & ( m1_subset_1(esk4_3(X14,X15,X16),u1_struct_0(X15))
        | v5_orders_3(X16,X14,X15)
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15))))
        | ~ l1_orders_2(X15)
        | ~ l1_orders_2(X14) )
      & ( esk3_3(X14,X15,X16) = k1_funct_1(X16,esk1_3(X14,X15,X16))
        | v5_orders_3(X16,X14,X15)
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15))))
        | ~ l1_orders_2(X15)
        | ~ l1_orders_2(X14) )
      & ( esk4_3(X14,X15,X16) = k1_funct_1(X16,esk2_3(X14,X15,X16))
        | v5_orders_3(X16,X14,X15)
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15))))
        | ~ l1_orders_2(X15)
        | ~ l1_orders_2(X14) )
      & ( ~ r1_orders_2(X15,esk3_3(X14,X15,X16),esk4_3(X14,X15,X16))
        | v5_orders_3(X16,X14,X15)
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15))))
        | ~ l1_orders_2(X15)
        | ~ l1_orders_2(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_orders_3])])])])])).

cnf(c_0_24,negated_conjecture,
    ( u1_struct_0(esk6_0) = X1
    | g1_orders_2(u1_struct_0(esk8_0),u1_orders_2(esk8_0)) != g1_orders_2(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(u1_orders_2(esk7_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_22]),c_0_16])])).

cnf(c_0_26,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk7_0)) = g1_orders_2(u1_struct_0(esk7_0),u1_orders_2(esk7_0)) ),
    inference(rw,[status(thm)],[c_0_15,c_0_22])).

cnf(c_0_27,plain,
    ( r1_orders_2(X3,X6,X7)
    | ~ v5_orders_3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ r1_orders_2(X2,X4,X5)
    | ~ m1_subset_1(X6,u1_struct_0(X3))
    | ~ m1_subset_1(X7,u1_struct_0(X3))
    | X6 != k1_funct_1(X1,X4)
    | X7 != k1_funct_1(X1,X5)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_orders_2(X3)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( u1_struct_0(esk6_0) = u1_struct_0(esk8_0) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( u1_struct_0(esk5_0) = X1
    | g1_orders_2(u1_struct_0(esk7_0),u1_orders_2(esk7_0)) != g1_orders_2(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_25]),c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( r1_orders_2(esk6_0,X1,X2)
    | X2 != k1_funct_1(X3,X4)
    | X1 != k1_funct_1(X3,X5)
    | ~ r1_orders_2(X6,X5,X4)
    | ~ v5_orders_3(X3,X6,esk6_0)
    | ~ v1_funct_2(X3,u1_struct_0(X6),u1_struct_0(esk8_0))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(esk8_0))))
    | ~ m1_subset_1(X2,u1_struct_0(esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0))
    | ~ m1_subset_1(X4,u1_struct_0(X6))
    | ~ m1_subset_1(X5,u1_struct_0(X6))
    | ~ l1_orders_2(X6) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_13])])).

cnf(c_0_31,negated_conjecture,
    ( u1_struct_0(esk5_0) = u1_struct_0(esk7_0) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_33,negated_conjecture,
    ( esk9_0 = esk10_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_2(esk10_0,u1_struct_0(esk7_0),u1_struct_0(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_35,negated_conjecture,
    ( ~ v5_orders_3(esk10_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_36,plain,(
    ! [X25,X26,X27,X28,X29,X30] :
      ( ~ l1_orders_2(X25)
      | ~ l1_orders_2(X26)
      | ~ m1_subset_1(X27,u1_struct_0(X25))
      | ~ m1_subset_1(X28,u1_struct_0(X25))
      | ~ m1_subset_1(X29,u1_struct_0(X26))
      | ~ m1_subset_1(X30,u1_struct_0(X26))
      | X27 != X29
      | X28 != X30
      | g1_orders_2(u1_struct_0(X25),u1_orders_2(X25)) != g1_orders_2(u1_struct_0(X26),u1_orders_2(X26))
      | ~ r1_orders_2(X25,X27,X28)
      | r1_orders_2(X26,X29,X30) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l20_yellow_6])])])).

cnf(c_0_37,negated_conjecture,
    ( r1_orders_2(esk6_0,X1,X2)
    | X2 != k1_funct_1(X3,X4)
    | X1 != k1_funct_1(X3,X5)
    | ~ r1_orders_2(esk5_0,X5,X4)
    | ~ v5_orders_3(X3,esk5_0,esk6_0)
    | ~ v1_funct_2(X3,u1_struct_0(esk7_0),u1_struct_0(esk8_0))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0))))
    | ~ m1_subset_1(X2,u1_struct_0(esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0))
    | ~ m1_subset_1(X4,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X5,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_16])])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0)))) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( v5_orders_3(esk9_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_40,negated_conjecture,
    ( v1_funct_2(esk9_0,u1_struct_0(esk7_0),u1_struct_0(esk8_0)) ),
    inference(rw,[status(thm)],[c_0_34,c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_42,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X2))
    | v5_orders_3(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_43,negated_conjecture,
    ( l1_orders_2(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_44,negated_conjecture,
    ( l1_orders_2(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_45,negated_conjecture,
    ( ~ v5_orders_3(esk9_0,esk7_0,esk8_0) ),
    inference(rw,[status(thm)],[c_0_35,c_0_33])).

cnf(c_0_46,plain,
    ( r1_orders_2(X2,X5,X6)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ m1_subset_1(X6,u1_struct_0(X2))
    | X3 != X5
    | X4 != X6
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
    | ~ r1_orders_2(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( r1_orders_2(esk6_0,X1,X2)
    | X2 != k1_funct_1(esk9_0,X3)
    | X1 != k1_funct_1(esk9_0,X4)
    | ~ r1_orders_2(esk5_0,X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X4,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40]),c_0_41])])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk4_3(esk7_0,esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_38]),c_0_40]),c_0_41]),c_0_43]),c_0_44])]),c_0_45])).

cnf(c_0_49,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X2))
    | v5_orders_3(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_50,plain,
    ( r1_orders_2(X1,X2,X3)
    | g1_orders_2(u1_struct_0(X4),u1_orders_2(X4)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ r1_orders_2(X4,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X2,u1_struct_0(X4))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X4) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_46])])).

cnf(c_0_51,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | v5_orders_3(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_52,negated_conjecture,
    ( r1_orders_2(esk6_0,X1,esk4_3(esk7_0,esk8_0,esk9_0))
    | esk4_3(esk7_0,esk8_0,esk9_0) != k1_funct_1(esk9_0,X2)
    | X1 != k1_funct_1(esk9_0,X3)
    | ~ r1_orders_2(esk5_0,X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk3_3(esk7_0,esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_38]),c_0_40]),c_0_41]),c_0_43]),c_0_44])]),c_0_45])).

cnf(c_0_54,plain,
    ( esk4_3(X1,X2,X3) = k1_funct_1(X3,esk2_3(X1,X2,X3))
    | v5_orders_3(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_55,negated_conjecture,
    ( r1_orders_2(esk5_0,X1,X2)
    | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(esk7_0),u1_orders_2(esk7_0))
    | ~ r1_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_31]),c_0_22]),c_0_16])])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk2_3(esk7_0,esk8_0,esk9_0),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_38]),c_0_40]),c_0_41]),c_0_43]),c_0_44])]),c_0_45])).

cnf(c_0_57,negated_conjecture,
    ( r1_orders_2(esk6_0,esk3_3(esk7_0,esk8_0,esk9_0),esk4_3(esk7_0,esk8_0,esk9_0))
    | esk4_3(esk7_0,esk8_0,esk9_0) != k1_funct_1(esk9_0,X1)
    | esk3_3(esk7_0,esk8_0,esk9_0) != k1_funct_1(esk9_0,X2)
    | ~ r1_orders_2(esk5_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( k1_funct_1(esk9_0,esk2_3(esk7_0,esk8_0,esk9_0)) = esk4_3(esk7_0,esk8_0,esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_38]),c_0_40]),c_0_41]),c_0_43]),c_0_44])]),c_0_45])).

cnf(c_0_59,negated_conjecture,
    ( r1_orders_2(esk5_0,X1,esk2_3(esk7_0,esk8_0,esk9_0))
    | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(esk7_0),u1_orders_2(esk7_0))
    | ~ r1_orders_2(X2,X1,esk2_3(esk7_0,esk8_0,esk9_0))
    | ~ m1_subset_1(esk2_3(esk7_0,esk8_0,esk9_0),u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( r1_orders_2(esk6_0,esk3_3(esk7_0,esk8_0,esk9_0),esk4_3(esk7_0,esk8_0,esk9_0))
    | esk3_3(esk7_0,esk8_0,esk9_0) != k1_funct_1(esk9_0,X1)
    | ~ r1_orders_2(esk5_0,X1,esk2_3(esk7_0,esk8_0,esk9_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_56]),c_0_58])])).

cnf(c_0_61,negated_conjecture,
    ( r1_orders_2(esk5_0,X1,esk2_3(esk7_0,esk8_0,esk9_0))
    | ~ r1_orders_2(esk7_0,X1,esk2_3(esk7_0,esk8_0,esk9_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_56]),c_0_44])])).

cnf(c_0_62,plain,
    ( r1_orders_2(X1,esk1_3(X1,X2,X3),esk2_3(X1,X2,X3))
    | v5_orders_3(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_63,plain,
    ( esk3_3(X1,X2,X3) = k1_funct_1(X3,esk1_3(X1,X2,X3))
    | v5_orders_3(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_64,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | v5_orders_3(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_65,negated_conjecture,
    ( r1_orders_2(esk8_0,X1,esk4_3(esk7_0,esk8_0,esk9_0))
    | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(esk8_0),u1_orders_2(esk8_0))
    | ~ r1_orders_2(X2,X1,esk4_3(esk7_0,esk8_0,esk9_0))
    | ~ m1_subset_1(esk4_3(esk7_0,esk8_0,esk9_0),u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_48]),c_0_43])])).

cnf(c_0_66,negated_conjecture,
    ( r1_orders_2(esk6_0,esk3_3(esk7_0,esk8_0,esk9_0),esk4_3(esk7_0,esk8_0,esk9_0))
    | esk3_3(esk7_0,esk8_0,esk9_0) != k1_funct_1(esk9_0,X1)
    | ~ r1_orders_2(esk7_0,X1,esk2_3(esk7_0,esk8_0,esk9_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( r1_orders_2(esk7_0,esk1_3(esk7_0,esk8_0,esk9_0),esk2_3(esk7_0,esk8_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_38]),c_0_40]),c_0_41]),c_0_43]),c_0_44])]),c_0_45])).

cnf(c_0_68,negated_conjecture,
    ( k1_funct_1(esk9_0,esk1_3(esk7_0,esk8_0,esk9_0)) = esk3_3(esk7_0,esk8_0,esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_38]),c_0_40]),c_0_41]),c_0_43]),c_0_44])]),c_0_45])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(esk1_3(esk7_0,esk8_0,esk9_0),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_38]),c_0_40]),c_0_41]),c_0_43]),c_0_44])]),c_0_45])).

cnf(c_0_70,negated_conjecture,
    ( r1_orders_2(esk8_0,X1,esk4_3(esk7_0,esk8_0,esk9_0))
    | ~ r1_orders_2(esk6_0,X1,esk4_3(esk7_0,esk8_0,esk9_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_28]),c_0_17]),c_0_48]),c_0_13])])).

cnf(c_0_71,negated_conjecture,
    ( r1_orders_2(esk6_0,esk3_3(esk7_0,esk8_0,esk9_0),esk4_3(esk7_0,esk8_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68]),c_0_69])])).

cnf(c_0_72,plain,
    ( v5_orders_3(X3,X2,X1)
    | ~ r1_orders_2(X1,esk3_3(X2,X1,X3),esk4_3(X2,X1,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_73,negated_conjecture,
    ( r1_orders_2(esk8_0,esk3_3(esk7_0,esk8_0,esk9_0),esk4_3(esk7_0,esk8_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_53])])).

cnf(c_0_74,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_40]),c_0_41]),c_0_38]),c_0_44]),c_0_43])]),c_0_45]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:31:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.46  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_AE_CS_SP_PS_S0V
% 0.18/0.46  # and selection function PSelectComplexExceptRRHorn.
% 0.18/0.46  #
% 0.18/0.46  # Preprocessing time       : 0.031 s
% 0.18/0.46  # Presaturation interreduction done
% 0.18/0.46  
% 0.18/0.46  # Proof found!
% 0.18/0.46  # SZS status Theorem
% 0.18/0.46  # SZS output start CNFRefutation
% 0.18/0.46  fof(free_g1_orders_2, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))=>![X3, X4]:(g1_orders_2(X1,X2)=g1_orders_2(X3,X4)=>(X1=X3&X2=X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_orders_2)).
% 0.18/0.46  fof(dt_u1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 0.18/0.46  fof(t1_waybel_9, conjecture, ![X1]:(l1_orders_2(X1)=>![X2]:(l1_orders_2(X2)=>![X3]:((~(v2_struct_0(X3))&l1_orders_2(X3))=>![X4]:((~(v2_struct_0(X4))&l1_orders_2(X4))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X4)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4)))))=>((((g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))=g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))&g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))=g1_orders_2(u1_struct_0(X4),u1_orders_2(X4)))&X5=X6)&v5_orders_3(X5,X1,X2))=>v5_orders_3(X6,X3,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_waybel_9)).
% 0.18/0.46  fof(d5_orders_3, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(l1_orders_2(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v5_orders_3(X3,X1,X2)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>(r1_orders_2(X1,X4,X5)=>![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>![X7]:(m1_subset_1(X7,u1_struct_0(X2))=>((X6=k1_funct_1(X3,X4)&X7=k1_funct_1(X3,X5))=>r1_orders_2(X2,X6,X7))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_orders_3)).
% 0.18/0.46  fof(l20_yellow_6, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(l1_orders_2(X2)=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>((((X3=X5&X4=X6)&g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))=g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)))&r1_orders_2(X1,X3,X4))=>r1_orders_2(X2,X5,X6)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l20_yellow_6)).
% 0.18/0.46  fof(c_0_5, plain, ![X9, X10, X11, X12]:((X9=X11|g1_orders_2(X9,X10)!=g1_orders_2(X11,X12)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X9,X9))))&(X10=X12|g1_orders_2(X9,X10)!=g1_orders_2(X11,X12)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X9,X9))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).
% 0.18/0.46  fof(c_0_6, plain, ![X8]:(~l1_orders_2(X8)|m1_subset_1(u1_orders_2(X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X8))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).
% 0.18/0.46  fof(c_0_7, negated_conjecture, ~(![X1]:(l1_orders_2(X1)=>![X2]:(l1_orders_2(X2)=>![X3]:((~(v2_struct_0(X3))&l1_orders_2(X3))=>![X4]:((~(v2_struct_0(X4))&l1_orders_2(X4))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X4)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4)))))=>((((g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))=g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))&g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))=g1_orders_2(u1_struct_0(X4),u1_orders_2(X4)))&X5=X6)&v5_orders_3(X5,X1,X2))=>v5_orders_3(X6,X3,X4))))))))), inference(assume_negation,[status(cth)],[t1_waybel_9])).
% 0.18/0.46  cnf(c_0_8, plain, (X1=X2|g1_orders_2(X3,X1)!=g1_orders_2(X4,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3)))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.18/0.46  cnf(c_0_9, plain, (m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.18/0.46  fof(c_0_10, negated_conjecture, (l1_orders_2(esk5_0)&(l1_orders_2(esk6_0)&((~v2_struct_0(esk7_0)&l1_orders_2(esk7_0))&((~v2_struct_0(esk8_0)&l1_orders_2(esk8_0))&(((v1_funct_1(esk9_0)&v1_funct_2(esk9_0,u1_struct_0(esk5_0),u1_struct_0(esk6_0)))&m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk6_0)))))&(((v1_funct_1(esk10_0)&v1_funct_2(esk10_0,u1_struct_0(esk7_0),u1_struct_0(esk8_0)))&m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0)))))&((((g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0))=g1_orders_2(u1_struct_0(esk7_0),u1_orders_2(esk7_0))&g1_orders_2(u1_struct_0(esk6_0),u1_orders_2(esk6_0))=g1_orders_2(u1_struct_0(esk8_0),u1_orders_2(esk8_0)))&esk9_0=esk10_0)&v5_orders_3(esk9_0,esk5_0,esk6_0))&~v5_orders_3(esk10_0,esk7_0,esk8_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).
% 0.18/0.46  cnf(c_0_11, plain, (u1_orders_2(X1)=X2|g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))!=g1_orders_2(X3,X2)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.18/0.46  cnf(c_0_12, negated_conjecture, (g1_orders_2(u1_struct_0(esk6_0),u1_orders_2(esk6_0))=g1_orders_2(u1_struct_0(esk8_0),u1_orders_2(esk8_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.46  cnf(c_0_13, negated_conjecture, (l1_orders_2(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.46  cnf(c_0_14, negated_conjecture, (u1_orders_2(esk6_0)=X1|g1_orders_2(u1_struct_0(esk8_0),u1_orders_2(esk8_0))!=g1_orders_2(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13])])).
% 0.18/0.46  cnf(c_0_15, negated_conjecture, (g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0))=g1_orders_2(u1_struct_0(esk7_0),u1_orders_2(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.46  cnf(c_0_16, negated_conjecture, (l1_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.46  cnf(c_0_17, negated_conjecture, (u1_orders_2(esk6_0)=u1_orders_2(esk8_0)), inference(er,[status(thm)],[c_0_14])).
% 0.18/0.46  cnf(c_0_18, negated_conjecture, (u1_orders_2(esk5_0)=X1|g1_orders_2(u1_struct_0(esk7_0),u1_orders_2(esk7_0))!=g1_orders_2(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_15]), c_0_16])])).
% 0.18/0.46  cnf(c_0_19, plain, (X1=X2|g1_orders_2(X1,X3)!=g1_orders_2(X2,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.18/0.46  cnf(c_0_20, negated_conjecture, (m1_subset_1(u1_orders_2(esk8_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk6_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_17]), c_0_13])])).
% 0.18/0.46  cnf(c_0_21, negated_conjecture, (g1_orders_2(u1_struct_0(esk6_0),u1_orders_2(esk8_0))=g1_orders_2(u1_struct_0(esk8_0),u1_orders_2(esk8_0))), inference(rw,[status(thm)],[c_0_12, c_0_17])).
% 0.18/0.46  cnf(c_0_22, negated_conjecture, (u1_orders_2(esk5_0)=u1_orders_2(esk7_0)), inference(er,[status(thm)],[c_0_18])).
% 0.18/0.46  fof(c_0_23, plain, ![X14, X15, X16, X17, X18, X19, X20]:((~v5_orders_3(X16,X14,X15)|(~m1_subset_1(X17,u1_struct_0(X14))|(~m1_subset_1(X18,u1_struct_0(X14))|(~r1_orders_2(X14,X17,X18)|(~m1_subset_1(X19,u1_struct_0(X15))|(~m1_subset_1(X20,u1_struct_0(X15))|(X19!=k1_funct_1(X16,X17)|X20!=k1_funct_1(X16,X18)|r1_orders_2(X15,X19,X20)))))))|(~v1_funct_1(X16)|~v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15)))))|~l1_orders_2(X15)|~l1_orders_2(X14))&((m1_subset_1(esk1_3(X14,X15,X16),u1_struct_0(X14))|v5_orders_3(X16,X14,X15)|(~v1_funct_1(X16)|~v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15)))))|~l1_orders_2(X15)|~l1_orders_2(X14))&((m1_subset_1(esk2_3(X14,X15,X16),u1_struct_0(X14))|v5_orders_3(X16,X14,X15)|(~v1_funct_1(X16)|~v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15)))))|~l1_orders_2(X15)|~l1_orders_2(X14))&((r1_orders_2(X14,esk1_3(X14,X15,X16),esk2_3(X14,X15,X16))|v5_orders_3(X16,X14,X15)|(~v1_funct_1(X16)|~v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15)))))|~l1_orders_2(X15)|~l1_orders_2(X14))&((m1_subset_1(esk3_3(X14,X15,X16),u1_struct_0(X15))|v5_orders_3(X16,X14,X15)|(~v1_funct_1(X16)|~v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15)))))|~l1_orders_2(X15)|~l1_orders_2(X14))&((m1_subset_1(esk4_3(X14,X15,X16),u1_struct_0(X15))|v5_orders_3(X16,X14,X15)|(~v1_funct_1(X16)|~v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15)))))|~l1_orders_2(X15)|~l1_orders_2(X14))&(((esk3_3(X14,X15,X16)=k1_funct_1(X16,esk1_3(X14,X15,X16))|v5_orders_3(X16,X14,X15)|(~v1_funct_1(X16)|~v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15)))))|~l1_orders_2(X15)|~l1_orders_2(X14))&(esk4_3(X14,X15,X16)=k1_funct_1(X16,esk2_3(X14,X15,X16))|v5_orders_3(X16,X14,X15)|(~v1_funct_1(X16)|~v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15)))))|~l1_orders_2(X15)|~l1_orders_2(X14)))&(~r1_orders_2(X15,esk3_3(X14,X15,X16),esk4_3(X14,X15,X16))|v5_orders_3(X16,X14,X15)|(~v1_funct_1(X16)|~v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15)))))|~l1_orders_2(X15)|~l1_orders_2(X14))))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_orders_3])])])])])).
% 0.18/0.46  cnf(c_0_24, negated_conjecture, (u1_struct_0(esk6_0)=X1|g1_orders_2(u1_struct_0(esk8_0),u1_orders_2(esk8_0))!=g1_orders_2(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])).
% 0.18/0.46  cnf(c_0_25, negated_conjecture, (m1_subset_1(u1_orders_2(esk7_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_22]), c_0_16])])).
% 0.18/0.46  cnf(c_0_26, negated_conjecture, (g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk7_0))=g1_orders_2(u1_struct_0(esk7_0),u1_orders_2(esk7_0))), inference(rw,[status(thm)],[c_0_15, c_0_22])).
% 0.18/0.46  cnf(c_0_27, plain, (r1_orders_2(X3,X6,X7)|~v5_orders_3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X5,u1_struct_0(X2))|~r1_orders_2(X2,X4,X5)|~m1_subset_1(X6,u1_struct_0(X3))|~m1_subset_1(X7,u1_struct_0(X3))|X6!=k1_funct_1(X1,X4)|X7!=k1_funct_1(X1,X5)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~l1_orders_2(X3)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.46  cnf(c_0_28, negated_conjecture, (u1_struct_0(esk6_0)=u1_struct_0(esk8_0)), inference(er,[status(thm)],[c_0_24])).
% 0.18/0.46  cnf(c_0_29, negated_conjecture, (u1_struct_0(esk5_0)=X1|g1_orders_2(u1_struct_0(esk7_0),u1_orders_2(esk7_0))!=g1_orders_2(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_25]), c_0_26])).
% 0.18/0.46  cnf(c_0_30, negated_conjecture, (r1_orders_2(esk6_0,X1,X2)|X2!=k1_funct_1(X3,X4)|X1!=k1_funct_1(X3,X5)|~r1_orders_2(X6,X5,X4)|~v5_orders_3(X3,X6,esk6_0)|~v1_funct_2(X3,u1_struct_0(X6),u1_struct_0(esk8_0))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(esk8_0))))|~m1_subset_1(X2,u1_struct_0(esk8_0))|~m1_subset_1(X1,u1_struct_0(esk8_0))|~m1_subset_1(X4,u1_struct_0(X6))|~m1_subset_1(X5,u1_struct_0(X6))|~l1_orders_2(X6)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_13])])).
% 0.18/0.46  cnf(c_0_31, negated_conjecture, (u1_struct_0(esk5_0)=u1_struct_0(esk7_0)), inference(er,[status(thm)],[c_0_29])).
% 0.18/0.46  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0))))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.46  cnf(c_0_33, negated_conjecture, (esk9_0=esk10_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.46  cnf(c_0_34, negated_conjecture, (v1_funct_2(esk10_0,u1_struct_0(esk7_0),u1_struct_0(esk8_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.46  cnf(c_0_35, negated_conjecture, (~v5_orders_3(esk10_0,esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.46  fof(c_0_36, plain, ![X25, X26, X27, X28, X29, X30]:(~l1_orders_2(X25)|(~l1_orders_2(X26)|(~m1_subset_1(X27,u1_struct_0(X25))|(~m1_subset_1(X28,u1_struct_0(X25))|(~m1_subset_1(X29,u1_struct_0(X26))|(~m1_subset_1(X30,u1_struct_0(X26))|(X27!=X29|X28!=X30|g1_orders_2(u1_struct_0(X25),u1_orders_2(X25))!=g1_orders_2(u1_struct_0(X26),u1_orders_2(X26))|~r1_orders_2(X25,X27,X28)|r1_orders_2(X26,X29,X30)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l20_yellow_6])])])).
% 0.18/0.46  cnf(c_0_37, negated_conjecture, (r1_orders_2(esk6_0,X1,X2)|X2!=k1_funct_1(X3,X4)|X1!=k1_funct_1(X3,X5)|~r1_orders_2(esk5_0,X5,X4)|~v5_orders_3(X3,esk5_0,esk6_0)|~v1_funct_2(X3,u1_struct_0(esk7_0),u1_struct_0(esk8_0))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0))))|~m1_subset_1(X2,u1_struct_0(esk8_0))|~m1_subset_1(X1,u1_struct_0(esk8_0))|~m1_subset_1(X4,u1_struct_0(esk7_0))|~m1_subset_1(X5,u1_struct_0(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_16])])).
% 0.18/0.46  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk8_0))))), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 0.18/0.46  cnf(c_0_39, negated_conjecture, (v5_orders_3(esk9_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.46  cnf(c_0_40, negated_conjecture, (v1_funct_2(esk9_0,u1_struct_0(esk7_0),u1_struct_0(esk8_0))), inference(rw,[status(thm)],[c_0_34, c_0_33])).
% 0.18/0.46  cnf(c_0_41, negated_conjecture, (v1_funct_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.46  cnf(c_0_42, plain, (m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X2))|v5_orders_3(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_orders_2(X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.46  cnf(c_0_43, negated_conjecture, (l1_orders_2(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.46  cnf(c_0_44, negated_conjecture, (l1_orders_2(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.46  cnf(c_0_45, negated_conjecture, (~v5_orders_3(esk9_0,esk7_0,esk8_0)), inference(rw,[status(thm)],[c_0_35, c_0_33])).
% 0.18/0.46  cnf(c_0_46, plain, (r1_orders_2(X2,X5,X6)|~l1_orders_2(X1)|~l1_orders_2(X2)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X5,u1_struct_0(X2))|~m1_subset_1(X6,u1_struct_0(X2))|X3!=X5|X4!=X6|g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))!=g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))|~r1_orders_2(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.18/0.46  cnf(c_0_47, negated_conjecture, (r1_orders_2(esk6_0,X1,X2)|X2!=k1_funct_1(esk9_0,X3)|X1!=k1_funct_1(esk9_0,X4)|~r1_orders_2(esk5_0,X4,X3)|~m1_subset_1(X2,u1_struct_0(esk8_0))|~m1_subset_1(X1,u1_struct_0(esk8_0))|~m1_subset_1(X3,u1_struct_0(esk7_0))|~m1_subset_1(X4,u1_struct_0(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_40]), c_0_41])])).
% 0.18/0.46  cnf(c_0_48, negated_conjecture, (m1_subset_1(esk4_3(esk7_0,esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_38]), c_0_40]), c_0_41]), c_0_43]), c_0_44])]), c_0_45])).
% 0.18/0.46  cnf(c_0_49, plain, (m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X2))|v5_orders_3(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_orders_2(X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.46  cnf(c_0_50, plain, (r1_orders_2(X1,X2,X3)|g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))!=g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))|~r1_orders_2(X4,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X4))|~m1_subset_1(X2,u1_struct_0(X4))|~l1_orders_2(X1)|~l1_orders_2(X4)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_46])])).
% 0.18/0.46  cnf(c_0_51, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))|v5_orders_3(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_orders_2(X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.46  cnf(c_0_52, negated_conjecture, (r1_orders_2(esk6_0,X1,esk4_3(esk7_0,esk8_0,esk9_0))|esk4_3(esk7_0,esk8_0,esk9_0)!=k1_funct_1(esk9_0,X2)|X1!=k1_funct_1(esk9_0,X3)|~r1_orders_2(esk5_0,X3,X2)|~m1_subset_1(X1,u1_struct_0(esk8_0))|~m1_subset_1(X2,u1_struct_0(esk7_0))|~m1_subset_1(X3,u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.18/0.46  cnf(c_0_53, negated_conjecture, (m1_subset_1(esk3_3(esk7_0,esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_38]), c_0_40]), c_0_41]), c_0_43]), c_0_44])]), c_0_45])).
% 0.18/0.46  cnf(c_0_54, plain, (esk4_3(X1,X2,X3)=k1_funct_1(X3,esk2_3(X1,X2,X3))|v5_orders_3(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_orders_2(X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.46  cnf(c_0_55, negated_conjecture, (r1_orders_2(esk5_0,X1,X2)|g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))!=g1_orders_2(u1_struct_0(esk7_0),u1_orders_2(esk7_0))|~r1_orders_2(X3,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk7_0))|~m1_subset_1(X1,u1_struct_0(esk7_0))|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~l1_orders_2(X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_31]), c_0_22]), c_0_16])])).
% 0.18/0.46  cnf(c_0_56, negated_conjecture, (m1_subset_1(esk2_3(esk7_0,esk8_0,esk9_0),u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_38]), c_0_40]), c_0_41]), c_0_43]), c_0_44])]), c_0_45])).
% 0.18/0.46  cnf(c_0_57, negated_conjecture, (r1_orders_2(esk6_0,esk3_3(esk7_0,esk8_0,esk9_0),esk4_3(esk7_0,esk8_0,esk9_0))|esk4_3(esk7_0,esk8_0,esk9_0)!=k1_funct_1(esk9_0,X1)|esk3_3(esk7_0,esk8_0,esk9_0)!=k1_funct_1(esk9_0,X2)|~r1_orders_2(esk5_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk7_0))|~m1_subset_1(X2,u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.18/0.46  cnf(c_0_58, negated_conjecture, (k1_funct_1(esk9_0,esk2_3(esk7_0,esk8_0,esk9_0))=esk4_3(esk7_0,esk8_0,esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_38]), c_0_40]), c_0_41]), c_0_43]), c_0_44])]), c_0_45])).
% 0.18/0.46  cnf(c_0_59, negated_conjecture, (r1_orders_2(esk5_0,X1,esk2_3(esk7_0,esk8_0,esk9_0))|g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))!=g1_orders_2(u1_struct_0(esk7_0),u1_orders_2(esk7_0))|~r1_orders_2(X2,X1,esk2_3(esk7_0,esk8_0,esk9_0))|~m1_subset_1(esk2_3(esk7_0,esk8_0,esk9_0),u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(esk7_0))|~m1_subset_1(X1,u1_struct_0(X2))|~l1_orders_2(X2)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.18/0.46  cnf(c_0_60, negated_conjecture, (r1_orders_2(esk6_0,esk3_3(esk7_0,esk8_0,esk9_0),esk4_3(esk7_0,esk8_0,esk9_0))|esk3_3(esk7_0,esk8_0,esk9_0)!=k1_funct_1(esk9_0,X1)|~r1_orders_2(esk5_0,X1,esk2_3(esk7_0,esk8_0,esk9_0))|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_56]), c_0_58])])).
% 0.18/0.46  cnf(c_0_61, negated_conjecture, (r1_orders_2(esk5_0,X1,esk2_3(esk7_0,esk8_0,esk9_0))|~r1_orders_2(esk7_0,X1,esk2_3(esk7_0,esk8_0,esk9_0))|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_56]), c_0_44])])).
% 0.18/0.46  cnf(c_0_62, plain, (r1_orders_2(X1,esk1_3(X1,X2,X3),esk2_3(X1,X2,X3))|v5_orders_3(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_orders_2(X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.46  cnf(c_0_63, plain, (esk3_3(X1,X2,X3)=k1_funct_1(X3,esk1_3(X1,X2,X3))|v5_orders_3(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_orders_2(X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.46  cnf(c_0_64, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|v5_orders_3(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_orders_2(X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.46  cnf(c_0_65, negated_conjecture, (r1_orders_2(esk8_0,X1,esk4_3(esk7_0,esk8_0,esk9_0))|g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))!=g1_orders_2(u1_struct_0(esk8_0),u1_orders_2(esk8_0))|~r1_orders_2(X2,X1,esk4_3(esk7_0,esk8_0,esk9_0))|~m1_subset_1(esk4_3(esk7_0,esk8_0,esk9_0),u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(esk8_0))|~m1_subset_1(X1,u1_struct_0(X2))|~l1_orders_2(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_48]), c_0_43])])).
% 0.18/0.46  cnf(c_0_66, negated_conjecture, (r1_orders_2(esk6_0,esk3_3(esk7_0,esk8_0,esk9_0),esk4_3(esk7_0,esk8_0,esk9_0))|esk3_3(esk7_0,esk8_0,esk9_0)!=k1_funct_1(esk9_0,X1)|~r1_orders_2(esk7_0,X1,esk2_3(esk7_0,esk8_0,esk9_0))|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.18/0.46  cnf(c_0_67, negated_conjecture, (r1_orders_2(esk7_0,esk1_3(esk7_0,esk8_0,esk9_0),esk2_3(esk7_0,esk8_0,esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_38]), c_0_40]), c_0_41]), c_0_43]), c_0_44])]), c_0_45])).
% 0.18/0.46  cnf(c_0_68, negated_conjecture, (k1_funct_1(esk9_0,esk1_3(esk7_0,esk8_0,esk9_0))=esk3_3(esk7_0,esk8_0,esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_38]), c_0_40]), c_0_41]), c_0_43]), c_0_44])]), c_0_45])).
% 0.18/0.46  cnf(c_0_69, negated_conjecture, (m1_subset_1(esk1_3(esk7_0,esk8_0,esk9_0),u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_38]), c_0_40]), c_0_41]), c_0_43]), c_0_44])]), c_0_45])).
% 0.18/0.46  cnf(c_0_70, negated_conjecture, (r1_orders_2(esk8_0,X1,esk4_3(esk7_0,esk8_0,esk9_0))|~r1_orders_2(esk6_0,X1,esk4_3(esk7_0,esk8_0,esk9_0))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_28]), c_0_17]), c_0_48]), c_0_13])])).
% 0.18/0.46  cnf(c_0_71, negated_conjecture, (r1_orders_2(esk6_0,esk3_3(esk7_0,esk8_0,esk9_0),esk4_3(esk7_0,esk8_0,esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68]), c_0_69])])).
% 0.18/0.46  cnf(c_0_72, plain, (v5_orders_3(X3,X2,X1)|~r1_orders_2(X1,esk3_3(X2,X1,X3),esk4_3(X2,X1,X3))|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~l1_orders_2(X1)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.46  cnf(c_0_73, negated_conjecture, (r1_orders_2(esk8_0,esk3_3(esk7_0,esk8_0,esk9_0),esk4_3(esk7_0,esk8_0,esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_53])])).
% 0.18/0.46  cnf(c_0_74, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_40]), c_0_41]), c_0_38]), c_0_44]), c_0_43])]), c_0_45]), ['proof']).
% 0.18/0.46  # SZS output end CNFRefutation
% 0.18/0.46  # Proof object total steps             : 75
% 0.18/0.46  # Proof object clause steps            : 64
% 0.18/0.46  # Proof object formula steps           : 11
% 0.18/0.46  # Proof object conjectures             : 52
% 0.18/0.46  # Proof object clause conjectures      : 49
% 0.18/0.46  # Proof object formula conjectures     : 3
% 0.18/0.46  # Proof object initial clauses used    : 25
% 0.18/0.46  # Proof object initial formulas used   : 5
% 0.18/0.46  # Proof object generating inferences   : 33
% 0.18/0.46  # Proof object simplifying inferences  : 92
% 0.18/0.46  # Training examples: 0 positive, 0 negative
% 0.18/0.46  # Parsed axioms                        : 6
% 0.18/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.46  # Initial clauses                      : 31
% 0.18/0.46  # Removed in clause preprocessing      : 0
% 0.18/0.46  # Initial clauses in saturation        : 31
% 0.18/0.46  # Processed clauses                    : 894
% 0.18/0.46  # ...of these trivial                  : 3
% 0.18/0.46  # ...subsumed                          : 438
% 0.18/0.46  # ...remaining for further processing  : 453
% 0.18/0.46  # Other redundant clauses eliminated   : 2
% 0.18/0.46  # Clauses deleted for lack of memory   : 0
% 0.18/0.46  # Backward-subsumed                    : 19
% 0.18/0.46  # Backward-rewritten                   : 25
% 0.18/0.46  # Generated clauses                    : 1721
% 0.18/0.46  # ...of the previous two non-trivial   : 1697
% 0.18/0.46  # Contextual simplify-reflections      : 5
% 0.18/0.46  # Paramodulations                      : 1694
% 0.18/0.46  # Factorizations                       : 0
% 0.18/0.46  # Equation resolutions                 : 28
% 0.18/0.46  # Propositional unsat checks           : 0
% 0.18/0.46  #    Propositional check models        : 0
% 0.18/0.46  #    Propositional check unsatisfiable : 0
% 0.18/0.46  #    Propositional clauses             : 0
% 0.18/0.46  #    Propositional clauses after purity: 0
% 0.18/0.46  #    Propositional unsat core size     : 0
% 0.18/0.46  #    Propositional preprocessing time  : 0.000
% 0.18/0.46  #    Propositional encoding time       : 0.000
% 0.18/0.46  #    Propositional solver time         : 0.000
% 0.18/0.46  #    Success case prop preproc time    : 0.000
% 0.18/0.46  #    Success case prop encoding time   : 0.000
% 0.18/0.46  #    Success case prop solver time     : 0.000
% 0.18/0.46  # Current number of processed clauses  : 378
% 0.18/0.46  #    Positive orientable unit clauses  : 24
% 0.18/0.46  #    Positive unorientable unit clauses: 0
% 0.18/0.46  #    Negative unit clauses             : 3
% 0.18/0.46  #    Non-unit-clauses                  : 351
% 0.18/0.46  # Current number of unprocessed clauses: 832
% 0.18/0.46  # ...number of literals in the above   : 5658
% 0.18/0.46  # Current number of archived formulas  : 0
% 0.18/0.46  # Current number of archived clauses   : 74
% 0.18/0.46  # Clause-clause subsumption calls (NU) : 11820
% 0.18/0.46  # Rec. Clause-clause subsumption calls : 2174
% 0.18/0.46  # Non-unit clause-clause subsumptions  : 458
% 0.18/0.46  # Unit Clause-clause subsumption calls : 14
% 0.18/0.46  # Rewrite failures with RHS unbound    : 0
% 0.18/0.46  # BW rewrite match attempts            : 8
% 0.18/0.46  # BW rewrite match successes           : 5
% 0.18/0.46  # Condensation attempts                : 0
% 0.18/0.46  # Condensation successes               : 0
% 0.18/0.46  # Termbank termtop insertions          : 66207
% 0.18/0.46  
% 0.18/0.46  # -------------------------------------------------
% 0.18/0.46  # User time                : 0.117 s
% 0.18/0.46  # System time              : 0.007 s
% 0.18/0.46  # Total time               : 0.123 s
% 0.18/0.46  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
