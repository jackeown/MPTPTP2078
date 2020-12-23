%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1685+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:35 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  176 (1605223 expanded)
%              Number of clauses        :  153 (619393 expanded)
%              Number of leaves         :   11 (372117 expanded)
%              Depth                    :   47
%              Number of atoms          :  700 (20979848 expanded)
%              Number of equality atoms :  124 (3040399 expanded)
%              Maximal formula depth    :   26 (   4 average)
%              Maximal clause size      :   43 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t65_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_orders_2(X2) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & l1_orders_2(X3) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & l1_orders_2(X4) )
                 => ( ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                      & g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(X4),u1_orders_2(X4)) )
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                       => ! [X6] :
                            ( ( v1_funct_1(X6)
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X4))
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4)))) )
                           => ( r1_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X3),u1_struct_0(X4),X5,X6)
                             => ! [X7] :
                                  ( m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))
                                 => ! [X8] :
                                      ( m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X3)))
                                     => ( X7 = X8
                                       => ( ( r4_waybel_0(X1,X2,X5,X7)
                                           => r4_waybel_0(X3,X4,X6,X8) )
                                          & ( r3_waybel_0(X1,X2,X5,X7)
                                           => r3_waybel_0(X3,X4,X6,X8) ) ) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_waybel_0)).

fof(free_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ! [X3,X4] :
          ( g1_orders_2(X1,X2) = g1_orders_2(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(d31_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_orders_2(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r4_waybel_0(X1,X2,X3,X4)
                  <=> ( r1_yellow_0(X1,X4)
                     => ( r1_yellow_0(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4))
                        & k1_yellow_0(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,k1_yellow_0(X1,X4)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d31_waybel_0)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(d30_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_orders_2(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r3_waybel_0(X1,X2,X3,X4)
                  <=> ( r2_yellow_0(X1,X4)
                     => ( r2_yellow_0(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4))
                        & k2_yellow_0(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,k2_yellow_0(X1,X4)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d30_waybel_0)).

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

fof(t26_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
           => ! [X3] :
                ( r1_yellow_0(X1,X3)
               => k1_yellow_0(X1,X3) = k1_yellow_0(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow_0)).

fof(redefinition_r1_funct_2,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X4)
        & v1_funct_1(X5)
        & v1_funct_2(X5,X1,X2)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & v1_funct_2(X6,X3,X4)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( r1_funct_2(X1,X2,X3,X4,X5,X6)
      <=> X5 = X6 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(t27_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
           => ! [X3] :
                ( r2_yellow_0(X1,X3)
               => k2_yellow_0(X1,X3) = k2_yellow_0(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_0)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & l1_orders_2(X2) )
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & l1_orders_2(X3) )
               => ! [X4] :
                    ( ( ~ v2_struct_0(X4)
                      & l1_orders_2(X4) )
                   => ( ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                        & g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(X4),u1_orders_2(X4)) )
                     => ! [X5] :
                          ( ( v1_funct_1(X5)
                            & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                         => ! [X6] :
                              ( ( v1_funct_1(X6)
                                & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X4))
                                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4)))) )
                             => ( r1_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X3),u1_struct_0(X4),X5,X6)
                               => ! [X7] :
                                    ( m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))
                                   => ! [X8] :
                                        ( m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X3)))
                                       => ( X7 = X8
                                         => ( ( r4_waybel_0(X1,X2,X5,X7)
                                             => r4_waybel_0(X3,X4,X6,X8) )
                                            & ( r3_waybel_0(X1,X2,X5,X7)
                                             => r3_waybel_0(X3,X4,X6,X8) ) ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t65_waybel_0])).

fof(c_0_12,plain,(
    ! [X24,X25,X26,X27] :
      ( ( X24 = X26
        | g1_orders_2(X24,X25) != g1_orders_2(X26,X27)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X24,X24))) )
      & ( X25 = X27
        | g1_orders_2(X24,X25) != g1_orders_2(X26,X27)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X24,X24))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

fof(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & l1_orders_2(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & l1_orders_2(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & l1_orders_2(esk3_0)
    & ~ v2_struct_0(esk4_0)
    & l1_orders_2(esk4_0)
    & g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) = g1_orders_2(u1_struct_0(esk3_0),u1_orders_2(esk3_0))
    & g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) = g1_orders_2(u1_struct_0(esk4_0),u1_orders_2(esk4_0))
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))
    & r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & esk7_0 = esk8_0
    & ( r3_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0)
      | r4_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0) )
    & ( ~ r3_waybel_0(esk3_0,esk4_0,esk6_0,esk8_0)
      | r4_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0) )
    & ( r3_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0)
      | ~ r4_waybel_0(esk3_0,esk4_0,esk6_0,esk8_0) )
    & ( ~ r3_waybel_0(esk3_0,esk4_0,esk6_0,esk8_0)
      | ~ r4_waybel_0(esk3_0,esk4_0,esk6_0,esk8_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])).

cnf(c_0_14,plain,
    ( X1 = X2
    | g1_orders_2(X3,X1) != g1_orders_2(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) = g1_orders_2(u1_struct_0(esk3_0),u1_orders_2(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_16,plain,(
    ! [X13,X14,X15,X16] :
      ( ( r1_yellow_0(X14,k7_relset_1(u1_struct_0(X13),u1_struct_0(X14),X15,X16))
        | ~ r1_yellow_0(X13,X16)
        | ~ r4_waybel_0(X13,X14,X15,X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X14))))
        | v2_struct_0(X14)
        | ~ l1_orders_2(X14)
        | v2_struct_0(X13)
        | ~ l1_orders_2(X13) )
      & ( k1_yellow_0(X14,k7_relset_1(u1_struct_0(X13),u1_struct_0(X14),X15,X16)) = k3_funct_2(u1_struct_0(X13),u1_struct_0(X14),X15,k1_yellow_0(X13,X16))
        | ~ r1_yellow_0(X13,X16)
        | ~ r4_waybel_0(X13,X14,X15,X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X14))))
        | v2_struct_0(X14)
        | ~ l1_orders_2(X14)
        | v2_struct_0(X13)
        | ~ l1_orders_2(X13) )
      & ( r1_yellow_0(X13,X16)
        | r4_waybel_0(X13,X14,X15,X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X14))))
        | v2_struct_0(X14)
        | ~ l1_orders_2(X14)
        | v2_struct_0(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_yellow_0(X14,k7_relset_1(u1_struct_0(X13),u1_struct_0(X14),X15,X16))
        | k1_yellow_0(X14,k7_relset_1(u1_struct_0(X13),u1_struct_0(X14),X15,X16)) != k3_funct_2(u1_struct_0(X13),u1_struct_0(X14),X15,k1_yellow_0(X13,X16))
        | r4_waybel_0(X13,X14,X15,X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X14))))
        | v2_struct_0(X14)
        | ~ l1_orders_2(X14)
        | v2_struct_0(X13)
        | ~ l1_orders_2(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d31_waybel_0])])])])])).

cnf(c_0_17,negated_conjecture,
    ( u1_orders_2(esk3_0) = X1
    | g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) != g1_orders_2(X2,X1)
    | ~ m1_subset_1(u1_orders_2(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_18,plain,(
    ! [X22] :
      ( ~ l1_orders_2(X22)
      | m1_subset_1(u1_orders_2(X22),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X22)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

cnf(c_0_19,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) = g1_orders_2(u1_struct_0(esk4_0),u1_orders_2(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( r1_yellow_0(X1,X2)
    | r4_waybel_0(X1,X3,X4,X2)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | ~ l1_orders_2(X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,negated_conjecture,
    ( esk7_0 = esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_30,plain,(
    ! [X9,X10,X11,X12] :
      ( ( r2_yellow_0(X10,k7_relset_1(u1_struct_0(X9),u1_struct_0(X10),X11,X12))
        | ~ r2_yellow_0(X9,X12)
        | ~ r3_waybel_0(X9,X10,X11,X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X10))))
        | v2_struct_0(X10)
        | ~ l1_orders_2(X10)
        | v2_struct_0(X9)
        | ~ l1_orders_2(X9) )
      & ( k2_yellow_0(X10,k7_relset_1(u1_struct_0(X9),u1_struct_0(X10),X11,X12)) = k3_funct_2(u1_struct_0(X9),u1_struct_0(X10),X11,k2_yellow_0(X9,X12))
        | ~ r2_yellow_0(X9,X12)
        | ~ r3_waybel_0(X9,X10,X11,X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X10))))
        | v2_struct_0(X10)
        | ~ l1_orders_2(X10)
        | v2_struct_0(X9)
        | ~ l1_orders_2(X9) )
      & ( r2_yellow_0(X9,X12)
        | r3_waybel_0(X9,X10,X11,X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X10))))
        | v2_struct_0(X10)
        | ~ l1_orders_2(X10)
        | v2_struct_0(X9)
        | ~ l1_orders_2(X9) )
      & ( ~ r2_yellow_0(X10,k7_relset_1(u1_struct_0(X9),u1_struct_0(X10),X11,X12))
        | k2_yellow_0(X10,k7_relset_1(u1_struct_0(X9),u1_struct_0(X10),X11,X12)) != k3_funct_2(u1_struct_0(X9),u1_struct_0(X10),X11,k2_yellow_0(X9,X12))
        | r3_waybel_0(X9,X10,X11,X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X10))))
        | v2_struct_0(X10)
        | ~ l1_orders_2(X10)
        | v2_struct_0(X9)
        | ~ l1_orders_2(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d30_waybel_0])])])])])).

cnf(c_0_31,negated_conjecture,
    ( u1_orders_2(esk3_0) = u1_orders_2(esk1_0)
    | ~ m1_subset_1(u1_orders_2(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0)))) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_32,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_33,negated_conjecture,
    ( u1_orders_2(esk4_0) = X1
    | g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) != g1_orders_2(X2,X1)
    | ~ m1_subset_1(u1_orders_2(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_14,c_0_19])).

cnf(c_0_34,negated_conjecture,
    ( ~ r3_waybel_0(esk3_0,esk4_0,esk6_0,esk8_0)
    | ~ r4_waybel_0(esk3_0,esk4_0,esk6_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_35,negated_conjecture,
    ( r1_yellow_0(esk3_0,X1)
    | r4_waybel_0(esk3_0,esk4_0,esk6_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_26]),c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_37,plain,
    ( r2_yellow_0(X1,X2)
    | r3_waybel_0(X1,X3,X4,X2)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | ~ l1_orders_2(X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( u1_orders_2(esk3_0) = u1_orders_2(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_25])])).

cnf(c_0_39,negated_conjecture,
    ( u1_orders_2(esk4_0) = u1_orders_2(esk2_0)
    | ~ m1_subset_1(u1_orders_2(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0)))) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( ~ r4_waybel_0(esk3_0,esk4_0,esk6_0,esk7_0)
    | ~ r3_waybel_0(esk3_0,esk4_0,esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_29]),c_0_29])).

cnf(c_0_41,negated_conjecture,
    ( r1_yellow_0(esk3_0,esk7_0)
    | r4_waybel_0(esk3_0,esk4_0,esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( r2_yellow_0(esk3_0,X1)
    | r3_waybel_0(esk3_0,esk4_0,esk6_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_26]),c_0_27])).

cnf(c_0_43,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_44,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk3_0),u1_orders_2(esk1_0)) = g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_15,c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(u1_orders_2(esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_38]),c_0_25])])).

cnf(c_0_46,negated_conjecture,
    ( u1_orders_2(esk4_0) = u1_orders_2(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_32]),c_0_24])])).

fof(c_0_47,plain,(
    ! [X42,X43,X44] :
      ( ( ~ r1_yellow_0(X42,X44)
        | r1_yellow_0(X43,X44)
        | g1_orders_2(u1_struct_0(X42),u1_orders_2(X42)) != g1_orders_2(u1_struct_0(X43),u1_orders_2(X43))
        | ~ l1_orders_2(X43)
        | ~ l1_orders_2(X42) )
      & ( ~ r2_yellow_0(X42,X44)
        | r2_yellow_0(X43,X44)
        | g1_orders_2(u1_struct_0(X42),u1_orders_2(X42)) != g1_orders_2(u1_struct_0(X43),u1_orders_2(X43))
        | ~ l1_orders_2(X43)
        | ~ l1_orders_2(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_yellow_0])])])])).

cnf(c_0_48,negated_conjecture,
    ( r1_yellow_0(esk3_0,esk7_0)
    | ~ r3_waybel_0(esk3_0,esk4_0,esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( r2_yellow_0(esk3_0,esk7_0)
    | r3_waybel_0(esk3_0,esk4_0,esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_36])).

cnf(c_0_50,negated_conjecture,
    ( u1_struct_0(esk3_0) = X1
    | g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) != g1_orders_2(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])])).

cnf(c_0_51,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk4_0),u1_orders_2(esk2_0)) = g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_19,c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(u1_orders_2(esk2_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_46]),c_0_24])])).

fof(c_0_53,plain,(
    ! [X45,X46,X47] :
      ( ~ l1_orders_2(X45)
      | ~ l1_orders_2(X46)
      | g1_orders_2(u1_struct_0(X45),u1_orders_2(X45)) != g1_orders_2(u1_struct_0(X46),u1_orders_2(X46))
      | ~ r1_yellow_0(X45,X47)
      | k1_yellow_0(X45,X47) = k1_yellow_0(X46,X47) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_yellow_0])])])).

cnf(c_0_54,negated_conjecture,
    ( r4_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0)
    | ~ r3_waybel_0(esk3_0,esk4_0,esk6_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_55,plain,
    ( r1_yellow_0(X3,X2)
    | ~ r1_yellow_0(X1,X2)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
    | ~ l1_orders_2(X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_56,negated_conjecture,
    ( r1_yellow_0(esk3_0,esk7_0)
    | r2_yellow_0(esk3_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

fof(c_0_57,plain,(
    ! [X36,X37,X38,X39,X40,X41] :
      ( ( ~ r1_funct_2(X36,X37,X38,X39,X40,X41)
        | X40 = X41
        | v1_xboole_0(X37)
        | v1_xboole_0(X39)
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,X36,X37)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,X38,X39)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( X40 != X41
        | r1_funct_2(X36,X37,X38,X39,X40,X41)
        | v1_xboole_0(X37)
        | v1_xboole_0(X39)
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,X36,X37)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,X38,X39)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).

cnf(c_0_58,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_59,negated_conjecture,
    ( u1_struct_0(esk3_0) = u1_struct_0(esk1_0) ),
    inference(er,[status(thm)],[c_0_50])).

fof(c_0_60,plain,(
    ! [X23] :
      ( v2_struct_0(X23)
      | ~ l1_struct_0(X23)
      | ~ v1_xboole_0(u1_struct_0(X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_61,negated_conjecture,
    ( u1_struct_0(esk4_0) = X1
    | g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) != g1_orders_2(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_51]),c_0_52])])).

cnf(c_0_62,plain,
    ( k1_yellow_0(X1,X3) = k1_yellow_0(X2,X3)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
    | ~ r1_yellow_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_63,negated_conjecture,
    ( r4_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0)
    | ~ r3_waybel_0(esk3_0,esk4_0,esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_54,c_0_29])).

cnf(c_0_64,negated_conjecture,
    ( r1_yellow_0(X1,esk7_0)
    | r2_yellow_0(esk3_0,esk7_0)
    | g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_38]),c_0_44]),c_0_25])])).

cnf(c_0_65,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_66,plain,
    ( X5 = X6
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | ~ r1_funct_2(X1,X2,X3,X4,X5,X6)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X1,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,X3,X4)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_67,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk4_0),esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk4_0)))) ),
    inference(rw,[status(thm)],[c_0_22,c_0_59])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_70,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk1_0),u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_21,c_0_59])).

cnf(c_0_71,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_72,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_73,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_74,negated_conjecture,
    ( u1_struct_0(esk4_0) = u1_struct_0(esk2_0) ),
    inference(er,[status(thm)],[c_0_61])).

fof(c_0_75,plain,(
    ! [X21] :
      ( ~ l1_orders_2(X21)
      | l1_struct_0(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_76,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_0) = k1_yellow_0(X1,esk7_0)
    | r2_yellow_0(esk3_0,esk7_0)
    | g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_56]),c_0_38]),c_0_44]),c_0_25])])).

cnf(c_0_77,plain,
    ( r1_yellow_0(X1,k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,X4))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_yellow_0(X2,X4)
    | ~ r4_waybel_0(X2,X1,X3,X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_78,negated_conjecture,
    ( r4_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0)
    | r2_yellow_0(esk3_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_49])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_80,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_81,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_82,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_83,negated_conjecture,
    ( r1_yellow_0(esk1_0,esk7_0)
    | r2_yellow_0(esk3_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_64]),c_0_65])])).

cnf(c_0_84,negated_conjecture,
    ( esk6_0 = esk5_0
    | v1_xboole_0(u1_struct_0(esk2_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68]),c_0_69]),c_0_70]),c_0_71]),c_0_23]),c_0_72])])).

cnf(c_0_85,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk2_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_26])).

cnf(c_0_86,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_87,plain,
    ( r4_waybel_0(X2,X1,X3,X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_yellow_0(X1,k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,X4))
    | k1_yellow_0(X1,k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,X4)) != k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k1_yellow_0(X2,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_88,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_0) = k1_yellow_0(esk1_0,esk7_0)
    | r2_yellow_0(esk3_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_76]),c_0_65])])).

cnf(c_0_89,negated_conjecture,
    ( r1_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0))
    | r2_yellow_0(esk3_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_69]),c_0_79]),c_0_71]),c_0_72]),c_0_65]),c_0_80])]),c_0_81]),c_0_82]),c_0_83])).

cnf(c_0_90,negated_conjecture,
    ( esk6_0 = esk5_0
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_74])])).

cnf(c_0_91,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_24])])).

cnf(c_0_92,negated_conjecture,
    ( r4_waybel_0(esk3_0,X1,X2,esk7_0)
    | r2_yellow_0(esk3_0,esk7_0)
    | v2_struct_0(X1)
    | k3_funct_2(u1_struct_0(esk1_0),u1_struct_0(X1),X2,k1_yellow_0(esk1_0,esk7_0)) != k1_yellow_0(X1,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(X1),X2,esk7_0))
    | ~ r1_yellow_0(X1,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(X1),X2,esk7_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))
    | ~ v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_59]),c_0_59]),c_0_59]),c_0_59]),c_0_59]),c_0_79]),c_0_59]),c_0_25])]),c_0_27])).

cnf(c_0_93,plain,
    ( k1_yellow_0(X1,k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,X4)) = k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k1_yellow_0(X2,X4))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_yellow_0(X2,X4)
    | ~ r4_waybel_0(X2,X1,X3,X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_94,negated_conjecture,
    ( r1_yellow_0(X1,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0))
    | r2_yellow_0(esk3_0,esk7_0)
    | g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_89]),c_0_80])])).

cnf(c_0_95,negated_conjecture,
    ( k1_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0)) = k1_yellow_0(X1,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0))
    | r2_yellow_0(esk3_0,esk7_0)
    | g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_89]),c_0_80])])).

cnf(c_0_96,negated_conjecture,
    ( esk6_0 = esk5_0 ),
    inference(sr,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_97,negated_conjecture,
    ( r4_waybel_0(esk3_0,esk4_0,X1,esk7_0)
    | r2_yellow_0(esk3_0,esk7_0)
    | k3_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),X1,k1_yellow_0(esk1_0,esk7_0)) != k1_yellow_0(esk4_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),X1,esk7_0))
    | ~ r1_yellow_0(esk4_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),X1,esk7_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(X1,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_74]),c_0_24])]),c_0_26])).

cnf(c_0_98,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,k1_yellow_0(esk1_0,esk7_0)) = k1_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0))
    | r2_yellow_0(esk3_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_78]),c_0_69]),c_0_79]),c_0_71]),c_0_72]),c_0_65]),c_0_80])]),c_0_81]),c_0_82]),c_0_83])).

cnf(c_0_99,negated_conjecture,
    ( r1_yellow_0(esk4_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0))
    | r2_yellow_0(esk3_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_46]),c_0_74]),c_0_24])])).

cnf(c_0_100,negated_conjecture,
    ( k1_yellow_0(esk4_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0)) = k1_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0))
    | r2_yellow_0(esk3_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_46]),c_0_74]),c_0_24])])).

cnf(c_0_101,negated_conjecture,
    ( r3_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0)
    | ~ r4_waybel_0(esk3_0,esk4_0,esk6_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_102,negated_conjecture,
    ( ~ r4_waybel_0(esk3_0,esk4_0,esk5_0,esk7_0)
    | ~ r3_waybel_0(esk3_0,esk4_0,esk5_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_96]),c_0_96])).

cnf(c_0_103,negated_conjecture,
    ( r4_waybel_0(esk3_0,esk4_0,esk5_0,esk7_0)
    | r2_yellow_0(esk3_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_69]),c_0_71]),c_0_72])]),c_0_99]),c_0_100])).

cnf(c_0_104,negated_conjecture,
    ( r2_yellow_0(esk3_0,esk7_0)
    | r3_waybel_0(esk3_0,esk4_0,esk5_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_49,c_0_96])).

cnf(c_0_105,negated_conjecture,
    ( r3_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0)
    | ~ r4_waybel_0(esk3_0,esk4_0,esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_101,c_0_29])).

cnf(c_0_106,plain,
    ( r2_yellow_0(X3,X2)
    | ~ r2_yellow_0(X1,X2)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
    | ~ l1_orders_2(X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_107,negated_conjecture,
    ( r2_yellow_0(esk3_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_104])).

cnf(c_0_108,plain,
    ( r2_yellow_0(X1,k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,X4))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r2_yellow_0(X2,X4)
    | ~ r3_waybel_0(X2,X1,X3,X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_109,negated_conjecture,
    ( r1_yellow_0(esk3_0,esk7_0)
    | r3_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_105,c_0_41])).

cnf(c_0_110,negated_conjecture,
    ( r2_yellow_0(X1,esk7_0)
    | g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_59]),c_0_38]),c_0_25])])).

cnf(c_0_111,negated_conjecture,
    ( r1_yellow_0(esk3_0,esk7_0)
    | r2_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0))
    | ~ r2_yellow_0(esk1_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_69]),c_0_79]),c_0_71]),c_0_72]),c_0_65]),c_0_80])]),c_0_81]),c_0_82])).

cnf(c_0_112,negated_conjecture,
    ( r2_yellow_0(esk1_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_110]),c_0_65])])).

cnf(c_0_113,negated_conjecture,
    ( r1_yellow_0(esk3_0,esk7_0)
    | r2_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_111,c_0_112])])).

cnf(c_0_114,negated_conjecture,
    ( r3_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0)
    | r4_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_115,negated_conjecture,
    ( r1_yellow_0(X1,esk7_0)
    | r2_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0))
    | g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_113]),c_0_59]),c_0_38]),c_0_25])])).

cnf(c_0_116,negated_conjecture,
    ( r1_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0))
    | r3_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0)
    | ~ r1_yellow_0(esk1_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_114]),c_0_69]),c_0_79]),c_0_71]),c_0_72]),c_0_65]),c_0_80])]),c_0_81]),c_0_82])).

cnf(c_0_117,negated_conjecture,
    ( r1_yellow_0(esk1_0,esk7_0)
    | r2_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_115]),c_0_65])])).

cnf(c_0_118,negated_conjecture,
    ( r1_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0))
    | r2_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0))
    | r3_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_116,c_0_117])).

cnf(c_0_119,negated_conjecture,
    ( r1_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0))
    | r2_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_118]),c_0_112]),c_0_69]),c_0_79]),c_0_71]),c_0_72]),c_0_65]),c_0_80])]),c_0_81]),c_0_82])).

cnf(c_0_120,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,k1_yellow_0(esk1_0,esk7_0)) = k1_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0))
    | r3_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0)
    | ~ r1_yellow_0(esk1_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_114]),c_0_69]),c_0_79]),c_0_71]),c_0_72]),c_0_65]),c_0_80])]),c_0_81]),c_0_82])).

cnf(c_0_121,negated_conjecture,
    ( r1_yellow_0(X1,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0))
    | r2_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0))
    | g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_119]),c_0_80])])).

cnf(c_0_122,negated_conjecture,
    ( k1_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0)) = k1_yellow_0(X1,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0))
    | r2_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0))
    | g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_119]),c_0_80])])).

cnf(c_0_123,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_0) = k1_yellow_0(X1,esk7_0)
    | r2_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0))
    | g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_113]),c_0_59]),c_0_38]),c_0_25])])).

cnf(c_0_124,negated_conjecture,
    ( r4_waybel_0(X1,esk4_0,X2,X3)
    | v2_struct_0(X1)
    | k3_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),X2,k1_yellow_0(X1,X3)) != k1_yellow_0(esk4_0,k7_relset_1(u1_struct_0(X1),u1_struct_0(esk2_0),X2,X3))
    | ~ r1_yellow_0(esk4_0,k7_relset_1(u1_struct_0(X1),u1_struct_0(esk2_0),X2,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X2)
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_74]),c_0_24])]),c_0_26])).

cnf(c_0_125,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,k1_yellow_0(esk1_0,esk7_0)) = k1_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0))
    | r2_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0))
    | r3_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_120,c_0_117])).

cnf(c_0_126,negated_conjecture,
    ( r1_yellow_0(esk4_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0))
    | r2_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_46]),c_0_74]),c_0_24])])).

cnf(c_0_127,negated_conjecture,
    ( k1_yellow_0(esk4_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0)) = k1_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0))
    | r2_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_46]),c_0_74]),c_0_24])])).

fof(c_0_128,plain,(
    ! [X48,X49,X50] :
      ( ~ l1_orders_2(X48)
      | ~ l1_orders_2(X49)
      | g1_orders_2(u1_struct_0(X48),u1_orders_2(X48)) != g1_orders_2(u1_struct_0(X49),u1_orders_2(X49))
      | ~ r2_yellow_0(X48,X50)
      | k2_yellow_0(X48,X50) = k2_yellow_0(X49,X50) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_yellow_0])])])).

cnf(c_0_129,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_0) = k1_yellow_0(esk1_0,esk7_0)
    | r2_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_123]),c_0_65])])).

cnf(c_0_130,negated_conjecture,
    ( r4_waybel_0(esk1_0,esk4_0,esk5_0,esk7_0)
    | r2_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0))
    | r3_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_125]),c_0_69]),c_0_79]),c_0_71]),c_0_72]),c_0_65])]),c_0_81]),c_0_126]),c_0_127])).

cnf(c_0_131,plain,
    ( k2_yellow_0(X1,X3) = k2_yellow_0(X2,X3)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
    | ~ r2_yellow_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_128])).

cnf(c_0_132,negated_conjecture,
    ( r4_waybel_0(esk3_0,esk4_0,X1,esk7_0)
    | r2_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0))
    | k3_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),X1,k1_yellow_0(esk1_0,esk7_0)) != k1_yellow_0(esk4_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),X1,esk7_0))
    | ~ r1_yellow_0(esk4_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),X1,esk7_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(X1,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_129]),c_0_59]),c_0_59]),c_0_59]),c_0_59]),c_0_59]),c_0_79]),c_0_59]),c_0_25])]),c_0_27])).

cnf(c_0_133,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,k1_yellow_0(esk1_0,esk7_0)) = k1_yellow_0(esk4_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0))
    | r2_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0))
    | r3_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_130]),c_0_74]),c_0_74]),c_0_74]),c_0_69]),c_0_79]),c_0_74]),c_0_71]),c_0_72]),c_0_65]),c_0_24])]),c_0_81]),c_0_26]),c_0_117])).

cnf(c_0_134,negated_conjecture,
    ( r3_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0)
    | ~ r4_waybel_0(esk3_0,esk4_0,esk5_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_105,c_0_96])).

cnf(c_0_135,plain,
    ( r3_waybel_0(X2,X1,X3,X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r2_yellow_0(X1,k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,X4))
    | k2_yellow_0(X1,k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,X4)) != k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k2_yellow_0(X2,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_136,negated_conjecture,
    ( k2_yellow_0(esk3_0,esk7_0) = k2_yellow_0(X1,esk7_0)
    | g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_107]),c_0_59]),c_0_38]),c_0_25])])).

cnf(c_0_137,plain,
    ( k2_yellow_0(X1,k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,X4)) = k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k2_yellow_0(X2,X4))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r2_yellow_0(X2,X4)
    | ~ r3_waybel_0(X2,X1,X3,X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_138,negated_conjecture,
    ( r2_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0))
    | r3_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_133]),c_0_69]),c_0_71]),c_0_72])]),c_0_126]),c_0_134])).

cnf(c_0_139,negated_conjecture,
    ( r3_waybel_0(X1,esk4_0,X2,X3)
    | v2_struct_0(X1)
    | k3_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),X2,k2_yellow_0(X1,X3)) != k2_yellow_0(esk4_0,k7_relset_1(u1_struct_0(X1),u1_struct_0(esk2_0),X2,X3))
    | ~ r2_yellow_0(esk4_0,k7_relset_1(u1_struct_0(X1),u1_struct_0(esk2_0),X2,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X2)
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_74]),c_0_24])]),c_0_26])).

cnf(c_0_140,negated_conjecture,
    ( k2_yellow_0(esk3_0,esk7_0) = k2_yellow_0(esk1_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_136]),c_0_65])])).

cnf(c_0_141,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,k2_yellow_0(esk1_0,esk7_0)) = k2_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0))
    | r1_yellow_0(esk3_0,esk7_0)
    | ~ r2_yellow_0(esk1_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_109]),c_0_69]),c_0_79]),c_0_71]),c_0_72]),c_0_65]),c_0_80])]),c_0_81]),c_0_82])).

cnf(c_0_142,negated_conjecture,
    ( r2_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_138]),c_0_112]),c_0_69]),c_0_79]),c_0_71]),c_0_72]),c_0_65]),c_0_80])]),c_0_81]),c_0_82])).

cnf(c_0_143,negated_conjecture,
    ( r3_waybel_0(esk3_0,esk4_0,X1,esk7_0)
    | k3_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),X1,k2_yellow_0(esk1_0,esk7_0)) != k2_yellow_0(esk4_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),X1,esk7_0))
    | ~ r2_yellow_0(esk4_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),X1,esk7_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(X1,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_140]),c_0_59]),c_0_59]),c_0_59]),c_0_59]),c_0_59]),c_0_79]),c_0_59]),c_0_25])]),c_0_27])).

cnf(c_0_144,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,k2_yellow_0(esk1_0,esk7_0)) = k2_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0))
    | r1_yellow_0(esk3_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_141,c_0_112])])).

cnf(c_0_145,negated_conjecture,
    ( r1_yellow_0(esk3_0,esk7_0)
    | ~ r3_waybel_0(esk3_0,esk4_0,esk5_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_48,c_0_96])).

cnf(c_0_146,negated_conjecture,
    ( r2_yellow_0(X1,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0))
    | g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_142]),c_0_80])])).

cnf(c_0_147,negated_conjecture,
    ( r1_yellow_0(esk3_0,esk7_0)
    | k2_yellow_0(esk4_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0)) != k2_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0))
    | ~ r2_yellow_0(esk4_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_144]),c_0_69]),c_0_71]),c_0_72])]),c_0_145])).

cnf(c_0_148,negated_conjecture,
    ( r2_yellow_0(esk4_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_146,c_0_46]),c_0_74]),c_0_24])])).

cnf(c_0_149,negated_conjecture,
    ( k2_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0)) = k2_yellow_0(X1,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0))
    | g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_142]),c_0_80])])).

cnf(c_0_150,negated_conjecture,
    ( r1_yellow_0(esk3_0,esk7_0)
    | k2_yellow_0(esk4_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0)) != k2_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_147,c_0_148])])).

cnf(c_0_151,negated_conjecture,
    ( k2_yellow_0(esk4_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0)) = k2_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149,c_0_46]),c_0_74]),c_0_24])])).

cnf(c_0_152,negated_conjecture,
    ( r1_yellow_0(esk3_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_150,c_0_151])])).

cnf(c_0_153,negated_conjecture,
    ( r1_yellow_0(X1,esk7_0)
    | g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_152]),c_0_59]),c_0_38]),c_0_25])])).

cnf(c_0_154,negated_conjecture,
    ( r1_yellow_0(esk1_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_153]),c_0_65])])).

cnf(c_0_155,negated_conjecture,
    ( r1_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0))
    | r3_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_116,c_0_154])])).

cnf(c_0_156,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,k2_yellow_0(esk1_0,esk7_0)) = k2_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0))
    | r1_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_155]),c_0_112]),c_0_69]),c_0_79]),c_0_71]),c_0_72]),c_0_65]),c_0_80])]),c_0_81]),c_0_82])).

cnf(c_0_157,negated_conjecture,
    ( r4_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0)
    | ~ r3_waybel_0(esk3_0,esk4_0,esk5_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_63,c_0_96])).

cnf(c_0_158,negated_conjecture,
    ( r1_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0))
    | r3_waybel_0(esk3_0,esk4_0,esk5_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_156]),c_0_151]),c_0_148]),c_0_69]),c_0_71]),c_0_72])])).

cnf(c_0_159,negated_conjecture,
    ( r1_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0))
    | r4_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_157,c_0_158])).

cnf(c_0_160,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_0) = k1_yellow_0(X1,esk7_0)
    | g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_152]),c_0_59]),c_0_38]),c_0_25])])).

cnf(c_0_161,negated_conjecture,
    ( r1_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_159]),c_0_154]),c_0_69]),c_0_79]),c_0_71]),c_0_72]),c_0_65]),c_0_80])]),c_0_81]),c_0_82])).

cnf(c_0_162,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_0) = k1_yellow_0(esk1_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_160]),c_0_65])])).

cnf(c_0_163,negated_conjecture,
    ( k1_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0)) = k1_yellow_0(X1,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0))
    | g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_161]),c_0_80])])).

cnf(c_0_164,negated_conjecture,
    ( r1_yellow_0(X1,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0))
    | g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_161]),c_0_80])])).

cnf(c_0_165,negated_conjecture,
    ( r4_waybel_0(esk3_0,esk4_0,X1,esk7_0)
    | k3_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),X1,k1_yellow_0(esk1_0,esk7_0)) != k1_yellow_0(esk4_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),X1,esk7_0))
    | ~ r1_yellow_0(esk4_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),X1,esk7_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(X1,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_162]),c_0_59]),c_0_59]),c_0_59]),c_0_59]),c_0_59]),c_0_79]),c_0_59]),c_0_25])]),c_0_27])).

cnf(c_0_166,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,k1_yellow_0(esk1_0,esk7_0)) = k1_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0))
    | r3_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_120,c_0_154])])).

cnf(c_0_167,negated_conjecture,
    ( k1_yellow_0(esk4_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0)) = k1_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_163,c_0_46]),c_0_74]),c_0_24])])).

cnf(c_0_168,negated_conjecture,
    ( r1_yellow_0(esk4_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_164,c_0_46]),c_0_74]),c_0_24])])).

cnf(c_0_169,negated_conjecture,
    ( r3_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_165,c_0_166]),c_0_167]),c_0_168]),c_0_69]),c_0_71]),c_0_72])]),c_0_134])).

cnf(c_0_170,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,k2_yellow_0(esk1_0,esk7_0)) = k2_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_169]),c_0_112]),c_0_69]),c_0_79]),c_0_71]),c_0_72]),c_0_65]),c_0_80])]),c_0_81]),c_0_82])).

cnf(c_0_171,negated_conjecture,
    ( r3_waybel_0(esk3_0,esk4_0,esk5_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_170]),c_0_151]),c_0_148]),c_0_69]),c_0_71]),c_0_72])])).

cnf(c_0_172,negated_conjecture,
    ( r4_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_157,c_0_171])])).

cnf(c_0_173,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,k1_yellow_0(esk1_0,esk7_0)) = k1_yellow_0(esk2_0,k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_172]),c_0_154]),c_0_69]),c_0_79]),c_0_71]),c_0_72]),c_0_65]),c_0_80])]),c_0_81]),c_0_82])).

cnf(c_0_174,negated_conjecture,
    ( ~ r4_waybel_0(esk3_0,esk4_0,esk5_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_171])])).

cnf(c_0_175,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_165,c_0_173]),c_0_167]),c_0_168]),c_0_69]),c_0_71]),c_0_72])]),c_0_174]),
    [proof]).

%------------------------------------------------------------------------------
