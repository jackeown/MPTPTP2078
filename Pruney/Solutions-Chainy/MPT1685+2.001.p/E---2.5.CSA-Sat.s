%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:29 EST 2020

% Result     : CounterSatisfiable 0.18s
% Output     : Saturation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  100 (3365 expanded)
%              Number of clauses        :   81 (1402 expanded)
%              Number of leaves         :    9 ( 779 expanded)
%              Depth                    :   13
%              Number of atoms          :  374 (36305 expanded)
%              Number of equality atoms :   77 (6199 expanded)
%              Maximal formula depth    :   26 (   5 average)
%              Maximal clause size      :   28 (   3 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_waybel_0)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

fof(t27_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
           => ! [X3] :
                ( r2_yellow_0(X1,X3)
               => k2_yellow_0(X1,X3) = k2_yellow_0(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_0)).

fof(t26_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
           => ! [X3] :
                ( r1_yellow_0(X1,X3)
               => k1_yellow_0(X1,X3) = k1_yellow_0(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_0)).

fof(c_0_9,plain,(
    ! [X12,X13,X14,X15] :
      ( ( X12 = X14
        | g1_orders_2(X12,X13) != g1_orders_2(X14,X15)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X12,X12))) )
      & ( X13 = X15
        | g1_orders_2(X12,X13) != g1_orders_2(X14,X15)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X12,X12))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

fof(c_0_10,plain,(
    ! [X11] :
      ( ~ l1_orders_2(X11)
      | m1_subset_1(u1_orders_2(X11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(X11)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

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

cnf(c_0_12,plain,
    ( X1 = X2
    | g1_orders_2(X3,X1) != g1_orders_2(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_13,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

fof(c_0_14,negated_conjecture,
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

cnf(c_0_15,plain,
    ( u1_orders_2(X1) = X2
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(X3,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13]),
    [final]).

cnf(c_0_16,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) = g1_orders_2(u1_struct_0(esk4_0),u1_orders_2(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_18,negated_conjecture,
    ( u1_orders_2(esk4_0) = X1
    | g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) != g1_orders_2(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

cnf(c_0_19,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) = g1_orders_2(u1_struct_0(esk3_0),u1_orders_2(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_21,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_22,negated_conjecture,
    ( u1_orders_2(esk4_0) = u1_orders_2(esk2_0) ),
    inference(er,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_23,negated_conjecture,
    ( u1_orders_2(esk3_0) = X1
    | g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) != g1_orders_2(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_19]),c_0_20])])).

cnf(c_0_24,plain,
    ( u1_struct_0(X1) = X2
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_13]),
    [final]).

cnf(c_0_25,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk4_0),u1_orders_2(esk2_0)) = g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_16,c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( u1_orders_2(esk3_0) = u1_orders_2(esk1_0) ),
    inference(er,[status(thm)],[c_0_23]),
    [final]).

cnf(c_0_27,negated_conjecture,
    ( u1_struct_0(esk4_0) = X1
    | g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) != g1_orders_2(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_22]),c_0_25]),c_0_17])])).

cnf(c_0_28,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk3_0),u1_orders_2(esk1_0)) = g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_19,c_0_26])).

fof(c_0_29,plain,(
    ! [X9] :
      ( v2_struct_0(X9)
      | ~ l1_struct_0(X9)
      | ~ v1_xboole_0(u1_struct_0(X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_30,plain,(
    ! [X10] :
      ( ~ l1_orders_2(X10)
      | l1_struct_0(X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_32,negated_conjecture,
    ( u1_struct_0(esk4_0) = u1_struct_0(esk2_0) ),
    inference(er,[status(thm)],[c_0_27]),
    [final]).

cnf(c_0_33,negated_conjecture,
    ( u1_struct_0(esk3_0) = X1
    | g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) != g1_orders_2(X1,X2) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_26]),c_0_20])]),c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_35,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29]),
    [final]).

cnf(c_0_36,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30]),
    [final]).

fof(c_0_37,plain,(
    ! [X25,X26,X27,X28,X29,X30] :
      ( ( ~ r1_funct_2(X25,X26,X27,X28,X29,X30)
        | X29 = X30
        | v1_xboole_0(X26)
        | v1_xboole_0(X28)
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,X25,X26)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,X27,X28)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) )
      & ( X29 != X30
        | r1_funct_2(X25,X26,X27,X28,X29,X30)
        | v1_xboole_0(X26)
        | v1_xboole_0(X28)
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,X25,X26)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,X27,X28)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( u1_struct_0(esk3_0) = u1_struct_0(esk1_0) ),
    inference(er,[status(thm)],[c_0_33]),
    [final]).

cnf(c_0_40,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_34,c_0_32])).

cnf(c_0_41,plain,
    ( v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36]),
    [final]).

cnf(c_0_42,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_43,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_44,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_37]),
    [final]).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_40,c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_48,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_32]),c_0_17])]),c_0_42]),
    [final]).

cnf(c_0_49,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_43,c_0_32])).

cnf(c_0_50,plain,
    ( r1_funct_2(X3,X4,X5,X6,X1,X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X6)
    | X1 != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X5,X6)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(u1_orders_2(esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_26]),c_0_20])])).

cnf(c_0_52,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(u1_orders_2(esk2_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_22]),c_0_17])])).

cnf(c_0_54,negated_conjecture,
    ( r3_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0)
    | ~ r4_waybel_0(esk3_0,esk4_0,esk6_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_55,negated_conjecture,
    ( esk7_0 = esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_56,negated_conjecture,
    ( X1 = esk6_0
    | v1_xboole_0(X2)
    | ~ r1_funct_2(X3,X2,u1_struct_0(esk1_0),u1_struct_0(esk2_0),X1,esk6_0)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47])]),c_0_48])).

cnf(c_0_57,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_49,c_0_39])).

cnf(c_0_58,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_59,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_61,negated_conjecture,
    ( r4_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0)
    | ~ r3_waybel_0(esk3_0,esk4_0,esk6_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_62,negated_conjecture,
    ( ~ r3_waybel_0(esk3_0,esk4_0,esk6_0,esk8_0)
    | ~ r4_waybel_0(esk3_0,esk4_0,esk6_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_63,plain,
    ( r1_funct_2(X1,X2,X3,X4,X5,X5)
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | ~ v1_funct_2(X5,X3,X4)
    | ~ v1_funct_2(X5,X1,X2)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_50]),
    [final]).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(u1_orders_2(esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_39]),c_0_39]),
    [final]).

cnf(c_0_65,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_39]),c_0_20])]),c_0_52]),
    [final]).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(u1_orders_2(esk2_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_32]),c_0_32]),
    [final]).

cnf(c_0_67,negated_conjecture,
    ( r3_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0)
    | ~ r4_waybel_0(esk3_0,esk4_0,esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_68,negated_conjecture,
    ( esk6_0 = esk5_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58]),c_0_59]),c_0_60])]),c_0_48]),
    [final]).

cnf(c_0_69,negated_conjecture,
    ( r4_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0)
    | ~ r3_waybel_0(esk3_0,esk4_0,esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_61,c_0_55])).

cnf(c_0_70,negated_conjecture,
    ( ~ r3_waybel_0(esk3_0,esk4_0,esk6_0,esk7_0)
    | ~ r4_waybel_0(esk3_0,esk4_0,esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_55]),c_0_55])).

fof(c_0_71,plain,(
    ! [X22,X23,X24] :
      ( ~ l1_orders_2(X22)
      | ~ l1_orders_2(X23)
      | g1_orders_2(u1_struct_0(X22),u1_orders_2(X22)) != g1_orders_2(u1_struct_0(X23),u1_orders_2(X23))
      | ~ r2_yellow_0(X22,X24)
      | k2_yellow_0(X22,X24) = k2_yellow_0(X23,X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_yellow_0])])])).

fof(c_0_72,plain,(
    ! [X19,X20,X21] :
      ( ~ l1_orders_2(X19)
      | ~ l1_orders_2(X20)
      | g1_orders_2(u1_struct_0(X19),u1_orders_2(X19)) != g1_orders_2(u1_struct_0(X20),u1_orders_2(X20))
      | ~ r1_yellow_0(X19,X21)
      | k1_yellow_0(X19,X21) = k1_yellow_0(X20,X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_yellow_0])])])).

fof(c_0_73,plain,(
    ! [X16,X17,X18] :
      ( ( ~ r1_yellow_0(X16,X18)
        | r1_yellow_0(X17,X18)
        | g1_orders_2(u1_struct_0(X16),u1_orders_2(X16)) != g1_orders_2(u1_struct_0(X17),u1_orders_2(X17))
        | ~ l1_orders_2(X17)
        | ~ l1_orders_2(X16) )
      & ( ~ r2_yellow_0(X16,X18)
        | r2_yellow_0(X17,X18)
        | g1_orders_2(u1_struct_0(X16),u1_orders_2(X16)) != g1_orders_2(u1_struct_0(X17),u1_orders_2(X17))
        | ~ l1_orders_2(X17)
        | ~ l1_orders_2(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_yellow_0])])])])).

cnf(c_0_74,negated_conjecture,
    ( r1_funct_2(X1,X2,u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk5_0)
    | v1_xboole_0(X2)
    | ~ v1_funct_2(esk5_0,X1,X2)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_60]),c_0_58]),c_0_59])]),c_0_48]),
    [final]).

cnf(c_0_75,plain,
    ( r1_funct_2(X1,X2,u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),u1_orders_2(X3))
    | v1_xboole_0(u1_struct_0(X3))
    | v1_xboole_0(X2)
    | ~ v1_funct_2(u1_orders_2(X3),u1_struct_0(X3),u1_struct_0(X3))
    | ~ v1_funct_2(u1_orders_2(X3),X1,X2)
    | ~ v1_funct_1(u1_orders_2(X3))
    | ~ m1_subset_1(u1_orders_2(X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ l1_orders_2(X3) ),
    inference(spm,[status(thm)],[c_0_63,c_0_13]),
    [final]).

cnf(c_0_76,plain,
    ( X1 = u1_orders_2(X2)
    | v1_xboole_0(u1_struct_0(X2))
    | v1_xboole_0(X3)
    | ~ r1_funct_2(X4,X3,u1_struct_0(X2),u1_struct_0(X2),X1,u1_orders_2(X2))
    | ~ v1_funct_2(u1_orders_2(X2),u1_struct_0(X2),u1_struct_0(X2))
    | ~ v1_funct_2(X1,X4,X3)
    | ~ v1_funct_1(u1_orders_2(X2))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_13]),
    [final]).

cnf(c_0_77,negated_conjecture,
    ( X1 = u1_orders_2(esk1_0)
    | v1_xboole_0(X2)
    | ~ r1_funct_2(X3,X2,u1_struct_0(esk1_0),u1_struct_0(esk1_0),X1,u1_orders_2(esk1_0))
    | ~ v1_funct_2(u1_orders_2(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0))
    | ~ v1_funct_2(X1,X3,X2)
    | ~ v1_funct_1(u1_orders_2(esk1_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_64]),c_0_65]),
    [final]).

cnf(c_0_78,negated_conjecture,
    ( X1 = u1_orders_2(esk2_0)
    | v1_xboole_0(X2)
    | ~ r1_funct_2(X3,X2,u1_struct_0(esk2_0),u1_struct_0(esk2_0),X1,u1_orders_2(esk2_0))
    | ~ v1_funct_2(u1_orders_2(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0))
    | ~ v1_funct_2(X1,X3,X2)
    | ~ v1_funct_1(u1_orders_2(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_66]),c_0_48]),
    [final]).

cnf(c_0_79,negated_conjecture,
    ( r1_funct_2(X1,X2,u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_orders_2(esk1_0),u1_orders_2(esk1_0))
    | v1_xboole_0(X2)
    | ~ v1_funct_2(u1_orders_2(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0))
    | ~ v1_funct_2(u1_orders_2(esk1_0),X1,X2)
    | ~ v1_funct_1(u1_orders_2(esk1_0))
    | ~ m1_subset_1(u1_orders_2(esk1_0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65]),
    [final]).

cnf(c_0_80,negated_conjecture,
    ( r3_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0)
    | ~ r4_waybel_0(esk3_0,esk4_0,esk5_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_67,c_0_68]),
    [final]).

cnf(c_0_81,negated_conjecture,
    ( r4_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0)
    | ~ r3_waybel_0(esk3_0,esk4_0,esk5_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_69,c_0_68]),
    [final]).

cnf(c_0_82,negated_conjecture,
    ( ~ r3_waybel_0(esk3_0,esk4_0,esk5_0,esk7_0)
    | ~ r4_waybel_0(esk3_0,esk4_0,esk5_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_68]),c_0_68]),
    [final]).

cnf(c_0_83,negated_conjecture,
    ( X1 = esk5_0
    | v1_xboole_0(X2)
    | ~ r1_funct_2(X3,X2,u1_struct_0(esk1_0),u1_struct_0(esk2_0),X1,esk5_0)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_60]),c_0_58]),c_0_59])]),c_0_48]),
    [final]).

cnf(c_0_84,negated_conjecture,
    ( r1_funct_2(X1,X2,u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_orders_2(esk2_0),u1_orders_2(esk2_0))
    | v1_xboole_0(X2)
    | ~ v1_funct_2(u1_orders_2(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0))
    | ~ v1_funct_2(u1_orders_2(esk2_0),X1,X2)
    | ~ v1_funct_1(u1_orders_2(esk2_0))
    | ~ m1_subset_1(u1_orders_2(esk2_0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_66]),c_0_48]),
    [final]).

cnf(c_0_85,negated_conjecture,
    ( u1_struct_0(esk1_0) = X1
    | g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) != g1_orders_2(X1,X2) ),
    inference(rw,[status(thm)],[c_0_33,c_0_39]),
    [final]).

cnf(c_0_86,negated_conjecture,
    ( u1_struct_0(esk2_0) = X1
    | g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) != g1_orders_2(X1,X2) ),
    inference(rw,[status(thm)],[c_0_27,c_0_32]),
    [final]).

cnf(c_0_87,negated_conjecture,
    ( u1_orders_2(esk1_0) = X1
    | g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) != g1_orders_2(X2,X1) ),
    inference(rw,[status(thm)],[c_0_23,c_0_26]),
    [final]).

cnf(c_0_88,negated_conjecture,
    ( u1_orders_2(esk2_0) = X1
    | g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) != g1_orders_2(X2,X1) ),
    inference(rw,[status(thm)],[c_0_18,c_0_22]),
    [final]).

cnf(c_0_89,plain,
    ( k2_yellow_0(X1,X3) = k2_yellow_0(X2,X3)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
    | ~ r2_yellow_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_71]),
    [final]).

cnf(c_0_90,plain,
    ( k1_yellow_0(X1,X3) = k1_yellow_0(X2,X3)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
    | ~ r1_yellow_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_72]),
    [final]).

cnf(c_0_91,plain,
    ( r2_yellow_0(X3,X2)
    | ~ r2_yellow_0(X1,X2)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
    | ~ l1_orders_2(X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73]),
    [final]).

cnf(c_0_92,plain,
    ( r1_yellow_0(X3,X2)
    | ~ r1_yellow_0(X1,X2)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
    | ~ l1_orders_2(X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73]),
    [final]).

cnf(c_0_93,negated_conjecture,
    ( r3_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0)
    | r4_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_94,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_95,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_96,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_60]),c_0_58])]),c_0_48]),
    [final]).

cnf(c_0_97,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_98,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_99,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:47:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.18/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.18/0.37  #
% 0.18/0.37  # Preprocessing time       : 0.028 s
% 0.18/0.37  # Presaturation interreduction done
% 0.18/0.37  
% 0.18/0.37  # No proof found!
% 0.18/0.37  # SZS status CounterSatisfiable
% 0.18/0.37  # SZS output start Saturation
% 0.18/0.37  fof(free_g1_orders_2, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))=>![X3, X4]:(g1_orders_2(X1,X2)=g1_orders_2(X3,X4)=>(X1=X3&X2=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_orders_2)).
% 0.18/0.37  fof(dt_u1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 0.18/0.37  fof(t65_waybel_0, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:((~(v2_struct_0(X2))&l1_orders_2(X2))=>![X3]:((~(v2_struct_0(X3))&l1_orders_2(X3))=>![X4]:((~(v2_struct_0(X4))&l1_orders_2(X4))=>((g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))=g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))&g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))=g1_orders_2(u1_struct_0(X4),u1_orders_2(X4)))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X4)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4)))))=>(r1_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X3),u1_struct_0(X4),X5,X6)=>![X7]:(m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))=>![X8]:(m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X3)))=>(X7=X8=>((r4_waybel_0(X1,X2,X5,X7)=>r4_waybel_0(X3,X4,X6,X8))&(r3_waybel_0(X1,X2,X5,X7)=>r3_waybel_0(X3,X4,X6,X8)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_waybel_0)).
% 0.18/0.37  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.18/0.37  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.18/0.37  fof(redefinition_r1_funct_2, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((~(v1_xboole_0(X2))&~(v1_xboole_0(X4)))&v1_funct_1(X5))&v1_funct_2(X5,X1,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X3,X4))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(r1_funct_2(X1,X2,X3,X4,X5,X6)<=>X5=X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 0.18/0.37  fof(t27_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(l1_orders_2(X2)=>(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))=g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))=>![X3]:(r2_yellow_0(X1,X3)=>k2_yellow_0(X1,X3)=k2_yellow_0(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_yellow_0)).
% 0.18/0.37  fof(t26_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(l1_orders_2(X2)=>(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))=g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))=>![X3]:(r1_yellow_0(X1,X3)=>k1_yellow_0(X1,X3)=k1_yellow_0(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_yellow_0)).
% 0.18/0.37  fof(t14_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(l1_orders_2(X2)=>(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))=g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))=>![X3]:((r1_yellow_0(X1,X3)=>r1_yellow_0(X2,X3))&(r2_yellow_0(X1,X3)=>r2_yellow_0(X2,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow_0)).
% 0.18/0.37  fof(c_0_9, plain, ![X12, X13, X14, X15]:((X12=X14|g1_orders_2(X12,X13)!=g1_orders_2(X14,X15)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X12,X12))))&(X13=X15|g1_orders_2(X12,X13)!=g1_orders_2(X14,X15)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X12,X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).
% 0.18/0.37  fof(c_0_10, plain, ![X11]:(~l1_orders_2(X11)|m1_subset_1(u1_orders_2(X11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(X11))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).
% 0.18/0.37  fof(c_0_11, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:((~(v2_struct_0(X2))&l1_orders_2(X2))=>![X3]:((~(v2_struct_0(X3))&l1_orders_2(X3))=>![X4]:((~(v2_struct_0(X4))&l1_orders_2(X4))=>((g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))=g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))&g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))=g1_orders_2(u1_struct_0(X4),u1_orders_2(X4)))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X4)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4)))))=>(r1_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X3),u1_struct_0(X4),X5,X6)=>![X7]:(m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))=>![X8]:(m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X3)))=>(X7=X8=>((r4_waybel_0(X1,X2,X5,X7)=>r4_waybel_0(X3,X4,X6,X8))&(r3_waybel_0(X1,X2,X5,X7)=>r3_waybel_0(X3,X4,X6,X8))))))))))))))), inference(assume_negation,[status(cth)],[t65_waybel_0])).
% 0.18/0.37  cnf(c_0_12, plain, (X1=X2|g1_orders_2(X3,X1)!=g1_orders_2(X4,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3)))), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.18/0.37  cnf(c_0_13, plain, (m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.18/0.37  fof(c_0_14, negated_conjecture, ((~v2_struct_0(esk1_0)&l1_orders_2(esk1_0))&((~v2_struct_0(esk2_0)&l1_orders_2(esk2_0))&((~v2_struct_0(esk3_0)&l1_orders_2(esk3_0))&((~v2_struct_0(esk4_0)&l1_orders_2(esk4_0))&((g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0))=g1_orders_2(u1_struct_0(esk3_0),u1_orders_2(esk3_0))&g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0))=g1_orders_2(u1_struct_0(esk4_0),u1_orders_2(esk4_0)))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))))&(r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0)&(m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(esk7_0=esk8_0&(((r3_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0)|r4_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0))&(~r3_waybel_0(esk3_0,esk4_0,esk6_0,esk8_0)|r4_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0)))&((r3_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0)|~r4_waybel_0(esk3_0,esk4_0,esk6_0,esk8_0))&(~r3_waybel_0(esk3_0,esk4_0,esk6_0,esk8_0)|~r4_waybel_0(esk3_0,esk4_0,esk6_0,esk8_0))))))))))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])).
% 0.18/0.37  cnf(c_0_15, plain, (u1_orders_2(X1)=X2|g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))!=g1_orders_2(X3,X2)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_12, c_0_13]), ['final']).
% 0.18/0.37  cnf(c_0_16, negated_conjecture, (g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0))=g1_orders_2(u1_struct_0(esk4_0),u1_orders_2(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.37  cnf(c_0_17, negated_conjecture, (l1_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.18/0.37  cnf(c_0_18, negated_conjecture, (u1_orders_2(esk4_0)=X1|g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0))!=g1_orders_2(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])])).
% 0.18/0.37  cnf(c_0_19, negated_conjecture, (g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0))=g1_orders_2(u1_struct_0(esk3_0),u1_orders_2(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.37  cnf(c_0_20, negated_conjecture, (l1_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.18/0.37  cnf(c_0_21, plain, (X1=X2|g1_orders_2(X1,X3)!=g1_orders_2(X2,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.18/0.37  cnf(c_0_22, negated_conjecture, (u1_orders_2(esk4_0)=u1_orders_2(esk2_0)), inference(er,[status(thm)],[c_0_18]), ['final']).
% 0.18/0.37  cnf(c_0_23, negated_conjecture, (u1_orders_2(esk3_0)=X1|g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0))!=g1_orders_2(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_19]), c_0_20])])).
% 0.18/0.37  cnf(c_0_24, plain, (u1_struct_0(X1)=X2|g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))!=g1_orders_2(X2,X3)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_21, c_0_13]), ['final']).
% 0.18/0.37  cnf(c_0_25, negated_conjecture, (g1_orders_2(u1_struct_0(esk4_0),u1_orders_2(esk2_0))=g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0))), inference(rw,[status(thm)],[c_0_16, c_0_22])).
% 0.18/0.37  cnf(c_0_26, negated_conjecture, (u1_orders_2(esk3_0)=u1_orders_2(esk1_0)), inference(er,[status(thm)],[c_0_23]), ['final']).
% 0.18/0.37  cnf(c_0_27, negated_conjecture, (u1_struct_0(esk4_0)=X1|g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0))!=g1_orders_2(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_22]), c_0_25]), c_0_17])])).
% 0.18/0.37  cnf(c_0_28, negated_conjecture, (g1_orders_2(u1_struct_0(esk3_0),u1_orders_2(esk1_0))=g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0))), inference(rw,[status(thm)],[c_0_19, c_0_26])).
% 0.18/0.37  fof(c_0_29, plain, ![X9]:(v2_struct_0(X9)|~l1_struct_0(X9)|~v1_xboole_0(u1_struct_0(X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.18/0.37  fof(c_0_30, plain, ![X10]:(~l1_orders_2(X10)|l1_struct_0(X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.18/0.37  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.37  cnf(c_0_32, negated_conjecture, (u1_struct_0(esk4_0)=u1_struct_0(esk2_0)), inference(er,[status(thm)],[c_0_27]), ['final']).
% 0.18/0.37  cnf(c_0_33, negated_conjecture, (u1_struct_0(esk3_0)=X1|g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0))!=g1_orders_2(X1,X2)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_26]), c_0_20])]), c_0_28])).
% 0.18/0.37  cnf(c_0_34, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.37  cnf(c_0_35, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_29]), ['final']).
% 0.18/0.37  cnf(c_0_36, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_30]), ['final']).
% 0.18/0.37  fof(c_0_37, plain, ![X25, X26, X27, X28, X29, X30]:((~r1_funct_2(X25,X26,X27,X28,X29,X30)|X29=X30|(v1_xboole_0(X26)|v1_xboole_0(X28)|~v1_funct_1(X29)|~v1_funct_2(X29,X25,X26)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))|~v1_funct_1(X30)|~v1_funct_2(X30,X27,X28)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))))&(X29!=X30|r1_funct_2(X25,X26,X27,X28,X29,X30)|(v1_xboole_0(X26)|v1_xboole_0(X28)|~v1_funct_1(X29)|~v1_funct_2(X29,X25,X26)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))|~v1_funct_1(X30)|~v1_funct_2(X30,X27,X28)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).
% 0.18/0.37  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 0.18/0.37  cnf(c_0_39, negated_conjecture, (u1_struct_0(esk3_0)=u1_struct_0(esk1_0)), inference(er,[status(thm)],[c_0_33]), ['final']).
% 0.18/0.37  cnf(c_0_40, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0))), inference(rw,[status(thm)],[c_0_34, c_0_32])).
% 0.18/0.37  cnf(c_0_41, plain, (v2_struct_0(X1)|~l1_orders_2(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_35, c_0_36]), ['final']).
% 0.18/0.37  cnf(c_0_42, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.18/0.37  cnf(c_0_43, negated_conjecture, (r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.37  cnf(c_0_44, plain, (X5=X6|v1_xboole_0(X2)|v1_xboole_0(X4)|~r1_funct_2(X1,X2,X3,X4,X5,X6)|~v1_funct_1(X5)|~v1_funct_2(X5,X1,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X3,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_37]), ['final']).
% 0.18/0.37  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(rw,[status(thm)],[c_0_38, c_0_39])).
% 0.18/0.37  cnf(c_0_46, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(rw,[status(thm)],[c_0_40, c_0_39])).
% 0.18/0.37  cnf(c_0_47, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.37  cnf(c_0_48, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_32]), c_0_17])]), c_0_42]), ['final']).
% 0.18/0.37  cnf(c_0_49, negated_conjecture, (r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_43, c_0_32])).
% 0.18/0.37  cnf(c_0_50, plain, (r1_funct_2(X3,X4,X5,X6,X1,X2)|v1_xboole_0(X4)|v1_xboole_0(X6)|X1!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X2)|~v1_funct_2(X2,X5,X6)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.18/0.37  cnf(c_0_51, negated_conjecture, (m1_subset_1(u1_orders_2(esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_26]), c_0_20])])).
% 0.18/0.37  cnf(c_0_52, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.18/0.37  cnf(c_0_53, negated_conjecture, (m1_subset_1(u1_orders_2(esk2_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_22]), c_0_17])])).
% 0.18/0.37  cnf(c_0_54, negated_conjecture, (r3_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0)|~r4_waybel_0(esk3_0,esk4_0,esk6_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.37  cnf(c_0_55, negated_conjecture, (esk7_0=esk8_0), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.18/0.37  cnf(c_0_56, negated_conjecture, (X1=esk6_0|v1_xboole_0(X2)|~r1_funct_2(X3,X2,u1_struct_0(esk1_0),u1_struct_0(esk2_0),X1,esk6_0)|~v1_funct_2(X1,X3,X2)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_47])]), c_0_48])).
% 0.18/0.37  cnf(c_0_57, negated_conjecture, (r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_49, c_0_39])).
% 0.18/0.37  cnf(c_0_58, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.18/0.37  cnf(c_0_59, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.18/0.37  cnf(c_0_60, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.18/0.37  cnf(c_0_61, negated_conjecture, (r4_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0)|~r3_waybel_0(esk3_0,esk4_0,esk6_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.37  cnf(c_0_62, negated_conjecture, (~r3_waybel_0(esk3_0,esk4_0,esk6_0,esk8_0)|~r4_waybel_0(esk3_0,esk4_0,esk6_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.37  cnf(c_0_63, plain, (r1_funct_2(X1,X2,X3,X4,X5,X5)|v1_xboole_0(X4)|v1_xboole_0(X2)|~v1_funct_2(X5,X3,X4)|~v1_funct_2(X5,X1,X2)|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_50]), ['final']).
% 0.18/0.37  cnf(c_0_64, negated_conjecture, (m1_subset_1(u1_orders_2(esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_39]), c_0_39]), ['final']).
% 0.18/0.37  cnf(c_0_65, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_39]), c_0_20])]), c_0_52]), ['final']).
% 0.18/0.37  cnf(c_0_66, negated_conjecture, (m1_subset_1(u1_orders_2(esk2_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_32]), c_0_32]), ['final']).
% 0.18/0.37  cnf(c_0_67, negated_conjecture, (r3_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0)|~r4_waybel_0(esk3_0,esk4_0,esk6_0,esk7_0)), inference(rw,[status(thm)],[c_0_54, c_0_55])).
% 0.18/0.37  cnf(c_0_68, negated_conjecture, (esk6_0=esk5_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58]), c_0_59]), c_0_60])]), c_0_48]), ['final']).
% 0.18/0.37  cnf(c_0_69, negated_conjecture, (r4_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0)|~r3_waybel_0(esk3_0,esk4_0,esk6_0,esk7_0)), inference(rw,[status(thm)],[c_0_61, c_0_55])).
% 0.18/0.37  cnf(c_0_70, negated_conjecture, (~r3_waybel_0(esk3_0,esk4_0,esk6_0,esk7_0)|~r4_waybel_0(esk3_0,esk4_0,esk6_0,esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_55]), c_0_55])).
% 0.18/0.37  fof(c_0_71, plain, ![X22, X23, X24]:(~l1_orders_2(X22)|(~l1_orders_2(X23)|(g1_orders_2(u1_struct_0(X22),u1_orders_2(X22))!=g1_orders_2(u1_struct_0(X23),u1_orders_2(X23))|(~r2_yellow_0(X22,X24)|k2_yellow_0(X22,X24)=k2_yellow_0(X23,X24))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_yellow_0])])])).
% 0.18/0.37  fof(c_0_72, plain, ![X19, X20, X21]:(~l1_orders_2(X19)|(~l1_orders_2(X20)|(g1_orders_2(u1_struct_0(X19),u1_orders_2(X19))!=g1_orders_2(u1_struct_0(X20),u1_orders_2(X20))|(~r1_yellow_0(X19,X21)|k1_yellow_0(X19,X21)=k1_yellow_0(X20,X21))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_yellow_0])])])).
% 0.18/0.37  fof(c_0_73, plain, ![X16, X17, X18]:((~r1_yellow_0(X16,X18)|r1_yellow_0(X17,X18)|g1_orders_2(u1_struct_0(X16),u1_orders_2(X16))!=g1_orders_2(u1_struct_0(X17),u1_orders_2(X17))|~l1_orders_2(X17)|~l1_orders_2(X16))&(~r2_yellow_0(X16,X18)|r2_yellow_0(X17,X18)|g1_orders_2(u1_struct_0(X16),u1_orders_2(X16))!=g1_orders_2(u1_struct_0(X17),u1_orders_2(X17))|~l1_orders_2(X17)|~l1_orders_2(X16))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_yellow_0])])])])).
% 0.18/0.37  cnf(c_0_74, negated_conjecture, (r1_funct_2(X1,X2,u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk5_0)|v1_xboole_0(X2)|~v1_funct_2(esk5_0,X1,X2)|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_60]), c_0_58]), c_0_59])]), c_0_48]), ['final']).
% 0.18/0.37  cnf(c_0_75, plain, (r1_funct_2(X1,X2,u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),u1_orders_2(X3))|v1_xboole_0(u1_struct_0(X3))|v1_xboole_0(X2)|~v1_funct_2(u1_orders_2(X3),u1_struct_0(X3),u1_struct_0(X3))|~v1_funct_2(u1_orders_2(X3),X1,X2)|~v1_funct_1(u1_orders_2(X3))|~m1_subset_1(u1_orders_2(X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~l1_orders_2(X3)), inference(spm,[status(thm)],[c_0_63, c_0_13]), ['final']).
% 0.18/0.37  cnf(c_0_76, plain, (X1=u1_orders_2(X2)|v1_xboole_0(u1_struct_0(X2))|v1_xboole_0(X3)|~r1_funct_2(X4,X3,u1_struct_0(X2),u1_struct_0(X2),X1,u1_orders_2(X2))|~v1_funct_2(u1_orders_2(X2),u1_struct_0(X2),u1_struct_0(X2))|~v1_funct_2(X1,X4,X3)|~v1_funct_1(u1_orders_2(X2))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))|~l1_orders_2(X2)), inference(spm,[status(thm)],[c_0_44, c_0_13]), ['final']).
% 0.18/0.37  cnf(c_0_77, negated_conjecture, (X1=u1_orders_2(esk1_0)|v1_xboole_0(X2)|~r1_funct_2(X3,X2,u1_struct_0(esk1_0),u1_struct_0(esk1_0),X1,u1_orders_2(esk1_0))|~v1_funct_2(u1_orders_2(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0))|~v1_funct_2(X1,X3,X2)|~v1_funct_1(u1_orders_2(esk1_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_64]), c_0_65]), ['final']).
% 0.18/0.37  cnf(c_0_78, negated_conjecture, (X1=u1_orders_2(esk2_0)|v1_xboole_0(X2)|~r1_funct_2(X3,X2,u1_struct_0(esk2_0),u1_struct_0(esk2_0),X1,u1_orders_2(esk2_0))|~v1_funct_2(u1_orders_2(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0))|~v1_funct_2(X1,X3,X2)|~v1_funct_1(u1_orders_2(esk2_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_66]), c_0_48]), ['final']).
% 0.18/0.37  cnf(c_0_79, negated_conjecture, (r1_funct_2(X1,X2,u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_orders_2(esk1_0),u1_orders_2(esk1_0))|v1_xboole_0(X2)|~v1_funct_2(u1_orders_2(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0))|~v1_funct_2(u1_orders_2(esk1_0),X1,X2)|~v1_funct_1(u1_orders_2(esk1_0))|~m1_subset_1(u1_orders_2(esk1_0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65]), ['final']).
% 0.18/0.37  cnf(c_0_80, negated_conjecture, (r3_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0)|~r4_waybel_0(esk3_0,esk4_0,esk5_0,esk7_0)), inference(rw,[status(thm)],[c_0_67, c_0_68]), ['final']).
% 0.18/0.37  cnf(c_0_81, negated_conjecture, (r4_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0)|~r3_waybel_0(esk3_0,esk4_0,esk5_0,esk7_0)), inference(rw,[status(thm)],[c_0_69, c_0_68]), ['final']).
% 0.18/0.37  cnf(c_0_82, negated_conjecture, (~r3_waybel_0(esk3_0,esk4_0,esk5_0,esk7_0)|~r4_waybel_0(esk3_0,esk4_0,esk5_0,esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_68]), c_0_68]), ['final']).
% 0.18/0.37  cnf(c_0_83, negated_conjecture, (X1=esk5_0|v1_xboole_0(X2)|~r1_funct_2(X3,X2,u1_struct_0(esk1_0),u1_struct_0(esk2_0),X1,esk5_0)|~v1_funct_2(X1,X3,X2)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_60]), c_0_58]), c_0_59])]), c_0_48]), ['final']).
% 0.18/0.37  cnf(c_0_84, negated_conjecture, (r1_funct_2(X1,X2,u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_orders_2(esk2_0),u1_orders_2(esk2_0))|v1_xboole_0(X2)|~v1_funct_2(u1_orders_2(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0))|~v1_funct_2(u1_orders_2(esk2_0),X1,X2)|~v1_funct_1(u1_orders_2(esk2_0))|~m1_subset_1(u1_orders_2(esk2_0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_66]), c_0_48]), ['final']).
% 0.18/0.37  cnf(c_0_85, negated_conjecture, (u1_struct_0(esk1_0)=X1|g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0))!=g1_orders_2(X1,X2)), inference(rw,[status(thm)],[c_0_33, c_0_39]), ['final']).
% 0.18/0.37  cnf(c_0_86, negated_conjecture, (u1_struct_0(esk2_0)=X1|g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0))!=g1_orders_2(X1,X2)), inference(rw,[status(thm)],[c_0_27, c_0_32]), ['final']).
% 0.18/0.37  cnf(c_0_87, negated_conjecture, (u1_orders_2(esk1_0)=X1|g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0))!=g1_orders_2(X2,X1)), inference(rw,[status(thm)],[c_0_23, c_0_26]), ['final']).
% 0.18/0.37  cnf(c_0_88, negated_conjecture, (u1_orders_2(esk2_0)=X1|g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0))!=g1_orders_2(X2,X1)), inference(rw,[status(thm)],[c_0_18, c_0_22]), ['final']).
% 0.18/0.37  cnf(c_0_89, plain, (k2_yellow_0(X1,X3)=k2_yellow_0(X2,X3)|~l1_orders_2(X1)|~l1_orders_2(X2)|g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))!=g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))|~r2_yellow_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_71]), ['final']).
% 0.18/0.37  cnf(c_0_90, plain, (k1_yellow_0(X1,X3)=k1_yellow_0(X2,X3)|~l1_orders_2(X1)|~l1_orders_2(X2)|g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))!=g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))|~r1_yellow_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_72]), ['final']).
% 0.18/0.37  cnf(c_0_91, plain, (r2_yellow_0(X3,X2)|~r2_yellow_0(X1,X2)|g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))!=g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))|~l1_orders_2(X3)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_73]), ['final']).
% 0.18/0.37  cnf(c_0_92, plain, (r1_yellow_0(X3,X2)|~r1_yellow_0(X1,X2)|g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))!=g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))|~l1_orders_2(X3)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_73]), ['final']).
% 0.18/0.37  cnf(c_0_93, negated_conjecture, (r3_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0)|r4_waybel_0(esk1_0,esk2_0,esk5_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.18/0.37  cnf(c_0_94, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.18/0.37  cnf(c_0_95, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.18/0.37  cnf(c_0_96, negated_conjecture, (r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_60]), c_0_58])]), c_0_48]), ['final']).
% 0.18/0.37  cnf(c_0_97, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.18/0.37  cnf(c_0_98, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.18/0.37  cnf(c_0_99, negated_conjecture, (l1_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.18/0.37  # SZS output end Saturation
% 0.18/0.37  # Proof object total steps             : 100
% 0.18/0.37  # Proof object clause steps            : 81
% 0.18/0.37  # Proof object formula steps           : 19
% 0.18/0.37  # Proof object conjectures             : 67
% 0.18/0.37  # Proof object clause conjectures      : 64
% 0.18/0.37  # Proof object formula conjectures     : 3
% 0.18/0.37  # Proof object initial clauses used    : 34
% 0.18/0.37  # Proof object initial formulas used   : 9
% 0.18/0.37  # Proof object generating inferences   : 26
% 0.18/0.37  # Proof object simplifying inferences  : 69
% 0.18/0.37  # Parsed axioms                        : 9
% 0.18/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.37  # Initial clauses                      : 35
% 0.18/0.37  # Removed in clause preprocessing      : 0
% 0.18/0.37  # Initial clauses in saturation        : 35
% 0.18/0.37  # Processed clauses                    : 144
% 0.18/0.37  # ...of these trivial                  : 4
% 0.18/0.37  # ...subsumed                          : 24
% 0.18/0.37  # ...remaining for further processing  : 116
% 0.18/0.37  # Other redundant clauses eliminated   : 1
% 0.18/0.37  # Clauses deleted for lack of memory   : 0
% 0.18/0.37  # Backward-subsumed                    : 0
% 0.18/0.37  # Backward-rewritten                   : 27
% 0.18/0.37  # Generated clauses                    : 80
% 0.18/0.37  # ...of the previous two non-trivial   : 95
% 0.18/0.37  # Contextual simplify-reflections      : 0
% 0.18/0.37  # Paramodulations                      : 69
% 0.18/0.37  # Factorizations                       : 0
% 0.18/0.37  # Equation resolutions                 : 11
% 0.18/0.37  # Propositional unsat checks           : 0
% 0.18/0.37  #    Propositional check models        : 0
% 0.18/0.37  #    Propositional check unsatisfiable : 0
% 0.18/0.37  #    Propositional clauses             : 0
% 0.18/0.37  #    Propositional clauses after purity: 0
% 0.18/0.37  #    Propositional unsat core size     : 0
% 0.18/0.37  #    Propositional preprocessing time  : 0.000
% 0.18/0.37  #    Propositional encoding time       : 0.000
% 0.18/0.37  #    Propositional solver time         : 0.000
% 0.18/0.37  #    Success case prop preproc time    : 0.000
% 0.18/0.37  #    Success case prop encoding time   : 0.000
% 0.18/0.37  #    Success case prop solver time     : 0.000
% 0.18/0.37  # Current number of processed clauses  : 53
% 0.18/0.37  #    Positive orientable unit clauses  : 17
% 0.18/0.37  #    Positive unorientable unit clauses: 0
% 0.18/0.37  #    Negative unit clauses             : 6
% 0.18/0.37  #    Non-unit-clauses                  : 30
% 0.18/0.37  # Current number of unprocessed clauses: 0
% 0.18/0.37  # ...number of literals in the above   : 0
% 0.18/0.37  # Current number of archived formulas  : 0
% 0.18/0.37  # Current number of archived clauses   : 62
% 0.18/0.37  # Clause-clause subsumption calls (NU) : 193
% 0.18/0.37  # Rec. Clause-clause subsumption calls : 34
% 0.18/0.37  # Non-unit clause-clause subsumptions  : 24
% 0.18/0.37  # Unit Clause-clause subsumption calls : 16
% 0.18/0.37  # Rewrite failures with RHS unbound    : 0
% 0.18/0.37  # BW rewrite match attempts            : 8
% 0.18/0.37  # BW rewrite match successes           : 5
% 0.18/0.37  # Condensation attempts                : 0
% 0.18/0.37  # Condensation successes               : 0
% 0.18/0.37  # Termbank termtop insertions          : 5156
% 0.18/0.37  
% 0.18/0.37  # -------------------------------------------------
% 0.18/0.37  # User time                : 0.033 s
% 0.18/0.37  # System time              : 0.006 s
% 0.18/0.37  # Total time               : 0.039 s
% 0.18/0.37  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
