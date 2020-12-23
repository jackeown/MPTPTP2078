%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:33 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 231 expanded)
%              Number of clauses        :   33 (  84 expanded)
%              Number of leaves         :   10 (  57 expanded)
%              Depth                    :   14
%              Number of atoms          :  247 (1028 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   35 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k4_yellow_6,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & l1_waybel_0(X2,X1) )
     => m1_subset_1(k4_yellow_6(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_yellow_6)).

fof(rc5_waybel_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ? [X2] :
          ( l1_waybel_0(X2,X1)
          & ~ v2_struct_0(X2)
          & v3_orders_2(X2)
          & v4_orders_2(X2)
          & v5_orders_2(X2)
          & v6_waybel_0(X2,X1)
          & v7_waybel_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc5_waybel_0)).

fof(t8_waybel_9,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => r1_waybel_0(X1,X2,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_9)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(dt_l1_waybel_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => l1_orders_2(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(d11_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( r1_waybel_0(X1,X2,X3)
            <=> ? [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X2))
                  & ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                     => ( r1_orders_2(X2,X4,X5)
                       => r2_hidden(k2_waybel_0(X1,X2,X5),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_waybel_0)).

fof(t189_funct_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( m1_subset_1(X3,X1)
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,X1,X2)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
                 => r2_hidden(k3_funct_2(X1,X2,X4,X3),k2_relset_1(X1,X2,X4)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_funct_2)).

fof(dt_u1_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( l1_struct_0(X1)
        & l1_waybel_0(X2,X1) )
     => ( v1_funct_1(u1_waybel_0(X1,X2))
        & v1_funct_2(u1_waybel_0(X1,X2),u1_struct_0(X2),u1_struct_0(X1))
        & m1_subset_1(u1_waybel_0(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_waybel_0)).

fof(d8_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => k2_waybel_0(X1,X2,X3) = k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_waybel_0)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(c_0_10,plain,(
    ! [X27,X28] :
      ( v2_struct_0(X27)
      | ~ l1_struct_0(X27)
      | ~ l1_waybel_0(X28,X27)
      | m1_subset_1(k4_yellow_6(X27,X28),u1_struct_0(X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_yellow_6])])])).

fof(c_0_11,plain,(
    ! [X29] :
      ( ( l1_waybel_0(esk3_1(X29),X29)
        | ~ l1_struct_0(X29) )
      & ( ~ v2_struct_0(esk3_1(X29))
        | ~ l1_struct_0(X29) )
      & ( v3_orders_2(esk3_1(X29))
        | ~ l1_struct_0(X29) )
      & ( v4_orders_2(esk3_1(X29))
        | ~ l1_struct_0(X29) )
      & ( v5_orders_2(esk3_1(X29))
        | ~ l1_struct_0(X29) )
      & ( v6_waybel_0(esk3_1(X29),X29)
        | ~ l1_struct_0(X29) )
      & ( v7_waybel_0(esk3_1(X29))
        | ~ l1_struct_0(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc5_waybel_0])])])])])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_struct_0(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & l1_waybel_0(X2,X1) )
           => r1_waybel_0(X1,X2,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t8_waybel_9])).

cnf(c_0_13,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k4_yellow_6(X1,X2),u1_struct_0(X1))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( l1_waybel_0(esk3_1(X1),X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X11] :
      ( ~ l1_orders_2(X11)
      | l1_struct_0(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_16,plain,(
    ! [X23,X24] :
      ( ~ l1_struct_0(X23)
      | ~ l1_waybel_0(X24,X23)
      | l1_orders_2(X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).

fof(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & l1_struct_0(esk4_0)
    & ~ v2_struct_0(esk5_0)
    & l1_waybel_0(esk5_0,esk4_0)
    & ~ r1_waybel_0(esk4_0,esk5_0,k2_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk5_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

cnf(c_0_18,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k4_yellow_6(X1,esk3_1(X1)),u1_struct_0(X1))
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( l1_orders_2(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( l1_waybel_0(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( l1_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X12,X13,X14,X16,X17,X18] :
      ( ( m1_subset_1(esk1_3(X12,X13,X14),u1_struct_0(X13))
        | ~ r1_waybel_0(X12,X13,X14)
        | v2_struct_0(X13)
        | ~ l1_waybel_0(X13,X12)
        | v2_struct_0(X12)
        | ~ l1_struct_0(X12) )
      & ( ~ m1_subset_1(X16,u1_struct_0(X13))
        | ~ r1_orders_2(X13,esk1_3(X12,X13,X14),X16)
        | r2_hidden(k2_waybel_0(X12,X13,X16),X14)
        | ~ r1_waybel_0(X12,X13,X14)
        | v2_struct_0(X13)
        | ~ l1_waybel_0(X13,X12)
        | v2_struct_0(X12)
        | ~ l1_struct_0(X12) )
      & ( m1_subset_1(esk2_4(X12,X13,X17,X18),u1_struct_0(X13))
        | ~ m1_subset_1(X18,u1_struct_0(X13))
        | r1_waybel_0(X12,X13,X17)
        | v2_struct_0(X13)
        | ~ l1_waybel_0(X13,X12)
        | v2_struct_0(X12)
        | ~ l1_struct_0(X12) )
      & ( r1_orders_2(X13,X18,esk2_4(X12,X13,X17,X18))
        | ~ m1_subset_1(X18,u1_struct_0(X13))
        | r1_waybel_0(X12,X13,X17)
        | v2_struct_0(X13)
        | ~ l1_waybel_0(X13,X12)
        | v2_struct_0(X12)
        | ~ l1_struct_0(X12) )
      & ( ~ r2_hidden(k2_waybel_0(X12,X13,esk2_4(X12,X13,X17,X18)),X17)
        | ~ m1_subset_1(X18,u1_struct_0(X13))
        | r1_waybel_0(X12,X13,X17)
        | v2_struct_0(X13)
        | ~ l1_waybel_0(X13,X12)
        | v2_struct_0(X12)
        | ~ l1_struct_0(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_waybel_0])])])])])])])).

cnf(c_0_24,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k4_yellow_6(X1,esk3_1(X1)),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_27,plain,(
    ! [X6,X7,X8,X9] :
      ( v1_xboole_0(X6)
      | v1_xboole_0(X7)
      | ~ m1_subset_1(X8,X6)
      | ~ v1_funct_1(X9)
      | ~ v1_funct_2(X9,X6,X7)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | r2_hidden(k3_funct_2(X6,X7,X9,X8),k2_relset_1(X6,X7,X9)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t189_funct_2])])])])).

fof(c_0_28,plain,(
    ! [X25,X26] :
      ( ( v1_funct_1(u1_waybel_0(X25,X26))
        | ~ l1_struct_0(X25)
        | ~ l1_waybel_0(X26,X25) )
      & ( v1_funct_2(u1_waybel_0(X25,X26),u1_struct_0(X26),u1_struct_0(X25))
        | ~ l1_struct_0(X25)
        | ~ l1_waybel_0(X26,X25) )
      & ( m1_subset_1(u1_waybel_0(X25,X26),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X25))))
        | ~ l1_struct_0(X25)
        | ~ l1_waybel_0(X26,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_waybel_0])])])).

cnf(c_0_29,plain,
    ( m1_subset_1(esk2_4(X1,X2,X3,X4),u1_struct_0(X2))
    | r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(k4_yellow_6(esk5_0,esk3_1(esk5_0)),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

cnf(c_0_31,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | r2_hidden(k3_funct_2(X1,X2,X4,X3),k2_relset_1(X1,X2,X4))
    | ~ m1_subset_1(X3,X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( m1_subset_1(u1_waybel_0(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( v1_funct_1(u1_waybel_0(X1,X2))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( v1_funct_2(u1_waybel_0(X1,X2),u1_struct_0(X2),u1_struct_0(X1))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( r1_waybel_0(X1,esk5_0,X2)
    | v2_struct_0(X1)
    | m1_subset_1(esk2_4(X1,esk5_0,X2,k4_yellow_6(esk5_0,esk3_1(esk5_0))),u1_struct_0(esk5_0))
    | ~ l1_waybel_0(esk5_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_37,plain,(
    ! [X20,X21,X22] :
      ( v2_struct_0(X20)
      | ~ l1_struct_0(X20)
      | v2_struct_0(X21)
      | ~ l1_waybel_0(X21,X20)
      | ~ m1_subset_1(X22,u1_struct_0(X21))
      | k2_waybel_0(X20,X21,X22) = k3_funct_2(u1_struct_0(X21),u1_struct_0(X20),u1_waybel_0(X20,X21),X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_waybel_0])])])])).

cnf(c_0_38,plain,
    ( r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),X3),k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1)))
    | v1_xboole_0(u1_struct_0(X1))
    | v1_xboole_0(u1_struct_0(X2))
    | ~ l1_waybel_0(X1,X2)
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( r1_waybel_0(esk4_0,esk5_0,X1)
    | m1_subset_1(esk2_4(esk4_0,esk5_0,X1,k4_yellow_6(esk5_0,esk3_1(esk5_0))),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_21]),c_0_22])]),c_0_36])).

cnf(c_0_40,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k2_waybel_0(X1,X2,X3) = k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),X3)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( r1_waybel_0(esk4_0,esk5_0,X1)
    | r2_hidden(k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(X2),u1_waybel_0(X2,esk5_0),esk2_4(esk4_0,esk5_0,X1,k4_yellow_6(esk5_0,esk3_1(esk5_0)))),k2_relset_1(u1_struct_0(esk5_0),u1_struct_0(X2),u1_waybel_0(X2,esk5_0)))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | v1_xboole_0(u1_struct_0(X2))
    | ~ l1_waybel_0(esk5_0,X2)
    | ~ l1_struct_0(X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(X1),u1_waybel_0(X1,esk5_0),esk2_4(esk4_0,esk5_0,X2,k4_yellow_6(esk5_0,esk3_1(esk5_0)))) = k2_waybel_0(X1,esk5_0,esk2_4(esk4_0,esk5_0,X2,k4_yellow_6(esk5_0,esk3_1(esk5_0))))
    | r1_waybel_0(esk4_0,esk5_0,X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(esk5_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_39]),c_0_26])).

cnf(c_0_43,negated_conjecture,
    ( r1_waybel_0(esk4_0,esk5_0,X1)
    | r2_hidden(k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk5_0),esk2_4(esk4_0,esk5_0,X1,k4_yellow_6(esk5_0,esk3_1(esk5_0)))),k2_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk5_0)))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_21]),c_0_22])])).

cnf(c_0_44,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk5_0),esk2_4(esk4_0,esk5_0,X1,k4_yellow_6(esk5_0,esk3_1(esk5_0)))) = k2_waybel_0(esk4_0,esk5_0,esk2_4(esk4_0,esk5_0,X1,k4_yellow_6(esk5_0,esk3_1(esk5_0))))
    | r1_waybel_0(esk4_0,esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_21]),c_0_22])]),c_0_36])).

fof(c_0_45,plain,(
    ! [X10] :
      ( v2_struct_0(X10)
      | ~ l1_struct_0(X10)
      | ~ v1_xboole_0(u1_struct_0(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_46,plain,
    ( r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(k2_waybel_0(X1,X2,esk2_4(X1,X2,X3,X4)),X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_47,negated_conjecture,
    ( r1_waybel_0(esk4_0,esk5_0,X1)
    | r2_hidden(k2_waybel_0(esk4_0,esk5_0,esk2_4(esk4_0,esk5_0,X1,k4_yellow_6(esk5_0,esk3_1(esk5_0)))),k2_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk5_0)))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( ~ r1_waybel_0(esk4_0,esk5_0,k2_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_49,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_21]),c_0_22]),c_0_30])]),c_0_48]),c_0_26]),c_0_36])).

cnf(c_0_51,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_22])]),c_0_36])).

cnf(c_0_52,negated_conjecture,
    ( ~ l1_struct_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_51]),c_0_26])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_19]),c_0_25])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:21:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C02CMA_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(dt_k4_yellow_6, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_struct_0(X1))&l1_waybel_0(X2,X1))=>m1_subset_1(k4_yellow_6(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_yellow_6)).
% 0.13/0.38  fof(rc5_waybel_0, axiom, ![X1]:(l1_struct_0(X1)=>?[X2]:((((((l1_waybel_0(X2,X1)&~(v2_struct_0(X2)))&v3_orders_2(X2))&v4_orders_2(X2))&v5_orders_2(X2))&v6_waybel_0(X2,X1))&v7_waybel_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc5_waybel_0)).
% 0.13/0.38  fof(t8_waybel_9, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>r1_waybel_0(X1,X2,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_9)).
% 0.13/0.38  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.13/0.38  fof(dt_l1_waybel_0, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_waybel_0(X2,X1)=>l1_orders_2(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 0.13/0.38  fof(d11_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r1_waybel_0(X1,X2,X3)<=>?[X4]:(m1_subset_1(X4,u1_struct_0(X2))&![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>(r1_orders_2(X2,X4,X5)=>r2_hidden(k2_waybel_0(X1,X2,X5),X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_waybel_0)).
% 0.13/0.38  fof(t189_funct_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,X1)=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>r2_hidden(k3_funct_2(X1,X2,X4,X3),k2_relset_1(X1,X2,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t189_funct_2)).
% 0.13/0.38  fof(dt_u1_waybel_0, axiom, ![X1, X2]:((l1_struct_0(X1)&l1_waybel_0(X2,X1))=>((v1_funct_1(u1_waybel_0(X1,X2))&v1_funct_2(u1_waybel_0(X1,X2),u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(u1_waybel_0(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_waybel_0)).
% 0.13/0.38  fof(d8_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>k2_waybel_0(X1,X2,X3)=k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_waybel_0)).
% 0.13/0.38  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.13/0.38  fof(c_0_10, plain, ![X27, X28]:(v2_struct_0(X27)|~l1_struct_0(X27)|~l1_waybel_0(X28,X27)|m1_subset_1(k4_yellow_6(X27,X28),u1_struct_0(X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_yellow_6])])])).
% 0.13/0.38  fof(c_0_11, plain, ![X29]:(((((((l1_waybel_0(esk3_1(X29),X29)|~l1_struct_0(X29))&(~v2_struct_0(esk3_1(X29))|~l1_struct_0(X29)))&(v3_orders_2(esk3_1(X29))|~l1_struct_0(X29)))&(v4_orders_2(esk3_1(X29))|~l1_struct_0(X29)))&(v5_orders_2(esk3_1(X29))|~l1_struct_0(X29)))&(v6_waybel_0(esk3_1(X29),X29)|~l1_struct_0(X29)))&(v7_waybel_0(esk3_1(X29))|~l1_struct_0(X29))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc5_waybel_0])])])])])).
% 0.13/0.38  fof(c_0_12, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>r1_waybel_0(X1,X2,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)))))), inference(assume_negation,[status(cth)],[t8_waybel_9])).
% 0.13/0.38  cnf(c_0_13, plain, (v2_struct_0(X1)|m1_subset_1(k4_yellow_6(X1,X2),u1_struct_0(X1))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_14, plain, (l1_waybel_0(esk3_1(X1),X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  fof(c_0_15, plain, ![X11]:(~l1_orders_2(X11)|l1_struct_0(X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.13/0.38  fof(c_0_16, plain, ![X23, X24]:(~l1_struct_0(X23)|(~l1_waybel_0(X24,X23)|l1_orders_2(X24))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).
% 0.13/0.38  fof(c_0_17, negated_conjecture, ((~v2_struct_0(esk4_0)&l1_struct_0(esk4_0))&((~v2_struct_0(esk5_0)&l1_waybel_0(esk5_0,esk4_0))&~r1_waybel_0(esk4_0,esk5_0,k2_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk5_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).
% 0.13/0.38  cnf(c_0_18, plain, (v2_struct_0(X1)|m1_subset_1(k4_yellow_6(X1,esk3_1(X1)),u1_struct_0(X1))|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.13/0.38  cnf(c_0_19, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_20, plain, (l1_orders_2(X2)|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_21, negated_conjecture, (l1_waybel_0(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (l1_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  fof(c_0_23, plain, ![X12, X13, X14, X16, X17, X18]:(((m1_subset_1(esk1_3(X12,X13,X14),u1_struct_0(X13))|~r1_waybel_0(X12,X13,X14)|(v2_struct_0(X13)|~l1_waybel_0(X13,X12))|(v2_struct_0(X12)|~l1_struct_0(X12)))&(~m1_subset_1(X16,u1_struct_0(X13))|(~r1_orders_2(X13,esk1_3(X12,X13,X14),X16)|r2_hidden(k2_waybel_0(X12,X13,X16),X14))|~r1_waybel_0(X12,X13,X14)|(v2_struct_0(X13)|~l1_waybel_0(X13,X12))|(v2_struct_0(X12)|~l1_struct_0(X12))))&((m1_subset_1(esk2_4(X12,X13,X17,X18),u1_struct_0(X13))|~m1_subset_1(X18,u1_struct_0(X13))|r1_waybel_0(X12,X13,X17)|(v2_struct_0(X13)|~l1_waybel_0(X13,X12))|(v2_struct_0(X12)|~l1_struct_0(X12)))&((r1_orders_2(X13,X18,esk2_4(X12,X13,X17,X18))|~m1_subset_1(X18,u1_struct_0(X13))|r1_waybel_0(X12,X13,X17)|(v2_struct_0(X13)|~l1_waybel_0(X13,X12))|(v2_struct_0(X12)|~l1_struct_0(X12)))&(~r2_hidden(k2_waybel_0(X12,X13,esk2_4(X12,X13,X17,X18)),X17)|~m1_subset_1(X18,u1_struct_0(X13))|r1_waybel_0(X12,X13,X17)|(v2_struct_0(X13)|~l1_waybel_0(X13,X12))|(v2_struct_0(X12)|~l1_struct_0(X12)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_waybel_0])])])])])])])).
% 0.13/0.38  cnf(c_0_24, plain, (v2_struct_0(X1)|m1_subset_1(k4_yellow_6(X1,esk3_1(X1)),u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (l1_orders_2(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  fof(c_0_27, plain, ![X6, X7, X8, X9]:(v1_xboole_0(X6)|(v1_xboole_0(X7)|(~m1_subset_1(X8,X6)|(~v1_funct_1(X9)|~v1_funct_2(X9,X6,X7)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))|r2_hidden(k3_funct_2(X6,X7,X9,X8),k2_relset_1(X6,X7,X9)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t189_funct_2])])])])).
% 0.13/0.38  fof(c_0_28, plain, ![X25, X26]:(((v1_funct_1(u1_waybel_0(X25,X26))|(~l1_struct_0(X25)|~l1_waybel_0(X26,X25)))&(v1_funct_2(u1_waybel_0(X25,X26),u1_struct_0(X26),u1_struct_0(X25))|(~l1_struct_0(X25)|~l1_waybel_0(X26,X25))))&(m1_subset_1(u1_waybel_0(X25,X26),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X25))))|(~l1_struct_0(X25)|~l1_waybel_0(X26,X25)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_waybel_0])])])).
% 0.13/0.38  cnf(c_0_29, plain, (m1_subset_1(esk2_4(X1,X2,X3,X4),u1_struct_0(X2))|r1_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (m1_subset_1(k4_yellow_6(esk5_0,esk3_1(esk5_0)),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])).
% 0.13/0.38  cnf(c_0_31, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|r2_hidden(k3_funct_2(X1,X2,X4,X3),k2_relset_1(X1,X2,X4))|~m1_subset_1(X3,X1)|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.38  cnf(c_0_32, plain, (m1_subset_1(u1_waybel_0(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.38  cnf(c_0_33, plain, (v1_funct_1(u1_waybel_0(X1,X2))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.38  cnf(c_0_34, plain, (v1_funct_2(u1_waybel_0(X1,X2),u1_struct_0(X2),u1_struct_0(X1))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (r1_waybel_0(X1,esk5_0,X2)|v2_struct_0(X1)|m1_subset_1(esk2_4(X1,esk5_0,X2,k4_yellow_6(esk5_0,esk3_1(esk5_0))),u1_struct_0(esk5_0))|~l1_waybel_0(esk5_0,X1)|~l1_struct_0(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_26])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  fof(c_0_37, plain, ![X20, X21, X22]:(v2_struct_0(X20)|~l1_struct_0(X20)|(v2_struct_0(X21)|~l1_waybel_0(X21,X20)|(~m1_subset_1(X22,u1_struct_0(X21))|k2_waybel_0(X20,X21,X22)=k3_funct_2(u1_struct_0(X21),u1_struct_0(X20),u1_waybel_0(X20,X21),X22)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_waybel_0])])])])).
% 0.13/0.38  cnf(c_0_38, plain, (r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),X3),k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1)))|v1_xboole_0(u1_struct_0(X1))|v1_xboole_0(u1_struct_0(X2))|~l1_waybel_0(X1,X2)|~l1_struct_0(X2)|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34])).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, (r1_waybel_0(esk4_0,esk5_0,X1)|m1_subset_1(esk2_4(esk4_0,esk5_0,X1,k4_yellow_6(esk5_0,esk3_1(esk5_0))),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_21]), c_0_22])]), c_0_36])).
% 0.13/0.38  cnf(c_0_40, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_waybel_0(X1,X2,X3)=k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),X3)|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (r1_waybel_0(esk4_0,esk5_0,X1)|r2_hidden(k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(X2),u1_waybel_0(X2,esk5_0),esk2_4(esk4_0,esk5_0,X1,k4_yellow_6(esk5_0,esk3_1(esk5_0)))),k2_relset_1(u1_struct_0(esk5_0),u1_struct_0(X2),u1_waybel_0(X2,esk5_0)))|v1_xboole_0(u1_struct_0(esk5_0))|v1_xboole_0(u1_struct_0(X2))|~l1_waybel_0(esk5_0,X2)|~l1_struct_0(X2)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(X1),u1_waybel_0(X1,esk5_0),esk2_4(esk4_0,esk5_0,X2,k4_yellow_6(esk5_0,esk3_1(esk5_0))))=k2_waybel_0(X1,esk5_0,esk2_4(esk4_0,esk5_0,X2,k4_yellow_6(esk5_0,esk3_1(esk5_0))))|r1_waybel_0(esk4_0,esk5_0,X2)|v2_struct_0(X1)|~l1_waybel_0(esk5_0,X1)|~l1_struct_0(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_39]), c_0_26])).
% 0.13/0.38  cnf(c_0_43, negated_conjecture, (r1_waybel_0(esk4_0,esk5_0,X1)|r2_hidden(k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk5_0),esk2_4(esk4_0,esk5_0,X1,k4_yellow_6(esk5_0,esk3_1(esk5_0)))),k2_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk5_0)))|v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_21]), c_0_22])])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk5_0),esk2_4(esk4_0,esk5_0,X1,k4_yellow_6(esk5_0,esk3_1(esk5_0))))=k2_waybel_0(esk4_0,esk5_0,esk2_4(esk4_0,esk5_0,X1,k4_yellow_6(esk5_0,esk3_1(esk5_0))))|r1_waybel_0(esk4_0,esk5_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_21]), c_0_22])]), c_0_36])).
% 0.13/0.38  fof(c_0_45, plain, ![X10]:(v2_struct_0(X10)|~l1_struct_0(X10)|~v1_xboole_0(u1_struct_0(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.13/0.38  cnf(c_0_46, plain, (r1_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r2_hidden(k2_waybel_0(X1,X2,esk2_4(X1,X2,X3,X4)),X3)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_47, negated_conjecture, (r1_waybel_0(esk4_0,esk5_0,X1)|r2_hidden(k2_waybel_0(esk4_0,esk5_0,esk2_4(esk4_0,esk5_0,X1,k4_yellow_6(esk5_0,esk3_1(esk5_0)))),k2_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk5_0)))|v1_xboole_0(u1_struct_0(esk5_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.13/0.38  cnf(c_0_48, negated_conjecture, (~r1_waybel_0(esk4_0,esk5_0,k2_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_49, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_21]), c_0_22]), c_0_30])]), c_0_48]), c_0_26]), c_0_36])).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (v1_xboole_0(u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_22])]), c_0_36])).
% 0.13/0.38  cnf(c_0_52, negated_conjecture, (~l1_struct_0(esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_51]), c_0_26])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_19]), c_0_25])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 54
% 0.13/0.38  # Proof object clause steps            : 33
% 0.13/0.38  # Proof object formula steps           : 21
% 0.13/0.38  # Proof object conjectures             : 21
% 0.13/0.38  # Proof object clause conjectures      : 18
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 17
% 0.13/0.38  # Proof object initial formulas used   : 10
% 0.13/0.38  # Proof object generating inferences   : 16
% 0.13/0.38  # Proof object simplifying inferences  : 28
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 10
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 26
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 26
% 0.13/0.38  # Processed clauses                    : 107
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 0
% 0.13/0.38  # ...remaining for further processing  : 107
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 3
% 0.13/0.38  # Backward-rewritten                   : 3
% 0.13/0.38  # Generated clauses                    : 79
% 0.13/0.38  # ...of the previous two non-trivial   : 78
% 0.13/0.38  # Contextual simplify-reflections      : 7
% 0.13/0.38  # Paramodulations                      : 79
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 0
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 75
% 0.13/0.38  #    Positive orientable unit clauses  : 10
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 4
% 0.13/0.38  #    Non-unit-clauses                  : 61
% 0.13/0.38  # Current number of unprocessed clauses: 23
% 0.13/0.38  # ...number of literals in the above   : 124
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 32
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 2573
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 372
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 10
% 0.13/0.38  # Unit Clause-clause subsumption calls : 29
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 1
% 0.13/0.38  # BW rewrite match successes           : 1
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 6477
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.034 s
% 0.13/0.38  # System time              : 0.006 s
% 0.13/0.38  # Total time               : 0.040 s
% 0.13/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
