%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:33 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   43 (  88 expanded)
%              Number of clauses        :   24 (  31 expanded)
%              Number of leaves         :    9 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :  210 ( 447 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   35 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(dt_u1_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( l1_struct_0(X1)
        & l1_waybel_0(X2,X1) )
     => ( v1_funct_1(u1_waybel_0(X1,X2))
        & v1_funct_2(u1_waybel_0(X1,X2),u1_struct_0(X2),u1_struct_0(X1))
        & m1_subset_1(u1_waybel_0(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_waybel_0)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

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

fof(dt_o_2_4_waybel_9,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X2)
        & l1_waybel_0(X2,X1) )
     => m1_subset_1(o_2_4_waybel_9(X1,X2),u1_struct_0(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_2_4_waybel_9)).

fof(t8_waybel_9,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => r1_waybel_0(X1,X2,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_9)).

fof(dt_l1_waybel_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => l1_orders_2(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(c_0_9,plain,(
    ! [X6,X7,X8,X9] :
      ( v1_xboole_0(X6)
      | v1_xboole_0(X7)
      | ~ m1_subset_1(X8,X6)
      | ~ v1_funct_1(X9)
      | ~ v1_funct_2(X9,X6,X7)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | r2_hidden(k3_funct_2(X6,X7,X9,X8),k2_relset_1(X6,X7,X9)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t189_funct_2])])])])).

fof(c_0_10,plain,(
    ! [X20,X21,X22] :
      ( v2_struct_0(X20)
      | ~ l1_struct_0(X20)
      | v2_struct_0(X21)
      | ~ l1_waybel_0(X21,X20)
      | ~ m1_subset_1(X22,u1_struct_0(X21))
      | k2_waybel_0(X20,X21,X22) = k3_funct_2(u1_struct_0(X21),u1_struct_0(X20),u1_waybel_0(X20,X21),X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_waybel_0])])])])).

fof(c_0_11,plain,(
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

fof(c_0_12,plain,(
    ! [X10] :
      ( v2_struct_0(X10)
      | ~ l1_struct_0(X10)
      | ~ v1_xboole_0(u1_struct_0(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_13,plain,(
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

cnf(c_0_14,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | r2_hidden(k3_funct_2(X1,X2,X4,X3),k2_relset_1(X1,X2,X4))
    | ~ m1_subset_1(X3,X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k2_waybel_0(X1,X2,X3) = k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),X3)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( m1_subset_1(u1_waybel_0(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( v1_funct_1(u1_waybel_0(X1,X2))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( v1_funct_2(u1_waybel_0(X1,X2),u1_struct_0(X2),u1_struct_0(X1))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(k2_waybel_0(X1,X2,esk2_4(X1,X2,X3,X4)),X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r2_hidden(k2_waybel_0(X1,X2,X3),k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)))
    | v1_xboole_0(u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_22,plain,
    ( m1_subset_1(esk2_4(X1,X2,X3,X4),u1_struct_0(X2))
    | r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_23,plain,(
    ! [X27,X28] :
      ( v2_struct_0(X27)
      | ~ l1_struct_0(X27)
      | v2_struct_0(X28)
      | ~ l1_waybel_0(X28,X27)
      | m1_subset_1(o_2_4_waybel_9(X27,X28),u1_struct_0(X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_o_2_4_waybel_9])])])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_struct_0(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & l1_waybel_0(X2,X1) )
           => r1_waybel_0(X1,X2,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t8_waybel_9])).

cnf(c_0_25,plain,
    ( r1_waybel_0(X1,X2,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v1_xboole_0(u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_26,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(o_2_4_waybel_9(X1,X2),u1_struct_0(X2))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & l1_struct_0(esk3_0)
    & ~ v2_struct_0(esk4_0)
    & l1_waybel_0(esk4_0,esk3_0)
    & ~ r1_waybel_0(esk3_0,esk4_0,k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),u1_waybel_0(esk3_0,esk4_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_24])])])])).

fof(c_0_28,plain,(
    ! [X23,X24] :
      ( ~ l1_struct_0(X23)
      | ~ l1_waybel_0(X24,X23)
      | l1_orders_2(X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).

cnf(c_0_29,plain,
    ( r1_waybel_0(X1,X2,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v1_xboole_0(u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_waybel_0(X2,X3)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X3) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( l1_waybel_0(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( l1_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( ~ r1_waybel_0(esk3_0,esk4_0,k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),u1_waybel_0(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_35,plain,(
    ! [X11] :
      ( ~ l1_orders_2(X11)
      | l1_struct_0(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_36,plain,
    ( l1_orders_2(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ l1_waybel_0(esk4_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])]),c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_38,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_30]),c_0_31])])).

cnf(c_0_40,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_30]),c_0_31])]),c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_40]),c_0_41])]),c_0_33]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:58:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C00_02_nc_F1_SE_CS_SP_PS_S033N
% 0.20/0.38  # and selection function PSelectUnlessUniqMax.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.028 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t189_funct_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,X1)=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>r2_hidden(k3_funct_2(X1,X2,X4,X3),k2_relset_1(X1,X2,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t189_funct_2)).
% 0.20/0.38  fof(d8_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>k2_waybel_0(X1,X2,X3)=k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_waybel_0)).
% 0.20/0.38  fof(dt_u1_waybel_0, axiom, ![X1, X2]:((l1_struct_0(X1)&l1_waybel_0(X2,X1))=>((v1_funct_1(u1_waybel_0(X1,X2))&v1_funct_2(u1_waybel_0(X1,X2),u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(u1_waybel_0(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_waybel_0)).
% 0.20/0.38  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.20/0.38  fof(d11_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r1_waybel_0(X1,X2,X3)<=>?[X4]:(m1_subset_1(X4,u1_struct_0(X2))&![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>(r1_orders_2(X2,X4,X5)=>r2_hidden(k2_waybel_0(X1,X2,X5),X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_waybel_0)).
% 0.20/0.38  fof(dt_o_2_4_waybel_9, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v2_struct_0(X2)))&l1_waybel_0(X2,X1))=>m1_subset_1(o_2_4_waybel_9(X1,X2),u1_struct_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_o_2_4_waybel_9)).
% 0.20/0.38  fof(t8_waybel_9, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>r1_waybel_0(X1,X2,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_9)).
% 0.20/0.38  fof(dt_l1_waybel_0, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_waybel_0(X2,X1)=>l1_orders_2(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 0.20/0.38  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.20/0.38  fof(c_0_9, plain, ![X6, X7, X8, X9]:(v1_xboole_0(X6)|(v1_xboole_0(X7)|(~m1_subset_1(X8,X6)|(~v1_funct_1(X9)|~v1_funct_2(X9,X6,X7)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))|r2_hidden(k3_funct_2(X6,X7,X9,X8),k2_relset_1(X6,X7,X9)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t189_funct_2])])])])).
% 0.20/0.38  fof(c_0_10, plain, ![X20, X21, X22]:(v2_struct_0(X20)|~l1_struct_0(X20)|(v2_struct_0(X21)|~l1_waybel_0(X21,X20)|(~m1_subset_1(X22,u1_struct_0(X21))|k2_waybel_0(X20,X21,X22)=k3_funct_2(u1_struct_0(X21),u1_struct_0(X20),u1_waybel_0(X20,X21),X22)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_waybel_0])])])])).
% 0.20/0.38  fof(c_0_11, plain, ![X25, X26]:(((v1_funct_1(u1_waybel_0(X25,X26))|(~l1_struct_0(X25)|~l1_waybel_0(X26,X25)))&(v1_funct_2(u1_waybel_0(X25,X26),u1_struct_0(X26),u1_struct_0(X25))|(~l1_struct_0(X25)|~l1_waybel_0(X26,X25))))&(m1_subset_1(u1_waybel_0(X25,X26),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X25))))|(~l1_struct_0(X25)|~l1_waybel_0(X26,X25)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_waybel_0])])])).
% 0.20/0.38  fof(c_0_12, plain, ![X10]:(v2_struct_0(X10)|~l1_struct_0(X10)|~v1_xboole_0(u1_struct_0(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.20/0.38  fof(c_0_13, plain, ![X12, X13, X14, X16, X17, X18]:(((m1_subset_1(esk1_3(X12,X13,X14),u1_struct_0(X13))|~r1_waybel_0(X12,X13,X14)|(v2_struct_0(X13)|~l1_waybel_0(X13,X12))|(v2_struct_0(X12)|~l1_struct_0(X12)))&(~m1_subset_1(X16,u1_struct_0(X13))|(~r1_orders_2(X13,esk1_3(X12,X13,X14),X16)|r2_hidden(k2_waybel_0(X12,X13,X16),X14))|~r1_waybel_0(X12,X13,X14)|(v2_struct_0(X13)|~l1_waybel_0(X13,X12))|(v2_struct_0(X12)|~l1_struct_0(X12))))&((m1_subset_1(esk2_4(X12,X13,X17,X18),u1_struct_0(X13))|~m1_subset_1(X18,u1_struct_0(X13))|r1_waybel_0(X12,X13,X17)|(v2_struct_0(X13)|~l1_waybel_0(X13,X12))|(v2_struct_0(X12)|~l1_struct_0(X12)))&((r1_orders_2(X13,X18,esk2_4(X12,X13,X17,X18))|~m1_subset_1(X18,u1_struct_0(X13))|r1_waybel_0(X12,X13,X17)|(v2_struct_0(X13)|~l1_waybel_0(X13,X12))|(v2_struct_0(X12)|~l1_struct_0(X12)))&(~r2_hidden(k2_waybel_0(X12,X13,esk2_4(X12,X13,X17,X18)),X17)|~m1_subset_1(X18,u1_struct_0(X13))|r1_waybel_0(X12,X13,X17)|(v2_struct_0(X13)|~l1_waybel_0(X13,X12))|(v2_struct_0(X12)|~l1_struct_0(X12)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_waybel_0])])])])])])])).
% 0.20/0.38  cnf(c_0_14, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|r2_hidden(k3_funct_2(X1,X2,X4,X3),k2_relset_1(X1,X2,X4))|~m1_subset_1(X3,X1)|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  cnf(c_0_15, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_waybel_0(X1,X2,X3)=k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),X3)|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_16, plain, (m1_subset_1(u1_waybel_0(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  cnf(c_0_17, plain, (v1_funct_1(u1_waybel_0(X1,X2))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  cnf(c_0_18, plain, (v1_funct_2(u1_waybel_0(X1,X2),u1_struct_0(X2),u1_struct_0(X1))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  cnf(c_0_19, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_20, plain, (r1_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r2_hidden(k2_waybel_0(X1,X2,esk2_4(X1,X2,X3,X4)),X3)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_21, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r2_hidden(k2_waybel_0(X1,X2,X3),k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)))|v1_xboole_0(u1_struct_0(X2))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_17]), c_0_18]), c_0_19])).
% 0.20/0.38  cnf(c_0_22, plain, (m1_subset_1(esk2_4(X1,X2,X3,X4),u1_struct_0(X2))|r1_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  fof(c_0_23, plain, ![X27, X28]:(v2_struct_0(X27)|~l1_struct_0(X27)|v2_struct_0(X28)|~l1_waybel_0(X28,X27)|m1_subset_1(o_2_4_waybel_9(X27,X28),u1_struct_0(X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_o_2_4_waybel_9])])])).
% 0.20/0.38  fof(c_0_24, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>r1_waybel_0(X1,X2,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)))))), inference(assume_negation,[status(cth)],[t8_waybel_9])).
% 0.20/0.38  cnf(c_0_25, plain, (r1_waybel_0(X1,X2,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)))|v2_struct_0(X1)|v2_struct_0(X2)|v1_xboole_0(u1_struct_0(X2))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])).
% 0.20/0.38  cnf(c_0_26, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(o_2_4_waybel_9(X1,X2),u1_struct_0(X2))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.38  fof(c_0_27, negated_conjecture, ((~v2_struct_0(esk3_0)&l1_struct_0(esk3_0))&((~v2_struct_0(esk4_0)&l1_waybel_0(esk4_0,esk3_0))&~r1_waybel_0(esk3_0,esk4_0,k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),u1_waybel_0(esk3_0,esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_24])])])])).
% 0.20/0.38  fof(c_0_28, plain, ![X23, X24]:(~l1_struct_0(X23)|(~l1_waybel_0(X24,X23)|l1_orders_2(X24))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).
% 0.20/0.38  cnf(c_0_29, plain, (r1_waybel_0(X1,X2,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)))|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|v1_xboole_0(u1_struct_0(X2))|~l1_waybel_0(X2,X1)|~l1_waybel_0(X2,X3)|~l1_struct_0(X1)|~l1_struct_0(X3)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.38  cnf(c_0_30, negated_conjecture, (l1_waybel_0(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.38  cnf(c_0_31, negated_conjecture, (l1_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.38  cnf(c_0_32, negated_conjecture, (~r1_waybel_0(esk3_0,esk4_0,k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),u1_waybel_0(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.38  cnf(c_0_33, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.38  cnf(c_0_34, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.38  fof(c_0_35, plain, ![X11]:(~l1_orders_2(X11)|l1_struct_0(X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.20/0.38  cnf(c_0_36, plain, (l1_orders_2(X2)|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.38  cnf(c_0_37, negated_conjecture, (v2_struct_0(X1)|v1_xboole_0(u1_struct_0(esk4_0))|~l1_waybel_0(esk4_0,X1)|~l1_struct_0(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])]), c_0_32]), c_0_33]), c_0_34])).
% 0.20/0.38  cnf(c_0_38, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.38  cnf(c_0_39, negated_conjecture, (l1_orders_2(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_30]), c_0_31])])).
% 0.20/0.38  cnf(c_0_40, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_30]), c_0_31])]), c_0_34])).
% 0.20/0.38  cnf(c_0_41, negated_conjecture, (l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.38  cnf(c_0_42, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_40]), c_0_41])]), c_0_33]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 43
% 0.20/0.38  # Proof object clause steps            : 24
% 0.20/0.38  # Proof object formula steps           : 19
% 0.20/0.38  # Proof object conjectures             : 13
% 0.20/0.38  # Proof object clause conjectures      : 10
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 16
% 0.20/0.38  # Proof object initial formulas used   : 9
% 0.20/0.38  # Proof object generating inferences   : 8
% 0.20/0.38  # Proof object simplifying inferences  : 18
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 9
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 19
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 19
% 0.20/0.38  # Processed clauses                    : 46
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 0
% 0.20/0.38  # ...remaining for further processing  : 46
% 0.20/0.38  # Other redundant clauses eliminated   : 0
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 1
% 0.20/0.38  # Backward-rewritten                   : 0
% 0.20/0.38  # Generated clauses                    : 12
% 0.20/0.38  # ...of the previous two non-trivial   : 10
% 0.20/0.38  # Contextual simplify-reflections      : 6
% 0.20/0.38  # Paramodulations                      : 12
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 0
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 26
% 0.20/0.38  #    Positive orientable unit clauses  : 5
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 3
% 0.20/0.38  #    Non-unit-clauses                  : 18
% 0.20/0.38  # Current number of unprocessed clauses: 2
% 0.20/0.38  # ...number of literals in the above   : 21
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 20
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 519
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 48
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 6
% 0.20/0.38  # Unit Clause-clause subsumption calls : 20
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 1
% 0.20/0.38  # BW rewrite match successes           : 1
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 2753
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.030 s
% 0.20/0.38  # System time              : 0.005 s
% 0.20/0.38  # Total time               : 0.035 s
% 0.20/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
