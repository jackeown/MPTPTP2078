%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:28 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 272 expanded)
%              Number of clauses        :   35 ( 102 expanded)
%              Number of leaves         :    9 (  65 expanded)
%              Depth                    :   11
%              Number of atoms          :  208 (2059 expanded)
%              Number of equality atoms :   21 (  82 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t8_waybel_7,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_yellow_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v2_waybel_0(X2,X1)
            & v13_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ( v1_subset_1(X2,u1_struct_0(X1))
          <=> ~ r2_hidden(k3_yellow_0(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).

fof(d20_waybel_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v13_waybel_0(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( ( r2_hidden(X3,X2)
                        & r1_orders_2(X1,X3,X4) )
                     => r2_hidden(X4,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(t49_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( ! [X3] :
            ( m1_subset_1(X3,X1)
           => r2_hidden(X3,X2) )
       => X1 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(t44_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v1_yellow_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r1_orders_2(X1,k3_yellow_0(X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_yellow_0)).

fof(dt_k1_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(d11_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & v1_yellow_0(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v2_waybel_0(X2,X1)
              & v13_waybel_0(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => ( v1_subset_1(X2,u1_struct_0(X1))
            <=> ~ r2_hidden(k3_yellow_0(X1),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t8_waybel_7])).

fof(c_0_10,plain,(
    ! [X18,X19,X20,X21] :
      ( ( ~ v13_waybel_0(X19,X18)
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ r2_hidden(X20,X19)
        | ~ r1_orders_2(X18,X20,X21)
        | r2_hidden(X21,X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_orders_2(X18) )
      & ( m1_subset_1(esk2_2(X18,X19),u1_struct_0(X18))
        | v13_waybel_0(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_orders_2(X18) )
      & ( m1_subset_1(esk3_2(X18,X19),u1_struct_0(X18))
        | v13_waybel_0(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_orders_2(X18) )
      & ( r2_hidden(esk2_2(X18,X19),X19)
        | v13_waybel_0(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_orders_2(X18) )
      & ( r1_orders_2(X18,esk2_2(X18,X19),esk3_2(X18,X19))
        | v13_waybel_0(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_orders_2(X18) )
      & ( ~ r2_hidden(esk3_2(X18,X19),X19)
        | v13_waybel_0(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_orders_2(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).

fof(c_0_11,plain,(
    ! [X10,X11,X12] :
      ( ~ r2_hidden(X10,X11)
      | ~ m1_subset_1(X11,k1_zfmisc_1(X12))
      | m1_subset_1(X10,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_12,plain,(
    ! [X5,X6] :
      ( ( m1_subset_1(esk1_2(X5,X6),X5)
        | X5 = X6
        | ~ m1_subset_1(X6,k1_zfmisc_1(X5)) )
      & ( ~ r2_hidden(esk1_2(X5,X6),X6)
        | X5 = X6
        | ~ m1_subset_1(X6,k1_zfmisc_1(X5)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_subset_1])])])])).

fof(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v3_orders_2(esk4_0)
    & v4_orders_2(esk4_0)
    & v5_orders_2(esk4_0)
    & v1_yellow_0(esk4_0)
    & l1_orders_2(esk4_0)
    & ~ v1_xboole_0(esk5_0)
    & v2_waybel_0(esk5_0,esk4_0)
    & v13_waybel_0(esk5_0,esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & ( ~ v1_subset_1(esk5_0,u1_struct_0(esk4_0))
      | r2_hidden(k3_yellow_0(esk4_0),esk5_0) )
    & ( v1_subset_1(esk5_0,u1_struct_0(esk4_0))
      | ~ r2_hidden(k3_yellow_0(esk4_0),esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

cnf(c_0_14,plain,
    ( r2_hidden(X4,X1)
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(X3,X1)
    | ~ r1_orders_2(X2,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( m1_subset_1(esk1_2(X1,X2),X1)
    | X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X24,X25] :
      ( ( ~ v1_subset_1(X25,X24)
        | X25 != X24
        | ~ m1_subset_1(X25,k1_zfmisc_1(X24)) )
      & ( X25 = X24
        | v1_subset_1(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(X24)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X2)
    | ~ v13_waybel_0(X2,X3)
    | ~ r1_orders_2(X3,X4,X1)
    | ~ l1_orders_2(X3)
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3)) ),
    inference(csr,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( u1_struct_0(esk4_0) = esk5_0
    | m1_subset_1(esk1_2(u1_struct_0(esk4_0),esk5_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( X1 = X2
    | ~ r2_hidden(esk1_2(X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X16,X17] :
      ( v2_struct_0(X16)
      | ~ v5_orders_2(X16)
      | ~ v1_yellow_0(X16)
      | ~ l1_orders_2(X16)
      | ~ m1_subset_1(X17,u1_struct_0(X16))
      | r1_orders_2(X16,k3_yellow_0(X16),X17) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t44_yellow_0])])])])).

cnf(c_0_25,negated_conjecture,
    ( u1_struct_0(esk4_0) = esk5_0
    | r2_hidden(esk1_2(u1_struct_0(esk4_0),esk5_0),X1)
    | ~ v13_waybel_0(X1,esk4_0)
    | ~ r1_orders_2(esk4_0,X2,esk1_2(u1_struct_0(esk4_0),esk5_0))
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_26,negated_conjecture,
    ( v13_waybel_0(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,negated_conjecture,
    ( u1_struct_0(esk4_0) = esk5_0
    | ~ r2_hidden(esk1_2(u1_struct_0(esk4_0),esk5_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(k3_yellow_0(esk4_0),esk5_0)
    | ~ v1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,negated_conjecture,
    ( u1_struct_0(esk4_0) = esk5_0
    | v1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_17])).

cnf(c_0_30,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,k3_yellow_0(X1),X2)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( v1_yellow_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_32,negated_conjecture,
    ( v5_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_33,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_34,negated_conjecture,
    ( u1_struct_0(esk4_0) = esk5_0
    | ~ r1_orders_2(esk4_0,X1,esk1_2(u1_struct_0(esk4_0),esk5_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_17])]),c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( u1_struct_0(esk4_0) = esk5_0
    | r2_hidden(k3_yellow_0(esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( u1_struct_0(esk4_0) = esk5_0
    | r1_orders_2(esk4_0,k3_yellow_0(esk4_0),esk1_2(u1_struct_0(esk4_0),esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_20]),c_0_31]),c_0_32]),c_0_21])]),c_0_33])).

fof(c_0_37,plain,(
    ! [X14,X15] :
      ( ~ l1_orders_2(X14)
      | m1_subset_1(k1_yellow_0(X14,X15),u1_struct_0(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

fof(c_0_38,plain,(
    ! [X13] :
      ( ~ l1_orders_2(X13)
      | k3_yellow_0(X13) = k1_yellow_0(X13,k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).

cnf(c_0_39,plain,
    ( ~ v1_subset_1(X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_40,negated_conjecture,
    ( u1_struct_0(esk4_0) = esk5_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_41,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_42,plain,
    ( k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_43,plain,
    ( ~ v1_subset_1(X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_17,c_0_40])).

fof(c_0_45,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X8,X9)
      | v1_xboole_0(X9)
      | r2_hidden(X8,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_46,plain,
    ( m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( v1_subset_1(esk5_0,u1_struct_0(esk4_0))
    | ~ r2_hidden(k3_yellow_0(esk4_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_48,negated_conjecture,
    ( ~ v1_subset_1(esk5_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(k3_yellow_0(esk4_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_40]),c_0_21])])).

cnf(c_0_51,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_52,negated_conjecture,
    ( ~ r2_hidden(k3_yellow_0(esk4_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_40]),c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_52]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:12:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2S
% 0.19/0.38  # and selection function SelectNewComplexAHP.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.027 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t8_waybel_7, conjecture, ![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_7)).
% 0.19/0.38  fof(d20_waybel_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v13_waybel_0(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r2_hidden(X3,X2)&r1_orders_2(X1,X3,X4))=>r2_hidden(X4,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_waybel_0)).
% 0.19/0.38  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.19/0.38  fof(t49_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(![X3]:(m1_subset_1(X3,X1)=>r2_hidden(X3,X2))=>X1=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_subset_1)).
% 0.19/0.38  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 0.19/0.38  fof(t44_yellow_0, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r1_orders_2(X1,k3_yellow_0(X1),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_yellow_0)).
% 0.19/0.38  fof(dt_k1_yellow_0, axiom, ![X1, X2]:(l1_orders_2(X1)=>m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 0.19/0.38  fof(d11_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_yellow_0)).
% 0.19/0.38  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.19/0.38  fof(c_0_9, negated_conjecture, ~(![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2)))))), inference(assume_negation,[status(cth)],[t8_waybel_7])).
% 0.19/0.38  fof(c_0_10, plain, ![X18, X19, X20, X21]:((~v13_waybel_0(X19,X18)|(~m1_subset_1(X20,u1_struct_0(X18))|(~m1_subset_1(X21,u1_struct_0(X18))|(~r2_hidden(X20,X19)|~r1_orders_2(X18,X20,X21)|r2_hidden(X21,X19))))|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|~l1_orders_2(X18))&((m1_subset_1(esk2_2(X18,X19),u1_struct_0(X18))|v13_waybel_0(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|~l1_orders_2(X18))&((m1_subset_1(esk3_2(X18,X19),u1_struct_0(X18))|v13_waybel_0(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|~l1_orders_2(X18))&(((r2_hidden(esk2_2(X18,X19),X19)|v13_waybel_0(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|~l1_orders_2(X18))&(r1_orders_2(X18,esk2_2(X18,X19),esk3_2(X18,X19))|v13_waybel_0(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|~l1_orders_2(X18)))&(~r2_hidden(esk3_2(X18,X19),X19)|v13_waybel_0(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|~l1_orders_2(X18)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).
% 0.19/0.38  fof(c_0_11, plain, ![X10, X11, X12]:(~r2_hidden(X10,X11)|~m1_subset_1(X11,k1_zfmisc_1(X12))|m1_subset_1(X10,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.19/0.38  fof(c_0_12, plain, ![X5, X6]:((m1_subset_1(esk1_2(X5,X6),X5)|X5=X6|~m1_subset_1(X6,k1_zfmisc_1(X5)))&(~r2_hidden(esk1_2(X5,X6),X6)|X5=X6|~m1_subset_1(X6,k1_zfmisc_1(X5)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_subset_1])])])])).
% 0.19/0.38  fof(c_0_13, negated_conjecture, ((((((~v2_struct_0(esk4_0)&v3_orders_2(esk4_0))&v4_orders_2(esk4_0))&v5_orders_2(esk4_0))&v1_yellow_0(esk4_0))&l1_orders_2(esk4_0))&((((~v1_xboole_0(esk5_0)&v2_waybel_0(esk5_0,esk4_0))&v13_waybel_0(esk5_0,esk4_0))&m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))))&((~v1_subset_1(esk5_0,u1_struct_0(esk4_0))|r2_hidden(k3_yellow_0(esk4_0),esk5_0))&(v1_subset_1(esk5_0,u1_struct_0(esk4_0))|~r2_hidden(k3_yellow_0(esk4_0),esk5_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).
% 0.19/0.38  cnf(c_0_14, plain, (r2_hidden(X4,X1)|~v13_waybel_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~r2_hidden(X3,X1)|~r1_orders_2(X2,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  cnf(c_0_15, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_16, plain, (m1_subset_1(esk1_2(X1,X2),X1)|X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  fof(c_0_18, plain, ![X24, X25]:((~v1_subset_1(X25,X24)|X25!=X24|~m1_subset_1(X25,k1_zfmisc_1(X24)))&(X25=X24|v1_subset_1(X25,X24)|~m1_subset_1(X25,k1_zfmisc_1(X24)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.19/0.38  cnf(c_0_19, plain, (r2_hidden(X1,X2)|~v13_waybel_0(X2,X3)|~r1_orders_2(X3,X4,X1)|~l1_orders_2(X3)|~r2_hidden(X4,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X1,u1_struct_0(X3))), inference(csr,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.38  cnf(c_0_20, negated_conjecture, (u1_struct_0(esk4_0)=esk5_0|m1_subset_1(esk1_2(u1_struct_0(esk4_0),esk5_0),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.38  cnf(c_0_21, negated_conjecture, (l1_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_22, plain, (X1=X2|~r2_hidden(esk1_2(X1,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_23, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.38  fof(c_0_24, plain, ![X16, X17]:(v2_struct_0(X16)|~v5_orders_2(X16)|~v1_yellow_0(X16)|~l1_orders_2(X16)|(~m1_subset_1(X17,u1_struct_0(X16))|r1_orders_2(X16,k3_yellow_0(X16),X17))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t44_yellow_0])])])])).
% 0.19/0.38  cnf(c_0_25, negated_conjecture, (u1_struct_0(esk4_0)=esk5_0|r2_hidden(esk1_2(u1_struct_0(esk4_0),esk5_0),X1)|~v13_waybel_0(X1,esk4_0)|~r1_orders_2(esk4_0,X2,esk1_2(u1_struct_0(esk4_0),esk5_0))|~r2_hidden(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])])).
% 0.19/0.38  cnf(c_0_26, negated_conjecture, (v13_waybel_0(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_27, negated_conjecture, (u1_struct_0(esk4_0)=esk5_0|~r2_hidden(esk1_2(u1_struct_0(esk4_0),esk5_0),esk5_0)), inference(spm,[status(thm)],[c_0_22, c_0_17])).
% 0.19/0.38  cnf(c_0_28, negated_conjecture, (r2_hidden(k3_yellow_0(esk4_0),esk5_0)|~v1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_29, negated_conjecture, (u1_struct_0(esk4_0)=esk5_0|v1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_23, c_0_17])).
% 0.19/0.38  cnf(c_0_30, plain, (v2_struct_0(X1)|r1_orders_2(X1,k3_yellow_0(X1),X2)|~v5_orders_2(X1)|~v1_yellow_0(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.38  cnf(c_0_31, negated_conjecture, (v1_yellow_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_32, negated_conjecture, (v5_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_33, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_34, negated_conjecture, (u1_struct_0(esk4_0)=esk5_0|~r1_orders_2(esk4_0,X1,esk1_2(u1_struct_0(esk4_0),esk5_0))|~r2_hidden(X1,esk5_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_17])]), c_0_27])).
% 0.19/0.38  cnf(c_0_35, negated_conjecture, (u1_struct_0(esk4_0)=esk5_0|r2_hidden(k3_yellow_0(esk4_0),esk5_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.38  cnf(c_0_36, negated_conjecture, (u1_struct_0(esk4_0)=esk5_0|r1_orders_2(esk4_0,k3_yellow_0(esk4_0),esk1_2(u1_struct_0(esk4_0),esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_20]), c_0_31]), c_0_32]), c_0_21])]), c_0_33])).
% 0.19/0.38  fof(c_0_37, plain, ![X14, X15]:(~l1_orders_2(X14)|m1_subset_1(k1_yellow_0(X14,X15),u1_struct_0(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).
% 0.19/0.38  fof(c_0_38, plain, ![X13]:(~l1_orders_2(X13)|k3_yellow_0(X13)=k1_yellow_0(X13,k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).
% 0.19/0.38  cnf(c_0_39, plain, (~v1_subset_1(X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.38  cnf(c_0_40, negated_conjecture, (u1_struct_0(esk4_0)=esk5_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 0.19/0.38  cnf(c_0_41, plain, (m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.38  cnf(c_0_42, plain, (k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.38  cnf(c_0_43, plain, (~v1_subset_1(X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(X1))), inference(er,[status(thm)],[c_0_39])).
% 0.19/0.38  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk5_0))), inference(rw,[status(thm)],[c_0_17, c_0_40])).
% 0.19/0.38  fof(c_0_45, plain, ![X8, X9]:(~m1_subset_1(X8,X9)|(v1_xboole_0(X9)|r2_hidden(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.19/0.38  cnf(c_0_46, plain, (m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.38  cnf(c_0_47, negated_conjecture, (v1_subset_1(esk5_0,u1_struct_0(esk4_0))|~r2_hidden(k3_yellow_0(esk4_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_48, negated_conjecture, (~v1_subset_1(esk5_0,esk5_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.38  cnf(c_0_49, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.38  cnf(c_0_50, negated_conjecture, (m1_subset_1(k3_yellow_0(esk4_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_40]), c_0_21])])).
% 0.19/0.38  cnf(c_0_51, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_52, negated_conjecture, (~r2_hidden(k3_yellow_0(esk4_0),esk5_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_40]), c_0_48])).
% 0.19/0.38  cnf(c_0_53, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51]), c_0_52]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 54
% 0.19/0.38  # Proof object clause steps            : 35
% 0.19/0.38  # Proof object formula steps           : 19
% 0.19/0.38  # Proof object conjectures             : 25
% 0.19/0.38  # Proof object clause conjectures      : 22
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 19
% 0.19/0.38  # Proof object initial formulas used   : 9
% 0.19/0.38  # Proof object generating inferences   : 12
% 0.19/0.38  # Proof object simplifying inferences  : 20
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 9
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 27
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 27
% 0.19/0.38  # Processed clauses                    : 99
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 11
% 0.19/0.38  # ...remaining for further processing  : 88
% 0.19/0.38  # Other redundant clauses eliminated   : 1
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 1
% 0.19/0.38  # Backward-rewritten                   : 21
% 0.19/0.38  # Generated clauses                    : 62
% 0.19/0.38  # ...of the previous two non-trivial   : 60
% 0.19/0.38  # Contextual simplify-reflections      : 3
% 0.19/0.38  # Paramodulations                      : 61
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 1
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 38
% 0.19/0.38  #    Positive orientable unit clauses  : 10
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 4
% 0.19/0.38  #    Non-unit-clauses                  : 24
% 0.19/0.38  # Current number of unprocessed clauses: 15
% 0.19/0.38  # ...number of literals in the above   : 42
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 49
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 345
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 93
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 15
% 0.19/0.38  # Unit Clause-clause subsumption calls : 0
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 1
% 0.19/0.38  # BW rewrite match successes           : 1
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 3429
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.033 s
% 0.19/0.38  # System time              : 0.003 s
% 0.19/0.38  # Total time               : 0.036 s
% 0.19/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
