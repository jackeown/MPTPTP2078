%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1582+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:26 EST 2020

% Result     : Theorem 16.11s
% Output     : CNFRefutation 16.11s
% Verified   : 
% Statistics : Number of formulae       :  129 (2324 expanded)
%              Number of clauses        :  104 (1229 expanded)
%              Number of leaves         :   12 ( 523 expanded)
%              Depth                    :   24
%              Number of atoms          :  417 (14795 expanded)
%              Number of equality atoms :   85 (4138 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(d6_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k2_wellord1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_wellord1)).

fof(redefinition_k1_toler_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => k1_toler_1(X1,X2) = k2_wellord1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_toler_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(d14_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_yellow_0(X2,X1)
         => ( v4_yellow_0(X2,X1)
          <=> u1_orders_2(X2) = k1_toler_1(u1_orders_2(X1),u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_yellow_0)).

fof(t61_yellow_0,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( ( v4_yellow_0(X2,X1)
            & m1_yellow_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X2))
                         => ( ( X5 = X3
                              & X6 = X4
                              & r1_orders_2(X1,X3,X4)
                              & r2_hidden(X5,u1_struct_0(X2)) )
                           => r1_orders_2(X2,X5,X6) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_yellow_0)).

fof(t106_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

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

fof(dt_m1_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_yellow_0(X2,X1)
         => l1_orders_2(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_yellow_0)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(c_0_12,plain,(
    ! [X12,X13,X14,X15,X16,X17,X18,X19] :
      ( ( r2_hidden(X15,X12)
        | ~ r2_hidden(X15,X14)
        | X14 != k3_xboole_0(X12,X13) )
      & ( r2_hidden(X15,X13)
        | ~ r2_hidden(X15,X14)
        | X14 != k3_xboole_0(X12,X13) )
      & ( ~ r2_hidden(X16,X12)
        | ~ r2_hidden(X16,X13)
        | r2_hidden(X16,X14)
        | X14 != k3_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk1_3(X17,X18,X19),X19)
        | ~ r2_hidden(esk1_3(X17,X18,X19),X17)
        | ~ r2_hidden(esk1_3(X17,X18,X19),X18)
        | X19 = k3_xboole_0(X17,X18) )
      & ( r2_hidden(esk1_3(X17,X18,X19),X17)
        | r2_hidden(esk1_3(X17,X18,X19),X19)
        | X19 = k3_xboole_0(X17,X18) )
      & ( r2_hidden(esk1_3(X17,X18,X19),X18)
        | r2_hidden(esk1_3(X17,X18,X19),X19)
        | X19 = k3_xboole_0(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_13,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( k3_xboole_0(X1,X2) = X2
    | r2_hidden(esk1_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r2_hidden(esk1_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_16])).

cnf(c_0_19,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,X3)
    | r2_hidden(esk1_3(X1,k3_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_17,c_0_16])).

fof(c_0_20,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X21)
      | k2_wellord1(X21,X22) = k3_xboole_0(X21,k2_zfmisc_1(X22,X22)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_wellord1])])])).

cnf(c_0_21,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_22,plain,
    ( k2_wellord1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_23,plain,(
    ! [X29,X30] :
      ( ~ v1_relat_1(X29)
      | k1_toler_1(X29,X30) = k2_wellord1(X29,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_toler_1])])).

fof(c_0_24,plain,(
    ! [X7,X8,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | v1_relat_1(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_25,plain,(
    ! [X28] :
      ( ~ l1_orders_2(X28)
      | m1_subset_1(u1_orders_2(X28),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X28)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

cnf(c_0_26,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X1),k2_wellord1(X2,X1)) = k2_wellord1(X2,X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,plain,
    ( k1_toler_1(X1,X2) = k2_wellord1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_28,plain,(
    ! [X10,X11] :
      ( ( ~ v4_yellow_0(X11,X10)
        | u1_orders_2(X11) = k1_toler_1(u1_orders_2(X10),u1_struct_0(X11))
        | ~ m1_yellow_0(X11,X10)
        | ~ l1_orders_2(X10) )
      & ( u1_orders_2(X11) != k1_toler_1(u1_orders_2(X10),u1_struct_0(X11))
        | v4_yellow_0(X11,X10)
        | ~ m1_yellow_0(X11,X10)
        | ~ l1_orders_2(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_yellow_0])])])])).

cnf(c_0_29,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_31,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2] :
            ( ( v4_yellow_0(X2,X1)
              & m1_yellow_0(X2,X1) )
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X2))
                       => ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X2))
                           => ( ( X5 = X3
                                & X6 = X4
                                & r1_orders_2(X1,X3,X4)
                                & r2_hidden(X5,u1_struct_0(X2)) )
                             => r1_orders_2(X2,X5,X6) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t61_yellow_0])).

cnf(c_0_32,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_34,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X1),k1_toler_1(X2,X1)) = k1_toler_1(X2,X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_35,plain,
    ( u1_orders_2(X1) = k1_toler_1(u1_orders_2(X2),u1_struct_0(X1))
    | ~ v4_yellow_0(X1,X2)
    | ~ m1_yellow_0(X1,X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( v1_relat_1(u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_37,negated_conjecture,
    ( l1_orders_2(esk2_0)
    & v4_yellow_0(esk3_0,esk2_0)
    & m1_yellow_0(esk3_0,esk2_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk5_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk6_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk7_0,u1_struct_0(esk3_0))
    & esk6_0 = esk4_0
    & esk7_0 = esk5_0
    & r1_orders_2(esk2_0,esk4_0,esk5_0)
    & r2_hidden(esk6_0,u1_struct_0(esk3_0))
    & ~ r1_orders_2(esk3_0,esk6_0,esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).

cnf(c_0_38,plain,
    ( k3_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( k3_xboole_0(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)),u1_orders_2(X1)) = u1_orders_2(X1)
    | ~ v4_yellow_0(X1,X2)
    | ~ m1_yellow_0(X1,X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( v4_yellow_0(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( m1_yellow_0(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r2_hidden(esk1_3(X1,X2,X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_38]),c_0_38])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_47,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X3,X4)
    | r2_hidden(esk1_3(X3,X4,k3_xboole_0(X1,X2)),X4)
    | r2_hidden(esk1_3(X3,X4,k3_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_13])).

cnf(c_0_48,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = X3
    | ~ r2_hidden(esk1_3(k3_xboole_0(X1,X2),X3,X3),X2)
    | ~ r2_hidden(esk1_3(k3_xboole_0(X1,X2),X3,X3),X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0)),u1_orders_2(esk3_0)) = u1_orders_2(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_44])])).

cnf(c_0_50,plain,
    ( X1 = k3_xboole_0(X2,k3_xboole_0(X3,X4))
    | r2_hidden(esk1_3(X2,k3_xboole_0(X3,X4),X1),X1)
    | r2_hidden(esk1_3(X2,k3_xboole_0(X3,X4),X1),X4) ),
    inference(spm,[status(thm)],[c_0_17,c_0_13])).

cnf(c_0_51,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = X1
    | ~ r2_hidden(esk1_3(X1,k3_xboole_0(X2,X3),X1),X3)
    | ~ r2_hidden(esk1_3(X1,k3_xboole_0(X2,X3),X1),X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_40])).

cnf(c_0_52,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,X2)
    | r2_hidden(esk1_3(k3_xboole_0(X1,X2),X3,k3_xboole_0(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_38])).

cnf(c_0_53,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X3,k3_xboole_0(X4,X5))
    | r2_hidden(esk1_3(X3,k3_xboole_0(X4,X5),k3_xboole_0(X1,X2)),X2)
    | r2_hidden(esk1_3(X3,k3_xboole_0(X4,X5),k3_xboole_0(X1,X2)),X4) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k2_wellord1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_22])).

cnf(c_0_55,plain,
    ( k3_xboole_0(k2_wellord1(X1,X2),X3) = X3
    | ~ r2_hidden(esk1_3(k2_wellord1(X1,X2),X3,X3),k2_zfmisc_1(X2,X2))
    | ~ r2_hidden(esk1_3(k2_wellord1(X1,X2),X3,X3),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_22])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0)))
    | ~ r2_hidden(X1,u1_orders_2(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_49])).

cnf(c_0_57,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X3,k3_xboole_0(X4,X5))
    | r2_hidden(esk1_3(X3,k3_xboole_0(X4,X5),k3_xboole_0(X1,X2)),X5)
    | r2_hidden(esk1_3(X3,k3_xboole_0(X4,X5),k3_xboole_0(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_50])).

cnf(c_0_58,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1)) = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1),k3_xboole_0(X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_59,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X3,k3_xboole_0(X2,X4))
    | r2_hidden(esk1_3(X3,k3_xboole_0(X2,X4),k3_xboole_0(X1,X2)),X2) ),
    inference(ef,[status(thm)],[c_0_53])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_toler_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_27])).

cnf(c_0_61,negated_conjecture,
    ( k3_xboole_0(k2_wellord1(X1,u1_struct_0(esk3_0)),X2) = X2
    | ~ r2_hidden(esk1_3(k2_wellord1(X1,u1_struct_0(esk3_0)),X2,X2),u1_orders_2(esk3_0))
    | ~ r2_hidden(esk1_3(k2_wellord1(X1,u1_struct_0(esk3_0)),X2,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_62,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X3,k3_xboole_0(X4,X1))
    | r2_hidden(esk1_3(X3,k3_xboole_0(X4,X1),k3_xboole_0(X1,X2)),X1) ),
    inference(ef,[status(thm)],[c_0_57])).

cnf(c_0_63,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_18,c_0_16])).

cnf(c_0_64,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,u1_orders_2(X2))
    | ~ r2_hidden(X1,u1_orders_2(X3))
    | ~ v4_yellow_0(X3,X2)
    | ~ m1_yellow_0(X3,X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_35]),c_0_36])).

cnf(c_0_66,negated_conjecture,
    ( k3_xboole_0(k2_wellord1(X1,u1_struct_0(esk3_0)),u1_orders_2(esk3_0)) = u1_orders_2(esk3_0)
    | ~ r2_hidden(esk1_3(k2_wellord1(X1,u1_struct_0(esk3_0)),u1_orders_2(esk3_0),u1_orders_2(esk3_0)),X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63]),c_0_63]),c_0_63]),c_0_63])).

cnf(c_0_67,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_64]),c_0_64])).

cnf(c_0_68,plain,
    ( k3_xboole_0(X1,u1_orders_2(X2)) = u1_orders_2(X2)
    | r2_hidden(esk1_3(X1,u1_orders_2(X2),u1_orders_2(X2)),u1_orders_2(X3))
    | ~ v4_yellow_0(X2,X3)
    | ~ m1_yellow_0(X2,X3)
    | ~ l1_orders_2(X3) ),
    inference(spm,[status(thm)],[c_0_65,c_0_16])).

cnf(c_0_69,plain,
    ( X1 = X2
    | ~ r2_hidden(esk1_3(X2,X2,X1),X1)
    | ~ r2_hidden(esk1_3(X2,X2,X1),X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_63])).

cnf(c_0_70,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = X3
    | r2_hidden(esk1_3(X1,k3_xboole_0(X2,X3),X3),X3) ),
    inference(ef,[status(thm)],[c_0_50])).

cnf(c_0_71,negated_conjecture,
    ( k3_xboole_0(u1_orders_2(esk3_0),k2_wellord1(X1,u1_struct_0(esk3_0))) = u1_orders_2(esk3_0)
    | ~ r2_hidden(esk1_3(k2_wellord1(X1,u1_struct_0(esk3_0)),u1_orders_2(esk3_0),u1_orders_2(esk3_0)),X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( k3_xboole_0(X1,u1_orders_2(esk3_0)) = u1_orders_2(esk3_0)
    | r2_hidden(esk1_3(X1,u1_orders_2(esk3_0),u1_orders_2(esk3_0)),u1_orders_2(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_42]),c_0_43]),c_0_44])])).

cnf(c_0_73,plain,
    ( k2_wellord1(X1,X2) = k3_xboole_0(X3,X4)
    | r2_hidden(esk1_3(X3,X4,k2_wellord1(X1,X2)),X4)
    | r2_hidden(esk1_3(X3,X4,k2_wellord1(X1,X2)),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_13])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | X4 != k3_xboole_0(X3,X2)
    | ~ r2_hidden(X1,X4) ),
    inference(spm,[status(thm)],[c_0_14,c_0_64])).

cnf(c_0_75,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r2_hidden(esk1_3(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),X2),k3_xboole_0(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_63])])).

cnf(c_0_76,negated_conjecture,
    ( k3_xboole_0(u1_orders_2(esk3_0),k2_wellord1(u1_orders_2(esk2_0),u1_struct_0(esk3_0))) = u1_orders_2(esk3_0)
    | ~ v1_relat_1(u1_orders_2(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_67])])).

cnf(c_0_77,plain,
    ( k2_wellord1(u1_orders_2(X1),X2) = k3_xboole_0(X3,X4)
    | r2_hidden(esk1_3(X3,X4,k2_wellord1(u1_orders_2(X1),X2)),u1_orders_2(X1))
    | r2_hidden(esk1_3(X3,X4,k2_wellord1(u1_orders_2(X1),X2)),X4)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_36])).

cnf(c_0_78,plain,
    ( r2_hidden(X1,k2_wellord1(X2,X3))
    | X4 != k3_xboole_0(k2_zfmisc_1(X3,X3),X2)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_74,c_0_22])).

cnf(c_0_79,plain,
    ( r2_hidden(X1,k2_wellord1(X2,X3))
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X3))
    | ~ r2_hidden(X1,X2)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_22])).

cnf(c_0_80,negated_conjecture,
    ( k2_wellord1(u1_orders_2(esk2_0),u1_struct_0(esk3_0)) = u1_orders_2(esk3_0)
    | ~ r2_hidden(esk1_3(u1_orders_2(esk3_0),u1_orders_2(esk3_0),k2_wellord1(u1_orders_2(esk2_0),u1_struct_0(esk3_0))),u1_orders_2(esk3_0))
    | ~ v1_relat_1(u1_orders_2(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_81,negated_conjecture,
    ( k2_wellord1(u1_orders_2(esk2_0),X1) = k3_xboole_0(X2,X3)
    | r2_hidden(esk1_3(X2,X3,k2_wellord1(u1_orders_2(esk2_0),X1)),u1_orders_2(esk2_0))
    | r2_hidden(esk1_3(X2,X3,k2_wellord1(u1_orders_2(esk2_0),X1)),X3) ),
    inference(spm,[status(thm)],[c_0_77,c_0_44])).

cnf(c_0_82,plain,
    ( r2_hidden(X1,k2_wellord1(X2,X3))
    | X4 != k3_xboole_0(X2,k2_zfmisc_1(X3,X3))
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_78,c_0_67])).

cnf(c_0_83,plain,
    ( k3_xboole_0(X1,k2_zfmisc_1(X2,X2)) = k3_xboole_0(X3,X4)
    | r2_hidden(esk1_3(X3,X4,k3_xboole_0(X1,k2_zfmisc_1(X2,X2))),k2_wellord1(X5,X2))
    | r2_hidden(esk1_3(X3,X4,k3_xboole_0(X1,k2_zfmisc_1(X2,X2))),X4)
    | ~ r2_hidden(esk1_3(X3,X4,k3_xboole_0(X1,k2_zfmisc_1(X2,X2))),X5)
    | ~ v1_relat_1(X5) ),
    inference(spm,[status(thm)],[c_0_79,c_0_47])).

cnf(c_0_84,negated_conjecture,
    ( k2_wellord1(u1_orders_2(esk2_0),u1_struct_0(esk3_0)) = u1_orders_2(esk3_0)
    | r2_hidden(esk1_3(u1_orders_2(esk3_0),u1_orders_2(esk3_0),k2_wellord1(u1_orders_2(esk2_0),u1_struct_0(esk3_0))),u1_orders_2(esk2_0))
    | ~ v1_relat_1(u1_orders_2(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_63])])).

fof(c_0_85,plain,(
    ! [X31,X32,X33,X34] :
      ( ( r2_hidden(X31,X33)
        | ~ r2_hidden(k4_tarski(X31,X32),k2_zfmisc_1(X33,X34)) )
      & ( r2_hidden(X32,X34)
        | ~ r2_hidden(k4_tarski(X31,X32),k2_zfmisc_1(X33,X34)) )
      & ( ~ r2_hidden(X31,X33)
        | ~ r2_hidden(X32,X34)
        | r2_hidden(k4_tarski(X31,X32),k2_zfmisc_1(X33,X34)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_zfmisc_1])])])).

cnf(c_0_86,plain,
    ( r2_hidden(X1,k1_toler_1(X2,X3))
    | X4 != k3_xboole_0(X2,k2_zfmisc_1(X3,X3))
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_82,c_0_27])).

cnf(c_0_87,plain,
    ( k2_wellord1(X1,X2) = k3_xboole_0(X3,X4)
    | r2_hidden(esk1_3(X3,X4,k2_wellord1(X1,X2)),k2_wellord1(X5,X2))
    | r2_hidden(esk1_3(X3,X4,k2_wellord1(X1,X2)),X4)
    | ~ r2_hidden(esk1_3(X3,X4,k2_wellord1(X1,X2)),X5)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_83,c_0_22])).

cnf(c_0_88,negated_conjecture,
    ( k2_wellord1(u1_orders_2(esk2_0),u1_struct_0(esk3_0)) = u1_orders_2(esk3_0)
    | r2_hidden(esk1_3(u1_orders_2(esk3_0),u1_orders_2(esk3_0),k2_wellord1(u1_orders_2(esk2_0),u1_struct_0(esk3_0))),u1_orders_2(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_36]),c_0_44])])).

cnf(c_0_89,negated_conjecture,
    ( r2_hidden(X1,k2_wellord1(u1_orders_2(esk2_0),u1_struct_0(esk3_0)))
    | ~ r2_hidden(X1,u1_orders_2(esk3_0))
    | ~ v1_relat_1(u1_orders_2(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_76])).

cnf(c_0_90,plain,
    ( r2_hidden(X1,X2)
    | X2 != k2_wellord1(X3,X4)
    | ~ r2_hidden(X1,k2_zfmisc_1(X4,X4))
    | ~ r2_hidden(X1,X3)
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_33,c_0_22])).

cnf(c_0_91,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

fof(c_0_92,plain,(
    ! [X23,X24,X25] :
      ( ( ~ r1_orders_2(X23,X24,X25)
        | r2_hidden(k4_tarski(X24,X25),u1_orders_2(X23))
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | ~ l1_orders_2(X23) )
      & ( ~ r2_hidden(k4_tarski(X24,X25),u1_orders_2(X23))
        | r1_orders_2(X23,X24,X25)
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | ~ l1_orders_2(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).

cnf(c_0_93,plain,
    ( r2_hidden(X1,k1_toler_1(X2,X3))
    | X4 != k2_wellord1(X2,X3)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_86,c_0_22])).

cnf(c_0_94,negated_conjecture,
    ( k2_wellord1(u1_orders_2(esk2_0),u1_struct_0(esk3_0)) = u1_orders_2(esk3_0)
    | r2_hidden(esk1_3(u1_orders_2(esk3_0),u1_orders_2(esk3_0),k2_wellord1(u1_orders_2(esk2_0),u1_struct_0(esk3_0))),k2_wellord1(u1_orders_2(esk2_0),u1_struct_0(esk3_0)))
    | ~ v1_relat_1(u1_orders_2(esk2_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_63])]),c_0_89])).

cnf(c_0_95,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | X3 != k2_wellord1(X4,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X4)
    | ~ r2_hidden(X2,X5)
    | ~ r2_hidden(X1,X5)
    | ~ v1_relat_1(X4) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_96,plain,
    ( r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_97,plain,
    ( r2_hidden(X1,u1_orders_2(X2))
    | X3 != k2_wellord1(u1_orders_2(X4),u1_struct_0(X2))
    | ~ r2_hidden(X1,X3)
    | ~ v4_yellow_0(X2,X4)
    | ~ m1_yellow_0(X2,X4)
    | ~ l1_orders_2(X4) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_35]),c_0_36])).

cnf(c_0_98,negated_conjecture,
    ( k2_wellord1(u1_orders_2(esk2_0),u1_struct_0(esk3_0)) = u1_orders_2(esk3_0)
    | r2_hidden(esk1_3(u1_orders_2(esk3_0),u1_orders_2(esk3_0),k2_wellord1(u1_orders_2(esk2_0),u1_struct_0(esk3_0))),k2_wellord1(u1_orders_2(esk2_0),u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_36]),c_0_44])])).

cnf(c_0_99,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | X3 != k2_wellord1(u1_orders_2(X4),X5)
    | ~ r1_orders_2(X4,X1,X2)
    | ~ r2_hidden(X2,X5)
    | ~ r2_hidden(X1,X5)
    | ~ l1_orders_2(X4)
    | ~ m1_subset_1(X2,u1_struct_0(X4))
    | ~ m1_subset_1(X1,u1_struct_0(X4)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_36])).

cnf(c_0_100,plain,
    ( r2_hidden(X1,u1_orders_2(X2))
    | ~ r2_hidden(X1,k2_wellord1(u1_orders_2(X3),u1_struct_0(X2)))
    | ~ v4_yellow_0(X2,X3)
    | ~ m1_yellow_0(X2,X3)
    | ~ l1_orders_2(X3) ),
    inference(er,[status(thm)],[c_0_97])).

cnf(c_0_101,negated_conjecture,
    ( k2_wellord1(u1_orders_2(esk2_0),u1_struct_0(esk3_0)) = u1_orders_2(esk3_0)
    | ~ r2_hidden(esk1_3(u1_orders_2(esk3_0),u1_orders_2(esk3_0),k2_wellord1(u1_orders_2(esk2_0),u1_struct_0(esk3_0))),u1_orders_2(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_98]),c_0_63])])).

fof(c_0_102,plain,(
    ! [X26,X27] :
      ( ~ l1_orders_2(X26)
      | ~ m1_yellow_0(X27,X26)
      | l1_orders_2(X27) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_yellow_0])])])).

fof(c_0_103,plain,(
    ! [X37,X38] :
      ( ~ r2_hidden(X37,X38)
      | ~ v1_xboole_0(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_104,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_wellord1(u1_orders_2(X3),X4))
    | ~ r1_orders_2(X3,X1,X2)
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X4)
    | ~ l1_orders_2(X3)
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3)) ),
    inference(er,[status(thm)],[c_0_99])).

cnf(c_0_105,negated_conjecture,
    ( k2_wellord1(u1_orders_2(esk2_0),u1_struct_0(esk3_0)) = u1_orders_2(esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_98]),c_0_42]),c_0_43]),c_0_44])]),c_0_101])).

cnf(c_0_106,plain,
    ( l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ m1_yellow_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

fof(c_0_107,plain,(
    ! [X35,X36] :
      ( ~ m1_subset_1(X35,X36)
      | v1_xboole_0(X36)
      | r2_hidden(X35,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_108,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_109,negated_conjecture,
    ( r2_hidden(esk6_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_110,plain,
    ( r1_orders_2(X3,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_111,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(esk3_0))
    | ~ r1_orders_2(esk2_0,X1,X2)
    | ~ r2_hidden(X2,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_44])])).

cnf(c_0_112,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_43]),c_0_44])])).

cnf(c_0_113,negated_conjecture,
    ( r1_orders_2(esk2_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_114,negated_conjecture,
    ( esk6_0 = esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_115,negated_conjecture,
    ( esk7_0 = esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_116,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_107])).

cnf(c_0_117,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_118,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_119,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_120,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_121,negated_conjecture,
    ( ~ r1_orders_2(esk3_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_122,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,X2)
    | ~ r1_orders_2(esk2_0,X1,X2)
    | ~ r2_hidden(X2,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_112])])).

cnf(c_0_123,negated_conjecture,
    ( r1_orders_2(esk2_0,esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_113,c_0_114]),c_0_115])).

cnf(c_0_124,negated_conjecture,
    ( r2_hidden(esk7_0,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_117]),c_0_118])).

cnf(c_0_125,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_126,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_119,c_0_115])).

cnf(c_0_127,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_120,c_0_114])).

cnf(c_0_128,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_122]),c_0_123]),c_0_124]),c_0_109]),c_0_117]),c_0_125]),c_0_126]),c_0_127])]),
    [proof]).

%------------------------------------------------------------------------------
