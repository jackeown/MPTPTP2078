%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow_0__t61_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:46 EDT 2019

% Result     : Theorem 151.28s
% Output     : CNFRefutation 151.28s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 153 expanded)
%              Number of clauses        :   49 (  62 expanded)
%              Number of leaves         :   12 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :  222 ( 980 expanded)
%              Number of equality atoms :   30 ( 152 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/yellow_0__t61_yellow_0.p',t61_yellow_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t61_yellow_0.p',t2_subset)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t61_yellow_0.p',t7_boole)).

fof(dt_m1_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_yellow_0(X2,X1)
         => l1_orders_2(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t61_yellow_0.p',dt_m1_yellow_0)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t61_yellow_0.p',dt_u1_orders_2)).

fof(t106_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t61_yellow_0.p',t106_zfmisc_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t61_yellow_0.p',cc1_relset_1)).

fof(d9_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_orders_2(X1,X2,X3)
              <=> r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t61_yellow_0.p',d9_orders_2)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t61_yellow_0.p',d4_xboole_0)).

fof(redefinition_k1_toler_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => k1_toler_1(X1,X2) = k2_wellord1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t61_yellow_0.p',redefinition_k1_toler_1)).

fof(d14_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_yellow_0(X2,X1)
         => ( v4_yellow_0(X2,X1)
          <=> u1_orders_2(X2) = k1_toler_1(u1_orders_2(X1),u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t61_yellow_0.p',d14_yellow_0)).

fof(d6_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k2_wellord1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t61_yellow_0.p',d6_wellord1)).

fof(c_0_12,negated_conjecture,(
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

fof(c_0_13,plain,(
    ! [X57,X58] :
      ( ~ m1_subset_1(X57,X58)
      | v1_xboole_0(X58)
      | r2_hidden(X57,X58) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_14,negated_conjecture,
    ( l1_orders_2(esk1_0)
    & v4_yellow_0(esk2_0,esk1_0)
    & m1_yellow_0(esk2_0,esk1_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk4_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk5_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk6_0,u1_struct_0(esk2_0))
    & esk5_0 = esk3_0
    & esk6_0 = esk4_0
    & r1_orders_2(esk1_0,esk3_0,esk4_0)
    & r2_hidden(esk5_0,u1_struct_0(esk2_0))
    & ~ r1_orders_2(esk2_0,esk5_0,esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_15,plain,(
    ! [X68,X69] :
      ( ~ r2_hidden(X68,X69)
      | ~ v1_xboole_0(X69) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_16,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X38,X39] :
      ( ~ l1_orders_2(X38)
      | ~ m1_yellow_0(X39,X38)
      | l1_orders_2(X39) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_yellow_0])])])).

cnf(c_0_19,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | r2_hidden(esk6_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_21,plain,(
    ! [X40] :
      ( ~ l1_orders_2(X40)
      | m1_subset_1(u1_orders_2(X40),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X40),u1_struct_0(X40)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

cnf(c_0_22,plain,
    ( l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ m1_yellow_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_24,plain,(
    ! [X50,X51,X52,X53] :
      ( ( r2_hidden(X50,X52)
        | ~ r2_hidden(k4_tarski(X50,X51),k2_zfmisc_1(X52,X53)) )
      & ( r2_hidden(X51,X53)
        | ~ r2_hidden(k4_tarski(X50,X51),k2_zfmisc_1(X52,X53)) )
      & ( ~ r2_hidden(X50,X52)
        | ~ r2_hidden(X51,X53)
        | r2_hidden(k4_tarski(X50,X51),k2_zfmisc_1(X52,X53)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_zfmisc_1])])])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk6_0,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk5_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_27,plain,(
    ! [X72,X73,X74] :
      ( ~ m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(X72,X73)))
      | v1_relat_1(X74) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_28,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_29,plain,(
    ! [X30,X31,X32] :
      ( ( ~ r1_orders_2(X30,X31,X32)
        | r2_hidden(k4_tarski(X31,X32),u1_orders_2(X30))
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | ~ l1_orders_2(X30) )
      & ( ~ r2_hidden(k4_tarski(X31,X32),u1_orders_2(X30))
        | r1_orders_2(X30,X31,X32)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | ~ l1_orders_2(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).

cnf(c_0_30,negated_conjecture,
    ( l1_orders_2(X1)
    | ~ m1_yellow_0(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( m1_yellow_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_32,plain,(
    ! [X19,X20,X21,X22,X23,X24,X25,X26] :
      ( ( r2_hidden(X22,X19)
        | ~ r2_hidden(X22,X21)
        | X21 != k3_xboole_0(X19,X20) )
      & ( r2_hidden(X22,X20)
        | ~ r2_hidden(X22,X21)
        | X21 != k3_xboole_0(X19,X20) )
      & ( ~ r2_hidden(X23,X19)
        | ~ r2_hidden(X23,X20)
        | r2_hidden(X23,X21)
        | X21 != k3_xboole_0(X19,X20) )
      & ( ~ r2_hidden(esk7_3(X24,X25,X26),X26)
        | ~ r2_hidden(esk7_3(X24,X25,X26),X24)
        | ~ r2_hidden(esk7_3(X24,X25,X26),X25)
        | X26 = k3_xboole_0(X24,X25) )
      & ( r2_hidden(esk7_3(X24,X25,X26),X24)
        | r2_hidden(esk7_3(X24,X25,X26),X26)
        | X26 = k3_xboole_0(X24,X25) )
      & ( r2_hidden(esk7_3(X24,X25,X26),X25)
        | r2_hidden(esk7_3(X24,X25,X26),X26)
        | X26 = k3_xboole_0(X24,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_33,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk6_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_35,plain,(
    ! [X48,X49] :
      ( ~ v1_relat_1(X48)
      | k1_toler_1(X48,X49) = k2_wellord1(X48,X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_toler_1])])).

cnf(c_0_36,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(u1_orders_2(esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_23])).

fof(c_0_38,plain,(
    ! [X17,X18] :
      ( ( ~ v4_yellow_0(X18,X17)
        | u1_orders_2(X18) = k1_toler_1(u1_orders_2(X17),u1_struct_0(X18))
        | ~ m1_yellow_0(X18,X17)
        | ~ l1_orders_2(X17) )
      & ( u1_orders_2(X18) != k1_toler_1(u1_orders_2(X17),u1_struct_0(X18))
        | v4_yellow_0(X18,X17)
        | ~ m1_yellow_0(X18,X17)
        | ~ l1_orders_2(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_yellow_0])])])])).

cnf(c_0_39,plain,
    ( r1_orders_2(X3,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk6_0),k2_zfmisc_1(X2,u1_struct_0(esk2_0)))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_43,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X28)
      | k2_wellord1(X28,X29) = k3_xboole_0(X28,k2_zfmisc_1(X29,X29)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_wellord1])])])).

cnf(c_0_44,plain,
    ( k1_toler_1(X1,X2) = k2_wellord1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( v1_relat_1(u1_orders_2(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_46,plain,
    ( u1_orders_2(X1) = k1_toler_1(u1_orders_2(X2),u1_struct_0(X1))
    | ~ v4_yellow_0(X1,X2)
    | ~ m1_yellow_0(X1,X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(esk2_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,plain,
    ( r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_50,negated_conjecture,
    ( esk6_0 = esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_0,esk6_0),k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_26])).

cnf(c_0_53,plain,
    ( k2_wellord1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,negated_conjecture,
    ( k2_wellord1(u1_orders_2(esk1_0),X1) = k1_toler_1(u1_orders_2(esk1_0),X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_55,negated_conjecture,
    ( k1_toler_1(u1_orders_2(esk1_0),u1_struct_0(X1)) = u1_orders_2(X1)
    | ~ m1_yellow_0(X1,esk1_0)
    | ~ v4_yellow_0(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_23])).

cnf(c_0_56,negated_conjecture,
    ( v4_yellow_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_57,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk6_0)
    | ~ r2_hidden(k4_tarski(X1,esk6_0),u1_orders_2(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_17])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_59,negated_conjecture,
    ( ~ r1_orders_2(esk2_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(esk1_0))
    | ~ r1_orders_2(esk1_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_23])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_62,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_63,negated_conjecture,
    ( esk5_0 = esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_0,esk6_0),k3_xboole_0(X1,k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))
    | ~ r2_hidden(k4_tarski(esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_66,negated_conjecture,
    ( k3_xboole_0(u1_orders_2(esk1_0),k2_zfmisc_1(X1,X1)) = k1_toler_1(u1_orders_2(esk1_0),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_45]),c_0_54])).

cnf(c_0_67,negated_conjecture,
    ( k1_toler_1(u1_orders_2(esk1_0),u1_struct_0(esk2_0)) = u1_orders_2(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_31]),c_0_56])])).

cnf(c_0_68,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk5_0,esk6_0),u1_orders_2(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk6_0),u1_orders_2(esk1_0))
    | ~ r1_orders_2(esk1_0,X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_70,negated_conjecture,
    ( r1_orders_2(esk1_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63]),c_0_50])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_64,c_0_63])).

cnf(c_0_72,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk5_0,esk6_0),u1_orders_2(esk1_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_68])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])]),c_0_72]),
    [proof]).
%------------------------------------------------------------------------------
