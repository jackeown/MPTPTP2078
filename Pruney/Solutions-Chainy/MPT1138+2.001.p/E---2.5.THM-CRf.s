%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:30 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 234 expanded)
%              Number of clauses        :   40 (  91 expanded)
%              Number of leaves         :    9 (  55 expanded)
%              Depth                    :   11
%              Number of atoms          :  192 (1171 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t26_orders_2,conjecture,(
    ! [X1] :
      ( ( v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( ( r1_orders_2(X1,X2,X3)
                      & r1_orders_2(X1,X3,X4) )
                   => r1_orders_2(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_orders_2)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(d9_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_orders_2(X1,X2,X3)
              <=> r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(d8_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r8_relat_2(X1,X2)
        <=> ! [X3,X4,X5] :
              ( ( r2_hidden(X3,X2)
                & r2_hidden(X4,X2)
                & r2_hidden(X5,X2)
                & r2_hidden(k4_tarski(X3,X4),X1)
                & r2_hidden(k4_tarski(X4,X5),X1) )
             => r2_hidden(k4_tarski(X3,X5),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_2)).

fof(d5_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v4_orders_2(X1)
      <=> r8_relat_2(u1_orders_2(X1),u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_orders_2)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( v4_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( ( r1_orders_2(X1,X2,X3)
                        & r1_orders_2(X1,X3,X4) )
                     => r1_orders_2(X1,X2,X4) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t26_orders_2])).

fof(c_0_10,plain,(
    ! [X33] :
      ( ~ l1_orders_2(X33)
      | m1_subset_1(u1_orders_2(X33),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X33)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_11,negated_conjecture,
    ( v4_orders_2(esk5_0)
    & l1_orders_2(esk5_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk5_0))
    & m1_subset_1(esk7_0,u1_struct_0(esk5_0))
    & m1_subset_1(esk8_0,u1_struct_0(esk5_0))
    & r1_orders_2(esk5_0,esk6_0,esk7_0)
    & r1_orders_2(esk5_0,esk7_0,esk8_0)
    & ~ r1_orders_2(esk5_0,esk6_0,esk8_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_12,plain,(
    ! [X17,X18,X19] :
      ( ~ v1_xboole_0(X17)
      | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X18,X17)))
      | v1_xboole_0(X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

cnf(c_0_13,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(u1_orders_2(esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_17,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(X12,X13)
      | v1_xboole_0(X13)
      | r2_hidden(X12,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_18,plain,(
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

cnf(c_0_19,negated_conjecture,
    ( v1_xboole_0(u1_orders_2(esk5_0))
    | ~ v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_23,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
      | v1_relat_1(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_24,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,X7)
      | ~ v1_xboole_0(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_25,negated_conjecture,
    ( v1_xboole_0(u1_orders_2(esk5_0))
    | r2_hidden(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_27,plain,(
    ! [X20,X21,X22,X23,X24,X25] :
      ( ( ~ r8_relat_2(X20,X21)
        | ~ r2_hidden(X22,X21)
        | ~ r2_hidden(X23,X21)
        | ~ r2_hidden(X24,X21)
        | ~ r2_hidden(k4_tarski(X22,X23),X20)
        | ~ r2_hidden(k4_tarski(X23,X24),X20)
        | r2_hidden(k4_tarski(X22,X24),X20)
        | ~ v1_relat_1(X20) )
      & ( r2_hidden(esk2_2(X20,X25),X25)
        | r8_relat_2(X20,X25)
        | ~ v1_relat_1(X20) )
      & ( r2_hidden(esk3_2(X20,X25),X25)
        | r8_relat_2(X20,X25)
        | ~ v1_relat_1(X20) )
      & ( r2_hidden(esk4_2(X20,X25),X25)
        | r8_relat_2(X20,X25)
        | ~ v1_relat_1(X20) )
      & ( r2_hidden(k4_tarski(esk2_2(X20,X25),esk3_2(X20,X25)),X20)
        | r8_relat_2(X20,X25)
        | ~ v1_relat_1(X20) )
      & ( r2_hidden(k4_tarski(esk3_2(X20,X25),esk4_2(X20,X25)),X20)
        | r8_relat_2(X20,X25)
        | ~ v1_relat_1(X20) )
      & ( ~ r2_hidden(k4_tarski(esk2_2(X20,X25),esk4_2(X20,X25)),X20)
        | r8_relat_2(X20,X25)
        | ~ v1_relat_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_2])])])])])])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk8_0),u1_orders_2(esk5_0))
    | ~ r1_orders_2(esk5_0,X1,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_14])])).

cnf(c_0_29,negated_conjecture,
    ( r1_orders_2(esk5_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_30,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( v1_xboole_0(u1_orders_2(esk5_0))
    | r2_hidden(esk8_0,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_22])).

fof(c_0_33,plain,(
    ! [X29] :
      ( ( ~ v4_orders_2(X29)
        | r8_relat_2(u1_orders_2(X29),u1_struct_0(X29))
        | ~ l1_orders_2(X29) )
      & ( ~ r8_relat_2(u1_orders_2(X29),u1_struct_0(X29))
        | v4_orders_2(X29)
        | ~ l1_orders_2(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_orders_2])])])).

cnf(c_0_34,negated_conjecture,
    ( v1_xboole_0(u1_orders_2(esk5_0))
    | r2_hidden(esk7_0,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_36,plain,
    ( r2_hidden(k4_tarski(X3,X5),X1)
    | ~ r8_relat_2(X1,X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X4,X2)
    | ~ r2_hidden(X5,X2)
    | ~ r2_hidden(k4_tarski(X3,X4),X1)
    | ~ r2_hidden(k4_tarski(X4,X5),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_0,esk8_0),u1_orders_2(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_26])])).

cnf(c_0_38,negated_conjecture,
    ( v1_relat_1(u1_orders_2(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_16])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk8_0,u1_struct_0(esk5_0))
    | ~ r2_hidden(X1,u1_orders_2(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,plain,
    ( r8_relat_2(u1_orders_2(X1),u1_struct_0(X1))
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( v4_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk7_0,u1_struct_0(esk5_0))
    | ~ r2_hidden(X1,u1_orders_2(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( v1_xboole_0(u1_orders_2(esk5_0))
    | r2_hidden(esk6_0,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_35])).

cnf(c_0_44,plain,
    ( r1_orders_2(X3,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk8_0),u1_orders_2(esk5_0))
    | ~ r8_relat_2(u1_orders_2(esk5_0),X2)
    | ~ r2_hidden(k4_tarski(X1,esk7_0),u1_orders_2(esk5_0))
    | ~ r2_hidden(esk8_0,X2)
    | ~ r2_hidden(esk7_0,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk8_0,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( r8_relat_2(u1_orders_2(esk5_0),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_14])])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk7_0,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_37])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk6_0,u1_struct_0(esk5_0))
    | ~ r2_hidden(X1,u1_orders_2(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk7_0),u1_orders_2(esk5_0))
    | ~ r1_orders_2(esk5_0,X1,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_26]),c_0_14])])).

cnf(c_0_51,negated_conjecture,
    ( r1_orders_2(esk5_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_52,negated_conjecture,
    ( r1_orders_2(esk5_0,X1,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_hidden(k4_tarski(X1,esk8_0),u1_orders_2(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_22]),c_0_14])])).

cnf(c_0_53,negated_conjecture,
    ( ~ r1_orders_2(esk5_0,esk6_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk8_0),u1_orders_2(esk5_0))
    | ~ r2_hidden(k4_tarski(X1,esk7_0),u1_orders_2(esk5_0))
    | ~ r2_hidden(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_48])])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk6_0,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_37])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk7_0),u1_orders_2(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_35])])).

cnf(c_0_57,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk6_0,esk8_0),u1_orders_2(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_35]),c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])]),c_0_57]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.10/0.30  % Computer   : n024.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % WCLimit    : 600
% 0.10/0.30  % DateTime   : Tue Dec  1 18:21:36 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.10/0.31  # Version: 2.5pre002
% 0.10/0.31  # No SInE strategy applied
% 0.10/0.31  # Trying AutoSched0 for 299 seconds
% 0.15/0.34  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S01AI
% 0.15/0.34  # and selection function SelectMinOptimalNoXTypePred.
% 0.15/0.34  #
% 0.15/0.34  # Preprocessing time       : 0.028 s
% 0.15/0.34  # Presaturation interreduction done
% 0.15/0.34  
% 0.15/0.34  # Proof found!
% 0.15/0.34  # SZS status Theorem
% 0.15/0.34  # SZS output start CNFRefutation
% 0.15/0.34  fof(t26_orders_2, conjecture, ![X1]:((v4_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X3,X4))=>r1_orders_2(X1,X2,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_orders_2)).
% 0.15/0.34  fof(dt_u1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 0.15/0.34  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 0.15/0.34  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.15/0.34  fof(d9_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_orders_2(X1,X2,X3)<=>r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_orders_2)).
% 0.15/0.34  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.15/0.34  fof(t7_boole, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_boole)).
% 0.15/0.34  fof(d8_relat_2, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r8_relat_2(X1,X2)<=>![X3, X4, X5]:(((((r2_hidden(X3,X2)&r2_hidden(X4,X2))&r2_hidden(X5,X2))&r2_hidden(k4_tarski(X3,X4),X1))&r2_hidden(k4_tarski(X4,X5),X1))=>r2_hidden(k4_tarski(X3,X5),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_relat_2)).
% 0.15/0.34  fof(d5_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>(v4_orders_2(X1)<=>r8_relat_2(u1_orders_2(X1),u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_orders_2)).
% 0.15/0.34  fof(c_0_9, negated_conjecture, ~(![X1]:((v4_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X3,X4))=>r1_orders_2(X1,X2,X4))))))), inference(assume_negation,[status(cth)],[t26_orders_2])).
% 0.15/0.34  fof(c_0_10, plain, ![X33]:(~l1_orders_2(X33)|m1_subset_1(u1_orders_2(X33),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X33))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).
% 0.15/0.34  fof(c_0_11, negated_conjecture, ((v4_orders_2(esk5_0)&l1_orders_2(esk5_0))&(m1_subset_1(esk6_0,u1_struct_0(esk5_0))&(m1_subset_1(esk7_0,u1_struct_0(esk5_0))&(m1_subset_1(esk8_0,u1_struct_0(esk5_0))&((r1_orders_2(esk5_0,esk6_0,esk7_0)&r1_orders_2(esk5_0,esk7_0,esk8_0))&~r1_orders_2(esk5_0,esk6_0,esk8_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.15/0.34  fof(c_0_12, plain, ![X17, X18, X19]:(~v1_xboole_0(X17)|(~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X18,X17)))|v1_xboole_0(X19))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 0.15/0.34  cnf(c_0_13, plain, (m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.15/0.34  cnf(c_0_14, negated_conjecture, (l1_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.15/0.34  cnf(c_0_15, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.15/0.34  cnf(c_0_16, negated_conjecture, (m1_subset_1(u1_orders_2(esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0))))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.15/0.34  fof(c_0_17, plain, ![X12, X13]:(~m1_subset_1(X12,X13)|(v1_xboole_0(X13)|r2_hidden(X12,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.15/0.34  fof(c_0_18, plain, ![X30, X31, X32]:((~r1_orders_2(X30,X31,X32)|r2_hidden(k4_tarski(X31,X32),u1_orders_2(X30))|~m1_subset_1(X32,u1_struct_0(X30))|~m1_subset_1(X31,u1_struct_0(X30))|~l1_orders_2(X30))&(~r2_hidden(k4_tarski(X31,X32),u1_orders_2(X30))|r1_orders_2(X30,X31,X32)|~m1_subset_1(X32,u1_struct_0(X30))|~m1_subset_1(X31,u1_struct_0(X30))|~l1_orders_2(X30))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).
% 0.15/0.34  cnf(c_0_19, negated_conjecture, (v1_xboole_0(u1_orders_2(esk5_0))|~v1_xboole_0(u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.15/0.34  cnf(c_0_20, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.15/0.34  cnf(c_0_21, plain, (r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))|~r1_orders_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.15/0.34  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.15/0.34  fof(c_0_23, plain, ![X14, X15, X16]:(~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))|v1_relat_1(X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.15/0.34  fof(c_0_24, plain, ![X6, X7]:(~r2_hidden(X6,X7)|~v1_xboole_0(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).
% 0.15/0.34  cnf(c_0_25, negated_conjecture, (v1_xboole_0(u1_orders_2(esk5_0))|r2_hidden(X1,u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.15/0.34  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.15/0.34  fof(c_0_27, plain, ![X20, X21, X22, X23, X24, X25]:((~r8_relat_2(X20,X21)|(~r2_hidden(X22,X21)|~r2_hidden(X23,X21)|~r2_hidden(X24,X21)|~r2_hidden(k4_tarski(X22,X23),X20)|~r2_hidden(k4_tarski(X23,X24),X20)|r2_hidden(k4_tarski(X22,X24),X20))|~v1_relat_1(X20))&((((((r2_hidden(esk2_2(X20,X25),X25)|r8_relat_2(X20,X25)|~v1_relat_1(X20))&(r2_hidden(esk3_2(X20,X25),X25)|r8_relat_2(X20,X25)|~v1_relat_1(X20)))&(r2_hidden(esk4_2(X20,X25),X25)|r8_relat_2(X20,X25)|~v1_relat_1(X20)))&(r2_hidden(k4_tarski(esk2_2(X20,X25),esk3_2(X20,X25)),X20)|r8_relat_2(X20,X25)|~v1_relat_1(X20)))&(r2_hidden(k4_tarski(esk3_2(X20,X25),esk4_2(X20,X25)),X20)|r8_relat_2(X20,X25)|~v1_relat_1(X20)))&(~r2_hidden(k4_tarski(esk2_2(X20,X25),esk4_2(X20,X25)),X20)|r8_relat_2(X20,X25)|~v1_relat_1(X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_2])])])])])])).
% 0.15/0.34  cnf(c_0_28, negated_conjecture, (r2_hidden(k4_tarski(X1,esk8_0),u1_orders_2(esk5_0))|~r1_orders_2(esk5_0,X1,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_14])])).
% 0.15/0.34  cnf(c_0_29, negated_conjecture, (r1_orders_2(esk5_0,esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.15/0.34  cnf(c_0_30, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.15/0.34  cnf(c_0_31, plain, (~r2_hidden(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.15/0.34  cnf(c_0_32, negated_conjecture, (v1_xboole_0(u1_orders_2(esk5_0))|r2_hidden(esk8_0,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_25, c_0_22])).
% 0.15/0.34  fof(c_0_33, plain, ![X29]:((~v4_orders_2(X29)|r8_relat_2(u1_orders_2(X29),u1_struct_0(X29))|~l1_orders_2(X29))&(~r8_relat_2(u1_orders_2(X29),u1_struct_0(X29))|v4_orders_2(X29)|~l1_orders_2(X29))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_orders_2])])])).
% 0.15/0.34  cnf(c_0_34, negated_conjecture, (v1_xboole_0(u1_orders_2(esk5_0))|r2_hidden(esk7_0,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.15/0.34  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.15/0.34  cnf(c_0_36, plain, (r2_hidden(k4_tarski(X3,X5),X1)|~r8_relat_2(X1,X2)|~r2_hidden(X3,X2)|~r2_hidden(X4,X2)|~r2_hidden(X5,X2)|~r2_hidden(k4_tarski(X3,X4),X1)|~r2_hidden(k4_tarski(X4,X5),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.15/0.34  cnf(c_0_37, negated_conjecture, (r2_hidden(k4_tarski(esk7_0,esk8_0),u1_orders_2(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_26])])).
% 0.15/0.34  cnf(c_0_38, negated_conjecture, (v1_relat_1(u1_orders_2(esk5_0))), inference(spm,[status(thm)],[c_0_30, c_0_16])).
% 0.15/0.34  cnf(c_0_39, negated_conjecture, (r2_hidden(esk8_0,u1_struct_0(esk5_0))|~r2_hidden(X1,u1_orders_2(esk5_0))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.15/0.34  cnf(c_0_40, plain, (r8_relat_2(u1_orders_2(X1),u1_struct_0(X1))|~v4_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.15/0.34  cnf(c_0_41, negated_conjecture, (v4_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.15/0.34  cnf(c_0_42, negated_conjecture, (r2_hidden(esk7_0,u1_struct_0(esk5_0))|~r2_hidden(X1,u1_orders_2(esk5_0))), inference(spm,[status(thm)],[c_0_31, c_0_34])).
% 0.15/0.34  cnf(c_0_43, negated_conjecture, (v1_xboole_0(u1_orders_2(esk5_0))|r2_hidden(esk6_0,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_25, c_0_35])).
% 0.15/0.34  cnf(c_0_44, plain, (r1_orders_2(X3,X1,X2)|~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.15/0.34  cnf(c_0_45, negated_conjecture, (r2_hidden(k4_tarski(X1,esk8_0),u1_orders_2(esk5_0))|~r8_relat_2(u1_orders_2(esk5_0),X2)|~r2_hidden(k4_tarski(X1,esk7_0),u1_orders_2(esk5_0))|~r2_hidden(esk8_0,X2)|~r2_hidden(esk7_0,X2)|~r2_hidden(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])])).
% 0.15/0.34  cnf(c_0_46, negated_conjecture, (r2_hidden(esk8_0,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_39, c_0_37])).
% 0.15/0.34  cnf(c_0_47, negated_conjecture, (r8_relat_2(u1_orders_2(esk5_0),u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_14])])).
% 0.15/0.34  cnf(c_0_48, negated_conjecture, (r2_hidden(esk7_0,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_42, c_0_37])).
% 0.15/0.34  cnf(c_0_49, negated_conjecture, (r2_hidden(esk6_0,u1_struct_0(esk5_0))|~r2_hidden(X1,u1_orders_2(esk5_0))), inference(spm,[status(thm)],[c_0_31, c_0_43])).
% 0.15/0.34  cnf(c_0_50, negated_conjecture, (r2_hidden(k4_tarski(X1,esk7_0),u1_orders_2(esk5_0))|~r1_orders_2(esk5_0,X1,esk7_0)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_26]), c_0_14])])).
% 0.15/0.34  cnf(c_0_51, negated_conjecture, (r1_orders_2(esk5_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.15/0.34  cnf(c_0_52, negated_conjecture, (r1_orders_2(esk5_0,X1,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk5_0))|~r2_hidden(k4_tarski(X1,esk8_0),u1_orders_2(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_22]), c_0_14])])).
% 0.15/0.34  cnf(c_0_53, negated_conjecture, (~r1_orders_2(esk5_0,esk6_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.15/0.34  cnf(c_0_54, negated_conjecture, (r2_hidden(k4_tarski(X1,esk8_0),u1_orders_2(esk5_0))|~r2_hidden(k4_tarski(X1,esk7_0),u1_orders_2(esk5_0))|~r2_hidden(X1,u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47]), c_0_48])])).
% 0.15/0.34  cnf(c_0_55, negated_conjecture, (r2_hidden(esk6_0,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_49, c_0_37])).
% 0.15/0.34  cnf(c_0_56, negated_conjecture, (r2_hidden(k4_tarski(esk6_0,esk7_0),u1_orders_2(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_35])])).
% 0.15/0.34  cnf(c_0_57, negated_conjecture, (~r2_hidden(k4_tarski(esk6_0,esk8_0),u1_orders_2(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_35]), c_0_53])).
% 0.15/0.34  cnf(c_0_58, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])]), c_0_57]), ['proof']).
% 0.15/0.34  # SZS output end CNFRefutation
% 0.15/0.34  # Proof object total steps             : 59
% 0.15/0.34  # Proof object clause steps            : 40
% 0.15/0.34  # Proof object formula steps           : 19
% 0.15/0.34  # Proof object conjectures             : 34
% 0.15/0.34  # Proof object clause conjectures      : 31
% 0.15/0.34  # Proof object formula conjectures     : 3
% 0.15/0.34  # Proof object initial clauses used    : 17
% 0.15/0.34  # Proof object initial formulas used   : 9
% 0.15/0.34  # Proof object generating inferences   : 23
% 0.15/0.34  # Proof object simplifying inferences  : 21
% 0.15/0.34  # Training examples: 0 positive, 0 negative
% 0.15/0.34  # Parsed axioms                        : 10
% 0.15/0.34  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.34  # Initial clauses                      : 26
% 0.15/0.34  # Removed in clause preprocessing      : 0
% 0.15/0.34  # Initial clauses in saturation        : 26
% 0.15/0.34  # Processed clauses                    : 118
% 0.15/0.34  # ...of these trivial                  : 0
% 0.15/0.34  # ...subsumed                          : 7
% 0.15/0.34  # ...remaining for further processing  : 111
% 0.15/0.34  # Other redundant clauses eliminated   : 0
% 0.15/0.34  # Clauses deleted for lack of memory   : 0
% 0.15/0.34  # Backward-subsumed                    : 0
% 0.15/0.34  # Backward-rewritten                   : 9
% 0.15/0.34  # Generated clauses                    : 83
% 0.15/0.34  # ...of the previous two non-trivial   : 72
% 0.15/0.34  # Contextual simplify-reflections      : 0
% 0.15/0.34  # Paramodulations                      : 83
% 0.15/0.34  # Factorizations                       : 0
% 0.15/0.34  # Equation resolutions                 : 0
% 0.15/0.34  # Propositional unsat checks           : 0
% 0.15/0.34  #    Propositional check models        : 0
% 0.15/0.34  #    Propositional check unsatisfiable : 0
% 0.15/0.34  #    Propositional clauses             : 0
% 0.15/0.34  #    Propositional clauses after purity: 0
% 0.15/0.34  #    Propositional unsat core size     : 0
% 0.15/0.34  #    Propositional preprocessing time  : 0.000
% 0.15/0.34  #    Propositional encoding time       : 0.000
% 0.15/0.34  #    Propositional solver time         : 0.000
% 0.15/0.34  #    Success case prop preproc time    : 0.000
% 0.15/0.34  #    Success case prop encoding time   : 0.000
% 0.15/0.34  #    Success case prop solver time     : 0.000
% 0.15/0.34  # Current number of processed clauses  : 76
% 0.15/0.34  #    Positive orientable unit clauses  : 15
% 0.15/0.34  #    Positive unorientable unit clauses: 0
% 0.15/0.34  #    Negative unit clauses             : 2
% 0.15/0.34  #    Non-unit-clauses                  : 59
% 0.15/0.34  # Current number of unprocessed clauses: 2
% 0.15/0.34  # ...number of literals in the above   : 9
% 0.15/0.34  # Current number of archived formulas  : 0
% 0.15/0.34  # Current number of archived clauses   : 35
% 0.15/0.34  # Clause-clause subsumption calls (NU) : 1052
% 0.15/0.34  # Rec. Clause-clause subsumption calls : 420
% 0.15/0.34  # Non-unit clause-clause subsumptions  : 7
% 0.15/0.34  # Unit Clause-clause subsumption calls : 4
% 0.15/0.34  # Rewrite failures with RHS unbound    : 0
% 0.15/0.34  # BW rewrite match attempts            : 5
% 0.15/0.34  # BW rewrite match successes           : 3
% 0.15/0.34  # Condensation attempts                : 0
% 0.15/0.34  # Condensation successes               : 0
% 0.15/0.34  # Termbank termtop insertions          : 4810
% 0.15/0.34  
% 0.15/0.34  # -------------------------------------------------
% 0.15/0.34  # User time                : 0.036 s
% 0.15/0.34  # System time              : 0.002 s
% 0.15/0.34  # Total time               : 0.038 s
% 0.15/0.34  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
