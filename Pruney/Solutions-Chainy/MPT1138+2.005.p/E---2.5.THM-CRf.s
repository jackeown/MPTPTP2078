%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:30 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 237 expanded)
%              Number of clauses        :   41 (  92 expanded)
%              Number of leaves         :   10 (  56 expanded)
%              Depth                    :   11
%              Number of atoms          :  212 (1219 expanded)
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

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

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

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

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

fof(c_0_10,negated_conjecture,(
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

fof(c_0_11,plain,(
    ! [X32] :
      ( ~ l1_orders_2(X32)
      | m1_subset_1(u1_orders_2(X32),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X32)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_12,negated_conjecture,
    ( v4_orders_2(esk5_0)
    & l1_orders_2(esk5_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk5_0))
    & m1_subset_1(esk7_0,u1_struct_0(esk5_0))
    & m1_subset_1(esk8_0,u1_struct_0(esk5_0))
    & r1_orders_2(esk5_0,esk6_0,esk7_0)
    & r1_orders_2(esk5_0,esk7_0,esk8_0)
    & ~ r1_orders_2(esk5_0,esk6_0,esk8_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_13,plain,(
    ! [X16,X17,X18] :
      ( ~ v1_xboole_0(X16)
      | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X17,X16)))
      | v1_xboole_0(X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

cnf(c_0_14,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(u1_orders_2(esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_18,plain,(
    ! [X10,X11] :
      ( ( ~ m1_subset_1(X11,X10)
        | r2_hidden(X11,X10)
        | v1_xboole_0(X10) )
      & ( ~ r2_hidden(X11,X10)
        | m1_subset_1(X11,X10)
        | v1_xboole_0(X10) )
      & ( ~ m1_subset_1(X11,X10)
        | v1_xboole_0(X11)
        | ~ v1_xboole_0(X10) )
      & ( ~ v1_xboole_0(X11)
        | m1_subset_1(X11,X10)
        | ~ v1_xboole_0(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_19,plain,(
    ! [X29,X30,X31] :
      ( ( ~ r1_orders_2(X29,X30,X31)
        | r2_hidden(k4_tarski(X30,X31),u1_orders_2(X29))
        | ~ m1_subset_1(X31,u1_struct_0(X29))
        | ~ m1_subset_1(X30,u1_struct_0(X29))
        | ~ l1_orders_2(X29) )
      & ( ~ r2_hidden(k4_tarski(X30,X31),u1_orders_2(X29))
        | r1_orders_2(X29,X30,X31)
        | ~ m1_subset_1(X31,u1_struct_0(X29))
        | ~ m1_subset_1(X30,u1_struct_0(X29))
        | ~ l1_orders_2(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).

cnf(c_0_20,negated_conjecture,
    ( v1_xboole_0(u1_orders_2(esk5_0))
    | ~ v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_24,plain,(
    ! [X12,X13] :
      ( ~ v1_relat_1(X12)
      | ~ m1_subset_1(X13,k1_zfmisc_1(X12))
      | v1_relat_1(X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_25,plain,(
    ! [X14,X15] : v1_relat_1(k2_zfmisc_1(X14,X15)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_26,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk5_0))
    | v1_xboole_0(u1_orders_2(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_29,plain,(
    ! [X19,X20,X21,X22,X23,X24] :
      ( ( ~ r8_relat_2(X19,X20)
        | ~ r2_hidden(X21,X20)
        | ~ r2_hidden(X22,X20)
        | ~ r2_hidden(X23,X20)
        | ~ r2_hidden(k4_tarski(X21,X22),X19)
        | ~ r2_hidden(k4_tarski(X22,X23),X19)
        | r2_hidden(k4_tarski(X21,X23),X19)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(esk2_2(X19,X24),X24)
        | r8_relat_2(X19,X24)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(esk3_2(X19,X24),X24)
        | r8_relat_2(X19,X24)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(esk4_2(X19,X24),X24)
        | r8_relat_2(X19,X24)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(k4_tarski(esk2_2(X19,X24),esk3_2(X19,X24)),X19)
        | r8_relat_2(X19,X24)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(k4_tarski(esk3_2(X19,X24),esk4_2(X19,X24)),X19)
        | r8_relat_2(X19,X24)
        | ~ v1_relat_1(X19) )
      & ( ~ r2_hidden(k4_tarski(esk2_2(X19,X24),esk4_2(X19,X24)),X19)
        | r8_relat_2(X19,X24)
        | ~ v1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_2])])])])])])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk8_0),u1_orders_2(esk5_0))
    | ~ r1_orders_2(esk5_0,X1,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_15])])).

cnf(c_0_31,negated_conjecture,
    ( r1_orders_2(esk5_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_32,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk8_0,u1_struct_0(esk5_0))
    | v1_xboole_0(u1_orders_2(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_23])).

fof(c_0_36,plain,(
    ! [X28] :
      ( ( ~ v4_orders_2(X28)
        | r8_relat_2(u1_orders_2(X28),u1_struct_0(X28))
        | ~ l1_orders_2(X28) )
      & ( ~ r8_relat_2(u1_orders_2(X28),u1_struct_0(X28))
        | v4_orders_2(X28)
        | ~ l1_orders_2(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_orders_2])])])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk7_0,u1_struct_0(esk5_0))
    | v1_xboole_0(u1_orders_2(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_39,plain,
    ( r2_hidden(k4_tarski(X3,X5),X1)
    | ~ r8_relat_2(X1,X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X4,X2)
    | ~ r2_hidden(X5,X2)
    | ~ r2_hidden(k4_tarski(X3,X4),X1)
    | ~ r2_hidden(k4_tarski(X4,X5),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_0,esk8_0),u1_orders_2(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_28])])).

cnf(c_0_41,negated_conjecture,
    ( v1_relat_1(u1_orders_2(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_17]),c_0_33])])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk8_0,u1_struct_0(esk5_0))
    | ~ r2_hidden(X1,u1_orders_2(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,plain,
    ( r8_relat_2(u1_orders_2(X1),u1_struct_0(X1))
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( v4_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk7_0,u1_struct_0(esk5_0))
    | ~ r2_hidden(X1,u1_orders_2(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk6_0,u1_struct_0(esk5_0))
    | v1_xboole_0(u1_orders_2(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_38])).

cnf(c_0_47,plain,
    ( r1_orders_2(X3,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk8_0),u1_orders_2(esk5_0))
    | ~ r8_relat_2(u1_orders_2(esk5_0),X2)
    | ~ r2_hidden(k4_tarski(X1,esk7_0),u1_orders_2(esk5_0))
    | ~ r2_hidden(esk8_0,X2)
    | ~ r2_hidden(esk7_0,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk8_0,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( r8_relat_2(u1_orders_2(esk5_0),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_15])])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk7_0,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_40])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk6_0,u1_struct_0(esk5_0))
    | ~ r2_hidden(X1,u1_orders_2(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk7_0),u1_orders_2(esk5_0))
    | ~ r1_orders_2(esk5_0,X1,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_28]),c_0_15])])).

cnf(c_0_54,negated_conjecture,
    ( r1_orders_2(esk5_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_55,negated_conjecture,
    ( r1_orders_2(esk5_0,X1,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_hidden(k4_tarski(X1,esk8_0),u1_orders_2(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_23]),c_0_15])])).

cnf(c_0_56,negated_conjecture,
    ( ~ r1_orders_2(esk5_0,esk6_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk8_0),u1_orders_2(esk5_0))
    | ~ r2_hidden(k4_tarski(X1,esk7_0),u1_orders_2(esk5_0))
    | ~ r2_hidden(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_51])])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk6_0,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_40])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk7_0),u1_orders_2(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_38])])).

cnf(c_0_60,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk6_0,esk8_0),u1_orders_2(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_38]),c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])]),c_0_60]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:41:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.48  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S01AI
% 0.21/0.48  # and selection function SelectMinOptimalNoXTypePred.
% 0.21/0.48  #
% 0.21/0.48  # Preprocessing time       : 0.028 s
% 0.21/0.48  # Presaturation interreduction done
% 0.21/0.48  
% 0.21/0.48  # Proof found!
% 0.21/0.48  # SZS status Theorem
% 0.21/0.48  # SZS output start CNFRefutation
% 0.21/0.48  fof(t26_orders_2, conjecture, ![X1]:((v4_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X3,X4))=>r1_orders_2(X1,X2,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_orders_2)).
% 0.21/0.48  fof(dt_u1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 0.21/0.48  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 0.21/0.48  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.21/0.48  fof(d9_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_orders_2(X1,X2,X3)<=>r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_orders_2)).
% 0.21/0.48  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.21/0.48  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.21/0.48  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.21/0.48  fof(d8_relat_2, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r8_relat_2(X1,X2)<=>![X3, X4, X5]:(((((r2_hidden(X3,X2)&r2_hidden(X4,X2))&r2_hidden(X5,X2))&r2_hidden(k4_tarski(X3,X4),X1))&r2_hidden(k4_tarski(X4,X5),X1))=>r2_hidden(k4_tarski(X3,X5),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_relat_2)).
% 0.21/0.48  fof(d5_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>(v4_orders_2(X1)<=>r8_relat_2(u1_orders_2(X1),u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_orders_2)).
% 0.21/0.48  fof(c_0_10, negated_conjecture, ~(![X1]:((v4_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X3,X4))=>r1_orders_2(X1,X2,X4))))))), inference(assume_negation,[status(cth)],[t26_orders_2])).
% 0.21/0.48  fof(c_0_11, plain, ![X32]:(~l1_orders_2(X32)|m1_subset_1(u1_orders_2(X32),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X32))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).
% 0.21/0.48  fof(c_0_12, negated_conjecture, ((v4_orders_2(esk5_0)&l1_orders_2(esk5_0))&(m1_subset_1(esk6_0,u1_struct_0(esk5_0))&(m1_subset_1(esk7_0,u1_struct_0(esk5_0))&(m1_subset_1(esk8_0,u1_struct_0(esk5_0))&((r1_orders_2(esk5_0,esk6_0,esk7_0)&r1_orders_2(esk5_0,esk7_0,esk8_0))&~r1_orders_2(esk5_0,esk6_0,esk8_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.21/0.48  fof(c_0_13, plain, ![X16, X17, X18]:(~v1_xboole_0(X16)|(~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X17,X16)))|v1_xboole_0(X18))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 0.21/0.48  cnf(c_0_14, plain, (m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.48  cnf(c_0_15, negated_conjecture, (l1_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.48  cnf(c_0_16, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.48  cnf(c_0_17, negated_conjecture, (m1_subset_1(u1_orders_2(esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0))))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.21/0.48  fof(c_0_18, plain, ![X10, X11]:(((~m1_subset_1(X11,X10)|r2_hidden(X11,X10)|v1_xboole_0(X10))&(~r2_hidden(X11,X10)|m1_subset_1(X11,X10)|v1_xboole_0(X10)))&((~m1_subset_1(X11,X10)|v1_xboole_0(X11)|~v1_xboole_0(X10))&(~v1_xboole_0(X11)|m1_subset_1(X11,X10)|~v1_xboole_0(X10)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.21/0.48  fof(c_0_19, plain, ![X29, X30, X31]:((~r1_orders_2(X29,X30,X31)|r2_hidden(k4_tarski(X30,X31),u1_orders_2(X29))|~m1_subset_1(X31,u1_struct_0(X29))|~m1_subset_1(X30,u1_struct_0(X29))|~l1_orders_2(X29))&(~r2_hidden(k4_tarski(X30,X31),u1_orders_2(X29))|r1_orders_2(X29,X30,X31)|~m1_subset_1(X31,u1_struct_0(X29))|~m1_subset_1(X30,u1_struct_0(X29))|~l1_orders_2(X29))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).
% 0.21/0.48  cnf(c_0_20, negated_conjecture, (v1_xboole_0(u1_orders_2(esk5_0))|~v1_xboole_0(u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.21/0.48  cnf(c_0_21, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.48  cnf(c_0_22, plain, (r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))|~r1_orders_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.48  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.48  fof(c_0_24, plain, ![X12, X13]:(~v1_relat_1(X12)|(~m1_subset_1(X13,k1_zfmisc_1(X12))|v1_relat_1(X13))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.21/0.48  fof(c_0_25, plain, ![X14, X15]:v1_relat_1(k2_zfmisc_1(X14,X15)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.21/0.48  fof(c_0_26, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.21/0.48  cnf(c_0_27, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk5_0))|v1_xboole_0(u1_orders_2(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.21/0.48  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.48  fof(c_0_29, plain, ![X19, X20, X21, X22, X23, X24]:((~r8_relat_2(X19,X20)|(~r2_hidden(X21,X20)|~r2_hidden(X22,X20)|~r2_hidden(X23,X20)|~r2_hidden(k4_tarski(X21,X22),X19)|~r2_hidden(k4_tarski(X22,X23),X19)|r2_hidden(k4_tarski(X21,X23),X19))|~v1_relat_1(X19))&((((((r2_hidden(esk2_2(X19,X24),X24)|r8_relat_2(X19,X24)|~v1_relat_1(X19))&(r2_hidden(esk3_2(X19,X24),X24)|r8_relat_2(X19,X24)|~v1_relat_1(X19)))&(r2_hidden(esk4_2(X19,X24),X24)|r8_relat_2(X19,X24)|~v1_relat_1(X19)))&(r2_hidden(k4_tarski(esk2_2(X19,X24),esk3_2(X19,X24)),X19)|r8_relat_2(X19,X24)|~v1_relat_1(X19)))&(r2_hidden(k4_tarski(esk3_2(X19,X24),esk4_2(X19,X24)),X19)|r8_relat_2(X19,X24)|~v1_relat_1(X19)))&(~r2_hidden(k4_tarski(esk2_2(X19,X24),esk4_2(X19,X24)),X19)|r8_relat_2(X19,X24)|~v1_relat_1(X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_2])])])])])])).
% 0.21/0.48  cnf(c_0_30, negated_conjecture, (r2_hidden(k4_tarski(X1,esk8_0),u1_orders_2(esk5_0))|~r1_orders_2(esk5_0,X1,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_15])])).
% 0.21/0.48  cnf(c_0_31, negated_conjecture, (r1_orders_2(esk5_0,esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.48  cnf(c_0_32, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.48  cnf(c_0_33, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.48  cnf(c_0_34, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.48  cnf(c_0_35, negated_conjecture, (r2_hidden(esk8_0,u1_struct_0(esk5_0))|v1_xboole_0(u1_orders_2(esk5_0))), inference(spm,[status(thm)],[c_0_27, c_0_23])).
% 0.21/0.48  fof(c_0_36, plain, ![X28]:((~v4_orders_2(X28)|r8_relat_2(u1_orders_2(X28),u1_struct_0(X28))|~l1_orders_2(X28))&(~r8_relat_2(u1_orders_2(X28),u1_struct_0(X28))|v4_orders_2(X28)|~l1_orders_2(X28))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_orders_2])])])).
% 0.21/0.48  cnf(c_0_37, negated_conjecture, (r2_hidden(esk7_0,u1_struct_0(esk5_0))|v1_xboole_0(u1_orders_2(esk5_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.21/0.48  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.48  cnf(c_0_39, plain, (r2_hidden(k4_tarski(X3,X5),X1)|~r8_relat_2(X1,X2)|~r2_hidden(X3,X2)|~r2_hidden(X4,X2)|~r2_hidden(X5,X2)|~r2_hidden(k4_tarski(X3,X4),X1)|~r2_hidden(k4_tarski(X4,X5),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.48  cnf(c_0_40, negated_conjecture, (r2_hidden(k4_tarski(esk7_0,esk8_0),u1_orders_2(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_28])])).
% 0.21/0.48  cnf(c_0_41, negated_conjecture, (v1_relat_1(u1_orders_2(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_17]), c_0_33])])).
% 0.21/0.48  cnf(c_0_42, negated_conjecture, (r2_hidden(esk8_0,u1_struct_0(esk5_0))|~r2_hidden(X1,u1_orders_2(esk5_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.21/0.48  cnf(c_0_43, plain, (r8_relat_2(u1_orders_2(X1),u1_struct_0(X1))|~v4_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.21/0.48  cnf(c_0_44, negated_conjecture, (v4_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.48  cnf(c_0_45, negated_conjecture, (r2_hidden(esk7_0,u1_struct_0(esk5_0))|~r2_hidden(X1,u1_orders_2(esk5_0))), inference(spm,[status(thm)],[c_0_34, c_0_37])).
% 0.21/0.48  cnf(c_0_46, negated_conjecture, (r2_hidden(esk6_0,u1_struct_0(esk5_0))|v1_xboole_0(u1_orders_2(esk5_0))), inference(spm,[status(thm)],[c_0_27, c_0_38])).
% 0.21/0.48  cnf(c_0_47, plain, (r1_orders_2(X3,X1,X2)|~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.48  cnf(c_0_48, negated_conjecture, (r2_hidden(k4_tarski(X1,esk8_0),u1_orders_2(esk5_0))|~r8_relat_2(u1_orders_2(esk5_0),X2)|~r2_hidden(k4_tarski(X1,esk7_0),u1_orders_2(esk5_0))|~r2_hidden(esk8_0,X2)|~r2_hidden(esk7_0,X2)|~r2_hidden(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])])).
% 0.21/0.48  cnf(c_0_49, negated_conjecture, (r2_hidden(esk8_0,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_42, c_0_40])).
% 0.21/0.48  cnf(c_0_50, negated_conjecture, (r8_relat_2(u1_orders_2(esk5_0),u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_15])])).
% 0.21/0.48  cnf(c_0_51, negated_conjecture, (r2_hidden(esk7_0,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_45, c_0_40])).
% 0.21/0.48  cnf(c_0_52, negated_conjecture, (r2_hidden(esk6_0,u1_struct_0(esk5_0))|~r2_hidden(X1,u1_orders_2(esk5_0))), inference(spm,[status(thm)],[c_0_34, c_0_46])).
% 0.21/0.48  cnf(c_0_53, negated_conjecture, (r2_hidden(k4_tarski(X1,esk7_0),u1_orders_2(esk5_0))|~r1_orders_2(esk5_0,X1,esk7_0)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_28]), c_0_15])])).
% 0.21/0.48  cnf(c_0_54, negated_conjecture, (r1_orders_2(esk5_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.48  cnf(c_0_55, negated_conjecture, (r1_orders_2(esk5_0,X1,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk5_0))|~r2_hidden(k4_tarski(X1,esk8_0),u1_orders_2(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_23]), c_0_15])])).
% 0.21/0.48  cnf(c_0_56, negated_conjecture, (~r1_orders_2(esk5_0,esk6_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.48  cnf(c_0_57, negated_conjecture, (r2_hidden(k4_tarski(X1,esk8_0),u1_orders_2(esk5_0))|~r2_hidden(k4_tarski(X1,esk7_0),u1_orders_2(esk5_0))|~r2_hidden(X1,u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_51])])).
% 0.21/0.48  cnf(c_0_58, negated_conjecture, (r2_hidden(esk6_0,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_52, c_0_40])).
% 0.21/0.48  cnf(c_0_59, negated_conjecture, (r2_hidden(k4_tarski(esk6_0,esk7_0),u1_orders_2(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_38])])).
% 0.21/0.48  cnf(c_0_60, negated_conjecture, (~r2_hidden(k4_tarski(esk6_0,esk8_0),u1_orders_2(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_38]), c_0_56])).
% 0.21/0.48  cnf(c_0_61, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])]), c_0_60]), ['proof']).
% 0.21/0.48  # SZS output end CNFRefutation
% 0.21/0.48  # Proof object total steps             : 62
% 0.21/0.48  # Proof object clause steps            : 41
% 0.21/0.48  # Proof object formula steps           : 21
% 0.21/0.48  # Proof object conjectures             : 34
% 0.21/0.48  # Proof object clause conjectures      : 31
% 0.21/0.48  # Proof object formula conjectures     : 3
% 0.21/0.48  # Proof object initial clauses used    : 18
% 0.21/0.48  # Proof object initial formulas used   : 10
% 0.21/0.48  # Proof object generating inferences   : 23
% 0.21/0.48  # Proof object simplifying inferences  : 23
% 0.21/0.48  # Training examples: 0 positive, 0 negative
% 0.21/0.48  # Parsed axioms                        : 10
% 0.21/0.48  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.48  # Initial clauses                      : 29
% 0.21/0.48  # Removed in clause preprocessing      : 0
% 0.21/0.48  # Initial clauses in saturation        : 29
% 0.21/0.48  # Processed clauses                    : 788
% 0.21/0.48  # ...of these trivial                  : 10
% 0.21/0.48  # ...subsumed                          : 417
% 0.21/0.48  # ...remaining for further processing  : 361
% 0.21/0.48  # Other redundant clauses eliminated   : 0
% 0.21/0.48  # Clauses deleted for lack of memory   : 0
% 0.21/0.48  # Backward-subsumed                    : 9
% 0.21/0.48  # Backward-rewritten                   : 67
% 0.21/0.48  # Generated clauses                    : 3788
% 0.21/0.48  # ...of the previous two non-trivial   : 3373
% 0.21/0.48  # Contextual simplify-reflections      : 1
% 0.21/0.48  # Paramodulations                      : 3788
% 0.21/0.48  # Factorizations                       : 0
% 0.21/0.48  # Equation resolutions                 : 0
% 0.21/0.48  # Propositional unsat checks           : 0
% 0.21/0.48  #    Propositional check models        : 0
% 0.21/0.48  #    Propositional check unsatisfiable : 0
% 0.21/0.48  #    Propositional clauses             : 0
% 0.21/0.48  #    Propositional clauses after purity: 0
% 0.21/0.48  #    Propositional unsat core size     : 0
% 0.21/0.48  #    Propositional preprocessing time  : 0.000
% 0.21/0.48  #    Propositional encoding time       : 0.000
% 0.21/0.48  #    Propositional solver time         : 0.000
% 0.21/0.48  #    Success case prop preproc time    : 0.000
% 0.21/0.48  #    Success case prop encoding time   : 0.000
% 0.21/0.48  #    Success case prop solver time     : 0.000
% 0.21/0.48  # Current number of processed clauses  : 256
% 0.21/0.48  #    Positive orientable unit clauses  : 20
% 0.21/0.48  #    Positive unorientable unit clauses: 0
% 0.21/0.48  #    Negative unit clauses             : 2
% 0.21/0.48  #    Non-unit-clauses                  : 234
% 0.21/0.48  # Current number of unprocessed clauses: 2420
% 0.21/0.48  # ...number of literals in the above   : 21057
% 0.21/0.48  # Current number of archived formulas  : 0
% 0.21/0.48  # Current number of archived clauses   : 105
% 0.21/0.48  # Clause-clause subsumption calls (NU) : 18987
% 0.21/0.48  # Rec. Clause-clause subsumption calls : 7980
% 0.21/0.48  # Non-unit clause-clause subsumptions  : 425
% 0.21/0.48  # Unit Clause-clause subsumption calls : 14
% 0.21/0.48  # Rewrite failures with RHS unbound    : 0
% 0.21/0.48  # BW rewrite match attempts            : 9
% 0.21/0.48  # BW rewrite match successes           : 6
% 0.21/0.48  # Condensation attempts                : 0
% 0.21/0.48  # Condensation successes               : 0
% 0.21/0.48  # Termbank termtop insertions          : 71025
% 0.21/0.49  
% 0.21/0.49  # -------------------------------------------------
% 0.21/0.49  # User time                : 0.133 s
% 0.21/0.49  # System time              : 0.009 s
% 0.21/0.49  # Total time               : 0.142 s
% 0.21/0.49  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
