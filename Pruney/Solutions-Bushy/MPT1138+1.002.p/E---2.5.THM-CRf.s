%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1138+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:48 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 324 expanded)
%              Number of clauses        :   42 ( 127 expanded)
%              Number of leaves         :   10 (  76 expanded)
%              Depth                    :   11
%              Number of atoms          :  205 (1615 expanded)
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

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

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

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

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

fof(t106_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

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
    ! [X22] :
      ( ~ l1_orders_2(X22)
      | m1_subset_1(u1_orders_2(X22),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X22)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_12,negated_conjecture,
    ( v4_orders_2(esk4_0)
    & l1_orders_2(esk4_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    & m1_subset_1(esk6_0,u1_struct_0(esk4_0))
    & m1_subset_1(esk7_0,u1_struct_0(esk4_0))
    & r1_orders_2(esk4_0,esk5_0,esk6_0)
    & r1_orders_2(esk4_0,esk6_0,esk7_0)
    & ~ r1_orders_2(esk4_0,esk5_0,esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_13,plain,(
    ! [X34,X35,X36] :
      ( ~ r2_hidden(X34,X35)
      | ~ m1_subset_1(X35,k1_zfmisc_1(X36))
      | ~ v1_xboole_0(X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_14,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X19,X20,X21] :
      ( ( ~ r1_orders_2(X19,X20,X21)
        | r2_hidden(k4_tarski(X20,X21),u1_orders_2(X19))
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | ~ l1_orders_2(X19) )
      & ( ~ r2_hidden(k4_tarski(X20,X21),u1_orders_2(X19))
        | r1_orders_2(X19,X20,X21)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | ~ l1_orders_2(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).

cnf(c_0_17,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(u1_orders_2(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_19,plain,(
    ! [X29,X30] :
      ( ~ m1_subset_1(X29,X30)
      | v1_xboole_0(X30)
      | r2_hidden(X29,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_22,plain,(
    ! [X31,X32,X33] :
      ( ~ r2_hidden(X31,X32)
      | ~ m1_subset_1(X32,k1_zfmisc_1(X33))
      | m1_subset_1(X31,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_23,negated_conjecture,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0)))
    | ~ r2_hidden(X1,u1_orders_2(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk7_0),u1_orders_2(esk4_0))
    | ~ r1_orders_2(esk4_0,X1,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_15])])).

cnf(c_0_26,negated_conjecture,
    ( r1_orders_2(esk4_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_28,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,plain,(
    ! [X6,X7,X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | v1_relat_1(X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0)))
    | ~ r2_hidden(X2,u1_orders_2(esk4_0))
    | ~ m1_subset_1(X1,k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk7_0),u1_orders_2(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(X1,k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0)))
    | ~ r2_hidden(X1,u1_orders_2(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_18])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk6_0),u1_orders_2(esk4_0))
    | ~ r1_orders_2(esk4_0,X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_27]),c_0_15])])).

cnf(c_0_34,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_36,plain,(
    ! [X10,X11,X12,X13,X14,X15] :
      ( ( ~ r8_relat_2(X10,X11)
        | ~ r2_hidden(X12,X11)
        | ~ r2_hidden(X13,X11)
        | ~ r2_hidden(X14,X11)
        | ~ r2_hidden(k4_tarski(X12,X13),X10)
        | ~ r2_hidden(k4_tarski(X13,X14),X10)
        | r2_hidden(k4_tarski(X12,X14),X10)
        | ~ v1_relat_1(X10) )
      & ( r2_hidden(esk1_2(X10,X15),X15)
        | r8_relat_2(X10,X15)
        | ~ v1_relat_1(X10) )
      & ( r2_hidden(esk2_2(X10,X15),X15)
        | r8_relat_2(X10,X15)
        | ~ v1_relat_1(X10) )
      & ( r2_hidden(esk3_2(X10,X15),X15)
        | r8_relat_2(X10,X15)
        | ~ v1_relat_1(X10) )
      & ( r2_hidden(k4_tarski(esk1_2(X10,X15),esk2_2(X10,X15)),X10)
        | r8_relat_2(X10,X15)
        | ~ v1_relat_1(X10) )
      & ( r2_hidden(k4_tarski(esk2_2(X10,X15),esk3_2(X10,X15)),X10)
        | r8_relat_2(X10,X15)
        | ~ v1_relat_1(X10) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X10,X15),esk3_2(X10,X15)),X10)
        | r8_relat_2(X10,X15)
        | ~ v1_relat_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_2])])])])])])).

cnf(c_0_37,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_38,plain,(
    ! [X23,X24,X25,X26] :
      ( ( r2_hidden(X23,X25)
        | ~ r2_hidden(k4_tarski(X23,X24),k2_zfmisc_1(X25,X26)) )
      & ( r2_hidden(X24,X26)
        | ~ r2_hidden(k4_tarski(X23,X24),k2_zfmisc_1(X25,X26)) )
      & ( ~ r2_hidden(X23,X25)
        | ~ r2_hidden(X24,X26)
        | r2_hidden(k4_tarski(X23,X24),k2_zfmisc_1(X25,X26)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_zfmisc_1])])])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(k4_tarski(esk6_0,esk7_0),k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_31])).

fof(c_0_41,plain,(
    ! [X9] :
      ( ( ~ v4_orders_2(X9)
        | r8_relat_2(u1_orders_2(X9),u1_struct_0(X9))
        | ~ l1_orders_2(X9) )
      & ( ~ r8_relat_2(u1_orders_2(X9),u1_struct_0(X9))
        | v4_orders_2(X9)
        | ~ l1_orders_2(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_orders_2])])])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_0,esk6_0),u1_orders_2(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

cnf(c_0_43,plain,
    ( r2_hidden(k4_tarski(X3,X5),X1)
    | ~ r8_relat_2(X1,X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X4,X2)
    | ~ r2_hidden(X5,X2)
    | ~ r2_hidden(k4_tarski(X3,X4),X1)
    | ~ r2_hidden(k4_tarski(X4,X5),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( v1_relat_1(u1_orders_2(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_18])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk7_0),k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,plain,
    ( r8_relat_2(u1_orders_2(X1),u1_struct_0(X1))
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( v4_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(k4_tarski(esk5_0,esk6_0),k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_42])).

cnf(c_0_51,plain,
    ( r1_orders_2(X3,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk7_0),u1_orders_2(esk4_0))
    | ~ r2_hidden(k4_tarski(X1,esk6_0),u1_orders_2(esk4_0))
    | ~ r2_hidden(esk7_0,X2)
    | ~ r2_hidden(esk6_0,X2)
    | ~ r2_hidden(X1,X2)
    | ~ r8_relat_2(u1_orders_2(esk4_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_31]),c_0_44])])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk7_0,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk6_0,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( r8_relat_2(u1_orders_2(esk4_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_15])])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_0,esk6_0),k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( r1_orders_2(esk4_0,X1,esk7_0)
    | ~ r2_hidden(k4_tarski(X1,esk7_0),u1_orders_2(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_21]),c_0_15])])).

cnf(c_0_58,negated_conjecture,
    ( ~ r1_orders_2(esk4_0,esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk7_0),u1_orders_2(esk4_0))
    | ~ r2_hidden(k4_tarski(X1,esk6_0),u1_orders_2(esk4_0))
    | ~ r2_hidden(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_55])])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk5_0,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk5_0,esk7_0),u1_orders_2(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_35]),c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_42])]),c_0_61]),
    [proof]).

%------------------------------------------------------------------------------
