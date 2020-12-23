%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1138+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:48 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 337 expanded)
%              Number of clauses        :   43 ( 133 expanded)
%              Number of leaves         :   11 (  79 expanded)
%              Depth                    :   11
%              Number of atoms          :  214 (1661 expanded)
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

fof(c_0_11,negated_conjecture,(
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

fof(c_0_12,plain,(
    ! [X22] :
      ( ~ l1_orders_2(X22)
      | m1_subset_1(u1_orders_2(X22),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X22)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_13,negated_conjecture,
    ( v4_orders_2(esk4_0)
    & l1_orders_2(esk4_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    & m1_subset_1(esk6_0,u1_struct_0(esk4_0))
    & m1_subset_1(esk7_0,u1_struct_0(esk4_0))
    & r1_orders_2(esk4_0,esk5_0,esk6_0)
    & r1_orders_2(esk4_0,esk6_0,esk7_0)
    & ~ r1_orders_2(esk4_0,esk5_0,esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_14,plain,(
    ! [X32,X33,X34] :
      ( ~ r2_hidden(X32,X33)
      | ~ m1_subset_1(X33,k1_zfmisc_1(X34))
      | ~ v1_xboole_0(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_15,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
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

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(u1_orders_2(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_20,plain,(
    ! [X27,X28] :
      ( ~ m1_subset_1(X27,X28)
      | v1_xboole_0(X28)
      | r2_hidden(X27,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_23,plain,(
    ! [X29,X30,X31] :
      ( ~ r2_hidden(X29,X30)
      | ~ m1_subset_1(X30,k1_zfmisc_1(X31))
      | m1_subset_1(X29,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_24,negated_conjecture,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0)))
    | ~ r2_hidden(X1,u1_orders_2(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk7_0),u1_orders_2(esk4_0))
    | ~ r1_orders_2(esk4_0,X1,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_16])])).

cnf(c_0_27,negated_conjecture,
    ( r1_orders_2(esk4_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_30,plain,(
    ! [X6,X7,X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | v1_relat_1(X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0)))
    | ~ r2_hidden(X2,u1_orders_2(esk4_0))
    | ~ m1_subset_1(X1,k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk7_0),u1_orders_2(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(X1,k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0)))
    | ~ r2_hidden(X1,u1_orders_2(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_19])).

fof(c_0_34,plain,(
    ! [X35,X36] :
      ( ~ r2_hidden(X35,X36)
      | ~ v1_xboole_0(X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_35,plain,(
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

cnf(c_0_36,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_37,plain,(
    ! [X23,X24,X25,X26] :
      ( ( r2_hidden(X23,X25)
        | ~ r2_hidden(k4_tarski(X23,X24),k2_zfmisc_1(X25,X26)) )
      & ( r2_hidden(X24,X26)
        | ~ r2_hidden(k4_tarski(X23,X24),k2_zfmisc_1(X25,X26)) )
      & ( ~ r2_hidden(X23,X25)
        | ~ r2_hidden(X24,X26)
        | r2_hidden(k4_tarski(X23,X24),k2_zfmisc_1(X25,X26)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_zfmisc_1])])])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(k4_tarski(esk6_0,esk7_0),k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_32])).

fof(c_0_40,plain,(
    ! [X9] :
      ( ( ~ v4_orders_2(X9)
        | r8_relat_2(u1_orders_2(X9),u1_struct_0(X9))
        | ~ l1_orders_2(X9) )
      & ( ~ r8_relat_2(u1_orders_2(X9),u1_struct_0(X9))
        | v4_orders_2(X9)
        | ~ l1_orders_2(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_orders_2])])])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( r2_hidden(k4_tarski(X3,X5),X1)
    | ~ r8_relat_2(X1,X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X4,X2)
    | ~ r2_hidden(X5,X2)
    | ~ r2_hidden(k4_tarski(X3,X4),X1)
    | ~ r2_hidden(k4_tarski(X4,X5),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( v1_relat_1(u1_orders_2(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_19])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk7_0),k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,plain,
    ( r8_relat_2(u1_orders_2(X1),u1_struct_0(X1))
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( v4_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_25])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_51,plain,
    ( r1_orders_2(X3,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk7_0),u1_orders_2(esk4_0))
    | ~ r2_hidden(k4_tarski(X1,esk6_0),u1_orders_2(esk4_0))
    | ~ r2_hidden(esk7_0,X2)
    | ~ r2_hidden(esk6_0,X2)
    | ~ r2_hidden(X1,X2)
    | ~ r8_relat_2(u1_orders_2(esk4_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_32]),c_0_43])])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk7_0,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk6_0,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_45])).

cnf(c_0_55,negated_conjecture,
    ( r8_relat_2(u1_orders_2(esk4_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_16])])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk5_0,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk6_0),u1_orders_2(esk4_0))
    | ~ r1_orders_2(esk4_0,X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_28]),c_0_16])])).

cnf(c_0_58,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_59,negated_conjecture,
    ( r1_orders_2(esk4_0,X1,esk7_0)
    | ~ r2_hidden(k4_tarski(X1,esk7_0),u1_orders_2(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_22]),c_0_16])])).

cnf(c_0_60,negated_conjecture,
    ( ~ r1_orders_2(esk4_0,esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk7_0),u1_orders_2(esk4_0))
    | ~ r2_hidden(k4_tarski(X1,esk6_0),u1_orders_2(esk4_0))
    | ~ r2_hidden(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_55])])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk5_0,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_54])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_0,esk6_0),u1_orders_2(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_50])])).

cnf(c_0_64,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk5_0,esk7_0),u1_orders_2(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_50]),c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])]),c_0_64]),
    [proof]).

%------------------------------------------------------------------------------
