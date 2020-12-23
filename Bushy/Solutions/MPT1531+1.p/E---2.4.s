%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow_0__t9_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:48 EDT 2019

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 472 expanded)
%              Number of clauses        :   52 ( 185 expanded)
%              Number of leaves         :    9 ( 112 expanded)
%              Depth                    :   16
%              Number of atoms          :  230 (2704 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t9_yellow_0,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( r1_tarski(X2,X3)
         => ! [X4] :
              ( m1_subset_1(X4,u1_struct_0(X1))
             => ( ( r1_lattice3(X1,X3,X4)
                 => r1_lattice3(X1,X2,X4) )
                & ( r2_lattice3(X1,X3,X4)
                 => r2_lattice3(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t9_yellow_0.p',t9_yellow_0)).

fof(d9_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r2_lattice3(X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r1_orders_2(X1,X4,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t9_yellow_0.p',d9_lattice3)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t9_yellow_0.p',t3_subset)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t9_yellow_0.p',t4_subset)).

fof(d8_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r1_lattice3(X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r1_orders_2(X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t9_yellow_0.p',d8_lattice3)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t9_yellow_0.p',t2_subset)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t9_yellow_0.p',t7_boole)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t9_yellow_0.p',t5_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t9_yellow_0.p',existence_m1_subset_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2,X3] :
            ( r1_tarski(X2,X3)
           => ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( ( r1_lattice3(X1,X3,X4)
                   => r1_lattice3(X1,X2,X4) )
                  & ( r2_lattice3(X1,X3,X4)
                   => r2_lattice3(X1,X2,X4) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t9_yellow_0])).

fof(c_0_10,plain,(
    ! [X16,X17,X18,X19] :
      ( ( ~ r2_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ r2_hidden(X19,X17)
        | r1_orders_2(X16,X19,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ l1_orders_2(X16) )
      & ( m1_subset_1(esk6_3(X16,X17,X18),u1_struct_0(X16))
        | r2_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ l1_orders_2(X16) )
      & ( r2_hidden(esk6_3(X16,X17,X18),X17)
        | r2_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ l1_orders_2(X16) )
      & ( ~ r1_orders_2(X16,esk6_3(X16,X17,X18),X18)
        | r2_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ l1_orders_2(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

fof(c_0_11,negated_conjecture,
    ( l1_orders_2(esk1_0)
    & r1_tarski(esk2_0,esk3_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk1_0))
    & ( r2_lattice3(esk1_0,esk3_0,esk4_0)
      | r1_lattice3(esk1_0,esk3_0,esk4_0) )
    & ( ~ r2_lattice3(esk1_0,esk2_0,esk4_0)
      | r1_lattice3(esk1_0,esk3_0,esk4_0) )
    & ( r2_lattice3(esk1_0,esk3_0,esk4_0)
      | ~ r1_lattice3(esk1_0,esk2_0,esk4_0) )
    & ( ~ r2_lattice3(esk1_0,esk2_0,esk4_0)
      | ~ r1_lattice3(esk1_0,esk2_0,esk4_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).

fof(c_0_12,plain,(
    ! [X30,X31] :
      ( ( ~ m1_subset_1(X30,k1_zfmisc_1(X31))
        | r1_tarski(X30,X31) )
      & ( ~ r1_tarski(X30,X31)
        | m1_subset_1(X30,k1_zfmisc_1(X31)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_13,plain,
    ( m1_subset_1(esk6_3(X1,X2,X3),u1_struct_0(X1))
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X32,X33,X34] :
      ( ~ r2_hidden(X32,X33)
      | ~ m1_subset_1(X33,k1_zfmisc_1(X34))
      | m1_subset_1(X32,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_17,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_19,plain,(
    ! [X11,X12,X13,X14] :
      ( ( ~ r1_lattice3(X11,X12,X13)
        | ~ m1_subset_1(X14,u1_struct_0(X11))
        | ~ r2_hidden(X14,X12)
        | r1_orders_2(X11,X13,X14)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ l1_orders_2(X11) )
      & ( m1_subset_1(esk5_3(X11,X12,X13),u1_struct_0(X11))
        | r1_lattice3(X11,X12,X13)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ l1_orders_2(X11) )
      & ( r2_hidden(esk5_3(X11,X12,X13),X12)
        | r1_lattice3(X11,X12,X13)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ l1_orders_2(X11) )
      & ( ~ r1_orders_2(X11,X13,esk5_3(X11,X12,X13))
        | r1_lattice3(X11,X12,X13)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ l1_orders_2(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).

cnf(c_0_20,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( r2_lattice3(esk1_0,X1,esk4_0)
    | m1_subset_1(esk6_3(esk1_0,X1,esk4_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])])).

cnf(c_0_22,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk6_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_26,plain,
    ( m1_subset_1(esk5_3(X1,X2,X3),u1_struct_0(X1))
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( r1_orders_2(esk1_0,esk6_3(esk1_0,X1,esk4_0),X2)
    | r2_lattice3(esk1_0,X1,esk4_0)
    | ~ r2_hidden(esk6_3(esk1_0,X1,esk4_0),X3)
    | ~ r2_lattice3(esk1_0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_15])])).

cnf(c_0_28,negated_conjecture,
    ( r2_lattice3(esk1_0,X1,esk4_0)
    | ~ r1_orders_2(esk1_0,esk6_3(esk1_0,X1,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_14]),c_0_15])])).

fof(c_0_29,plain,(
    ! [X28,X29] :
      ( ~ m1_subset_1(X28,X29)
      | v1_xboole_0(X29)
      | r2_hidden(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(X1,esk3_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk6_3(esk1_0,X1,esk4_0),X1)
    | r2_lattice3(esk1_0,X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_14]),c_0_15])])).

fof(c_0_32,plain,(
    ! [X39,X40] :
      ( ~ r2_hidden(X39,X40)
      | ~ v1_xboole_0(X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_33,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X2)
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_34,plain,
    ( r1_orders_2(X1,X3,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_35,negated_conjecture,
    ( r1_lattice3(esk1_0,X1,esk4_0)
    | m1_subset_1(esk5_3(esk1_0,X1,esk4_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_14]),c_0_15])])).

cnf(c_0_36,plain,
    ( r1_lattice3(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,esk5_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_37,negated_conjecture,
    ( r2_lattice3(esk1_0,X1,esk4_0)
    | ~ r2_hidden(esk6_3(esk1_0,X1,esk4_0),X2)
    | ~ r2_lattice3(esk1_0,X2,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_14]),c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( r2_lattice3(esk1_0,esk3_0,esk4_0)
    | r1_lattice3(esk1_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_39,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,negated_conjecture,
    ( r2_lattice3(esk1_0,esk2_0,esk4_0)
    | m1_subset_1(esk6_3(esk1_0,esk2_0,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,X1,esk4_0),X1)
    | r1_lattice3(esk1_0,X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_14]),c_0_15])])).

cnf(c_0_43,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk5_3(esk1_0,X2,esk4_0))
    | r1_lattice3(esk1_0,X2,esk4_0)
    | ~ r2_hidden(esk5_3(esk1_0,X2,esk4_0),X3)
    | ~ r1_lattice3(esk1_0,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_15])])).

cnf(c_0_44,negated_conjecture,
    ( r1_lattice3(esk1_0,X1,esk4_0)
    | ~ r1_orders_2(esk1_0,esk4_0,esk5_3(esk1_0,X1,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_14]),c_0_15])])).

cnf(c_0_45,negated_conjecture,
    ( r2_lattice3(esk1_0,X1,esk4_0)
    | r1_lattice3(esk1_0,esk3_0,esk4_0)
    | ~ r2_hidden(esk6_3(esk1_0,X1,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | r2_hidden(esk6_3(esk1_0,esk2_0,esk4_0),esk3_0)
    | r2_lattice3(esk1_0,esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( r1_lattice3(esk1_0,esk3_0,esk4_0)
    | ~ r2_lattice3(esk1_0,esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_48,negated_conjecture,
    ( r1_lattice3(esk1_0,X1,esk4_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( r1_lattice3(esk1_0,X1,esk4_0)
    | ~ r2_hidden(esk5_3(esk1_0,X1,esk4_0),X2)
    | ~ r1_lattice3(esk1_0,X2,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_14]),c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( r1_lattice3(esk1_0,esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk4_0)
    | m1_subset_1(esk5_3(esk1_0,esk2_0,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( r1_lattice3(esk1_0,X1,esk4_0)
    | ~ r2_hidden(esk5_3(esk1_0,X1,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | r2_hidden(esk5_3(esk1_0,esk2_0,esk4_0),esk3_0)
    | r1_lattice3(esk1_0,esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_51])).

cnf(c_0_54,negated_conjecture,
    ( r2_lattice3(esk1_0,esk3_0,esk4_0)
    | ~ r1_lattice3(esk1_0,esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_55,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | r1_lattice3(esk1_0,esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( r2_lattice3(esk1_0,X1,esk4_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_31])).

cnf(c_0_57,negated_conjecture,
    ( r2_lattice3(esk1_0,esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])).

fof(c_0_58,plain,(
    ! [X35,X36,X37] :
      ( ~ r2_hidden(X35,X36)
      | ~ m1_subset_1(X36,k1_zfmisc_1(X37))
      | ~ v1_xboole_0(X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_59,negated_conjecture,
    ( r2_lattice3(esk1_0,X1,esk4_0)
    | ~ r2_hidden(esk6_3(esk1_0,X1,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_57])).

cnf(c_0_60,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( ~ r2_lattice3(esk1_0,esk2_0,esk4_0)
    | ~ r1_lattice3(esk1_0,esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_62,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | r2_lattice3(esk1_0,esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_46])).

fof(c_0_63,plain,(
    ! [X24] : m1_subset_1(esk9_1(X24),X24) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_64,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_24])).

cnf(c_0_65,negated_conjecture,
    ( v1_xboole_0(esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_55])).

cnf(c_0_66,plain,
    ( m1_subset_1(esk9_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( ~ r2_hidden(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_65])])).

cnf(c_0_68,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk9_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_66])).

cnf(c_0_69,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_56]),c_0_48])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69]),
    [proof]).
%------------------------------------------------------------------------------
