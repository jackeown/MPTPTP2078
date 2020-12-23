%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1531+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:20 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   92 (7648 expanded)
%              Number of clauses        :   77 (3061 expanded)
%              Number of leaves         :    7 (1780 expanded)
%              Depth                    :   41
%              Number of atoms          :  294 (42750 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   18 (   3 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(c_0_7,negated_conjecture,(
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

fof(c_0_8,plain,(
    ! [X17,X18] :
      ( ( ~ m1_subset_1(X17,k1_zfmisc_1(X18))
        | r1_tarski(X17,X18) )
      & ( ~ r1_tarski(X17,X18)
        | m1_subset_1(X17,k1_zfmisc_1(X18)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_9,negated_conjecture,
    ( l1_orders_2(esk3_0)
    & r1_tarski(esk4_0,esk5_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk3_0))
    & ( r2_lattice3(esk3_0,esk5_0,esk6_0)
      | r1_lattice3(esk3_0,esk5_0,esk6_0) )
    & ( ~ r2_lattice3(esk3_0,esk4_0,esk6_0)
      | r1_lattice3(esk3_0,esk5_0,esk6_0) )
    & ( r2_lattice3(esk3_0,esk5_0,esk6_0)
      | ~ r1_lattice3(esk3_0,esk4_0,esk6_0) )
    & ( ~ r2_lattice3(esk3_0,esk4_0,esk6_0)
      | ~ r1_lattice3(esk3_0,esk4_0,esk6_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).

fof(c_0_10,plain,(
    ! [X19,X20,X21] :
      ( ~ r2_hidden(X19,X20)
      | ~ m1_subset_1(X20,k1_zfmisc_1(X21))
      | m1_subset_1(X19,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_11,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X10,X11,X12,X13] :
      ( ( ~ r2_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r2_hidden(X13,X11)
        | r1_orders_2(X10,X13,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ l1_orders_2(X10) )
      & ( m1_subset_1(esk2_3(X10,X11,X12),u1_struct_0(X10))
        | r2_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ l1_orders_2(X10) )
      & ( r2_hidden(esk2_3(X10,X11,X12),X11)
        | r2_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ l1_orders_2(X10) )
      & ( ~ r1_orders_2(X10,esk2_3(X10,X11,X12),X12)
        | r2_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ l1_orders_2(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

cnf(c_0_14,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_19,plain,(
    ! [X5,X6,X7,X8] :
      ( ( ~ r1_lattice3(X5,X6,X7)
        | ~ m1_subset_1(X8,u1_struct_0(X5))
        | ~ r2_hidden(X8,X6)
        | r1_orders_2(X5,X7,X8)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ l1_orders_2(X5) )
      & ( m1_subset_1(esk1_3(X5,X6,X7),u1_struct_0(X5))
        | r1_lattice3(X5,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ l1_orders_2(X5) )
      & ( r2_hidden(esk1_3(X5,X6,X7),X6)
        | r1_lattice3(X5,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ l1_orders_2(X5) )
      & ( ~ r1_orders_2(X5,X7,esk1_3(X5,X6,X7))
        | r1_lattice3(X5,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ l1_orders_2(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(X1,esk5_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | r2_hidden(esk2_3(esk3_0,X1,esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])])).

cnf(c_0_22,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( ~ r2_lattice3(esk3_0,esk4_0,esk6_0)
    | ~ r1_lattice3(esk3_0,esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,negated_conjecture,
    ( r2_lattice3(esk3_0,esk4_0,esk6_0)
    | m1_subset_1(esk2_3(esk3_0,esk4_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk1_3(esk3_0,X1,esk6_0),X1)
    | r1_lattice3(esk3_0,X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_17]),c_0_18])])).

cnf(c_0_26,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_27,plain,(
    ! [X22,X23,X24] :
      ( ~ r2_hidden(X22,X23)
      | ~ m1_subset_1(X23,k1_zfmisc_1(X24))
      | ~ v1_xboole_0(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_28,plain,(
    ! [X15,X16] :
      ( ~ m1_subset_1(X15,X16)
      | v1_xboole_0(X16)
      | r2_hidden(X15,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,esk4_0,esk6_0),esk5_0)
    | ~ r1_lattice3(esk3_0,esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( r1_lattice3(esk3_0,esk4_0,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk2_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_17]),c_0_18])])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),esk5_0)
    | m1_subset_1(esk2_3(esk3_0,esk4_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_lattice3(esk3_0,esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_15])).

cnf(c_0_37,negated_conjecture,
    ( v1_xboole_0(esk5_0)
    | r2_hidden(esk2_3(esk3_0,esk4_0,esk6_0),esk5_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,esk4_0,esk6_0),esk5_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),esk5_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( r1_orders_2(esk3_0,esk2_3(esk3_0,esk4_0,esk6_0),X1)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),esk5_0)
    | ~ r2_lattice3(esk3_0,X2,X1)
    | ~ r2_hidden(esk2_3(esk3_0,esk4_0,esk6_0),X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_18])])).

cnf(c_0_42,negated_conjecture,
    ( r2_lattice3(esk3_0,esk4_0,esk6_0)
    | r2_hidden(esk2_3(esk3_0,esk4_0,esk6_0),esk5_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_21])).

cnf(c_0_43,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0)
    | ~ r1_lattice3(esk3_0,esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_44,negated_conjecture,
    ( r2_lattice3(esk3_0,esk4_0,esk6_0)
    | r1_orders_2(esk3_0,esk2_3(esk3_0,esk4_0,esk6_0),X1)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),esk5_0)
    | ~ r2_lattice3(esk3_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_30])).

cnf(c_0_46,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk2_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_47,negated_conjecture,
    ( r2_lattice3(esk3_0,esk4_0,esk6_0)
    | r1_orders_2(esk3_0,esk2_3(esk3_0,esk4_0,esk6_0),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_17])])).

cnf(c_0_48,negated_conjecture,
    ( r2_lattice3(esk3_0,esk4_0,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_17]),c_0_18])])).

cnf(c_0_49,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_48]),c_0_30])).

cnf(c_0_51,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_17]),c_0_18])])).

cnf(c_0_52,negated_conjecture,
    ( v1_xboole_0(esk5_0)
    | r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_50])).

cnf(c_0_53,plain,
    ( r1_orders_2(X1,X3,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))
    | m1_subset_1(esk2_3(esk3_0,esk4_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),esk5_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | m1_subset_1(esk2_3(esk3_0,esk4_0,esk6_0),esk5_0)
    | ~ r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),X2)
    | ~ r1_lattice3(esk3_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_18])])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),esk5_0)
    | r1_lattice3(esk3_0,esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_25])).

cnf(c_0_58,negated_conjecture,
    ( r1_lattice3(esk3_0,esk5_0,esk6_0)
    | ~ r2_lattice3(esk3_0,esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_59,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | m1_subset_1(esk2_3(esk3_0,esk4_0,esk6_0),esk5_0)
    | ~ r1_lattice3(esk3_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_29])).

cnf(c_0_60,negated_conjecture,
    ( r1_lattice3(esk3_0,esk5_0,esk6_0)
    | m1_subset_1(esk2_3(esk3_0,esk4_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_24])).

cnf(c_0_61,plain,
    ( r1_lattice3(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,esk1_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_62,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))
    | m1_subset_1(esk2_3(esk3_0,esk4_0,esk6_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_17])])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,esk4_0,esk6_0),esk5_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_17]),c_0_18])]),c_0_29])).

cnf(c_0_64,negated_conjecture,
    ( v1_xboole_0(esk5_0)
    | r2_hidden(esk2_3(esk3_0,esk4_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_63])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))
    | m1_subset_1(esk2_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_51])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,esk4_0,esk6_0),esk5_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_64])).

cnf(c_0_67,negated_conjecture,
    ( r1_orders_2(esk3_0,esk2_3(esk3_0,esk4_0,esk6_0),X1)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r2_lattice3(esk3_0,X2,X1)
    | ~ r2_hidden(esk2_3(esk3_0,esk4_0,esk6_0),X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_65]),c_0_18])])).

cnf(c_0_68,negated_conjecture,
    ( r2_lattice3(esk3_0,esk4_0,esk6_0)
    | r2_hidden(esk2_3(esk3_0,esk4_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_21])).

cnf(c_0_69,negated_conjecture,
    ( r2_lattice3(esk3_0,esk4_0,esk6_0)
    | r1_orders_2(esk3_0,esk2_3(esk3_0,esk4_0,esk6_0),X1)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r2_lattice3(esk3_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_70,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_51])).

cnf(c_0_71,negated_conjecture,
    ( r2_lattice3(esk3_0,esk4_0,esk6_0)
    | r1_orders_2(esk3_0,esk2_3(esk3_0,esk4_0,esk6_0),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_17])])).

cnf(c_0_72,negated_conjecture,
    ( r2_lattice3(esk3_0,esk4_0,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_71]),c_0_17]),c_0_18])])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_72]),c_0_51])).

cnf(c_0_74,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),X2)
    | ~ r1_lattice3(esk3_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_73]),c_0_18])])).

cnf(c_0_75,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | r1_lattice3(esk3_0,esk4_0,esk6_0)
    | ~ r1_lattice3(esk3_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_57])).

cnf(c_0_76,negated_conjecture,
    ( r1_lattice3(esk3_0,esk5_0,esk6_0)
    | m1_subset_1(esk2_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_31])).

cnf(c_0_77,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))
    | m1_subset_1(esk2_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_17])]),c_0_35])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_77]),c_0_17]),c_0_18])]),c_0_35])).

cnf(c_0_79,negated_conjecture,
    ( r1_orders_2(esk3_0,esk2_3(esk3_0,esk4_0,esk6_0),X1)
    | ~ r2_lattice3(esk3_0,X2,X1)
    | ~ r2_hidden(esk2_3(esk3_0,esk4_0,esk6_0),X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_78]),c_0_18])])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,esk4_0,esk6_0),esk5_0)
    | r1_lattice3(esk3_0,esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_25])).

cnf(c_0_81,negated_conjecture,
    ( r1_orders_2(esk3_0,esk2_3(esk3_0,esk4_0,esk6_0),X1)
    | r1_lattice3(esk3_0,esk4_0,esk6_0)
    | ~ r2_lattice3(esk3_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_82,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0)
    | r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_83,negated_conjecture,
    ( r1_orders_2(esk3_0,esk2_3(esk3_0,esk4_0,esk6_0),esk6_0)
    | r1_lattice3(esk3_0,esk5_0,esk6_0)
    | r1_lattice3(esk3_0,esk4_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_17])])).

cnf(c_0_84,negated_conjecture,
    ( r1_lattice3(esk3_0,esk4_0,esk6_0)
    | r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_83]),c_0_17]),c_0_18])]),c_0_58])).

cnf(c_0_85,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))
    | r1_lattice3(esk3_0,esk4_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_84]),c_0_17])])).

cnf(c_0_86,negated_conjecture,
    ( r1_lattice3(esk3_0,esk4_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_85]),c_0_17]),c_0_18])])).

cnf(c_0_87,negated_conjecture,
    ( r2_lattice3(esk3_0,esk4_0,esk6_0)
    | r1_orders_2(esk3_0,esk2_3(esk3_0,esk4_0,esk6_0),X1)
    | ~ r2_lattice3(esk3_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_68])).

cnf(c_0_88,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_86])])).

cnf(c_0_89,negated_conjecture,
    ( ~ r2_lattice3(esk3_0,esk4_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_86])])).

cnf(c_0_90,negated_conjecture,
    ( r1_orders_2(esk3_0,esk2_3(esk3_0,esk4_0,esk6_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_17])]),c_0_89])).

cnf(c_0_91,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_90]),c_0_17]),c_0_18])]),c_0_89]),
    [proof]).

%------------------------------------------------------------------------------
