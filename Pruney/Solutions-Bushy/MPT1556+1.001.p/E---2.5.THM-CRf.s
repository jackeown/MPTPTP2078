%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1556+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:23 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 133 expanded)
%              Number of clauses        :   37 (  54 expanded)
%              Number of leaves         :    8 (  32 expanded)
%              Depth                    :   19
%              Number of atoms          :  212 ( 603 expanded)
%              Number of equality atoms :    9 (  15 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t34_yellow_0,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( ( r1_tarski(X2,X3)
            & r1_yellow_0(X1,X2)
            & r1_yellow_0(X1,X3) )
         => r1_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_yellow_0)).

fof(d9_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r1_yellow_0(X1,X2)
           => ( X3 = k1_yellow_0(X1,X2)
            <=> ( r2_lattice3(X1,X2,X3)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r2_lattice3(X1,X2,X4)
                     => r1_orders_2(X1,X3,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).

fof(dt_k1_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

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

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2,X3] :
            ( ( r1_tarski(X2,X3)
              & r1_yellow_0(X1,X2)
              & r1_yellow_0(X1,X3) )
           => r1_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t34_yellow_0])).

fof(c_0_9,plain,(
    ! [X10,X11,X12,X13] :
      ( ( r2_lattice3(X10,X11,X12)
        | X12 != k1_yellow_0(X10,X11)
        | ~ r1_yellow_0(X10,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ l1_orders_2(X10) )
      & ( ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r2_lattice3(X10,X11,X13)
        | r1_orders_2(X10,X12,X13)
        | X12 != k1_yellow_0(X10,X11)
        | ~ r1_yellow_0(X10,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ l1_orders_2(X10) )
      & ( m1_subset_1(esk2_3(X10,X11,X12),u1_struct_0(X10))
        | ~ r2_lattice3(X10,X11,X12)
        | X12 = k1_yellow_0(X10,X11)
        | ~ r1_yellow_0(X10,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ l1_orders_2(X10) )
      & ( r2_lattice3(X10,X11,esk2_3(X10,X11,X12))
        | ~ r2_lattice3(X10,X11,X12)
        | X12 = k1_yellow_0(X10,X11)
        | ~ r1_yellow_0(X10,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ l1_orders_2(X10) )
      & ( ~ r1_orders_2(X10,X12,esk2_3(X10,X11,X12))
        | ~ r2_lattice3(X10,X11,X12)
        | X12 = k1_yellow_0(X10,X11)
        | ~ r1_yellow_0(X10,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ l1_orders_2(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).

fof(c_0_10,plain,(
    ! [X15,X16] :
      ( ~ l1_orders_2(X15)
      | m1_subset_1(k1_yellow_0(X15,X16),u1_struct_0(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

fof(c_0_11,plain,(
    ! [X19,X20] :
      ( ( ~ m1_subset_1(X19,k1_zfmisc_1(X20))
        | r1_tarski(X19,X20) )
      & ( ~ r1_tarski(X19,X20)
        | m1_subset_1(X19,k1_zfmisc_1(X20)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_12,negated_conjecture,
    ( l1_orders_2(esk3_0)
    & r1_tarski(esk4_0,esk5_0)
    & r1_yellow_0(esk3_0,esk4_0)
    & r1_yellow_0(esk3_0,esk5_0)
    & ~ r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk4_0),k1_yellow_0(esk3_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_13,plain,
    ( r2_lattice3(X1,X2,X3)
    | X3 != k1_yellow_0(X1,X2)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X21,X22,X23] :
      ( ~ r2_hidden(X21,X22)
      | ~ m1_subset_1(X22,k1_zfmisc_1(X23))
      | m1_subset_1(X21,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_16,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X5,X6,X7,X8] :
      ( ( ~ r2_lattice3(X5,X6,X7)
        | ~ m1_subset_1(X8,u1_struct_0(X5))
        | ~ r2_hidden(X8,X6)
        | r1_orders_2(X5,X8,X7)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ l1_orders_2(X5) )
      & ( m1_subset_1(esk1_3(X5,X6,X7),u1_struct_0(X5))
        | r2_lattice3(X5,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ l1_orders_2(X5) )
      & ( r2_hidden(esk1_3(X5,X6,X7),X6)
        | r2_lattice3(X5,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ l1_orders_2(X5) )
      & ( ~ r1_orders_2(X5,esk1_3(X5,X6,X7),X7)
        | r2_lattice3(X5,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ l1_orders_2(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

cnf(c_0_19,plain,
    ( r2_lattice3(X1,X2,k1_yellow_0(X1,X2))
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_13]),c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( r1_yellow_0(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,k1_yellow_0(esk3_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

fof(c_0_26,plain,(
    ! [X17,X18] :
      ( ~ m1_subset_1(X17,X18)
      | v1_xboole_0(X18)
      | r2_hidden(X17,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(X1,esk5_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk1_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,k1_yellow_0(esk3_0,esk5_0))
    | ~ r2_hidden(X1,esk5_0)
    | ~ m1_subset_1(k1_yellow_0(esk3_0,esk5_0),u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_21])])).

cnf(c_0_31,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( r2_lattice3(X1,esk4_0,X2)
    | m1_subset_1(esk1_3(X1,esk4_0,X2),esk5_0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_33,plain,(
    ! [X24,X25,X26] :
      ( ~ r2_hidden(X24,X25)
      | ~ m1_subset_1(X25,k1_zfmisc_1(X26))
      | ~ v1_xboole_0(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_34,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,k1_yellow_0(esk3_0,esk5_0))
    | ~ r2_hidden(esk1_3(esk3_0,X1,k1_yellow_0(esk3_0,esk5_0)),esk5_0)
    | ~ m1_subset_1(esk1_3(esk3_0,X1,k1_yellow_0(esk3_0,esk5_0)),u1_struct_0(esk3_0))
    | ~ m1_subset_1(k1_yellow_0(esk3_0,esk5_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_21])])).

cnf(c_0_35,negated_conjecture,
    ( v1_xboole_0(esk5_0)
    | r2_hidden(esk1_3(X1,esk4_0,X2),esk5_0)
    | r2_lattice3(X1,esk4_0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( v1_xboole_0(esk5_0)
    | r2_lattice3(esk3_0,esk4_0,k1_yellow_0(esk3_0,esk5_0))
    | ~ m1_subset_1(esk1_3(esk3_0,esk4_0,k1_yellow_0(esk3_0,esk5_0)),u1_struct_0(esk3_0))
    | ~ m1_subset_1(k1_yellow_0(esk3_0,esk5_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_21])])).

cnf(c_0_38,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_39,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_23])).

cnf(c_0_40,negated_conjecture,
    ( v1_xboole_0(esk5_0)
    | r2_lattice3(esk3_0,esk4_0,k1_yellow_0(esk3_0,esk5_0))
    | ~ m1_subset_1(k1_yellow_0(esk3_0,esk5_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_21])])).

cnf(c_0_41,negated_conjecture,
    ( r2_lattice3(esk3_0,esk4_0,k1_yellow_0(esk3_0,esk5_0))
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(k1_yellow_0(esk3_0,esk5_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_42,negated_conjecture,
    ( r2_lattice3(esk3_0,esk4_0,k1_yellow_0(esk3_0,esk5_0))
    | r2_lattice3(X1,esk4_0,X2)
    | ~ m1_subset_1(k1_yellow_0(esk3_0,esk5_0),u1_struct_0(esk3_0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_28])).

cnf(c_0_43,negated_conjecture,
    ( r2_lattice3(esk3_0,esk4_0,k1_yellow_0(esk3_0,esk5_0))
    | r2_lattice3(X1,esk4_0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_14]),c_0_21])])).

cnf(c_0_44,negated_conjecture,
    ( r2_lattice3(esk3_0,esk4_0,k1_yellow_0(esk3_0,esk5_0))
    | r2_lattice3(X1,esk4_0,k1_yellow_0(X1,X2))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_14])).

cnf(c_0_45,negated_conjecture,
    ( r2_lattice3(esk3_0,esk4_0,k1_yellow_0(esk3_0,esk5_0))
    | r2_lattice3(esk3_0,esk4_0,k1_yellow_0(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_21])).

cnf(c_0_46,plain,
    ( r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | X4 != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_47,negated_conjecture,
    ( r2_lattice3(esk3_0,esk4_0,k1_yellow_0(esk3_0,esk5_0)) ),
    inference(ef,[status(thm)],[c_0_45])).

cnf(c_0_48,negated_conjecture,
    ( r1_yellow_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_49,negated_conjecture,
    ( ~ r1_orders_2(esk3_0,k1_yellow_0(esk3_0,esk4_0),k1_yellow_0(esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_50,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,k1_yellow_0(esk3_0,esk5_0))
    | X1 != k1_yellow_0(esk3_0,esk4_0)
    | ~ m1_subset_1(k1_yellow_0(esk3_0,esk5_0),u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_21])])).

cnf(c_0_51,negated_conjecture,
    ( ~ m1_subset_1(k1_yellow_0(esk3_0,esk5_0),u1_struct_0(esk3_0))
    | ~ m1_subset_1(k1_yellow_0(esk3_0,esk4_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_52,negated_conjecture,
    ( ~ m1_subset_1(k1_yellow_0(esk3_0,esk4_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_14]),c_0_21])])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_14]),c_0_21])]),
    [proof]).

%------------------------------------------------------------------------------
