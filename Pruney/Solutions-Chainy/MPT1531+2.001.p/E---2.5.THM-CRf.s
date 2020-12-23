%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:13 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 526 expanded)
%              Number of clauses        :   55 ( 199 expanded)
%              Number of leaves         :    9 ( 130 expanded)
%              Depth                    :   16
%              Number of atoms          :  260 (2935 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

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

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

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

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(c_0_9,plain,(
    ! [X30,X31,X32] :
      ( ~ r2_hidden(X30,X31)
      | ~ m1_subset_1(X31,k1_zfmisc_1(X32))
      | ~ v1_xboole_0(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_10,plain,(
    ! [X25,X26] :
      ( ( ~ m1_subset_1(X25,k1_zfmisc_1(X26))
        | r1_tarski(X25,X26) )
      & ( ~ r1_tarski(X25,X26)
        | m1_subset_1(X25,k1_zfmisc_1(X26)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_11,negated_conjecture,(
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

cnf(c_0_12,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,negated_conjecture,
    ( l1_orders_2(esk5_0)
    & r1_tarski(esk6_0,esk7_0)
    & m1_subset_1(esk8_0,u1_struct_0(esk5_0))
    & ( r2_lattice3(esk5_0,esk7_0,esk8_0)
      | r1_lattice3(esk5_0,esk7_0,esk8_0) )
    & ( ~ r2_lattice3(esk5_0,esk6_0,esk8_0)
      | r1_lattice3(esk5_0,esk7_0,esk8_0) )
    & ( r2_lattice3(esk5_0,esk7_0,esk8_0)
      | ~ r1_lattice3(esk5_0,esk6_0,esk8_0) )
    & ( ~ r2_lattice3(esk5_0,esk6_0,esk8_0)
      | ~ r1_lattice3(esk5_0,esk6_0,esk8_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).

fof(c_0_15,plain,(
    ! [X42,X43,X44,X45] :
      ( ( ~ r2_lattice3(X42,X43,X44)
        | ~ m1_subset_1(X45,u1_struct_0(X42))
        | ~ r2_hidden(X45,X43)
        | r1_orders_2(X42,X45,X44)
        | ~ m1_subset_1(X44,u1_struct_0(X42))
        | ~ l1_orders_2(X42) )
      & ( m1_subset_1(esk4_3(X42,X43,X44),u1_struct_0(X42))
        | r2_lattice3(X42,X43,X44)
        | ~ m1_subset_1(X44,u1_struct_0(X42))
        | ~ l1_orders_2(X42) )
      & ( r2_hidden(esk4_3(X42,X43,X44),X43)
        | r2_lattice3(X42,X43,X44)
        | ~ m1_subset_1(X44,u1_struct_0(X42))
        | ~ l1_orders_2(X42) )
      & ( ~ r1_orders_2(X42,esk4_3(X42,X43,X44),X44)
        | r2_lattice3(X42,X43,X44)
        | ~ m1_subset_1(X44,u1_struct_0(X42))
        | ~ l1_orders_2(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

cnf(c_0_16,plain,
    ( ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_19,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( r2_lattice3(esk5_0,esk7_0,esk8_0)
    | r1_lattice3(esk5_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( ~ r2_hidden(X1,esk6_0)
    | ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_25,plain,(
    ! [X37,X38,X39,X40] :
      ( ( ~ r1_lattice3(X37,X38,X39)
        | ~ m1_subset_1(X40,u1_struct_0(X37))
        | ~ r2_hidden(X40,X38)
        | r1_orders_2(X37,X39,X40)
        | ~ m1_subset_1(X39,u1_struct_0(X37))
        | ~ l1_orders_2(X37) )
      & ( m1_subset_1(esk3_3(X37,X38,X39),u1_struct_0(X37))
        | r1_lattice3(X37,X38,X39)
        | ~ m1_subset_1(X39,u1_struct_0(X37))
        | ~ l1_orders_2(X37) )
      & ( r2_hidden(esk3_3(X37,X38,X39),X38)
        | r1_lattice3(X37,X38,X39)
        | ~ m1_subset_1(X39,u1_struct_0(X37))
        | ~ l1_orders_2(X37) )
      & ( ~ r1_orders_2(X37,X39,esk3_3(X37,X38,X39))
        | r1_lattice3(X37,X38,X39)
        | ~ m1_subset_1(X39,u1_struct_0(X37))
        | ~ l1_orders_2(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).

fof(c_0_26,plain,(
    ! [X27,X28,X29] :
      ( ~ r2_hidden(X27,X28)
      | ~ m1_subset_1(X28,k1_zfmisc_1(X29))
      | m1_subset_1(X27,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_27,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk4_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,negated_conjecture,
    ( r1_orders_2(esk5_0,X1,esk8_0)
    | r1_lattice3(esk5_0,esk7_0,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22])])).

cnf(c_0_30,negated_conjecture,
    ( ~ r2_lattice3(esk5_0,esk6_0,esk8_0)
    | ~ r1_lattice3(esk5_0,esk6_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_31,negated_conjecture,
    ( r2_lattice3(X1,esk6_0,X2)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_34,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_24])).

cnf(c_0_36,negated_conjecture,
    ( r2_lattice3(esk5_0,X1,esk8_0)
    | r1_lattice3(esk5_0,esk7_0,esk8_0)
    | ~ m1_subset_1(esk4_3(esk5_0,X1,esk8_0),u1_struct_0(esk5_0))
    | ~ r2_hidden(esk4_3(esk5_0,X1,esk8_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_21]),c_0_22])])).

cnf(c_0_37,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_38,plain,(
    ! [X23,X24] :
      ( ~ m1_subset_1(X23,X24)
      | v1_xboole_0(X24)
      | r2_hidden(X23,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_39,negated_conjecture,
    ( ~ r1_lattice3(esk5_0,esk6_0,esk8_0)
    | ~ v1_xboole_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_21]),c_0_22])])).

cnf(c_0_40,plain,
    ( r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( v1_xboole_0(esk6_0)
    | ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_33])).

cnf(c_0_42,plain,
    ( m1_subset_1(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_34,c_0_13])).

cnf(c_0_43,negated_conjecture,
    ( ~ r1_lattice3(esk5_0,esk6_0,esk8_0)
    | ~ v1_xboole_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_35]),c_0_21]),c_0_22])])).

cnf(c_0_44,negated_conjecture,
    ( r2_lattice3(esk5_0,X1,esk8_0)
    | r1_lattice3(esk5_0,esk7_0,esk8_0)
    | ~ r2_hidden(esk4_3(esk5_0,X1,esk8_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_21]),c_0_22])])).

cnf(c_0_45,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_21]),c_0_22])]),c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(X1,esk7_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_17])).

cnf(c_0_48,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_40]),c_0_21]),c_0_22])])).

fof(c_0_49,plain,(
    ! [X21,X22] :
      ( ~ r2_hidden(X21,X22)
      | m1_subset_1(X21,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_50,negated_conjecture,
    ( r2_lattice3(esk5_0,X1,esk8_0)
    | r1_lattice3(esk5_0,esk7_0,esk8_0)
    | ~ m1_subset_1(esk4_3(esk5_0,X1,esk8_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(X1,esk7_0)
    | ~ m1_subset_1(X1,esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_45]),c_0_48])).

cnf(c_0_52,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( r2_lattice3(esk5_0,X1,esk8_0)
    | r1_lattice3(esk5_0,esk7_0,esk8_0)
    | ~ m1_subset_1(esk4_3(esk5_0,X1,esk8_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_54,plain,
    ( r2_lattice3(X1,X2,X3)
    | m1_subset_1(esk4_3(X1,X2,X3),X2)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_24])).

cnf(c_0_55,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,esk8_0)
    | ~ r2_lattice3(esk5_0,esk6_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_56,negated_conjecture,
    ( r2_lattice3(esk5_0,esk7_0,esk8_0)
    | ~ r1_lattice3(esk5_0,esk6_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_57,plain,
    ( r1_orders_2(X1,X3,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_58,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_21]),c_0_22])]),c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( r1_orders_2(esk5_0,X1,esk8_0)
    | ~ r1_lattice3(esk5_0,esk6_0,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_56]),c_0_21]),c_0_22])])).

cnf(c_0_60,plain,
    ( r1_lattice3(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,esk3_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_61,negated_conjecture,
    ( r1_orders_2(esk5_0,esk8_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_21]),c_0_22])])).

cnf(c_0_62,negated_conjecture,
    ( r2_lattice3(esk5_0,X1,esk8_0)
    | ~ r1_lattice3(esk5_0,esk6_0,esk8_0)
    | ~ m1_subset_1(esk4_3(esk5_0,X1,esk8_0),u1_struct_0(esk5_0))
    | ~ r2_hidden(esk4_3(esk5_0,X1,esk8_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_59]),c_0_21]),c_0_22])])).

cnf(c_0_63,negated_conjecture,
    ( r1_lattice3(esk5_0,X1,esk8_0)
    | ~ m1_subset_1(esk3_3(esk5_0,X1,esk8_0),u1_struct_0(esk5_0))
    | ~ r2_hidden(esk3_3(esk5_0,X1,esk8_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_21]),c_0_22])])).

cnf(c_0_64,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_65,negated_conjecture,
    ( r2_lattice3(esk5_0,X1,esk8_0)
    | ~ r1_lattice3(esk5_0,esk6_0,esk8_0)
    | ~ r2_hidden(esk4_3(esk5_0,X1,esk8_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_37]),c_0_21]),c_0_22])])).

cnf(c_0_66,negated_conjecture,
    ( r1_lattice3(esk5_0,X1,esk8_0)
    | ~ r2_hidden(esk3_3(esk5_0,X1,esk8_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_21]),c_0_22])])).

cnf(c_0_67,negated_conjecture,
    ( r2_lattice3(esk5_0,X1,esk8_0)
    | ~ r1_lattice3(esk5_0,esk6_0,esk8_0)
    | ~ m1_subset_1(esk4_3(esk5_0,X1,esk8_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_45]),c_0_46])).

cnf(c_0_68,negated_conjecture,
    ( r1_lattice3(esk5_0,X1,esk8_0)
    | ~ m1_subset_1(esk3_3(esk5_0,X1,esk8_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_45]),c_0_46])).

cnf(c_0_69,negated_conjecture,
    ( r2_lattice3(esk5_0,X1,esk8_0)
    | ~ r1_lattice3(esk5_0,esk6_0,esk8_0)
    | ~ m1_subset_1(esk4_3(esk5_0,X1,esk8_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_51])).

cnf(c_0_70,negated_conjecture,
    ( r1_lattice3(esk5_0,X1,esk8_0)
    | ~ m1_subset_1(esk3_3(esk5_0,X1,esk8_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_51])).

cnf(c_0_71,plain,
    ( r1_lattice3(X1,X2,X3)
    | m1_subset_1(esk3_3(X1,X2,X3),X2)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_32])).

cnf(c_0_72,negated_conjecture,
    ( ~ r1_lattice3(esk5_0,esk6_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_54]),c_0_21]),c_0_22])]),c_0_30])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_21]),c_0_22])]),c_0_72]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:54:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.13/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.038 s
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.13/0.40  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.40  fof(t9_yellow_0, conjecture, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r1_lattice3(X1,X3,X4)=>r1_lattice3(X1,X2,X4))&(r2_lattice3(X1,X3,X4)=>r2_lattice3(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_yellow_0)).
% 0.13/0.40  fof(d9_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 0.13/0.40  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.13/0.40  fof(d8_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattice3)).
% 0.13/0.40  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.13/0.40  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.13/0.40  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.13/0.40  fof(c_0_9, plain, ![X30, X31, X32]:(~r2_hidden(X30,X31)|~m1_subset_1(X31,k1_zfmisc_1(X32))|~v1_xboole_0(X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.13/0.40  fof(c_0_10, plain, ![X25, X26]:((~m1_subset_1(X25,k1_zfmisc_1(X26))|r1_tarski(X25,X26))&(~r1_tarski(X25,X26)|m1_subset_1(X25,k1_zfmisc_1(X26)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.40  fof(c_0_11, negated_conjecture, ~(![X1]:(l1_orders_2(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r1_lattice3(X1,X3,X4)=>r1_lattice3(X1,X2,X4))&(r2_lattice3(X1,X3,X4)=>r2_lattice3(X1,X2,X4))))))), inference(assume_negation,[status(cth)],[t9_yellow_0])).
% 0.13/0.40  cnf(c_0_12, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.40  cnf(c_0_13, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.40  fof(c_0_14, negated_conjecture, (l1_orders_2(esk5_0)&(r1_tarski(esk6_0,esk7_0)&(m1_subset_1(esk8_0,u1_struct_0(esk5_0))&(((r2_lattice3(esk5_0,esk7_0,esk8_0)|r1_lattice3(esk5_0,esk7_0,esk8_0))&(~r2_lattice3(esk5_0,esk6_0,esk8_0)|r1_lattice3(esk5_0,esk7_0,esk8_0)))&((r2_lattice3(esk5_0,esk7_0,esk8_0)|~r1_lattice3(esk5_0,esk6_0,esk8_0))&(~r2_lattice3(esk5_0,esk6_0,esk8_0)|~r1_lattice3(esk5_0,esk6_0,esk8_0))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).
% 0.13/0.40  fof(c_0_15, plain, ![X42, X43, X44, X45]:((~r2_lattice3(X42,X43,X44)|(~m1_subset_1(X45,u1_struct_0(X42))|(~r2_hidden(X45,X43)|r1_orders_2(X42,X45,X44)))|~m1_subset_1(X44,u1_struct_0(X42))|~l1_orders_2(X42))&((m1_subset_1(esk4_3(X42,X43,X44),u1_struct_0(X42))|r2_lattice3(X42,X43,X44)|~m1_subset_1(X44,u1_struct_0(X42))|~l1_orders_2(X42))&((r2_hidden(esk4_3(X42,X43,X44),X43)|r2_lattice3(X42,X43,X44)|~m1_subset_1(X44,u1_struct_0(X42))|~l1_orders_2(X42))&(~r1_orders_2(X42,esk4_3(X42,X43,X44),X44)|r2_lattice3(X42,X43,X44)|~m1_subset_1(X44,u1_struct_0(X42))|~l1_orders_2(X42))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).
% 0.13/0.40  cnf(c_0_16, plain, (~r1_tarski(X1,X2)|~r2_hidden(X3,X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.13/0.40  cnf(c_0_17, negated_conjecture, (r1_tarski(esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.40  fof(c_0_18, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.13/0.40  cnf(c_0_19, plain, (r1_orders_2(X1,X4,X3)|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.40  cnf(c_0_20, negated_conjecture, (r2_lattice3(esk5_0,esk7_0,esk8_0)|r1_lattice3(esk5_0,esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.40  cnf(c_0_21, negated_conjecture, (l1_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.40  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.40  cnf(c_0_23, negated_conjecture, (~r2_hidden(X1,esk6_0)|~v1_xboole_0(esk7_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.13/0.40  cnf(c_0_24, plain, (r2_hidden(esk4_3(X1,X2,X3),X2)|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.40  fof(c_0_25, plain, ![X37, X38, X39, X40]:((~r1_lattice3(X37,X38,X39)|(~m1_subset_1(X40,u1_struct_0(X37))|(~r2_hidden(X40,X38)|r1_orders_2(X37,X39,X40)))|~m1_subset_1(X39,u1_struct_0(X37))|~l1_orders_2(X37))&((m1_subset_1(esk3_3(X37,X38,X39),u1_struct_0(X37))|r1_lattice3(X37,X38,X39)|~m1_subset_1(X39,u1_struct_0(X37))|~l1_orders_2(X37))&((r2_hidden(esk3_3(X37,X38,X39),X38)|r1_lattice3(X37,X38,X39)|~m1_subset_1(X39,u1_struct_0(X37))|~l1_orders_2(X37))&(~r1_orders_2(X37,X39,esk3_3(X37,X38,X39))|r1_lattice3(X37,X38,X39)|~m1_subset_1(X39,u1_struct_0(X37))|~l1_orders_2(X37))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).
% 0.13/0.40  fof(c_0_26, plain, ![X27, X28, X29]:(~r2_hidden(X27,X28)|~m1_subset_1(X28,k1_zfmisc_1(X29))|m1_subset_1(X27,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.13/0.40  cnf(c_0_27, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.40  cnf(c_0_28, plain, (r2_lattice3(X1,X2,X3)|~r1_orders_2(X1,esk4_3(X1,X2,X3),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.40  cnf(c_0_29, negated_conjecture, (r1_orders_2(esk5_0,X1,esk8_0)|r1_lattice3(esk5_0,esk7_0,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk5_0))|~r2_hidden(X1,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22])])).
% 0.13/0.40  cnf(c_0_30, negated_conjecture, (~r2_lattice3(esk5_0,esk6_0,esk8_0)|~r1_lattice3(esk5_0,esk6_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.40  cnf(c_0_31, negated_conjecture, (r2_lattice3(X1,esk6_0,X2)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v1_xboole_0(esk7_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.40  cnf(c_0_32, plain, (r2_hidden(esk3_3(X1,X2,X3),X2)|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.40  cnf(c_0_33, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.40  cnf(c_0_34, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.40  cnf(c_0_35, plain, (r2_lattice3(X1,X2,X3)|~l1_orders_2(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_27, c_0_24])).
% 0.13/0.40  cnf(c_0_36, negated_conjecture, (r2_lattice3(esk5_0,X1,esk8_0)|r1_lattice3(esk5_0,esk7_0,esk8_0)|~m1_subset_1(esk4_3(esk5_0,X1,esk8_0),u1_struct_0(esk5_0))|~r2_hidden(esk4_3(esk5_0,X1,esk8_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_21]), c_0_22])])).
% 0.13/0.40  cnf(c_0_37, plain, (m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.40  fof(c_0_38, plain, ![X23, X24]:(~m1_subset_1(X23,X24)|(v1_xboole_0(X24)|r2_hidden(X23,X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.13/0.40  cnf(c_0_39, negated_conjecture, (~r1_lattice3(esk5_0,esk6_0,esk8_0)|~v1_xboole_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_21]), c_0_22])])).
% 0.13/0.40  cnf(c_0_40, plain, (r1_lattice3(X1,X2,X3)|~l1_orders_2(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_27, c_0_32])).
% 0.13/0.40  cnf(c_0_41, negated_conjecture, (v1_xboole_0(esk6_0)|~v1_xboole_0(esk7_0)), inference(spm,[status(thm)],[c_0_23, c_0_33])).
% 0.13/0.40  cnf(c_0_42, plain, (m1_subset_1(X1,X2)|~r1_tarski(X3,X2)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_34, c_0_13])).
% 0.13/0.40  cnf(c_0_43, negated_conjecture, (~r1_lattice3(esk5_0,esk6_0,esk8_0)|~v1_xboole_0(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_35]), c_0_21]), c_0_22])])).
% 0.13/0.40  cnf(c_0_44, negated_conjecture, (r2_lattice3(esk5_0,X1,esk8_0)|r1_lattice3(esk5_0,esk7_0,esk8_0)|~r2_hidden(esk4_3(esk5_0,X1,esk8_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_21]), c_0_22])])).
% 0.13/0.40  cnf(c_0_45, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.40  cnf(c_0_46, negated_conjecture, (~v1_xboole_0(esk7_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_21]), c_0_22])]), c_0_41])).
% 0.13/0.40  cnf(c_0_47, negated_conjecture, (m1_subset_1(X1,esk7_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_42, c_0_17])).
% 0.13/0.40  cnf(c_0_48, negated_conjecture, (~v1_xboole_0(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_40]), c_0_21]), c_0_22])])).
% 0.13/0.40  fof(c_0_49, plain, ![X21, X22]:(~r2_hidden(X21,X22)|m1_subset_1(X21,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.13/0.40  cnf(c_0_50, negated_conjecture, (r2_lattice3(esk5_0,X1,esk8_0)|r1_lattice3(esk5_0,esk7_0,esk8_0)|~m1_subset_1(esk4_3(esk5_0,X1,esk8_0),esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])).
% 0.13/0.40  cnf(c_0_51, negated_conjecture, (m1_subset_1(X1,esk7_0)|~m1_subset_1(X1,esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_45]), c_0_48])).
% 0.13/0.40  cnf(c_0_52, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.13/0.40  cnf(c_0_53, negated_conjecture, (r2_lattice3(esk5_0,X1,esk8_0)|r1_lattice3(esk5_0,esk7_0,esk8_0)|~m1_subset_1(esk4_3(esk5_0,X1,esk8_0),esk6_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.13/0.40  cnf(c_0_54, plain, (r2_lattice3(X1,X2,X3)|m1_subset_1(esk4_3(X1,X2,X3),X2)|~l1_orders_2(X1)|~m1_subset_1(X3,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_52, c_0_24])).
% 0.13/0.40  cnf(c_0_55, negated_conjecture, (r1_lattice3(esk5_0,esk7_0,esk8_0)|~r2_lattice3(esk5_0,esk6_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.40  cnf(c_0_56, negated_conjecture, (r2_lattice3(esk5_0,esk7_0,esk8_0)|~r1_lattice3(esk5_0,esk6_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.40  cnf(c_0_57, plain, (r1_orders_2(X1,X3,X4)|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.40  cnf(c_0_58, negated_conjecture, (r1_lattice3(esk5_0,esk7_0,esk8_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_21]), c_0_22])]), c_0_55])).
% 0.13/0.40  cnf(c_0_59, negated_conjecture, (r1_orders_2(esk5_0,X1,esk8_0)|~r1_lattice3(esk5_0,esk6_0,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk5_0))|~r2_hidden(X1,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_56]), c_0_21]), c_0_22])])).
% 0.13/0.40  cnf(c_0_60, plain, (r1_lattice3(X1,X3,X2)|~r1_orders_2(X1,X2,esk3_3(X1,X3,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.40  cnf(c_0_61, negated_conjecture, (r1_orders_2(esk5_0,esk8_0,X1)|~m1_subset_1(X1,u1_struct_0(esk5_0))|~r2_hidden(X1,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_21]), c_0_22])])).
% 0.13/0.40  cnf(c_0_62, negated_conjecture, (r2_lattice3(esk5_0,X1,esk8_0)|~r1_lattice3(esk5_0,esk6_0,esk8_0)|~m1_subset_1(esk4_3(esk5_0,X1,esk8_0),u1_struct_0(esk5_0))|~r2_hidden(esk4_3(esk5_0,X1,esk8_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_59]), c_0_21]), c_0_22])])).
% 0.13/0.40  cnf(c_0_63, negated_conjecture, (r1_lattice3(esk5_0,X1,esk8_0)|~m1_subset_1(esk3_3(esk5_0,X1,esk8_0),u1_struct_0(esk5_0))|~r2_hidden(esk3_3(esk5_0,X1,esk8_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_21]), c_0_22])])).
% 0.13/0.40  cnf(c_0_64, plain, (m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.40  cnf(c_0_65, negated_conjecture, (r2_lattice3(esk5_0,X1,esk8_0)|~r1_lattice3(esk5_0,esk6_0,esk8_0)|~r2_hidden(esk4_3(esk5_0,X1,esk8_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_37]), c_0_21]), c_0_22])])).
% 0.13/0.40  cnf(c_0_66, negated_conjecture, (r1_lattice3(esk5_0,X1,esk8_0)|~r2_hidden(esk3_3(esk5_0,X1,esk8_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_21]), c_0_22])])).
% 0.13/0.40  cnf(c_0_67, negated_conjecture, (r2_lattice3(esk5_0,X1,esk8_0)|~r1_lattice3(esk5_0,esk6_0,esk8_0)|~m1_subset_1(esk4_3(esk5_0,X1,esk8_0),esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_45]), c_0_46])).
% 0.13/0.40  cnf(c_0_68, negated_conjecture, (r1_lattice3(esk5_0,X1,esk8_0)|~m1_subset_1(esk3_3(esk5_0,X1,esk8_0),esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_45]), c_0_46])).
% 0.13/0.40  cnf(c_0_69, negated_conjecture, (r2_lattice3(esk5_0,X1,esk8_0)|~r1_lattice3(esk5_0,esk6_0,esk8_0)|~m1_subset_1(esk4_3(esk5_0,X1,esk8_0),esk6_0)), inference(spm,[status(thm)],[c_0_67, c_0_51])).
% 0.13/0.40  cnf(c_0_70, negated_conjecture, (r1_lattice3(esk5_0,X1,esk8_0)|~m1_subset_1(esk3_3(esk5_0,X1,esk8_0),esk6_0)), inference(spm,[status(thm)],[c_0_68, c_0_51])).
% 0.13/0.40  cnf(c_0_71, plain, (r1_lattice3(X1,X2,X3)|m1_subset_1(esk3_3(X1,X2,X3),X2)|~l1_orders_2(X1)|~m1_subset_1(X3,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_52, c_0_32])).
% 0.13/0.40  cnf(c_0_72, negated_conjecture, (~r1_lattice3(esk5_0,esk6_0,esk8_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_54]), c_0_21]), c_0_22])]), c_0_30])).
% 0.13/0.40  cnf(c_0_73, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_21]), c_0_22])]), c_0_72]), ['proof']).
% 0.13/0.40  # SZS output end CNFRefutation
% 0.13/0.40  # Proof object total steps             : 74
% 0.13/0.40  # Proof object clause steps            : 55
% 0.13/0.40  # Proof object formula steps           : 19
% 0.13/0.40  # Proof object conjectures             : 37
% 0.13/0.40  # Proof object clause conjectures      : 34
% 0.13/0.40  # Proof object formula conjectures     : 3
% 0.13/0.40  # Proof object initial clauses used    : 22
% 0.13/0.40  # Proof object initial formulas used   : 9
% 0.13/0.40  # Proof object generating inferences   : 33
% 0.13/0.40  # Proof object simplifying inferences  : 56
% 0.13/0.40  # Training examples: 0 positive, 0 negative
% 0.13/0.40  # Parsed axioms                        : 14
% 0.13/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.40  # Initial clauses                      : 33
% 0.13/0.40  # Removed in clause preprocessing      : 0
% 0.13/0.40  # Initial clauses in saturation        : 33
% 0.13/0.40  # Processed clauses                    : 162
% 0.13/0.40  # ...of these trivial                  : 1
% 0.13/0.40  # ...subsumed                          : 47
% 0.13/0.40  # ...remaining for further processing  : 114
% 0.13/0.40  # Other redundant clauses eliminated   : 5
% 0.13/0.40  # Clauses deleted for lack of memory   : 0
% 0.13/0.40  # Backward-subsumed                    : 7
% 0.13/0.40  # Backward-rewritten                   : 6
% 0.13/0.40  # Generated clauses                    : 223
% 0.13/0.40  # ...of the previous two non-trivial   : 202
% 0.13/0.40  # Contextual simplify-reflections      : 3
% 0.13/0.40  # Paramodulations                      : 219
% 0.13/0.40  # Factorizations                       : 0
% 0.13/0.40  # Equation resolutions                 : 5
% 0.13/0.40  # Propositional unsat checks           : 0
% 0.13/0.40  #    Propositional check models        : 0
% 0.13/0.40  #    Propositional check unsatisfiable : 0
% 0.13/0.40  #    Propositional clauses             : 0
% 0.13/0.40  #    Propositional clauses after purity: 0
% 0.13/0.40  #    Propositional unsat core size     : 0
% 0.13/0.40  #    Propositional preprocessing time  : 0.000
% 0.13/0.40  #    Propositional encoding time       : 0.000
% 0.13/0.40  #    Propositional solver time         : 0.000
% 0.13/0.40  #    Success case prop preproc time    : 0.000
% 0.13/0.40  #    Success case prop encoding time   : 0.000
% 0.13/0.40  #    Success case prop solver time     : 0.000
% 0.13/0.40  # Current number of processed clauses  : 97
% 0.13/0.40  #    Positive orientable unit clauses  : 9
% 0.13/0.40  #    Positive unorientable unit clauses: 0
% 0.13/0.40  #    Negative unit clauses             : 4
% 0.13/0.40  #    Non-unit-clauses                  : 84
% 0.13/0.40  # Current number of unprocessed clauses: 72
% 0.13/0.40  # ...number of literals in the above   : 308
% 0.13/0.40  # Current number of archived formulas  : 0
% 0.13/0.40  # Current number of archived clauses   : 13
% 0.13/0.40  # Clause-clause subsumption calls (NU) : 932
% 0.13/0.40  # Rec. Clause-clause subsumption calls : 647
% 0.13/0.40  # Non-unit clause-clause subsumptions  : 42
% 0.13/0.40  # Unit Clause-clause subsumption calls : 127
% 0.13/0.40  # Rewrite failures with RHS unbound    : 0
% 0.13/0.40  # BW rewrite match attempts            : 7
% 0.13/0.40  # BW rewrite match successes           : 1
% 0.13/0.40  # Condensation attempts                : 0
% 0.13/0.40  # Condensation successes               : 0
% 0.13/0.40  # Termbank termtop insertions          : 5864
% 0.13/0.40  
% 0.13/0.40  # -------------------------------------------------
% 0.13/0.40  # User time                : 0.050 s
% 0.13/0.40  # System time              : 0.009 s
% 0.13/0.40  # Total time               : 0.058 s
% 0.13/0.40  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
