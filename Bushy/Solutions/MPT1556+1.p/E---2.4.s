%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow_0__t34_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:40 EDT 2019

% Result     : Theorem 6.57s
% Output     : CNFRefutation 6.57s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 160 expanded)
%              Number of clauses        :   44 (  69 expanded)
%              Number of leaves         :   10 (  39 expanded)
%              Depth                    :   14
%              Number of atoms          :  231 ( 686 expanded)
%              Number of equality atoms :    8 (  21 expanded)
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
    file('/export/starexec/sandbox2/benchmark/yellow_0__t34_yellow_0.p',t34_yellow_0)).

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
    file('/export/starexec/sandbox2/benchmark/yellow_0__t34_yellow_0.p',d9_lattice3)).

fof(dt_k1_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t34_yellow_0.p',dt_k1_yellow_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t34_yellow_0.p',t3_subset)).

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
    file('/export/starexec/sandbox2/benchmark/yellow_0__t34_yellow_0.p',d9_yellow_0)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t34_yellow_0.p',t4_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t34_yellow_0.p',t2_subset)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t34_yellow_0.p',t7_boole)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t34_yellow_0.p',t5_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t34_yellow_0.p',existence_m1_subset_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2,X3] :
            ( ( r1_tarski(X2,X3)
              & r1_yellow_0(X1,X2)
              & r1_yellow_0(X1,X3) )
           => r1_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t34_yellow_0])).

fof(c_0_11,plain,(
    ! [X10,X11,X12,X13] :
      ( ( ~ r2_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r2_hidden(X13,X11)
        | r1_orders_2(X10,X13,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ l1_orders_2(X10) )
      & ( m1_subset_1(esk4_3(X10,X11,X12),u1_struct_0(X10))
        | r2_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ l1_orders_2(X10) )
      & ( r2_hidden(esk4_3(X10,X11,X12),X11)
        | r2_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ l1_orders_2(X10) )
      & ( ~ r1_orders_2(X10,esk4_3(X10,X11,X12),X12)
        | r2_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ l1_orders_2(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

fof(c_0_12,plain,(
    ! [X20,X21] :
      ( ~ l1_orders_2(X20)
      | m1_subset_1(k1_yellow_0(X20,X21),u1_struct_0(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

fof(c_0_13,plain,(
    ! [X31,X32] :
      ( ( ~ m1_subset_1(X31,k1_zfmisc_1(X32))
        | r1_tarski(X31,X32) )
      & ( ~ r1_tarski(X31,X32)
        | m1_subset_1(X31,k1_zfmisc_1(X32)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_14,negated_conjecture,
    ( l1_orders_2(esk1_0)
    & r1_tarski(esk2_0,esk3_0)
    & r1_yellow_0(esk1_0,esk2_0)
    & r1_yellow_0(esk1_0,esk3_0)
    & ~ r1_orders_2(esk1_0,k1_yellow_0(esk1_0,esk2_0),k1_yellow_0(esk1_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_15,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X15,X16,X17,X18] :
      ( ( r2_lattice3(X15,X16,X17)
        | X17 != k1_yellow_0(X15,X16)
        | ~ r1_yellow_0(X15,X16)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ l1_orders_2(X15) )
      & ( ~ m1_subset_1(X18,u1_struct_0(X15))
        | ~ r2_lattice3(X15,X16,X18)
        | r1_orders_2(X15,X17,X18)
        | X17 != k1_yellow_0(X15,X16)
        | ~ r1_yellow_0(X15,X16)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ l1_orders_2(X15) )
      & ( m1_subset_1(esk5_3(X15,X16,X17),u1_struct_0(X15))
        | ~ r2_lattice3(X15,X16,X17)
        | X17 = k1_yellow_0(X15,X16)
        | ~ r1_yellow_0(X15,X16)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ l1_orders_2(X15) )
      & ( r2_lattice3(X15,X16,esk5_3(X15,X16,X17))
        | ~ r2_lattice3(X15,X16,X17)
        | X17 = k1_yellow_0(X15,X16)
        | ~ r1_yellow_0(X15,X16)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ l1_orders_2(X15) )
      & ( ~ r1_orders_2(X15,X17,esk5_3(X15,X16,X17))
        | ~ r2_lattice3(X15,X16,X17)
        | X17 = k1_yellow_0(X15,X16)
        | ~ r1_yellow_0(X15,X16)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ l1_orders_2(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).

fof(c_0_18,plain,(
    ! [X33,X34,X35] :
      ( ~ r2_hidden(X33,X34)
      | ~ m1_subset_1(X34,k1_zfmisc_1(X35))
      | m1_subset_1(X33,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_19,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,plain,
    ( r2_lattice3(X1,X2,k1_yellow_0(X1,X3))
    | m1_subset_1(esk4_3(X1,X2,k1_yellow_0(X1,X3)),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,plain,
    ( r2_lattice3(X1,X2,X3)
    | X3 != k1_yellow_0(X1,X2)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_27,plain,
    ( r2_lattice3(X1,X2,k1_yellow_0(X1,X3))
    | r1_orders_2(X1,esk4_3(X1,X2,k1_yellow_0(X1,X3)),X4)
    | ~ r2_lattice3(X1,X5,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(esk4_3(X1,X2,k1_yellow_0(X1,X3)),X5)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( r2_lattice3(X1,X2,k1_yellow_0(X1,X2))
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_23]),c_0_16])).

cnf(c_0_29,negated_conjecture,
    ( r1_yellow_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_30,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_31,plain,(
    ! [X29,X30] :
      ( ~ m1_subset_1(X29,X30)
      | v1_xboole_0(X30)
      | r2_hidden(X29,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(X1,esk3_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,plain,
    ( r2_lattice3(X1,X2,k1_yellow_0(X1,X3))
    | r2_hidden(esk4_3(X1,X2,k1_yellow_0(X1,X3)),X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_16])).

cnf(c_0_34,plain,
    ( r2_lattice3(X1,X2,k1_yellow_0(X1,X3))
    | r1_orders_2(X1,esk4_3(X1,X2,k1_yellow_0(X1,X3)),k1_yellow_0(X1,X4))
    | ~ r2_lattice3(X1,X5,k1_yellow_0(X1,X4))
    | ~ r2_hidden(esk4_3(X1,X2,k1_yellow_0(X1,X3)),X5)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_16])).

cnf(c_0_35,negated_conjecture,
    ( r2_lattice3(esk1_0,esk3_0,k1_yellow_0(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

cnf(c_0_36,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( r2_lattice3(X1,esk2_0,k1_yellow_0(X1,X2))
    | m1_subset_1(esk4_3(X1,esk2_0,k1_yellow_0(X1,X2)),esk3_0)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,plain,
    ( r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | X4 != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_39,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk4_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_40,negated_conjecture,
    ( r2_lattice3(esk1_0,X1,k1_yellow_0(esk1_0,X2))
    | r1_orders_2(esk1_0,esk4_3(esk1_0,X1,k1_yellow_0(esk1_0,X2)),k1_yellow_0(esk1_0,esk3_0))
    | ~ r2_hidden(esk4_3(esk1_0,X1,k1_yellow_0(esk1_0,X2)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_30])])).

cnf(c_0_41,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | r2_lattice3(X1,esk2_0,k1_yellow_0(X1,X2))
    | r2_hidden(esk4_3(X1,esk2_0,k1_yellow_0(X1,X2)),esk3_0)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_42,plain,(
    ! [X40,X41] :
      ( ~ r2_hidden(X40,X41)
      | ~ v1_xboole_0(X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_43,plain,(
    ! [X36,X37,X38] :
      ( ~ r2_hidden(X36,X37)
      | ~ m1_subset_1(X37,k1_zfmisc_1(X38))
      | ~ v1_xboole_0(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_44,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_38]),c_0_16])).

cnf(c_0_45,plain,
    ( r2_lattice3(X1,X2,k1_yellow_0(X1,X3))
    | ~ r1_orders_2(X1,esk4_3(X1,X2,k1_yellow_0(X1,X3)),k1_yellow_0(X1,X3))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_16])).

cnf(c_0_46,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | r2_lattice3(esk1_0,esk2_0,k1_yellow_0(esk1_0,X1))
    | r1_orders_2(esk1_0,esk4_3(esk1_0,esk2_0,k1_yellow_0(esk1_0,X1)),k1_yellow_0(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_30])])).

cnf(c_0_47,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3))
    | ~ r2_lattice3(X1,X2,k1_yellow_0(X1,X3))
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_16])).

cnf(c_0_50,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | r2_lattice3(esk1_0,esk2_0,k1_yellow_0(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_30])])).

cnf(c_0_51,negated_conjecture,
    ( r1_yellow_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_52,negated_conjecture,
    ( ~ r1_orders_2(esk1_0,k1_yellow_0(esk1_0,esk2_0),k1_yellow_0(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_53,plain,(
    ! [X25] : m1_subset_1(esk8_1(X25),X25) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_54,plain,
    ( r2_lattice3(X1,X2,k1_yellow_0(X1,X3))
    | ~ v1_xboole_0(X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_33])).

cnf(c_0_55,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_25])).

cnf(c_0_56,negated_conjecture,
    ( v1_xboole_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_30])]),c_0_52])).

cnf(c_0_57,plain,
    ( m1_subset_1(esk8_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_58,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3))
    | ~ v1_xboole_0(X2)
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( ~ r2_hidden(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_56])])).

cnf(c_0_60,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk8_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( r1_orders_2(esk1_0,k1_yellow_0(esk1_0,esk2_0),k1_yellow_0(esk1_0,X1))
    | ~ v1_xboole_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_51]),c_0_30])])).

cnf(c_0_62,negated_conjecture,
    ( v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_63,negated_conjecture,
    ( r1_orders_2(esk1_0,k1_yellow_0(esk1_0,esk2_0),k1_yellow_0(esk1_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62])])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_63])]),
    [proof]).
%------------------------------------------------------------------------------
