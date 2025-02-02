%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow_0__t53_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:45 EDT 2019

% Result     : Theorem 0.75s
% Output     : CNFRefutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 221 expanded)
%              Number of clauses        :   29 (  86 expanded)
%              Number of leaves         :    8 (  55 expanded)
%              Depth                    :   13
%              Number of atoms          :  192 ( 954 expanded)
%              Number of equality atoms :   11 (  40 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   30 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t53_yellow_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ( ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => r1_yellow_0(X1,X2) )
       => v3_lattice3(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t53_yellow_0.p',t53_yellow_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t53_yellow_0.p',t3_subset)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t53_yellow_0.p',t17_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t53_yellow_0.p',commutativity_k3_xboole_0)).

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
    file('/export/starexec/sandbox/benchmark/yellow_0__t53_yellow_0.p',d9_yellow_0)).

fof(dt_k1_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t53_yellow_0.p',dt_k1_yellow_0)).

fof(t50_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( r1_yellow_0(X1,X2)
           => r1_yellow_0(X1,k3_xboole_0(X2,u1_struct_0(X1))) )
          & ( r1_yellow_0(X1,k3_xboole_0(X2,u1_struct_0(X1)))
           => r1_yellow_0(X1,X2) )
          & ( r2_yellow_0(X1,X2)
           => r2_yellow_0(X1,k3_xboole_0(X2,u1_struct_0(X1))) )
          & ( r2_yellow_0(X1,k3_xboole_0(X2,u1_struct_0(X1)))
           => r2_yellow_0(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t53_yellow_0.p',t50_yellow_0)).

fof(d12_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v3_lattice3(X1)
      <=> ! [X2] :
          ? [X3] :
            ( m1_subset_1(X3,u1_struct_0(X1))
            & r2_lattice3(X1,X2,X3)
            & ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_lattice3(X1,X2,X4)
                 => r1_orders_2(X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t53_yellow_0.p',d12_lattice3)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_orders_2(X1) )
       => ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => r1_yellow_0(X1,X2) )
         => v3_lattice3(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t53_yellow_0])).

fof(c_0_9,plain,(
    ! [X38,X39] :
      ( ( ~ m1_subset_1(X38,k1_zfmisc_1(X39))
        | r1_tarski(X38,X39) )
      & ( ~ r1_tarski(X38,X39)
        | m1_subset_1(X38,k1_zfmisc_1(X39)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_10,plain,(
    ! [X31,X32] : r1_tarski(k3_xboole_0(X31,X32),X31) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_11,negated_conjecture,(
    ! [X6] :
      ( ~ v2_struct_0(esk1_0)
      & l1_orders_2(esk1_0)
      & ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(esk1_0)))
        | r1_yellow_0(esk1_0,X6) )
      & ~ v3_lattice3(esk1_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])).

cnf(c_0_12,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( r1_yellow_0(esk1_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_16,plain,(
    ! [X9,X10] : k3_xboole_0(X9,X10) = k3_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_17,plain,(
    ! [X18,X19,X20,X21] :
      ( ( r2_lattice3(X18,X19,X20)
        | X20 != k1_yellow_0(X18,X19)
        | ~ r1_yellow_0(X18,X19)
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ l1_orders_2(X18) )
      & ( ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ r2_lattice3(X18,X19,X21)
        | r1_orders_2(X18,X20,X21)
        | X20 != k1_yellow_0(X18,X19)
        | ~ r1_yellow_0(X18,X19)
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ l1_orders_2(X18) )
      & ( m1_subset_1(esk5_3(X18,X19,X20),u1_struct_0(X18))
        | ~ r2_lattice3(X18,X19,X20)
        | X20 = k1_yellow_0(X18,X19)
        | ~ r1_yellow_0(X18,X19)
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ l1_orders_2(X18) )
      & ( r2_lattice3(X18,X19,esk5_3(X18,X19,X20))
        | ~ r2_lattice3(X18,X19,X20)
        | X20 = k1_yellow_0(X18,X19)
        | ~ r1_yellow_0(X18,X19)
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ l1_orders_2(X18) )
      & ( ~ r1_orders_2(X18,X20,esk5_3(X18,X19,X20))
        | ~ r2_lattice3(X18,X19,X20)
        | X20 = k1_yellow_0(X18,X19)
        | ~ r1_yellow_0(X18,X19)
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ l1_orders_2(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).

fof(c_0_18,plain,(
    ! [X23,X24] :
      ( ~ l1_orders_2(X23)
      | m1_subset_1(k1_yellow_0(X23,X24),u1_struct_0(X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

fof(c_0_19,plain,(
    ! [X43,X44] :
      ( ( ~ r1_yellow_0(X43,X44)
        | r1_yellow_0(X43,k3_xboole_0(X44,u1_struct_0(X43)))
        | v2_struct_0(X43)
        | ~ l1_orders_2(X43) )
      & ( ~ r1_yellow_0(X43,k3_xboole_0(X44,u1_struct_0(X43)))
        | r1_yellow_0(X43,X44)
        | v2_struct_0(X43)
        | ~ l1_orders_2(X43) )
      & ( ~ r2_yellow_0(X43,X44)
        | r2_yellow_0(X43,k3_xboole_0(X44,u1_struct_0(X43)))
        | v2_struct_0(X43)
        | ~ l1_orders_2(X43) )
      & ( ~ r2_yellow_0(X43,k3_xboole_0(X44,u1_struct_0(X43)))
        | r2_yellow_0(X43,X44)
        | v2_struct_0(X43)
        | ~ l1_orders_2(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t50_yellow_0])])])])])).

cnf(c_0_20,negated_conjecture,
    ( r1_yellow_0(esk1_0,k3_xboole_0(u1_struct_0(esk1_0),X1)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( r2_lattice3(X1,X2,X3)
    | X3 != k1_yellow_0(X1,X2)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( r1_yellow_0(X1,X2)
    | v2_struct_0(X1)
    | ~ r1_yellow_0(X1,k3_xboole_0(X2,u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( r1_yellow_0(esk1_0,k3_xboole_0(X1,u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_28,plain,(
    ! [X11,X12,X14,X16] :
      ( ( m1_subset_1(esk2_2(X11,X12),u1_struct_0(X11))
        | ~ v3_lattice3(X11)
        | ~ l1_orders_2(X11) )
      & ( r2_lattice3(X11,X12,esk2_2(X11,X12))
        | ~ v3_lattice3(X11)
        | ~ l1_orders_2(X11) )
      & ( ~ m1_subset_1(X14,u1_struct_0(X11))
        | ~ r2_lattice3(X11,X12,X14)
        | r1_orders_2(X11,esk2_2(X11,X12),X14)
        | ~ v3_lattice3(X11)
        | ~ l1_orders_2(X11) )
      & ( m1_subset_1(esk4_2(X11,X16),u1_struct_0(X11))
        | ~ m1_subset_1(X16,u1_struct_0(X11))
        | ~ r2_lattice3(X11,esk3_1(X11),X16)
        | v3_lattice3(X11)
        | ~ l1_orders_2(X11) )
      & ( r2_lattice3(X11,esk3_1(X11),esk4_2(X11,X16))
        | ~ m1_subset_1(X16,u1_struct_0(X11))
        | ~ r2_lattice3(X11,esk3_1(X11),X16)
        | v3_lattice3(X11)
        | ~ l1_orders_2(X11) )
      & ( ~ r1_orders_2(X11,X16,esk4_2(X11,X16))
        | ~ m1_subset_1(X16,u1_struct_0(X11))
        | ~ r2_lattice3(X11,esk3_1(X11),X16)
        | v3_lattice3(X11)
        | ~ l1_orders_2(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_lattice3])])])])])).

cnf(c_0_29,plain,
    ( r2_lattice3(X1,X2,k1_yellow_0(X1,X2))
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_22]),c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( r1_yellow_0(esk1_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_31,plain,
    ( m1_subset_1(esk4_2(X1,X2),u1_struct_0(X1))
    | v3_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_lattice3(X1,esk3_1(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( r2_lattice3(esk1_0,X1,k1_yellow_0(esk1_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_26])])).

cnf(c_0_33,negated_conjecture,
    ( ~ v3_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_34,plain,
    ( r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | X4 != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk4_2(esk1_0,k1_yellow_0(esk1_0,esk3_1(esk1_0))),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k1_yellow_0(esk1_0,esk3_1(esk1_0)),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_26])]),c_0_33])).

cnf(c_0_36,plain,
    ( r2_lattice3(X1,esk3_1(X1),esk4_2(X1,X2))
    | v3_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_lattice3(X1,esk3_1(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_34]),c_0_23])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk4_2(esk1_0,k1_yellow_0(esk1_0,esk3_1(esk1_0))),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_23]),c_0_26])])).

cnf(c_0_39,negated_conjecture,
    ( r2_lattice3(esk1_0,esk3_1(esk1_0),esk4_2(esk1_0,k1_yellow_0(esk1_0,esk3_1(esk1_0))))
    | ~ m1_subset_1(k1_yellow_0(esk1_0,esk3_1(esk1_0)),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_32]),c_0_26])]),c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( r1_orders_2(esk1_0,k1_yellow_0(esk1_0,X1),esk4_2(esk1_0,k1_yellow_0(esk1_0,esk3_1(esk1_0))))
    | ~ r2_lattice3(esk1_0,X1,esk4_2(esk1_0,k1_yellow_0(esk1_0,esk3_1(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_30]),c_0_26])])).

cnf(c_0_41,negated_conjecture,
    ( r2_lattice3(esk1_0,esk3_1(esk1_0),esk4_2(esk1_0,k1_yellow_0(esk1_0,esk3_1(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_23]),c_0_26])])).

cnf(c_0_42,plain,
    ( v3_lattice3(X1)
    | ~ r1_orders_2(X1,X2,esk4_2(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_lattice3(X1,esk3_1(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_43,negated_conjecture,
    ( r1_orders_2(esk1_0,k1_yellow_0(esk1_0,esk3_1(esk1_0)),esk4_2(esk1_0,k1_yellow_0(esk1_0,esk3_1(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( ~ m1_subset_1(k1_yellow_0(esk1_0,esk3_1(esk1_0)),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_32]),c_0_26])]),c_0_33])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_23]),c_0_26])]),
    [proof]).
%------------------------------------------------------------------------------
