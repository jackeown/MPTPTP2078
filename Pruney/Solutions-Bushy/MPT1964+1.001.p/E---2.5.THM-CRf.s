%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1964+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:04 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   59 (1198 expanded)
%              Number of clauses        :   42 ( 457 expanded)
%              Number of leaves         :    8 ( 327 expanded)
%              Depth                    :   13
%              Number of atoms          :  274 (7418 expanded)
%              Number of equality atoms :    9 (  49 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   46 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t13_waybel_7,conjecture,(
    ! [X1,X2] :
      ( ( v13_waybel_0(X2,k3_yellow_1(X1))
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) )
     => ( v2_waybel_0(X2,k3_yellow_1(X1))
      <=> ! [X3,X4] :
            ( ( r2_hidden(X3,X2)
              & r2_hidden(X4,X2) )
           => r2_hidden(k3_xboole_0(X3,X4),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_waybel_7)).

fof(cc8_waybel_1,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( ( ~ v2_struct_0(X1)
          & v11_waybel_1(X1) )
       => ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & v1_lattice3(X1)
          & v2_lattice3(X1)
          & v3_yellow_0(X1)
          & v2_waybel_1(X1)
          & v10_waybel_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc8_waybel_1)).

fof(fc1_waybel_7,axiom,(
    ! [X1] :
      ( v1_orders_2(k3_yellow_1(X1))
      & v11_waybel_1(k3_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_waybel_7)).

fof(dt_k3_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k3_yellow_1(X1))
      & l1_orders_2(k3_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_1)).

fof(fc7_yellow_1,axiom,(
    ! [X1] :
      ( ~ v2_struct_0(k3_yellow_1(X1))
      & v1_orders_2(k3_yellow_1(X1))
      & v3_orders_2(k3_yellow_1(X1))
      & v4_orders_2(k3_yellow_1(X1))
      & v5_orders_2(k3_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_yellow_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t41_waybel_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( v13_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ( v2_waybel_0(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( ( r2_hidden(X3,X2)
                        & r2_hidden(X4,X2) )
                     => r2_hidden(k12_lattice3(X1,X3,X4),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_waybel_0)).

fof(t17_yellow_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,u1_struct_0(k3_yellow_1(X1)))
         => ( k13_lattice3(k3_yellow_1(X1),X2,X3) = k2_xboole_0(X2,X3)
            & k12_lattice3(k3_yellow_1(X1),X2,X3) = k3_xboole_0(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v13_waybel_0(X2,k3_yellow_1(X1))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) )
       => ( v2_waybel_0(X2,k3_yellow_1(X1))
        <=> ! [X3,X4] :
              ( ( r2_hidden(X3,X2)
                & r2_hidden(X4,X2) )
             => r2_hidden(k3_xboole_0(X3,X4),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t13_waybel_7])).

fof(c_0_9,plain,(
    ! [X5] :
      ( ( ~ v2_struct_0(X5)
        | v2_struct_0(X5)
        | ~ v11_waybel_1(X5)
        | ~ l1_orders_2(X5) )
      & ( v3_orders_2(X5)
        | v2_struct_0(X5)
        | ~ v11_waybel_1(X5)
        | ~ l1_orders_2(X5) )
      & ( v4_orders_2(X5)
        | v2_struct_0(X5)
        | ~ v11_waybel_1(X5)
        | ~ l1_orders_2(X5) )
      & ( v5_orders_2(X5)
        | v2_struct_0(X5)
        | ~ v11_waybel_1(X5)
        | ~ l1_orders_2(X5) )
      & ( v1_lattice3(X5)
        | v2_struct_0(X5)
        | ~ v11_waybel_1(X5)
        | ~ l1_orders_2(X5) )
      & ( v2_lattice3(X5)
        | v2_struct_0(X5)
        | ~ v11_waybel_1(X5)
        | ~ l1_orders_2(X5) )
      & ( v3_yellow_0(X5)
        | v2_struct_0(X5)
        | ~ v11_waybel_1(X5)
        | ~ l1_orders_2(X5) )
      & ( v2_waybel_1(X5)
        | v2_struct_0(X5)
        | ~ v11_waybel_1(X5)
        | ~ l1_orders_2(X5) )
      & ( v10_waybel_1(X5)
        | v2_struct_0(X5)
        | ~ v11_waybel_1(X5)
        | ~ l1_orders_2(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc8_waybel_1])])])])).

fof(c_0_10,plain,(
    ! [X7] :
      ( v1_orders_2(k3_yellow_1(X7))
      & v11_waybel_1(k3_yellow_1(X7)) ) ),
    inference(variable_rename,[status(thm)],[fc1_waybel_7])).

fof(c_0_11,plain,(
    ! [X6] :
      ( v1_orders_2(k3_yellow_1(X6))
      & l1_orders_2(k3_yellow_1(X6)) ) ),
    inference(variable_rename,[status(thm)],[dt_k3_yellow_1])).

fof(c_0_12,plain,(
    ! [X8] :
      ( ~ v2_struct_0(k3_yellow_1(X8))
      & v1_orders_2(k3_yellow_1(X8))
      & v3_orders_2(k3_yellow_1(X8))
      & v4_orders_2(k3_yellow_1(X8))
      & v5_orders_2(k3_yellow_1(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc7_yellow_1])])).

fof(c_0_13,plain,(
    ! [X18,X19,X20] :
      ( ~ r2_hidden(X18,X19)
      | ~ m1_subset_1(X19,k1_zfmisc_1(X20))
      | m1_subset_1(X18,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_14,negated_conjecture,(
    ! [X25,X26] :
      ( v13_waybel_0(esk4_0,k3_yellow_1(esk3_0))
      & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(esk3_0))))
      & ( r2_hidden(esk5_0,esk4_0)
        | ~ v2_waybel_0(esk4_0,k3_yellow_1(esk3_0)) )
      & ( r2_hidden(esk6_0,esk4_0)
        | ~ v2_waybel_0(esk4_0,k3_yellow_1(esk3_0)) )
      & ( ~ r2_hidden(k3_xboole_0(esk5_0,esk6_0),esk4_0)
        | ~ v2_waybel_0(esk4_0,k3_yellow_1(esk3_0)) )
      & ( v2_waybel_0(esk4_0,k3_yellow_1(esk3_0))
        | ~ r2_hidden(X25,esk4_0)
        | ~ r2_hidden(X26,esk4_0)
        | r2_hidden(k3_xboole_0(X25,X26),esk4_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])])).

fof(c_0_15,plain,(
    ! [X12,X13,X14,X15] :
      ( ( ~ v2_waybel_0(X13,X12)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ m1_subset_1(X15,u1_struct_0(X12))
        | ~ r2_hidden(X14,X13)
        | ~ r2_hidden(X15,X13)
        | r2_hidden(k12_lattice3(X12,X14,X15),X13)
        | ~ v13_waybel_0(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ v5_orders_2(X12)
        | ~ v2_lattice3(X12)
        | ~ l1_orders_2(X12) )
      & ( m1_subset_1(esk1_2(X12,X13),u1_struct_0(X12))
        | v2_waybel_0(X13,X12)
        | ~ v13_waybel_0(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ v5_orders_2(X12)
        | ~ v2_lattice3(X12)
        | ~ l1_orders_2(X12) )
      & ( m1_subset_1(esk2_2(X12,X13),u1_struct_0(X12))
        | v2_waybel_0(X13,X12)
        | ~ v13_waybel_0(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ v5_orders_2(X12)
        | ~ v2_lattice3(X12)
        | ~ l1_orders_2(X12) )
      & ( r2_hidden(esk1_2(X12,X13),X13)
        | v2_waybel_0(X13,X12)
        | ~ v13_waybel_0(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ v5_orders_2(X12)
        | ~ v2_lattice3(X12)
        | ~ l1_orders_2(X12) )
      & ( r2_hidden(esk2_2(X12,X13),X13)
        | v2_waybel_0(X13,X12)
        | ~ v13_waybel_0(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ v5_orders_2(X12)
        | ~ v2_lattice3(X12)
        | ~ l1_orders_2(X12) )
      & ( ~ r2_hidden(k12_lattice3(X12,esk1_2(X12,X13),esk2_2(X12,X13)),X13)
        | v2_waybel_0(X13,X12)
        | ~ v13_waybel_0(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ v5_orders_2(X12)
        | ~ v2_lattice3(X12)
        | ~ l1_orders_2(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_waybel_0])])])])])).

cnf(c_0_16,plain,
    ( v2_lattice3(X1)
    | v2_struct_0(X1)
    | ~ v11_waybel_1(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( v11_waybel_1(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( l1_orders_2(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( ~ v2_struct_0(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | v2_waybel_0(X2,X1)
    | ~ v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( v13_waybel_0(esk4_0,k3_yellow_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( v2_lattice3(k3_yellow_1(X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_25,plain,
    ( v5_orders_2(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_26,plain,(
    ! [X9,X10,X11] :
      ( ( k13_lattice3(k3_yellow_1(X9),X10,X11) = k2_xboole_0(X10,X11)
        | ~ m1_subset_1(X11,u1_struct_0(k3_yellow_1(X9)))
        | ~ m1_subset_1(X10,u1_struct_0(k3_yellow_1(X9))) )
      & ( k12_lattice3(k3_yellow_1(X9),X10,X11) = k3_xboole_0(X10,X11)
        | ~ m1_subset_1(X11,u1_struct_0(k3_yellow_1(X9)))
        | ~ m1_subset_1(X10,u1_struct_0(k3_yellow_1(X9))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_yellow_1])])])])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(esk3_0)))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk2_2(k3_yellow_1(esk3_0),esk4_0),esk4_0)
    | v2_waybel_0(esk4_0,k3_yellow_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_21]),c_0_23]),c_0_24]),c_0_25]),c_0_18])])).

cnf(c_0_29,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | v2_waybel_0(X2,X1)
    | ~ v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_30,negated_conjecture,
    ( v2_waybel_0(esk4_0,k3_yellow_1(esk3_0))
    | r2_hidden(k3_xboole_0(X1,X2),esk4_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X2,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_31,plain,
    ( k12_lattice3(k3_yellow_1(X1),X2,X3) = k3_xboole_0(X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(k3_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( v2_waybel_0(esk4_0,k3_yellow_1(esk3_0))
    | m1_subset_1(esk2_2(k3_yellow_1(esk3_0),esk4_0),u1_struct_0(k3_yellow_1(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk1_2(k3_yellow_1(esk3_0),esk4_0),esk4_0)
    | v2_waybel_0(esk4_0,k3_yellow_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_21]),c_0_23]),c_0_24]),c_0_25]),c_0_18])])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(k3_xboole_0(X1,esk2_2(k3_yellow_1(esk3_0),esk4_0)),esk4_0)
    | v2_waybel_0(esk4_0,k3_yellow_1(esk3_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( k3_xboole_0(X1,esk2_2(k3_yellow_1(esk3_0),esk4_0)) = k12_lattice3(k3_yellow_1(esk3_0),X1,esk2_2(k3_yellow_1(esk3_0),esk4_0))
    | v2_waybel_0(esk4_0,k3_yellow_1(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( v2_waybel_0(esk4_0,k3_yellow_1(esk3_0))
    | m1_subset_1(esk1_2(k3_yellow_1(esk3_0),esk4_0),u1_struct_0(k3_yellow_1(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(k3_xboole_0(esk1_2(k3_yellow_1(esk3_0),esk4_0),esk2_2(k3_yellow_1(esk3_0),esk4_0)),esk4_0)
    | v2_waybel_0(esk4_0,k3_yellow_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( k3_xboole_0(esk1_2(k3_yellow_1(esk3_0),esk4_0),esk2_2(k3_yellow_1(esk3_0),esk4_0)) = k12_lattice3(k3_yellow_1(esk3_0),esk1_2(k3_yellow_1(esk3_0),esk4_0),esk2_2(k3_yellow_1(esk3_0),esk4_0))
    | v2_waybel_0(esk4_0,k3_yellow_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk6_0,esk4_0)
    | ~ v2_waybel_0(esk4_0,k3_yellow_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_40,plain,
    ( v2_waybel_0(X2,X1)
    | ~ r2_hidden(k12_lattice3(X1,esk1_2(X1,X2),esk2_2(X1,X2)),X2)
    | ~ v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(k12_lattice3(k3_yellow_1(esk3_0),esk1_2(k3_yellow_1(esk3_0),esk4_0),esk2_2(k3_yellow_1(esk3_0),esk4_0)),esk4_0)
    | v2_waybel_0(esk4_0,k3_yellow_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,plain,
    ( r2_hidden(k12_lattice3(X2,X3,X4),X1)
    | ~ v2_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(X3,X1)
    | ~ r2_hidden(X4,X1)
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v5_orders_2(X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(k3_yellow_1(esk3_0)))
    | ~ v2_waybel_0(esk4_0,k3_yellow_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( v2_waybel_0(esk4_0,k3_yellow_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_23]),c_0_21]),c_0_24]),c_0_25]),c_0_18])])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0)
    | ~ v2_waybel_0(esk4_0,k3_yellow_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_46,plain,
    ( r2_hidden(k12_lattice3(X1,X2,X3),X4)
    | ~ r2_hidden(X3,X4)
    | ~ r2_hidden(X2,X4)
    | ~ v2_waybel_0(X4,X1)
    | ~ v13_waybel_0(X4,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_42,c_0_20]),c_0_20])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(k3_yellow_1(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44])])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(k3_yellow_1(esk3_0)))
    | ~ v2_waybel_0(esk4_0,k3_yellow_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(k12_lattice3(k3_yellow_1(esk3_0),X1,X2),esk4_0)
    | ~ r2_hidden(X2,esk4_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ v2_waybel_0(esk4_0,k3_yellow_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_21]),c_0_23]),c_0_24]),c_0_25]),c_0_18])])).

cnf(c_0_50,negated_conjecture,
    ( k12_lattice3(k3_yellow_1(esk3_0),X1,esk6_0) = k3_xboole_0(X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(k3_yellow_1(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_44])])).

cnf(c_0_52,negated_conjecture,
    ( ~ r2_hidden(k3_xboole_0(esk5_0,esk6_0),esk4_0)
    | ~ v2_waybel_0(esk4_0,k3_yellow_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(k12_lattice3(k3_yellow_1(esk3_0),X1,X2),esk4_0)
    | ~ r2_hidden(X2,esk4_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_44])])).

cnf(c_0_54,negated_conjecture,
    ( k12_lattice3(k3_yellow_1(esk3_0),esk5_0,esk6_0) = k3_xboole_0(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk6_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_44])])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_44])])).

cnf(c_0_57,negated_conjecture,
    ( ~ r2_hidden(k3_xboole_0(esk5_0,esk6_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_44])])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),c_0_56])]),c_0_57]),
    [proof]).

%------------------------------------------------------------------------------
