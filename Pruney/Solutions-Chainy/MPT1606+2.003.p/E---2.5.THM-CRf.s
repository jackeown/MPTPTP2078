%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:48 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 121 expanded)
%              Number of clauses        :   28 (  47 expanded)
%              Number of leaves         :   13 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :  241 ( 441 expanded)
%              Number of equality atoms :   28 (  80 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   50 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
             => ( r3_orders_2(k2_yellow_1(X1),X2,X3)
              <=> r1_tarski(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).

fof(t1_yellow_1,axiom,(
    ! [X1] :
      ( u1_struct_0(k2_yellow_1(X1)) = X1
      & u1_orders_2(k2_yellow_1(X1)) = k1_yellow_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

fof(redefinition_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_orders_2(X1,X2,X3)
      <=> r1_orders_2(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(dt_k2_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & l1_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(fc5_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & v3_orders_2(k2_yellow_1(X1))
      & v4_orders_2(k2_yellow_1(X1))
      & v5_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(fc6_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( ~ v2_struct_0(k2_yellow_1(X1))
        & v1_orders_2(k2_yellow_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_yellow_1)).

fof(t14_yellow_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( r2_hidden(k3_tarski(X1),X1)
       => k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).

fof(t31_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( ( X2 = k2_yellow_0(X1,X3)
                  & r2_yellow_0(X1,X3) )
               => ( r1_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X4,X2) ) ) ) )
              & ( ( r1_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X4,X2) ) ) )
               => ( X2 = k2_yellow_0(X1,X3)
                  & r2_yellow_0(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_yellow_0)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(d12_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => k4_yellow_0(X1) = k2_yellow_0(X1,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_yellow_0)).

fof(t6_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r2_lattice3(X1,k1_xboole_0,X2)
            & r1_lattice3(X1,k1_xboole_0,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).

fof(c_0_13,plain,(
    ! [X27,X28,X29] :
      ( ( ~ r3_orders_2(k2_yellow_1(X27),X28,X29)
        | r1_tarski(X28,X29)
        | ~ m1_subset_1(X29,u1_struct_0(k2_yellow_1(X27)))
        | ~ m1_subset_1(X28,u1_struct_0(k2_yellow_1(X27)))
        | v1_xboole_0(X27) )
      & ( ~ r1_tarski(X28,X29)
        | r3_orders_2(k2_yellow_1(X27),X28,X29)
        | ~ m1_subset_1(X29,u1_struct_0(k2_yellow_1(X27)))
        | ~ m1_subset_1(X28,u1_struct_0(k2_yellow_1(X27)))
        | v1_xboole_0(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).

fof(c_0_14,plain,(
    ! [X26] :
      ( u1_struct_0(k2_yellow_1(X26)) = X26
      & u1_orders_2(k2_yellow_1(X26)) = k1_yellow_1(X26) ) ),
    inference(variable_rename,[status(thm)],[t1_yellow_1])).

fof(c_0_15,plain,(
    ! [X11,X12,X13] :
      ( ( ~ r3_orders_2(X11,X12,X13)
        | r1_orders_2(X11,X12,X13)
        | v2_struct_0(X11)
        | ~ v3_orders_2(X11)
        | ~ l1_orders_2(X11)
        | ~ m1_subset_1(X12,u1_struct_0(X11))
        | ~ m1_subset_1(X13,u1_struct_0(X11)) )
      & ( ~ r1_orders_2(X11,X12,X13)
        | r3_orders_2(X11,X12,X13)
        | v2_struct_0(X11)
        | ~ v3_orders_2(X11)
        | ~ l1_orders_2(X11)
        | ~ m1_subset_1(X12,u1_struct_0(X11))
        | ~ m1_subset_1(X13,u1_struct_0(X11)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_16,plain,
    ( r3_orders_2(k2_yellow_1(X3),X1,X2)
    | v1_xboole_0(X3)
    | ~ r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( u1_struct_0(k2_yellow_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X23] :
      ( v1_orders_2(k2_yellow_1(X23))
      & l1_orders_2(k2_yellow_1(X23)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

fof(c_0_19,plain,(
    ! [X24] :
      ( v1_orders_2(k2_yellow_1(X24))
      & v3_orders_2(k2_yellow_1(X24))
      & v4_orders_2(k2_yellow_1(X24))
      & v5_orders_2(k2_yellow_1(X24)) ) ),
    inference(variable_rename,[status(thm)],[fc5_yellow_1])).

fof(c_0_20,plain,(
    ! [X25] :
      ( ( ~ v2_struct_0(k2_yellow_1(X25))
        | v1_xboole_0(X25) )
      & ( v1_orders_2(k2_yellow_1(X25))
        | v1_xboole_0(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_yellow_1])])])])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ( r2_hidden(k3_tarski(X1),X1)
         => k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t14_yellow_1])).

fof(c_0_22,plain,(
    ! [X15,X16,X17,X18,X19] :
      ( ( r1_lattice3(X15,X17,X16)
        | X16 != k2_yellow_0(X15,X17)
        | ~ r2_yellow_0(X15,X17)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) )
      & ( ~ m1_subset_1(X18,u1_struct_0(X15))
        | ~ r1_lattice3(X15,X17,X18)
        | r1_orders_2(X15,X18,X16)
        | X16 != k2_yellow_0(X15,X17)
        | ~ r2_yellow_0(X15,X17)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) )
      & ( X16 = k2_yellow_0(X15,X19)
        | m1_subset_1(esk1_3(X15,X16,X19),u1_struct_0(X15))
        | ~ r1_lattice3(X15,X19,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) )
      & ( r2_yellow_0(X15,X19)
        | m1_subset_1(esk1_3(X15,X16,X19),u1_struct_0(X15))
        | ~ r1_lattice3(X15,X19,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) )
      & ( X16 = k2_yellow_0(X15,X19)
        | r1_lattice3(X15,X19,esk1_3(X15,X16,X19))
        | ~ r1_lattice3(X15,X19,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) )
      & ( r2_yellow_0(X15,X19)
        | r1_lattice3(X15,X19,esk1_3(X15,X16,X19))
        | ~ r1_lattice3(X15,X19,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) )
      & ( X16 = k2_yellow_0(X15,X19)
        | ~ r1_orders_2(X15,esk1_3(X15,X16,X19),X16)
        | ~ r1_lattice3(X15,X19,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) )
      & ( r2_yellow_0(X15,X19)
        | ~ r1_orders_2(X15,esk1_3(X15,X16,X19),X16)
        | ~ r1_lattice3(X15,X19,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v5_orders_2(X15)
        | ~ l1_orders_2(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_yellow_0])])])])])])).

cnf(c_0_23,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( r3_orders_2(k2_yellow_1(X1),X2,X3)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_17])).

cnf(c_0_25,plain,
    ( l1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( v3_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( v1_xboole_0(X1)
    | ~ v2_struct_0(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_28,plain,(
    ! [X7,X8] :
      ( ~ r2_hidden(X7,X8)
      | m1_subset_1(X7,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

fof(c_0_29,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    & r2_hidden(k3_tarski(esk2_0),esk2_0)
    & k4_yellow_0(k2_yellow_1(esk2_0)) != k3_tarski(esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).

cnf(c_0_30,plain,
    ( X1 = k2_yellow_0(X2,X3)
    | ~ r1_orders_2(X2,esk1_3(X2,X1,X3),X1)
    | ~ r1_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( r1_orders_2(k2_yellow_1(X1),X2,X3)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26]),c_0_17]),c_0_17])]),c_0_27])).

cnf(c_0_32,plain,
    ( v5_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(k3_tarski(esk2_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( X1 = k2_yellow_0(k2_yellow_1(X2),X3)
    | v1_xboole_0(X2)
    | ~ r1_lattice3(k2_yellow_1(X2),X3,X1)
    | ~ m1_subset_1(esk1_3(k2_yellow_1(X2),X1,X3),X2)
    | ~ m1_subset_1(X1,X2)
    | ~ r1_tarski(esk1_3(k2_yellow_1(X2),X1,X3),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_25]),c_0_17])])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(k3_tarski(esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_38,plain,(
    ! [X5,X6] :
      ( ~ r2_hidden(X5,X6)
      | r1_tarski(X5,k3_tarski(X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

cnf(c_0_39,negated_conjecture,
    ( k2_yellow_0(k2_yellow_1(esk2_0),X1) = k3_tarski(esk2_0)
    | ~ r1_lattice3(k2_yellow_1(esk2_0),X1,k3_tarski(esk2_0))
    | ~ m1_subset_1(esk1_3(k2_yellow_1(esk2_0),k3_tarski(esk2_0),X1),esk2_0)
    | ~ r1_tarski(esk1_3(k2_yellow_1(esk2_0),k3_tarski(esk2_0),X1),k3_tarski(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_41,plain,(
    ! [X9,X10] :
      ( ~ m1_subset_1(X9,X10)
      | v1_xboole_0(X10)
      | r2_hidden(X9,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_42,negated_conjecture,
    ( k2_yellow_0(k2_yellow_1(esk2_0),X1) = k3_tarski(esk2_0)
    | ~ r1_lattice3(k2_yellow_1(esk2_0),X1,k3_tarski(esk2_0))
    | ~ r2_hidden(esk1_3(k2_yellow_1(esk2_0),k3_tarski(esk2_0),X1),esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_33])).

cnf(c_0_43,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_44,plain,
    ( X1 = k2_yellow_0(X2,X3)
    | m1_subset_1(esk1_3(X2,X1,X3),u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_45,plain,(
    ! [X14] :
      ( ~ l1_orders_2(X14)
      | k4_yellow_0(X14) = k2_yellow_0(X14,k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_yellow_0])])).

cnf(c_0_46,negated_conjecture,
    ( k2_yellow_0(k2_yellow_1(esk2_0),X1) = k3_tarski(esk2_0)
    | ~ r1_lattice3(k2_yellow_1(esk2_0),X1,k3_tarski(esk2_0))
    | ~ m1_subset_1(esk1_3(k2_yellow_1(esk2_0),k3_tarski(esk2_0),X1),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_37])).

cnf(c_0_47,plain,
    ( X1 = k2_yellow_0(k2_yellow_1(X2),X3)
    | m1_subset_1(esk1_3(k2_yellow_1(X2),X1,X3),X2)
    | ~ r1_lattice3(k2_yellow_1(X2),X3,X1)
    | ~ m1_subset_1(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_17]),c_0_32]),c_0_25])])).

fof(c_0_48,plain,(
    ! [X21,X22] :
      ( ( r2_lattice3(X21,k1_xboole_0,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ l1_orders_2(X21) )
      & ( r1_lattice3(X21,k1_xboole_0,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ l1_orders_2(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_yellow_0])])])])).

cnf(c_0_49,negated_conjecture,
    ( k4_yellow_0(k2_yellow_1(esk2_0)) != k3_tarski(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_50,plain,
    ( k4_yellow_0(X1) = k2_yellow_0(X1,k1_xboole_0)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( k2_yellow_0(k2_yellow_1(esk2_0),X1) = k3_tarski(esk2_0)
    | ~ r1_lattice3(k2_yellow_1(esk2_0),X1,k3_tarski(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_36])])).

cnf(c_0_52,plain,
    ( r1_lattice3(X1,k1_xboole_0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( k2_yellow_0(k2_yellow_1(esk2_0),k1_xboole_0) != k3_tarski(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_25])])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_25]),c_0_17]),c_0_36])]),c_0_53]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:20:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05BN
% 0.13/0.38  # and selection function SelectUnlessUniqMaxSmallestOrientable.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t3_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>(r3_orders_2(k2_yellow_1(X1),X2,X3)<=>r1_tarski(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_yellow_1)).
% 0.13/0.38  fof(t1_yellow_1, axiom, ![X1]:(u1_struct_0(k2_yellow_1(X1))=X1&u1_orders_2(k2_yellow_1(X1))=k1_yellow_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 0.13/0.38  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 0.13/0.38  fof(dt_k2_yellow_1, axiom, ![X1]:(v1_orders_2(k2_yellow_1(X1))&l1_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 0.13/0.38  fof(fc5_yellow_1, axiom, ![X1]:(((v1_orders_2(k2_yellow_1(X1))&v3_orders_2(k2_yellow_1(X1)))&v4_orders_2(k2_yellow_1(X1)))&v5_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow_1)).
% 0.13/0.38  fof(fc6_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>(~(v2_struct_0(k2_yellow_1(X1)))&v1_orders_2(k2_yellow_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_yellow_1)).
% 0.13/0.38  fof(t14_yellow_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k3_tarski(X1),X1)=>k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow_1)).
% 0.13/0.38  fof(t31_yellow_0, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(((X2=k2_yellow_0(X1,X3)&r2_yellow_0(X1,X3))=>(r1_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattice3(X1,X3,X4)=>r1_orders_2(X1,X4,X2)))))&((r1_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattice3(X1,X3,X4)=>r1_orders_2(X1,X4,X2))))=>(X2=k2_yellow_0(X1,X3)&r2_yellow_0(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_yellow_0)).
% 0.13/0.38  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.13/0.38  fof(l49_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 0.13/0.38  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.13/0.38  fof(d12_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>k4_yellow_0(X1)=k2_yellow_0(X1,k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_yellow_0)).
% 0.13/0.38  fof(t6_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(r2_lattice3(X1,k1_xboole_0,X2)&r1_lattice3(X1,k1_xboole_0,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_yellow_0)).
% 0.13/0.38  fof(c_0_13, plain, ![X27, X28, X29]:((~r3_orders_2(k2_yellow_1(X27),X28,X29)|r1_tarski(X28,X29)|~m1_subset_1(X29,u1_struct_0(k2_yellow_1(X27)))|~m1_subset_1(X28,u1_struct_0(k2_yellow_1(X27)))|v1_xboole_0(X27))&(~r1_tarski(X28,X29)|r3_orders_2(k2_yellow_1(X27),X28,X29)|~m1_subset_1(X29,u1_struct_0(k2_yellow_1(X27)))|~m1_subset_1(X28,u1_struct_0(k2_yellow_1(X27)))|v1_xboole_0(X27))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).
% 0.13/0.38  fof(c_0_14, plain, ![X26]:(u1_struct_0(k2_yellow_1(X26))=X26&u1_orders_2(k2_yellow_1(X26))=k1_yellow_1(X26)), inference(variable_rename,[status(thm)],[t1_yellow_1])).
% 0.13/0.38  fof(c_0_15, plain, ![X11, X12, X13]:((~r3_orders_2(X11,X12,X13)|r1_orders_2(X11,X12,X13)|(v2_struct_0(X11)|~v3_orders_2(X11)|~l1_orders_2(X11)|~m1_subset_1(X12,u1_struct_0(X11))|~m1_subset_1(X13,u1_struct_0(X11))))&(~r1_orders_2(X11,X12,X13)|r3_orders_2(X11,X12,X13)|(v2_struct_0(X11)|~v3_orders_2(X11)|~l1_orders_2(X11)|~m1_subset_1(X12,u1_struct_0(X11))|~m1_subset_1(X13,u1_struct_0(X11))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.13/0.38  cnf(c_0_16, plain, (r3_orders_2(k2_yellow_1(X3),X1,X2)|v1_xboole_0(X3)|~r1_tarski(X1,X2)|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X3)))|~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_17, plain, (u1_struct_0(k2_yellow_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  fof(c_0_18, plain, ![X23]:(v1_orders_2(k2_yellow_1(X23))&l1_orders_2(k2_yellow_1(X23))), inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).
% 0.13/0.38  fof(c_0_19, plain, ![X24]:(((v1_orders_2(k2_yellow_1(X24))&v3_orders_2(k2_yellow_1(X24)))&v4_orders_2(k2_yellow_1(X24)))&v5_orders_2(k2_yellow_1(X24))), inference(variable_rename,[status(thm)],[fc5_yellow_1])).
% 0.13/0.38  fof(c_0_20, plain, ![X25]:((~v2_struct_0(k2_yellow_1(X25))|v1_xboole_0(X25))&(v1_orders_2(k2_yellow_1(X25))|v1_xboole_0(X25))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_yellow_1])])])])).
% 0.13/0.38  fof(c_0_21, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k3_tarski(X1),X1)=>k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1)))), inference(assume_negation,[status(cth)],[t14_yellow_1])).
% 0.13/0.38  fof(c_0_22, plain, ![X15, X16, X17, X18, X19]:(((r1_lattice3(X15,X17,X16)|(X16!=k2_yellow_0(X15,X17)|~r2_yellow_0(X15,X17))|~m1_subset_1(X16,u1_struct_0(X15))|(~v5_orders_2(X15)|~l1_orders_2(X15)))&(~m1_subset_1(X18,u1_struct_0(X15))|(~r1_lattice3(X15,X17,X18)|r1_orders_2(X15,X18,X16))|(X16!=k2_yellow_0(X15,X17)|~r2_yellow_0(X15,X17))|~m1_subset_1(X16,u1_struct_0(X15))|(~v5_orders_2(X15)|~l1_orders_2(X15))))&(((X16=k2_yellow_0(X15,X19)|(m1_subset_1(esk1_3(X15,X16,X19),u1_struct_0(X15))|~r1_lattice3(X15,X19,X16))|~m1_subset_1(X16,u1_struct_0(X15))|(~v5_orders_2(X15)|~l1_orders_2(X15)))&(r2_yellow_0(X15,X19)|(m1_subset_1(esk1_3(X15,X16,X19),u1_struct_0(X15))|~r1_lattice3(X15,X19,X16))|~m1_subset_1(X16,u1_struct_0(X15))|(~v5_orders_2(X15)|~l1_orders_2(X15))))&(((X16=k2_yellow_0(X15,X19)|(r1_lattice3(X15,X19,esk1_3(X15,X16,X19))|~r1_lattice3(X15,X19,X16))|~m1_subset_1(X16,u1_struct_0(X15))|(~v5_orders_2(X15)|~l1_orders_2(X15)))&(r2_yellow_0(X15,X19)|(r1_lattice3(X15,X19,esk1_3(X15,X16,X19))|~r1_lattice3(X15,X19,X16))|~m1_subset_1(X16,u1_struct_0(X15))|(~v5_orders_2(X15)|~l1_orders_2(X15))))&((X16=k2_yellow_0(X15,X19)|(~r1_orders_2(X15,esk1_3(X15,X16,X19),X16)|~r1_lattice3(X15,X19,X16))|~m1_subset_1(X16,u1_struct_0(X15))|(~v5_orders_2(X15)|~l1_orders_2(X15)))&(r2_yellow_0(X15,X19)|(~r1_orders_2(X15,esk1_3(X15,X16,X19),X16)|~r1_lattice3(X15,X19,X16))|~m1_subset_1(X16,u1_struct_0(X15))|(~v5_orders_2(X15)|~l1_orders_2(X15))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_yellow_0])])])])])])).
% 0.13/0.38  cnf(c_0_23, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r3_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_24, plain, (r3_orders_2(k2_yellow_1(X1),X2,X3)|v1_xboole_0(X1)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)|~r1_tarski(X2,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_17])).
% 0.13/0.38  cnf(c_0_25, plain, (l1_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_26, plain, (v3_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_27, plain, (v1_xboole_0(X1)|~v2_struct_0(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  fof(c_0_28, plain, ![X7, X8]:(~r2_hidden(X7,X8)|m1_subset_1(X7,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.13/0.38  fof(c_0_29, negated_conjecture, (~v1_xboole_0(esk2_0)&(r2_hidden(k3_tarski(esk2_0),esk2_0)&k4_yellow_0(k2_yellow_1(esk2_0))!=k3_tarski(esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).
% 0.13/0.38  cnf(c_0_30, plain, (X1=k2_yellow_0(X2,X3)|~r1_orders_2(X2,esk1_3(X2,X1,X3),X1)|~r1_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_31, plain, (r1_orders_2(k2_yellow_1(X1),X2,X3)|v1_xboole_0(X1)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)|~r1_tarski(X2,X3)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26]), c_0_17]), c_0_17])]), c_0_27])).
% 0.13/0.38  cnf(c_0_32, plain, (v5_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_33, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, (r2_hidden(k3_tarski(esk2_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.38  cnf(c_0_35, plain, (X1=k2_yellow_0(k2_yellow_1(X2),X3)|v1_xboole_0(X2)|~r1_lattice3(k2_yellow_1(X2),X3,X1)|~m1_subset_1(esk1_3(k2_yellow_1(X2),X1,X3),X2)|~m1_subset_1(X1,X2)|~r1_tarski(esk1_3(k2_yellow_1(X2),X1,X3),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_25]), c_0_17])])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (m1_subset_1(k3_tarski(esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.38  fof(c_0_38, plain, ![X5, X6]:(~r2_hidden(X5,X6)|r1_tarski(X5,k3_tarski(X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, (k2_yellow_0(k2_yellow_1(esk2_0),X1)=k3_tarski(esk2_0)|~r1_lattice3(k2_yellow_1(esk2_0),X1,k3_tarski(esk2_0))|~m1_subset_1(esk1_3(k2_yellow_1(esk2_0),k3_tarski(esk2_0),X1),esk2_0)|~r1_tarski(esk1_3(k2_yellow_1(esk2_0),k3_tarski(esk2_0),X1),k3_tarski(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])).
% 0.13/0.38  cnf(c_0_40, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.38  fof(c_0_41, plain, ![X9, X10]:(~m1_subset_1(X9,X10)|(v1_xboole_0(X10)|r2_hidden(X9,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (k2_yellow_0(k2_yellow_1(esk2_0),X1)=k3_tarski(esk2_0)|~r1_lattice3(k2_yellow_1(esk2_0),X1,k3_tarski(esk2_0))|~r2_hidden(esk1_3(k2_yellow_1(esk2_0),k3_tarski(esk2_0),X1),esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_33])).
% 0.13/0.38  cnf(c_0_43, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.13/0.38  cnf(c_0_44, plain, (X1=k2_yellow_0(X2,X3)|m1_subset_1(esk1_3(X2,X1,X3),u1_struct_0(X2))|~r1_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  fof(c_0_45, plain, ![X14]:(~l1_orders_2(X14)|k4_yellow_0(X14)=k2_yellow_0(X14,k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_yellow_0])])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (k2_yellow_0(k2_yellow_1(esk2_0),X1)=k3_tarski(esk2_0)|~r1_lattice3(k2_yellow_1(esk2_0),X1,k3_tarski(esk2_0))|~m1_subset_1(esk1_3(k2_yellow_1(esk2_0),k3_tarski(esk2_0),X1),esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_37])).
% 0.13/0.38  cnf(c_0_47, plain, (X1=k2_yellow_0(k2_yellow_1(X2),X3)|m1_subset_1(esk1_3(k2_yellow_1(X2),X1,X3),X2)|~r1_lattice3(k2_yellow_1(X2),X3,X1)|~m1_subset_1(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_17]), c_0_32]), c_0_25])])).
% 0.13/0.38  fof(c_0_48, plain, ![X21, X22]:((r2_lattice3(X21,k1_xboole_0,X22)|~m1_subset_1(X22,u1_struct_0(X21))|~l1_orders_2(X21))&(r1_lattice3(X21,k1_xboole_0,X22)|~m1_subset_1(X22,u1_struct_0(X21))|~l1_orders_2(X21))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_yellow_0])])])])).
% 0.13/0.38  cnf(c_0_49, negated_conjecture, (k4_yellow_0(k2_yellow_1(esk2_0))!=k3_tarski(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.38  cnf(c_0_50, plain, (k4_yellow_0(X1)=k2_yellow_0(X1,k1_xboole_0)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (k2_yellow_0(k2_yellow_1(esk2_0),X1)=k3_tarski(esk2_0)|~r1_lattice3(k2_yellow_1(esk2_0),X1,k3_tarski(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_36])])).
% 0.13/0.38  cnf(c_0_52, plain, (r1_lattice3(X1,k1_xboole_0,X2)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (k2_yellow_0(k2_yellow_1(esk2_0),k1_xboole_0)!=k3_tarski(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_25])])).
% 0.13/0.38  cnf(c_0_54, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_25]), c_0_17]), c_0_36])]), c_0_53]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 55
% 0.13/0.38  # Proof object clause steps            : 28
% 0.13/0.38  # Proof object formula steps           : 27
% 0.13/0.38  # Proof object conjectures             : 13
% 0.13/0.38  # Proof object clause conjectures      : 10
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 17
% 0.13/0.38  # Proof object initial formulas used   : 13
% 0.13/0.38  # Proof object generating inferences   : 10
% 0.13/0.38  # Proof object simplifying inferences  : 27
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 13
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 31
% 0.13/0.38  # Removed in clause preprocessing      : 1
% 0.13/0.38  # Initial clauses in saturation        : 30
% 0.13/0.38  # Processed clauses                    : 77
% 0.13/0.38  # ...of these trivial                  : 2
% 0.13/0.38  # ...subsumed                          : 0
% 0.13/0.38  # ...remaining for further processing  : 75
% 0.13/0.38  # Other redundant clauses eliminated   : 2
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 6
% 0.13/0.38  # Backward-rewritten                   : 0
% 0.13/0.38  # Generated clauses                    : 36
% 0.13/0.38  # ...of the previous two non-trivial   : 31
% 0.13/0.38  # Contextual simplify-reflections      : 4
% 0.13/0.38  # Paramodulations                      : 34
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 2
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 39
% 0.13/0.38  #    Positive orientable unit clauses  : 9
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 3
% 0.13/0.38  #    Non-unit-clauses                  : 27
% 0.13/0.38  # Current number of unprocessed clauses: 12
% 0.13/0.38  # ...number of literals in the above   : 97
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 35
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 452
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 44
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 10
% 0.13/0.38  # Unit Clause-clause subsumption calls : 6
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 0
% 0.13/0.38  # BW rewrite match successes           : 0
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 3776
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.033 s
% 0.13/0.38  # System time              : 0.004 s
% 0.13/0.38  # Total time               : 0.037 s
% 0.13/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
