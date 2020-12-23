%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:55 EST 2020

% Result     : Theorem 4.93s
% Output     : CNFRefutation 4.93s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 248 expanded)
%              Number of clauses        :   57 ( 111 expanded)
%              Number of leaves         :   12 (  62 expanded)
%              Depth                    :   15
%              Number of atoms          :  242 ( 882 expanded)
%              Number of equality atoms :   51 ( 238 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t15_yellow19,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
            & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
            & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) )
         => X2 = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).

fof(t2_yellow19,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
            & v2_waybel_0(X2,k3_yellow_1(X1))
            & v13_waybel_0(X2,k3_yellow_1(X1))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) )
         => ! [X3] :
              ~ ( r2_hidden(X3,X2)
                & v1_xboole_0(X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow19)).

fof(d2_yellow_1,axiom,(
    ! [X1] : k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t14_yellow19,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
            & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))),X2,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow19)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(fc5_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(k2_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(c_0_12,plain,(
    ! [X16,X17,X18,X19,X20,X21] :
      ( ( ~ r2_hidden(X18,X17)
        | X18 = X16
        | X17 != k1_tarski(X16) )
      & ( X19 != X16
        | r2_hidden(X19,X17)
        | X17 != k1_tarski(X16) )
      & ( ~ r2_hidden(esk3_2(X20,X21),X21)
        | esk3_2(X20,X21) != X20
        | X21 = k1_tarski(X20) )
      & ( r2_hidden(esk3_2(X20,X21),X21)
        | esk3_2(X20,X21) = X20
        | X21 = k1_tarski(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_13,plain,(
    ! [X23] : k2_tarski(X23,X23) = k1_tarski(X23) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_14,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_16,plain,(
    ! [X8,X9,X11,X12,X13] :
      ( ( r2_hidden(esk2_2(X8,X9),X8)
        | r1_xboole_0(X8,X9) )
      & ( r2_hidden(esk2_2(X8,X9),X9)
        | r1_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X13,X11)
        | ~ r2_hidden(X13,X12)
        | ~ r1_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_17,plain,
    ( X1 = X3
    | X2 != k2_tarski(X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_tarski(X2,X2)) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(esk2_2(X1,X2),X3) ),
    inference(pm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,plain,
    ( esk2_2(k2_tarski(X1,X1),X2) = X1
    | r1_xboole_0(k2_tarski(X1,X1),X2) ),
    inference(pm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,plain,
    ( r1_xboole_0(k2_tarski(X1,X1),X2)
    | ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,X3) ),
    inference(pm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,plain,
    ( r1_xboole_0(k2_tarski(X1,X1),X2)
    | r2_hidden(X1,X2) ),
    inference(pm,[status(thm)],[c_0_19,c_0_23])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X2) ),
    inference(rw,[status(thm)],[c_0_24,c_0_15])).

fof(c_0_28,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_struct_0(X1) )
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
              & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
              & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) )
           => X2 = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t15_yellow19])).

cnf(c_0_29,plain,
    ( r1_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2))
    | r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3) ),
    inference(pm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,k2_tarski(X2,X2))
    | X1 != X2 ),
    inference(er,[status(thm)],[c_0_27])).

fof(c_0_31,plain,(
    ! [X31,X32,X33] :
      ( v1_xboole_0(X31)
      | v1_xboole_0(X32)
      | ~ v1_subset_1(X32,u1_struct_0(k3_yellow_1(X31)))
      | ~ v2_waybel_0(X32,k3_yellow_1(X31))
      | ~ v13_waybel_0(X32,k3_yellow_1(X31))
      | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X31))))
      | ~ r2_hidden(X33,X32)
      | ~ v1_xboole_0(X33) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t2_yellow19])])])])).

fof(c_0_32,plain,(
    ! [X28] : k3_yellow_1(X28) = k3_lattice3(k1_lattice3(X28)) ),
    inference(variable_rename,[status(thm)],[d2_yellow_1])).

fof(c_0_33,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & l1_struct_0(esk4_0)
    & ~ v1_xboole_0(esk5_0)
    & v1_subset_1(esk5_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk4_0))))
    & v2_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk4_0)))
    & v13_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk4_0)))
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk4_0)))))
    & esk5_0 != k2_yellow19(esk4_0,k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_28])])])])).

cnf(c_0_34,plain,
    ( r1_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2))
    | r2_hidden(X2,k2_tarski(X3,X3))
    | X1 != X3 ),
    inference(pm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_35,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X2)
    | X2 != k2_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_27])).

fof(c_0_37,plain,(
    ! [X29,X30] :
      ( v2_struct_0(X29)
      | ~ l1_struct_0(X29)
      | v1_xboole_0(X30)
      | ~ v2_waybel_0(X30,k3_yellow_1(k2_struct_0(X29)))
      | ~ v13_waybel_0(X30,k3_yellow_1(k2_struct_0(X29)))
      | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X29)))))
      | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X29))),X30,k1_tarski(k1_xboole_0)) = k2_yellow19(X29,k3_yellow19(X29,k2_struct_0(X29),X30)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow19])])])])).

cnf(c_0_38,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
    | ~ v2_waybel_0(X2,k3_yellow_1(X1))
    | ~ v13_waybel_0(X2,k3_yellow_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ r2_hidden(X3,X2)
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk4_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( v1_subset_1(esk5_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( v13_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( v2_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_45,plain,
    ( X1 = X2
    | r1_xboole_0(k2_tarski(X3,X3),k2_tarski(X1,X1))
    | X3 != X2 ),
    inference(pm,[status(thm)],[c_0_20,c_0_34])).

cnf(c_0_46,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,k2_tarski(X1,X1)) ),
    inference(er,[status(thm)],[c_0_36])).

fof(c_0_48,plain,(
    ! [X24,X25,X26] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(X24))
      | k7_subset_1(X24,X25,X26) = k4_xboole_0(X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_49,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))),X2,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | ~ l1_struct_0(X1)
    | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_50,plain,(
    ! [X27] :
      ( v2_struct_0(X27)
      | ~ l1_struct_0(X27)
      | ~ v1_xboole_0(k2_struct_0(X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_struct_0])])])).

cnf(c_0_51,plain,
    ( v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ v1_xboole_0(X3)
    | ~ r2_hidden(X3,X2)
    | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
    | ~ v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39]),c_0_39]),c_0_39]),c_0_39])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk4_0)))))) ),
    inference(rw,[status(thm)],[c_0_40,c_0_39])).

cnf(c_0_53,negated_conjecture,
    ( v1_subset_1(esk5_0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk4_0))))) ),
    inference(rw,[status(thm)],[c_0_41,c_0_39])).

cnf(c_0_54,negated_conjecture,
    ( v13_waybel_0(esk5_0,k3_lattice3(k1_lattice3(k2_struct_0(esk4_0)))) ),
    inference(rw,[status(thm)],[c_0_42,c_0_39])).

cnf(c_0_55,negated_conjecture,
    ( v2_waybel_0(esk5_0,k3_lattice3(k1_lattice3(k2_struct_0(esk4_0)))) ),
    inference(rw,[status(thm)],[c_0_43,c_0_39])).

cnf(c_0_56,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_57,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_58,plain,
    ( r1_xboole_0(k2_tarski(X1,X1),k2_tarski(k1_xboole_0,k1_xboole_0))
    | v1_xboole_0(X2)
    | X1 != X2 ),
    inference(pm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_59,plain,
    ( ~ v1_xboole_0(k2_tarski(X1,X1)) ),
    inference(pm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_60,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_61,plain,
    ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X2,k2_tarski(k1_xboole_0,k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_15]),c_0_39]),c_0_39]),c_0_39]),c_0_39])).

cnf(c_0_62,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(k2_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_63,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk4_0))
    | ~ r2_hidden(X1,esk5_0)
    | ~ v1_xboole_0(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_54]),c_0_55])]),c_0_56])).

cnf(c_0_64,negated_conjecture,
    ( l1_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_65,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_66,plain,
    ( v1_xboole_0(X1)
    | ~ r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_1(X1),X2) ),
    inference(pm,[status(thm)],[c_0_18,c_0_57])).

cnf(c_0_67,plain,
    ( r1_xboole_0(k2_tarski(X1,X1),k2_tarski(k1_xboole_0,k1_xboole_0))
    | v1_xboole_0(X1) ),
    inference(er,[status(thm)],[c_0_58])).

cnf(c_0_68,plain,
    ( esk1_1(k2_tarski(X1,X1)) = X1 ),
    inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_20,c_0_57]),c_0_59])).

cnf(c_0_69,plain,
    ( k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)) = k4_xboole_0(X2,k2_tarski(k1_xboole_0,k1_xboole_0))
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))) ),
    inference(pm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_70,negated_conjecture,
    ( ~ r2_hidden(X1,esk5_0)
    | ~ v1_xboole_0(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_62,c_0_63]),c_0_64])]),c_0_65])).

cnf(c_0_71,plain,
    ( v1_xboole_0(X1)
    | ~ r2_hidden(X1,k2_tarski(k1_xboole_0,k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_66,c_0_67]),c_0_68]),c_0_59])).

cnf(c_0_72,negated_conjecture,
    ( esk5_0 != k2_yellow19(esk4_0,k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_73,negated_conjecture,
    ( k2_yellow19(esk4_0,k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0)) = k4_xboole_0(esk5_0,k2_tarski(k1_xboole_0,k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_69,c_0_52]),c_0_54]),c_0_55]),c_0_64])]),c_0_65]),c_0_56])).

fof(c_0_74,plain,(
    ! [X14,X15] :
      ( ( ~ r1_xboole_0(X14,X15)
        | k4_xboole_0(X14,X15) = X14 )
      & ( k4_xboole_0(X14,X15) != X14
        | r1_xboole_0(X14,X15) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_75,negated_conjecture,
    ( r1_xboole_0(esk5_0,X1)
    | ~ v1_xboole_0(esk2_2(esk5_0,X1)) ),
    inference(pm,[status(thm)],[c_0_70,c_0_21])).

cnf(c_0_76,plain,
    ( r1_xboole_0(X1,k2_tarski(k1_xboole_0,k1_xboole_0))
    | v1_xboole_0(esk2_2(X1,k2_tarski(k1_xboole_0,k1_xboole_0))) ),
    inference(pm,[status(thm)],[c_0_71,c_0_19])).

cnf(c_0_77,negated_conjecture,
    ( k4_xboole_0(esk5_0,k2_tarski(k1_xboole_0,k1_xboole_0)) != esk5_0 ),
    inference(rw,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_78,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_79,negated_conjecture,
    ( r1_xboole_0(esk5_0,k2_tarski(k1_xboole_0,k1_xboole_0)) ),
    inference(pm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_77,c_0_78]),c_0_79])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:24:55 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 4.93/5.15  # AutoSched0-Mode selected heuristic G_E___300_C01_S00
% 4.93/5.15  # and selection function NoSelection.
% 4.93/5.15  #
% 4.93/5.15  # Preprocessing time       : 0.028 s
% 4.93/5.15  
% 4.93/5.15  # Proof found!
% 4.93/5.15  # SZS status Theorem
% 4.93/5.15  # SZS output start CNFRefutation
% 4.93/5.15  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 4.93/5.15  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.93/5.15  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.93/5.15  fof(t15_yellow19, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 4.93/5.15  fof(t2_yellow19, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))))&v2_waybel_0(X2,k3_yellow_1(X1)))&v13_waybel_0(X2,k3_yellow_1(X1)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))))=>![X3]:~((r2_hidden(X3,X2)&v1_xboole_0(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_yellow19)).
% 4.93/5.15  fof(d2_yellow_1, axiom, ![X1]:k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_yellow_1)).
% 4.93/5.15  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.93/5.15  fof(t14_yellow19, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))),X2,k1_tarski(k1_xboole_0))=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow19)).
% 4.93/5.15  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.93/5.15  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.93/5.15  fof(fc5_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(k2_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 4.93/5.15  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.93/5.15  fof(c_0_12, plain, ![X16, X17, X18, X19, X20, X21]:(((~r2_hidden(X18,X17)|X18=X16|X17!=k1_tarski(X16))&(X19!=X16|r2_hidden(X19,X17)|X17!=k1_tarski(X16)))&((~r2_hidden(esk3_2(X20,X21),X21)|esk3_2(X20,X21)!=X20|X21=k1_tarski(X20))&(r2_hidden(esk3_2(X20,X21),X21)|esk3_2(X20,X21)=X20|X21=k1_tarski(X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 4.93/5.15  fof(c_0_13, plain, ![X23]:k2_tarski(X23,X23)=k1_tarski(X23), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 4.93/5.15  cnf(c_0_14, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 4.93/5.15  cnf(c_0_15, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 4.93/5.15  fof(c_0_16, plain, ![X8, X9, X11, X12, X13]:(((r2_hidden(esk2_2(X8,X9),X8)|r1_xboole_0(X8,X9))&(r2_hidden(esk2_2(X8,X9),X9)|r1_xboole_0(X8,X9)))&(~r2_hidden(X13,X11)|~r2_hidden(X13,X12)|~r1_xboole_0(X11,X12))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 4.93/5.15  cnf(c_0_17, plain, (X1=X3|X2!=k2_tarski(X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 4.93/5.15  cnf(c_0_18, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 4.93/5.15  cnf(c_0_19, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 4.93/5.15  cnf(c_0_20, plain, (X1=X2|~r2_hidden(X1,k2_tarski(X2,X2))), inference(er,[status(thm)],[c_0_17])).
% 4.93/5.15  cnf(c_0_21, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 4.93/5.15  cnf(c_0_22, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X3)|~r2_hidden(esk2_2(X1,X2),X3)), inference(pm,[status(thm)],[c_0_18, c_0_19])).
% 4.93/5.15  cnf(c_0_23, plain, (esk2_2(k2_tarski(X1,X1),X2)=X1|r1_xboole_0(k2_tarski(X1,X1),X2)), inference(pm,[status(thm)],[c_0_20, c_0_21])).
% 4.93/5.15  cnf(c_0_24, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 4.93/5.15  cnf(c_0_25, plain, (r1_xboole_0(k2_tarski(X1,X1),X2)|~r1_xboole_0(X2,X3)|~r2_hidden(X1,X3)), inference(pm,[status(thm)],[c_0_22, c_0_23])).
% 4.93/5.15  cnf(c_0_26, plain, (r1_xboole_0(k2_tarski(X1,X1),X2)|r2_hidden(X1,X2)), inference(pm,[status(thm)],[c_0_19, c_0_23])).
% 4.93/5.15  cnf(c_0_27, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X2)), inference(rw,[status(thm)],[c_0_24, c_0_15])).
% 4.93/5.15  fof(c_0_28, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))))), inference(assume_negation,[status(cth)],[t15_yellow19])).
% 4.93/5.15  cnf(c_0_29, plain, (r1_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2))|r2_hidden(X2,X3)|~r2_hidden(X1,X3)), inference(pm,[status(thm)],[c_0_25, c_0_26])).
% 4.93/5.15  cnf(c_0_30, plain, (r2_hidden(X1,k2_tarski(X2,X2))|X1!=X2), inference(er,[status(thm)],[c_0_27])).
% 4.93/5.15  fof(c_0_31, plain, ![X31, X32, X33]:(v1_xboole_0(X31)|(v1_xboole_0(X32)|~v1_subset_1(X32,u1_struct_0(k3_yellow_1(X31)))|~v2_waybel_0(X32,k3_yellow_1(X31))|~v13_waybel_0(X32,k3_yellow_1(X31))|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X31))))|(~r2_hidden(X33,X32)|~v1_xboole_0(X33)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t2_yellow19])])])])).
% 4.93/5.15  fof(c_0_32, plain, ![X28]:k3_yellow_1(X28)=k3_lattice3(k1_lattice3(X28)), inference(variable_rename,[status(thm)],[d2_yellow_1])).
% 4.93/5.15  fof(c_0_33, negated_conjecture, ((~v2_struct_0(esk4_0)&l1_struct_0(esk4_0))&(((((~v1_xboole_0(esk5_0)&v1_subset_1(esk5_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk4_0)))))&v2_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk4_0))))&v13_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk4_0))))&m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk4_0))))))&esk5_0!=k2_yellow19(esk4_0,k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_28])])])])).
% 4.93/5.15  cnf(c_0_34, plain, (r1_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2))|r2_hidden(X2,k2_tarski(X3,X3))|X1!=X3), inference(pm,[status(thm)],[c_0_29, c_0_30])).
% 4.93/5.15  fof(c_0_35, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 4.93/5.15  cnf(c_0_36, plain, (r2_hidden(X1,X2)|X2!=k2_tarski(X1,X1)), inference(er,[status(thm)],[c_0_27])).
% 4.93/5.15  fof(c_0_37, plain, ![X29, X30]:(v2_struct_0(X29)|~l1_struct_0(X29)|(v1_xboole_0(X30)|~v2_waybel_0(X30,k3_yellow_1(k2_struct_0(X29)))|~v13_waybel_0(X30,k3_yellow_1(k2_struct_0(X29)))|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X29)))))|k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X29))),X30,k1_tarski(k1_xboole_0))=k2_yellow19(X29,k3_yellow19(X29,k2_struct_0(X29),X30)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow19])])])])).
% 4.93/5.15  cnf(c_0_38, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))|~v2_waybel_0(X2,k3_yellow_1(X1))|~v13_waybel_0(X2,k3_yellow_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))|~r2_hidden(X3,X2)|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 4.93/5.15  cnf(c_0_39, plain, (k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 4.93/5.15  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk4_0)))))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 4.93/5.15  cnf(c_0_41, negated_conjecture, (v1_subset_1(esk5_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 4.93/5.15  cnf(c_0_42, negated_conjecture, (v13_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 4.93/5.15  cnf(c_0_43, negated_conjecture, (v2_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 4.93/5.15  cnf(c_0_44, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 4.93/5.15  cnf(c_0_45, plain, (X1=X2|r1_xboole_0(k2_tarski(X3,X3),k2_tarski(X1,X1))|X3!=X2), inference(pm,[status(thm)],[c_0_20, c_0_34])).
% 4.93/5.15  cnf(c_0_46, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 4.93/5.15  cnf(c_0_47, plain, (r2_hidden(X1,k2_tarski(X1,X1))), inference(er,[status(thm)],[c_0_36])).
% 4.93/5.15  fof(c_0_48, plain, ![X24, X25, X26]:(~m1_subset_1(X25,k1_zfmisc_1(X24))|k7_subset_1(X24,X25,X26)=k4_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 4.93/5.15  cnf(c_0_49, plain, (v2_struct_0(X1)|v1_xboole_0(X2)|k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))),X2,k1_tarski(k1_xboole_0))=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))|~l1_struct_0(X1)|~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))|~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 4.93/5.15  fof(c_0_50, plain, ![X27]:(v2_struct_0(X27)|~l1_struct_0(X27)|~v1_xboole_0(k2_struct_0(X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_struct_0])])])).
% 4.93/5.15  cnf(c_0_51, plain, (v1_xboole_0(X2)|v1_xboole_0(X1)|~v1_xboole_0(X3)|~r2_hidden(X3,X2)|~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))|~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))|~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39]), c_0_39]), c_0_39]), c_0_39])).
% 4.93/5.15  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk4_0))))))), inference(rw,[status(thm)],[c_0_40, c_0_39])).
% 4.93/5.15  cnf(c_0_53, negated_conjecture, (v1_subset_1(esk5_0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk4_0)))))), inference(rw,[status(thm)],[c_0_41, c_0_39])).
% 4.93/5.15  cnf(c_0_54, negated_conjecture, (v13_waybel_0(esk5_0,k3_lattice3(k1_lattice3(k2_struct_0(esk4_0))))), inference(rw,[status(thm)],[c_0_42, c_0_39])).
% 4.93/5.15  cnf(c_0_55, negated_conjecture, (v2_waybel_0(esk5_0,k3_lattice3(k1_lattice3(k2_struct_0(esk4_0))))), inference(rw,[status(thm)],[c_0_43, c_0_39])).
% 4.93/5.15  cnf(c_0_56, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 4.93/5.15  cnf(c_0_57, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 4.93/5.15  cnf(c_0_58, plain, (r1_xboole_0(k2_tarski(X1,X1),k2_tarski(k1_xboole_0,k1_xboole_0))|v1_xboole_0(X2)|X1!=X2), inference(pm,[status(thm)],[c_0_44, c_0_45])).
% 4.93/5.15  cnf(c_0_59, plain, (~v1_xboole_0(k2_tarski(X1,X1))), inference(pm,[status(thm)],[c_0_46, c_0_47])).
% 4.93/5.15  cnf(c_0_60, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 4.93/5.15  cnf(c_0_61, plain, (k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X2,k2_tarski(k1_xboole_0,k1_xboole_0))=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))|v1_xboole_0(X2)|v2_struct_0(X1)|~l1_struct_0(X1)|~v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_15]), c_0_39]), c_0_39]), c_0_39]), c_0_39])).
% 4.93/5.15  cnf(c_0_62, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(k2_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 4.93/5.15  cnf(c_0_63, negated_conjecture, (v1_xboole_0(k2_struct_0(esk4_0))|~r2_hidden(X1,esk5_0)|~v1_xboole_0(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_51, c_0_52]), c_0_53]), c_0_54]), c_0_55])]), c_0_56])).
% 4.93/5.15  cnf(c_0_64, negated_conjecture, (l1_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 4.93/5.15  cnf(c_0_65, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 4.93/5.15  cnf(c_0_66, plain, (v1_xboole_0(X1)|~r1_xboole_0(X1,X2)|~r2_hidden(esk1_1(X1),X2)), inference(pm,[status(thm)],[c_0_18, c_0_57])).
% 4.93/5.15  cnf(c_0_67, plain, (r1_xboole_0(k2_tarski(X1,X1),k2_tarski(k1_xboole_0,k1_xboole_0))|v1_xboole_0(X1)), inference(er,[status(thm)],[c_0_58])).
% 4.93/5.15  cnf(c_0_68, plain, (esk1_1(k2_tarski(X1,X1))=X1), inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_20, c_0_57]), c_0_59])).
% 4.93/5.15  cnf(c_0_69, plain, (k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))=k4_xboole_0(X2,k2_tarski(k1_xboole_0,k1_xboole_0))|v2_struct_0(X1)|v1_xboole_0(X2)|~v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))), inference(pm,[status(thm)],[c_0_60, c_0_61])).
% 4.93/5.15  cnf(c_0_70, negated_conjecture, (~r2_hidden(X1,esk5_0)|~v1_xboole_0(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_62, c_0_63]), c_0_64])]), c_0_65])).
% 4.93/5.15  cnf(c_0_71, plain, (v1_xboole_0(X1)|~r2_hidden(X1,k2_tarski(k1_xboole_0,k1_xboole_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_66, c_0_67]), c_0_68]), c_0_59])).
% 4.93/5.15  cnf(c_0_72, negated_conjecture, (esk5_0!=k2_yellow19(esk4_0,k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 4.93/5.15  cnf(c_0_73, negated_conjecture, (k2_yellow19(esk4_0,k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))=k4_xboole_0(esk5_0,k2_tarski(k1_xboole_0,k1_xboole_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_69, c_0_52]), c_0_54]), c_0_55]), c_0_64])]), c_0_65]), c_0_56])).
% 4.93/5.15  fof(c_0_74, plain, ![X14, X15]:((~r1_xboole_0(X14,X15)|k4_xboole_0(X14,X15)=X14)&(k4_xboole_0(X14,X15)!=X14|r1_xboole_0(X14,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 4.93/5.15  cnf(c_0_75, negated_conjecture, (r1_xboole_0(esk5_0,X1)|~v1_xboole_0(esk2_2(esk5_0,X1))), inference(pm,[status(thm)],[c_0_70, c_0_21])).
% 4.93/5.15  cnf(c_0_76, plain, (r1_xboole_0(X1,k2_tarski(k1_xboole_0,k1_xboole_0))|v1_xboole_0(esk2_2(X1,k2_tarski(k1_xboole_0,k1_xboole_0)))), inference(pm,[status(thm)],[c_0_71, c_0_19])).
% 4.93/5.15  cnf(c_0_77, negated_conjecture, (k4_xboole_0(esk5_0,k2_tarski(k1_xboole_0,k1_xboole_0))!=esk5_0), inference(rw,[status(thm)],[c_0_72, c_0_73])).
% 4.93/5.15  cnf(c_0_78, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 4.93/5.15  cnf(c_0_79, negated_conjecture, (r1_xboole_0(esk5_0,k2_tarski(k1_xboole_0,k1_xboole_0))), inference(pm,[status(thm)],[c_0_75, c_0_76])).
% 4.93/5.15  cnf(c_0_80, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_77, c_0_78]), c_0_79])]), ['proof']).
% 4.93/5.15  # SZS output end CNFRefutation
% 4.93/5.15  # Proof object total steps             : 81
% 4.93/5.15  # Proof object clause steps            : 57
% 4.93/5.15  # Proof object formula steps           : 24
% 4.93/5.15  # Proof object conjectures             : 22
% 4.93/5.15  # Proof object clause conjectures      : 19
% 4.93/5.15  # Proof object formula conjectures     : 3
% 4.93/5.15  # Proof object initial clauses used    : 23
% 4.93/5.15  # Proof object initial formulas used   : 12
% 4.93/5.15  # Proof object generating inferences   : 25
% 4.93/5.15  # Proof object simplifying inferences  : 35
% 4.93/5.15  # Training examples: 0 positive, 0 negative
% 4.93/5.15  # Parsed axioms                        : 12
% 4.93/5.15  # Removed by relevancy pruning/SinE    : 0
% 4.93/5.15  # Initial clauses                      : 26
% 4.93/5.15  # Removed in clause preprocessing      : 2
% 4.93/5.15  # Initial clauses in saturation        : 24
% 4.93/5.15  # Processed clauses                    : 5273
% 4.93/5.15  # ...of these trivial                  : 36
% 4.93/5.15  # ...subsumed                          : 4082
% 4.93/5.15  # ...remaining for further processing  : 1155
% 4.93/5.15  # Other redundant clauses eliminated   : 0
% 4.93/5.15  # Clauses deleted for lack of memory   : 0
% 4.93/5.15  # Backward-subsumed                    : 37
% 4.93/5.15  # Backward-rewritten                   : 9
% 4.93/5.15  # Generated clauses                    : 459810
% 4.93/5.15  # ...of the previous two non-trivial   : 444901
% 4.93/5.15  # Contextual simplify-reflections      : 0
% 4.93/5.15  # Paramodulations                      : 459208
% 4.93/5.15  # Factorizations                       : 150
% 4.93/5.15  # Equation resolutions                 : 452
% 4.93/5.15  # Propositional unsat checks           : 0
% 4.93/5.15  #    Propositional check models        : 0
% 4.93/5.15  #    Propositional check unsatisfiable : 0
% 4.93/5.15  #    Propositional clauses             : 0
% 4.93/5.15  #    Propositional clauses after purity: 0
% 4.93/5.15  #    Propositional unsat core size     : 0
% 4.93/5.15  #    Propositional preprocessing time  : 0.000
% 4.93/5.15  #    Propositional encoding time       : 0.000
% 4.93/5.15  #    Propositional solver time         : 0.000
% 4.93/5.15  #    Success case prop preproc time    : 0.000
% 4.93/5.15  #    Success case prop encoding time   : 0.000
% 4.93/5.15  #    Success case prop solver time     : 0.000
% 4.93/5.15  # Current number of processed clauses  : 1109
% 4.93/5.15  #    Positive orientable unit clauses  : 18
% 4.93/5.15  #    Positive unorientable unit clauses: 0
% 4.93/5.15  #    Negative unit clauses             : 26
% 4.93/5.15  #    Non-unit-clauses                  : 1065
% 4.93/5.15  # Current number of unprocessed clauses: 439378
% 4.93/5.15  # ...number of literals in the above   : 2913010
% 4.93/5.15  # Current number of archived formulas  : 0
% 4.93/5.15  # Current number of archived clauses   : 48
% 4.93/5.15  # Clause-clause subsumption calls (NU) : 126482
% 4.93/5.15  # Rec. Clause-clause subsumption calls : 61818
% 4.93/5.15  # Non-unit clause-clause subsumptions  : 3366
% 4.93/5.15  # Unit Clause-clause subsumption calls : 1681
% 4.93/5.15  # Rewrite failures with RHS unbound    : 0
% 4.93/5.15  # BW rewrite match attempts            : 7
% 4.93/5.15  # BW rewrite match successes           : 6
% 4.93/5.15  # Condensation attempts                : 0
% 4.93/5.15  # Condensation successes               : 0
% 4.93/5.15  # Termbank termtop insertions          : 6555256
% 5.00/5.17  
% 5.00/5.17  # -------------------------------------------------
% 5.00/5.17  # User time                : 4.655 s
% 5.00/5.17  # System time              : 0.169 s
% 5.00/5.17  # Total time               : 4.824 s
% 5.00/5.17  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
