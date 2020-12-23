%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:54 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 187 expanded)
%              Number of clauses        :   50 (  78 expanded)
%              Number of leaves         :   14 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :  230 ( 631 expanded)
%              Number of equality atoms :   52 ( 151 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow19)).

fof(d2_yellow_1,axiom,(
    ! [X1] : k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow19)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(fc5_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(k2_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_14,plain,(
    ! [X23,X24,X25] :
      ( ( r2_hidden(X23,X24)
        | ~ r2_hidden(X23,k4_xboole_0(X24,k1_tarski(X25))) )
      & ( X23 != X25
        | ~ r2_hidden(X23,k4_xboole_0(X24,k1_tarski(X25))) )
      & ( ~ r2_hidden(X23,X24)
        | X23 = X25
        | r2_hidden(X23,k4_xboole_0(X24,k1_tarski(X25))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

fof(c_0_15,plain,(
    ! [X18,X19] : k4_xboole_0(X18,X19) = k5_xboole_0(X18,k3_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_16,plain,(
    ! [X20] : k4_xboole_0(k1_xboole_0,X20) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_17,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X16,X17] :
      ( ( k4_xboole_0(X16,X17) != k1_xboole_0
        | r1_tarski(X16,X17) )
      & ( ~ r1_tarski(X16,X17)
        | k4_xboole_0(X16,X17) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_21,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k5_xboole_0(X3,k3_xboole_0(X3,k1_tarski(X2)))) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_19,c_0_18])).

fof(c_0_23,negated_conjecture,(
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

cnf(c_0_24,plain,
    ( X1 = X3
    | r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(pm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_27,plain,(
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(X26))
      | k7_subset_1(X26,X27,X28) = k4_xboole_0(X27,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_28,plain,(
    ! [X31,X32] :
      ( v2_struct_0(X31)
      | ~ l1_struct_0(X31)
      | v1_xboole_0(X32)
      | ~ v2_waybel_0(X32,k3_yellow_1(k2_struct_0(X31)))
      | ~ v13_waybel_0(X32,k3_yellow_1(k2_struct_0(X31)))
      | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X31)))))
      | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X31))),X32,k1_tarski(k1_xboole_0)) = k2_yellow19(X31,k3_yellow19(X31,k2_struct_0(X31),X32)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow19])])])])).

fof(c_0_29,plain,(
    ! [X30] : k3_yellow_1(X30) = k3_lattice3(k1_lattice3(X30)) ),
    inference(variable_rename,[status(thm)],[d2_yellow_1])).

fof(c_0_30,plain,(
    ! [X33,X34,X35] :
      ( v1_xboole_0(X33)
      | v1_xboole_0(X34)
      | ~ v1_subset_1(X34,u1_struct_0(k3_yellow_1(X33)))
      | ~ v2_waybel_0(X34,k3_yellow_1(X33))
      | ~ v13_waybel_0(X34,k3_yellow_1(X33))
      | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X33))))
      | ~ r2_hidden(X35,X34)
      | ~ v1_xboole_0(X35) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t2_yellow19])])])])).

fof(c_0_31,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & l1_struct_0(esk3_0)
    & ~ v1_xboole_0(esk4_0)
    & v1_subset_1(esk4_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0))))
    & v2_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0)))
    & v13_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0)))
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0)))))
    & esk4_0 != k2_yellow19(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_23])])])])).

cnf(c_0_32,plain,
    ( X1 = X3
    | r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k1_tarski(X3))))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_24,c_0_18])).

cnf(c_0_33,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_25,c_0_18])).

cnf(c_0_34,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_26])).

fof(c_0_35,plain,(
    ! [X8,X9,X11,X12,X13] :
      ( ( r2_hidden(esk2_2(X8,X9),X8)
        | r1_xboole_0(X8,X9) )
      & ( r2_hidden(esk2_2(X8,X9),X9)
        | r1_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X13,X11)
        | ~ r2_hidden(X13,X12)
        | ~ r1_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_36,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))),X2,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | ~ l1_struct_0(X1)
    | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
    | ~ v2_waybel_0(X2,k3_yellow_1(X1))
    | ~ v13_waybel_0(X2,k3_yellow_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ r2_hidden(X3,X2)
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( v1_subset_1(esk4_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( v13_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,negated_conjecture,
    ( v2_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,plain,
    ( X1 = X2
    | ~ r1_tarski(X3,k1_tarski(X2))
    | ~ r2_hidden(X1,X3) ),
    inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

cnf(c_0_45,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k3_xboole_0(X1,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_36,c_0_18])).

cnf(c_0_47,plain,
    ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X2,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38]),c_0_38]),c_0_38]),c_0_38])).

fof(c_0_48,plain,(
    ! [X29] :
      ( v2_struct_0(X29)
      | ~ l1_struct_0(X29)
      | ~ v1_xboole_0(k2_struct_0(X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_struct_0])])])).

cnf(c_0_49,plain,
    ( v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ v1_xboole_0(X3)
    | ~ r2_hidden(X3,X2)
    | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
    | ~ v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_38]),c_0_38]),c_0_38]),c_0_38])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk3_0)))))) ),
    inference(rw,[status(thm)],[c_0_40,c_0_38])).

cnf(c_0_51,negated_conjecture,
    ( v1_subset_1(esk4_0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk3_0))))) ),
    inference(rw,[status(thm)],[c_0_41,c_0_38])).

cnf(c_0_52,negated_conjecture,
    ( v13_waybel_0(esk4_0,k3_lattice3(k1_lattice3(k2_struct_0(esk3_0)))) ),
    inference(rw,[status(thm)],[c_0_42,c_0_38])).

cnf(c_0_53,negated_conjecture,
    ( v2_waybel_0(esk4_0,k3_lattice3(k1_lattice3(k2_struct_0(esk3_0)))) ),
    inference(rw,[status(thm)],[c_0_43,c_0_38])).

cnf(c_0_54,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_55,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_56,plain,
    ( esk2_2(X1,X2) = X3
    | r1_xboole_0(X1,X2)
    | ~ r1_tarski(X2,k1_tarski(X3)) ),
    inference(pm,[status(thm)],[c_0_44,c_0_45])).

fof(c_0_57,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(X14,X15)
        | X14 != X15 )
      & ( r1_tarski(X15,X14)
        | X14 != X15 )
      & ( ~ r1_tarski(X14,X15)
        | ~ r1_tarski(X15,X14)
        | X14 = X15 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_58,plain,
    ( k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)) = k5_xboole_0(X2,k3_xboole_0(X2,k1_tarski(k1_xboole_0)))
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))) ),
    inference(pm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_59,negated_conjecture,
    ( l1_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_60,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_61,plain,(
    ! [X21,X22] :
      ( ( ~ r1_xboole_0(X21,X22)
        | k4_xboole_0(X21,X22) = X21 )
      & ( k4_xboole_0(X21,X22) != X21
        | r1_xboole_0(X21,X22) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_62,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(k2_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_63,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk4_0)
    | ~ v1_xboole_0(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_52]),c_0_53])]),c_0_54])).

cnf(c_0_64,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(X3,X1)
    | ~ r1_tarski(X2,k1_tarski(X3)) ),
    inference(pm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_65,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_66,negated_conjecture,
    ( esk4_0 != k2_yellow19(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_67,negated_conjecture,
    ( k2_yellow19(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0)) = k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k1_tarski(k1_xboole_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_58,c_0_50]),c_0_52]),c_0_53]),c_0_59])]),c_0_60]),c_0_54])).

cnf(c_0_68,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( ~ r2_hidden(X1,esk4_0)
    | ~ v1_xboole_0(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_62,c_0_63]),c_0_59])]),c_0_60])).

cnf(c_0_70,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(X3,X1)
    | X2 != k1_tarski(X3) ),
    inference(pm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k1_tarski(k1_xboole_0))) != esk4_0 ),
    inference(rw,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_72,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_68,c_0_18])).

cnf(c_0_73,negated_conjecture,
    ( r1_xboole_0(esk4_0,X1)
    | X1 != k1_tarski(X2)
    | ~ v1_xboole_0(X2) ),
    inference(pm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( ~ r1_xboole_0(esk4_0,k1_tarski(k1_xboole_0)) ),
    inference(pm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_75,negated_conjecture,
    ( r1_xboole_0(esk4_0,k1_tarski(X1))
    | ~ v1_xboole_0(X1) ),
    inference(er,[status(thm)],[c_0_73])).

cnf(c_0_76,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_77,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_74,c_0_75]),c_0_76])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:26:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 2.45/2.61  # AutoSched0-Mode selected heuristic G_E___300_C01_S00
% 2.45/2.61  # and selection function NoSelection.
% 2.45/2.61  #
% 2.45/2.61  # Preprocessing time       : 0.028 s
% 2.45/2.61  
% 2.45/2.61  # Proof found!
% 2.45/2.61  # SZS status Theorem
% 2.45/2.61  # SZS output start CNFRefutation
% 2.45/2.61  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.45/2.61  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.45/2.61  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.45/2.61  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.45/2.61  fof(t15_yellow19, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 2.45/2.61  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.45/2.61  fof(t14_yellow19, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))),X2,k1_tarski(k1_xboole_0))=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow19)).
% 2.45/2.61  fof(d2_yellow_1, axiom, ![X1]:k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_yellow_1)).
% 2.45/2.61  fof(t2_yellow19, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))))&v2_waybel_0(X2,k3_yellow_1(X1)))&v13_waybel_0(X2,k3_yellow_1(X1)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))))=>![X3]:~((r2_hidden(X3,X2)&v1_xboole_0(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_yellow19)).
% 2.45/2.61  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.45/2.61  fof(fc5_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(k2_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 2.45/2.61  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.45/2.61  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.45/2.61  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.45/2.61  fof(c_0_14, plain, ![X23, X24, X25]:(((r2_hidden(X23,X24)|~r2_hidden(X23,k4_xboole_0(X24,k1_tarski(X25))))&(X23!=X25|~r2_hidden(X23,k4_xboole_0(X24,k1_tarski(X25)))))&(~r2_hidden(X23,X24)|X23=X25|r2_hidden(X23,k4_xboole_0(X24,k1_tarski(X25))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 2.45/2.61  fof(c_0_15, plain, ![X18, X19]:k4_xboole_0(X18,X19)=k5_xboole_0(X18,k3_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 2.45/2.61  fof(c_0_16, plain, ![X20]:k4_xboole_0(k1_xboole_0,X20)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 2.45/2.61  cnf(c_0_17, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.45/2.61  cnf(c_0_18, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.45/2.61  cnf(c_0_19, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.45/2.61  fof(c_0_20, plain, ![X16, X17]:((k4_xboole_0(X16,X17)!=k1_xboole_0|r1_tarski(X16,X17))&(~r1_tarski(X16,X17)|k4_xboole_0(X16,X17)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 2.45/2.61  cnf(c_0_21, plain, (X1!=X2|~r2_hidden(X1,k5_xboole_0(X3,k3_xboole_0(X3,k1_tarski(X2))))), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 2.45/2.61  cnf(c_0_22, plain, (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(rw,[status(thm)],[c_0_19, c_0_18])).
% 2.45/2.61  fof(c_0_23, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))))), inference(assume_negation,[status(cth)],[t15_yellow19])).
% 2.45/2.61  cnf(c_0_24, plain, (X1=X3|r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.45/2.61  cnf(c_0_25, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.45/2.61  cnf(c_0_26, plain, (X1!=X2|~r2_hidden(X1,k1_xboole_0)), inference(pm,[status(thm)],[c_0_21, c_0_22])).
% 2.45/2.61  fof(c_0_27, plain, ![X26, X27, X28]:(~m1_subset_1(X27,k1_zfmisc_1(X26))|k7_subset_1(X26,X27,X28)=k4_xboole_0(X27,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 2.45/2.61  fof(c_0_28, plain, ![X31, X32]:(v2_struct_0(X31)|~l1_struct_0(X31)|(v1_xboole_0(X32)|~v2_waybel_0(X32,k3_yellow_1(k2_struct_0(X31)))|~v13_waybel_0(X32,k3_yellow_1(k2_struct_0(X31)))|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X31)))))|k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X31))),X32,k1_tarski(k1_xboole_0))=k2_yellow19(X31,k3_yellow19(X31,k2_struct_0(X31),X32)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow19])])])])).
% 2.45/2.61  fof(c_0_29, plain, ![X30]:k3_yellow_1(X30)=k3_lattice3(k1_lattice3(X30)), inference(variable_rename,[status(thm)],[d2_yellow_1])).
% 2.45/2.61  fof(c_0_30, plain, ![X33, X34, X35]:(v1_xboole_0(X33)|(v1_xboole_0(X34)|~v1_subset_1(X34,u1_struct_0(k3_yellow_1(X33)))|~v2_waybel_0(X34,k3_yellow_1(X33))|~v13_waybel_0(X34,k3_yellow_1(X33))|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X33))))|(~r2_hidden(X35,X34)|~v1_xboole_0(X35)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t2_yellow19])])])])).
% 2.45/2.61  fof(c_0_31, negated_conjecture, ((~v2_struct_0(esk3_0)&l1_struct_0(esk3_0))&(((((~v1_xboole_0(esk4_0)&v1_subset_1(esk4_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0)))))&v2_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0))))&v13_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0))))&m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0))))))&esk4_0!=k2_yellow19(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_23])])])])).
% 2.45/2.61  cnf(c_0_32, plain, (X1=X3|r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k1_tarski(X3))))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_24, c_0_18])).
% 2.45/2.61  cnf(c_0_33, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_25, c_0_18])).
% 2.45/2.61  cnf(c_0_34, plain, (~r2_hidden(X1,k1_xboole_0)), inference(er,[status(thm)],[c_0_26])).
% 2.45/2.61  fof(c_0_35, plain, ![X8, X9, X11, X12, X13]:(((r2_hidden(esk2_2(X8,X9),X8)|r1_xboole_0(X8,X9))&(r2_hidden(esk2_2(X8,X9),X9)|r1_xboole_0(X8,X9)))&(~r2_hidden(X13,X11)|~r2_hidden(X13,X12)|~r1_xboole_0(X11,X12))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 2.45/2.61  cnf(c_0_36, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 2.45/2.61  cnf(c_0_37, plain, (v2_struct_0(X1)|v1_xboole_0(X2)|k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))),X2,k1_tarski(k1_xboole_0))=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))|~l1_struct_0(X1)|~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))|~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 2.45/2.61  cnf(c_0_38, plain, (k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 2.45/2.61  cnf(c_0_39, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))|~v2_waybel_0(X2,k3_yellow_1(X1))|~v13_waybel_0(X2,k3_yellow_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))|~r2_hidden(X3,X2)|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 2.45/2.61  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0)))))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 2.45/2.61  cnf(c_0_41, negated_conjecture, (v1_subset_1(esk4_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 2.45/2.61  cnf(c_0_42, negated_conjecture, (v13_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 2.45/2.61  cnf(c_0_43, negated_conjecture, (v2_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 2.45/2.61  cnf(c_0_44, plain, (X1=X2|~r1_tarski(X3,k1_tarski(X2))|~r2_hidden(X1,X3)), inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_32, c_0_33]), c_0_34])).
% 2.45/2.61  cnf(c_0_45, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 2.45/2.61  cnf(c_0_46, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k3_xboole_0(X1,X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_36, c_0_18])).
% 2.45/2.61  cnf(c_0_47, plain, (k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X2,k1_tarski(k1_xboole_0))=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))|v1_xboole_0(X2)|v2_struct_0(X1)|~l1_struct_0(X1)|~v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38]), c_0_38]), c_0_38]), c_0_38])).
% 2.45/2.61  fof(c_0_48, plain, ![X29]:(v2_struct_0(X29)|~l1_struct_0(X29)|~v1_xboole_0(k2_struct_0(X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_struct_0])])])).
% 2.45/2.61  cnf(c_0_49, plain, (v1_xboole_0(X2)|v1_xboole_0(X1)|~v1_xboole_0(X3)|~r2_hidden(X3,X2)|~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))|~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))|~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_38]), c_0_38]), c_0_38]), c_0_38])).
% 2.45/2.61  cnf(c_0_50, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk3_0))))))), inference(rw,[status(thm)],[c_0_40, c_0_38])).
% 2.45/2.61  cnf(c_0_51, negated_conjecture, (v1_subset_1(esk4_0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk3_0)))))), inference(rw,[status(thm)],[c_0_41, c_0_38])).
% 2.45/2.61  cnf(c_0_52, negated_conjecture, (v13_waybel_0(esk4_0,k3_lattice3(k1_lattice3(k2_struct_0(esk3_0))))), inference(rw,[status(thm)],[c_0_42, c_0_38])).
% 2.45/2.61  cnf(c_0_53, negated_conjecture, (v2_waybel_0(esk4_0,k3_lattice3(k1_lattice3(k2_struct_0(esk3_0))))), inference(rw,[status(thm)],[c_0_43, c_0_38])).
% 2.45/2.61  cnf(c_0_54, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 2.45/2.61  cnf(c_0_55, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 2.45/2.61  cnf(c_0_56, plain, (esk2_2(X1,X2)=X3|r1_xboole_0(X1,X2)|~r1_tarski(X2,k1_tarski(X3))), inference(pm,[status(thm)],[c_0_44, c_0_45])).
% 2.45/2.61  fof(c_0_57, plain, ![X14, X15]:(((r1_tarski(X14,X15)|X14!=X15)&(r1_tarski(X15,X14)|X14!=X15))&(~r1_tarski(X14,X15)|~r1_tarski(X15,X14)|X14=X15)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 2.45/2.61  cnf(c_0_58, plain, (k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))=k5_xboole_0(X2,k3_xboole_0(X2,k1_tarski(k1_xboole_0)))|v2_struct_0(X1)|v1_xboole_0(X2)|~v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))), inference(pm,[status(thm)],[c_0_46, c_0_47])).
% 2.45/2.61  cnf(c_0_59, negated_conjecture, (l1_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 2.45/2.61  cnf(c_0_60, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 2.45/2.61  fof(c_0_61, plain, ![X21, X22]:((~r1_xboole_0(X21,X22)|k4_xboole_0(X21,X22)=X21)&(k4_xboole_0(X21,X22)!=X21|r1_xboole_0(X21,X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 2.45/2.61  cnf(c_0_62, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(k2_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 2.45/2.61  cnf(c_0_63, negated_conjecture, (v1_xboole_0(k2_struct_0(esk3_0))|~r2_hidden(X1,esk4_0)|~v1_xboole_0(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_49, c_0_50]), c_0_51]), c_0_52]), c_0_53])]), c_0_54])).
% 2.45/2.61  cnf(c_0_64, plain, (r1_xboole_0(X1,X2)|r2_hidden(X3,X1)|~r1_tarski(X2,k1_tarski(X3))), inference(pm,[status(thm)],[c_0_55, c_0_56])).
% 2.45/2.61  cnf(c_0_65, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_57])).
% 2.45/2.61  cnf(c_0_66, negated_conjecture, (esk4_0!=k2_yellow19(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 2.45/2.61  cnf(c_0_67, negated_conjecture, (k2_yellow19(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))=k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k1_tarski(k1_xboole_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_58, c_0_50]), c_0_52]), c_0_53]), c_0_59])]), c_0_60]), c_0_54])).
% 2.45/2.61  cnf(c_0_68, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 2.45/2.61  cnf(c_0_69, negated_conjecture, (~r2_hidden(X1,esk4_0)|~v1_xboole_0(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_62, c_0_63]), c_0_59])]), c_0_60])).
% 2.45/2.61  cnf(c_0_70, plain, (r1_xboole_0(X1,X2)|r2_hidden(X3,X1)|X2!=k1_tarski(X3)), inference(pm,[status(thm)],[c_0_64, c_0_65])).
% 2.45/2.61  cnf(c_0_71, negated_conjecture, (k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k1_tarski(k1_xboole_0)))!=esk4_0), inference(rw,[status(thm)],[c_0_66, c_0_67])).
% 2.45/2.61  cnf(c_0_72, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_68, c_0_18])).
% 2.45/2.61  cnf(c_0_73, negated_conjecture, (r1_xboole_0(esk4_0,X1)|X1!=k1_tarski(X2)|~v1_xboole_0(X2)), inference(pm,[status(thm)],[c_0_69, c_0_70])).
% 2.45/2.61  cnf(c_0_74, negated_conjecture, (~r1_xboole_0(esk4_0,k1_tarski(k1_xboole_0))), inference(pm,[status(thm)],[c_0_71, c_0_72])).
% 2.45/2.61  cnf(c_0_75, negated_conjecture, (r1_xboole_0(esk4_0,k1_tarski(X1))|~v1_xboole_0(X1)), inference(er,[status(thm)],[c_0_73])).
% 2.45/2.61  cnf(c_0_76, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 2.45/2.61  cnf(c_0_77, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_74, c_0_75]), c_0_76])]), ['proof']).
% 2.45/2.61  # SZS output end CNFRefutation
% 2.45/2.61  # Proof object total steps             : 78
% 2.45/2.61  # Proof object clause steps            : 50
% 2.45/2.61  # Proof object formula steps           : 28
% 2.45/2.61  # Proof object conjectures             : 23
% 2.45/2.61  # Proof object clause conjectures      : 20
% 2.45/2.61  # Proof object formula conjectures     : 3
% 2.45/2.61  # Proof object initial clauses used    : 23
% 2.45/2.61  # Proof object initial formulas used   : 14
% 2.45/2.61  # Proof object generating inferences   : 14
% 2.45/2.61  # Proof object simplifying inferences  : 36
% 2.45/2.61  # Training examples: 0 positive, 0 negative
% 2.45/2.61  # Parsed axioms                        : 15
% 2.45/2.61  # Removed by relevancy pruning/SinE    : 0
% 2.45/2.61  # Initial clauses                      : 31
% 2.45/2.61  # Removed in clause preprocessing      : 2
% 2.45/2.61  # Initial clauses in saturation        : 29
% 2.45/2.61  # Processed clauses                    : 6727
% 2.45/2.61  # ...of these trivial                  : 49
% 2.45/2.61  # ...subsumed                          : 5598
% 2.45/2.61  # ...remaining for further processing  : 1080
% 2.45/2.61  # Other redundant clauses eliminated   : 0
% 2.45/2.61  # Clauses deleted for lack of memory   : 0
% 2.45/2.61  # Backward-subsumed                    : 55
% 2.45/2.61  # Backward-rewritten                   : 1
% 2.45/2.61  # Generated clauses                    : 218100
% 2.45/2.61  # ...of the previous two non-trivial   : 214813
% 2.45/2.61  # Contextual simplify-reflections      : 0
% 2.45/2.61  # Paramodulations                      : 217781
% 2.45/2.61  # Factorizations                       : 8
% 2.45/2.61  # Equation resolutions                 : 311
% 2.45/2.61  # Propositional unsat checks           : 0
% 2.45/2.61  #    Propositional check models        : 0
% 2.45/2.61  #    Propositional check unsatisfiable : 0
% 2.45/2.61  #    Propositional clauses             : 0
% 2.45/2.61  #    Propositional clauses after purity: 0
% 2.45/2.61  #    Propositional unsat core size     : 0
% 2.45/2.61  #    Propositional preprocessing time  : 0.000
% 2.45/2.61  #    Propositional encoding time       : 0.000
% 2.45/2.61  #    Propositional solver time         : 0.000
% 2.45/2.61  #    Success case prop preproc time    : 0.000
% 2.45/2.61  #    Success case prop encoding time   : 0.000
% 2.45/2.61  #    Success case prop solver time     : 0.000
% 2.45/2.61  # Current number of processed clauses  : 1024
% 2.45/2.61  #    Positive orientable unit clauses  : 11
% 2.45/2.61  #    Positive unorientable unit clauses: 0
% 2.45/2.61  #    Negative unit clauses             : 16
% 2.45/2.61  #    Non-unit-clauses                  : 997
% 2.45/2.61  # Current number of unprocessed clauses: 207906
% 2.45/2.61  # ...number of literals in the above   : 1280465
% 2.45/2.61  # Current number of archived formulas  : 0
% 2.45/2.61  # Current number of archived clauses   : 58
% 2.45/2.61  # Clause-clause subsumption calls (NU) : 188755
% 2.45/2.61  # Rec. Clause-clause subsumption calls : 69865
% 2.45/2.61  # Non-unit clause-clause subsumptions  : 4869
% 2.45/2.61  # Unit Clause-clause subsumption calls : 518
% 2.45/2.61  # Rewrite failures with RHS unbound    : 0
% 2.45/2.61  # BW rewrite match attempts            : 2
% 2.45/2.61  # BW rewrite match successes           : 1
% 2.45/2.61  # Condensation attempts                : 0
% 2.45/2.61  # Condensation successes               : 0
% 2.45/2.61  # Termbank termtop insertions          : 2485415
% 2.45/2.62  
% 2.45/2.62  # -------------------------------------------------
% 2.45/2.62  # User time                : 2.200 s
% 2.45/2.62  # System time              : 0.073 s
% 2.45/2.62  # Total time               : 2.273 s
% 2.45/2.62  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
