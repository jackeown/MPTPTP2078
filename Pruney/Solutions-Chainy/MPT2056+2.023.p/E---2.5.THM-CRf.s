%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:54 EST 2020

% Result     : Theorem 0.41s
% Output     : CNFRefutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 246 expanded)
%              Number of clauses        :   54 ( 105 expanded)
%              Number of leaves         :   18 (  64 expanded)
%              Depth                    :   11
%              Number of atoms          :  244 ( 714 expanded)
%              Number of equality atoms :   54 ( 202 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

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

fof(d2_yellow_1,axiom,(
    ! [X1] : k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).

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

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

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

fof(l24_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_xboole_0(k1_tarski(X1),X2)
        & r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

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

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(fc5_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(k2_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_18,plain,(
    ! [X16,X17] :
      ( ( k4_xboole_0(X16,X17) != k1_xboole_0
        | r1_tarski(X16,X17) )
      & ( ~ r1_tarski(X16,X17)
        | k4_xboole_0(X16,X17) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_19,plain,(
    ! [X18,X19] : k4_xboole_0(X18,X19) = k5_xboole_0(X18,k3_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_20,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(X14,X15)
        | X14 != X15 )
      & ( r1_tarski(X15,X14)
        | X14 != X15 )
      & ( ~ r1_tarski(X14,X15)
        | ~ r1_tarski(X15,X14)
        | X14 = X15 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_21,plain,(
    ! [X38,X39,X40] :
      ( v1_xboole_0(X38)
      | v1_xboole_0(X39)
      | ~ v1_subset_1(X39,u1_struct_0(k3_yellow_1(X38)))
      | ~ v2_waybel_0(X39,k3_yellow_1(X38))
      | ~ v13_waybel_0(X39,k3_yellow_1(X38))
      | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X38))))
      | ~ r2_hidden(X40,X39)
      | ~ v1_xboole_0(X40) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t2_yellow19])])])])).

fof(c_0_22,plain,(
    ! [X35] : k3_yellow_1(X35) = k3_lattice3(k1_lattice3(X35)) ),
    inference(variable_rename,[status(thm)],[d2_yellow_1])).

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

fof(c_0_24,plain,(
    ! [X21,X22] : k4_xboole_0(X21,k4_xboole_0(X21,X22)) = k3_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_28,plain,(
    ! [X20] : k4_xboole_0(X20,k1_xboole_0) = X20 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_29,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
    | ~ v2_waybel_0(X2,k3_yellow_1(X1))
    | ~ v13_waybel_0(X2,k3_yellow_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ r2_hidden(X3,X2)
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_31,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_32,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & l1_struct_0(esk3_0)
    & ~ v1_xboole_0(esk4_0)
    & v1_subset_1(esk4_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0))))
    & v2_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0)))
    & v13_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0)))
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0)))))
    & esk4_0 != k2_yellow19(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_23])])])])).

fof(c_0_33,plain,(
    ! [X28,X29,X30] :
      ( ( r2_hidden(X28,X29)
        | ~ r2_hidden(X28,k4_xboole_0(X29,k1_tarski(X30))) )
      & ( X28 != X30
        | ~ r2_hidden(X28,k4_xboole_0(X29,k1_tarski(X30))) )
      & ( ~ r2_hidden(X28,X29)
        | X28 = X30
        | r2_hidden(X28,k4_xboole_0(X29,k1_tarski(X30))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ v1_xboole_0(X3)
    | ~ r2_hidden(X3,X2)
    | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
    | ~ v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30]),c_0_30]),c_0_30]),c_0_30])).

cnf(c_0_39,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( v13_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( v1_subset_1(esk4_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( v2_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( X1 = X3
    | r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_45,plain,(
    ! [X8,X9,X11,X12,X13] :
      ( ( r2_hidden(esk2_2(X8,X9),X8)
        | r1_xboole_0(X8,X9) )
      & ( r2_hidden(esk2_2(X8,X9),X9)
        | r1_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X13,X11)
        | ~ r2_hidden(X13,X12)
        | ~ r1_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_46,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_26]),c_0_26])).

cnf(c_0_47,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_48,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_37,c_0_26])).

fof(c_0_49,plain,(
    ! [X26,X27] :
      ( ~ r1_xboole_0(k1_tarski(X26),X27)
      | ~ r2_hidden(X26,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).

fof(c_0_50,plain,(
    ! [X23] : r1_xboole_0(X23,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_51,plain,(
    ! [X31,X32,X33] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(X31))
      | k7_subset_1(X31,X32,X33) = k4_xboole_0(X32,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_52,plain,
    ( v1_xboole_0(X1)
    | ~ v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
    | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ r2_hidden(X3,X2)
    | ~ v1_xboole_0(X3) ),
    inference(csr,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_53,negated_conjecture,
    ( v13_waybel_0(esk4_0,k3_lattice3(k1_lattice3(k2_struct_0(esk3_0)))) ),
    inference(rw,[status(thm)],[c_0_40,c_0_30])).

cnf(c_0_54,negated_conjecture,
    ( v1_subset_1(esk4_0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk3_0))))) ),
    inference(rw,[status(thm)],[c_0_41,c_0_30])).

cnf(c_0_55,negated_conjecture,
    ( v2_waybel_0(esk4_0,k3_lattice3(k1_lattice3(k2_struct_0(esk3_0)))) ),
    inference(rw,[status(thm)],[c_0_42,c_0_30])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk3_0)))))) ),
    inference(rw,[status(thm)],[c_0_43,c_0_30])).

cnf(c_0_57,plain,
    ( X1 = X3
    | r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k1_tarski(X3))))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_44,c_0_26])).

cnf(c_0_58,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_59,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])).

cnf(c_0_60,plain,
    ( ~ r1_xboole_0(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_61,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_62,plain,(
    ! [X36,X37] :
      ( v2_struct_0(X36)
      | ~ l1_struct_0(X36)
      | v1_xboole_0(X37)
      | ~ v2_waybel_0(X37,k3_yellow_1(k2_struct_0(X36)))
      | ~ v13_waybel_0(X37,k3_yellow_1(k2_struct_0(X36)))
      | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X36)))))
      | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X36))),X37,k1_tarski(k1_xboole_0)) = k2_yellow19(X36,k3_yellow19(X36,k2_struct_0(X36),X37)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow19])])])])).

cnf(c_0_63,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_64,plain,(
    ! [X24,X25] :
      ( ( ~ r1_xboole_0(X24,X25)
        | k4_xboole_0(X24,X25) = X24 )
      & ( k4_xboole_0(X24,X25) != X24
        | r1_xboole_0(X24,X25) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_65,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk4_0)
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_55]),c_0_56])])).

cnf(c_0_66,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_67,plain,
    ( esk2_2(X1,X2) = X3
    | r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k5_xboole_0(X2,k3_xboole_0(X2,k1_tarski(X3)))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_68,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_47,c_0_59])).

cnf(c_0_69,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_70,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))),X2,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | ~ l1_struct_0(X1)
    | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_71,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k3_xboole_0(X1,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_63,c_0_26])).

cnf(c_0_72,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_73,negated_conjecture,
    ( r1_xboole_0(esk4_0,X1)
    | v1_xboole_0(k2_struct_0(esk3_0))
    | ~ v1_xboole_0(esk2_2(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_74,plain,
    ( esk2_2(X1,k1_tarski(X2)) = X2
    | r1_xboole_0(X1,k1_tarski(X2)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_59]),c_0_68]),c_0_69])).

cnf(c_0_75,plain,
    ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X2,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_30]),c_0_30]),c_0_30]),c_0_30])).

cnf(c_0_76,negated_conjecture,
    ( l1_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_77,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_78,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_79,negated_conjecture,
    ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk3_0)))),esk4_0,X1) = k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_56])).

cnf(c_0_80,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_72,c_0_26])).

cnf(c_0_81,negated_conjecture,
    ( r1_xboole_0(esk4_0,k1_tarski(X1))
    | v1_xboole_0(k2_struct_0(esk3_0))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

fof(c_0_82,plain,(
    ! [X34] :
      ( v2_struct_0(X34)
      | ~ l1_struct_0(X34)
      | ~ v1_xboole_0(k2_struct_0(X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_struct_0])])])).

cnf(c_0_83,negated_conjecture,
    ( k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k1_tarski(k1_xboole_0))) = k2_yellow19(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0)) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_53]),c_0_55]),c_0_76]),c_0_56])]),c_0_77]),c_0_78]),c_0_79])).

cnf(c_0_84,negated_conjecture,
    ( k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k1_tarski(X1))) = esk4_0
    | v1_xboole_0(k2_struct_0(esk3_0))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_85,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_86,negated_conjecture,
    ( esk4_0 != k2_yellow19(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_87,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(k2_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_88,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85])]),c_0_86])).

cnf(c_0_89,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_76])]),c_0_77]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:07:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.41/0.60  # AutoSched0-Mode selected heuristic G_E___110_C45_F1_PI_SE_CS_SP_PS_S4S
% 0.41/0.60  # and selection function SelectNewComplexAHPNS.
% 0.41/0.60  #
% 0.41/0.60  # Preprocessing time       : 0.028 s
% 0.41/0.60  # Presaturation interreduction done
% 0.41/0.60  
% 0.41/0.60  # Proof found!
% 0.41/0.60  # SZS status Theorem
% 0.41/0.60  # SZS output start CNFRefutation
% 0.41/0.60  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.41/0.60  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.41/0.60  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.41/0.60  fof(t2_yellow19, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))))&v2_waybel_0(X2,k3_yellow_1(X1)))&v13_waybel_0(X2,k3_yellow_1(X1)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))))=>![X3]:~((r2_hidden(X3,X2)&v1_xboole_0(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_yellow19)).
% 0.41/0.60  fof(d2_yellow_1, axiom, ![X1]:k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_yellow_1)).
% 0.41/0.60  fof(t15_yellow19, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 0.41/0.60  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.41/0.60  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.41/0.60  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.41/0.60  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 0.41/0.60  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.41/0.60  fof(l24_zfmisc_1, axiom, ![X1, X2]:~((r1_xboole_0(k1_tarski(X1),X2)&r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 0.41/0.60  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.41/0.60  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.41/0.60  fof(t14_yellow19, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))),X2,k1_tarski(k1_xboole_0))=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow19)).
% 0.41/0.60  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.41/0.60  fof(fc5_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(k2_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 0.41/0.60  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.41/0.60  fof(c_0_18, plain, ![X16, X17]:((k4_xboole_0(X16,X17)!=k1_xboole_0|r1_tarski(X16,X17))&(~r1_tarski(X16,X17)|k4_xboole_0(X16,X17)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.41/0.60  fof(c_0_19, plain, ![X18, X19]:k4_xboole_0(X18,X19)=k5_xboole_0(X18,k3_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.41/0.60  fof(c_0_20, plain, ![X14, X15]:(((r1_tarski(X14,X15)|X14!=X15)&(r1_tarski(X15,X14)|X14!=X15))&(~r1_tarski(X14,X15)|~r1_tarski(X15,X14)|X14=X15)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.41/0.60  fof(c_0_21, plain, ![X38, X39, X40]:(v1_xboole_0(X38)|(v1_xboole_0(X39)|~v1_subset_1(X39,u1_struct_0(k3_yellow_1(X38)))|~v2_waybel_0(X39,k3_yellow_1(X38))|~v13_waybel_0(X39,k3_yellow_1(X38))|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X38))))|(~r2_hidden(X40,X39)|~v1_xboole_0(X40)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t2_yellow19])])])])).
% 0.41/0.60  fof(c_0_22, plain, ![X35]:k3_yellow_1(X35)=k3_lattice3(k1_lattice3(X35)), inference(variable_rename,[status(thm)],[d2_yellow_1])).
% 0.41/0.60  fof(c_0_23, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))))), inference(assume_negation,[status(cth)],[t15_yellow19])).
% 0.41/0.60  fof(c_0_24, plain, ![X21, X22]:k4_xboole_0(X21,k4_xboole_0(X21,X22))=k3_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.41/0.60  cnf(c_0_25, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.41/0.60  cnf(c_0_26, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.41/0.60  cnf(c_0_27, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.41/0.60  fof(c_0_28, plain, ![X20]:k4_xboole_0(X20,k1_xboole_0)=X20, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.41/0.60  cnf(c_0_29, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))|~v2_waybel_0(X2,k3_yellow_1(X1))|~v13_waybel_0(X2,k3_yellow_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))|~r2_hidden(X3,X2)|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.41/0.60  cnf(c_0_30, plain, (k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.41/0.60  fof(c_0_31, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.41/0.60  fof(c_0_32, negated_conjecture, ((~v2_struct_0(esk3_0)&l1_struct_0(esk3_0))&(((((~v1_xboole_0(esk4_0)&v1_subset_1(esk4_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0)))))&v2_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0))))&v13_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0))))&m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0))))))&esk4_0!=k2_yellow19(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_23])])])])).
% 0.41/0.60  fof(c_0_33, plain, ![X28, X29, X30]:(((r2_hidden(X28,X29)|~r2_hidden(X28,k4_xboole_0(X29,k1_tarski(X30))))&(X28!=X30|~r2_hidden(X28,k4_xboole_0(X29,k1_tarski(X30)))))&(~r2_hidden(X28,X29)|X28=X30|r2_hidden(X28,k4_xboole_0(X29,k1_tarski(X30))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 0.41/0.60  cnf(c_0_34, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.41/0.60  cnf(c_0_35, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.41/0.60  cnf(c_0_36, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_27])).
% 0.41/0.60  cnf(c_0_37, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.41/0.60  cnf(c_0_38, plain, (v1_xboole_0(X2)|v1_xboole_0(X1)|~v1_xboole_0(X3)|~r2_hidden(X3,X2)|~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))|~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))|~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30]), c_0_30]), c_0_30]), c_0_30])).
% 0.41/0.60  cnf(c_0_39, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.41/0.60  cnf(c_0_40, negated_conjecture, (v13_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.41/0.60  cnf(c_0_41, negated_conjecture, (v1_subset_1(esk4_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.41/0.60  cnf(c_0_42, negated_conjecture, (v2_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.41/0.60  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0)))))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.41/0.60  cnf(c_0_44, plain, (X1=X3|r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.41/0.60  fof(c_0_45, plain, ![X8, X9, X11, X12, X13]:(((r2_hidden(esk2_2(X8,X9),X8)|r1_xboole_0(X8,X9))&(r2_hidden(esk2_2(X8,X9),X9)|r1_xboole_0(X8,X9)))&(~r2_hidden(X13,X11)|~r2_hidden(X13,X12)|~r1_xboole_0(X11,X12))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.41/0.60  cnf(c_0_46, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_26]), c_0_26])).
% 0.41/0.60  cnf(c_0_47, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.41/0.60  cnf(c_0_48, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_37, c_0_26])).
% 0.41/0.60  fof(c_0_49, plain, ![X26, X27]:(~r1_xboole_0(k1_tarski(X26),X27)|~r2_hidden(X26,X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).
% 0.41/0.60  fof(c_0_50, plain, ![X23]:r1_xboole_0(X23,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.41/0.60  fof(c_0_51, plain, ![X31, X32, X33]:(~m1_subset_1(X32,k1_zfmisc_1(X31))|k7_subset_1(X31,X32,X33)=k4_xboole_0(X32,X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.41/0.60  cnf(c_0_52, plain, (v1_xboole_0(X1)|~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))|~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))|~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))|~r2_hidden(X3,X2)|~v1_xboole_0(X3)), inference(csr,[status(thm)],[c_0_38, c_0_39])).
% 0.41/0.60  cnf(c_0_53, negated_conjecture, (v13_waybel_0(esk4_0,k3_lattice3(k1_lattice3(k2_struct_0(esk3_0))))), inference(rw,[status(thm)],[c_0_40, c_0_30])).
% 0.41/0.60  cnf(c_0_54, negated_conjecture, (v1_subset_1(esk4_0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk3_0)))))), inference(rw,[status(thm)],[c_0_41, c_0_30])).
% 0.41/0.60  cnf(c_0_55, negated_conjecture, (v2_waybel_0(esk4_0,k3_lattice3(k1_lattice3(k2_struct_0(esk3_0))))), inference(rw,[status(thm)],[c_0_42, c_0_30])).
% 0.41/0.60  cnf(c_0_56, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk3_0))))))), inference(rw,[status(thm)],[c_0_43, c_0_30])).
% 0.41/0.60  cnf(c_0_57, plain, (X1=X3|r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k1_tarski(X3))))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_44, c_0_26])).
% 0.41/0.60  cnf(c_0_58, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.41/0.60  cnf(c_0_59, plain, (k3_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])).
% 0.41/0.60  cnf(c_0_60, plain, (~r1_xboole_0(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.41/0.60  cnf(c_0_61, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.41/0.60  fof(c_0_62, plain, ![X36, X37]:(v2_struct_0(X36)|~l1_struct_0(X36)|(v1_xboole_0(X37)|~v2_waybel_0(X37,k3_yellow_1(k2_struct_0(X36)))|~v13_waybel_0(X37,k3_yellow_1(k2_struct_0(X36)))|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X36)))))|k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X36))),X37,k1_tarski(k1_xboole_0))=k2_yellow19(X36,k3_yellow19(X36,k2_struct_0(X36),X37)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow19])])])])).
% 0.41/0.60  cnf(c_0_63, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.41/0.60  fof(c_0_64, plain, ![X24, X25]:((~r1_xboole_0(X24,X25)|k4_xboole_0(X24,X25)=X24)&(k4_xboole_0(X24,X25)!=X24|r1_xboole_0(X24,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.41/0.60  cnf(c_0_65, negated_conjecture, (v1_xboole_0(k2_struct_0(esk3_0))|~r2_hidden(X1,esk4_0)|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), c_0_55]), c_0_56])])).
% 0.41/0.60  cnf(c_0_66, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.41/0.60  cnf(c_0_67, plain, (esk2_2(X1,X2)=X3|r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k5_xboole_0(X2,k3_xboole_0(X2,k1_tarski(X3))))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.41/0.60  cnf(c_0_68, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_47, c_0_59])).
% 0.41/0.60  cnf(c_0_69, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.41/0.60  cnf(c_0_70, plain, (v2_struct_0(X1)|v1_xboole_0(X2)|k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))),X2,k1_tarski(k1_xboole_0))=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))|~l1_struct_0(X1)|~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))|~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.41/0.60  cnf(c_0_71, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k3_xboole_0(X1,X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_63, c_0_26])).
% 0.41/0.60  cnf(c_0_72, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.41/0.60  cnf(c_0_73, negated_conjecture, (r1_xboole_0(esk4_0,X1)|v1_xboole_0(k2_struct_0(esk3_0))|~v1_xboole_0(esk2_2(esk4_0,X1))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.41/0.60  cnf(c_0_74, plain, (esk2_2(X1,k1_tarski(X2))=X2|r1_xboole_0(X1,k1_tarski(X2))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_59]), c_0_68]), c_0_69])).
% 0.41/0.60  cnf(c_0_75, plain, (k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X2,k1_tarski(k1_xboole_0))=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))|v1_xboole_0(X2)|v2_struct_0(X1)|~l1_struct_0(X1)|~v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_30]), c_0_30]), c_0_30]), c_0_30])).
% 0.41/0.60  cnf(c_0_76, negated_conjecture, (l1_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.41/0.60  cnf(c_0_77, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.41/0.60  cnf(c_0_78, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.41/0.60  cnf(c_0_79, negated_conjecture, (k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk3_0)))),esk4_0,X1)=k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,X1))), inference(spm,[status(thm)],[c_0_71, c_0_56])).
% 0.41/0.60  cnf(c_0_80, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_72, c_0_26])).
% 0.41/0.60  cnf(c_0_81, negated_conjecture, (r1_xboole_0(esk4_0,k1_tarski(X1))|v1_xboole_0(k2_struct_0(esk3_0))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.41/0.60  fof(c_0_82, plain, ![X34]:(v2_struct_0(X34)|~l1_struct_0(X34)|~v1_xboole_0(k2_struct_0(X34))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_struct_0])])])).
% 0.41/0.60  cnf(c_0_83, negated_conjecture, (k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k1_tarski(k1_xboole_0)))=k2_yellow19(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_53]), c_0_55]), c_0_76]), c_0_56])]), c_0_77]), c_0_78]), c_0_79])).
% 0.41/0.60  cnf(c_0_84, negated_conjecture, (k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k1_tarski(X1)))=esk4_0|v1_xboole_0(k2_struct_0(esk3_0))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.41/0.60  cnf(c_0_85, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.41/0.60  cnf(c_0_86, negated_conjecture, (esk4_0!=k2_yellow19(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.41/0.60  cnf(c_0_87, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(k2_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.41/0.60  cnf(c_0_88, negated_conjecture, (v1_xboole_0(k2_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_85])]), c_0_86])).
% 0.41/0.60  cnf(c_0_89, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_76])]), c_0_77]), ['proof']).
% 0.41/0.60  # SZS output end CNFRefutation
% 0.41/0.60  # Proof object total steps             : 90
% 0.41/0.60  # Proof object clause steps            : 54
% 0.41/0.60  # Proof object formula steps           : 36
% 0.41/0.60  # Proof object conjectures             : 23
% 0.41/0.60  # Proof object clause conjectures      : 20
% 0.41/0.60  # Proof object formula conjectures     : 3
% 0.41/0.60  # Proof object initial clauses used    : 26
% 0.41/0.60  # Proof object initial formulas used   : 18
% 0.41/0.60  # Proof object generating inferences   : 13
% 0.41/0.60  # Proof object simplifying inferences  : 42
% 0.41/0.60  # Training examples: 0 positive, 0 negative
% 0.41/0.60  # Parsed axioms                        : 18
% 0.41/0.60  # Removed by relevancy pruning/SinE    : 0
% 0.41/0.60  # Initial clauses                      : 34
% 0.41/0.60  # Removed in clause preprocessing      : 2
% 0.41/0.60  # Initial clauses in saturation        : 32
% 0.41/0.60  # Processed clauses                    : 3058
% 0.41/0.60  # ...of these trivial                  : 9
% 0.41/0.60  # ...subsumed                          : 2560
% 0.41/0.60  # ...remaining for further processing  : 489
% 0.41/0.60  # Other redundant clauses eliminated   : 186
% 0.41/0.60  # Clauses deleted for lack of memory   : 0
% 0.41/0.60  # Backward-subsumed                    : 41
% 0.41/0.60  # Backward-rewritten                   : 19
% 0.41/0.60  # Generated clauses                    : 15691
% 0.41/0.60  # ...of the previous two non-trivial   : 13900
% 0.41/0.60  # Contextual simplify-reflections      : 3
% 0.41/0.60  # Paramodulations                      : 15505
% 0.41/0.60  # Factorizations                       : 0
% 0.41/0.60  # Equation resolutions                 : 186
% 0.41/0.60  # Propositional unsat checks           : 0
% 0.41/0.60  #    Propositional check models        : 0
% 0.41/0.60  #    Propositional check unsatisfiable : 0
% 0.41/0.60  #    Propositional clauses             : 0
% 0.41/0.60  #    Propositional clauses after purity: 0
% 0.41/0.60  #    Propositional unsat core size     : 0
% 0.41/0.60  #    Propositional preprocessing time  : 0.000
% 0.41/0.60  #    Propositional encoding time       : 0.000
% 0.41/0.60  #    Propositional solver time         : 0.000
% 0.41/0.60  #    Success case prop preproc time    : 0.000
% 0.41/0.60  #    Success case prop encoding time   : 0.000
% 0.41/0.60  #    Success case prop solver time     : 0.000
% 0.41/0.60  # Current number of processed clauses  : 393
% 0.41/0.60  #    Positive orientable unit clauses  : 22
% 0.41/0.60  #    Positive unorientable unit clauses: 0
% 0.41/0.60  #    Negative unit clauses             : 8
% 0.41/0.60  #    Non-unit-clauses                  : 363
% 0.41/0.60  # Current number of unprocessed clauses: 10716
% 0.41/0.60  # ...number of literals in the above   : 50906
% 0.41/0.60  # Current number of archived formulas  : 0
% 0.41/0.60  # Current number of archived clauses   : 93
% 0.41/0.60  # Clause-clause subsumption calls (NU) : 78236
% 0.41/0.60  # Rec. Clause-clause subsumption calls : 31341
% 0.41/0.60  # Non-unit clause-clause subsumptions  : 2198
% 0.41/0.60  # Unit Clause-clause subsumption calls : 172
% 0.41/0.60  # Rewrite failures with RHS unbound    : 0
% 0.41/0.60  # BW rewrite match attempts            : 28
% 0.41/0.60  # BW rewrite match successes           : 5
% 0.41/0.60  # Condensation attempts                : 0
% 0.41/0.60  # Condensation successes               : 0
% 0.41/0.60  # Termbank termtop insertions          : 246039
% 0.41/0.60  
% 0.41/0.60  # -------------------------------------------------
% 0.41/0.60  # User time                : 0.248 s
% 0.41/0.60  # System time              : 0.009 s
% 0.41/0.60  # Total time               : 0.257 s
% 0.41/0.60  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
