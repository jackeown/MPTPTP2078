%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:52 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 650 expanded)
%              Number of clauses        :   77 ( 293 expanded)
%              Number of leaves         :   19 ( 171 expanded)
%              Depth                    :   16
%              Number of atoms          :  302 (1276 expanded)
%              Number of equality atoms :   77 ( 591 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

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

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

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

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

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

fof(c_0_19,plain,(
    ! [X42] : k4_xboole_0(k1_xboole_0,X42) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

fof(c_0_20,plain,(
    ! [X36,X37] : k4_xboole_0(X36,X37) = k5_xboole_0(X36,k3_xboole_0(X36,X37)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_21,plain,(
    ! [X40,X41] : k4_xboole_0(X40,k4_xboole_0(X40,X41)) = k3_xboole_0(X40,X41) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_22,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_25,plain,(
    ! [X39] : k4_xboole_0(X39,k1_xboole_0) = X39 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_26,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_27,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_23]),c_0_23])).

fof(c_0_29,negated_conjecture,(
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

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_33,plain,(
    ! [X49] :
      ( ~ l1_struct_0(X49)
      | k2_struct_0(X49) = u1_struct_0(X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_34,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & l1_struct_0(esk5_0)
    & ~ v1_xboole_0(esk6_0)
    & v1_subset_1(esk6_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0))))
    & v2_waybel_0(esk6_0,k3_yellow_1(k2_struct_0(esk5_0)))
    & v13_waybel_0(esk6_0,k3_yellow_1(k2_struct_0(esk5_0)))
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0)))))
    & esk6_0 != k2_yellow19(esk5_0,k3_yellow19(esk5_0,k2_struct_0(esk5_0),esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_29])])])])).

cnf(c_0_35,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_30,c_0_23])).

cnf(c_0_36,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_37,plain,(
    ! [X43,X44,X45] :
      ( ( r2_hidden(X43,X44)
        | ~ r2_hidden(X43,k4_xboole_0(X44,k1_tarski(X45))) )
      & ( X43 != X45
        | ~ r2_hidden(X43,k4_xboole_0(X44,k1_tarski(X45))) )
      & ( ~ r2_hidden(X43,X44)
        | X43 = X45
        | r2_hidden(X43,k4_xboole_0(X44,k1_tarski(X45))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

fof(c_0_38,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( r2_hidden(X16,X13)
        | ~ r2_hidden(X16,X15)
        | X15 != k4_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X16,X14)
        | ~ r2_hidden(X16,X15)
        | X15 != k4_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X17,X13)
        | r2_hidden(X17,X14)
        | r2_hidden(X17,X15)
        | X15 != k4_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X20)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X18)
        | r2_hidden(esk2_3(X18,X19,X20),X19)
        | X20 = k4_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X18)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k4_xboole_0(X18,X19) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X19)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k4_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_39,plain,(
    ! [X54,X55,X56] :
      ( v1_xboole_0(X54)
      | v1_xboole_0(X55)
      | ~ v1_subset_1(X55,u1_struct_0(k3_yellow_1(X54)))
      | ~ v2_waybel_0(X55,k3_yellow_1(X54))
      | ~ v13_waybel_0(X55,k3_yellow_1(X54))
      | ~ m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X54))))
      | ~ r2_hidden(X56,X55)
      | ~ v1_xboole_0(X56) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t2_yellow19])])])])).

fof(c_0_40,plain,(
    ! [X51] : k3_yellow_1(X51) = k3_lattice3(k1_lattice3(X51)) ),
    inference(variable_rename,[status(thm)],[d2_yellow_1])).

fof(c_0_41,plain,(
    ! [X50] :
      ( v2_struct_0(X50)
      | ~ l1_struct_0(X50)
      | ~ v1_xboole_0(u1_struct_0(X50)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_42,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( l1_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_45,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
    | ~ v2_waybel_0(X2,k3_yellow_1(X1))
    | ~ v13_waybel_0(X2,k3_yellow_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ r2_hidden(X3,X2)
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,plain,
    ( k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( v13_waybel_0(esk6_0,k3_yellow_1(k2_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_50,negated_conjecture,
    ( v1_subset_1(esk6_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_51,negated_conjecture,
    ( v2_waybel_0(esk6_0,k3_yellow_1(k2_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_53,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_54,negated_conjecture,
    ( u1_struct_0(esk5_0) = k2_struct_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_55,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_56,plain,
    ( X1 = X3
    | r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_57,plain,(
    ! [X22,X23,X25,X26,X27] :
      ( ( r2_hidden(esk3_2(X22,X23),X22)
        | r1_xboole_0(X22,X23) )
      & ( r2_hidden(esk3_2(X22,X23),X23)
        | r1_xboole_0(X22,X23) )
      & ( ~ r2_hidden(X27,X25)
        | ~ r2_hidden(X27,X26)
        | ~ r1_xboole_0(X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_58,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_36]),c_0_44])).

cnf(c_0_59,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k5_xboole_0(X3,k3_xboole_0(X3,k1_tarski(X2)))) ),
    inference(rw,[status(thm)],[c_0_45,c_0_23])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,X2)
    | X3 != k5_xboole_0(X2,k3_xboole_0(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_46,c_0_23])).

fof(c_0_61,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_62,plain,
    ( v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ v1_xboole_0(X3)
    | ~ r2_hidden(X3,X2)
    | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
    | ~ v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48]),c_0_48]),c_0_48]),c_0_48])).

cnf(c_0_63,negated_conjecture,
    ( v13_waybel_0(esk6_0,k3_lattice3(k1_lattice3(k2_struct_0(esk5_0)))) ),
    inference(rw,[status(thm)],[c_0_49,c_0_48])).

cnf(c_0_64,negated_conjecture,
    ( v1_subset_1(esk6_0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk5_0))))) ),
    inference(rw,[status(thm)],[c_0_50,c_0_48])).

cnf(c_0_65,negated_conjecture,
    ( v2_waybel_0(esk6_0,k3_lattice3(k1_lattice3(k2_struct_0(esk5_0)))) ),
    inference(rw,[status(thm)],[c_0_51,c_0_48])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk5_0)))))) ),
    inference(rw,[status(thm)],[c_0_52,c_0_48])).

cnf(c_0_67,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_68,negated_conjecture,
    ( ~ v1_xboole_0(k2_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_43])]),c_0_55])).

cnf(c_0_69,plain,
    ( X1 = X3
    | r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k1_tarski(X3))))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_56,c_0_23])).

cnf(c_0_70,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_71,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_58]),c_0_36]),c_0_44])).

cnf(c_0_72,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k1_tarski(X1)))) ),
    inference(er,[status(thm)],[c_0_59])).

cnf(c_0_73,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(er,[status(thm)],[c_0_60])).

cnf(c_0_74,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

fof(c_0_75,plain,(
    ! [X28,X29,X31,X32,X33] :
      ( ( r1_xboole_0(X28,X29)
        | r2_hidden(esk4_2(X28,X29),k3_xboole_0(X28,X29)) )
      & ( ~ r2_hidden(X33,k3_xboole_0(X31,X32))
        | ~ r1_xboole_0(X31,X32) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_76,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_77,negated_conjecture,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64]),c_0_65]),c_0_66])]),c_0_67]),c_0_68])).

cnf(c_0_78,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_79,plain,
    ( esk3_2(X1,X2) = X3
    | r1_xboole_0(X1,X2)
    | r2_hidden(esk3_2(X1,X2),k5_xboole_0(X2,k3_xboole_0(X2,k1_tarski(X3)))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_80,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_58,c_0_71])).

cnf(c_0_81,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_27])).

cnf(c_0_82,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_83,plain,
    ( r2_hidden(esk1_2(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3),X1)
    | r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_84,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_85,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_76,c_0_23])).

cnf(c_0_86,negated_conjecture,
    ( r1_xboole_0(esk6_0,X1)
    | ~ v1_xboole_0(esk3_2(esk6_0,X1)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_87,plain,
    ( esk3_2(X1,k1_tarski(X2)) = X2
    | r1_xboole_0(X1,k1_tarski(X2)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_71]),c_0_80]),c_0_81])).

cnf(c_0_88,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_89,plain,
    ( ~ r1_xboole_0(X1,X2)
    | ~ r2_hidden(X3,k3_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_31])).

cnf(c_0_90,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_3(k1_xboole_0,X2,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_85]),c_0_27])).

cnf(c_0_91,plain,
    ( r1_xboole_0(k3_xboole_0(X1,X2),X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_84,c_0_78])).

cnf(c_0_92,negated_conjecture,
    ( r1_xboole_0(esk6_0,k1_tarski(X1))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

fof(c_0_93,plain,(
    ! [X46,X47,X48] :
      ( ~ m1_subset_1(X47,k1_zfmisc_1(X46))
      | k7_subset_1(X46,X47,X48) = k4_xboole_0(X47,X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_94,plain,(
    ! [X34,X35] :
      ( ( r1_tarski(X34,X35)
        | X34 != X35 )
      & ( r1_tarski(X35,X34)
        | X34 != X35 )
      & ( ~ r1_tarski(X34,X35)
        | ~ r1_tarski(X35,X34)
        | X34 = X35 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_95,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_88,c_0_28])).

cnf(c_0_96,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_97,negated_conjecture,
    ( r1_xboole_0(k3_xboole_0(esk6_0,k1_tarski(X1)),X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

fof(c_0_98,plain,(
    ! [X52,X53] :
      ( v2_struct_0(X52)
      | ~ l1_struct_0(X52)
      | v1_xboole_0(X53)
      | ~ v2_waybel_0(X53,k3_yellow_1(k2_struct_0(X52)))
      | ~ v13_waybel_0(X53,k3_yellow_1(k2_struct_0(X52)))
      | ~ m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X52)))))
      | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X52))),X53,k1_tarski(k1_xboole_0)) = k2_yellow19(X52,k3_yellow19(X52,k2_struct_0(X52),X53)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow19])])])])).

cnf(c_0_99,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_100,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_101,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_95,c_0_31])).

cnf(c_0_102,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2))) = k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_28])).

cnf(c_0_103,negated_conjecture,
    ( k3_xboole_0(X1,k3_xboole_0(esk6_0,k1_tarski(X2))) = k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_104,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))),X2,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | ~ l1_struct_0(X1)
    | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_105,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k3_xboole_0(X1,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_99,c_0_23])).

cnf(c_0_106,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_107,negated_conjecture,
    ( k3_xboole_0(esk6_0,k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,k1_tarski(X1)))) = esk6_0
    | ~ v1_xboole_0(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_44])).

cnf(c_0_108,plain,
    ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X2,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_104,c_0_48]),c_0_48]),c_0_48]),c_0_48])).

cnf(c_0_109,negated_conjecture,
    ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk5_0)))),esk6_0,X1) = k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,X1)) ),
    inference(spm,[status(thm)],[c_0_105,c_0_66])).

cnf(c_0_110,negated_conjecture,
    ( k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,k1_tarski(X1))) = esk6_0
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_88])])).

cnf(c_0_111,negated_conjecture,
    ( k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,k1_tarski(k1_xboole_0))) = k2_yellow19(esk5_0,k3_yellow19(esk5_0,k2_struct_0(esk5_0),esk6_0)) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_63]),c_0_65]),c_0_43]),c_0_66])]),c_0_55]),c_0_67]),c_0_109])).

cnf(c_0_112,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_113,negated_conjecture,
    ( esk6_0 != k2_yellow19(esk5_0,k3_yellow19(esk5_0,k2_struct_0(esk5_0),esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_114,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_112])]),c_0_113]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:01:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.50  # AutoSched0-Mode selected heuristic G_E___110_C45_F1_PI_SE_CS_SP_PS_S4S
% 0.19/0.50  # and selection function SelectNewComplexAHPNS.
% 0.19/0.50  #
% 0.19/0.50  # Preprocessing time       : 0.028 s
% 0.19/0.50  # Presaturation interreduction done
% 0.19/0.50  
% 0.19/0.50  # Proof found!
% 0.19/0.50  # SZS status Theorem
% 0.19/0.50  # SZS output start CNFRefutation
% 0.19/0.50  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 0.19/0.50  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.50  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.19/0.50  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.19/0.50  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.50  fof(t15_yellow19, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 0.19/0.50  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.19/0.50  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 0.19/0.50  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.19/0.50  fof(t2_yellow19, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))))&v2_waybel_0(X2,k3_yellow_1(X1)))&v13_waybel_0(X2,k3_yellow_1(X1)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))))=>![X3]:~((r2_hidden(X3,X2)&v1_xboole_0(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_yellow19)).
% 0.19/0.50  fof(d2_yellow_1, axiom, ![X1]:k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_yellow_1)).
% 0.19/0.50  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.19/0.50  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.19/0.50  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.50  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.19/0.50  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.19/0.50  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.50  fof(t14_yellow19, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))),X2,k1_tarski(k1_xboole_0))=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow19)).
% 0.19/0.50  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.50  fof(c_0_19, plain, ![X42]:k4_xboole_0(k1_xboole_0,X42)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.19/0.50  fof(c_0_20, plain, ![X36, X37]:k4_xboole_0(X36,X37)=k5_xboole_0(X36,k3_xboole_0(X36,X37)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.50  fof(c_0_21, plain, ![X40, X41]:k4_xboole_0(X40,k4_xboole_0(X40,X41))=k3_xboole_0(X40,X41), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.19/0.50  cnf(c_0_22, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.50  cnf(c_0_23, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.50  cnf(c_0_24, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.50  fof(c_0_25, plain, ![X39]:k4_xboole_0(X39,k1_xboole_0)=X39, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.19/0.50  fof(c_0_26, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.50  cnf(c_0_27, plain, (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.50  cnf(c_0_28, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_23]), c_0_23])).
% 0.19/0.50  fof(c_0_29, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))))), inference(assume_negation,[status(cth)],[t15_yellow19])).
% 0.19/0.50  cnf(c_0_30, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.50  cnf(c_0_31, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.50  cnf(c_0_32, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.50  fof(c_0_33, plain, ![X49]:(~l1_struct_0(X49)|k2_struct_0(X49)=u1_struct_0(X49)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.19/0.50  fof(c_0_34, negated_conjecture, ((~v2_struct_0(esk5_0)&l1_struct_0(esk5_0))&(((((~v1_xboole_0(esk6_0)&v1_subset_1(esk6_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0)))))&v2_waybel_0(esk6_0,k3_yellow_1(k2_struct_0(esk5_0))))&v13_waybel_0(esk6_0,k3_yellow_1(k2_struct_0(esk5_0))))&m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0))))))&esk6_0!=k2_yellow19(esk5_0,k3_yellow19(esk5_0,k2_struct_0(esk5_0),esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_29])])])])).
% 0.19/0.50  cnf(c_0_35, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_30, c_0_23])).
% 0.19/0.50  cnf(c_0_36, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.50  fof(c_0_37, plain, ![X43, X44, X45]:(((r2_hidden(X43,X44)|~r2_hidden(X43,k4_xboole_0(X44,k1_tarski(X45))))&(X43!=X45|~r2_hidden(X43,k4_xboole_0(X44,k1_tarski(X45)))))&(~r2_hidden(X43,X44)|X43=X45|r2_hidden(X43,k4_xboole_0(X44,k1_tarski(X45))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 0.19/0.50  fof(c_0_38, plain, ![X13, X14, X15, X16, X17, X18, X19, X20]:((((r2_hidden(X16,X13)|~r2_hidden(X16,X15)|X15!=k4_xboole_0(X13,X14))&(~r2_hidden(X16,X14)|~r2_hidden(X16,X15)|X15!=k4_xboole_0(X13,X14)))&(~r2_hidden(X17,X13)|r2_hidden(X17,X14)|r2_hidden(X17,X15)|X15!=k4_xboole_0(X13,X14)))&((~r2_hidden(esk2_3(X18,X19,X20),X20)|(~r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X19))|X20=k4_xboole_0(X18,X19))&((r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k4_xboole_0(X18,X19))&(~r2_hidden(esk2_3(X18,X19,X20),X19)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k4_xboole_0(X18,X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.19/0.50  fof(c_0_39, plain, ![X54, X55, X56]:(v1_xboole_0(X54)|(v1_xboole_0(X55)|~v1_subset_1(X55,u1_struct_0(k3_yellow_1(X54)))|~v2_waybel_0(X55,k3_yellow_1(X54))|~v13_waybel_0(X55,k3_yellow_1(X54))|~m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X54))))|(~r2_hidden(X56,X55)|~v1_xboole_0(X56)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t2_yellow19])])])])).
% 0.19/0.50  fof(c_0_40, plain, ![X51]:k3_yellow_1(X51)=k3_lattice3(k1_lattice3(X51)), inference(variable_rename,[status(thm)],[d2_yellow_1])).
% 0.19/0.50  fof(c_0_41, plain, ![X50]:(v2_struct_0(X50)|~l1_struct_0(X50)|~v1_xboole_0(u1_struct_0(X50))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.19/0.50  cnf(c_0_42, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.50  cnf(c_0_43, negated_conjecture, (l1_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.50  cnf(c_0_44, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.50  cnf(c_0_45, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.50  cnf(c_0_46, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.50  cnf(c_0_47, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))|~v2_waybel_0(X2,k3_yellow_1(X1))|~v13_waybel_0(X2,k3_yellow_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))|~r2_hidden(X3,X2)|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.50  cnf(c_0_48, plain, (k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.50  cnf(c_0_49, negated_conjecture, (v13_waybel_0(esk6_0,k3_yellow_1(k2_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.50  cnf(c_0_50, negated_conjecture, (v1_subset_1(esk6_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0))))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.50  cnf(c_0_51, negated_conjecture, (v2_waybel_0(esk6_0,k3_yellow_1(k2_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.50  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk5_0)))))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.50  cnf(c_0_53, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.50  cnf(c_0_54, negated_conjecture, (u1_struct_0(esk5_0)=k2_struct_0(esk5_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.50  cnf(c_0_55, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.50  cnf(c_0_56, plain, (X1=X3|r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.50  fof(c_0_57, plain, ![X22, X23, X25, X26, X27]:(((r2_hidden(esk3_2(X22,X23),X22)|r1_xboole_0(X22,X23))&(r2_hidden(esk3_2(X22,X23),X23)|r1_xboole_0(X22,X23)))&(~r2_hidden(X27,X25)|~r2_hidden(X27,X26)|~r1_xboole_0(X25,X26))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.19/0.50  cnf(c_0_58, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_36]), c_0_44])).
% 0.19/0.50  cnf(c_0_59, plain, (X1!=X2|~r2_hidden(X1,k5_xboole_0(X3,k3_xboole_0(X3,k1_tarski(X2))))), inference(rw,[status(thm)],[c_0_45, c_0_23])).
% 0.19/0.50  cnf(c_0_60, plain, (r2_hidden(X1,X2)|X3!=k5_xboole_0(X2,k3_xboole_0(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_46, c_0_23])).
% 0.19/0.50  fof(c_0_61, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.50  cnf(c_0_62, plain, (v1_xboole_0(X2)|v1_xboole_0(X1)|~v1_xboole_0(X3)|~r2_hidden(X3,X2)|~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))|~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))|~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_48]), c_0_48]), c_0_48]), c_0_48])).
% 0.19/0.50  cnf(c_0_63, negated_conjecture, (v13_waybel_0(esk6_0,k3_lattice3(k1_lattice3(k2_struct_0(esk5_0))))), inference(rw,[status(thm)],[c_0_49, c_0_48])).
% 0.19/0.50  cnf(c_0_64, negated_conjecture, (v1_subset_1(esk6_0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk5_0)))))), inference(rw,[status(thm)],[c_0_50, c_0_48])).
% 0.19/0.50  cnf(c_0_65, negated_conjecture, (v2_waybel_0(esk6_0,k3_lattice3(k1_lattice3(k2_struct_0(esk5_0))))), inference(rw,[status(thm)],[c_0_51, c_0_48])).
% 0.19/0.50  cnf(c_0_66, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk5_0))))))), inference(rw,[status(thm)],[c_0_52, c_0_48])).
% 0.19/0.50  cnf(c_0_67, negated_conjecture, (~v1_xboole_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.50  cnf(c_0_68, negated_conjecture, (~v1_xboole_0(k2_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_43])]), c_0_55])).
% 0.19/0.50  cnf(c_0_69, plain, (X1=X3|r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k1_tarski(X3))))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_56, c_0_23])).
% 0.19/0.50  cnf(c_0_70, plain, (r2_hidden(esk3_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.50  cnf(c_0_71, plain, (k3_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_58]), c_0_36]), c_0_44])).
% 0.19/0.50  cnf(c_0_72, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k1_tarski(X1))))), inference(er,[status(thm)],[c_0_59])).
% 0.19/0.50  cnf(c_0_73, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(er,[status(thm)],[c_0_60])).
% 0.19/0.50  cnf(c_0_74, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.50  fof(c_0_75, plain, ![X28, X29, X31, X32, X33]:((r1_xboole_0(X28,X29)|r2_hidden(esk4_2(X28,X29),k3_xboole_0(X28,X29)))&(~r2_hidden(X33,k3_xboole_0(X31,X32))|~r1_xboole_0(X31,X32))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.19/0.50  cnf(c_0_76, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.50  cnf(c_0_77, negated_conjecture, (~v1_xboole_0(X1)|~r2_hidden(X1,esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64]), c_0_65]), c_0_66])]), c_0_67]), c_0_68])).
% 0.19/0.50  cnf(c_0_78, plain, (r2_hidden(esk3_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.50  cnf(c_0_79, plain, (esk3_2(X1,X2)=X3|r1_xboole_0(X1,X2)|r2_hidden(esk3_2(X1,X2),k5_xboole_0(X2,k3_xboole_0(X2,k1_tarski(X3))))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.19/0.50  cnf(c_0_80, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_58, c_0_71])).
% 0.19/0.50  cnf(c_0_81, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_72, c_0_27])).
% 0.19/0.50  cnf(c_0_82, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.50  cnf(c_0_83, plain, (r2_hidden(esk1_2(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3),X1)|r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.19/0.50  cnf(c_0_84, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.19/0.50  cnf(c_0_85, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_76, c_0_23])).
% 0.19/0.50  cnf(c_0_86, negated_conjecture, (r1_xboole_0(esk6_0,X1)|~v1_xboole_0(esk3_2(esk6_0,X1))), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.19/0.50  cnf(c_0_87, plain, (esk3_2(X1,k1_tarski(X2))=X2|r1_xboole_0(X1,k1_tarski(X2))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_71]), c_0_80]), c_0_81])).
% 0.19/0.50  cnf(c_0_88, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.19/0.50  cnf(c_0_89, plain, (~r1_xboole_0(X1,X2)|~r2_hidden(X3,k3_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_84, c_0_31])).
% 0.19/0.50  cnf(c_0_90, plain, (X1=k1_xboole_0|r2_hidden(esk2_3(k1_xboole_0,X2,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_85]), c_0_27])).
% 0.19/0.50  cnf(c_0_91, plain, (r1_xboole_0(k3_xboole_0(X1,X2),X3)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_84, c_0_78])).
% 0.19/0.50  cnf(c_0_92, negated_conjecture, (r1_xboole_0(esk6_0,k1_tarski(X1))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.19/0.50  fof(c_0_93, plain, ![X46, X47, X48]:(~m1_subset_1(X47,k1_zfmisc_1(X46))|k7_subset_1(X46,X47,X48)=k4_xboole_0(X47,X48)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.19/0.50  fof(c_0_94, plain, ![X34, X35]:(((r1_tarski(X34,X35)|X34!=X35)&(r1_tarski(X35,X34)|X34!=X35))&(~r1_tarski(X34,X35)|~r1_tarski(X35,X34)|X34=X35)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.50  cnf(c_0_95, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_88, c_0_28])).
% 0.19/0.50  cnf(c_0_96, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.19/0.50  cnf(c_0_97, negated_conjecture, (r1_xboole_0(k3_xboole_0(esk6_0,k1_tarski(X1)),X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.19/0.50  fof(c_0_98, plain, ![X52, X53]:(v2_struct_0(X52)|~l1_struct_0(X52)|(v1_xboole_0(X53)|~v2_waybel_0(X53,k3_yellow_1(k2_struct_0(X52)))|~v13_waybel_0(X53,k3_yellow_1(k2_struct_0(X52)))|~m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X52)))))|k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X52))),X53,k1_tarski(k1_xboole_0))=k2_yellow19(X52,k3_yellow19(X52,k2_struct_0(X52),X53)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow19])])])])).
% 0.19/0.50  cnf(c_0_99, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_93])).
% 0.19/0.50  cnf(c_0_100, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_94])).
% 0.19/0.50  cnf(c_0_101, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_95, c_0_31])).
% 0.19/0.50  cnf(c_0_102, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2)))=k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_28, c_0_28])).
% 0.19/0.50  cnf(c_0_103, negated_conjecture, (k3_xboole_0(X1,k3_xboole_0(esk6_0,k1_tarski(X2)))=k1_xboole_0|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 0.19/0.50  cnf(c_0_104, plain, (v2_struct_0(X1)|v1_xboole_0(X2)|k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))),X2,k1_tarski(k1_xboole_0))=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))|~l1_struct_0(X1)|~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))|~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))), inference(split_conjunct,[status(thm)],[c_0_98])).
% 0.19/0.50  cnf(c_0_105, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k3_xboole_0(X1,X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_99, c_0_23])).
% 0.19/0.50  cnf(c_0_106, plain, (k3_xboole_0(X1,X2)=X2|~r1_tarski(X2,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_100, c_0_101])).
% 0.19/0.50  cnf(c_0_107, negated_conjecture, (k3_xboole_0(esk6_0,k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,k1_tarski(X1))))=esk6_0|~v1_xboole_0(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_44])).
% 0.19/0.50  cnf(c_0_108, plain, (k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X2,k1_tarski(k1_xboole_0))=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))|v1_xboole_0(X2)|v2_struct_0(X1)|~l1_struct_0(X1)|~v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_104, c_0_48]), c_0_48]), c_0_48]), c_0_48])).
% 0.19/0.50  cnf(c_0_109, negated_conjecture, (k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk5_0)))),esk6_0,X1)=k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,X1))), inference(spm,[status(thm)],[c_0_105, c_0_66])).
% 0.19/0.50  cnf(c_0_110, negated_conjecture, (k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,k1_tarski(X1)))=esk6_0|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_88])])).
% 0.19/0.50  cnf(c_0_111, negated_conjecture, (k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,k1_tarski(k1_xboole_0)))=k2_yellow19(esk5_0,k3_yellow19(esk5_0,k2_struct_0(esk5_0),esk6_0))), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_63]), c_0_65]), c_0_43]), c_0_66])]), c_0_55]), c_0_67]), c_0_109])).
% 0.19/0.50  cnf(c_0_112, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.50  cnf(c_0_113, negated_conjecture, (esk6_0!=k2_yellow19(esk5_0,k3_yellow19(esk5_0,k2_struct_0(esk5_0),esk6_0))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.50  cnf(c_0_114, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_112])]), c_0_113]), ['proof']).
% 0.19/0.50  # SZS output end CNFRefutation
% 0.19/0.50  # Proof object total steps             : 115
% 0.19/0.50  # Proof object clause steps            : 77
% 0.19/0.50  # Proof object formula steps           : 38
% 0.19/0.50  # Proof object conjectures             : 27
% 0.19/0.50  # Proof object clause conjectures      : 24
% 0.19/0.50  # Proof object formula conjectures     : 3
% 0.19/0.50  # Proof object initial clauses used    : 30
% 0.19/0.50  # Proof object initial formulas used   : 19
% 0.19/0.50  # Proof object generating inferences   : 29
% 0.19/0.50  # Proof object simplifying inferences  : 53
% 0.19/0.50  # Training examples: 0 positive, 0 negative
% 0.19/0.50  # Parsed axioms                        : 20
% 0.19/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.50  # Initial clauses                      : 41
% 0.19/0.50  # Removed in clause preprocessing      : 2
% 0.19/0.50  # Initial clauses in saturation        : 39
% 0.19/0.50  # Processed clauses                    : 666
% 0.19/0.50  # ...of these trivial                  : 26
% 0.19/0.50  # ...subsumed                          : 407
% 0.19/0.50  # ...remaining for further processing  : 233
% 0.19/0.50  # Other redundant clauses eliminated   : 8
% 0.19/0.50  # Clauses deleted for lack of memory   : 0
% 0.19/0.50  # Backward-subsumed                    : 3
% 0.19/0.50  # Backward-rewritten                   : 4
% 0.19/0.50  # Generated clauses                    : 6723
% 0.19/0.50  # ...of the previous two non-trivial   : 6221
% 0.19/0.50  # Contextual simplify-reflections      : 1
% 0.19/0.50  # Paramodulations                      : 6670
% 0.19/0.50  # Factorizations                       : 45
% 0.19/0.50  # Equation resolutions                 : 8
% 0.19/0.50  # Propositional unsat checks           : 0
% 0.19/0.50  #    Propositional check models        : 0
% 0.19/0.50  #    Propositional check unsatisfiable : 0
% 0.19/0.50  #    Propositional clauses             : 0
% 0.19/0.50  #    Propositional clauses after purity: 0
% 0.19/0.50  #    Propositional unsat core size     : 0
% 0.19/0.50  #    Propositional preprocessing time  : 0.000
% 0.19/0.50  #    Propositional encoding time       : 0.000
% 0.19/0.50  #    Propositional solver time         : 0.000
% 0.19/0.50  #    Success case prop preproc time    : 0.000
% 0.19/0.50  #    Success case prop encoding time   : 0.000
% 0.19/0.50  #    Success case prop solver time     : 0.000
% 0.19/0.50  # Current number of processed clauses  : 183
% 0.19/0.50  #    Positive orientable unit clauses  : 34
% 0.19/0.50  #    Positive unorientable unit clauses: 1
% 0.19/0.50  #    Negative unit clauses             : 7
% 0.19/0.50  #    Non-unit-clauses                  : 141
% 0.19/0.50  # Current number of unprocessed clauses: 5568
% 0.19/0.50  # ...number of literals in the above   : 25368
% 0.19/0.50  # Current number of archived formulas  : 0
% 0.19/0.50  # Current number of archived clauses   : 46
% 0.19/0.50  # Clause-clause subsumption calls (NU) : 7147
% 0.19/0.50  # Rec. Clause-clause subsumption calls : 3300
% 0.19/0.50  # Non-unit clause-clause subsumptions  : 280
% 0.19/0.50  # Unit Clause-clause subsumption calls : 129
% 0.19/0.50  # Rewrite failures with RHS unbound    : 0
% 0.19/0.50  # BW rewrite match attempts            : 63
% 0.19/0.50  # BW rewrite match successes           : 14
% 0.19/0.50  # Condensation attempts                : 0
% 0.19/0.50  # Condensation successes               : 0
% 0.19/0.50  # Termbank termtop insertions          : 121116
% 0.19/0.50  
% 0.19/0.50  # -------------------------------------------------
% 0.19/0.50  # User time                : 0.154 s
% 0.19/0.50  # System time              : 0.008 s
% 0.19/0.50  # Total time               : 0.163 s
% 0.19/0.50  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
