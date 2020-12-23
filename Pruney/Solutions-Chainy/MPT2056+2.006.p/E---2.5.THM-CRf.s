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

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 195 expanded)
%              Number of clauses        :   48 (  79 expanded)
%              Number of leaves         :   17 (  51 expanded)
%              Depth                    :    9
%              Number of atoms          :  201 ( 608 expanded)
%              Number of equality atoms :   46 ( 148 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(d2_yellow_1,axiom,(
    ! [X1] : k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(l27_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X1,X2)
     => r1_xboole_0(k1_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

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

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

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

fof(fc5_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(k2_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_17,negated_conjecture,(
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

fof(c_0_18,plain,(
    ! [X12,X13,X15,X16,X17] :
      ( ( r1_xboole_0(X12,X13)
        | r2_hidden(esk2_2(X12,X13),k3_xboole_0(X12,X13)) )
      & ( ~ r2_hidden(X17,k3_xboole_0(X15,X16))
        | ~ r1_xboole_0(X15,X16) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_19,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_20,plain,(
    ! [X26] : k4_xboole_0(k1_xboole_0,X26) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

fof(c_0_21,plain,(
    ! [X20,X21] : k4_xboole_0(X20,X21) = k5_xboole_0(X20,k3_xboole_0(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_22,plain,(
    ! [X24,X25] : k4_xboole_0(X24,k4_xboole_0(X24,X25)) = k3_xboole_0(X24,X25) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_23,plain,(
    ! [X29,X30,X31] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(X29))
      | k7_subset_1(X29,X30,X31) = k4_xboole_0(X30,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & l1_struct_0(esk3_0)
    & ~ v1_xboole_0(esk4_0)
    & v1_subset_1(esk4_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0))))
    & v2_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0)))
    & v13_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0)))
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0)))))
    & esk4_0 != k2_yellow19(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).

fof(c_0_25,plain,(
    ! [X33] : k3_yellow_1(X33) = k3_lattice3(k1_lattice3(X33)) ),
    inference(variable_rename,[status(thm)],[d2_yellow_1])).

fof(c_0_26,plain,(
    ! [X18,X19] :
      ( ( r1_tarski(X18,X19)
        | X18 != X19 )
      & ( r1_tarski(X19,X18)
        | X18 != X19 )
      & ( ~ r1_tarski(X18,X19)
        | ~ r1_tarski(X19,X18)
        | X18 = X19 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_27,plain,(
    ! [X22] : r1_tarski(k1_xboole_0,X22) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_30,plain,(
    ! [X27,X28] :
      ( r2_hidden(X27,X28)
      | r1_xboole_0(k1_tarski(X27),X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).

cnf(c_0_31,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_34,plain,(
    ! [X34,X35] :
      ( v2_struct_0(X34)
      | ~ l1_struct_0(X34)
      | v1_xboole_0(X35)
      | ~ v2_waybel_0(X35,k3_yellow_1(k2_struct_0(X34)))
      | ~ v13_waybel_0(X35,k3_yellow_1(k2_struct_0(X34)))
      | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X34)))))
      | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X34))),X35,k1_tarski(k1_xboole_0)) = k2_yellow19(X34,k3_yellow19(X34,k2_struct_0(X34),X35)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow19])])])])).

cnf(c_0_35,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,plain,
    ( k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_42,plain,(
    ! [X23] : k4_xboole_0(X23,k1_xboole_0) = X23 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_43,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_44,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_45,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_32]),c_0_32])).

fof(c_0_46,plain,(
    ! [X36,X37,X38] :
      ( v1_xboole_0(X36)
      | v1_xboole_0(X37)
      | ~ v1_subset_1(X37,u1_struct_0(k3_yellow_1(X36)))
      | ~ v2_waybel_0(X37,k3_yellow_1(X36))
      | ~ v13_waybel_0(X37,k3_yellow_1(X36))
      | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X36))))
      | ~ r2_hidden(X38,X37)
      | ~ v1_xboole_0(X38) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t2_yellow19])])])])).

cnf(c_0_47,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))),X2,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | ~ l1_struct_0(X1)
    | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_48,negated_conjecture,
    ( v13_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_49,negated_conjecture,
    ( v2_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_50,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k3_xboole_0(X1,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_35,c_0_32])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk3_0)))))) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_52,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,X2)
    | r1_tarski(k3_xboole_0(k1_tarski(X1),X2),X3) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_54,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_55,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_56,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_57,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
    | ~ v2_waybel_0(X2,k3_yellow_1(X1))
    | ~ v13_waybel_0(X2,k3_yellow_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ r2_hidden(X3,X2)
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_58,negated_conjecture,
    ( v1_subset_1(esk4_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_59,plain,
    ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X2,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_37]),c_0_37]),c_0_37]),c_0_37])).

cnf(c_0_60,negated_conjecture,
    ( v13_waybel_0(esk4_0,k3_lattice3(k1_lattice3(k2_struct_0(esk3_0)))) ),
    inference(rw,[status(thm)],[c_0_48,c_0_37])).

cnf(c_0_61,negated_conjecture,
    ( v2_waybel_0(esk4_0,k3_lattice3(k1_lattice3(k2_struct_0(esk3_0)))) ),
    inference(rw,[status(thm)],[c_0_49,c_0_37])).

cnf(c_0_62,negated_conjecture,
    ( l1_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_63,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_64,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_65,negated_conjecture,
    ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk3_0)))),esk4_0,X1) = k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_66,plain,
    ( k3_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
    | r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_67,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_54,c_0_32])).

cnf(c_0_68,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_69,plain,
    ( v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ v1_xboole_0(X3)
    | ~ r2_hidden(X3,X2)
    | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
    | ~ v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_37]),c_0_37]),c_0_37]),c_0_37])).

cnf(c_0_70,negated_conjecture,
    ( v1_subset_1(esk4_0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk3_0))))) ),
    inference(rw,[status(thm)],[c_0_58,c_0_37])).

cnf(c_0_71,negated_conjecture,
    ( k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k1_tarski(k1_xboole_0))) = k2_yellow19(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0)) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_62]),c_0_51])]),c_0_63]),c_0_64]),c_0_65])).

cnf(c_0_72,plain,
    ( k3_xboole_0(X1,k1_tarski(X2)) = k1_xboole_0
    | r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_66])).

cnf(c_0_73,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( esk4_0 != k2_yellow19(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_75,plain,(
    ! [X32] :
      ( v2_struct_0(X32)
      | ~ l1_struct_0(X32)
      | ~ v1_xboole_0(k2_struct_0(X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_struct_0])])])).

cnf(c_0_76,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk3_0))
    | ~ v1_xboole_0(X1)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_60]),c_0_70]),c_0_61]),c_0_51])]),c_0_64])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(k1_xboole_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73]),c_0_74])).

cnf(c_0_78,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_79,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(k2_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78])])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_62])]),c_0_63]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:46:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___110_C45_F1_PI_SE_CS_SP_PS_S4S
% 0.13/0.39  # and selection function SelectNewComplexAHPNS.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.028 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t15_yellow19, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 0.13/0.39  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.13/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.39  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 0.13/0.39  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.13/0.39  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.13/0.39  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.13/0.39  fof(d2_yellow_1, axiom, ![X1]:k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_yellow_1)).
% 0.13/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.39  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.13/0.39  fof(l27_zfmisc_1, axiom, ![X1, X2]:(~(r2_hidden(X1,X2))=>r1_xboole_0(k1_tarski(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 0.13/0.39  fof(t14_yellow19, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))),X2,k1_tarski(k1_xboole_0))=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow19)).
% 0.13/0.39  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.13/0.39  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.13/0.39  fof(t2_yellow19, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))))&v2_waybel_0(X2,k3_yellow_1(X1)))&v13_waybel_0(X2,k3_yellow_1(X1)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))))=>![X3]:~((r2_hidden(X3,X2)&v1_xboole_0(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_yellow19)).
% 0.13/0.39  fof(fc5_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(k2_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 0.13/0.39  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.13/0.39  fof(c_0_17, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))))), inference(assume_negation,[status(cth)],[t15_yellow19])).
% 0.13/0.39  fof(c_0_18, plain, ![X12, X13, X15, X16, X17]:((r1_xboole_0(X12,X13)|r2_hidden(esk2_2(X12,X13),k3_xboole_0(X12,X13)))&(~r2_hidden(X17,k3_xboole_0(X15,X16))|~r1_xboole_0(X15,X16))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.13/0.39  fof(c_0_19, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.39  fof(c_0_20, plain, ![X26]:k4_xboole_0(k1_xboole_0,X26)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.13/0.39  fof(c_0_21, plain, ![X20, X21]:k4_xboole_0(X20,X21)=k5_xboole_0(X20,k3_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.13/0.39  fof(c_0_22, plain, ![X24, X25]:k4_xboole_0(X24,k4_xboole_0(X24,X25))=k3_xboole_0(X24,X25), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.13/0.39  fof(c_0_23, plain, ![X29, X30, X31]:(~m1_subset_1(X30,k1_zfmisc_1(X29))|k7_subset_1(X29,X30,X31)=k4_xboole_0(X30,X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.13/0.39  fof(c_0_24, negated_conjecture, ((~v2_struct_0(esk3_0)&l1_struct_0(esk3_0))&(((((~v1_xboole_0(esk4_0)&v1_subset_1(esk4_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0)))))&v2_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0))))&v13_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0))))&m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0))))))&esk4_0!=k2_yellow19(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).
% 0.13/0.39  fof(c_0_25, plain, ![X33]:k3_yellow_1(X33)=k3_lattice3(k1_lattice3(X33)), inference(variable_rename,[status(thm)],[d2_yellow_1])).
% 0.13/0.39  fof(c_0_26, plain, ![X18, X19]:(((r1_tarski(X18,X19)|X18!=X19)&(r1_tarski(X19,X18)|X18!=X19))&(~r1_tarski(X18,X19)|~r1_tarski(X19,X18)|X18=X19)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.39  fof(c_0_27, plain, ![X22]:r1_tarski(k1_xboole_0,X22), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.13/0.39  cnf(c_0_28, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  cnf(c_0_29, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.39  fof(c_0_30, plain, ![X27, X28]:(r2_hidden(X27,X28)|r1_xboole_0(k1_tarski(X27),X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).
% 0.13/0.39  cnf(c_0_31, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.39  cnf(c_0_32, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.39  cnf(c_0_33, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  fof(c_0_34, plain, ![X34, X35]:(v2_struct_0(X34)|~l1_struct_0(X34)|(v1_xboole_0(X35)|~v2_waybel_0(X35,k3_yellow_1(k2_struct_0(X34)))|~v13_waybel_0(X35,k3_yellow_1(k2_struct_0(X34)))|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X34)))))|k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X34))),X35,k1_tarski(k1_xboole_0))=k2_yellow19(X34,k3_yellow19(X34,k2_struct_0(X34),X35)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow19])])])])).
% 0.13/0.39  cnf(c_0_35, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.39  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0)))))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.39  cnf(c_0_37, plain, (k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.39  cnf(c_0_38, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.39  cnf(c_0_39, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.39  cnf(c_0_40, plain, (r1_tarski(k3_xboole_0(X1,X2),X3)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.39  cnf(c_0_41, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.39  fof(c_0_42, plain, ![X23]:k4_xboole_0(X23,k1_xboole_0)=X23, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.13/0.39  fof(c_0_43, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.13/0.39  cnf(c_0_44, plain, (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 0.13/0.39  cnf(c_0_45, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_32]), c_0_32])).
% 0.13/0.39  fof(c_0_46, plain, ![X36, X37, X38]:(v1_xboole_0(X36)|(v1_xboole_0(X37)|~v1_subset_1(X37,u1_struct_0(k3_yellow_1(X36)))|~v2_waybel_0(X37,k3_yellow_1(X36))|~v13_waybel_0(X37,k3_yellow_1(X36))|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X36))))|(~r2_hidden(X38,X37)|~v1_xboole_0(X38)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t2_yellow19])])])])).
% 0.13/0.39  cnf(c_0_47, plain, (v2_struct_0(X1)|v1_xboole_0(X2)|k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))),X2,k1_tarski(k1_xboole_0))=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))|~l1_struct_0(X1)|~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))|~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.39  cnf(c_0_48, negated_conjecture, (v13_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.39  cnf(c_0_49, negated_conjecture, (v2_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.39  cnf(c_0_50, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k3_xboole_0(X1,X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_35, c_0_32])).
% 0.13/0.39  cnf(c_0_51, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk3_0))))))), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.13/0.39  cnf(c_0_52, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.13/0.39  cnf(c_0_53, plain, (r2_hidden(X1,X2)|r1_tarski(k3_xboole_0(k1_tarski(X1),X2),X3)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.13/0.39  cnf(c_0_54, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.13/0.39  cnf(c_0_55, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.39  cnf(c_0_56, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.13/0.39  cnf(c_0_57, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))|~v2_waybel_0(X2,k3_yellow_1(X1))|~v13_waybel_0(X2,k3_yellow_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))|~r2_hidden(X3,X2)|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.13/0.39  cnf(c_0_58, negated_conjecture, (v1_subset_1(esk4_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.39  cnf(c_0_59, plain, (k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X2,k1_tarski(k1_xboole_0))=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))|v1_xboole_0(X2)|v2_struct_0(X1)|~l1_struct_0(X1)|~v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_37]), c_0_37]), c_0_37]), c_0_37])).
% 0.13/0.39  cnf(c_0_60, negated_conjecture, (v13_waybel_0(esk4_0,k3_lattice3(k1_lattice3(k2_struct_0(esk3_0))))), inference(rw,[status(thm)],[c_0_48, c_0_37])).
% 0.13/0.39  cnf(c_0_61, negated_conjecture, (v2_waybel_0(esk4_0,k3_lattice3(k1_lattice3(k2_struct_0(esk3_0))))), inference(rw,[status(thm)],[c_0_49, c_0_37])).
% 0.13/0.39  cnf(c_0_62, negated_conjecture, (l1_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.39  cnf(c_0_63, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.39  cnf(c_0_64, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.39  cnf(c_0_65, negated_conjecture, (k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk3_0)))),esk4_0,X1)=k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,X1))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.13/0.39  cnf(c_0_66, plain, (k3_xboole_0(k1_tarski(X1),X2)=k1_xboole_0|r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.13/0.39  cnf(c_0_67, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_54, c_0_32])).
% 0.13/0.39  cnf(c_0_68, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.13/0.39  cnf(c_0_69, plain, (v1_xboole_0(X2)|v1_xboole_0(X1)|~v1_xboole_0(X3)|~r2_hidden(X3,X2)|~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))|~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))|~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_37]), c_0_37]), c_0_37]), c_0_37])).
% 0.13/0.39  cnf(c_0_70, negated_conjecture, (v1_subset_1(esk4_0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk3_0)))))), inference(rw,[status(thm)],[c_0_58, c_0_37])).
% 0.13/0.39  cnf(c_0_71, negated_conjecture, (k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k1_tarski(k1_xboole_0)))=k2_yellow19(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61]), c_0_62]), c_0_51])]), c_0_63]), c_0_64]), c_0_65])).
% 0.13/0.39  cnf(c_0_72, plain, (k3_xboole_0(X1,k1_tarski(X2))=k1_xboole_0|r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_55, c_0_66])).
% 0.13/0.39  cnf(c_0_73, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_67, c_0_68])).
% 0.13/0.39  cnf(c_0_74, negated_conjecture, (esk4_0!=k2_yellow19(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.39  fof(c_0_75, plain, ![X32]:(v2_struct_0(X32)|~l1_struct_0(X32)|~v1_xboole_0(k2_struct_0(X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_struct_0])])])).
% 0.13/0.39  cnf(c_0_76, negated_conjecture, (v1_xboole_0(k2_struct_0(esk3_0))|~v1_xboole_0(X1)|~r2_hidden(X1,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_60]), c_0_70]), c_0_61]), c_0_51])]), c_0_64])).
% 0.13/0.39  cnf(c_0_77, negated_conjecture, (r2_hidden(k1_xboole_0,esk4_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73]), c_0_74])).
% 0.13/0.39  cnf(c_0_78, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.13/0.39  cnf(c_0_79, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(k2_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.13/0.39  cnf(c_0_80, negated_conjecture, (v1_xboole_0(k2_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78])])).
% 0.13/0.39  cnf(c_0_81, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_62])]), c_0_63]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 82
% 0.13/0.39  # Proof object clause steps            : 48
% 0.13/0.39  # Proof object formula steps           : 34
% 0.13/0.39  # Proof object conjectures             : 21
% 0.13/0.39  # Proof object clause conjectures      : 18
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 24
% 0.13/0.39  # Proof object initial formulas used   : 17
% 0.13/0.39  # Proof object generating inferences   : 13
% 0.13/0.39  # Proof object simplifying inferences  : 37
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 17
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 29
% 0.13/0.39  # Removed in clause preprocessing      : 2
% 0.13/0.39  # Initial clauses in saturation        : 27
% 0.13/0.39  # Processed clauses                    : 133
% 0.13/0.39  # ...of these trivial                  : 8
% 0.13/0.39  # ...subsumed                          : 25
% 0.13/0.39  # ...remaining for further processing  : 100
% 0.13/0.39  # Other redundant clauses eliminated   : 2
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 7
% 0.13/0.39  # Backward-rewritten                   : 11
% 0.13/0.39  # Generated clauses                    : 255
% 0.13/0.39  # ...of the previous two non-trivial   : 205
% 0.13/0.39  # Contextual simplify-reflections      : 1
% 0.13/0.39  # Paramodulations                      : 253
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 2
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 54
% 0.13/0.39  #    Positive orientable unit clauses  : 22
% 0.13/0.39  #    Positive unorientable unit clauses: 1
% 0.13/0.39  #    Negative unit clauses             : 4
% 0.13/0.39  #    Non-unit-clauses                  : 27
% 0.13/0.39  # Current number of unprocessed clauses: 64
% 0.13/0.39  # ...number of literals in the above   : 172
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 46
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 506
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 226
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 27
% 0.13/0.39  # Unit Clause-clause subsumption calls : 29
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 33
% 0.13/0.39  # BW rewrite match successes           : 11
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 4432
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.036 s
% 0.13/0.39  # System time              : 0.002 s
% 0.13/0.39  # Total time               : 0.038 s
% 0.13/0.39  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
