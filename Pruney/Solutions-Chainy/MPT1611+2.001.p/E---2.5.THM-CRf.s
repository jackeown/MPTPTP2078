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
% DateTime   : Thu Dec  3 11:15:52 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 142 expanded)
%              Number of clauses        :   40 (  67 expanded)
%              Number of leaves         :   19 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :  126 ( 214 expanded)
%              Number of equality atoms :   78 ( 144 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t19_yellow_1,conjecture,(
    ! [X1] : k4_yellow_0(k3_yellow_1(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_yellow_1)).

fof(t4_yellow_1,axiom,(
    ! [X1] : k3_yellow_1(X1) = k2_yellow_1(k9_setfam_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).

fof(redefinition_k9_setfam_1,axiom,(
    ! [X1] : k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d1_yellow_1,axiom,(
    ! [X1] : k2_yellow_1(X1) = g1_orders_2(X1,k1_yellow_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_yellow_1)).

fof(d2_yellow_1,axiom,(
    ! [X1] : k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).

fof(t14_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( r2_hidden(k3_tarski(X1),X1)
       => k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).

fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t99_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(c_0_19,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | X7 != X8 )
      & ( r1_tarski(X8,X7)
        | X7 != X8 )
      & ( ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X7)
        | X7 = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_20,plain,(
    ! [X34,X35] : k1_setfam_1(k2_tarski(X34,X35)) = k3_xboole_0(X34,X35) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_21,plain,(
    ! [X16,X17] : k1_enumset1(X16,X16,X17) = k2_tarski(X16,X17) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1] : k4_yellow_0(k3_yellow_1(X1)) = X1 ),
    inference(assume_negation,[status(cth)],[t19_yellow_1])).

fof(c_0_23,plain,(
    ! [X44] : k3_yellow_1(X44) = k2_yellow_1(k9_setfam_1(X44)) ),
    inference(variable_rename,[status(thm)],[t4_yellow_1])).

fof(c_0_24,plain,(
    ! [X40] : k9_setfam_1(X40) = k1_zfmisc_1(X40) ),
    inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).

fof(c_0_25,plain,(
    ! [X21,X22,X23,X24,X25,X26] :
      ( ( ~ r2_hidden(X23,X22)
        | r1_tarski(X23,X21)
        | X22 != k1_zfmisc_1(X21) )
      & ( ~ r1_tarski(X24,X21)
        | r2_hidden(X24,X22)
        | X22 != k1_zfmisc_1(X21) )
      & ( ~ r2_hidden(esk1_2(X25,X26),X26)
        | ~ r1_tarski(esk1_2(X25,X26),X25)
        | X26 = k1_zfmisc_1(X25) )
      & ( r2_hidden(esk1_2(X25,X26),X26)
        | r1_tarski(esk1_2(X25,X26),X25)
        | X26 = k1_zfmisc_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_27,plain,(
    ! [X9,X10] : k4_xboole_0(X9,X10) = k5_xboole_0(X9,k3_xboole_0(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_28,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_30,negated_conjecture,(
    k4_yellow_0(k3_yellow_1(esk3_0)) != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).

cnf(c_0_31,plain,
    ( k3_yellow_1(X1) = k2_yellow_1(k9_setfam_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_33,plain,(
    ! [X41] : k2_yellow_1(X41) = g1_orders_2(X41,k1_yellow_1(X41)) ),
    inference(variable_rename,[status(thm)],[d1_yellow_1])).

fof(c_0_34,plain,(
    ! [X42] : k3_yellow_1(X42) = k3_lattice3(k1_lattice3(X42)) ),
    inference(variable_rename,[status(thm)],[d2_yellow_1])).

fof(c_0_35,plain,(
    ! [X43] :
      ( v1_xboole_0(X43)
      | ~ r2_hidden(k3_tarski(X43),X43)
      | k4_yellow_0(k2_yellow_1(X43)) = k3_tarski(X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_26])).

fof(c_0_38,plain,(
    ! [X28,X29,X30] :
      ( ( r2_hidden(X28,X29)
        | ~ r2_hidden(X28,k4_xboole_0(X29,k1_tarski(X30))) )
      & ( X28 != X30
        | ~ r2_hidden(X28,k4_xboole_0(X29,k1_tarski(X30))) )
      & ( ~ r2_hidden(X28,X29)
        | X28 = X30
        | r2_hidden(X28,k4_xboole_0(X29,k1_tarski(X30))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

fof(c_0_39,plain,(
    ! [X15] : k2_tarski(X15,X15) = k1_tarski(X15) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_41,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_42,plain,(
    ! [X18,X19,X20] : k2_enumset1(X18,X18,X19,X20) = k1_enumset1(X18,X19,X20) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

cnf(c_0_43,negated_conjecture,
    ( k4_yellow_0(k3_yellow_1(esk3_0)) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_44,plain,
    ( k3_yellow_1(X1) = k2_yellow_1(k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_45,plain,
    ( k2_yellow_1(X1) = g1_orders_2(X1,k1_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,plain,
    ( k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,plain,
    ( v1_xboole_0(X1)
    | k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1)
    | ~ r2_hidden(k3_tarski(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_48,plain,(
    ! [X31] : k3_tarski(k1_zfmisc_1(X31)) = X31 ),
    inference(variable_rename,[status(thm)],[t99_zfmisc_1])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_50,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_51,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_52,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_53,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_54,plain,(
    ! [X14] : k5_xboole_0(X14,k1_xboole_0) = X14 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_55,plain,(
    ! [X4,X5] : k5_xboole_0(X4,X5) = k5_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

fof(c_0_56,plain,(
    ! [X13] : k4_xboole_0(k1_xboole_0,X13) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_57,negated_conjecture,
    ( k4_yellow_0(g1_orders_2(k1_zfmisc_1(esk3_0),k1_yellow_1(k1_zfmisc_1(esk3_0)))) != esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44]),c_0_45])).

cnf(c_0_58,plain,
    ( g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))) = k3_lattice3(k1_lattice3(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_44]),c_0_45])).

cnf(c_0_59,plain,
    ( k4_yellow_0(g1_orders_2(X1,k1_yellow_1(X1))) = k3_tarski(X1)
    | v1_xboole_0(X1)
    | ~ r2_hidden(k3_tarski(X1),X1) ),
    inference(rw,[status(thm)],[c_0_47,c_0_45])).

cnf(c_0_60,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_62,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k5_xboole_0(X3,k1_setfam_1(k2_enumset1(X3,X3,X3,k2_enumset1(X2,X2,X2,X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_51]),c_0_29]),c_0_52]),c_0_53]),c_0_53])).

cnf(c_0_63,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_64,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_65,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

fof(c_0_66,plain,(
    ! [X6] :
      ( ~ v1_xboole_0(X6)
      | X6 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_67,negated_conjecture,
    ( k4_yellow_0(k3_lattice3(k1_lattice3(esk3_0))) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_68,plain,
    ( k4_yellow_0(k3_lattice3(k1_lattice3(X1))) = X1
    | v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_58]),c_0_61])])).

cnf(c_0_69,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k2_enumset1(X2,X2,X2,k2_enumset1(X1,X1,X1,X1))))) ),
    inference(er,[status(thm)],[c_0_62])).

cnf(c_0_70,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_71,plain,
    ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_52]),c_0_53])).

cnf(c_0_72,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_73,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_74,plain,
    ( ~ r2_hidden(X1,k1_setfam_1(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_enumset1(X1,X1,X1,X1)))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_75,plain,
    ( k1_setfam_1(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_71,c_0_70])).

cnf(c_0_76,negated_conjecture,
    ( k1_zfmisc_1(esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_77,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_78,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_76]),c_0_77]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:00:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.37  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.14/0.37  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.14/0.37  #
% 0.14/0.37  # Preprocessing time       : 0.028 s
% 0.14/0.37  
% 0.14/0.37  # Proof found!
% 0.14/0.37  # SZS status Theorem
% 0.14/0.37  # SZS output start CNFRefutation
% 0.14/0.37  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.14/0.37  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.14/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.14/0.37  fof(t19_yellow_1, conjecture, ![X1]:k4_yellow_0(k3_yellow_1(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_yellow_1)).
% 0.14/0.37  fof(t4_yellow_1, axiom, ![X1]:k3_yellow_1(X1)=k2_yellow_1(k9_setfam_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_yellow_1)).
% 0.14/0.37  fof(redefinition_k9_setfam_1, axiom, ![X1]:k9_setfam_1(X1)=k1_zfmisc_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 0.14/0.37  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.14/0.37  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.14/0.37  fof(d1_yellow_1, axiom, ![X1]:k2_yellow_1(X1)=g1_orders_2(X1,k1_yellow_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_yellow_1)).
% 0.14/0.37  fof(d2_yellow_1, axiom, ![X1]:k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_yellow_1)).
% 0.14/0.37  fof(t14_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k3_tarski(X1),X1)=>k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow_1)).
% 0.14/0.37  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 0.14/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.14/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.14/0.37  fof(t99_zfmisc_1, axiom, ![X1]:k3_tarski(k1_zfmisc_1(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 0.14/0.37  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 0.14/0.37  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.14/0.37  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 0.14/0.37  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.14/0.37  fof(c_0_19, plain, ![X7, X8]:(((r1_tarski(X7,X8)|X7!=X8)&(r1_tarski(X8,X7)|X7!=X8))&(~r1_tarski(X7,X8)|~r1_tarski(X8,X7)|X7=X8)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.14/0.37  fof(c_0_20, plain, ![X34, X35]:k1_setfam_1(k2_tarski(X34,X35))=k3_xboole_0(X34,X35), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.14/0.37  fof(c_0_21, plain, ![X16, X17]:k1_enumset1(X16,X16,X17)=k2_tarski(X16,X17), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.14/0.37  fof(c_0_22, negated_conjecture, ~(![X1]:k4_yellow_0(k3_yellow_1(X1))=X1), inference(assume_negation,[status(cth)],[t19_yellow_1])).
% 0.14/0.37  fof(c_0_23, plain, ![X44]:k3_yellow_1(X44)=k2_yellow_1(k9_setfam_1(X44)), inference(variable_rename,[status(thm)],[t4_yellow_1])).
% 0.14/0.37  fof(c_0_24, plain, ![X40]:k9_setfam_1(X40)=k1_zfmisc_1(X40), inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).
% 0.14/0.37  fof(c_0_25, plain, ![X21, X22, X23, X24, X25, X26]:(((~r2_hidden(X23,X22)|r1_tarski(X23,X21)|X22!=k1_zfmisc_1(X21))&(~r1_tarski(X24,X21)|r2_hidden(X24,X22)|X22!=k1_zfmisc_1(X21)))&((~r2_hidden(esk1_2(X25,X26),X26)|~r1_tarski(esk1_2(X25,X26),X25)|X26=k1_zfmisc_1(X25))&(r2_hidden(esk1_2(X25,X26),X26)|r1_tarski(esk1_2(X25,X26),X25)|X26=k1_zfmisc_1(X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.14/0.37  cnf(c_0_26, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.37  fof(c_0_27, plain, ![X9, X10]:k4_xboole_0(X9,X10)=k5_xboole_0(X9,k3_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.14/0.37  cnf(c_0_28, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.37  cnf(c_0_29, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.37  fof(c_0_30, negated_conjecture, k4_yellow_0(k3_yellow_1(esk3_0))!=esk3_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).
% 0.14/0.37  cnf(c_0_31, plain, (k3_yellow_1(X1)=k2_yellow_1(k9_setfam_1(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.37  cnf(c_0_32, plain, (k9_setfam_1(X1)=k1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.37  fof(c_0_33, plain, ![X41]:k2_yellow_1(X41)=g1_orders_2(X41,k1_yellow_1(X41)), inference(variable_rename,[status(thm)],[d1_yellow_1])).
% 0.14/0.37  fof(c_0_34, plain, ![X42]:k3_yellow_1(X42)=k3_lattice3(k1_lattice3(X42)), inference(variable_rename,[status(thm)],[d2_yellow_1])).
% 0.14/0.37  fof(c_0_35, plain, ![X43]:(v1_xboole_0(X43)|(~r2_hidden(k3_tarski(X43),X43)|k4_yellow_0(k2_yellow_1(X43))=k3_tarski(X43))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).
% 0.14/0.38  cnf(c_0_36, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.14/0.38  cnf(c_0_37, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_26])).
% 0.14/0.38  fof(c_0_38, plain, ![X28, X29, X30]:(((r2_hidden(X28,X29)|~r2_hidden(X28,k4_xboole_0(X29,k1_tarski(X30))))&(X28!=X30|~r2_hidden(X28,k4_xboole_0(X29,k1_tarski(X30)))))&(~r2_hidden(X28,X29)|X28=X30|r2_hidden(X28,k4_xboole_0(X29,k1_tarski(X30))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 0.14/0.38  fof(c_0_39, plain, ![X15]:k2_tarski(X15,X15)=k1_tarski(X15), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.14/0.38  cnf(c_0_40, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.14/0.38  cnf(c_0_41, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 0.14/0.38  fof(c_0_42, plain, ![X18, X19, X20]:k2_enumset1(X18,X18,X19,X20)=k1_enumset1(X18,X19,X20), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.14/0.38  cnf(c_0_43, negated_conjecture, (k4_yellow_0(k3_yellow_1(esk3_0))!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.38  cnf(c_0_44, plain, (k3_yellow_1(X1)=k2_yellow_1(k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 0.14/0.38  cnf(c_0_45, plain, (k2_yellow_1(X1)=g1_orders_2(X1,k1_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.14/0.38  cnf(c_0_46, plain, (k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.14/0.38  cnf(c_0_47, plain, (v1_xboole_0(X1)|k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1)|~r2_hidden(k3_tarski(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.14/0.38  fof(c_0_48, plain, ![X31]:k3_tarski(k1_zfmisc_1(X31))=X31, inference(variable_rename,[status(thm)],[t99_zfmisc_1])).
% 0.14/0.38  cnf(c_0_49, plain, (r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.14/0.38  cnf(c_0_50, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.14/0.38  cnf(c_0_51, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.14/0.38  cnf(c_0_52, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 0.14/0.38  cnf(c_0_53, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.14/0.38  fof(c_0_54, plain, ![X14]:k5_xboole_0(X14,k1_xboole_0)=X14, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.14/0.38  fof(c_0_55, plain, ![X4, X5]:k5_xboole_0(X4,X5)=k5_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.14/0.38  fof(c_0_56, plain, ![X13]:k4_xboole_0(k1_xboole_0,X13)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.14/0.38  cnf(c_0_57, negated_conjecture, (k4_yellow_0(g1_orders_2(k1_zfmisc_1(esk3_0),k1_yellow_1(k1_zfmisc_1(esk3_0))))!=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44]), c_0_45])).
% 0.14/0.38  cnf(c_0_58, plain, (g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1)))=k3_lattice3(k1_lattice3(X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_44]), c_0_45])).
% 0.14/0.38  cnf(c_0_59, plain, (k4_yellow_0(g1_orders_2(X1,k1_yellow_1(X1)))=k3_tarski(X1)|v1_xboole_0(X1)|~r2_hidden(k3_tarski(X1),X1)), inference(rw,[status(thm)],[c_0_47, c_0_45])).
% 0.14/0.38  cnf(c_0_60, plain, (k3_tarski(k1_zfmisc_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.14/0.38  cnf(c_0_61, plain, (r2_hidden(X1,k1_zfmisc_1(X1))), inference(er,[status(thm)],[c_0_49])).
% 0.14/0.38  cnf(c_0_62, plain, (X1!=X2|~r2_hidden(X1,k5_xboole_0(X3,k1_setfam_1(k2_enumset1(X3,X3,X3,k2_enumset1(X2,X2,X2,X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_51]), c_0_29]), c_0_52]), c_0_53]), c_0_53])).
% 0.14/0.38  cnf(c_0_63, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.14/0.38  cnf(c_0_64, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.14/0.38  cnf(c_0_65, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.14/0.38  fof(c_0_66, plain, ![X6]:(~v1_xboole_0(X6)|X6=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.14/0.38  cnf(c_0_67, negated_conjecture, (k4_yellow_0(k3_lattice3(k1_lattice3(esk3_0)))!=esk3_0), inference(rw,[status(thm)],[c_0_57, c_0_58])).
% 0.14/0.38  cnf(c_0_68, plain, (k4_yellow_0(k3_lattice3(k1_lattice3(X1)))=X1|v1_xboole_0(k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_58]), c_0_61])])).
% 0.14/0.38  cnf(c_0_69, plain, (~r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k2_enumset1(X2,X2,X2,k2_enumset1(X1,X1,X1,X1)))))), inference(er,[status(thm)],[c_0_62])).
% 0.14/0.38  cnf(c_0_70, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.14/0.38  cnf(c_0_71, plain, (k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_52]), c_0_53])).
% 0.14/0.38  cnf(c_0_72, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.14/0.38  cnf(c_0_73, negated_conjecture, (v1_xboole_0(k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.14/0.38  cnf(c_0_74, plain, (~r2_hidden(X1,k1_setfam_1(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_enumset1(X1,X1,X1,X1))))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.14/0.38  cnf(c_0_75, plain, (k1_setfam_1(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))=k1_xboole_0), inference(rw,[status(thm)],[c_0_71, c_0_70])).
% 0.14/0.38  cnf(c_0_76, negated_conjecture, (k1_zfmisc_1(esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.14/0.38  cnf(c_0_77, plain, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_74, c_0_75])).
% 0.14/0.38  cnf(c_0_78, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_76]), c_0_77]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 79
% 0.14/0.38  # Proof object clause steps            : 40
% 0.14/0.38  # Proof object formula steps           : 39
% 0.14/0.38  # Proof object conjectures             : 9
% 0.14/0.38  # Proof object clause conjectures      : 6
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 19
% 0.14/0.38  # Proof object initial formulas used   : 19
% 0.14/0.38  # Proof object generating inferences   : 8
% 0.14/0.38  # Proof object simplifying inferences  : 24
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 26
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 42
% 0.14/0.38  # Removed in clause preprocessing      : 9
% 0.14/0.38  # Initial clauses in saturation        : 33
% 0.14/0.38  # Processed clauses                    : 78
% 0.14/0.38  # ...of these trivial                  : 6
% 0.14/0.38  # ...subsumed                          : 5
% 0.14/0.38  # ...remaining for further processing  : 67
% 0.14/0.38  # Other redundant clauses eliminated   : 3
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 4
% 0.14/0.38  # Backward-rewritten                   : 6
% 0.14/0.38  # Generated clauses                    : 86
% 0.14/0.38  # ...of the previous two non-trivial   : 74
% 0.14/0.38  # Contextual simplify-reflections      : 0
% 0.14/0.38  # Paramodulations                      : 77
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 9
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 54
% 0.14/0.38  #    Positive orientable unit clauses  : 16
% 0.14/0.38  #    Positive unorientable unit clauses: 1
% 0.14/0.38  #    Negative unit clauses             : 5
% 0.14/0.38  #    Non-unit-clauses                  : 32
% 0.14/0.38  # Current number of unprocessed clauses: 23
% 0.14/0.38  # ...number of literals in the above   : 68
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 19
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 122
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 116
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 4
% 0.14/0.38  # Unit Clause-clause subsumption calls : 35
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 20
% 0.14/0.38  # BW rewrite match successes           : 12
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 2757
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.034 s
% 0.14/0.38  # System time              : 0.002 s
% 0.14/0.38  # Total time               : 0.036 s
% 0.14/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
