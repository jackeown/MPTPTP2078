%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:03 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 250 expanded)
%              Number of clauses        :   34 ( 105 expanded)
%              Number of leaves         :   14 (  71 expanded)
%              Depth                    :    8
%              Number of atoms          :  129 ( 555 expanded)
%              Number of equality atoms :   38 ( 135 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(fc2_funcop_1,axiom,(
    ! [X1] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funcop_1)).

fof(redefinition_k7_funcop_1,axiom,(
    ! [X1,X2] : k7_funcop_1(X1,X2) = k2_funcop_1(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

fof(t27_yellow_1,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => k6_yellow_1(k1_xboole_0,X1) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_1)).

fof(fc10_yellow_1,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X2)
     => v1_yellow_1(k2_funcop_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_yellow_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t26_yellow_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v4_relat_1(X1,k1_xboole_0)
        & v1_funct_1(X1)
        & v1_partfun1(X1,k1_xboole_0)
        & v1_yellow_1(X1) )
     => k5_yellow_1(k1_xboole_0,X1) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow_1)).

fof(t134_pboole,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v4_relat_1(X1,k1_xboole_0)
        & v1_funct_1(X1)
        & v1_partfun1(X1,k1_xboole_0) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_pboole)).

fof(rc1_yellow_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( v1_relat_1(X2)
      & v4_relat_1(X2,X1)
      & v1_funct_1(X2)
      & v1_partfun1(X2,X1)
      & v1_yellow_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_yellow_1)).

fof(d5_yellow_1,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X2)
     => k6_yellow_1(X1,X2) = k5_yellow_1(X1,k7_funcop_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_yellow_1)).

fof(c_0_14,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_15,plain,(
    ! [X9] :
      ( X9 = k1_xboole_0
      | r2_hidden(esk2_1(X9),X9) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_16,plain,(
    ! [X25] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X25)) ),
    inference(variable_rename,[status(thm)],[fc2_funcop_1])).

fof(c_0_17,plain,(
    ! [X28,X29] : k7_funcop_1(X28,X29) = k2_funcop_1(X28,X29) ),
    inference(variable_rename,[status(thm)],[redefinition_k7_funcop_1])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => k6_yellow_1(k1_xboole_0,X1) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    inference(assume_negation,[status(cth)],[t27_yellow_1])).

fof(c_0_19,plain,(
    ! [X23,X24] :
      ( ~ l1_orders_2(X24)
      | v1_yellow_1(k2_funcop_1(X23,X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_yellow_1])])).

cnf(c_0_20,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( v1_xboole_0(k2_funcop_1(k1_xboole_0,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k7_funcop_1(X1,X2) = k2_funcop_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,negated_conjecture,
    ( l1_orders_2(esk4_0)
    & k6_yellow_1(k1_xboole_0,esk4_0) != g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

fof(c_0_25,plain,(
    ! [X11] : k2_tarski(X11,X11) = k1_tarski(X11) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_26,plain,(
    ! [X12,X13] : k1_enumset1(X12,X12,X13) = k2_tarski(X12,X13) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_27,plain,(
    ! [X14,X15,X16] : k2_enumset1(X14,X14,X15,X16) = k1_enumset1(X14,X15,X16) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_28,plain,(
    ! [X17,X18,X19,X20] : k3_enumset1(X17,X17,X18,X19,X20) = k2_enumset1(X17,X18,X19,X20) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_29,plain,(
    ! [X31] :
      ( ~ v1_relat_1(X31)
      | ~ v4_relat_1(X31,k1_xboole_0)
      | ~ v1_funct_1(X31)
      | ~ v1_partfun1(X31,k1_xboole_0)
      | ~ v1_yellow_1(X31)
      | k5_yellow_1(k1_xboole_0,X31) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_yellow_1])])).

fof(c_0_30,plain,(
    ! [X30] :
      ( ~ v1_relat_1(X30)
      | ~ v4_relat_1(X30,k1_xboole_0)
      | ~ v1_funct_1(X30)
      | ~ v1_partfun1(X30,k1_xboole_0)
      | X30 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t134_pboole])])).

fof(c_0_31,plain,(
    ! [X26] :
      ( v1_relat_1(esk3_1(X26))
      & v4_relat_1(esk3_1(X26),X26)
      & v1_funct_1(esk3_1(X26))
      & v1_partfun1(esk3_1(X26),X26)
      & v1_yellow_1(esk3_1(X26)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_yellow_1])])).

cnf(c_0_32,plain,
    ( v1_yellow_1(k2_funcop_1(X2,X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_34,plain,
    ( v1_xboole_0(k7_funcop_1(k1_xboole_0,X1)) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_35,negated_conjecture,
    ( k6_yellow_1(k1_xboole_0,esk4_0) != g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( k5_yellow_1(k1_xboole_0,X1) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,k1_xboole_0)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,k1_xboole_0)
    | ~ v1_yellow_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( X1 = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,k1_xboole_0)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( v1_partfun1(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,plain,
    ( v1_funct_1(esk3_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,plain,
    ( v4_relat_1(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_45,plain,
    ( v1_relat_1(esk3_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_46,plain,
    ( v1_yellow_1(k7_funcop_1(X2,X1))
    | ~ l1_orders_2(X1) ),
    inference(rw,[status(thm)],[c_0_32,c_0_23])).

cnf(c_0_47,plain,
    ( k7_funcop_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_48,negated_conjecture,
    ( k6_yellow_1(k1_xboole_0,esk4_0) != g1_orders_2(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39])).

cnf(c_0_49,plain,
    ( k5_yellow_1(k1_xboole_0,X1) = g1_orders_2(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
    | ~ v1_yellow_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v4_relat_1(X1,k1_xboole_0)
    | ~ v1_partfun1(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39])).

fof(c_0_50,plain,(
    ! [X21,X22] :
      ( ~ l1_orders_2(X22)
      | k6_yellow_1(X21,X22) = k5_yellow_1(X21,k7_funcop_1(X21,X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_yellow_1])])).

cnf(c_0_51,plain,
    ( esk3_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_44]),c_0_45])])).

cnf(c_0_52,plain,
    ( v1_yellow_1(k1_xboole_0)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_54,negated_conjecture,
    ( k5_yellow_1(k1_xboole_0,X1) != k6_yellow_1(k1_xboole_0,esk4_0)
    | ~ v1_partfun1(X1,k1_xboole_0)
    | ~ v1_funct_1(X1)
    | ~ v4_relat_1(X1,k1_xboole_0)
    | ~ v1_relat_1(X1)
    | ~ v1_yellow_1(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_55,plain,
    ( k6_yellow_1(X2,X1) = k5_yellow_1(X2,k7_funcop_1(X2,X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_56,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_51])).

cnf(c_0_57,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_51])).

cnf(c_0_58,plain,
    ( v4_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_51])).

cnf(c_0_59,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_51])).

cnf(c_0_60,negated_conjecture,
    ( v1_yellow_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_61,negated_conjecture,
    ( k6_yellow_1(k1_xboole_0,X1) != k6_yellow_1(k1_xboole_0,esk4_0)
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_47]),c_0_56]),c_0_47]),c_0_57]),c_0_47]),c_0_58]),c_0_47]),c_0_59]),c_0_47]),c_0_60])])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_61]),c_0_53])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:22:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.37  #
% 0.14/0.37  # Preprocessing time       : 0.027 s
% 0.14/0.37  # Presaturation interreduction done
% 0.14/0.37  
% 0.14/0.37  # Proof found!
% 0.14/0.37  # SZS status Theorem
% 0.14/0.37  # SZS output start CNFRefutation
% 0.14/0.37  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.14/0.37  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.14/0.37  fof(fc2_funcop_1, axiom, ![X1]:v1_xboole_0(k2_funcop_1(k1_xboole_0,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funcop_1)).
% 0.14/0.37  fof(redefinition_k7_funcop_1, axiom, ![X1, X2]:k7_funcop_1(X1,X2)=k2_funcop_1(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_funcop_1)).
% 0.14/0.37  fof(t27_yellow_1, conjecture, ![X1]:(l1_orders_2(X1)=>k6_yellow_1(k1_xboole_0,X1)=g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_yellow_1)).
% 0.14/0.37  fof(fc10_yellow_1, axiom, ![X1, X2]:(l1_orders_2(X2)=>v1_yellow_1(k2_funcop_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_yellow_1)).
% 0.14/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.14/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.14/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.14/0.37  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.14/0.37  fof(t26_yellow_1, axiom, ![X1]:(((((v1_relat_1(X1)&v4_relat_1(X1,k1_xboole_0))&v1_funct_1(X1))&v1_partfun1(X1,k1_xboole_0))&v1_yellow_1(X1))=>k5_yellow_1(k1_xboole_0,X1)=g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_yellow_1)).
% 0.14/0.37  fof(t134_pboole, axiom, ![X1]:((((v1_relat_1(X1)&v4_relat_1(X1,k1_xboole_0))&v1_funct_1(X1))&v1_partfun1(X1,k1_xboole_0))=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_pboole)).
% 0.14/0.37  fof(rc1_yellow_1, axiom, ![X1]:?[X2]:((((v1_relat_1(X2)&v4_relat_1(X2,X1))&v1_funct_1(X2))&v1_partfun1(X2,X1))&v1_yellow_1(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_yellow_1)).
% 0.14/0.37  fof(d5_yellow_1, axiom, ![X1, X2]:(l1_orders_2(X2)=>k6_yellow_1(X1,X2)=k5_yellow_1(X1,k7_funcop_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_yellow_1)).
% 0.14/0.37  fof(c_0_14, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.14/0.37  fof(c_0_15, plain, ![X9]:(X9=k1_xboole_0|r2_hidden(esk2_1(X9),X9)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.14/0.37  fof(c_0_16, plain, ![X25]:v1_xboole_0(k2_funcop_1(k1_xboole_0,X25)), inference(variable_rename,[status(thm)],[fc2_funcop_1])).
% 0.14/0.37  fof(c_0_17, plain, ![X28, X29]:k7_funcop_1(X28,X29)=k2_funcop_1(X28,X29), inference(variable_rename,[status(thm)],[redefinition_k7_funcop_1])).
% 0.14/0.37  fof(c_0_18, negated_conjecture, ~(![X1]:(l1_orders_2(X1)=>k6_yellow_1(k1_xboole_0,X1)=g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))))), inference(assume_negation,[status(cth)],[t27_yellow_1])).
% 0.14/0.37  fof(c_0_19, plain, ![X23, X24]:(~l1_orders_2(X24)|v1_yellow_1(k2_funcop_1(X23,X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_yellow_1])])).
% 0.14/0.37  cnf(c_0_20, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.37  cnf(c_0_21, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.37  cnf(c_0_22, plain, (v1_xboole_0(k2_funcop_1(k1_xboole_0,X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.37  cnf(c_0_23, plain, (k7_funcop_1(X1,X2)=k2_funcop_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.37  fof(c_0_24, negated_conjecture, (l1_orders_2(esk4_0)&k6_yellow_1(k1_xboole_0,esk4_0)!=g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.14/0.37  fof(c_0_25, plain, ![X11]:k2_tarski(X11,X11)=k1_tarski(X11), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.14/0.37  fof(c_0_26, plain, ![X12, X13]:k1_enumset1(X12,X12,X13)=k2_tarski(X12,X13), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.14/0.37  fof(c_0_27, plain, ![X14, X15, X16]:k2_enumset1(X14,X14,X15,X16)=k1_enumset1(X14,X15,X16), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.14/0.37  fof(c_0_28, plain, ![X17, X18, X19, X20]:k3_enumset1(X17,X17,X18,X19,X20)=k2_enumset1(X17,X18,X19,X20), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.14/0.37  fof(c_0_29, plain, ![X31]:(~v1_relat_1(X31)|~v4_relat_1(X31,k1_xboole_0)|~v1_funct_1(X31)|~v1_partfun1(X31,k1_xboole_0)|~v1_yellow_1(X31)|k5_yellow_1(k1_xboole_0,X31)=g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_yellow_1])])).
% 0.14/0.37  fof(c_0_30, plain, ![X30]:(~v1_relat_1(X30)|~v4_relat_1(X30,k1_xboole_0)|~v1_funct_1(X30)|~v1_partfun1(X30,k1_xboole_0)|X30=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t134_pboole])])).
% 0.14/0.37  fof(c_0_31, plain, ![X26]:((((v1_relat_1(esk3_1(X26))&v4_relat_1(esk3_1(X26),X26))&v1_funct_1(esk3_1(X26)))&v1_partfun1(esk3_1(X26),X26))&v1_yellow_1(esk3_1(X26))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_yellow_1])])).
% 0.14/0.37  cnf(c_0_32, plain, (v1_yellow_1(k2_funcop_1(X2,X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.37  cnf(c_0_33, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.14/0.37  cnf(c_0_34, plain, (v1_xboole_0(k7_funcop_1(k1_xboole_0,X1))), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.14/0.37  cnf(c_0_35, negated_conjecture, (k6_yellow_1(k1_xboole_0,esk4_0)!=g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.37  cnf(c_0_36, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.14/0.37  cnf(c_0_37, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.14/0.37  cnf(c_0_38, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.14/0.37  cnf(c_0_39, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.14/0.37  cnf(c_0_40, plain, (k5_yellow_1(k1_xboole_0,X1)=g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))|~v1_relat_1(X1)|~v4_relat_1(X1,k1_xboole_0)|~v1_funct_1(X1)|~v1_partfun1(X1,k1_xboole_0)|~v1_yellow_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.14/0.37  cnf(c_0_41, plain, (X1=k1_xboole_0|~v1_relat_1(X1)|~v4_relat_1(X1,k1_xboole_0)|~v1_funct_1(X1)|~v1_partfun1(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.37  cnf(c_0_42, plain, (v1_partfun1(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.37  cnf(c_0_43, plain, (v1_funct_1(esk3_1(X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.37  cnf(c_0_44, plain, (v4_relat_1(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.37  cnf(c_0_45, plain, (v1_relat_1(esk3_1(X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.37  cnf(c_0_46, plain, (v1_yellow_1(k7_funcop_1(X2,X1))|~l1_orders_2(X1)), inference(rw,[status(thm)],[c_0_32, c_0_23])).
% 0.14/0.37  cnf(c_0_47, plain, (k7_funcop_1(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.14/0.37  cnf(c_0_48, negated_conjecture, (k6_yellow_1(k1_xboole_0,esk4_0)!=g1_orders_2(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39])).
% 0.14/0.37  cnf(c_0_49, plain, (k5_yellow_1(k1_xboole_0,X1)=g1_orders_2(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))|~v1_yellow_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v4_relat_1(X1,k1_xboole_0)|~v1_partfun1(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39])).
% 0.14/0.37  fof(c_0_50, plain, ![X21, X22]:(~l1_orders_2(X22)|k6_yellow_1(X21,X22)=k5_yellow_1(X21,k7_funcop_1(X21,X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_yellow_1])])).
% 0.14/0.37  cnf(c_0_51, plain, (esk3_1(k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43]), c_0_44]), c_0_45])])).
% 0.14/0.37  cnf(c_0_52, plain, (v1_yellow_1(k1_xboole_0)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.14/0.37  cnf(c_0_53, negated_conjecture, (l1_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.37  cnf(c_0_54, negated_conjecture, (k5_yellow_1(k1_xboole_0,X1)!=k6_yellow_1(k1_xboole_0,esk4_0)|~v1_partfun1(X1,k1_xboole_0)|~v1_funct_1(X1)|~v4_relat_1(X1,k1_xboole_0)|~v1_relat_1(X1)|~v1_yellow_1(X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.14/0.37  cnf(c_0_55, plain, (k6_yellow_1(X2,X1)=k5_yellow_1(X2,k7_funcop_1(X2,X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.14/0.37  cnf(c_0_56, plain, (v1_partfun1(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_42, c_0_51])).
% 0.14/0.37  cnf(c_0_57, plain, (v1_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_43, c_0_51])).
% 0.14/0.37  cnf(c_0_58, plain, (v4_relat_1(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_44, c_0_51])).
% 0.14/0.37  cnf(c_0_59, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_45, c_0_51])).
% 0.14/0.37  cnf(c_0_60, negated_conjecture, (v1_yellow_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.14/0.37  cnf(c_0_61, negated_conjecture, (k6_yellow_1(k1_xboole_0,X1)!=k6_yellow_1(k1_xboole_0,esk4_0)|~l1_orders_2(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_47]), c_0_56]), c_0_47]), c_0_57]), c_0_47]), c_0_58]), c_0_47]), c_0_59]), c_0_47]), c_0_60])])).
% 0.14/0.37  cnf(c_0_62, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_61]), c_0_53])]), ['proof']).
% 0.14/0.37  # SZS output end CNFRefutation
% 0.14/0.37  # Proof object total steps             : 63
% 0.14/0.37  # Proof object clause steps            : 34
% 0.14/0.37  # Proof object formula steps           : 29
% 0.14/0.37  # Proof object conjectures             : 10
% 0.14/0.37  # Proof object clause conjectures      : 7
% 0.14/0.37  # Proof object formula conjectures     : 3
% 0.14/0.37  # Proof object initial clauses used    : 18
% 0.14/0.37  # Proof object initial formulas used   : 14
% 0.14/0.37  # Proof object generating inferences   : 12
% 0.14/0.37  # Proof object simplifying inferences  : 35
% 0.14/0.37  # Training examples: 0 positive, 0 negative
% 0.14/0.37  # Parsed axioms                        : 14
% 0.14/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.37  # Initial clauses                      : 20
% 0.14/0.37  # Removed in clause preprocessing      : 5
% 0.14/0.37  # Initial clauses in saturation        : 15
% 0.14/0.37  # Processed clauses                    : 42
% 0.14/0.37  # ...of these trivial                  : 0
% 0.14/0.37  # ...subsumed                          : 0
% 0.14/0.37  # ...remaining for further processing  : 42
% 0.14/0.37  # Other redundant clauses eliminated   : 0
% 0.14/0.37  # Clauses deleted for lack of memory   : 0
% 0.14/0.37  # Backward-subsumed                    : 0
% 0.14/0.37  # Backward-rewritten                   : 2
% 0.14/0.37  # Generated clauses                    : 18
% 0.14/0.37  # ...of the previous two non-trivial   : 16
% 0.14/0.37  # Contextual simplify-reflections      : 0
% 0.14/0.37  # Paramodulations                      : 17
% 0.14/0.37  # Factorizations                       : 0
% 0.14/0.37  # Equation resolutions                 : 1
% 0.14/0.37  # Propositional unsat checks           : 0
% 0.14/0.37  #    Propositional check models        : 0
% 0.14/0.37  #    Propositional check unsatisfiable : 0
% 0.14/0.37  #    Propositional clauses             : 0
% 0.14/0.37  #    Propositional clauses after purity: 0
% 0.14/0.37  #    Propositional unsat core size     : 0
% 0.14/0.37  #    Propositional preprocessing time  : 0.000
% 0.14/0.37  #    Propositional encoding time       : 0.000
% 0.14/0.37  #    Propositional solver time         : 0.000
% 0.14/0.37  #    Success case prop preproc time    : 0.000
% 0.14/0.37  #    Success case prop encoding time   : 0.000
% 0.14/0.37  #    Success case prop solver time     : 0.000
% 0.14/0.37  # Current number of processed clauses  : 25
% 0.14/0.37  #    Positive orientable unit clauses  : 14
% 0.14/0.37  #    Positive unorientable unit clauses: 0
% 0.14/0.37  #    Negative unit clauses             : 1
% 0.14/0.37  #    Non-unit-clauses                  : 10
% 0.14/0.37  # Current number of unprocessed clauses: 4
% 0.14/0.37  # ...number of literals in the above   : 22
% 0.14/0.37  # Current number of archived formulas  : 0
% 0.14/0.37  # Current number of archived clauses   : 22
% 0.14/0.37  # Clause-clause subsumption calls (NU) : 57
% 0.14/0.37  # Rec. Clause-clause subsumption calls : 1
% 0.14/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.37  # Unit Clause-clause subsumption calls : 2
% 0.14/0.37  # Rewrite failures with RHS unbound    : 0
% 0.14/0.37  # BW rewrite match attempts            : 2
% 0.14/0.37  # BW rewrite match successes           : 2
% 0.14/0.37  # Condensation attempts                : 0
% 0.14/0.37  # Condensation successes               : 0
% 0.14/0.37  # Termbank termtop insertions          : 1597
% 0.14/0.37  
% 0.14/0.37  # -------------------------------------------------
% 0.14/0.37  # User time                : 0.028 s
% 0.14/0.37  # System time              : 0.004 s
% 0.14/0.37  # Total time               : 0.032 s
% 0.14/0.37  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
