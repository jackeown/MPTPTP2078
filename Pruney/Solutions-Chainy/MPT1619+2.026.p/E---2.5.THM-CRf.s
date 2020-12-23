%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:04 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 152 expanded)
%              Number of clauses        :   30 (  67 expanded)
%              Number of leaves         :   12 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :  100 ( 237 expanded)
%              Number of equality atoms :   32 ( 103 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t27_yellow_1,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => k6_yellow_1(k1_xboole_0,X1) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_1)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t26_yellow_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v4_relat_1(X1,k1_xboole_0)
        & v1_funct_1(X1)
        & v1_partfun1(X1,k1_xboole_0)
        & v1_yellow_1(X1) )
     => k5_yellow_1(k1_xboole_0,X1) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow_1)).

fof(fc2_funcop_1,axiom,(
    ! [X1] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funcop_1)).

fof(redefinition_k7_funcop_1,axiom,(
    ! [X1,X2] : k7_funcop_1(X1,X2) = k2_funcop_1(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(fc11_funct_2,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v4_relat_1(k6_relat_1(X1),X1)
      & v1_funct_1(k6_relat_1(X1))
      & v1_partfun1(k6_relat_1(X1),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_funct_2)).

fof(d5_yellow_1,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X2)
     => k6_yellow_1(X1,X2) = k5_yellow_1(X1,k7_funcop_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_yellow_1)).

fof(t81_relat_1,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(fc10_yellow_1,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X2)
     => v1_yellow_1(k2_funcop_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_yellow_1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => k6_yellow_1(k1_xboole_0,X1) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    inference(assume_negation,[status(cth)],[t27_yellow_1])).

fof(c_0_13,negated_conjecture,
    ( l1_orders_2(esk1_0)
    & k6_yellow_1(k1_xboole_0,esk1_0) != g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_14,plain,(
    ! [X8] : k6_partfun1(X8) = k6_relat_1(X8) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_15,plain,(
    ! [X4] : k2_tarski(X4,X4) = k1_tarski(X4) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_16,plain,(
    ! [X5,X6] : k1_enumset1(X5,X5,X6) = k2_tarski(X5,X6) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_17,plain,(
    ! [X16] :
      ( ~ v1_relat_1(X16)
      | ~ v4_relat_1(X16,k1_xboole_0)
      | ~ v1_funct_1(X16)
      | ~ v1_partfun1(X16,k1_xboole_0)
      | ~ v1_yellow_1(X16)
      | k5_yellow_1(k1_xboole_0,X16) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_yellow_1])])).

fof(c_0_18,plain,(
    ! [X13] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X13)) ),
    inference(variable_rename,[status(thm)],[fc2_funcop_1])).

fof(c_0_19,plain,(
    ! [X14,X15] : k7_funcop_1(X14,X15) = k2_funcop_1(X14,X15) ),
    inference(variable_rename,[status(thm)],[redefinition_k7_funcop_1])).

cnf(c_0_20,negated_conjecture,
    ( k6_yellow_1(k1_xboole_0,esk1_0) != g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k5_yellow_1(k1_xboole_0,X1) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,k1_xboole_0)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,k1_xboole_0)
    | ~ v1_yellow_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_25,plain,(
    ! [X3] :
      ( ~ v1_xboole_0(X3)
      | X3 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_26,plain,
    ( v1_xboole_0(k2_funcop_1(k1_xboole_0,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k7_funcop_1(X1,X2) = k2_funcop_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_28,plain,(
    ! [X7] :
      ( v1_relat_1(k6_relat_1(X7))
      & v4_relat_1(k6_relat_1(X7),X7)
      & v1_funct_1(k6_relat_1(X7))
      & v1_partfun1(k6_relat_1(X7),X7) ) ),
    inference(variable_rename,[status(thm)],[fc11_funct_2])).

cnf(c_0_29,negated_conjecture,
    ( k6_yellow_1(k1_xboole_0,esk1_0) != g1_orders_2(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_22]),c_0_23]),c_0_23])).

cnf(c_0_30,plain,
    ( k5_yellow_1(k1_xboole_0,X1) = g1_orders_2(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_yellow_1(X1)
    | ~ v4_relat_1(X1,k1_xboole_0)
    | ~ v1_partfun1(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_21]),c_0_22]),c_0_22]),c_0_23]),c_0_23])).

fof(c_0_31,plain,(
    ! [X9,X10] :
      ( ~ l1_orders_2(X10)
      | k6_yellow_1(X9,X10) = k5_yellow_1(X9,k7_funcop_1(X9,X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_yellow_1])])).

cnf(c_0_32,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( v1_xboole_0(k7_funcop_1(k1_xboole_0,X1)) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,plain,
    ( v1_partfun1(k6_relat_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t81_relat_1])).

cnf(c_0_36,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( v4_relat_1(k6_relat_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_39,plain,(
    ! [X11,X12] :
      ( ~ l1_orders_2(X12)
      | v1_yellow_1(k2_funcop_1(X11,X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_yellow_1])])).

cnf(c_0_40,negated_conjecture,
    ( k5_yellow_1(k1_xboole_0,X1) != k6_yellow_1(k1_xboole_0,esk1_0)
    | ~ v1_yellow_1(X1)
    | ~ v1_partfun1(X1,k1_xboole_0)
    | ~ v1_funct_1(X1)
    | ~ v4_relat_1(X1,k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_41,plain,
    ( k6_yellow_1(X2,X1) = k5_yellow_1(X2,k7_funcop_1(X2,X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,plain,
    ( k7_funcop_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_43,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_44,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_35])).

cnf(c_0_45,plain,
    ( v4_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_35])).

cnf(c_0_46,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_35])).

cnf(c_0_47,plain,
    ( v1_yellow_1(k2_funcop_1(X2,X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( k6_yellow_1(k1_xboole_0,X1) != k6_yellow_1(k1_xboole_0,esk1_0)
    | ~ v1_yellow_1(k1_xboole_0)
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_42]),c_0_43]),c_0_42]),c_0_44]),c_0_42]),c_0_45]),c_0_42]),c_0_46])])).

cnf(c_0_49,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_50,plain,
    ( v1_yellow_1(k7_funcop_1(X2,X1))
    | ~ l1_orders_2(X1) ),
    inference(rw,[status(thm)],[c_0_47,c_0_27])).

cnf(c_0_51,negated_conjecture,
    ( ~ v1_yellow_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_48]),c_0_49])])).

cnf(c_0_52,plain,
    ( ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_42]),c_0_51])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_49,c_0_52]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:23:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.027 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t27_yellow_1, conjecture, ![X1]:(l1_orders_2(X1)=>k6_yellow_1(k1_xboole_0,X1)=g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_yellow_1)).
% 0.14/0.38  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.14/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.14/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.14/0.38  fof(t26_yellow_1, axiom, ![X1]:(((((v1_relat_1(X1)&v4_relat_1(X1,k1_xboole_0))&v1_funct_1(X1))&v1_partfun1(X1,k1_xboole_0))&v1_yellow_1(X1))=>k5_yellow_1(k1_xboole_0,X1)=g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_yellow_1)).
% 0.14/0.38  fof(fc2_funcop_1, axiom, ![X1]:v1_xboole_0(k2_funcop_1(k1_xboole_0,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funcop_1)).
% 0.14/0.38  fof(redefinition_k7_funcop_1, axiom, ![X1, X2]:k7_funcop_1(X1,X2)=k2_funcop_1(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_funcop_1)).
% 0.14/0.38  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.14/0.38  fof(fc11_funct_2, axiom, ![X1]:(((v1_relat_1(k6_relat_1(X1))&v4_relat_1(k6_relat_1(X1),X1))&v1_funct_1(k6_relat_1(X1)))&v1_partfun1(k6_relat_1(X1),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc11_funct_2)).
% 0.14/0.38  fof(d5_yellow_1, axiom, ![X1, X2]:(l1_orders_2(X2)=>k6_yellow_1(X1,X2)=k5_yellow_1(X1,k7_funcop_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_yellow_1)).
% 0.14/0.38  fof(t81_relat_1, axiom, k6_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 0.14/0.38  fof(fc10_yellow_1, axiom, ![X1, X2]:(l1_orders_2(X2)=>v1_yellow_1(k2_funcop_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_yellow_1)).
% 0.14/0.38  fof(c_0_12, negated_conjecture, ~(![X1]:(l1_orders_2(X1)=>k6_yellow_1(k1_xboole_0,X1)=g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))))), inference(assume_negation,[status(cth)],[t27_yellow_1])).
% 0.14/0.38  fof(c_0_13, negated_conjecture, (l1_orders_2(esk1_0)&k6_yellow_1(k1_xboole_0,esk1_0)!=g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.14/0.38  fof(c_0_14, plain, ![X8]:k6_partfun1(X8)=k6_relat_1(X8), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.14/0.38  fof(c_0_15, plain, ![X4]:k2_tarski(X4,X4)=k1_tarski(X4), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.14/0.38  fof(c_0_16, plain, ![X5, X6]:k1_enumset1(X5,X5,X6)=k2_tarski(X5,X6), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.14/0.38  fof(c_0_17, plain, ![X16]:(~v1_relat_1(X16)|~v4_relat_1(X16,k1_xboole_0)|~v1_funct_1(X16)|~v1_partfun1(X16,k1_xboole_0)|~v1_yellow_1(X16)|k5_yellow_1(k1_xboole_0,X16)=g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_yellow_1])])).
% 0.14/0.38  fof(c_0_18, plain, ![X13]:v1_xboole_0(k2_funcop_1(k1_xboole_0,X13)), inference(variable_rename,[status(thm)],[fc2_funcop_1])).
% 0.14/0.38  fof(c_0_19, plain, ![X14, X15]:k7_funcop_1(X14,X15)=k2_funcop_1(X14,X15), inference(variable_rename,[status(thm)],[redefinition_k7_funcop_1])).
% 0.14/0.38  cnf(c_0_20, negated_conjecture, (k6_yellow_1(k1_xboole_0,esk1_0)!=g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_21, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.38  cnf(c_0_22, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  cnf(c_0_23, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.38  cnf(c_0_24, plain, (k5_yellow_1(k1_xboole_0,X1)=g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))|~v1_relat_1(X1)|~v4_relat_1(X1,k1_xboole_0)|~v1_funct_1(X1)|~v1_partfun1(X1,k1_xboole_0)|~v1_yellow_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.38  fof(c_0_25, plain, ![X3]:(~v1_xboole_0(X3)|X3=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.14/0.38  cnf(c_0_26, plain, (v1_xboole_0(k2_funcop_1(k1_xboole_0,X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.38  cnf(c_0_27, plain, (k7_funcop_1(X1,X2)=k2_funcop_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.38  fof(c_0_28, plain, ![X7]:(((v1_relat_1(k6_relat_1(X7))&v4_relat_1(k6_relat_1(X7),X7))&v1_funct_1(k6_relat_1(X7)))&v1_partfun1(k6_relat_1(X7),X7)), inference(variable_rename,[status(thm)],[fc11_funct_2])).
% 0.14/0.38  cnf(c_0_29, negated_conjecture, (k6_yellow_1(k1_xboole_0,esk1_0)!=g1_orders_2(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_22]), c_0_23]), c_0_23])).
% 0.14/0.38  cnf(c_0_30, plain, (k5_yellow_1(k1_xboole_0,X1)=g1_orders_2(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_yellow_1(X1)|~v4_relat_1(X1,k1_xboole_0)|~v1_partfun1(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_21]), c_0_22]), c_0_22]), c_0_23]), c_0_23])).
% 0.14/0.38  fof(c_0_31, plain, ![X9, X10]:(~l1_orders_2(X10)|k6_yellow_1(X9,X10)=k5_yellow_1(X9,k7_funcop_1(X9,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_yellow_1])])).
% 0.14/0.38  cnf(c_0_32, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.14/0.38  cnf(c_0_33, plain, (v1_xboole_0(k7_funcop_1(k1_xboole_0,X1))), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.14/0.38  cnf(c_0_34, plain, (v1_partfun1(k6_relat_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.14/0.38  cnf(c_0_35, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t81_relat_1])).
% 0.14/0.38  cnf(c_0_36, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.14/0.38  cnf(c_0_37, plain, (v4_relat_1(k6_relat_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.14/0.38  cnf(c_0_38, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.14/0.38  fof(c_0_39, plain, ![X11, X12]:(~l1_orders_2(X12)|v1_yellow_1(k2_funcop_1(X11,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_yellow_1])])).
% 0.14/0.38  cnf(c_0_40, negated_conjecture, (k5_yellow_1(k1_xboole_0,X1)!=k6_yellow_1(k1_xboole_0,esk1_0)|~v1_yellow_1(X1)|~v1_partfun1(X1,k1_xboole_0)|~v1_funct_1(X1)|~v4_relat_1(X1,k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.14/0.38  cnf(c_0_41, plain, (k6_yellow_1(X2,X1)=k5_yellow_1(X2,k7_funcop_1(X2,X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.38  cnf(c_0_42, plain, (k7_funcop_1(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.14/0.38  cnf(c_0_43, plain, (v1_partfun1(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.14/0.38  cnf(c_0_44, plain, (v1_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_36, c_0_35])).
% 0.14/0.38  cnf(c_0_45, plain, (v4_relat_1(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_37, c_0_35])).
% 0.14/0.38  cnf(c_0_46, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_38, c_0_35])).
% 0.14/0.38  cnf(c_0_47, plain, (v1_yellow_1(k2_funcop_1(X2,X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.14/0.38  cnf(c_0_48, negated_conjecture, (k6_yellow_1(k1_xboole_0,X1)!=k6_yellow_1(k1_xboole_0,esk1_0)|~v1_yellow_1(k1_xboole_0)|~l1_orders_2(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42]), c_0_42]), c_0_43]), c_0_42]), c_0_44]), c_0_42]), c_0_45]), c_0_42]), c_0_46])])).
% 0.14/0.38  cnf(c_0_49, negated_conjecture, (l1_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_50, plain, (v1_yellow_1(k7_funcop_1(X2,X1))|~l1_orders_2(X1)), inference(rw,[status(thm)],[c_0_47, c_0_27])).
% 0.14/0.38  cnf(c_0_51, negated_conjecture, (~v1_yellow_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_48]), c_0_49])])).
% 0.14/0.38  cnf(c_0_52, plain, (~l1_orders_2(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_42]), c_0_51])).
% 0.14/0.38  cnf(c_0_53, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_49, c_0_52]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 54
% 0.14/0.38  # Proof object clause steps            : 30
% 0.14/0.38  # Proof object formula steps           : 24
% 0.14/0.38  # Proof object conjectures             : 10
% 0.14/0.38  # Proof object clause conjectures      : 7
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 16
% 0.14/0.38  # Proof object initial formulas used   : 12
% 0.14/0.38  # Proof object generating inferences   : 9
% 0.14/0.38  # Proof object simplifying inferences  : 26
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 12
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 16
% 0.14/0.38  # Removed in clause preprocessing      : 4
% 0.14/0.38  # Initial clauses in saturation        : 12
% 0.14/0.38  # Processed clauses                    : 35
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 1
% 0.14/0.38  # ...remaining for further processing  : 34
% 0.14/0.38  # Other redundant clauses eliminated   : 0
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 0
% 0.14/0.38  # Backward-rewritten                   : 1
% 0.14/0.38  # Generated clauses                    : 14
% 0.14/0.38  # ...of the previous two non-trivial   : 14
% 0.14/0.38  # Contextual simplify-reflections      : 0
% 0.14/0.38  # Paramodulations                      : 12
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 1
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
% 0.14/0.38  # Current number of processed clauses  : 20
% 0.14/0.38  #    Positive orientable unit clauses  : 11
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 3
% 0.14/0.38  #    Non-unit-clauses                  : 6
% 0.14/0.38  # Current number of unprocessed clauses: 3
% 0.14/0.38  # ...number of literals in the above   : 16
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 18
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 0
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 0
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.38  # Unit Clause-clause subsumption calls : 7
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 1
% 0.14/0.38  # BW rewrite match successes           : 1
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 1122
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.029 s
% 0.14/0.38  # System time              : 0.002 s
% 0.14/0.38  # Total time               : 0.031 s
% 0.14/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
