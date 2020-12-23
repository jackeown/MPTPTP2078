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

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 199 expanded)
%              Number of clauses        :   29 (  83 expanded)
%              Number of leaves         :   10 (  57 expanded)
%              Depth                    :    8
%              Number of atoms          :  111 ( 515 expanded)
%              Number of equality atoms :   32 (  97 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t27_yellow_1,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => k6_yellow_1(k1_xboole_0,X1) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t26_yellow_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v4_relat_1(X1,k1_xboole_0)
        & v1_funct_1(X1)
        & v1_partfun1(X1,k1_xboole_0)
        & v1_yellow_1(X1) )
     => k5_yellow_1(k1_xboole_0,X1) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_1)).

fof(fc2_funcop_1,axiom,(
    ! [X1] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funcop_1)).

fof(redefinition_k7_funcop_1,axiom,(
    ! [X1,X2] : k7_funcop_1(X1,X2) = k2_funcop_1(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

fof(t134_pboole,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v4_relat_1(X1,k1_xboole_0)
        & v1_funct_1(X1)
        & v1_partfun1(X1,k1_xboole_0) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_pboole)).

fof(rc1_yellow_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( v1_relat_1(X2)
      & v4_relat_1(X2,X1)
      & v1_funct_1(X2)
      & v1_partfun1(X2,X1)
      & v1_yellow_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_yellow_1)).

fof(d5_yellow_1,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X2)
     => k6_yellow_1(X1,X2) = k5_yellow_1(X1,k7_funcop_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_yellow_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => k6_yellow_1(k1_xboole_0,X1) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    inference(assume_negation,[status(cth)],[t27_yellow_1])).

fof(c_0_11,negated_conjecture,
    ( l1_orders_2(esk2_0)
    & k6_yellow_1(k1_xboole_0,esk2_0) != g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_12,plain,(
    ! [X4] : k2_tarski(X4,X4) = k1_tarski(X4) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_13,plain,(
    ! [X5,X6] : k1_enumset1(X5,X5,X6) = k2_tarski(X5,X6) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_14,plain,(
    ! [X15] :
      ( ~ v1_relat_1(X15)
      | ~ v4_relat_1(X15,k1_xboole_0)
      | ~ v1_funct_1(X15)
      | ~ v1_partfun1(X15,k1_xboole_0)
      | ~ v1_yellow_1(X15)
      | k5_yellow_1(k1_xboole_0,X15) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_yellow_1])])).

cnf(c_0_15,negated_conjecture,
    ( k6_yellow_1(k1_xboole_0,esk2_0) != g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k5_yellow_1(k1_xboole_0,X1) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,k1_xboole_0)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,k1_xboole_0)
    | ~ v1_yellow_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X9] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X9)) ),
    inference(variable_rename,[status(thm)],[fc2_funcop_1])).

fof(c_0_20,plain,(
    ! [X12,X13] : k7_funcop_1(X12,X13) = k2_funcop_1(X12,X13) ),
    inference(variable_rename,[status(thm)],[redefinition_k7_funcop_1])).

fof(c_0_21,plain,(
    ! [X14] :
      ( ~ v1_relat_1(X14)
      | ~ v4_relat_1(X14,k1_xboole_0)
      | ~ v1_funct_1(X14)
      | ~ v1_partfun1(X14,k1_xboole_0)
      | X14 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t134_pboole])])).

fof(c_0_22,plain,(
    ! [X10] :
      ( v1_relat_1(esk1_1(X10))
      & v4_relat_1(esk1_1(X10),X10)
      & v1_funct_1(esk1_1(X10))
      & v1_partfun1(esk1_1(X10),X10)
      & v1_yellow_1(esk1_1(X10)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_yellow_1])])).

cnf(c_0_23,negated_conjecture,
    ( k6_yellow_1(k1_xboole_0,esk2_0) != g1_orders_2(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_16]),c_0_17]),c_0_17])).

cnf(c_0_24,plain,
    ( k5_yellow_1(k1_xboole_0,X1) = g1_orders_2(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_yellow_1(X1)
    | ~ v4_relat_1(X1,k1_xboole_0)
    | ~ v1_partfun1(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_16]),c_0_16]),c_0_17]),c_0_17])).

fof(c_0_25,plain,(
    ! [X7,X8] :
      ( ~ l1_orders_2(X8)
      | k6_yellow_1(X7,X8) = k5_yellow_1(X7,k7_funcop_1(X7,X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_yellow_1])])).

fof(c_0_26,plain,(
    ! [X3] :
      ( ~ v1_xboole_0(X3)
      | X3 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_27,plain,
    ( v1_xboole_0(k2_funcop_1(k1_xboole_0,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( k7_funcop_1(X1,X2) = k2_funcop_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( X1 = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,k1_xboole_0)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( v1_partfun1(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( v1_funct_1(esk1_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( v4_relat_1(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( v1_relat_1(esk1_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( k5_yellow_1(k1_xboole_0,X1) != k6_yellow_1(k1_xboole_0,esk2_0)
    | ~ v1_yellow_1(X1)
    | ~ v1_partfun1(X1,k1_xboole_0)
    | ~ v1_funct_1(X1)
    | ~ v4_relat_1(X1,k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_35,plain,
    ( k6_yellow_1(X2,X1) = k5_yellow_1(X2,k7_funcop_1(X2,X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( v1_xboole_0(k7_funcop_1(k1_xboole_0,X1)) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_38,plain,
    ( v1_yellow_1(esk1_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_39,plain,
    ( esk1_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32]),c_0_33])])).

cnf(c_0_40,negated_conjecture,
    ( k6_yellow_1(k1_xboole_0,X1) != k6_yellow_1(k1_xboole_0,esk2_0)
    | ~ v1_yellow_1(k7_funcop_1(k1_xboole_0,X1))
    | ~ v1_partfun1(k7_funcop_1(k1_xboole_0,X1),k1_xboole_0)
    | ~ v1_funct_1(k7_funcop_1(k1_xboole_0,X1))
    | ~ v4_relat_1(k7_funcop_1(k1_xboole_0,X1),k1_xboole_0)
    | ~ v1_relat_1(k7_funcop_1(k1_xboole_0,X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,plain,
    ( k7_funcop_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,plain,
    ( v1_yellow_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_43,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_39])).

cnf(c_0_44,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_39])).

cnf(c_0_45,plain,
    ( v4_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_39])).

cnf(c_0_46,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( k6_yellow_1(k1_xboole_0,X1) != k6_yellow_1(k1_xboole_0,esk2_0)
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_41]),c_0_43]),c_0_41]),c_0_44]),c_0_41]),c_0_45]),c_0_41]),c_0_46])])).

cnf(c_0_48,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_47]),c_0_48])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:43:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.027 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t27_yellow_1, conjecture, ![X1]:(l1_orders_2(X1)=>k6_yellow_1(k1_xboole_0,X1)=g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_yellow_1)).
% 0.19/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.37  fof(t26_yellow_1, axiom, ![X1]:(((((v1_relat_1(X1)&v4_relat_1(X1,k1_xboole_0))&v1_funct_1(X1))&v1_partfun1(X1,k1_xboole_0))&v1_yellow_1(X1))=>k5_yellow_1(k1_xboole_0,X1)=g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_yellow_1)).
% 0.19/0.37  fof(fc2_funcop_1, axiom, ![X1]:v1_xboole_0(k2_funcop_1(k1_xboole_0,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_funcop_1)).
% 0.19/0.37  fof(redefinition_k7_funcop_1, axiom, ![X1, X2]:k7_funcop_1(X1,X2)=k2_funcop_1(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_funcop_1)).
% 0.19/0.37  fof(t134_pboole, axiom, ![X1]:((((v1_relat_1(X1)&v4_relat_1(X1,k1_xboole_0))&v1_funct_1(X1))&v1_partfun1(X1,k1_xboole_0))=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_pboole)).
% 0.19/0.37  fof(rc1_yellow_1, axiom, ![X1]:?[X2]:((((v1_relat_1(X2)&v4_relat_1(X2,X1))&v1_funct_1(X2))&v1_partfun1(X2,X1))&v1_yellow_1(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_yellow_1)).
% 0.19/0.37  fof(d5_yellow_1, axiom, ![X1, X2]:(l1_orders_2(X2)=>k6_yellow_1(X1,X2)=k5_yellow_1(X1,k7_funcop_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_yellow_1)).
% 0.19/0.37  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.19/0.37  fof(c_0_10, negated_conjecture, ~(![X1]:(l1_orders_2(X1)=>k6_yellow_1(k1_xboole_0,X1)=g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))))), inference(assume_negation,[status(cth)],[t27_yellow_1])).
% 0.19/0.37  fof(c_0_11, negated_conjecture, (l1_orders_2(esk2_0)&k6_yellow_1(k1_xboole_0,esk2_0)!=g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.19/0.37  fof(c_0_12, plain, ![X4]:k2_tarski(X4,X4)=k1_tarski(X4), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.37  fof(c_0_13, plain, ![X5, X6]:k1_enumset1(X5,X5,X6)=k2_tarski(X5,X6), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.37  fof(c_0_14, plain, ![X15]:(~v1_relat_1(X15)|~v4_relat_1(X15,k1_xboole_0)|~v1_funct_1(X15)|~v1_partfun1(X15,k1_xboole_0)|~v1_yellow_1(X15)|k5_yellow_1(k1_xboole_0,X15)=g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_yellow_1])])).
% 0.19/0.37  cnf(c_0_15, negated_conjecture, (k6_yellow_1(k1_xboole_0,esk2_0)!=g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.37  cnf(c_0_16, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  cnf(c_0_17, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_18, plain, (k5_yellow_1(k1_xboole_0,X1)=g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))|~v1_relat_1(X1)|~v4_relat_1(X1,k1_xboole_0)|~v1_funct_1(X1)|~v1_partfun1(X1,k1_xboole_0)|~v1_yellow_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  fof(c_0_19, plain, ![X9]:v1_xboole_0(k2_funcop_1(k1_xboole_0,X9)), inference(variable_rename,[status(thm)],[fc2_funcop_1])).
% 0.19/0.37  fof(c_0_20, plain, ![X12, X13]:k7_funcop_1(X12,X13)=k2_funcop_1(X12,X13), inference(variable_rename,[status(thm)],[redefinition_k7_funcop_1])).
% 0.19/0.37  fof(c_0_21, plain, ![X14]:(~v1_relat_1(X14)|~v4_relat_1(X14,k1_xboole_0)|~v1_funct_1(X14)|~v1_partfun1(X14,k1_xboole_0)|X14=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t134_pboole])])).
% 0.19/0.37  fof(c_0_22, plain, ![X10]:((((v1_relat_1(esk1_1(X10))&v4_relat_1(esk1_1(X10),X10))&v1_funct_1(esk1_1(X10)))&v1_partfun1(esk1_1(X10),X10))&v1_yellow_1(esk1_1(X10))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_yellow_1])])).
% 0.19/0.37  cnf(c_0_23, negated_conjecture, (k6_yellow_1(k1_xboole_0,esk2_0)!=g1_orders_2(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_16]), c_0_17]), c_0_17])).
% 0.19/0.37  cnf(c_0_24, plain, (k5_yellow_1(k1_xboole_0,X1)=g1_orders_2(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_yellow_1(X1)|~v4_relat_1(X1,k1_xboole_0)|~v1_partfun1(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_16]), c_0_16]), c_0_17]), c_0_17])).
% 0.19/0.37  fof(c_0_25, plain, ![X7, X8]:(~l1_orders_2(X8)|k6_yellow_1(X7,X8)=k5_yellow_1(X7,k7_funcop_1(X7,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_yellow_1])])).
% 0.19/0.37  fof(c_0_26, plain, ![X3]:(~v1_xboole_0(X3)|X3=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.19/0.37  cnf(c_0_27, plain, (v1_xboole_0(k2_funcop_1(k1_xboole_0,X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.37  cnf(c_0_28, plain, (k7_funcop_1(X1,X2)=k2_funcop_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.37  cnf(c_0_29, plain, (X1=k1_xboole_0|~v1_relat_1(X1)|~v4_relat_1(X1,k1_xboole_0)|~v1_funct_1(X1)|~v1_partfun1(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.37  cnf(c_0_30, plain, (v1_partfun1(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.37  cnf(c_0_31, plain, (v1_funct_1(esk1_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.37  cnf(c_0_32, plain, (v4_relat_1(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.37  cnf(c_0_33, plain, (v1_relat_1(esk1_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.37  cnf(c_0_34, negated_conjecture, (k5_yellow_1(k1_xboole_0,X1)!=k6_yellow_1(k1_xboole_0,esk2_0)|~v1_yellow_1(X1)|~v1_partfun1(X1,k1_xboole_0)|~v1_funct_1(X1)|~v4_relat_1(X1,k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.37  cnf(c_0_35, plain, (k6_yellow_1(X2,X1)=k5_yellow_1(X2,k7_funcop_1(X2,X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.37  cnf(c_0_36, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.37  cnf(c_0_37, plain, (v1_xboole_0(k7_funcop_1(k1_xboole_0,X1))), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.37  cnf(c_0_38, plain, (v1_yellow_1(esk1_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.37  cnf(c_0_39, plain, (esk1_1(k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32]), c_0_33])])).
% 0.19/0.37  cnf(c_0_40, negated_conjecture, (k6_yellow_1(k1_xboole_0,X1)!=k6_yellow_1(k1_xboole_0,esk2_0)|~v1_yellow_1(k7_funcop_1(k1_xboole_0,X1))|~v1_partfun1(k7_funcop_1(k1_xboole_0,X1),k1_xboole_0)|~v1_funct_1(k7_funcop_1(k1_xboole_0,X1))|~v4_relat_1(k7_funcop_1(k1_xboole_0,X1),k1_xboole_0)|~v1_relat_1(k7_funcop_1(k1_xboole_0,X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.37  cnf(c_0_41, plain, (k7_funcop_1(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.37  cnf(c_0_42, plain, (v1_yellow_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.37  cnf(c_0_43, plain, (v1_partfun1(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_30, c_0_39])).
% 0.19/0.37  cnf(c_0_44, plain, (v1_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_31, c_0_39])).
% 0.19/0.37  cnf(c_0_45, plain, (v4_relat_1(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_32, c_0_39])).
% 0.19/0.37  cnf(c_0_46, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_33, c_0_39])).
% 0.19/0.37  cnf(c_0_47, negated_conjecture, (k6_yellow_1(k1_xboole_0,X1)!=k6_yellow_1(k1_xboole_0,esk2_0)|~l1_orders_2(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41]), c_0_42]), c_0_41]), c_0_43]), c_0_41]), c_0_44]), c_0_41]), c_0_45]), c_0_41]), c_0_46])])).
% 0.19/0.37  cnf(c_0_48, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.37  cnf(c_0_49, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_47]), c_0_48])]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 50
% 0.19/0.37  # Proof object clause steps            : 29
% 0.19/0.37  # Proof object formula steps           : 21
% 0.19/0.37  # Proof object conjectures             : 10
% 0.19/0.37  # Proof object clause conjectures      : 7
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 15
% 0.19/0.37  # Proof object initial formulas used   : 10
% 0.19/0.37  # Proof object generating inferences   : 10
% 0.19/0.37  # Proof object simplifying inferences  : 26
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 10
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 15
% 0.19/0.37  # Removed in clause preprocessing      : 3
% 0.19/0.37  # Initial clauses in saturation        : 12
% 0.19/0.37  # Processed clauses                    : 36
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 1
% 0.19/0.37  # ...remaining for further processing  : 35
% 0.19/0.37  # Other redundant clauses eliminated   : 0
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 2
% 0.19/0.37  # Generated clauses                    : 14
% 0.19/0.37  # ...of the previous two non-trivial   : 15
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 13
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 1
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 21
% 0.19/0.37  #    Positive orientable unit clauses  : 14
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 1
% 0.19/0.37  #    Non-unit-clauses                  : 6
% 0.19/0.37  # Current number of unprocessed clauses: 3
% 0.19/0.37  # ...number of literals in the above   : 20
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 17
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 53
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 2
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.37  # Unit Clause-clause subsumption calls : 1
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 1
% 0.19/0.37  # BW rewrite match successes           : 1
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 1247
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.029 s
% 0.19/0.37  # System time              : 0.003 s
% 0.19/0.37  # Total time               : 0.032 s
% 0.19/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
