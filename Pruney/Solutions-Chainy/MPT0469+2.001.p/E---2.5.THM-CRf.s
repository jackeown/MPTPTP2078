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
% DateTime   : Thu Dec  3 10:48:46 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 139 expanded)
%              Number of clauses        :   35 (  66 expanded)
%              Number of leaves         :   13 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :  148 ( 290 expanded)
%              Number of equality atoms :   65 ( 139 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t24_relat_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( v1_relat_1(X5)
     => ( X5 = k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4))
       => ( k1_relat_1(X5) = k2_tarski(X1,X3)
          & k2_relat_1(X5) = k2_tarski(X2,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relat_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(fc7_relat_1,axiom,(
    ! [X1,X2,X3,X4] : v1_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_relat_1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(cc1_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(antisymmetry_r2_hidden,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(t60_relat_1,conjecture,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(c_0_13,plain,(
    ! [X30,X31,X32,X33,X34] :
      ( ( k1_relat_1(X34) = k2_tarski(X30,X32)
        | X34 != k2_tarski(k4_tarski(X30,X31),k4_tarski(X32,X33))
        | ~ v1_relat_1(X34) )
      & ( k2_relat_1(X34) = k2_tarski(X31,X33)
        | X34 != k2_tarski(k4_tarski(X30,X31),k4_tarski(X32,X33))
        | ~ v1_relat_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_relat_1])])])).

fof(c_0_14,plain,(
    ! [X21,X22] : k1_enumset1(X21,X21,X22) = k2_tarski(X21,X22) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_15,plain,(
    ! [X26,X27,X28,X29] : v1_relat_1(k2_tarski(k4_tarski(X26,X27),k4_tarski(X28,X29))) ),
    inference(variable_rename,[status(thm)],[fc7_relat_1])).

cnf(c_0_16,plain,
    ( k1_relat_1(X1) = k2_tarski(X2,X3)
    | X1 != k2_tarski(k4_tarski(X2,X4),k4_tarski(X3,X5))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( v1_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X14,X13)
        | X14 = X11
        | X14 = X12
        | X13 != k2_tarski(X11,X12) )
      & ( X15 != X11
        | r2_hidden(X15,X13)
        | X13 != k2_tarski(X11,X12) )
      & ( X15 != X12
        | r2_hidden(X15,X13)
        | X13 != k2_tarski(X11,X12) )
      & ( esk1_3(X16,X17,X18) != X16
        | ~ r2_hidden(esk1_3(X16,X17,X18),X18)
        | X18 = k2_tarski(X16,X17) )
      & ( esk1_3(X16,X17,X18) != X17
        | ~ r2_hidden(esk1_3(X16,X17,X18),X18)
        | X18 = k2_tarski(X16,X17) )
      & ( r2_hidden(esk1_3(X16,X17,X18),X18)
        | esk1_3(X16,X17,X18) = X16
        | esk1_3(X16,X17,X18) = X17
        | X18 = k2_tarski(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_20,plain,(
    ! [X23,X24] :
      ( ( k4_xboole_0(X23,k1_tarski(X24)) != X23
        | ~ r2_hidden(X24,X23) )
      & ( r2_hidden(X24,X23)
        | k4_xboole_0(X23,k1_tarski(X24)) = X23 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

fof(c_0_21,plain,(
    ! [X20] : k2_tarski(X20,X20) = k1_tarski(X20) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_22,plain,(
    ! [X35,X36] :
      ( ( r1_tarski(k1_relat_1(X35),k1_relat_1(X36))
        | ~ r1_tarski(X35,X36)
        | ~ v1_relat_1(X36)
        | ~ v1_relat_1(X35) )
      & ( r1_tarski(k2_relat_1(X35),k2_relat_1(X36))
        | ~ r1_tarski(X35,X36)
        | ~ v1_relat_1(X36)
        | ~ v1_relat_1(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

cnf(c_0_23,plain,
    ( k1_relat_1(X1) = k1_enumset1(X2,X2,X3)
    | X1 != k1_enumset1(k4_tarski(X2,X4),k4_tarski(X2,X4),k4_tarski(X3,X5))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_17])).

cnf(c_0_24,plain,
    ( v1_relat_1(k1_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X3,X4))) ),
    inference(rw,[status(thm)],[c_0_18,c_0_17])).

fof(c_0_25,plain,(
    ! [X25] :
      ( ~ v1_xboole_0(X25)
      | v1_relat_1(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_27,plain,(
    ! [X8,X9] :
      ( ( k4_xboole_0(X8,X9) != k1_xboole_0
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | k4_xboole_0(X8,X9) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(X2,k1_tarski(X1)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k1_relat_1(k1_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X3,X4))) = k1_enumset1(X1,X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_23]),c_0_24])])).

fof(c_0_32,plain,(
    ! [X10] : r1_tarski(k1_xboole_0,X10) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_33,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_35,plain,
    ( k2_relat_1(X1) = k2_tarski(X2,X3)
    | X1 != k2_tarski(k4_tarski(X4,X2),k4_tarski(X5,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_36,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,X7)
      | ~ r2_hidden(X7,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X4,X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_17])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X2,k1_enumset1(X1,X1,X1)) = X2
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_17])).

cnf(c_0_40,plain,
    ( r1_tarski(k1_relat_1(X1),k1_enumset1(X2,X2,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,k1_enumset1(k4_tarski(X2,X4),k4_tarski(X2,X4),k4_tarski(X3,X5))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_24])])).

cnf(c_0_41,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_43,plain,
    ( k2_relat_1(X1) = k1_enumset1(X2,X2,X3)
    | X1 != k1_enumset1(k4_tarski(X4,X2),k4_tarski(X4,X2),k4_tarski(X5,X3))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_17]),c_0_17])).

fof(c_0_44,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t60_relat_1])).

cnf(c_0_45,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_37])])).

cnf(c_0_47,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,X1)
    | ~ r1_tarski(X1,k1_enumset1(X2,X2,X2)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_48,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k1_enumset1(X1,X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])])).

cnf(c_0_49,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_50,plain,
    ( k2_relat_1(k1_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X3,X4))) = k1_enumset1(X2,X2,X4) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_43]),c_0_24])])).

fof(c_0_51,negated_conjecture,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(fof_nnf,[status(thm)],[c_0_44])).

cnf(c_0_52,plain,
    ( ~ r2_hidden(k1_enumset1(X1,X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_54,plain,
    ( r1_tarski(k2_relat_1(X1),k1_enumset1(X2,X2,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,k1_enumset1(k4_tarski(X4,X2),k4_tarski(X4,X2),k4_tarski(X5,X3))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_24])])).

cnf(c_0_55,negated_conjecture,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_56,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_57,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),k1_enumset1(X1,X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_41]),c_0_42])])).

cnf(c_0_58,negated_conjecture,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_56])])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,k2_relat_1(k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_57]),c_0_58])).

cnf(c_0_60,plain,
    ( $false ),
    inference(spm,[status(thm)],[c_0_52,c_0_59]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:33:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 0.15/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.15/0.39  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.15/0.39  #
% 0.15/0.39  # Preprocessing time       : 0.027 s
% 0.15/0.39  # Presaturation interreduction done
% 0.15/0.39  
% 0.15/0.39  # Proof found!
% 0.15/0.39  # SZS status Theorem
% 0.15/0.39  # SZS output start CNFRefutation
% 0.15/0.39  fof(t24_relat_1, axiom, ![X1, X2, X3, X4, X5]:(v1_relat_1(X5)=>(X5=k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4))=>(k1_relat_1(X5)=k2_tarski(X1,X3)&k2_relat_1(X5)=k2_tarski(X2,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_relat_1)).
% 0.15/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.15/0.39  fof(fc7_relat_1, axiom, ![X1, X2, X3, X4]:v1_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_relat_1)).
% 0.15/0.39  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.15/0.39  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.15/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.15/0.39  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 0.15/0.39  fof(cc1_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 0.15/0.39  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.15/0.39  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.15/0.39  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.15/0.39  fof(antisymmetry_r2_hidden, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 0.15/0.39  fof(t60_relat_1, conjecture, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.15/0.39  fof(c_0_13, plain, ![X30, X31, X32, X33, X34]:((k1_relat_1(X34)=k2_tarski(X30,X32)|X34!=k2_tarski(k4_tarski(X30,X31),k4_tarski(X32,X33))|~v1_relat_1(X34))&(k2_relat_1(X34)=k2_tarski(X31,X33)|X34!=k2_tarski(k4_tarski(X30,X31),k4_tarski(X32,X33))|~v1_relat_1(X34))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_relat_1])])])).
% 0.15/0.39  fof(c_0_14, plain, ![X21, X22]:k1_enumset1(X21,X21,X22)=k2_tarski(X21,X22), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.15/0.39  fof(c_0_15, plain, ![X26, X27, X28, X29]:v1_relat_1(k2_tarski(k4_tarski(X26,X27),k4_tarski(X28,X29))), inference(variable_rename,[status(thm)],[fc7_relat_1])).
% 0.15/0.39  cnf(c_0_16, plain, (k1_relat_1(X1)=k2_tarski(X2,X3)|X1!=k2_tarski(k4_tarski(X2,X4),k4_tarski(X3,X5))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.15/0.39  cnf(c_0_17, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.15/0.39  cnf(c_0_18, plain, (v1_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.15/0.39  fof(c_0_19, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:(((~r2_hidden(X14,X13)|(X14=X11|X14=X12)|X13!=k2_tarski(X11,X12))&((X15!=X11|r2_hidden(X15,X13)|X13!=k2_tarski(X11,X12))&(X15!=X12|r2_hidden(X15,X13)|X13!=k2_tarski(X11,X12))))&(((esk1_3(X16,X17,X18)!=X16|~r2_hidden(esk1_3(X16,X17,X18),X18)|X18=k2_tarski(X16,X17))&(esk1_3(X16,X17,X18)!=X17|~r2_hidden(esk1_3(X16,X17,X18),X18)|X18=k2_tarski(X16,X17)))&(r2_hidden(esk1_3(X16,X17,X18),X18)|(esk1_3(X16,X17,X18)=X16|esk1_3(X16,X17,X18)=X17)|X18=k2_tarski(X16,X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.15/0.39  fof(c_0_20, plain, ![X23, X24]:((k4_xboole_0(X23,k1_tarski(X24))!=X23|~r2_hidden(X24,X23))&(r2_hidden(X24,X23)|k4_xboole_0(X23,k1_tarski(X24))=X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.15/0.39  fof(c_0_21, plain, ![X20]:k2_tarski(X20,X20)=k1_tarski(X20), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.15/0.39  fof(c_0_22, plain, ![X35, X36]:((r1_tarski(k1_relat_1(X35),k1_relat_1(X36))|~r1_tarski(X35,X36)|~v1_relat_1(X36)|~v1_relat_1(X35))&(r1_tarski(k2_relat_1(X35),k2_relat_1(X36))|~r1_tarski(X35,X36)|~v1_relat_1(X36)|~v1_relat_1(X35))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.15/0.39  cnf(c_0_23, plain, (k1_relat_1(X1)=k1_enumset1(X2,X2,X3)|X1!=k1_enumset1(k4_tarski(X2,X4),k4_tarski(X2,X4),k4_tarski(X3,X5))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_17])).
% 0.15/0.39  cnf(c_0_24, plain, (v1_relat_1(k1_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X3,X4)))), inference(rw,[status(thm)],[c_0_18, c_0_17])).
% 0.15/0.39  fof(c_0_25, plain, ![X25]:(~v1_xboole_0(X25)|v1_relat_1(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).
% 0.15/0.39  cnf(c_0_26, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.15/0.39  fof(c_0_27, plain, ![X8, X9]:((k4_xboole_0(X8,X9)!=k1_xboole_0|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|k4_xboole_0(X8,X9)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.15/0.39  cnf(c_0_28, plain, (r2_hidden(X1,X2)|k4_xboole_0(X2,k1_tarski(X1))=X2), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.15/0.39  cnf(c_0_29, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.15/0.39  cnf(c_0_30, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.15/0.39  cnf(c_0_31, plain, (k1_relat_1(k1_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X3,X4)))=k1_enumset1(X1,X1,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_23]), c_0_24])])).
% 0.15/0.39  fof(c_0_32, plain, ![X10]:r1_tarski(k1_xboole_0,X10), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.15/0.39  cnf(c_0_33, plain, (v1_relat_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.15/0.39  cnf(c_0_34, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.15/0.39  cnf(c_0_35, plain, (k2_relat_1(X1)=k2_tarski(X2,X3)|X1!=k2_tarski(k4_tarski(X4,X2),k4_tarski(X5,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.15/0.39  fof(c_0_36, plain, ![X6, X7]:(~r2_hidden(X6,X7)|~r2_hidden(X7,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).
% 0.15/0.39  cnf(c_0_37, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X4,X2)), inference(rw,[status(thm)],[c_0_26, c_0_17])).
% 0.15/0.39  cnf(c_0_38, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.15/0.39  cnf(c_0_39, plain, (k4_xboole_0(X2,k1_enumset1(X1,X1,X1))=X2|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_17])).
% 0.15/0.39  cnf(c_0_40, plain, (r1_tarski(k1_relat_1(X1),k1_enumset1(X2,X2,X3))|~v1_relat_1(X1)|~r1_tarski(X1,k1_enumset1(k4_tarski(X2,X4),k4_tarski(X2,X4),k4_tarski(X3,X5)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_24])])).
% 0.15/0.39  cnf(c_0_41, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.15/0.39  cnf(c_0_42, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.15/0.39  cnf(c_0_43, plain, (k2_relat_1(X1)=k1_enumset1(X2,X2,X3)|X1!=k1_enumset1(k4_tarski(X4,X2),k4_tarski(X4,X2),k4_tarski(X5,X3))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_17]), c_0_17])).
% 0.15/0.39  fof(c_0_44, negated_conjecture, ~((k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0)), inference(assume_negation,[status(cth)],[t60_relat_1])).
% 0.15/0.39  cnf(c_0_45, plain, (~r2_hidden(X1,X2)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.15/0.39  cnf(c_0_46, plain, (r2_hidden(X1,k1_enumset1(X2,X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_37])])).
% 0.15/0.39  cnf(c_0_47, plain, (X1=k1_xboole_0|r2_hidden(X2,X1)|~r1_tarski(X1,k1_enumset1(X2,X2,X2))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.15/0.39  cnf(c_0_48, plain, (r1_tarski(k1_relat_1(k1_xboole_0),k1_enumset1(X1,X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])])).
% 0.15/0.39  cnf(c_0_49, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.15/0.39  cnf(c_0_50, plain, (k2_relat_1(k1_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X3,X4)))=k1_enumset1(X2,X2,X4)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_43]), c_0_24])])).
% 0.15/0.39  fof(c_0_51, negated_conjecture, (k1_relat_1(k1_xboole_0)!=k1_xboole_0|k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(fof_nnf,[status(thm)],[c_0_44])).
% 0.15/0.39  cnf(c_0_52, plain, (~r2_hidden(k1_enumset1(X1,X1,X2),X2)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.15/0.39  cnf(c_0_53, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0|r2_hidden(X1,k1_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.15/0.39  cnf(c_0_54, plain, (r1_tarski(k2_relat_1(X1),k1_enumset1(X2,X2,X3))|~v1_relat_1(X1)|~r1_tarski(X1,k1_enumset1(k4_tarski(X4,X2),k4_tarski(X4,X2),k4_tarski(X5,X3)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_24])])).
% 0.15/0.39  cnf(c_0_55, negated_conjecture, (k1_relat_1(k1_xboole_0)!=k1_xboole_0|k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.15/0.39  cnf(c_0_56, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.15/0.39  cnf(c_0_57, plain, (r1_tarski(k2_relat_1(k1_xboole_0),k1_enumset1(X1,X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_41]), c_0_42])])).
% 0.15/0.39  cnf(c_0_58, negated_conjecture, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_56])])).
% 0.15/0.39  cnf(c_0_59, plain, (r2_hidden(X1,k2_relat_1(k1_xboole_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_57]), c_0_58])).
% 0.15/0.39  cnf(c_0_60, plain, ($false), inference(spm,[status(thm)],[c_0_52, c_0_59]), ['proof']).
% 0.15/0.39  # SZS output end CNFRefutation
% 0.15/0.39  # Proof object total steps             : 61
% 0.15/0.39  # Proof object clause steps            : 35
% 0.15/0.39  # Proof object formula steps           : 26
% 0.15/0.39  # Proof object conjectures             : 5
% 0.15/0.39  # Proof object clause conjectures      : 2
% 0.15/0.39  # Proof object formula conjectures     : 3
% 0.15/0.39  # Proof object initial clauses used    : 15
% 0.15/0.39  # Proof object initial formulas used   : 13
% 0.15/0.39  # Proof object generating inferences   : 11
% 0.15/0.39  # Proof object simplifying inferences  : 27
% 0.15/0.39  # Training examples: 0 positive, 0 negative
% 0.15/0.39  # Parsed axioms                        : 13
% 0.15/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.39  # Initial clauses                      : 22
% 0.15/0.39  # Removed in clause preprocessing      : 2
% 0.15/0.39  # Initial clauses in saturation        : 20
% 0.15/0.39  # Processed clauses                    : 71
% 0.15/0.39  # ...of these trivial                  : 0
% 0.15/0.39  # ...subsumed                          : 4
% 0.15/0.39  # ...remaining for further processing  : 67
% 0.15/0.39  # Other redundant clauses eliminated   : 34
% 0.15/0.39  # Clauses deleted for lack of memory   : 0
% 0.15/0.39  # Backward-subsumed                    : 0
% 0.15/0.39  # Backward-rewritten                   : 3
% 0.15/0.39  # Generated clauses                    : 256
% 0.15/0.39  # ...of the previous two non-trivial   : 200
% 0.15/0.39  # Contextual simplify-reflections      : 0
% 0.15/0.39  # Paramodulations                      : 204
% 0.15/0.39  # Factorizations                       : 20
% 0.15/0.39  # Equation resolutions                 : 34
% 0.15/0.39  # Propositional unsat checks           : 0
% 0.15/0.39  #    Propositional check models        : 0
% 0.15/0.39  #    Propositional check unsatisfiable : 0
% 0.15/0.39  #    Propositional clauses             : 0
% 0.15/0.39  #    Propositional clauses after purity: 0
% 0.15/0.39  #    Propositional unsat core size     : 0
% 0.15/0.39  #    Propositional preprocessing time  : 0.000
% 0.15/0.39  #    Propositional encoding time       : 0.000
% 0.15/0.39  #    Propositional solver time         : 0.000
% 0.15/0.39  #    Success case prop preproc time    : 0.000
% 0.15/0.39  #    Success case prop encoding time   : 0.000
% 0.15/0.39  #    Success case prop solver time     : 0.000
% 0.15/0.39  # Current number of processed clauses  : 39
% 0.15/0.39  #    Positive orientable unit clauses  : 11
% 0.15/0.39  #    Positive unorientable unit clauses: 0
% 0.15/0.39  #    Negative unit clauses             : 4
% 0.15/0.39  #    Non-unit-clauses                  : 24
% 0.15/0.39  # Current number of unprocessed clauses: 161
% 0.15/0.39  # ...number of literals in the above   : 876
% 0.15/0.39  # Current number of archived formulas  : 0
% 0.15/0.39  # Current number of archived clauses   : 25
% 0.15/0.39  # Clause-clause subsumption calls (NU) : 169
% 0.15/0.39  # Rec. Clause-clause subsumption calls : 124
% 0.15/0.39  # Non-unit clause-clause subsumptions  : 3
% 0.15/0.39  # Unit Clause-clause subsumption calls : 12
% 0.15/0.39  # Rewrite failures with RHS unbound    : 0
% 0.15/0.39  # BW rewrite match attempts            : 3
% 0.15/0.39  # BW rewrite match successes           : 1
% 0.15/0.39  # Condensation attempts                : 0
% 0.15/0.39  # Condensation successes               : 0
% 0.15/0.39  # Termbank termtop insertions          : 5001
% 0.15/0.39  
% 0.15/0.39  # -------------------------------------------------
% 0.15/0.39  # User time                : 0.036 s
% 0.15/0.39  # System time              : 0.002 s
% 0.15/0.39  # Total time               : 0.038 s
% 0.15/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
