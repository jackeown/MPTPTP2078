%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:47 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   49 (  64 expanded)
%              Number of clauses        :   28 (  28 expanded)
%              Number of leaves         :   10 (  16 expanded)
%              Depth                    :   10
%              Number of atoms          :  118 ( 175 expanded)
%              Number of equality atoms :   22 (  25 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t76_enumset1,axiom,(
    ! [X1] : k1_enumset1(X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t6_xboole_0,axiom,(
    ! [X1,X2] :
      ~ ( r2_xboole_0(X1,X2)
        & ! [X3] :
            ~ ( r2_hidden(X3,X2)
              & ~ r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

fof(t34_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t218_relat_1,conjecture,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v5_relat_1(X3,X1) )
         => v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t218_relat_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(c_0_10,plain,(
    ! [X20,X21] :
      ( ( k4_xboole_0(X20,k1_tarski(X21)) != X20
        | ~ r2_hidden(X21,X20) )
      & ( r2_hidden(X21,X20)
        | k4_xboole_0(X20,k1_tarski(X21)) = X20 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

fof(c_0_11,plain,(
    ! [X19] : k1_enumset1(X19,X19,X19) = k1_tarski(X19) ),
    inference(variable_rename,[status(thm)],[t76_enumset1])).

fof(c_0_12,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_13,plain,(
    ! [X10,X11] :
      ( ( r2_hidden(esk2_2(X10,X11),X11)
        | ~ r2_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk2_2(X10,X11),X10)
        | ~ r2_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_xboole_0])])])])])).

fof(c_0_14,plain,(
    ! [X15,X16,X17] :
      ( ~ r1_tarski(X15,X16)
      | r1_tarski(k4_xboole_0(X17,X16),k4_xboole_0(X17,X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_xboole_1])])).

fof(c_0_15,plain,(
    ! [X13,X14] :
      ( ( k4_xboole_0(X13,X14) != k1_xboole_0
        | r1_tarski(X13,X14) )
      & ( ~ r1_tarski(X13,X14)
        | k4_xboole_0(X13,X14) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_tarski(X1,X2)
       => ! [X3] :
            ( ( v1_relat_1(X3)
              & v5_relat_1(X3,X1) )
           => v5_relat_1(X3,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t218_relat_1])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,k1_tarski(X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_19,plain,(
    ! [X18] : k4_xboole_0(k1_xboole_0,X18) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_20,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_22,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | ~ r2_xboole_0(X8,X9) )
      & ( X8 != X9
        | ~ r2_xboole_0(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | X8 = X9
        | r2_xboole_0(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_23,plain,
    ( r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_25,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    & v1_relat_1(esk5_0)
    & v5_relat_1(esk5_0,esk3_0)
    & ~ v5_relat_1(esk5_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k1_enumset1(X2,X2,X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_27,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( ~ r2_xboole_0(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_29,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k1_xboole_0)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_34,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,esk4_0),k1_xboole_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_37,plain,(
    ! [X22,X23] :
      ( ( ~ v5_relat_1(X23,X22)
        | r1_tarski(k2_relat_1(X23),X22)
        | ~ v1_relat_1(X23) )
      & ( ~ r1_tarski(k2_relat_1(X23),X22)
        | v5_relat_1(X23,X22)
        | ~ v1_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_39,negated_conjecture,
    ( k4_xboole_0(X1,esk4_0) = k1_xboole_0
    | ~ r1_tarski(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])])).

cnf(c_0_40,plain,
    ( v5_relat_1(X1,X2)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( v5_relat_1(X1,esk4_0)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_43,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( v5_relat_1(X1,esk4_0)
    | ~ v5_relat_1(X1,esk3_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_45,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_46,negated_conjecture,
    ( v5_relat_1(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_47,negated_conjecture,
    ( ~ v5_relat_1(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])]),c_0_47]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:47:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S060N
% 0.20/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.027 s
% 0.20/0.37  # Presaturation interreduction done
% 0.20/0.37  
% 0.20/0.37  # Proof found!
% 0.20/0.37  # SZS status Theorem
% 0.20/0.37  # SZS output start CNFRefutation
% 0.20/0.37  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.20/0.37  fof(t76_enumset1, axiom, ![X1]:k1_enumset1(X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_enumset1)).
% 0.20/0.37  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.37  fof(t6_xboole_0, axiom, ![X1, X2]:~((r2_xboole_0(X1,X2)&![X3]:~((r2_hidden(X3,X2)&~(r2_hidden(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_0)).
% 0.20/0.37  fof(t34_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_xboole_1)).
% 0.20/0.37  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.20/0.37  fof(t218_relat_1, conjecture, ![X1, X2]:(r1_tarski(X1,X2)=>![X3]:((v1_relat_1(X3)&v5_relat_1(X3,X1))=>v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t218_relat_1)).
% 0.20/0.37  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 0.20/0.37  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.20/0.37  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 0.20/0.37  fof(c_0_10, plain, ![X20, X21]:((k4_xboole_0(X20,k1_tarski(X21))!=X20|~r2_hidden(X21,X20))&(r2_hidden(X21,X20)|k4_xboole_0(X20,k1_tarski(X21))=X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.20/0.37  fof(c_0_11, plain, ![X19]:k1_enumset1(X19,X19,X19)=k1_tarski(X19), inference(variable_rename,[status(thm)],[t76_enumset1])).
% 0.20/0.37  fof(c_0_12, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.37  fof(c_0_13, plain, ![X10, X11]:((r2_hidden(esk2_2(X10,X11),X11)|~r2_xboole_0(X10,X11))&(~r2_hidden(esk2_2(X10,X11),X10)|~r2_xboole_0(X10,X11))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_xboole_0])])])])])).
% 0.20/0.37  fof(c_0_14, plain, ![X15, X16, X17]:(~r1_tarski(X15,X16)|r1_tarski(k4_xboole_0(X17,X16),k4_xboole_0(X17,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_xboole_1])])).
% 0.20/0.37  fof(c_0_15, plain, ![X13, X14]:((k4_xboole_0(X13,X14)!=k1_xboole_0|r1_tarski(X13,X14))&(~r1_tarski(X13,X14)|k4_xboole_0(X13,X14)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.20/0.37  fof(c_0_16, negated_conjecture, ~(![X1, X2]:(r1_tarski(X1,X2)=>![X3]:((v1_relat_1(X3)&v5_relat_1(X3,X1))=>v5_relat_1(X3,X2)))), inference(assume_negation,[status(cth)],[t218_relat_1])).
% 0.20/0.37  cnf(c_0_17, plain, (k4_xboole_0(X1,k1_tarski(X2))!=X1|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.37  cnf(c_0_18, plain, (k1_enumset1(X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.37  fof(c_0_19, plain, ![X18]:k4_xboole_0(k1_xboole_0,X18)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.20/0.37  cnf(c_0_20, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.37  cnf(c_0_21, plain, (r2_hidden(esk2_2(X1,X2),X2)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.37  fof(c_0_22, plain, ![X8, X9]:(((r1_tarski(X8,X9)|~r2_xboole_0(X8,X9))&(X8!=X9|~r2_xboole_0(X8,X9)))&(~r1_tarski(X8,X9)|X8=X9|r2_xboole_0(X8,X9))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.20/0.37  cnf(c_0_23, plain, (r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.37  cnf(c_0_24, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.37  fof(c_0_25, negated_conjecture, (r1_tarski(esk3_0,esk4_0)&((v1_relat_1(esk5_0)&v5_relat_1(esk5_0,esk3_0))&~v5_relat_1(esk5_0,esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.20/0.37  cnf(c_0_26, plain, (k4_xboole_0(X1,k1_enumset1(X2,X2,X2))!=X1|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.37  cnf(c_0_27, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.37  cnf(c_0_28, plain, (~r2_xboole_0(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.37  cnf(c_0_29, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.37  cnf(c_0_30, plain, (r1_tarski(k4_xboole_0(X1,X2),k1_xboole_0)|~r1_tarski(X3,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.37  cnf(c_0_31, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.37  cnf(c_0_32, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.37  cnf(c_0_33, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.37  cnf(c_0_34, plain, (X1=X2|~r1_tarski(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.37  cnf(c_0_35, negated_conjecture, (r1_tarski(k4_xboole_0(X1,esk4_0),k1_xboole_0)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.37  cnf(c_0_36, plain, (v1_xboole_0(k1_xboole_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.37  fof(c_0_37, plain, ![X22, X23]:((~v5_relat_1(X23,X22)|r1_tarski(k2_relat_1(X23),X22)|~v1_relat_1(X23))&(~r1_tarski(k2_relat_1(X23),X22)|v5_relat_1(X23,X22)|~v1_relat_1(X23))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.20/0.37  cnf(c_0_38, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.37  cnf(c_0_39, negated_conjecture, (k4_xboole_0(X1,esk4_0)=k1_xboole_0|~r1_tarski(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])])).
% 0.20/0.37  cnf(c_0_40, plain, (v5_relat_1(X1,X2)|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.37  cnf(c_0_41, negated_conjecture, (r1_tarski(X1,esk4_0)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.37  cnf(c_0_42, negated_conjecture, (v5_relat_1(X1,esk4_0)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),esk3_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.37  cnf(c_0_43, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.37  cnf(c_0_44, negated_conjecture, (v5_relat_1(X1,esk4_0)|~v5_relat_1(X1,esk3_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.37  cnf(c_0_45, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.37  cnf(c_0_46, negated_conjecture, (v5_relat_1(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.37  cnf(c_0_47, negated_conjecture, (~v5_relat_1(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.37  cnf(c_0_48, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])]), c_0_47]), ['proof']).
% 0.20/0.37  # SZS output end CNFRefutation
% 0.20/0.37  # Proof object total steps             : 49
% 0.20/0.37  # Proof object clause steps            : 28
% 0.20/0.37  # Proof object formula steps           : 21
% 0.20/0.37  # Proof object conjectures             : 13
% 0.20/0.37  # Proof object clause conjectures      : 10
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 16
% 0.20/0.37  # Proof object initial formulas used   : 10
% 0.20/0.37  # Proof object generating inferences   : 11
% 0.20/0.37  # Proof object simplifying inferences  : 6
% 0.20/0.37  # Training examples: 0 positive, 0 negative
% 0.20/0.37  # Parsed axioms                        : 10
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 20
% 0.20/0.37  # Removed in clause preprocessing      : 1
% 0.20/0.37  # Initial clauses in saturation        : 19
% 0.20/0.37  # Processed clauses                    : 68
% 0.20/0.37  # ...of these trivial                  : 0
% 0.20/0.37  # ...subsumed                          : 5
% 0.20/0.37  # ...remaining for further processing  : 63
% 0.20/0.37  # Other redundant clauses eliminated   : 3
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 0
% 0.20/0.38  # Backward-rewritten                   : 0
% 0.20/0.38  # Generated clauses                    : 57
% 0.20/0.38  # ...of the previous two non-trivial   : 40
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 54
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 3
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 43
% 0.20/0.38  #    Positive orientable unit clauses  : 6
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 4
% 0.20/0.38  #    Non-unit-clauses                  : 33
% 0.20/0.38  # Current number of unprocessed clauses: 10
% 0.20/0.38  # ...number of literals in the above   : 30
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 20
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 90
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 72
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 3
% 0.20/0.38  # Unit Clause-clause subsumption calls : 7
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 0
% 0.20/0.38  # BW rewrite match successes           : 0
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 1735
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.028 s
% 0.20/0.38  # System time              : 0.005 s
% 0.20/0.38  # Total time               : 0.033 s
% 0.20/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
