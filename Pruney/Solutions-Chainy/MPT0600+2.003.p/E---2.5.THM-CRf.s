%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:12 EST 2020

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 145 expanded)
%              Number of clauses        :   29 (  63 expanded)
%              Number of leaves         :    9 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :  179 ( 452 expanded)
%              Number of equality atoms :   70 ( 150 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(t20_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(X2,k2_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

fof(t204_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> r2_hidden(X2,k11_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

fof(d16_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(c_0_9,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12,X13,X14,X15] :
      ( ( ~ r2_hidden(X10,X9)
        | X10 = X6
        | X10 = X7
        | X10 = X8
        | X9 != k1_enumset1(X6,X7,X8) )
      & ( X11 != X6
        | r2_hidden(X11,X9)
        | X9 != k1_enumset1(X6,X7,X8) )
      & ( X11 != X7
        | r2_hidden(X11,X9)
        | X9 != k1_enumset1(X6,X7,X8) )
      & ( X11 != X8
        | r2_hidden(X11,X9)
        | X9 != k1_enumset1(X6,X7,X8) )
      & ( esk1_4(X12,X13,X14,X15) != X12
        | ~ r2_hidden(esk1_4(X12,X13,X14,X15),X15)
        | X15 = k1_enumset1(X12,X13,X14) )
      & ( esk1_4(X12,X13,X14,X15) != X13
        | ~ r2_hidden(esk1_4(X12,X13,X14,X15),X15)
        | X15 = k1_enumset1(X12,X13,X14) )
      & ( esk1_4(X12,X13,X14,X15) != X14
        | ~ r2_hidden(esk1_4(X12,X13,X14,X15),X15)
        | X15 = k1_enumset1(X12,X13,X14) )
      & ( r2_hidden(esk1_4(X12,X13,X14,X15),X15)
        | esk1_4(X12,X13,X14,X15) = X12
        | esk1_4(X12,X13,X14,X15) = X13
        | esk1_4(X12,X13,X14,X15) = X14
        | X15 = k1_enumset1(X12,X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_10,plain,(
    ! [X29,X30,X31] : k2_enumset1(X29,X29,X30,X31) = k1_enumset1(X29,X30,X31) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_11,plain,(
    ! [X17,X18,X19,X20,X21,X22,X23,X24] :
      ( ( ~ r2_hidden(X20,X19)
        | X20 = X17
        | X20 = X18
        | X19 != k2_tarski(X17,X18) )
      & ( X21 != X17
        | r2_hidden(X21,X19)
        | X19 != k2_tarski(X17,X18) )
      & ( X21 != X18
        | r2_hidden(X21,X19)
        | X19 != k2_tarski(X17,X18) )
      & ( esk2_3(X22,X23,X24) != X22
        | ~ r2_hidden(esk2_3(X22,X23,X24),X24)
        | X24 = k2_tarski(X22,X23) )
      & ( esk2_3(X22,X23,X24) != X23
        | ~ r2_hidden(esk2_3(X22,X23,X24),X24)
        | X24 = k2_tarski(X22,X23) )
      & ( r2_hidden(esk2_3(X22,X23,X24),X24)
        | esk2_3(X22,X23,X24) = X22
        | esk2_3(X22,X23,X24) = X23
        | X24 = k2_tarski(X22,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_12,plain,(
    ! [X27,X28] : k1_enumset1(X27,X27,X28) = k2_tarski(X27,X28) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,plain,(
    ! [X34,X35,X36,X38] :
      ( ( r2_hidden(esk3_3(X34,X35,X36),k1_relat_1(X36))
        | ~ r2_hidden(X34,k9_relat_1(X36,X35))
        | ~ v1_relat_1(X36) )
      & ( r2_hidden(k4_tarski(esk3_3(X34,X35,X36),X34),X36)
        | ~ r2_hidden(X34,k9_relat_1(X36,X35))
        | ~ v1_relat_1(X36) )
      & ( r2_hidden(esk3_3(X34,X35,X36),X35)
        | ~ r2_hidden(X34,k9_relat_1(X36,X35))
        | ~ v1_relat_1(X36) )
      & ( ~ r2_hidden(X38,k1_relat_1(X36))
        | ~ r2_hidden(k4_tarski(X38,X34),X36)
        | ~ r2_hidden(X38,X35)
        | r2_hidden(X34,k9_relat_1(X36,X35))
        | ~ v1_relat_1(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

fof(c_0_14,plain,(
    ! [X39,X40,X41] :
      ( ( r2_hidden(X39,k1_relat_1(X41))
        | ~ r2_hidden(k4_tarski(X39,X40),X41)
        | ~ v1_relat_1(X41) )
      & ( r2_hidden(X40,k2_relat_1(X41))
        | ~ r2_hidden(k4_tarski(X39,X40),X41)
        | ~ v1_relat_1(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r2_hidden(k4_tarski(X1,X2),X3)
        <=> r2_hidden(X2,k11_relat_1(X3,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t204_relat_1])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( r2_hidden(X3,k9_relat_1(X2,X4))
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_22,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & ( ~ r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0)
      | ~ r2_hidden(esk5_0,k11_relat_1(esk6_0,esk4_0)) )
    & ( r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0)
      | r2_hidden(esk5_0,k11_relat_1(esk6_0,esk4_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_17])).

fof(c_0_25,plain,(
    ! [X32,X33] :
      ( ~ v1_relat_1(X32)
      | k11_relat_1(X32,X33) = k9_relat_1(X32,k1_tarski(X33)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).

fof(c_0_26,plain,(
    ! [X26] : k2_tarski(X26,X26) = k1_tarski(X26) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,k9_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X4,X1),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(csr,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0)
    | r2_hidden(esk5_0,k11_relat_1(esk6_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | X2 != k2_enumset1(X3,X3,X4,X1) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X3)) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_33,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk5_0,k11_relat_1(esk6_0,esk4_0))
    | r2_hidden(esk5_0,k9_relat_1(esk6_0,X1))
    | ~ r2_hidden(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( esk3_3(X1,k2_enumset1(X2,X2,X2,X3),X4) = X3
    | esk3_3(X1,k2_enumset1(X2,X2,X2,X3),X4) = X2
    | ~ v1_relat_1(X4)
    | ~ r2_hidden(X1,k9_relat_1(X4,k2_enumset1(X2,X2,X2,X3))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k2_enumset1(X2,X2,X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34]),c_0_19]),c_0_17])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk5_0,k9_relat_1(esk6_0,k2_enumset1(X1,X1,X2,esk4_0)))
    | r2_hidden(esk5_0,k11_relat_1(esk6_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,plain,
    ( r2_hidden(k4_tarski(esk3_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_41,plain,
    ( esk3_3(X1,k2_enumset1(X2,X2,X2,X2),X3) = X2
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k11_relat_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0)
    | ~ r2_hidden(esk5_0,k11_relat_1(esk6_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk5_0,k11_relat_1(esk6_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_38]),c_0_29])])).

cnf(c_0_44,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X2,k9_relat_1(X3,k2_enumset1(X1,X1,X1,X1)))
    | ~ r2_hidden(X2,k11_relat_1(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43])])).

cnf(c_0_46,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X2,k11_relat_1(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_29]),c_0_43])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n003.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 18:01:27 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 0.11/0.38  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.11/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.11/0.38  #
% 0.11/0.38  # Preprocessing time       : 0.031 s
% 0.11/0.38  # Presaturation interreduction done
% 0.11/0.38  
% 0.11/0.38  # Proof found!
% 0.11/0.38  # SZS status Theorem
% 0.11/0.38  # SZS output start CNFRefutation
% 0.11/0.38  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 0.11/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.11/0.38  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.11/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.11/0.38  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 0.11/0.38  fof(t20_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(X2,k2_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 0.11/0.38  fof(t204_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r2_hidden(X2,k11_relat_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 0.11/0.38  fof(d16_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 0.11/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.11/0.38  fof(c_0_9, plain, ![X6, X7, X8, X9, X10, X11, X12, X13, X14, X15]:(((~r2_hidden(X10,X9)|(X10=X6|X10=X7|X10=X8)|X9!=k1_enumset1(X6,X7,X8))&(((X11!=X6|r2_hidden(X11,X9)|X9!=k1_enumset1(X6,X7,X8))&(X11!=X7|r2_hidden(X11,X9)|X9!=k1_enumset1(X6,X7,X8)))&(X11!=X8|r2_hidden(X11,X9)|X9!=k1_enumset1(X6,X7,X8))))&((((esk1_4(X12,X13,X14,X15)!=X12|~r2_hidden(esk1_4(X12,X13,X14,X15),X15)|X15=k1_enumset1(X12,X13,X14))&(esk1_4(X12,X13,X14,X15)!=X13|~r2_hidden(esk1_4(X12,X13,X14,X15),X15)|X15=k1_enumset1(X12,X13,X14)))&(esk1_4(X12,X13,X14,X15)!=X14|~r2_hidden(esk1_4(X12,X13,X14,X15),X15)|X15=k1_enumset1(X12,X13,X14)))&(r2_hidden(esk1_4(X12,X13,X14,X15),X15)|(esk1_4(X12,X13,X14,X15)=X12|esk1_4(X12,X13,X14,X15)=X13|esk1_4(X12,X13,X14,X15)=X14)|X15=k1_enumset1(X12,X13,X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.11/0.38  fof(c_0_10, plain, ![X29, X30, X31]:k2_enumset1(X29,X29,X30,X31)=k1_enumset1(X29,X30,X31), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.11/0.38  fof(c_0_11, plain, ![X17, X18, X19, X20, X21, X22, X23, X24]:(((~r2_hidden(X20,X19)|(X20=X17|X20=X18)|X19!=k2_tarski(X17,X18))&((X21!=X17|r2_hidden(X21,X19)|X19!=k2_tarski(X17,X18))&(X21!=X18|r2_hidden(X21,X19)|X19!=k2_tarski(X17,X18))))&(((esk2_3(X22,X23,X24)!=X22|~r2_hidden(esk2_3(X22,X23,X24),X24)|X24=k2_tarski(X22,X23))&(esk2_3(X22,X23,X24)!=X23|~r2_hidden(esk2_3(X22,X23,X24),X24)|X24=k2_tarski(X22,X23)))&(r2_hidden(esk2_3(X22,X23,X24),X24)|(esk2_3(X22,X23,X24)=X22|esk2_3(X22,X23,X24)=X23)|X24=k2_tarski(X22,X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.11/0.38  fof(c_0_12, plain, ![X27, X28]:k1_enumset1(X27,X27,X28)=k2_tarski(X27,X28), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.11/0.38  fof(c_0_13, plain, ![X34, X35, X36, X38]:((((r2_hidden(esk3_3(X34,X35,X36),k1_relat_1(X36))|~r2_hidden(X34,k9_relat_1(X36,X35))|~v1_relat_1(X36))&(r2_hidden(k4_tarski(esk3_3(X34,X35,X36),X34),X36)|~r2_hidden(X34,k9_relat_1(X36,X35))|~v1_relat_1(X36)))&(r2_hidden(esk3_3(X34,X35,X36),X35)|~r2_hidden(X34,k9_relat_1(X36,X35))|~v1_relat_1(X36)))&(~r2_hidden(X38,k1_relat_1(X36))|~r2_hidden(k4_tarski(X38,X34),X36)|~r2_hidden(X38,X35)|r2_hidden(X34,k9_relat_1(X36,X35))|~v1_relat_1(X36))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.11/0.38  fof(c_0_14, plain, ![X39, X40, X41]:((r2_hidden(X39,k1_relat_1(X41))|~r2_hidden(k4_tarski(X39,X40),X41)|~v1_relat_1(X41))&(r2_hidden(X40,k2_relat_1(X41))|~r2_hidden(k4_tarski(X39,X40),X41)|~v1_relat_1(X41))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).
% 0.11/0.38  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r2_hidden(X2,k11_relat_1(X3,X1))))), inference(assume_negation,[status(cth)],[t204_relat_1])).
% 0.11/0.38  cnf(c_0_16, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.11/0.38  cnf(c_0_17, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.11/0.38  cnf(c_0_18, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.11/0.38  cnf(c_0_19, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.11/0.38  cnf(c_0_20, plain, (r2_hidden(X3,k9_relat_1(X2,X4))|~r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,X4)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.11/0.38  cnf(c_0_21, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.11/0.38  fof(c_0_22, negated_conjecture, (v1_relat_1(esk6_0)&((~r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0)|~r2_hidden(esk5_0,k11_relat_1(esk6_0,esk4_0)))&(r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0)|r2_hidden(esk5_0,k11_relat_1(esk6_0,esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.11/0.38  cnf(c_0_23, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X4,X5,X2)), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.11/0.38  cnf(c_0_24, plain, (X1=X4|X1=X3|X2!=k2_enumset1(X3,X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_17])).
% 0.11/0.38  fof(c_0_25, plain, ![X32, X33]:(~v1_relat_1(X32)|k11_relat_1(X32,X33)=k9_relat_1(X32,k1_tarski(X33))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).
% 0.11/0.38  fof(c_0_26, plain, ![X26]:k2_tarski(X26,X26)=k1_tarski(X26), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.11/0.38  cnf(c_0_27, plain, (r2_hidden(X1,k9_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X4,X1),X2)|~r2_hidden(X4,X3)), inference(csr,[status(thm)],[c_0_20, c_0_21])).
% 0.11/0.38  cnf(c_0_28, negated_conjecture, (r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0)|r2_hidden(esk5_0,k11_relat_1(esk6_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.11/0.38  cnf(c_0_29, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.11/0.38  cnf(c_0_30, plain, (r2_hidden(X1,X2)|X2!=k2_enumset1(X3,X3,X4,X1)), inference(er,[status(thm)],[c_0_23])).
% 0.11/0.38  cnf(c_0_31, plain, (X1=X2|X1=X3|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X3))), inference(er,[status(thm)],[c_0_24])).
% 0.11/0.38  cnf(c_0_32, plain, (r2_hidden(esk3_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.11/0.38  cnf(c_0_33, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.11/0.38  cnf(c_0_34, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.11/0.38  cnf(c_0_35, negated_conjecture, (r2_hidden(esk5_0,k11_relat_1(esk6_0,esk4_0))|r2_hidden(esk5_0,k9_relat_1(esk6_0,X1))|~r2_hidden(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])])).
% 0.11/0.38  cnf(c_0_36, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X3,X1))), inference(er,[status(thm)],[c_0_30])).
% 0.11/0.38  cnf(c_0_37, plain, (esk3_3(X1,k2_enumset1(X2,X2,X2,X3),X4)=X3|esk3_3(X1,k2_enumset1(X2,X2,X2,X3),X4)=X2|~v1_relat_1(X4)|~r2_hidden(X1,k9_relat_1(X4,k2_enumset1(X2,X2,X2,X3)))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.11/0.38  cnf(c_0_38, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k2_enumset1(X2,X2,X2,X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34]), c_0_19]), c_0_17])).
% 0.11/0.38  cnf(c_0_39, negated_conjecture, (r2_hidden(esk5_0,k9_relat_1(esk6_0,k2_enumset1(X1,X1,X2,esk4_0)))|r2_hidden(esk5_0,k11_relat_1(esk6_0,esk4_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.11/0.38  cnf(c_0_40, plain, (r2_hidden(k4_tarski(esk3_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.11/0.38  cnf(c_0_41, plain, (esk3_3(X1,k2_enumset1(X2,X2,X2,X2),X3)=X2|~v1_relat_1(X3)|~r2_hidden(X1,k11_relat_1(X3,X2))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.11/0.38  cnf(c_0_42, negated_conjecture, (~r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0)|~r2_hidden(esk5_0,k11_relat_1(esk6_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.11/0.38  cnf(c_0_43, negated_conjecture, (r2_hidden(esk5_0,k11_relat_1(esk6_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_38]), c_0_29])])).
% 0.11/0.38  cnf(c_0_44, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)|~r2_hidden(X2,k9_relat_1(X3,k2_enumset1(X1,X1,X1,X1)))|~r2_hidden(X2,k11_relat_1(X3,X1))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.11/0.38  cnf(c_0_45, negated_conjecture, (~r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43])])).
% 0.11/0.38  cnf(c_0_46, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)|~r2_hidden(X2,k11_relat_1(X3,X1))), inference(spm,[status(thm)],[c_0_44, c_0_38])).
% 0.11/0.38  cnf(c_0_47, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_29]), c_0_43])]), ['proof']).
% 0.11/0.38  # SZS output end CNFRefutation
% 0.11/0.38  # Proof object total steps             : 48
% 0.11/0.38  # Proof object clause steps            : 29
% 0.11/0.38  # Proof object formula steps           : 19
% 0.11/0.38  # Proof object conjectures             : 11
% 0.11/0.38  # Proof object clause conjectures      : 8
% 0.11/0.38  # Proof object formula conjectures     : 3
% 0.11/0.38  # Proof object initial clauses used    : 13
% 0.11/0.38  # Proof object initial formulas used   : 9
% 0.11/0.38  # Proof object generating inferences   : 10
% 0.11/0.38  # Proof object simplifying inferences  : 17
% 0.11/0.38  # Training examples: 0 positive, 0 negative
% 0.11/0.38  # Parsed axioms                        : 9
% 0.11/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.11/0.38  # Initial clauses                      : 27
% 0.11/0.38  # Removed in clause preprocessing      : 3
% 0.11/0.38  # Initial clauses in saturation        : 24
% 0.11/0.38  # Processed clauses                    : 166
% 0.11/0.38  # ...of these trivial                  : 0
% 0.11/0.38  # ...subsumed                          : 44
% 0.11/0.38  # ...remaining for further processing  : 122
% 0.11/0.38  # Other redundant clauses eliminated   : 5
% 0.11/0.38  # Clauses deleted for lack of memory   : 0
% 0.11/0.38  # Backward-subsumed                    : 4
% 0.11/0.38  # Backward-rewritten                   : 5
% 0.11/0.38  # Generated clauses                    : 474
% 0.11/0.38  # ...of the previous two non-trivial   : 460
% 0.11/0.38  # Contextual simplify-reflections      : 1
% 0.11/0.38  # Paramodulations                      : 464
% 0.11/0.38  # Factorizations                       : 0
% 0.11/0.38  # Equation resolutions                 : 10
% 0.11/0.38  # Propositional unsat checks           : 0
% 0.11/0.38  #    Propositional check models        : 0
% 0.11/0.38  #    Propositional check unsatisfiable : 0
% 0.11/0.38  #    Propositional clauses             : 0
% 0.11/0.38  #    Propositional clauses after purity: 0
% 0.11/0.38  #    Propositional unsat core size     : 0
% 0.11/0.38  #    Propositional preprocessing time  : 0.000
% 0.11/0.38  #    Propositional encoding time       : 0.000
% 0.11/0.38  #    Propositional solver time         : 0.000
% 0.11/0.38  #    Success case prop preproc time    : 0.000
% 0.11/0.38  #    Success case prop encoding time   : 0.000
% 0.11/0.38  #    Success case prop solver time     : 0.000
% 0.11/0.38  # Current number of processed clauses  : 86
% 0.11/0.38  #    Positive orientable unit clauses  : 8
% 0.11/0.38  #    Positive unorientable unit clauses: 0
% 0.11/0.38  #    Negative unit clauses             : 1
% 0.11/0.38  #    Non-unit-clauses                  : 77
% 0.11/0.38  # Current number of unprocessed clauses: 308
% 0.11/0.38  # ...number of literals in the above   : 1595
% 0.11/0.38  # Current number of archived formulas  : 0
% 0.11/0.38  # Current number of archived clauses   : 34
% 0.11/0.38  # Clause-clause subsumption calls (NU) : 3591
% 0.11/0.38  # Rec. Clause-clause subsumption calls : 1123
% 0.11/0.38  # Non-unit clause-clause subsumptions  : 47
% 0.11/0.38  # Unit Clause-clause subsumption calls : 2
% 0.11/0.38  # Rewrite failures with RHS unbound    : 0
% 0.11/0.38  # BW rewrite match attempts            : 4
% 0.11/0.38  # BW rewrite match successes           : 1
% 0.11/0.38  # Condensation attempts                : 0
% 0.11/0.38  # Condensation successes               : 0
% 0.11/0.38  # Termbank termtop insertions          : 12615
% 0.11/0.38  
% 0.11/0.38  # -------------------------------------------------
% 0.11/0.38  # User time                : 0.044 s
% 0.11/0.38  # System time              : 0.007 s
% 0.11/0.38  # Total time               : 0.052 s
% 0.11/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
