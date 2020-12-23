%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:12 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 137 expanded)
%              Number of clauses        :   28 (  59 expanded)
%              Number of leaves         :    9 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :  185 ( 458 expanded)
%              Number of equality atoms :   75 ( 154 expanded)
%              Maximal formula depth    :   27 (   5 average)
%              Maximal clause size      :   36 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

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

fof(d2_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( X5 = k2_enumset1(X1,X2,X3,X4)
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X6 != X1
              & X6 != X2
              & X6 != X3
              & X6 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).

fof(d16_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(c_0_9,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( ~ r2_hidden(X10,X9)
        | X10 = X7
        | X10 = X8
        | X9 != k2_tarski(X7,X8) )
      & ( X11 != X7
        | r2_hidden(X11,X9)
        | X9 != k2_tarski(X7,X8) )
      & ( X11 != X8
        | r2_hidden(X11,X9)
        | X9 != k2_tarski(X7,X8) )
      & ( esk1_3(X12,X13,X14) != X12
        | ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k2_tarski(X12,X13) )
      & ( esk1_3(X12,X13,X14) != X13
        | ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k2_tarski(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X14)
        | esk1_3(X12,X13,X14) = X12
        | esk1_3(X12,X13,X14) = X13
        | X14 = k2_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_10,plain,(
    ! [X17,X18] : k1_enumset1(X17,X17,X18) = k2_tarski(X17,X18) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_11,plain,(
    ! [X19,X20,X21] : k2_enumset1(X19,X19,X20,X21) = k1_enumset1(X19,X20,X21) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_12,plain,(
    ! [X37,X38,X39,X41] :
      ( ( r2_hidden(esk3_3(X37,X38,X39),k1_relat_1(X39))
        | ~ r2_hidden(X37,k9_relat_1(X39,X38))
        | ~ v1_relat_1(X39) )
      & ( r2_hidden(k4_tarski(esk3_3(X37,X38,X39),X37),X39)
        | ~ r2_hidden(X37,k9_relat_1(X39,X38))
        | ~ v1_relat_1(X39) )
      & ( r2_hidden(esk3_3(X37,X38,X39),X38)
        | ~ r2_hidden(X37,k9_relat_1(X39,X38))
        | ~ v1_relat_1(X39) )
      & ( ~ r2_hidden(X41,k1_relat_1(X39))
        | ~ r2_hidden(k4_tarski(X41,X37),X39)
        | ~ r2_hidden(X41,X38)
        | r2_hidden(X37,k9_relat_1(X39,X38))
        | ~ v1_relat_1(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

fof(c_0_13,plain,(
    ! [X42,X43,X44] :
      ( ( r2_hidden(X42,k1_relat_1(X44))
        | ~ r2_hidden(k4_tarski(X42,X43),X44)
        | ~ v1_relat_1(X44) )
      & ( r2_hidden(X43,k2_relat_1(X44))
        | ~ r2_hidden(k4_tarski(X42,X43),X44)
        | ~ v1_relat_1(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r2_hidden(k4_tarski(X1,X2),X3)
        <=> r2_hidden(X2,k11_relat_1(X3,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t204_relat_1])).

fof(c_0_15,plain,(
    ! [X22,X23,X24,X25,X26,X27,X28,X29,X30,X31,X32,X33] :
      ( ( ~ r2_hidden(X27,X26)
        | X27 = X22
        | X27 = X23
        | X27 = X24
        | X27 = X25
        | X26 != k2_enumset1(X22,X23,X24,X25) )
      & ( X28 != X22
        | r2_hidden(X28,X26)
        | X26 != k2_enumset1(X22,X23,X24,X25) )
      & ( X28 != X23
        | r2_hidden(X28,X26)
        | X26 != k2_enumset1(X22,X23,X24,X25) )
      & ( X28 != X24
        | r2_hidden(X28,X26)
        | X26 != k2_enumset1(X22,X23,X24,X25) )
      & ( X28 != X25
        | r2_hidden(X28,X26)
        | X26 != k2_enumset1(X22,X23,X24,X25) )
      & ( esk2_5(X29,X30,X31,X32,X33) != X29
        | ~ r2_hidden(esk2_5(X29,X30,X31,X32,X33),X33)
        | X33 = k2_enumset1(X29,X30,X31,X32) )
      & ( esk2_5(X29,X30,X31,X32,X33) != X30
        | ~ r2_hidden(esk2_5(X29,X30,X31,X32,X33),X33)
        | X33 = k2_enumset1(X29,X30,X31,X32) )
      & ( esk2_5(X29,X30,X31,X32,X33) != X31
        | ~ r2_hidden(esk2_5(X29,X30,X31,X32,X33),X33)
        | X33 = k2_enumset1(X29,X30,X31,X32) )
      & ( esk2_5(X29,X30,X31,X32,X33) != X32
        | ~ r2_hidden(esk2_5(X29,X30,X31,X32,X33),X33)
        | X33 = k2_enumset1(X29,X30,X31,X32) )
      & ( r2_hidden(esk2_5(X29,X30,X31,X32,X33),X33)
        | esk2_5(X29,X30,X31,X32,X33) = X29
        | esk2_5(X29,X30,X31,X32,X33) = X30
        | esk2_5(X29,X30,X31,X32,X33) = X31
        | esk2_5(X29,X30,X31,X32,X33) = X32
        | X33 = k2_enumset1(X29,X30,X31,X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_enumset1])])])])])])).

cnf(c_0_16,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( r2_hidden(X3,k9_relat_1(X2,X4))
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_21,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & ( ~ r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0)
      | ~ r2_hidden(esk5_0,k11_relat_1(esk6_0,esk4_0)) )
    & ( r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0)
      | r2_hidden(esk5_0,k11_relat_1(esk6_0,esk4_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X5,X6,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

fof(c_0_24,plain,(
    ! [X35,X36] :
      ( ~ v1_relat_1(X35)
      | k11_relat_1(X35,X36) = k9_relat_1(X35,k1_tarski(X36)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).

fof(c_0_25,plain,(
    ! [X16] : k2_tarski(X16,X16) = k1_tarski(X16) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,k9_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X4,X1),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(csr,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0)
    | r2_hidden(esk5_0,k11_relat_1(esk6_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X2)
    | X2 != k2_enumset1(X3,X4,X5,X1) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X3)) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_32,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk5_0,k11_relat_1(esk6_0,esk4_0))
    | r2_hidden(esk5_0,k9_relat_1(esk6_0,X1))
    | ~ r2_hidden(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X3,X4,X1)) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( esk3_3(X1,k2_enumset1(X2,X2,X2,X3),X4) = X3
    | esk3_3(X1,k2_enumset1(X2,X2,X2,X3),X4) = X2
    | ~ v1_relat_1(X4)
    | ~ r2_hidden(X1,k9_relat_1(X4,k2_enumset1(X2,X2,X2,X3))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k2_enumset1(X2,X2,X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33]),c_0_17]),c_0_18])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk5_0,k9_relat_1(esk6_0,k2_enumset1(X1,X2,X3,esk4_0)))
    | r2_hidden(esk5_0,k11_relat_1(esk6_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,plain,
    ( r2_hidden(k4_tarski(esk3_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_40,plain,
    ( esk3_3(X1,k2_enumset1(X2,X2,X2,X2),X3) = X2
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k11_relat_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0)
    | ~ r2_hidden(esk5_0,k11_relat_1(esk6_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk5_0,k11_relat_1(esk6_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_37]),c_0_28])])).

cnf(c_0_43,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X2,k9_relat_1(X3,k2_enumset1(X1,X1,X1,X1)))
    | ~ r2_hidden(X2,k11_relat_1(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42])])).

cnf(c_0_45,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X2,k11_relat_1(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_28]),c_0_42])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:14:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.39  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.18/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.18/0.39  #
% 0.18/0.39  # Preprocessing time       : 0.033 s
% 0.18/0.39  # Presaturation interreduction done
% 0.18/0.39  
% 0.18/0.39  # Proof found!
% 0.18/0.39  # SZS status Theorem
% 0.18/0.39  # SZS output start CNFRefutation
% 0.18/0.39  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.18/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.18/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.18/0.39  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 0.18/0.39  fof(t20_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(X2,k2_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 0.18/0.39  fof(t204_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r2_hidden(X2,k11_relat_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 0.18/0.39  fof(d2_enumset1, axiom, ![X1, X2, X3, X4, X5]:(X5=k2_enumset1(X1,X2,X3,X4)<=>![X6]:(r2_hidden(X6,X5)<=>~((((X6!=X1&X6!=X2)&X6!=X3)&X6!=X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_enumset1)).
% 0.18/0.39  fof(d16_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 0.18/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.18/0.39  fof(c_0_9, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:(((~r2_hidden(X10,X9)|(X10=X7|X10=X8)|X9!=k2_tarski(X7,X8))&((X11!=X7|r2_hidden(X11,X9)|X9!=k2_tarski(X7,X8))&(X11!=X8|r2_hidden(X11,X9)|X9!=k2_tarski(X7,X8))))&(((esk1_3(X12,X13,X14)!=X12|~r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k2_tarski(X12,X13))&(esk1_3(X12,X13,X14)!=X13|~r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k2_tarski(X12,X13)))&(r2_hidden(esk1_3(X12,X13,X14),X14)|(esk1_3(X12,X13,X14)=X12|esk1_3(X12,X13,X14)=X13)|X14=k2_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.18/0.39  fof(c_0_10, plain, ![X17, X18]:k1_enumset1(X17,X17,X18)=k2_tarski(X17,X18), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.18/0.39  fof(c_0_11, plain, ![X19, X20, X21]:k2_enumset1(X19,X19,X20,X21)=k1_enumset1(X19,X20,X21), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.18/0.39  fof(c_0_12, plain, ![X37, X38, X39, X41]:((((r2_hidden(esk3_3(X37,X38,X39),k1_relat_1(X39))|~r2_hidden(X37,k9_relat_1(X39,X38))|~v1_relat_1(X39))&(r2_hidden(k4_tarski(esk3_3(X37,X38,X39),X37),X39)|~r2_hidden(X37,k9_relat_1(X39,X38))|~v1_relat_1(X39)))&(r2_hidden(esk3_3(X37,X38,X39),X38)|~r2_hidden(X37,k9_relat_1(X39,X38))|~v1_relat_1(X39)))&(~r2_hidden(X41,k1_relat_1(X39))|~r2_hidden(k4_tarski(X41,X37),X39)|~r2_hidden(X41,X38)|r2_hidden(X37,k9_relat_1(X39,X38))|~v1_relat_1(X39))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.18/0.39  fof(c_0_13, plain, ![X42, X43, X44]:((r2_hidden(X42,k1_relat_1(X44))|~r2_hidden(k4_tarski(X42,X43),X44)|~v1_relat_1(X44))&(r2_hidden(X43,k2_relat_1(X44))|~r2_hidden(k4_tarski(X42,X43),X44)|~v1_relat_1(X44))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).
% 0.18/0.39  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r2_hidden(X2,k11_relat_1(X3,X1))))), inference(assume_negation,[status(cth)],[t204_relat_1])).
% 0.18/0.39  fof(c_0_15, plain, ![X22, X23, X24, X25, X26, X27, X28, X29, X30, X31, X32, X33]:(((~r2_hidden(X27,X26)|(X27=X22|X27=X23|X27=X24|X27=X25)|X26!=k2_enumset1(X22,X23,X24,X25))&((((X28!=X22|r2_hidden(X28,X26)|X26!=k2_enumset1(X22,X23,X24,X25))&(X28!=X23|r2_hidden(X28,X26)|X26!=k2_enumset1(X22,X23,X24,X25)))&(X28!=X24|r2_hidden(X28,X26)|X26!=k2_enumset1(X22,X23,X24,X25)))&(X28!=X25|r2_hidden(X28,X26)|X26!=k2_enumset1(X22,X23,X24,X25))))&(((((esk2_5(X29,X30,X31,X32,X33)!=X29|~r2_hidden(esk2_5(X29,X30,X31,X32,X33),X33)|X33=k2_enumset1(X29,X30,X31,X32))&(esk2_5(X29,X30,X31,X32,X33)!=X30|~r2_hidden(esk2_5(X29,X30,X31,X32,X33),X33)|X33=k2_enumset1(X29,X30,X31,X32)))&(esk2_5(X29,X30,X31,X32,X33)!=X31|~r2_hidden(esk2_5(X29,X30,X31,X32,X33),X33)|X33=k2_enumset1(X29,X30,X31,X32)))&(esk2_5(X29,X30,X31,X32,X33)!=X32|~r2_hidden(esk2_5(X29,X30,X31,X32,X33),X33)|X33=k2_enumset1(X29,X30,X31,X32)))&(r2_hidden(esk2_5(X29,X30,X31,X32,X33),X33)|(esk2_5(X29,X30,X31,X32,X33)=X29|esk2_5(X29,X30,X31,X32,X33)=X30|esk2_5(X29,X30,X31,X32,X33)=X31|esk2_5(X29,X30,X31,X32,X33)=X32)|X33=k2_enumset1(X29,X30,X31,X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_enumset1])])])])])])).
% 0.18/0.39  cnf(c_0_16, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.39  cnf(c_0_17, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.39  cnf(c_0_18, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.39  cnf(c_0_19, plain, (r2_hidden(X3,k9_relat_1(X2,X4))|~r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,X4)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.39  cnf(c_0_20, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.39  fof(c_0_21, negated_conjecture, (v1_relat_1(esk6_0)&((~r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0)|~r2_hidden(esk5_0,k11_relat_1(esk6_0,esk4_0)))&(r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0)|r2_hidden(esk5_0,k11_relat_1(esk6_0,esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.18/0.39  cnf(c_0_22, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X5,X6,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.39  cnf(c_0_23, plain, (X1=X4|X1=X3|X2!=k2_enumset1(X3,X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_18])).
% 0.18/0.39  fof(c_0_24, plain, ![X35, X36]:(~v1_relat_1(X35)|k11_relat_1(X35,X36)=k9_relat_1(X35,k1_tarski(X36))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).
% 0.18/0.39  fof(c_0_25, plain, ![X16]:k2_tarski(X16,X16)=k1_tarski(X16), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.18/0.39  cnf(c_0_26, plain, (r2_hidden(X1,k9_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X4,X1),X2)|~r2_hidden(X4,X3)), inference(csr,[status(thm)],[c_0_19, c_0_20])).
% 0.18/0.39  cnf(c_0_27, negated_conjecture, (r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0)|r2_hidden(esk5_0,k11_relat_1(esk6_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.39  cnf(c_0_28, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.39  cnf(c_0_29, plain, (r2_hidden(X1,X2)|X2!=k2_enumset1(X3,X4,X5,X1)), inference(er,[status(thm)],[c_0_22])).
% 0.18/0.39  cnf(c_0_30, plain, (X1=X2|X1=X3|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X3))), inference(er,[status(thm)],[c_0_23])).
% 0.18/0.39  cnf(c_0_31, plain, (r2_hidden(esk3_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.39  cnf(c_0_32, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.39  cnf(c_0_33, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.18/0.39  cnf(c_0_34, negated_conjecture, (r2_hidden(esk5_0,k11_relat_1(esk6_0,esk4_0))|r2_hidden(esk5_0,k9_relat_1(esk6_0,X1))|~r2_hidden(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])])).
% 0.18/0.39  cnf(c_0_35, plain, (r2_hidden(X1,k2_enumset1(X2,X3,X4,X1))), inference(er,[status(thm)],[c_0_29])).
% 0.18/0.39  cnf(c_0_36, plain, (esk3_3(X1,k2_enumset1(X2,X2,X2,X3),X4)=X3|esk3_3(X1,k2_enumset1(X2,X2,X2,X3),X4)=X2|~v1_relat_1(X4)|~r2_hidden(X1,k9_relat_1(X4,k2_enumset1(X2,X2,X2,X3)))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.18/0.39  cnf(c_0_37, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k2_enumset1(X2,X2,X2,X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33]), c_0_17]), c_0_18])).
% 0.18/0.39  cnf(c_0_38, negated_conjecture, (r2_hidden(esk5_0,k9_relat_1(esk6_0,k2_enumset1(X1,X2,X3,esk4_0)))|r2_hidden(esk5_0,k11_relat_1(esk6_0,esk4_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.18/0.39  cnf(c_0_39, plain, (r2_hidden(k4_tarski(esk3_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.39  cnf(c_0_40, plain, (esk3_3(X1,k2_enumset1(X2,X2,X2,X2),X3)=X2|~v1_relat_1(X3)|~r2_hidden(X1,k11_relat_1(X3,X2))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.18/0.39  cnf(c_0_41, negated_conjecture, (~r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0)|~r2_hidden(esk5_0,k11_relat_1(esk6_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.39  cnf(c_0_42, negated_conjecture, (r2_hidden(esk5_0,k11_relat_1(esk6_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_37]), c_0_28])])).
% 0.18/0.39  cnf(c_0_43, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)|~r2_hidden(X2,k9_relat_1(X3,k2_enumset1(X1,X1,X1,X1)))|~r2_hidden(X2,k11_relat_1(X3,X1))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.18/0.39  cnf(c_0_44, negated_conjecture, (~r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42])])).
% 0.18/0.39  cnf(c_0_45, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)|~r2_hidden(X2,k11_relat_1(X3,X1))), inference(spm,[status(thm)],[c_0_43, c_0_37])).
% 0.18/0.39  cnf(c_0_46, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_28]), c_0_42])]), ['proof']).
% 0.18/0.39  # SZS output end CNFRefutation
% 0.18/0.39  # Proof object total steps             : 47
% 0.18/0.39  # Proof object clause steps            : 28
% 0.18/0.39  # Proof object formula steps           : 19
% 0.18/0.39  # Proof object conjectures             : 11
% 0.18/0.39  # Proof object clause conjectures      : 8
% 0.18/0.39  # Proof object formula conjectures     : 3
% 0.18/0.39  # Proof object initial clauses used    : 13
% 0.18/0.39  # Proof object initial formulas used   : 9
% 0.18/0.39  # Proof object generating inferences   : 10
% 0.18/0.39  # Proof object simplifying inferences  : 16
% 0.18/0.39  # Training examples: 0 positive, 0 negative
% 0.18/0.39  # Parsed axioms                        : 9
% 0.18/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.39  # Initial clauses                      : 29
% 0.18/0.39  # Removed in clause preprocessing      : 3
% 0.18/0.39  # Initial clauses in saturation        : 26
% 0.18/0.39  # Processed clauses                    : 142
% 0.18/0.39  # ...of these trivial                  : 0
% 0.18/0.39  # ...subsumed                          : 29
% 0.18/0.39  # ...remaining for further processing  : 113
% 0.18/0.39  # Other redundant clauses eliminated   : 6
% 0.18/0.39  # Clauses deleted for lack of memory   : 0
% 0.18/0.39  # Backward-subsumed                    : 4
% 0.18/0.39  # Backward-rewritten                   : 5
% 0.18/0.39  # Generated clauses                    : 324
% 0.18/0.39  # ...of the previous two non-trivial   : 310
% 0.18/0.39  # Contextual simplify-reflections      : 1
% 0.18/0.39  # Paramodulations                      : 312
% 0.18/0.39  # Factorizations                       : 0
% 0.18/0.39  # Equation resolutions                 : 12
% 0.18/0.39  # Propositional unsat checks           : 0
% 0.18/0.39  #    Propositional check models        : 0
% 0.18/0.39  #    Propositional check unsatisfiable : 0
% 0.18/0.39  #    Propositional clauses             : 0
% 0.18/0.39  #    Propositional clauses after purity: 0
% 0.18/0.39  #    Propositional unsat core size     : 0
% 0.18/0.39  #    Propositional preprocessing time  : 0.000
% 0.18/0.39  #    Propositional encoding time       : 0.000
% 0.18/0.39  #    Propositional solver time         : 0.000
% 0.18/0.39  #    Success case prop preproc time    : 0.000
% 0.18/0.39  #    Success case prop encoding time   : 0.000
% 0.18/0.39  #    Success case prop solver time     : 0.000
% 0.18/0.39  # Current number of processed clauses  : 74
% 0.18/0.39  #    Positive orientable unit clauses  : 9
% 0.18/0.39  #    Positive unorientable unit clauses: 0
% 0.18/0.39  #    Negative unit clauses             : 1
% 0.18/0.39  #    Non-unit-clauses                  : 64
% 0.18/0.39  # Current number of unprocessed clauses: 197
% 0.18/0.39  # ...number of literals in the above   : 916
% 0.18/0.39  # Current number of archived formulas  : 0
% 0.18/0.39  # Current number of archived clauses   : 36
% 0.18/0.39  # Clause-clause subsumption calls (NU) : 1835
% 0.18/0.39  # Rec. Clause-clause subsumption calls : 1219
% 0.18/0.39  # Non-unit clause-clause subsumptions  : 32
% 0.18/0.39  # Unit Clause-clause subsumption calls : 2
% 0.18/0.39  # Rewrite failures with RHS unbound    : 0
% 0.18/0.39  # BW rewrite match attempts            : 7
% 0.18/0.39  # BW rewrite match successes           : 1
% 0.18/0.39  # Condensation attempts                : 0
% 0.18/0.39  # Condensation successes               : 0
% 0.18/0.39  # Termbank termtop insertions          : 8339
% 0.18/0.39  
% 0.18/0.39  # -------------------------------------------------
% 0.18/0.39  # User time                : 0.052 s
% 0.18/0.39  # System time              : 0.005 s
% 0.18/0.39  # Total time               : 0.057 s
% 0.18/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
