%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:05 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 276 expanded)
%              Number of clauses        :   31 ( 101 expanded)
%              Number of leaves         :    9 (  75 expanded)
%              Depth                    :   10
%              Number of atoms          :  179 ( 993 expanded)
%              Number of equality atoms :  101 ( 578 expanded)
%              Maximal formula depth    :   27 (   5 average)
%              Maximal clause size      :   36 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t17_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( ( k1_relat_1(X2) = k1_relat_1(X3)
              & k2_relat_1(X2) = k1_tarski(X1)
              & k2_relat_1(X3) = k1_tarski(X1) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_1)).

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

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(d2_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( X5 = k2_enumset1(X1,X2,X3,X4)
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X6 != X1
              & X6 != X2
              & X6 != X3
              & X6 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_enumset1)).

fof(t12_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => r2_hidden(k1_funct_1(X2,X1),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

fof(t9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( k1_relat_1(X1) = k1_relat_1(X2)
              & ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( v1_relat_1(X3)
              & v1_funct_1(X3) )
           => ( ( k1_relat_1(X2) = k1_relat_1(X3)
                & k2_relat_1(X2) = k1_tarski(X1)
                & k2_relat_1(X3) = k1_tarski(X1) )
             => X2 = X3 ) ) ) ),
    inference(assume_negation,[status(cth)],[t17_funct_1])).

fof(c_0_10,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & v1_funct_1(esk4_0)
    & v1_relat_1(esk5_0)
    & v1_funct_1(esk5_0)
    & k1_relat_1(esk4_0) = k1_relat_1(esk5_0)
    & k2_relat_1(esk4_0) = k1_tarski(esk3_0)
    & k2_relat_1(esk5_0) = k1_tarski(esk3_0)
    & esk4_0 != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_11,plain,(
    ! [X7] : k2_tarski(X7,X7) = k1_tarski(X7) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_12,plain,(
    ! [X8,X9] : k1_enumset1(X8,X8,X9) = k2_tarski(X8,X9) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,plain,(
    ! [X10,X11,X12] : k2_enumset1(X10,X10,X11,X12) = k1_enumset1(X10,X11,X12) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_14,plain,(
    ! [X13,X14,X15,X16] : k3_enumset1(X13,X13,X14,X15,X16) = k2_enumset1(X13,X14,X15,X16) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_15,plain,(
    ! [X17,X18,X19,X20,X21] : k4_enumset1(X17,X17,X18,X19,X20,X21) = k3_enumset1(X17,X18,X19,X20,X21) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_16,plain,(
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
      & ( esk1_5(X29,X30,X31,X32,X33) != X29
        | ~ r2_hidden(esk1_5(X29,X30,X31,X32,X33),X33)
        | X33 = k2_enumset1(X29,X30,X31,X32) )
      & ( esk1_5(X29,X30,X31,X32,X33) != X30
        | ~ r2_hidden(esk1_5(X29,X30,X31,X32,X33),X33)
        | X33 = k2_enumset1(X29,X30,X31,X32) )
      & ( esk1_5(X29,X30,X31,X32,X33) != X31
        | ~ r2_hidden(esk1_5(X29,X30,X31,X32,X33),X33)
        | X33 = k2_enumset1(X29,X30,X31,X32) )
      & ( esk1_5(X29,X30,X31,X32,X33) != X32
        | ~ r2_hidden(esk1_5(X29,X30,X31,X32,X33),X33)
        | X33 = k2_enumset1(X29,X30,X31,X32) )
      & ( r2_hidden(esk1_5(X29,X30,X31,X32,X33),X33)
        | esk1_5(X29,X30,X31,X32,X33) = X29
        | esk1_5(X29,X30,X31,X32,X33) = X30
        | esk1_5(X29,X30,X31,X32,X33) = X31
        | esk1_5(X29,X30,X31,X32,X33) = X32
        | X33 = k2_enumset1(X29,X30,X31,X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_enumset1])])])])])])).

cnf(c_0_17,negated_conjecture,
    ( k2_relat_1(esk5_0) = k1_tarski(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( k2_relat_1(esk4_0) = k1_tarski(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_24,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | X1 = X6
    | ~ r2_hidden(X1,X2)
    | X2 != k2_enumset1(X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( k2_relat_1(esk5_0) = k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( k2_relat_1(esk4_0) = k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_27,plain,
    ( X1 = X6
    | X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k4_enumset1(X3,X3,X3,X4,X5,X6)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_21]),c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( k2_relat_1(esk4_0) = k2_relat_1(esk5_0) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_29,plain,(
    ! [X35,X36] :
      ( ~ v1_relat_1(X36)
      | ~ v1_funct_1(X36)
      | ~ r2_hidden(X35,k1_relat_1(X36))
      | r2_hidden(k1_funct_1(X36,X35),k2_relat_1(X36)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_1])])).

cnf(c_0_30,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,k4_enumset1(X5,X5,X5,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k2_relat_1(esk5_0) ),
    inference(rw,[status(thm)],[c_0_26,c_0_28])).

cnf(c_0_32,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_34,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_35,negated_conjecture,
    ( k1_relat_1(esk4_0) = k1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_36,plain,(
    ! [X37,X38] :
      ( ( r2_hidden(esk2_2(X37,X38),k1_relat_1(X37))
        | k1_relat_1(X37) != k1_relat_1(X38)
        | X37 = X38
        | ~ v1_relat_1(X38)
        | ~ v1_funct_1(X38)
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) )
      & ( k1_funct_1(X37,esk2_2(X37,X38)) != k1_funct_1(X38,esk2_2(X37,X38))
        | k1_relat_1(X37) != k1_relat_1(X38)
        | X37 = X38
        | ~ v1_relat_1(X38)
        | ~ v1_funct_1(X38)
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_1])])])])])).

cnf(c_0_37,negated_conjecture,
    ( X1 = esk3_0
    | ~ r2_hidden(X1,k2_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk4_0,X1),k2_relat_1(esk5_0))
    | ~ r2_hidden(X1,k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_28]),c_0_33]),c_0_34]),c_0_35])])).

cnf(c_0_39,plain,
    ( r2_hidden(esk2_2(X1,X2),k1_relat_1(X1))
    | X1 = X2
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_40,plain,
    ( X1 = X2
    | k1_funct_1(X1,esk2_2(X1,X2)) != k1_funct_1(X2,esk2_2(X1,X2))
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( k1_funct_1(esk4_0,X1) = esk3_0
    | ~ r2_hidden(X1,k1_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_43,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_44,negated_conjecture,
    ( X1 = esk4_0
    | r2_hidden(esk2_2(X1,esk4_0),k1_relat_1(X1))
    | k1_relat_1(X1) != k1_relat_1(esk5_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_33]),c_0_35]),c_0_34])])).

cnf(c_0_45,negated_conjecture,
    ( esk4_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_46,negated_conjecture,
    ( X1 = esk4_0
    | k1_funct_1(X1,esk2_2(X1,esk4_0)) != esk3_0
    | k1_relat_1(X1) != k1_relat_1(esk5_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(esk2_2(X1,esk4_0),k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_35]),c_0_33]),c_0_34])])).

cnf(c_0_47,negated_conjecture,
    ( k1_funct_1(esk5_0,X1) = esk3_0
    | ~ r2_hidden(X1,k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_32]),c_0_42]),c_0_43])])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk2_2(esk5_0,esk4_0),k1_relat_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_44]),c_0_42]),c_0_43])]),c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_42]),c_0_43]),c_0_48])]),c_0_45]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:25:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.028 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t17_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(((k1_relat_1(X2)=k1_relat_1(X3)&k2_relat_1(X2)=k1_tarski(X1))&k2_relat_1(X3)=k1_tarski(X1))=>X2=X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_funct_1)).
% 0.19/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.37  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.37  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.19/0.37  fof(d2_enumset1, axiom, ![X1, X2, X3, X4, X5]:(X5=k2_enumset1(X1,X2,X3,X4)<=>![X6]:(r2_hidden(X6,X5)<=>~((((X6!=X1&X6!=X2)&X6!=X3)&X6!=X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_enumset1)).
% 0.19/0.37  fof(t12_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r2_hidden(X1,k1_relat_1(X2))=>r2_hidden(k1_funct_1(X2,X1),k2_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 0.19/0.37  fof(t9_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((k1_relat_1(X1)=k1_relat_1(X2)&![X3]:(r2_hidden(X3,k1_relat_1(X1))=>k1_funct_1(X1,X3)=k1_funct_1(X2,X3)))=>X1=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 0.19/0.37  fof(c_0_9, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(((k1_relat_1(X2)=k1_relat_1(X3)&k2_relat_1(X2)=k1_tarski(X1))&k2_relat_1(X3)=k1_tarski(X1))=>X2=X3)))), inference(assume_negation,[status(cth)],[t17_funct_1])).
% 0.19/0.37  fof(c_0_10, negated_conjecture, ((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&((v1_relat_1(esk5_0)&v1_funct_1(esk5_0))&(((k1_relat_1(esk4_0)=k1_relat_1(esk5_0)&k2_relat_1(esk4_0)=k1_tarski(esk3_0))&k2_relat_1(esk5_0)=k1_tarski(esk3_0))&esk4_0!=esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.19/0.37  fof(c_0_11, plain, ![X7]:k2_tarski(X7,X7)=k1_tarski(X7), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.37  fof(c_0_12, plain, ![X8, X9]:k1_enumset1(X8,X8,X9)=k2_tarski(X8,X9), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.37  fof(c_0_13, plain, ![X10, X11, X12]:k2_enumset1(X10,X10,X11,X12)=k1_enumset1(X10,X11,X12), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.37  fof(c_0_14, plain, ![X13, X14, X15, X16]:k3_enumset1(X13,X13,X14,X15,X16)=k2_enumset1(X13,X14,X15,X16), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.37  fof(c_0_15, plain, ![X17, X18, X19, X20, X21]:k4_enumset1(X17,X17,X18,X19,X20,X21)=k3_enumset1(X17,X18,X19,X20,X21), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.19/0.37  fof(c_0_16, plain, ![X22, X23, X24, X25, X26, X27, X28, X29, X30, X31, X32, X33]:(((~r2_hidden(X27,X26)|(X27=X22|X27=X23|X27=X24|X27=X25)|X26!=k2_enumset1(X22,X23,X24,X25))&((((X28!=X22|r2_hidden(X28,X26)|X26!=k2_enumset1(X22,X23,X24,X25))&(X28!=X23|r2_hidden(X28,X26)|X26!=k2_enumset1(X22,X23,X24,X25)))&(X28!=X24|r2_hidden(X28,X26)|X26!=k2_enumset1(X22,X23,X24,X25)))&(X28!=X25|r2_hidden(X28,X26)|X26!=k2_enumset1(X22,X23,X24,X25))))&(((((esk1_5(X29,X30,X31,X32,X33)!=X29|~r2_hidden(esk1_5(X29,X30,X31,X32,X33),X33)|X33=k2_enumset1(X29,X30,X31,X32))&(esk1_5(X29,X30,X31,X32,X33)!=X30|~r2_hidden(esk1_5(X29,X30,X31,X32,X33),X33)|X33=k2_enumset1(X29,X30,X31,X32)))&(esk1_5(X29,X30,X31,X32,X33)!=X31|~r2_hidden(esk1_5(X29,X30,X31,X32,X33),X33)|X33=k2_enumset1(X29,X30,X31,X32)))&(esk1_5(X29,X30,X31,X32,X33)!=X32|~r2_hidden(esk1_5(X29,X30,X31,X32,X33),X33)|X33=k2_enumset1(X29,X30,X31,X32)))&(r2_hidden(esk1_5(X29,X30,X31,X32,X33),X33)|(esk1_5(X29,X30,X31,X32,X33)=X29|esk1_5(X29,X30,X31,X32,X33)=X30|esk1_5(X29,X30,X31,X32,X33)=X31|esk1_5(X29,X30,X31,X32,X33)=X32)|X33=k2_enumset1(X29,X30,X31,X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_enumset1])])])])])])).
% 0.19/0.37  cnf(c_0_17, negated_conjecture, (k2_relat_1(esk5_0)=k1_tarski(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_18, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.37  cnf(c_0_19, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  cnf(c_0_20, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_21, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  cnf(c_0_22, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.37  cnf(c_0_23, negated_conjecture, (k2_relat_1(esk4_0)=k1_tarski(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_24, plain, (X1=X3|X1=X4|X1=X5|X1=X6|~r2_hidden(X1,X2)|X2!=k2_enumset1(X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.37  cnf(c_0_25, negated_conjecture, (k2_relat_1(esk5_0)=k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22])).
% 0.19/0.37  cnf(c_0_26, negated_conjecture, (k2_relat_1(esk4_0)=k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22])).
% 0.19/0.37  cnf(c_0_27, plain, (X1=X6|X1=X5|X1=X4|X1=X3|X2!=k4_enumset1(X3,X3,X3,X4,X5,X6)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_21]), c_0_22])).
% 0.19/0.37  cnf(c_0_28, negated_conjecture, (k2_relat_1(esk4_0)=k2_relat_1(esk5_0)), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.37  fof(c_0_29, plain, ![X35, X36]:(~v1_relat_1(X36)|~v1_funct_1(X36)|(~r2_hidden(X35,k1_relat_1(X36))|r2_hidden(k1_funct_1(X36,X35),k2_relat_1(X36)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_1])])).
% 0.19/0.37  cnf(c_0_30, plain, (X1=X2|X1=X3|X1=X4|X1=X5|~r2_hidden(X1,k4_enumset1(X5,X5,X5,X4,X3,X2))), inference(er,[status(thm)],[c_0_27])).
% 0.19/0.37  cnf(c_0_31, negated_conjecture, (k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k2_relat_1(esk5_0)), inference(rw,[status(thm)],[c_0_26, c_0_28])).
% 0.19/0.37  cnf(c_0_32, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.37  cnf(c_0_33, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_34, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_35, negated_conjecture, (k1_relat_1(esk4_0)=k1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  fof(c_0_36, plain, ![X37, X38]:((r2_hidden(esk2_2(X37,X38),k1_relat_1(X37))|k1_relat_1(X37)!=k1_relat_1(X38)|X37=X38|(~v1_relat_1(X38)|~v1_funct_1(X38))|(~v1_relat_1(X37)|~v1_funct_1(X37)))&(k1_funct_1(X37,esk2_2(X37,X38))!=k1_funct_1(X38,esk2_2(X37,X38))|k1_relat_1(X37)!=k1_relat_1(X38)|X37=X38|(~v1_relat_1(X38)|~v1_funct_1(X38))|(~v1_relat_1(X37)|~v1_funct_1(X37)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_1])])])])])).
% 0.19/0.37  cnf(c_0_37, negated_conjecture, (X1=esk3_0|~r2_hidden(X1,k2_relat_1(esk5_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.37  cnf(c_0_38, negated_conjecture, (r2_hidden(k1_funct_1(esk4_0,X1),k2_relat_1(esk5_0))|~r2_hidden(X1,k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_28]), c_0_33]), c_0_34]), c_0_35])])).
% 0.19/0.37  cnf(c_0_39, plain, (r2_hidden(esk2_2(X1,X2),k1_relat_1(X1))|X1=X2|k1_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.37  cnf(c_0_40, plain, (X1=X2|k1_funct_1(X1,esk2_2(X1,X2))!=k1_funct_1(X2,esk2_2(X1,X2))|k1_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.37  cnf(c_0_41, negated_conjecture, (k1_funct_1(esk4_0,X1)=esk3_0|~r2_hidden(X1,k1_relat_1(esk5_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.37  cnf(c_0_42, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_43, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_44, negated_conjecture, (X1=esk4_0|r2_hidden(esk2_2(X1,esk4_0),k1_relat_1(X1))|k1_relat_1(X1)!=k1_relat_1(esk5_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_33]), c_0_35]), c_0_34])])).
% 0.19/0.37  cnf(c_0_45, negated_conjecture, (esk4_0!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_46, negated_conjecture, (X1=esk4_0|k1_funct_1(X1,esk2_2(X1,esk4_0))!=esk3_0|k1_relat_1(X1)!=k1_relat_1(esk5_0)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(esk2_2(X1,esk4_0),k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_35]), c_0_33]), c_0_34])])).
% 0.19/0.37  cnf(c_0_47, negated_conjecture, (k1_funct_1(esk5_0,X1)=esk3_0|~r2_hidden(X1,k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_32]), c_0_42]), c_0_43])])).
% 0.19/0.37  cnf(c_0_48, negated_conjecture, (r2_hidden(esk2_2(esk5_0,esk4_0),k1_relat_1(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_44]), c_0_42]), c_0_43])]), c_0_45])).
% 0.19/0.37  cnf(c_0_49, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_42]), c_0_43]), c_0_48])]), c_0_45]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 50
% 0.19/0.37  # Proof object clause steps            : 31
% 0.19/0.37  # Proof object formula steps           : 19
% 0.19/0.37  # Proof object conjectures             : 23
% 0.19/0.37  # Proof object clause conjectures      : 20
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 17
% 0.19/0.37  # Proof object initial formulas used   : 9
% 0.19/0.37  # Proof object generating inferences   : 8
% 0.19/0.37  # Proof object simplifying inferences  : 38
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 9
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 26
% 0.19/0.37  # Removed in clause preprocessing      : 5
% 0.19/0.37  # Initial clauses in saturation        : 21
% 0.19/0.37  # Processed clauses                    : 58
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 0
% 0.19/0.37  # ...remaining for further processing  : 58
% 0.19/0.37  # Other redundant clauses eliminated   : 13
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 1
% 0.19/0.37  # Generated clauses                    : 68
% 0.19/0.37  # ...of the previous two non-trivial   : 52
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 56
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 16
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
% 0.19/0.37  # Current number of processed clauses  : 31
% 0.19/0.37  #    Positive orientable unit clauses  : 14
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 1
% 0.19/0.37  #    Non-unit-clauses                  : 16
% 0.19/0.37  # Current number of unprocessed clauses: 34
% 0.19/0.37  # ...number of literals in the above   : 266
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 27
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 38
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 28
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.37  # Unit Clause-clause subsumption calls : 5
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 13
% 0.19/0.37  # BW rewrite match successes           : 1
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 2811
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.031 s
% 0.19/0.37  # System time              : 0.005 s
% 0.19/0.37  # Total time               : 0.036 s
% 0.19/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
