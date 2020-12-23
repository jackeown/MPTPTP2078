%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:05 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 238 expanded)
%              Number of clauses        :   29 (  87 expanded)
%              Number of leaves         :    8 (  63 expanded)
%              Depth                    :   10
%              Number of atoms          :  181 ( 967 expanded)
%              Number of equality atoms :  102 ( 550 expanded)
%              Maximal formula depth    :   32 (   5 average)
%              Maximal clause size      :   44 (   2 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_funct_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(d3_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( X6 = k3_enumset1(X1,X2,X3,X4,X5)
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ~ ( X7 != X1
              & X7 != X2
              & X7 != X3
              & X7 != X4
              & X7 != X5 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).

fof(t12_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => r2_hidden(k1_funct_1(X2,X1),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

fof(c_0_8,negated_conjecture,(
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

fof(c_0_9,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & v1_funct_1(esk4_0)
    & v1_relat_1(esk5_0)
    & v1_funct_1(esk5_0)
    & k1_relat_1(esk4_0) = k1_relat_1(esk5_0)
    & k2_relat_1(esk4_0) = k1_tarski(esk3_0)
    & k2_relat_1(esk5_0) = k1_tarski(esk3_0)
    & esk4_0 != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_10,plain,(
    ! [X8] : k2_tarski(X8,X8) = k1_tarski(X8) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_11,plain,(
    ! [X9,X10] : k1_enumset1(X9,X9,X10) = k2_tarski(X9,X10) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_12,plain,(
    ! [X11,X12,X13] : k2_enumset1(X11,X11,X12,X13) = k1_enumset1(X11,X12,X13) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_13,plain,(
    ! [X14,X15,X16,X17] : k3_enumset1(X14,X14,X15,X16,X17) = k2_enumset1(X14,X15,X16,X17) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

cnf(c_0_14,negated_conjecture,
    ( k2_relat_1(esk5_0) = k1_tarski(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( k2_relat_1(esk4_0) = k1_tarski(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_20,plain,(
    ! [X18,X19,X20,X21,X22,X23,X24,X25,X26,X27,X28,X29,X30,X31] :
      ( ( ~ r2_hidden(X24,X23)
        | X24 = X18
        | X24 = X19
        | X24 = X20
        | X24 = X21
        | X24 = X22
        | X23 != k3_enumset1(X18,X19,X20,X21,X22) )
      & ( X25 != X18
        | r2_hidden(X25,X23)
        | X23 != k3_enumset1(X18,X19,X20,X21,X22) )
      & ( X25 != X19
        | r2_hidden(X25,X23)
        | X23 != k3_enumset1(X18,X19,X20,X21,X22) )
      & ( X25 != X20
        | r2_hidden(X25,X23)
        | X23 != k3_enumset1(X18,X19,X20,X21,X22) )
      & ( X25 != X21
        | r2_hidden(X25,X23)
        | X23 != k3_enumset1(X18,X19,X20,X21,X22) )
      & ( X25 != X22
        | r2_hidden(X25,X23)
        | X23 != k3_enumset1(X18,X19,X20,X21,X22) )
      & ( esk1_6(X26,X27,X28,X29,X30,X31) != X26
        | ~ r2_hidden(esk1_6(X26,X27,X28,X29,X30,X31),X31)
        | X31 = k3_enumset1(X26,X27,X28,X29,X30) )
      & ( esk1_6(X26,X27,X28,X29,X30,X31) != X27
        | ~ r2_hidden(esk1_6(X26,X27,X28,X29,X30,X31),X31)
        | X31 = k3_enumset1(X26,X27,X28,X29,X30) )
      & ( esk1_6(X26,X27,X28,X29,X30,X31) != X28
        | ~ r2_hidden(esk1_6(X26,X27,X28,X29,X30,X31),X31)
        | X31 = k3_enumset1(X26,X27,X28,X29,X30) )
      & ( esk1_6(X26,X27,X28,X29,X30,X31) != X29
        | ~ r2_hidden(esk1_6(X26,X27,X28,X29,X30,X31),X31)
        | X31 = k3_enumset1(X26,X27,X28,X29,X30) )
      & ( esk1_6(X26,X27,X28,X29,X30,X31) != X30
        | ~ r2_hidden(esk1_6(X26,X27,X28,X29,X30,X31),X31)
        | X31 = k3_enumset1(X26,X27,X28,X29,X30) )
      & ( r2_hidden(esk1_6(X26,X27,X28,X29,X30,X31),X31)
        | esk1_6(X26,X27,X28,X29,X30,X31) = X26
        | esk1_6(X26,X27,X28,X29,X30,X31) = X27
        | esk1_6(X26,X27,X28,X29,X30,X31) = X28
        | esk1_6(X26,X27,X28,X29,X30,X31) = X29
        | esk1_6(X26,X27,X28,X29,X30,X31) = X30
        | X31 = k3_enumset1(X26,X27,X28,X29,X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_enumset1])])])])])])).

cnf(c_0_21,negated_conjecture,
    ( k2_relat_1(esk5_0) = k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( k2_relat_1(esk4_0) = k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_15]),c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_23,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | X1 = X6
    | X1 = X7
    | ~ r2_hidden(X1,X2)
    | X2 != k3_enumset1(X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( k2_relat_1(esk4_0) = k2_relat_1(esk5_0) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | X1 = X5
    | X1 = X6
    | ~ r2_hidden(X1,k3_enumset1(X6,X5,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k2_relat_1(esk5_0) ),
    inference(rw,[status(thm)],[c_0_22,c_0_24])).

fof(c_0_27,plain,(
    ! [X33,X34] :
      ( ~ v1_relat_1(X34)
      | ~ v1_funct_1(X34)
      | ~ r2_hidden(X33,k1_relat_1(X34))
      | r2_hidden(k1_funct_1(X34,X33),k2_relat_1(X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_1])])).

fof(c_0_28,plain,(
    ! [X35,X36] :
      ( ( r2_hidden(esk2_2(X35,X36),k1_relat_1(X35))
        | k1_relat_1(X35) != k1_relat_1(X36)
        | X35 = X36
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( k1_funct_1(X35,esk2_2(X35,X36)) != k1_funct_1(X36,esk2_2(X35,X36))
        | k1_relat_1(X35) != k1_relat_1(X36)
        | X35 = X36
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_1])])])])])).

cnf(c_0_29,negated_conjecture,
    ( X1 = esk3_0
    | ~ r2_hidden(X1,k2_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_32,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_34,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_35,negated_conjecture,
    ( k1_relat_1(esk4_0) = k1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_36,plain,
    ( r2_hidden(esk2_2(X1,X2),k1_relat_1(X1))
    | X1 = X2
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( X1 = X2
    | k1_funct_1(X1,esk2_2(X1,X2)) != k1_funct_1(X2,esk2_2(X1,X2))
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( k1_funct_1(esk5_0,X1) = esk3_0
    | ~ r2_hidden(X1,k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32])])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk4_0,X1),k2_relat_1(esk5_0))
    | ~ r2_hidden(X1,k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_24]),c_0_33]),c_0_34]),c_0_35])])).

cnf(c_0_40,negated_conjecture,
    ( X1 = esk5_0
    | r2_hidden(esk2_2(X1,esk5_0),k1_relat_1(X1))
    | k1_relat_1(X1) != k1_relat_1(esk5_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_31]),c_0_32])])).

cnf(c_0_41,negated_conjecture,
    ( esk4_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_42,negated_conjecture,
    ( X1 = esk5_0
    | k1_funct_1(X1,esk2_2(X1,esk5_0)) != esk3_0
    | k1_relat_1(X1) != k1_relat_1(esk5_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(esk2_2(X1,esk5_0),k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_31]),c_0_32])])).

cnf(c_0_43,negated_conjecture,
    ( k1_funct_1(esk4_0,X1) = esk3_0
    | ~ r2_hidden(X1,k1_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk2_2(esk4_0,esk5_0),k1_relat_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_35]),c_0_33]),c_0_34])]),c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_35]),c_0_33]),c_0_34]),c_0_44])]),c_0_41]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:49:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.18/0.36  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.18/0.36  #
% 0.18/0.36  # Preprocessing time       : 0.028 s
% 0.18/0.36  # Presaturation interreduction done
% 0.18/0.36  
% 0.18/0.36  # Proof found!
% 0.18/0.36  # SZS status Theorem
% 0.18/0.36  # SZS output start CNFRefutation
% 0.18/0.36  fof(t17_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(((k1_relat_1(X2)=k1_relat_1(X3)&k2_relat_1(X2)=k1_tarski(X1))&k2_relat_1(X3)=k1_tarski(X1))=>X2=X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_funct_1)).
% 0.18/0.36  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.18/0.36  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.18/0.36  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.18/0.36  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.18/0.36  fof(d3_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:(X6=k3_enumset1(X1,X2,X3,X4,X5)<=>![X7]:(r2_hidden(X7,X6)<=>~(((((X7!=X1&X7!=X2)&X7!=X3)&X7!=X4)&X7!=X5)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_enumset1)).
% 0.18/0.36  fof(t12_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r2_hidden(X1,k1_relat_1(X2))=>r2_hidden(k1_funct_1(X2,X1),k2_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 0.18/0.36  fof(t9_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((k1_relat_1(X1)=k1_relat_1(X2)&![X3]:(r2_hidden(X3,k1_relat_1(X1))=>k1_funct_1(X1,X3)=k1_funct_1(X2,X3)))=>X1=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 0.18/0.36  fof(c_0_8, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(((k1_relat_1(X2)=k1_relat_1(X3)&k2_relat_1(X2)=k1_tarski(X1))&k2_relat_1(X3)=k1_tarski(X1))=>X2=X3)))), inference(assume_negation,[status(cth)],[t17_funct_1])).
% 0.18/0.36  fof(c_0_9, negated_conjecture, ((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&((v1_relat_1(esk5_0)&v1_funct_1(esk5_0))&(((k1_relat_1(esk4_0)=k1_relat_1(esk5_0)&k2_relat_1(esk4_0)=k1_tarski(esk3_0))&k2_relat_1(esk5_0)=k1_tarski(esk3_0))&esk4_0!=esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.18/0.36  fof(c_0_10, plain, ![X8]:k2_tarski(X8,X8)=k1_tarski(X8), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.18/0.36  fof(c_0_11, plain, ![X9, X10]:k1_enumset1(X9,X9,X10)=k2_tarski(X9,X10), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.18/0.36  fof(c_0_12, plain, ![X11, X12, X13]:k2_enumset1(X11,X11,X12,X13)=k1_enumset1(X11,X12,X13), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.18/0.36  fof(c_0_13, plain, ![X14, X15, X16, X17]:k3_enumset1(X14,X14,X15,X16,X17)=k2_enumset1(X14,X15,X16,X17), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.18/0.36  cnf(c_0_14, negated_conjecture, (k2_relat_1(esk5_0)=k1_tarski(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.36  cnf(c_0_15, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.36  cnf(c_0_16, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.36  cnf(c_0_17, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.36  cnf(c_0_18, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.36  cnf(c_0_19, negated_conjecture, (k2_relat_1(esk4_0)=k1_tarski(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.36  fof(c_0_20, plain, ![X18, X19, X20, X21, X22, X23, X24, X25, X26, X27, X28, X29, X30, X31]:(((~r2_hidden(X24,X23)|(X24=X18|X24=X19|X24=X20|X24=X21|X24=X22)|X23!=k3_enumset1(X18,X19,X20,X21,X22))&(((((X25!=X18|r2_hidden(X25,X23)|X23!=k3_enumset1(X18,X19,X20,X21,X22))&(X25!=X19|r2_hidden(X25,X23)|X23!=k3_enumset1(X18,X19,X20,X21,X22)))&(X25!=X20|r2_hidden(X25,X23)|X23!=k3_enumset1(X18,X19,X20,X21,X22)))&(X25!=X21|r2_hidden(X25,X23)|X23!=k3_enumset1(X18,X19,X20,X21,X22)))&(X25!=X22|r2_hidden(X25,X23)|X23!=k3_enumset1(X18,X19,X20,X21,X22))))&((((((esk1_6(X26,X27,X28,X29,X30,X31)!=X26|~r2_hidden(esk1_6(X26,X27,X28,X29,X30,X31),X31)|X31=k3_enumset1(X26,X27,X28,X29,X30))&(esk1_6(X26,X27,X28,X29,X30,X31)!=X27|~r2_hidden(esk1_6(X26,X27,X28,X29,X30,X31),X31)|X31=k3_enumset1(X26,X27,X28,X29,X30)))&(esk1_6(X26,X27,X28,X29,X30,X31)!=X28|~r2_hidden(esk1_6(X26,X27,X28,X29,X30,X31),X31)|X31=k3_enumset1(X26,X27,X28,X29,X30)))&(esk1_6(X26,X27,X28,X29,X30,X31)!=X29|~r2_hidden(esk1_6(X26,X27,X28,X29,X30,X31),X31)|X31=k3_enumset1(X26,X27,X28,X29,X30)))&(esk1_6(X26,X27,X28,X29,X30,X31)!=X30|~r2_hidden(esk1_6(X26,X27,X28,X29,X30,X31),X31)|X31=k3_enumset1(X26,X27,X28,X29,X30)))&(r2_hidden(esk1_6(X26,X27,X28,X29,X30,X31),X31)|(esk1_6(X26,X27,X28,X29,X30,X31)=X26|esk1_6(X26,X27,X28,X29,X30,X31)=X27|esk1_6(X26,X27,X28,X29,X30,X31)=X28|esk1_6(X26,X27,X28,X29,X30,X31)=X29|esk1_6(X26,X27,X28,X29,X30,X31)=X30)|X31=k3_enumset1(X26,X27,X28,X29,X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_enumset1])])])])])])).
% 0.18/0.36  cnf(c_0_21, negated_conjecture, (k2_relat_1(esk5_0)=k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_17]), c_0_18])).
% 0.18/0.36  cnf(c_0_22, negated_conjecture, (k2_relat_1(esk4_0)=k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_15]), c_0_16]), c_0_17]), c_0_18])).
% 0.18/0.36  cnf(c_0_23, plain, (X1=X3|X1=X4|X1=X5|X1=X6|X1=X7|~r2_hidden(X1,X2)|X2!=k3_enumset1(X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.36  cnf(c_0_24, negated_conjecture, (k2_relat_1(esk4_0)=k2_relat_1(esk5_0)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.18/0.36  cnf(c_0_25, plain, (X1=X2|X1=X3|X1=X4|X1=X5|X1=X6|~r2_hidden(X1,k3_enumset1(X6,X5,X4,X3,X2))), inference(er,[status(thm)],[c_0_23])).
% 0.18/0.36  cnf(c_0_26, negated_conjecture, (k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k2_relat_1(esk5_0)), inference(rw,[status(thm)],[c_0_22, c_0_24])).
% 0.18/0.36  fof(c_0_27, plain, ![X33, X34]:(~v1_relat_1(X34)|~v1_funct_1(X34)|(~r2_hidden(X33,k1_relat_1(X34))|r2_hidden(k1_funct_1(X34,X33),k2_relat_1(X34)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_1])])).
% 0.18/0.36  fof(c_0_28, plain, ![X35, X36]:((r2_hidden(esk2_2(X35,X36),k1_relat_1(X35))|k1_relat_1(X35)!=k1_relat_1(X36)|X35=X36|(~v1_relat_1(X36)|~v1_funct_1(X36))|(~v1_relat_1(X35)|~v1_funct_1(X35)))&(k1_funct_1(X35,esk2_2(X35,X36))!=k1_funct_1(X36,esk2_2(X35,X36))|k1_relat_1(X35)!=k1_relat_1(X36)|X35=X36|(~v1_relat_1(X36)|~v1_funct_1(X36))|(~v1_relat_1(X35)|~v1_funct_1(X35)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_1])])])])])).
% 0.18/0.36  cnf(c_0_29, negated_conjecture, (X1=esk3_0|~r2_hidden(X1,k2_relat_1(esk5_0))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.18/0.36  cnf(c_0_30, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.18/0.36  cnf(c_0_31, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.36  cnf(c_0_32, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.36  cnf(c_0_33, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.36  cnf(c_0_34, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.36  cnf(c_0_35, negated_conjecture, (k1_relat_1(esk4_0)=k1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.36  cnf(c_0_36, plain, (r2_hidden(esk2_2(X1,X2),k1_relat_1(X1))|X1=X2|k1_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.36  cnf(c_0_37, plain, (X1=X2|k1_funct_1(X1,esk2_2(X1,X2))!=k1_funct_1(X2,esk2_2(X1,X2))|k1_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.36  cnf(c_0_38, negated_conjecture, (k1_funct_1(esk5_0,X1)=esk3_0|~r2_hidden(X1,k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32])])).
% 0.18/0.36  cnf(c_0_39, negated_conjecture, (r2_hidden(k1_funct_1(esk4_0,X1),k2_relat_1(esk5_0))|~r2_hidden(X1,k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_24]), c_0_33]), c_0_34]), c_0_35])])).
% 0.18/0.36  cnf(c_0_40, negated_conjecture, (X1=esk5_0|r2_hidden(esk2_2(X1,esk5_0),k1_relat_1(X1))|k1_relat_1(X1)!=k1_relat_1(esk5_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_31]), c_0_32])])).
% 0.18/0.36  cnf(c_0_41, negated_conjecture, (esk4_0!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.36  cnf(c_0_42, negated_conjecture, (X1=esk5_0|k1_funct_1(X1,esk2_2(X1,esk5_0))!=esk3_0|k1_relat_1(X1)!=k1_relat_1(esk5_0)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(esk2_2(X1,esk5_0),k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_31]), c_0_32])])).
% 0.18/0.36  cnf(c_0_43, negated_conjecture, (k1_funct_1(esk4_0,X1)=esk3_0|~r2_hidden(X1,k1_relat_1(esk5_0))), inference(spm,[status(thm)],[c_0_29, c_0_39])).
% 0.18/0.36  cnf(c_0_44, negated_conjecture, (r2_hidden(esk2_2(esk4_0,esk5_0),k1_relat_1(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_35]), c_0_33]), c_0_34])]), c_0_41])).
% 0.18/0.36  cnf(c_0_45, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_35]), c_0_33]), c_0_34]), c_0_44])]), c_0_41]), ['proof']).
% 0.18/0.36  # SZS output end CNFRefutation
% 0.18/0.36  # Proof object total steps             : 46
% 0.18/0.36  # Proof object clause steps            : 29
% 0.18/0.36  # Proof object formula steps           : 17
% 0.18/0.36  # Proof object conjectures             : 23
% 0.18/0.36  # Proof object clause conjectures      : 20
% 0.18/0.36  # Proof object formula conjectures     : 3
% 0.18/0.36  # Proof object initial clauses used    : 16
% 0.18/0.36  # Proof object initial formulas used   : 8
% 0.18/0.36  # Proof object generating inferences   : 8
% 0.18/0.36  # Proof object simplifying inferences  : 33
% 0.18/0.36  # Training examples: 0 positive, 0 negative
% 0.18/0.36  # Parsed axioms                        : 8
% 0.18/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.36  # Initial clauses                      : 27
% 0.18/0.36  # Removed in clause preprocessing      : 4
% 0.18/0.36  # Initial clauses in saturation        : 23
% 0.18/0.36  # Processed clauses                    : 62
% 0.18/0.36  # ...of these trivial                  : 0
% 0.18/0.36  # ...subsumed                          : 0
% 0.18/0.36  # ...remaining for further processing  : 62
% 0.18/0.36  # Other redundant clauses eliminated   : 11
% 0.18/0.36  # Clauses deleted for lack of memory   : 0
% 0.18/0.36  # Backward-subsumed                    : 0
% 0.18/0.36  # Backward-rewritten                   : 1
% 0.18/0.36  # Generated clauses                    : 29
% 0.18/0.36  # ...of the previous two non-trivial   : 20
% 0.18/0.36  # Contextual simplify-reflections      : 0
% 0.18/0.36  # Paramodulations                      : 20
% 0.18/0.36  # Factorizations                       : 0
% 0.18/0.36  # Equation resolutions                 : 14
% 0.18/0.36  # Propositional unsat checks           : 0
% 0.18/0.36  #    Propositional check models        : 0
% 0.18/0.36  #    Propositional check unsatisfiable : 0
% 0.18/0.36  #    Propositional clauses             : 0
% 0.18/0.36  #    Propositional clauses after purity: 0
% 0.18/0.36  #    Propositional unsat core size     : 0
% 0.18/0.36  #    Propositional preprocessing time  : 0.000
% 0.18/0.36  #    Propositional encoding time       : 0.000
% 0.18/0.36  #    Propositional solver time         : 0.000
% 0.18/0.36  #    Success case prop preproc time    : 0.000
% 0.18/0.36  #    Success case prop encoding time   : 0.000
% 0.18/0.36  #    Success case prop solver time     : 0.000
% 0.18/0.36  # Current number of processed clauses  : 32
% 0.18/0.36  #    Positive orientable unit clauses  : 15
% 0.18/0.36  #    Positive unorientable unit clauses: 0
% 0.18/0.36  #    Negative unit clauses             : 1
% 0.18/0.36  #    Non-unit-clauses                  : 16
% 0.18/0.36  # Current number of unprocessed clauses: 4
% 0.18/0.36  # ...number of literals in the above   : 25
% 0.18/0.36  # Current number of archived formulas  : 0
% 0.18/0.36  # Current number of archived clauses   : 28
% 0.18/0.36  # Clause-clause subsumption calls (NU) : 54
% 0.18/0.36  # Rec. Clause-clause subsumption calls : 44
% 0.18/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.18/0.36  # Unit Clause-clause subsumption calls : 5
% 0.18/0.36  # Rewrite failures with RHS unbound    : 0
% 0.18/0.36  # BW rewrite match attempts            : 21
% 0.18/0.36  # BW rewrite match successes           : 1
% 0.18/0.36  # Condensation attempts                : 0
% 0.18/0.36  # Condensation successes               : 0
% 0.18/0.36  # Termbank termtop insertions          : 2154
% 0.18/0.36  
% 0.18/0.36  # -------------------------------------------------
% 0.18/0.36  # User time                : 0.026 s
% 0.18/0.36  # System time              : 0.007 s
% 0.18/0.36  # Total time               : 0.033 s
% 0.18/0.36  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
