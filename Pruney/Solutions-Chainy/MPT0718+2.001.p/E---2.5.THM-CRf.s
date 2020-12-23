%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:47 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   44 (  84 expanded)
%              Number of clauses        :   25 (  30 expanded)
%              Number of leaves         :   10 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :  133 ( 387 expanded)
%              Number of equality atoms :   22 (  55 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal clause size      :   19 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t173_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( v5_funct_1(X1,X2)
              & k1_relat_1(X1) = k1_relat_1(X2) )
           => v2_relat_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_funct_1)).

fof(d15_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_relat_1(X1)
      <=> ! [X2] :
            ~ ( r2_hidden(X2,k1_relat_1(X1))
              & v1_xboole_0(k1_funct_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_funct_1)).

fof(t142_funct_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k2_relat_1(X2))
      <=> k10_relat_1(X2,k1_tarski(X1)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(cc1_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(d20_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( v5_funct_1(X2,X1)
          <=> ! [X3] :
                ( r2_hidden(X3,k1_relat_1(X2))
               => r2_hidden(k1_funct_1(X2,X3),k1_funct_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(t172_relat_1,axiom,(
    ! [X1] : k10_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ( ( v5_funct_1(X1,X2)
                & k1_relat_1(X1) = k1_relat_1(X2) )
             => v2_relat_1(X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t173_funct_1])).

fof(c_0_11,plain,(
    ! [X8,X9] :
      ( ( ~ v2_relat_1(X8)
        | ~ r2_hidden(X9,k1_relat_1(X8))
        | ~ v1_xboole_0(k1_funct_1(X8,X9))
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( r2_hidden(esk1_1(X8),k1_relat_1(X8))
        | v2_relat_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( v1_xboole_0(k1_funct_1(X8,esk1_1(X8)))
        | v2_relat_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d15_funct_1])])])])])).

fof(c_0_12,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & v1_relat_1(esk4_0)
    & v1_funct_1(esk4_0)
    & v5_funct_1(esk3_0,esk4_0)
    & k1_relat_1(esk3_0) = k1_relat_1(esk4_0)
    & ~ v2_relat_1(esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_13,plain,(
    ! [X15,X16] :
      ( ( ~ r2_hidden(X15,k2_relat_1(X16))
        | k10_relat_1(X16,k1_tarski(X15)) != k1_xboole_0
        | ~ v1_relat_1(X16) )
      & ( k10_relat_1(X16,k1_tarski(X15)) = k1_xboole_0
        | r2_hidden(X15,k2_relat_1(X16))
        | ~ v1_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t142_funct_1])])])).

fof(c_0_14,plain,(
    ! [X5] : k2_tarski(X5,X5) = k1_tarski(X5) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_15,plain,(
    ! [X6] :
      ( ~ v1_xboole_0(X6)
      | v1_relat_1(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).

fof(c_0_16,plain,(
    ! [X11,X12,X13] :
      ( ( ~ v5_funct_1(X12,X11)
        | ~ r2_hidden(X13,k1_relat_1(X12))
        | r2_hidden(k1_funct_1(X12,X13),k1_funct_1(X11,X13))
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( r2_hidden(esk2_2(X11,X12),k1_relat_1(X12))
        | v5_funct_1(X12,X11)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( ~ r2_hidden(k1_funct_1(X12,esk2_2(X11,X12)),k1_funct_1(X11,esk2_2(X11,X12)))
        | v5_funct_1(X12,X11)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_funct_1])])])])])).

fof(c_0_17,plain,(
    ! [X4] :
      ( ~ v1_xboole_0(X4)
      | X4 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_18,plain,
    ( v1_xboole_0(k1_funct_1(X1,esk1_1(X1)))
    | v2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,k2_relat_1(X2))
    | k10_relat_1(X2,k1_tarski(X1)) != k1_xboole_0
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_24,plain,(
    ! [X7] : k10_relat_1(k1_xboole_0,X7) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t172_relat_1])).

cnf(c_0_25,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_27,plain,
    ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X2,X3))
    | ~ v5_funct_1(X1,X2)
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( v5_funct_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_29,negated_conjecture,
    ( k1_relat_1(esk3_0) = k1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_31,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_32,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_33,negated_conjecture,
    ( v1_xboole_0(k1_funct_1(esk4_0,esk1_1(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_34,plain,
    ( r2_hidden(esk1_1(X1),k1_relat_1(X1))
    | v2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_35,plain,
    ( k10_relat_1(X2,k2_tarski(X1,X1)) != k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k2_relat_1(X2)) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_36,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_37,plain,
    ( k10_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_38,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk3_0,X1),k1_funct_1(esk4_0,X1))
    | ~ r2_hidden(X1,k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_19]),c_0_30]),c_0_20]),c_0_31])])).

cnf(c_0_40,negated_conjecture,
    ( k1_funct_1(esk4_0,esk1_1(esk4_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk1_1(esk4_0),k1_relat_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38])])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])]),c_0_42]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:29:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S04AI
% 0.19/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.040 s
% 0.19/0.39  # Presaturation interreduction done
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(t173_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v5_funct_1(X1,X2)&k1_relat_1(X1)=k1_relat_1(X2))=>v2_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_funct_1)).
% 0.19/0.39  fof(d15_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_relat_1(X1)<=>![X2]:~((r2_hidden(X2,k1_relat_1(X1))&v1_xboole_0(k1_funct_1(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d15_funct_1)).
% 0.19/0.39  fof(t142_funct_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k2_relat_1(X2))<=>k10_relat_1(X2,k1_tarski(X1))!=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_1)).
% 0.19/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.39  fof(cc1_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 0.19/0.39  fof(d20_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v5_funct_1(X2,X1)<=>![X3]:(r2_hidden(X3,k1_relat_1(X2))=>r2_hidden(k1_funct_1(X2,X3),k1_funct_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_funct_1)).
% 0.19/0.39  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.19/0.39  fof(t172_relat_1, axiom, ![X1]:k10_relat_1(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 0.19/0.39  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.39  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.19/0.39  fof(c_0_10, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v5_funct_1(X1,X2)&k1_relat_1(X1)=k1_relat_1(X2))=>v2_relat_1(X2))))), inference(assume_negation,[status(cth)],[t173_funct_1])).
% 0.19/0.39  fof(c_0_11, plain, ![X8, X9]:((~v2_relat_1(X8)|(~r2_hidden(X9,k1_relat_1(X8))|~v1_xboole_0(k1_funct_1(X8,X9)))|(~v1_relat_1(X8)|~v1_funct_1(X8)))&((r2_hidden(esk1_1(X8),k1_relat_1(X8))|v2_relat_1(X8)|(~v1_relat_1(X8)|~v1_funct_1(X8)))&(v1_xboole_0(k1_funct_1(X8,esk1_1(X8)))|v2_relat_1(X8)|(~v1_relat_1(X8)|~v1_funct_1(X8))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d15_funct_1])])])])])).
% 0.19/0.39  fof(c_0_12, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&((v5_funct_1(esk3_0,esk4_0)&k1_relat_1(esk3_0)=k1_relat_1(esk4_0))&~v2_relat_1(esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.19/0.39  fof(c_0_13, plain, ![X15, X16]:((~r2_hidden(X15,k2_relat_1(X16))|k10_relat_1(X16,k1_tarski(X15))!=k1_xboole_0|~v1_relat_1(X16))&(k10_relat_1(X16,k1_tarski(X15))=k1_xboole_0|r2_hidden(X15,k2_relat_1(X16))|~v1_relat_1(X16))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t142_funct_1])])])).
% 0.19/0.39  fof(c_0_14, plain, ![X5]:k2_tarski(X5,X5)=k1_tarski(X5), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.39  fof(c_0_15, plain, ![X6]:(~v1_xboole_0(X6)|v1_relat_1(X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).
% 0.19/0.39  fof(c_0_16, plain, ![X11, X12, X13]:((~v5_funct_1(X12,X11)|(~r2_hidden(X13,k1_relat_1(X12))|r2_hidden(k1_funct_1(X12,X13),k1_funct_1(X11,X13)))|(~v1_relat_1(X12)|~v1_funct_1(X12))|(~v1_relat_1(X11)|~v1_funct_1(X11)))&((r2_hidden(esk2_2(X11,X12),k1_relat_1(X12))|v5_funct_1(X12,X11)|(~v1_relat_1(X12)|~v1_funct_1(X12))|(~v1_relat_1(X11)|~v1_funct_1(X11)))&(~r2_hidden(k1_funct_1(X12,esk2_2(X11,X12)),k1_funct_1(X11,esk2_2(X11,X12)))|v5_funct_1(X12,X11)|(~v1_relat_1(X12)|~v1_funct_1(X12))|(~v1_relat_1(X11)|~v1_funct_1(X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_funct_1])])])])])).
% 0.19/0.39  fof(c_0_17, plain, ![X4]:(~v1_xboole_0(X4)|X4=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.19/0.39  cnf(c_0_18, plain, (v1_xboole_0(k1_funct_1(X1,esk1_1(X1)))|v2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.39  cnf(c_0_19, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.39  cnf(c_0_20, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.39  cnf(c_0_21, negated_conjecture, (~v2_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.39  cnf(c_0_22, plain, (~r2_hidden(X1,k2_relat_1(X2))|k10_relat_1(X2,k1_tarski(X1))!=k1_xboole_0|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.39  cnf(c_0_23, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.39  fof(c_0_24, plain, ![X7]:k10_relat_1(k1_xboole_0,X7)=k1_xboole_0, inference(variable_rename,[status(thm)],[t172_relat_1])).
% 0.19/0.39  cnf(c_0_25, plain, (v1_relat_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.39  cnf(c_0_26, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.39  cnf(c_0_27, plain, (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X2,X3))|~v5_funct_1(X1,X2)|~r2_hidden(X3,k1_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.39  cnf(c_0_28, negated_conjecture, (v5_funct_1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.39  cnf(c_0_29, negated_conjecture, (k1_relat_1(esk3_0)=k1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.39  cnf(c_0_30, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.39  cnf(c_0_31, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.39  cnf(c_0_32, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.39  cnf(c_0_33, negated_conjecture, (v1_xboole_0(k1_funct_1(esk4_0,esk1_1(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])]), c_0_21])).
% 0.19/0.39  cnf(c_0_34, plain, (r2_hidden(esk1_1(X1),k1_relat_1(X1))|v2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.39  cnf(c_0_35, plain, (k10_relat_1(X2,k2_tarski(X1,X1))!=k1_xboole_0|~v1_relat_1(X2)|~r2_hidden(X1,k2_relat_1(X2))), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.39  cnf(c_0_36, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.19/0.39  cnf(c_0_37, plain, (k10_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.39  cnf(c_0_38, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.39  cnf(c_0_39, negated_conjecture, (r2_hidden(k1_funct_1(esk3_0,X1),k1_funct_1(esk4_0,X1))|~r2_hidden(X1,k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_19]), c_0_30]), c_0_20]), c_0_31])])).
% 0.19/0.39  cnf(c_0_40, negated_conjecture, (k1_funct_1(esk4_0,esk1_1(esk4_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.39  cnf(c_0_41, negated_conjecture, (r2_hidden(esk1_1(esk4_0),k1_relat_1(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_19]), c_0_20])]), c_0_21])).
% 0.19/0.39  cnf(c_0_42, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38])])).
% 0.19/0.39  cnf(c_0_43, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])]), c_0_42]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 44
% 0.19/0.39  # Proof object clause steps            : 25
% 0.19/0.39  # Proof object formula steps           : 19
% 0.19/0.39  # Proof object conjectures             : 15
% 0.19/0.39  # Proof object clause conjectures      : 12
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 17
% 0.19/0.39  # Proof object initial formulas used   : 10
% 0.19/0.39  # Proof object generating inferences   : 7
% 0.19/0.39  # Proof object simplifying inferences  : 19
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 10
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 22
% 0.19/0.39  # Removed in clause preprocessing      : 1
% 0.19/0.39  # Initial clauses in saturation        : 21
% 0.19/0.39  # Processed clauses                    : 63
% 0.19/0.39  # ...of these trivial                  : 0
% 0.19/0.39  # ...subsumed                          : 0
% 0.19/0.39  # ...remaining for further processing  : 63
% 0.19/0.39  # Other redundant clauses eliminated   : 0
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 0
% 0.19/0.39  # Backward-rewritten                   : 2
% 0.19/0.39  # Generated clauses                    : 31
% 0.19/0.39  # ...of the previous two non-trivial   : 25
% 0.19/0.39  # Contextual simplify-reflections      : 0
% 0.19/0.39  # Paramodulations                      : 31
% 0.19/0.39  # Factorizations                       : 0
% 0.19/0.39  # Equation resolutions                 : 0
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 40
% 0.19/0.39  #    Positive orientable unit clauses  : 13
% 0.19/0.39  #    Positive unorientable unit clauses: 0
% 0.19/0.39  #    Negative unit clauses             : 2
% 0.19/0.39  #    Non-unit-clauses                  : 25
% 0.19/0.39  # Current number of unprocessed clauses: 4
% 0.19/0.39  # ...number of literals in the above   : 16
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 24
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 80
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 19
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.39  # Unit Clause-clause subsumption calls : 2
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 1
% 0.19/0.39  # BW rewrite match successes           : 1
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 2066
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.043 s
% 0.19/0.39  # System time              : 0.003 s
% 0.19/0.39  # Total time               : 0.046 s
% 0.19/0.39  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
