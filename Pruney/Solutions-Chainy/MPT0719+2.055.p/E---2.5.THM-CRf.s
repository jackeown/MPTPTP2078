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
% DateTime   : Thu Dec  3 10:55:56 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   33 (  77 expanded)
%              Number of clauses        :   19 (  30 expanded)
%              Number of leaves         :    7 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :  102 ( 221 expanded)
%              Number of equality atoms :   14 (  22 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   19 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(fc8_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k7_relat_1(X1,X2))
        & v1_funct_1(k7_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

fof(t110_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).

fof(t174_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => v5_funct_1(k1_xboole_0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_1)).

fof(t142_funct_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k2_relat_1(X2))
      <=> k10_relat_1(X2,k1_tarski(X1)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

fof(t172_relat_1,axiom,(
    ! [X1] : k10_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

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

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(c_0_7,plain,(
    ! [X10,X11] :
      ( ( v1_relat_1(k7_relat_1(X10,X11))
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( v1_funct_1(k7_relat_1(X10,X11))
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).

fof(c_0_8,plain,(
    ! [X4] :
      ( ~ v1_relat_1(X4)
      | k7_relat_1(X4,k1_xboole_0) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t110_relat_1])])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => v5_funct_1(k1_xboole_0,X1) ) ),
    inference(assume_negation,[status(cth)],[t174_funct_1])).

cnf(c_0_10,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k7_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & ~ v5_funct_1(k1_xboole_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_13,plain,
    ( v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_14,plain,(
    ! [X12,X13] :
      ( ( ~ r2_hidden(X12,k2_relat_1(X13))
        | k10_relat_1(X13,k1_tarski(X12)) != k1_xboole_0
        | ~ v1_relat_1(X13) )
      & ( k10_relat_1(X13,k1_tarski(X12)) = k1_xboole_0
        | r2_hidden(X12,k2_relat_1(X13))
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t142_funct_1])])])).

fof(c_0_15,plain,(
    ! [X5] : k10_relat_1(k1_xboole_0,X5) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t172_relat_1])).

cnf(c_0_16,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_19,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v5_funct_1(X7,X6)
        | ~ r2_hidden(X8,k1_relat_1(X7))
        | r2_hidden(k1_funct_1(X7,X8),k1_funct_1(X6,X8))
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( r2_hidden(esk1_2(X6,X7),k1_relat_1(X7))
        | v5_funct_1(X7,X6)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( ~ r2_hidden(k1_funct_1(X7,esk1_2(X6,X7)),k1_funct_1(X6,esk1_2(X6,X7)))
        | v5_funct_1(X7,X6)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_funct_1])])])])])).

cnf(c_0_20,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_11])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,k2_relat_1(X2))
    | k10_relat_1(X2,k1_tarski(X1)) != k1_xboole_0
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k10_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])])).

cnf(c_0_25,plain,
    ( r2_hidden(esk1_2(X1,X2),k1_relat_1(X2))
    | v5_funct_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_17]),c_0_18])])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24])])).

cnf(c_0_29,plain,
    ( r2_hidden(esk1_2(X1,k1_xboole_0),k1_xboole_0)
    | v5_funct_1(k1_xboole_0,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_24])])).

cnf(c_0_30,negated_conjecture,
    ( ~ v5_funct_1(k1_xboole_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_31,plain,
    ( v5_funct_1(k1_xboole_0,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_17]),c_0_18])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:16:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 0.14/0.38  # and selection function SelectNewComplexAHP.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.026 s
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(fc8_funct_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k7_relat_1(X1,X2))&v1_funct_1(k7_relat_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_funct_1)).
% 0.14/0.38  fof(t110_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_relat_1)).
% 0.14/0.38  fof(t174_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>v5_funct_1(k1_xboole_0,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_funct_1)).
% 0.14/0.38  fof(t142_funct_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k2_relat_1(X2))<=>k10_relat_1(X2,k1_tarski(X1))!=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_1)).
% 0.14/0.38  fof(t172_relat_1, axiom, ![X1]:k10_relat_1(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 0.14/0.38  fof(d20_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v5_funct_1(X2,X1)<=>![X3]:(r2_hidden(X3,k1_relat_1(X2))=>r2_hidden(k1_funct_1(X2,X3),k1_funct_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_funct_1)).
% 0.14/0.38  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.14/0.38  fof(c_0_7, plain, ![X10, X11]:((v1_relat_1(k7_relat_1(X10,X11))|(~v1_relat_1(X10)|~v1_funct_1(X10)))&(v1_funct_1(k7_relat_1(X10,X11))|(~v1_relat_1(X10)|~v1_funct_1(X10)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).
% 0.14/0.38  fof(c_0_8, plain, ![X4]:(~v1_relat_1(X4)|k7_relat_1(X4,k1_xboole_0)=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t110_relat_1])])).
% 0.14/0.38  fof(c_0_9, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>v5_funct_1(k1_xboole_0,X1))), inference(assume_negation,[status(cth)],[t174_funct_1])).
% 0.14/0.38  cnf(c_0_10, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  cnf(c_0_11, plain, (k7_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  fof(c_0_12, negated_conjecture, ((v1_relat_1(esk2_0)&v1_funct_1(esk2_0))&~v5_funct_1(k1_xboole_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.14/0.38  cnf(c_0_13, plain, (v1_funct_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  fof(c_0_14, plain, ![X12, X13]:((~r2_hidden(X12,k2_relat_1(X13))|k10_relat_1(X13,k1_tarski(X12))!=k1_xboole_0|~v1_relat_1(X13))&(k10_relat_1(X13,k1_tarski(X12))=k1_xboole_0|r2_hidden(X12,k2_relat_1(X13))|~v1_relat_1(X13))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t142_funct_1])])])).
% 0.14/0.38  fof(c_0_15, plain, ![X5]:k10_relat_1(k1_xboole_0,X5)=k1_xboole_0, inference(variable_rename,[status(thm)],[t172_relat_1])).
% 0.14/0.38  cnf(c_0_16, plain, (v1_relat_1(k1_xboole_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.14/0.38  cnf(c_0_17, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_18, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  fof(c_0_19, plain, ![X6, X7, X8]:((~v5_funct_1(X7,X6)|(~r2_hidden(X8,k1_relat_1(X7))|r2_hidden(k1_funct_1(X7,X8),k1_funct_1(X6,X8)))|(~v1_relat_1(X7)|~v1_funct_1(X7))|(~v1_relat_1(X6)|~v1_funct_1(X6)))&((r2_hidden(esk1_2(X6,X7),k1_relat_1(X7))|v5_funct_1(X7,X6)|(~v1_relat_1(X7)|~v1_funct_1(X7))|(~v1_relat_1(X6)|~v1_funct_1(X6)))&(~r2_hidden(k1_funct_1(X7,esk1_2(X6,X7)),k1_funct_1(X6,esk1_2(X6,X7)))|v5_funct_1(X7,X6)|(~v1_relat_1(X7)|~v1_funct_1(X7))|(~v1_relat_1(X6)|~v1_funct_1(X6))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_funct_1])])])])])).
% 0.14/0.38  cnf(c_0_20, plain, (v1_funct_1(k1_xboole_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_13, c_0_11])).
% 0.14/0.38  cnf(c_0_21, plain, (~r2_hidden(X1,k2_relat_1(X2))|k10_relat_1(X2,k1_tarski(X1))!=k1_xboole_0|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.38  cnf(c_0_22, plain, (k10_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  cnf(c_0_23, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.14/0.38  cnf(c_0_24, negated_conjecture, (v1_relat_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])])).
% 0.14/0.38  cnf(c_0_25, plain, (r2_hidden(esk1_2(X1,X2),k1_relat_1(X2))|v5_funct_1(X2,X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.38  cnf(c_0_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.14/0.38  cnf(c_0_27, negated_conjecture, (v1_funct_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_17]), c_0_18])])).
% 0.14/0.38  cnf(c_0_28, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24])])).
% 0.14/0.38  cnf(c_0_29, plain, (r2_hidden(esk1_2(X1,k1_xboole_0),k1_xboole_0)|v5_funct_1(k1_xboole_0,X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_24])])).
% 0.14/0.38  cnf(c_0_30, negated_conjecture, (~v5_funct_1(k1_xboole_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_31, plain, (v5_funct_1(k1_xboole_0,X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.14/0.38  cnf(c_0_32, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_17]), c_0_18])]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 33
% 0.14/0.38  # Proof object clause steps            : 19
% 0.14/0.38  # Proof object formula steps           : 14
% 0.14/0.38  # Proof object conjectures             : 9
% 0.14/0.38  # Proof object clause conjectures      : 6
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 11
% 0.14/0.38  # Proof object initial formulas used   : 7
% 0.14/0.38  # Proof object generating inferences   : 8
% 0.14/0.38  # Proof object simplifying inferences  : 13
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 7
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 14
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 14
% 0.14/0.38  # Processed clauses                    : 22
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 0
% 0.14/0.38  # ...remaining for further processing  : 22
% 0.14/0.38  # Other redundant clauses eliminated   : 0
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 2
% 0.14/0.38  # Backward-rewritten                   : 1
% 0.14/0.38  # Generated clauses                    : 15
% 0.14/0.38  # ...of the previous two non-trivial   : 12
% 0.14/0.38  # Contextual simplify-reflections      : 0
% 0.14/0.38  # Paramodulations                      : 15
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 0
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
% 0.14/0.38  # Current number of processed clauses  : 19
% 0.14/0.38  #    Positive orientable unit clauses  : 7
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 2
% 0.14/0.38  #    Non-unit-clauses                  : 10
% 0.14/0.38  # Current number of unprocessed clauses: 1
% 0.14/0.38  # ...number of literals in the above   : 9
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 3
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 25
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 3
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 1
% 0.14/0.38  # Unit Clause-clause subsumption calls : 5
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 2
% 0.14/0.38  # BW rewrite match successes           : 2
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 1211
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.029 s
% 0.14/0.38  # System time              : 0.002 s
% 0.14/0.38  # Total time               : 0.031 s
% 0.14/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
