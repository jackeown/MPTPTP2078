%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:52 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   36 (  51 expanded)
%              Number of clauses        :   19 (  23 expanded)
%              Number of leaves         :    9 (  15 expanded)
%              Depth                    :    7
%              Number of atoms          :   92 ( 123 expanded)
%              Number of equality atoms :   15 (  17 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal clause size      :   19 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t142_funct_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k2_relat_1(X2))
      <=> k10_relat_1(X2,k1_tarski(X1)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t172_relat_1,axiom,(
    ! [X1] : k10_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

fof(cc1_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(cc1_funct_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_funct_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t174_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => v5_funct_1(k1_xboole_0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_1)).

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

fof(c_0_9,plain,(
    ! [X12,X13] :
      ( ( ~ r2_hidden(X12,k2_relat_1(X13))
        | k10_relat_1(X13,k1_tarski(X12)) != k1_xboole_0
        | ~ v1_relat_1(X13) )
      & ( k10_relat_1(X13,k1_tarski(X12)) = k1_xboole_0
        | r2_hidden(X12,k2_relat_1(X13))
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t142_funct_1])])])).

fof(c_0_10,plain,(
    ! [X4] : k2_tarski(X4,X4) = k1_tarski(X4) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_11,plain,
    ( ~ r2_hidden(X1,k2_relat_1(X2))
    | k10_relat_1(X2,k1_tarski(X1)) != k1_xboole_0
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_13,plain,(
    ! [X6] : k10_relat_1(k1_xboole_0,X6) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t172_relat_1])).

fof(c_0_14,plain,(
    ! [X5] :
      ( ~ v1_xboole_0(X5)
      | v1_relat_1(X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).

fof(c_0_15,plain,(
    ! [X7] :
      ( ~ v1_xboole_0(X7)
      | v1_funct_1(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_1])])).

cnf(c_0_16,plain,
    ( k10_relat_1(X2,k2_tarski(X1,X1)) != k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k2_relat_1(X2)) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_18,plain,
    ( k10_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => v5_funct_1(k1_xboole_0,X1) ) ),
    inference(assume_negation,[status(cth)],[t174_funct_1])).

fof(c_0_22,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v5_funct_1(X9,X8)
        | ~ r2_hidden(X10,k1_relat_1(X9))
        | r2_hidden(k1_funct_1(X9,X10),k1_funct_1(X8,X10))
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( r2_hidden(esk1_2(X8,X9),k1_relat_1(X9))
        | v5_funct_1(X9,X8)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( ~ r2_hidden(k1_funct_1(X9,esk1_2(X8,X9)),k1_funct_1(X8,esk1_2(X8,X9)))
        | v5_funct_1(X9,X8)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_funct_1])])])])])).

cnf(c_0_23,plain,
    ( v1_funct_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])])).

cnf(c_0_25,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_26,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & ~ v5_funct_1(k1_xboole_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

cnf(c_0_27,plain,
    ( r2_hidden(esk1_2(X1,X2),k1_relat_1(X2))
    | v5_funct_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_29,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_20])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25])])).

cnf(c_0_31,negated_conjecture,
    ( ~ v5_funct_1(k1_xboole_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( v5_funct_1(k1_xboole_0,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_25])]),c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:57:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___107_C41_F1_PI_AE_Q4_CS_SP_PS_S2U
% 0.19/0.38  # and selection function SelectNewComplexAHPExceptRRHorn.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.027 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t142_funct_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k2_relat_1(X2))<=>k10_relat_1(X2,k1_tarski(X1))!=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_1)).
% 0.19/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.38  fof(t172_relat_1, axiom, ![X1]:k10_relat_1(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 0.19/0.38  fof(cc1_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 0.19/0.38  fof(cc1_funct_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_funct_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 0.19/0.38  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.19/0.38  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.38  fof(t174_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>v5_funct_1(k1_xboole_0,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_funct_1)).
% 0.19/0.38  fof(d20_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v5_funct_1(X2,X1)<=>![X3]:(r2_hidden(X3,k1_relat_1(X2))=>r2_hidden(k1_funct_1(X2,X3),k1_funct_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_funct_1)).
% 0.19/0.38  fof(c_0_9, plain, ![X12, X13]:((~r2_hidden(X12,k2_relat_1(X13))|k10_relat_1(X13,k1_tarski(X12))!=k1_xboole_0|~v1_relat_1(X13))&(k10_relat_1(X13,k1_tarski(X12))=k1_xboole_0|r2_hidden(X12,k2_relat_1(X13))|~v1_relat_1(X13))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t142_funct_1])])])).
% 0.19/0.38  fof(c_0_10, plain, ![X4]:k2_tarski(X4,X4)=k1_tarski(X4), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.38  cnf(c_0_11, plain, (~r2_hidden(X1,k2_relat_1(X2))|k10_relat_1(X2,k1_tarski(X1))!=k1_xboole_0|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.38  cnf(c_0_12, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  fof(c_0_13, plain, ![X6]:k10_relat_1(k1_xboole_0,X6)=k1_xboole_0, inference(variable_rename,[status(thm)],[t172_relat_1])).
% 0.19/0.38  fof(c_0_14, plain, ![X5]:(~v1_xboole_0(X5)|v1_relat_1(X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).
% 0.19/0.38  fof(c_0_15, plain, ![X7]:(~v1_xboole_0(X7)|v1_funct_1(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_1])])).
% 0.19/0.38  cnf(c_0_16, plain, (k10_relat_1(X2,k2_tarski(X1,X1))!=k1_xboole_0|~v1_relat_1(X2)|~r2_hidden(X1,k2_relat_1(X2))), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 0.19/0.38  cnf(c_0_17, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.19/0.38  cnf(c_0_18, plain, (k10_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_19, plain, (v1_relat_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_20, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.38  fof(c_0_21, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>v5_funct_1(k1_xboole_0,X1))), inference(assume_negation,[status(cth)],[t174_funct_1])).
% 0.19/0.38  fof(c_0_22, plain, ![X8, X9, X10]:((~v5_funct_1(X9,X8)|(~r2_hidden(X10,k1_relat_1(X9))|r2_hidden(k1_funct_1(X9,X10),k1_funct_1(X8,X10)))|(~v1_relat_1(X9)|~v1_funct_1(X9))|(~v1_relat_1(X8)|~v1_funct_1(X8)))&((r2_hidden(esk1_2(X8,X9),k1_relat_1(X9))|v5_funct_1(X9,X8)|(~v1_relat_1(X9)|~v1_funct_1(X9))|(~v1_relat_1(X8)|~v1_funct_1(X8)))&(~r2_hidden(k1_funct_1(X9,esk1_2(X8,X9)),k1_funct_1(X8,esk1_2(X8,X9)))|v5_funct_1(X9,X8)|(~v1_relat_1(X9)|~v1_funct_1(X9))|(~v1_relat_1(X8)|~v1_funct_1(X8))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_funct_1])])])])])).
% 0.19/0.38  cnf(c_0_23, plain, (v1_funct_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_24, plain, (~r2_hidden(X1,k1_xboole_0)|~v1_relat_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])])).
% 0.19/0.38  cnf(c_0_25, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.38  fof(c_0_26, negated_conjecture, ((v1_relat_1(esk2_0)&v1_funct_1(esk2_0))&~v5_funct_1(k1_xboole_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.19/0.38  cnf(c_0_27, plain, (r2_hidden(esk1_2(X1,X2),k1_relat_1(X2))|v5_funct_1(X2,X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.38  cnf(c_0_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.19/0.38  cnf(c_0_29, plain, (v1_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_23, c_0_20])).
% 0.19/0.38  cnf(c_0_30, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25])])).
% 0.19/0.38  cnf(c_0_31, negated_conjecture, (~v5_funct_1(k1_xboole_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.38  cnf(c_0_32, plain, (v5_funct_1(k1_xboole_0,X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_25])]), c_0_30])).
% 0.19/0.38  cnf(c_0_33, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.38  cnf(c_0_34, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.38  cnf(c_0_35, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34])]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 36
% 0.19/0.38  # Proof object clause steps            : 19
% 0.19/0.38  # Proof object formula steps           : 17
% 0.19/0.38  # Proof object conjectures             : 7
% 0.19/0.38  # Proof object clause conjectures      : 4
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 12
% 0.19/0.38  # Proof object initial formulas used   : 9
% 0.19/0.38  # Proof object generating inferences   : 5
% 0.19/0.38  # Proof object simplifying inferences  : 12
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 9
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 15
% 0.19/0.38  # Removed in clause preprocessing      : 1
% 0.19/0.38  # Initial clauses in saturation        : 14
% 0.19/0.38  # Processed clauses                    : 33
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 0
% 0.19/0.38  # ...remaining for further processing  : 33
% 0.19/0.38  # Other redundant clauses eliminated   : 0
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 1
% 0.19/0.38  # Generated clauses                    : 6
% 0.19/0.38  # ...of the previous two non-trivial   : 5
% 0.19/0.38  # Contextual simplify-reflections      : 0
% 0.19/0.38  # Paramodulations                      : 6
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 0
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 18
% 0.19/0.38  #    Positive orientable unit clauses  : 8
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 2
% 0.19/0.38  #    Non-unit-clauses                  : 8
% 0.19/0.38  # Current number of unprocessed clauses: 0
% 0.19/0.38  # ...number of literals in the above   : 0
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 16
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 56
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 0
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.38  # Unit Clause-clause subsumption calls : 3
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 1
% 0.19/0.38  # BW rewrite match successes           : 1
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 1109
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.028 s
% 0.19/0.38  # System time              : 0.003 s
% 0.19/0.38  # Total time               : 0.031 s
% 0.19/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
