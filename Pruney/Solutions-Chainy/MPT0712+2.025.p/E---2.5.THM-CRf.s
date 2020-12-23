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
% DateTime   : Thu Dec  3 10:55:40 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 127 expanded)
%              Number of clauses        :   28 (  51 expanded)
%              Number of leaves         :   10 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :  125 ( 296 expanded)
%              Number of equality atoms :   52 ( 122 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   25 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t167_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k2_relat_1(k7_relat_1(X2,k1_tarski(X1))),k1_tarski(k1_funct_1(X2,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_funct_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(d16_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(t117_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => k11_relat_1(X2,X1) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

fof(t142_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r1_tarski(X4,k1_enumset1(X1,X2,X3))
    <=> ~ ( X4 != k1_xboole_0
          & X4 != k1_tarski(X1)
          & X4 != k1_tarski(X2)
          & X4 != k1_tarski(X3)
          & X4 != k2_tarski(X1,X2)
          & X4 != k2_tarski(X2,X3)
          & X4 != k2_tarski(X1,X3)
          & X4 != k1_enumset1(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_zfmisc_1)).

fof(l27_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X1,X2)
     => r1_xboole_0(k1_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(t187_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_xboole_0(X2,k1_relat_1(X1))
         => k7_relat_1(X1,X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => r1_tarski(k2_relat_1(k7_relat_1(X2,k1_tarski(X1))),k1_tarski(k1_funct_1(X2,X1))) ) ),
    inference(assume_negation,[status(cth)],[t167_funct_1])).

fof(c_0_11,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & ~ r1_tarski(k2_relat_1(k7_relat_1(esk2_0,k1_tarski(esk1_0))),k1_tarski(k1_funct_1(esk2_0,esk1_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_12,plain,(
    ! [X5] : k2_tarski(X5,X5) = k1_tarski(X5) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_13,plain,(
    ! [X6,X7] : k1_enumset1(X6,X6,X7) = k2_tarski(X6,X7) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_14,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(esk2_0,k1_tarski(esk1_0))),k1_tarski(k1_funct_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X17)
      | k2_relat_1(k7_relat_1(X17,X16)) = k9_relat_1(X17,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_18,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X14)
      | k11_relat_1(X14,X15) = k9_relat_1(X14,k1_tarski(X15)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).

cnf(c_0_19,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(esk2_0,k1_enumset1(esk1_0,esk1_0,esk1_0))),k1_enumset1(k1_funct_1(esk2_0,esk1_0),k1_funct_1(esk2_0,esk1_0),k1_funct_1(esk2_0,esk1_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_15]),c_0_15]),c_0_16]),c_0_16])).

cnf(c_0_20,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X21)
      | ~ v1_funct_1(X21)
      | ~ r2_hidden(X20,k1_relat_1(X21))
      | k11_relat_1(X21,X20) = k1_tarski(k1_funct_1(X21,X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t117_funct_1])])).

fof(c_0_24,plain,(
    ! [X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X13,k1_enumset1(X10,X11,X12))
        | X13 = k1_xboole_0
        | X13 = k1_tarski(X10)
        | X13 = k1_tarski(X11)
        | X13 = k1_tarski(X12)
        | X13 = k2_tarski(X10,X11)
        | X13 = k2_tarski(X11,X12)
        | X13 = k2_tarski(X10,X12)
        | X13 = k1_enumset1(X10,X11,X12) )
      & ( X13 != k1_xboole_0
        | r1_tarski(X13,k1_enumset1(X10,X11,X12)) )
      & ( X13 != k1_tarski(X10)
        | r1_tarski(X13,k1_enumset1(X10,X11,X12)) )
      & ( X13 != k1_tarski(X11)
        | r1_tarski(X13,k1_enumset1(X10,X11,X12)) )
      & ( X13 != k1_tarski(X12)
        | r1_tarski(X13,k1_enumset1(X10,X11,X12)) )
      & ( X13 != k2_tarski(X10,X11)
        | r1_tarski(X13,k1_enumset1(X10,X11,X12)) )
      & ( X13 != k2_tarski(X11,X12)
        | r1_tarski(X13,k1_enumset1(X10,X11,X12)) )
      & ( X13 != k2_tarski(X10,X12)
        | r1_tarski(X13,k1_enumset1(X10,X11,X12)) )
      & ( X13 != k1_enumset1(X10,X11,X12)
        | r1_tarski(X13,k1_enumset1(X10,X11,X12)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t142_zfmisc_1])])])).

fof(c_0_25,plain,(
    ! [X8,X9] :
      ( r2_hidden(X8,X9)
      | r1_xboole_0(k1_tarski(X8),X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).

cnf(c_0_26,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk2_0,k1_enumset1(esk1_0,esk1_0,esk1_0)),k1_enumset1(k1_funct_1(esk2_0,esk1_0),k1_funct_1(esk2_0,esk1_0),k1_funct_1(esk2_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_27,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_enumset1(X2,X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_15]),c_0_16])).

cnf(c_0_28,plain,
    ( k11_relat_1(X1,X2) = k1_tarski(k1_funct_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,k1_enumset1(X2,X3,X4))
    | X1 != k1_enumset1(X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_30,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X18)
      | ~ r1_xboole_0(X19,k1_relat_1(X18))
      | k7_relat_1(X18,X19) = k1_xboole_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t187_relat_1])])])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( ~ r1_tarski(k11_relat_1(esk2_0,esk1_0),k1_enumset1(k1_funct_1(esk2_0,esk1_0),k1_funct_1(esk2_0,esk1_0),k1_funct_1(esk2_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_21])])).

cnf(c_0_33,plain,
    ( k11_relat_1(X1,X2) = k1_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_15]),c_0_16])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_35,plain,
    ( r1_tarski(k1_enumset1(X1,X2,X3),k1_enumset1(X1,X2,X3)) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( k7_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_enumset1(X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_15]),c_0_16])).

cnf(c_0_38,negated_conjecture,
    ( ~ r1_tarski(k11_relat_1(esk2_0,esk1_0),k11_relat_1(esk2_0,esk1_0))
    | ~ r2_hidden(esk1_0,k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_21])])).

cnf(c_0_39,plain,
    ( r1_tarski(k11_relat_1(X1,X2),k11_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_33])).

cnf(c_0_40,plain,
    ( k7_relat_1(X1,k1_enumset1(X2,X2,X2)) = k1_xboole_0
    | r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( ~ r2_hidden(esk1_0,k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_34]),c_0_21])])).

cnf(c_0_42,negated_conjecture,
    ( k7_relat_1(esk2_0,k1_enumset1(X1,X1,X1)) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_21])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,k1_enumset1(X2,X3,X4))
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_44,negated_conjecture,
    ( k7_relat_1(esk2_0,k1_enumset1(esk1_0,esk1_0,esk1_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_45,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_46,plain,
    ( r1_tarski(k1_xboole_0,k1_enumset1(X1,X2,X3)) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_44]),c_0_45]),c_0_46])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:20:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.37  #
% 0.14/0.37  # Preprocessing time       : 0.027 s
% 0.14/0.37  # Presaturation interreduction done
% 0.14/0.37  
% 0.14/0.37  # Proof found!
% 0.14/0.37  # SZS status Theorem
% 0.14/0.37  # SZS output start CNFRefutation
% 0.14/0.37  fof(t167_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k2_relat_1(k7_relat_1(X2,k1_tarski(X1))),k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_funct_1)).
% 0.14/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.14/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.14/0.37  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.14/0.37  fof(d16_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 0.14/0.37  fof(t117_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r2_hidden(X1,k1_relat_1(X2))=>k11_relat_1(X2,X1)=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_funct_1)).
% 0.14/0.37  fof(t142_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r1_tarski(X4,k1_enumset1(X1,X2,X3))<=>~((((((((X4!=k1_xboole_0&X4!=k1_tarski(X1))&X4!=k1_tarski(X2))&X4!=k1_tarski(X3))&X4!=k2_tarski(X1,X2))&X4!=k2_tarski(X2,X3))&X4!=k2_tarski(X1,X3))&X4!=k1_enumset1(X1,X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 0.14/0.37  fof(l27_zfmisc_1, axiom, ![X1, X2]:(~(r2_hidden(X1,X2))=>r1_xboole_0(k1_tarski(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 0.14/0.37  fof(t187_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_xboole_0(X2,k1_relat_1(X1))=>k7_relat_1(X1,X2)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 0.14/0.37  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.14/0.37  fof(c_0_10, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k2_relat_1(k7_relat_1(X2,k1_tarski(X1))),k1_tarski(k1_funct_1(X2,X1))))), inference(assume_negation,[status(cth)],[t167_funct_1])).
% 0.14/0.37  fof(c_0_11, negated_conjecture, ((v1_relat_1(esk2_0)&v1_funct_1(esk2_0))&~r1_tarski(k2_relat_1(k7_relat_1(esk2_0,k1_tarski(esk1_0))),k1_tarski(k1_funct_1(esk2_0,esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.14/0.37  fof(c_0_12, plain, ![X5]:k2_tarski(X5,X5)=k1_tarski(X5), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.14/0.37  fof(c_0_13, plain, ![X6, X7]:k1_enumset1(X6,X6,X7)=k2_tarski(X6,X7), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.14/0.37  cnf(c_0_14, negated_conjecture, (~r1_tarski(k2_relat_1(k7_relat_1(esk2_0,k1_tarski(esk1_0))),k1_tarski(k1_funct_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.37  cnf(c_0_15, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.37  cnf(c_0_16, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.37  fof(c_0_17, plain, ![X16, X17]:(~v1_relat_1(X17)|k2_relat_1(k7_relat_1(X17,X16))=k9_relat_1(X17,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.14/0.37  fof(c_0_18, plain, ![X14, X15]:(~v1_relat_1(X14)|k11_relat_1(X14,X15)=k9_relat_1(X14,k1_tarski(X15))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).
% 0.14/0.37  cnf(c_0_19, negated_conjecture, (~r1_tarski(k2_relat_1(k7_relat_1(esk2_0,k1_enumset1(esk1_0,esk1_0,esk1_0))),k1_enumset1(k1_funct_1(esk2_0,esk1_0),k1_funct_1(esk2_0,esk1_0),k1_funct_1(esk2_0,esk1_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14, c_0_15]), c_0_15]), c_0_16]), c_0_16])).
% 0.14/0.37  cnf(c_0_20, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.37  cnf(c_0_21, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.37  cnf(c_0_22, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.37  fof(c_0_23, plain, ![X20, X21]:(~v1_relat_1(X21)|~v1_funct_1(X21)|(~r2_hidden(X20,k1_relat_1(X21))|k11_relat_1(X21,X20)=k1_tarski(k1_funct_1(X21,X20)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t117_funct_1])])).
% 0.14/0.37  fof(c_0_24, plain, ![X10, X11, X12, X13]:((~r1_tarski(X13,k1_enumset1(X10,X11,X12))|(X13=k1_xboole_0|X13=k1_tarski(X10)|X13=k1_tarski(X11)|X13=k1_tarski(X12)|X13=k2_tarski(X10,X11)|X13=k2_tarski(X11,X12)|X13=k2_tarski(X10,X12)|X13=k1_enumset1(X10,X11,X12)))&((((((((X13!=k1_xboole_0|r1_tarski(X13,k1_enumset1(X10,X11,X12)))&(X13!=k1_tarski(X10)|r1_tarski(X13,k1_enumset1(X10,X11,X12))))&(X13!=k1_tarski(X11)|r1_tarski(X13,k1_enumset1(X10,X11,X12))))&(X13!=k1_tarski(X12)|r1_tarski(X13,k1_enumset1(X10,X11,X12))))&(X13!=k2_tarski(X10,X11)|r1_tarski(X13,k1_enumset1(X10,X11,X12))))&(X13!=k2_tarski(X11,X12)|r1_tarski(X13,k1_enumset1(X10,X11,X12))))&(X13!=k2_tarski(X10,X12)|r1_tarski(X13,k1_enumset1(X10,X11,X12))))&(X13!=k1_enumset1(X10,X11,X12)|r1_tarski(X13,k1_enumset1(X10,X11,X12))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t142_zfmisc_1])])])).
% 0.14/0.37  fof(c_0_25, plain, ![X8, X9]:(r2_hidden(X8,X9)|r1_xboole_0(k1_tarski(X8),X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).
% 0.14/0.37  cnf(c_0_26, negated_conjecture, (~r1_tarski(k9_relat_1(esk2_0,k1_enumset1(esk1_0,esk1_0,esk1_0)),k1_enumset1(k1_funct_1(esk2_0,esk1_0),k1_funct_1(esk2_0,esk1_0),k1_funct_1(esk2_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])])).
% 0.14/0.37  cnf(c_0_27, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k1_enumset1(X2,X2,X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_15]), c_0_16])).
% 0.14/0.37  cnf(c_0_28, plain, (k11_relat_1(X1,X2)=k1_tarski(k1_funct_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.37  cnf(c_0_29, plain, (r1_tarski(X1,k1_enumset1(X2,X3,X4))|X1!=k1_enumset1(X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.37  fof(c_0_30, plain, ![X18, X19]:(~v1_relat_1(X18)|(~r1_xboole_0(X19,k1_relat_1(X18))|k7_relat_1(X18,X19)=k1_xboole_0)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t187_relat_1])])])).
% 0.14/0.37  cnf(c_0_31, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.14/0.37  cnf(c_0_32, negated_conjecture, (~r1_tarski(k11_relat_1(esk2_0,esk1_0),k1_enumset1(k1_funct_1(esk2_0,esk1_0),k1_funct_1(esk2_0,esk1_0),k1_funct_1(esk2_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_21])])).
% 0.14/0.37  cnf(c_0_33, plain, (k11_relat_1(X1,X2)=k1_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_15]), c_0_16])).
% 0.14/0.37  cnf(c_0_34, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.37  cnf(c_0_35, plain, (r1_tarski(k1_enumset1(X1,X2,X3),k1_enumset1(X1,X2,X3))), inference(er,[status(thm)],[c_0_29])).
% 0.14/0.37  cnf(c_0_36, plain, (k7_relat_1(X1,X2)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.37  cnf(c_0_37, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_enumset1(X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_15]), c_0_16])).
% 0.14/0.37  cnf(c_0_38, negated_conjecture, (~r1_tarski(k11_relat_1(esk2_0,esk1_0),k11_relat_1(esk2_0,esk1_0))|~r2_hidden(esk1_0,k1_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_21])])).
% 0.14/0.37  cnf(c_0_39, plain, (r1_tarski(k11_relat_1(X1,X2),k11_relat_1(X1,X2))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_35, c_0_33])).
% 0.14/0.37  cnf(c_0_40, plain, (k7_relat_1(X1,k1_enumset1(X2,X2,X2))=k1_xboole_0|r2_hidden(X2,k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.14/0.37  cnf(c_0_41, negated_conjecture, (~r2_hidden(esk1_0,k1_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_34]), c_0_21])])).
% 0.14/0.37  cnf(c_0_42, negated_conjecture, (k7_relat_1(esk2_0,k1_enumset1(X1,X1,X1))=k1_xboole_0|r2_hidden(X1,k1_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_40, c_0_21])).
% 0.14/0.37  cnf(c_0_43, plain, (r1_tarski(X1,k1_enumset1(X2,X3,X4))|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.37  cnf(c_0_44, negated_conjecture, (k7_relat_1(esk2_0,k1_enumset1(esk1_0,esk1_0,esk1_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.14/0.37  cnf(c_0_45, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.14/0.37  cnf(c_0_46, plain, (r1_tarski(k1_xboole_0,k1_enumset1(X1,X2,X3))), inference(er,[status(thm)],[c_0_43])).
% 0.14/0.37  cnf(c_0_47, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_44]), c_0_45]), c_0_46])]), ['proof']).
% 0.14/0.37  # SZS output end CNFRefutation
% 0.14/0.37  # Proof object total steps             : 48
% 0.14/0.37  # Proof object clause steps            : 28
% 0.14/0.37  # Proof object formula steps           : 20
% 0.14/0.37  # Proof object conjectures             : 14
% 0.14/0.37  # Proof object clause conjectures      : 11
% 0.14/0.37  # Proof object formula conjectures     : 3
% 0.14/0.37  # Proof object initial clauses used    : 13
% 0.14/0.37  # Proof object initial formulas used   : 10
% 0.14/0.37  # Proof object generating inferences   : 8
% 0.14/0.37  # Proof object simplifying inferences  : 26
% 0.14/0.37  # Training examples: 0 positive, 0 negative
% 0.14/0.37  # Parsed axioms                        : 10
% 0.14/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.37  # Initial clauses                      : 21
% 0.14/0.37  # Removed in clause preprocessing      : 2
% 0.14/0.37  # Initial clauses in saturation        : 19
% 0.14/0.37  # Processed clauses                    : 66
% 0.14/0.37  # ...of these trivial                  : 0
% 0.14/0.37  # ...subsumed                          : 2
% 0.14/0.37  # ...remaining for further processing  : 64
% 0.14/0.37  # Other redundant clauses eliminated   : 8
% 0.14/0.37  # Clauses deleted for lack of memory   : 0
% 0.14/0.37  # Backward-subsumed                    : 0
% 0.14/0.37  # Backward-rewritten                   : 2
% 0.14/0.37  # Generated clauses                    : 49
% 0.14/0.37  # ...of the previous two non-trivial   : 48
% 0.14/0.37  # Contextual simplify-reflections      : 0
% 0.14/0.37  # Paramodulations                      : 41
% 0.14/0.37  # Factorizations                       : 0
% 0.14/0.37  # Equation resolutions                 : 8
% 0.14/0.37  # Propositional unsat checks           : 0
% 0.14/0.37  #    Propositional check models        : 0
% 0.14/0.37  #    Propositional check unsatisfiable : 0
% 0.14/0.37  #    Propositional clauses             : 0
% 0.14/0.37  #    Propositional clauses after purity: 0
% 0.14/0.37  #    Propositional unsat core size     : 0
% 0.14/0.37  #    Propositional preprocessing time  : 0.000
% 0.14/0.37  #    Propositional encoding time       : 0.000
% 0.14/0.37  #    Propositional solver time         : 0.000
% 0.14/0.37  #    Success case prop preproc time    : 0.000
% 0.14/0.37  #    Success case prop encoding time   : 0.000
% 0.14/0.37  #    Success case prop solver time     : 0.000
% 0.14/0.37  # Current number of processed clauses  : 35
% 0.14/0.37  #    Positive orientable unit clauses  : 14
% 0.14/0.37  #    Positive unorientable unit clauses: 0
% 0.14/0.37  #    Negative unit clauses             : 3
% 0.14/0.37  #    Non-unit-clauses                  : 18
% 0.14/0.37  # Current number of unprocessed clauses: 19
% 0.14/0.37  # ...number of literals in the above   : 82
% 0.14/0.37  # Current number of archived formulas  : 0
% 0.14/0.37  # Current number of archived clauses   : 23
% 0.14/0.37  # Clause-clause subsumption calls (NU) : 19
% 0.14/0.37  # Rec. Clause-clause subsumption calls : 14
% 0.14/0.37  # Non-unit clause-clause subsumptions  : 2
% 0.14/0.37  # Unit Clause-clause subsumption calls : 17
% 0.14/0.37  # Rewrite failures with RHS unbound    : 0
% 0.14/0.37  # BW rewrite match attempts            : 43
% 0.14/0.37  # BW rewrite match successes           : 1
% 0.14/0.37  # Condensation attempts                : 0
% 0.14/0.37  # Condensation successes               : 0
% 0.14/0.37  # Termbank termtop insertions          : 2124
% 0.14/0.37  
% 0.14/0.37  # -------------------------------------------------
% 0.14/0.37  # User time                : 0.030 s
% 0.14/0.37  # System time              : 0.003 s
% 0.14/0.37  # Total time               : 0.033 s
% 0.14/0.37  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
