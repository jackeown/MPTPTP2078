%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:16 EST 2020

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 110 expanded)
%              Number of clauses        :   27 (  47 expanded)
%              Number of leaves         :   13 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :  130 ( 266 expanded)
%              Number of equality atoms :   32 (  89 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t57_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X3,X2)
        & ~ r1_xboole_0(k2_tarski(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t187_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_xboole_0(X2,k1_relat_1(X1))
         => k7_relat_1(X1,X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

fof(d16_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(t205_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k1_relat_1(X2))
      <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(t55_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r1_xboole_0(k2_tarski(X1,X2),X3)
        & r2_hidden(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(t204_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> r2_hidden(X2,k11_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(t166_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(c_0_13,plain,(
    ! [X12,X13,X14] :
      ( r2_hidden(X12,X13)
      | r2_hidden(X14,X13)
      | r1_xboole_0(k2_tarski(X12,X14),X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_zfmisc_1])])])).

fof(c_0_14,plain,(
    ! [X7,X8] : k1_enumset1(X7,X7,X8) = k2_tarski(X7,X8) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_15,plain,(
    ! [X25,X26] :
      ( ~ v1_relat_1(X25)
      | ~ r1_xboole_0(X26,k1_relat_1(X25))
      | k7_relat_1(X25,X26) = k1_xboole_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t187_relat_1])])])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X3,X2)
    | r1_xboole_0(k2_tarski(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X15)
      | k11_relat_1(X15,X16) = k9_relat_1(X15,k1_tarski(X16)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).

fof(c_0_19,plain,(
    ! [X6] : k2_tarski(X6,X6) = k1_tarski(X6) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_20,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X18)
      | k2_relat_1(k7_relat_1(X18,X17)) = k9_relat_1(X18,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_21,plain,
    ( k7_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( r2_hidden(X3,X2)
    | r2_hidden(X1,X2)
    | r1_xboole_0(k1_enumset1(X1,X1,X3),X2) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X1,k1_relat_1(X2))
        <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t205_relat_1])).

cnf(c_0_24,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k7_relat_1(X1,k1_enumset1(X2,X2,X3)) = k1_xboole_0
    | r2_hidden(X2,k1_relat_1(X1))
    | r2_hidden(X3,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

fof(c_0_29,plain,(
    ! [X9,X10,X11] :
      ( ~ r1_xboole_0(k2_tarski(X9,X10),X11)
      | ~ r2_hidden(X9,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_zfmisc_1])])).

fof(c_0_30,plain,(
    ! [X27,X28,X29] :
      ( ( ~ r2_hidden(k4_tarski(X27,X28),X29)
        | r2_hidden(X28,k11_relat_1(X29,X27))
        | ~ v1_relat_1(X29) )
      & ( ~ r2_hidden(X28,k11_relat_1(X29,X27))
        | r2_hidden(k4_tarski(X27,X28),X29)
        | ~ v1_relat_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).

fof(c_0_31,plain,(
    ! [X19,X20,X21,X23] :
      ( ( r2_hidden(esk1_3(X19,X20,X21),k2_relat_1(X21))
        | ~ r2_hidden(X19,k10_relat_1(X21,X20))
        | ~ v1_relat_1(X21) )
      & ( r2_hidden(k4_tarski(X19,esk1_3(X19,X20,X21)),X21)
        | ~ r2_hidden(X19,k10_relat_1(X21,X20))
        | ~ v1_relat_1(X21) )
      & ( r2_hidden(esk1_3(X19,X20,X21),X20)
        | ~ r2_hidden(X19,k10_relat_1(X21,X20))
        | ~ v1_relat_1(X21) )
      & ( ~ r2_hidden(X23,k2_relat_1(X21))
        | ~ r2_hidden(k4_tarski(X19,X23),X21)
        | ~ r2_hidden(X23,X20)
        | r2_hidden(X19,k10_relat_1(X21,X20))
        | ~ v1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

fof(c_0_32,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & ( ~ r2_hidden(esk2_0,k1_relat_1(esk3_0))
      | k11_relat_1(esk3_0,esk2_0) = k1_xboole_0 )
    & ( r2_hidden(esk2_0,k1_relat_1(esk3_0))
      | k11_relat_1(esk3_0,esk2_0) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

cnf(c_0_33,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_enumset1(X2,X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_17])).

cnf(c_0_34,plain,
    ( k9_relat_1(X1,k1_enumset1(X2,X2,X3)) = k1_xboole_0
    | r2_hidden(X3,k1_relat_1(X1))
    | r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_35,plain,
    ( ~ r1_xboole_0(k2_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_36,plain,(
    ! [X5] : r1_xboole_0(X5,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_37,plain,
    ( r2_hidden(X2,k11_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( r2_hidden(k4_tarski(X1,esk1_3(X1,X2,X3)),X3)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( k11_relat_1(esk3_0,esk2_0) = k1_xboole_0
    | ~ r2_hidden(esk2_0,k1_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( k11_relat_1(X1,X2) = k1_xboole_0
    | r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(k1_enumset1(X1,X1,X2),X3) ),
    inference(rw,[status(thm)],[c_0_35,c_0_17])).

cnf(c_0_43,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),k11_relat_1(X3,X1))
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( k11_relat_1(esk3_0,esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])])).

cnf(c_0_46,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

fof(c_0_47,plain,(
    ! [X24] :
      ( ~ v1_relat_1(X24)
      | k10_relat_1(X24,k2_relat_1(X24)) = k1_relat_1(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk2_0,k1_relat_1(esk3_0))
    | k11_relat_1(esk3_0,esk2_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_49,negated_conjecture,
    ( ~ r2_hidden(esk2_0,k10_relat_1(esk3_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_41])]),c_0_46])).

cnf(c_0_50,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk2_0,k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_45])])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_41])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.33  % Computer   : n008.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 14:23:00 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.34  # No SInE strategy applied
% 0.11/0.34  # Trying AutoSched0 for 299 seconds
% 0.11/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S060N
% 0.11/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.11/0.37  #
% 0.11/0.37  # Preprocessing time       : 0.027 s
% 0.11/0.37  # Presaturation interreduction done
% 0.11/0.37  
% 0.11/0.37  # Proof found!
% 0.11/0.37  # SZS status Theorem
% 0.11/0.37  # SZS output start CNFRefutation
% 0.11/0.37  fof(t57_zfmisc_1, axiom, ![X1, X2, X3]:~(((~(r2_hidden(X1,X2))&~(r2_hidden(X3,X2)))&~(r1_xboole_0(k2_tarski(X1,X3),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 0.11/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.11/0.37  fof(t187_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_xboole_0(X2,k1_relat_1(X1))=>k7_relat_1(X1,X2)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 0.11/0.37  fof(d16_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 0.11/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.11/0.37  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.11/0.37  fof(t205_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 0.11/0.37  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.11/0.37  fof(t55_zfmisc_1, axiom, ![X1, X2, X3]:~((r1_xboole_0(k2_tarski(X1,X2),X3)&r2_hidden(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 0.11/0.37  fof(t204_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r2_hidden(X2,k11_relat_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 0.11/0.37  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 0.11/0.37  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.11/0.37  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 0.11/0.37  fof(c_0_13, plain, ![X12, X13, X14]:(r2_hidden(X12,X13)|r2_hidden(X14,X13)|r1_xboole_0(k2_tarski(X12,X14),X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_zfmisc_1])])])).
% 0.11/0.37  fof(c_0_14, plain, ![X7, X8]:k1_enumset1(X7,X7,X8)=k2_tarski(X7,X8), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.11/0.37  fof(c_0_15, plain, ![X25, X26]:(~v1_relat_1(X25)|(~r1_xboole_0(X26,k1_relat_1(X25))|k7_relat_1(X25,X26)=k1_xboole_0)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t187_relat_1])])])).
% 0.11/0.37  cnf(c_0_16, plain, (r2_hidden(X1,X2)|r2_hidden(X3,X2)|r1_xboole_0(k2_tarski(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.11/0.37  cnf(c_0_17, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.11/0.37  fof(c_0_18, plain, ![X15, X16]:(~v1_relat_1(X15)|k11_relat_1(X15,X16)=k9_relat_1(X15,k1_tarski(X16))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).
% 0.11/0.37  fof(c_0_19, plain, ![X6]:k2_tarski(X6,X6)=k1_tarski(X6), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.11/0.37  fof(c_0_20, plain, ![X17, X18]:(~v1_relat_1(X18)|k2_relat_1(k7_relat_1(X18,X17))=k9_relat_1(X18,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.11/0.37  cnf(c_0_21, plain, (k7_relat_1(X1,X2)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.11/0.37  cnf(c_0_22, plain, (r2_hidden(X3,X2)|r2_hidden(X1,X2)|r1_xboole_0(k1_enumset1(X1,X1,X3),X2)), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.11/0.37  fof(c_0_23, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t205_relat_1])).
% 0.11/0.37  cnf(c_0_24, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.11/0.37  cnf(c_0_25, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.11/0.37  cnf(c_0_26, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.11/0.37  cnf(c_0_27, plain, (k7_relat_1(X1,k1_enumset1(X2,X2,X3))=k1_xboole_0|r2_hidden(X2,k1_relat_1(X1))|r2_hidden(X3,k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.11/0.37  cnf(c_0_28, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.11/0.37  fof(c_0_29, plain, ![X9, X10, X11]:(~r1_xboole_0(k2_tarski(X9,X10),X11)|~r2_hidden(X9,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_zfmisc_1])])).
% 0.11/0.37  fof(c_0_30, plain, ![X27, X28, X29]:((~r2_hidden(k4_tarski(X27,X28),X29)|r2_hidden(X28,k11_relat_1(X29,X27))|~v1_relat_1(X29))&(~r2_hidden(X28,k11_relat_1(X29,X27))|r2_hidden(k4_tarski(X27,X28),X29)|~v1_relat_1(X29))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).
% 0.11/0.37  fof(c_0_31, plain, ![X19, X20, X21, X23]:((((r2_hidden(esk1_3(X19,X20,X21),k2_relat_1(X21))|~r2_hidden(X19,k10_relat_1(X21,X20))|~v1_relat_1(X21))&(r2_hidden(k4_tarski(X19,esk1_3(X19,X20,X21)),X21)|~r2_hidden(X19,k10_relat_1(X21,X20))|~v1_relat_1(X21)))&(r2_hidden(esk1_3(X19,X20,X21),X20)|~r2_hidden(X19,k10_relat_1(X21,X20))|~v1_relat_1(X21)))&(~r2_hidden(X23,k2_relat_1(X21))|~r2_hidden(k4_tarski(X19,X23),X21)|~r2_hidden(X23,X20)|r2_hidden(X19,k10_relat_1(X21,X20))|~v1_relat_1(X21))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.11/0.37  fof(c_0_32, negated_conjecture, (v1_relat_1(esk3_0)&((~r2_hidden(esk2_0,k1_relat_1(esk3_0))|k11_relat_1(esk3_0,esk2_0)=k1_xboole_0)&(r2_hidden(esk2_0,k1_relat_1(esk3_0))|k11_relat_1(esk3_0,esk2_0)!=k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 0.11/0.37  cnf(c_0_33, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k1_enumset1(X2,X2,X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_17])).
% 0.11/0.37  cnf(c_0_34, plain, (k9_relat_1(X1,k1_enumset1(X2,X2,X3))=k1_xboole_0|r2_hidden(X3,k1_relat_1(X1))|r2_hidden(X2,k1_relat_1(X1))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 0.11/0.37  cnf(c_0_35, plain, (~r1_xboole_0(k2_tarski(X1,X2),X3)|~r2_hidden(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.11/0.37  fof(c_0_36, plain, ![X5]:r1_xboole_0(X5,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.11/0.37  cnf(c_0_37, plain, (r2_hidden(X2,k11_relat_1(X3,X1))|~r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.11/0.37  cnf(c_0_38, plain, (r2_hidden(k4_tarski(X1,esk1_3(X1,X2,X3)),X3)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.11/0.37  cnf(c_0_39, negated_conjecture, (k11_relat_1(esk3_0,esk2_0)=k1_xboole_0|~r2_hidden(esk2_0,k1_relat_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.11/0.37  cnf(c_0_40, plain, (k11_relat_1(X1,X2)=k1_xboole_0|r2_hidden(X2,k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.11/0.37  cnf(c_0_41, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.11/0.37  cnf(c_0_42, plain, (~r2_hidden(X1,X3)|~r1_xboole_0(k1_enumset1(X1,X1,X2),X3)), inference(rw,[status(thm)],[c_0_35, c_0_17])).
% 0.11/0.37  cnf(c_0_43, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.11/0.37  cnf(c_0_44, plain, (r2_hidden(esk1_3(X1,X2,X3),k11_relat_1(X3,X1))|~v1_relat_1(X3)|~r2_hidden(X1,k10_relat_1(X3,X2))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.11/0.37  cnf(c_0_45, negated_conjecture, (k11_relat_1(esk3_0,esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])])).
% 0.11/0.37  cnf(c_0_46, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.11/0.37  fof(c_0_47, plain, ![X24]:(~v1_relat_1(X24)|k10_relat_1(X24,k2_relat_1(X24))=k1_relat_1(X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.11/0.37  cnf(c_0_48, negated_conjecture, (r2_hidden(esk2_0,k1_relat_1(esk3_0))|k11_relat_1(esk3_0,esk2_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.11/0.37  cnf(c_0_49, negated_conjecture, (~r2_hidden(esk2_0,k10_relat_1(esk3_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_41])]), c_0_46])).
% 0.11/0.37  cnf(c_0_50, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.11/0.37  cnf(c_0_51, negated_conjecture, (r2_hidden(esk2_0,k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_45])])).
% 0.11/0.37  cnf(c_0_52, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51]), c_0_41])]), ['proof']).
% 0.11/0.37  # SZS output end CNFRefutation
% 0.11/0.37  # Proof object total steps             : 53
% 0.11/0.37  # Proof object clause steps            : 27
% 0.11/0.37  # Proof object formula steps           : 26
% 0.11/0.37  # Proof object conjectures             : 10
% 0.11/0.37  # Proof object clause conjectures      : 7
% 0.11/0.37  # Proof object formula conjectures     : 3
% 0.11/0.37  # Proof object initial clauses used    : 15
% 0.11/0.37  # Proof object initial formulas used   : 13
% 0.11/0.37  # Proof object generating inferences   : 8
% 0.11/0.37  # Proof object simplifying inferences  : 15
% 0.11/0.37  # Training examples: 0 positive, 0 negative
% 0.11/0.37  # Parsed axioms                        : 13
% 0.11/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.11/0.37  # Initial clauses                      : 20
% 0.11/0.37  # Removed in clause preprocessing      : 2
% 0.11/0.37  # Initial clauses in saturation        : 18
% 0.11/0.37  # Processed clauses                    : 129
% 0.11/0.37  # ...of these trivial                  : 0
% 0.11/0.37  # ...subsumed                          : 51
% 0.11/0.37  # ...remaining for further processing  : 78
% 0.11/0.37  # Other redundant clauses eliminated   : 0
% 0.11/0.37  # Clauses deleted for lack of memory   : 0
% 0.11/0.37  # Backward-subsumed                    : 0
% 0.11/0.37  # Backward-rewritten                   : 2
% 0.11/0.37  # Generated clauses                    : 181
% 0.11/0.37  # ...of the previous two non-trivial   : 178
% 0.11/0.37  # Contextual simplify-reflections      : 0
% 0.11/0.37  # Paramodulations                      : 181
% 0.11/0.37  # Factorizations                       : 0
% 0.11/0.37  # Equation resolutions                 : 0
% 0.11/0.37  # Propositional unsat checks           : 0
% 0.11/0.37  #    Propositional check models        : 0
% 0.11/0.37  #    Propositional check unsatisfiable : 0
% 0.11/0.37  #    Propositional clauses             : 0
% 0.11/0.37  #    Propositional clauses after purity: 0
% 0.11/0.37  #    Propositional unsat core size     : 0
% 0.11/0.37  #    Propositional preprocessing time  : 0.000
% 0.11/0.37  #    Propositional encoding time       : 0.000
% 0.11/0.37  #    Propositional solver time         : 0.000
% 0.11/0.37  #    Success case prop preproc time    : 0.000
% 0.11/0.37  #    Success case prop encoding time   : 0.000
% 0.11/0.37  #    Success case prop solver time     : 0.000
% 0.11/0.37  # Current number of processed clauses  : 58
% 0.11/0.37  #    Positive orientable unit clauses  : 6
% 0.11/0.37  #    Positive unorientable unit clauses: 0
% 0.11/0.37  #    Negative unit clauses             : 2
% 0.11/0.37  #    Non-unit-clauses                  : 50
% 0.11/0.37  # Current number of unprocessed clauses: 85
% 0.11/0.37  # ...number of literals in the above   : 387
% 0.11/0.37  # Current number of archived formulas  : 0
% 0.11/0.37  # Current number of archived clauses   : 22
% 0.11/0.37  # Clause-clause subsumption calls (NU) : 835
% 0.11/0.37  # Rec. Clause-clause subsumption calls : 158
% 0.11/0.37  # Non-unit clause-clause subsumptions  : 36
% 0.11/0.37  # Unit Clause-clause subsumption calls : 24
% 0.11/0.37  # Rewrite failures with RHS unbound    : 0
% 0.11/0.37  # BW rewrite match attempts            : 1
% 0.11/0.37  # BW rewrite match successes           : 1
% 0.11/0.37  # Condensation attempts                : 0
% 0.11/0.37  # Condensation successes               : 0
% 0.11/0.37  # Termbank termtop insertions          : 4845
% 0.11/0.37  
% 0.11/0.37  # -------------------------------------------------
% 0.11/0.37  # User time                : 0.035 s
% 0.11/0.37  # System time              : 0.002 s
% 0.11/0.37  # Total time               : 0.038 s
% 0.11/0.37  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
