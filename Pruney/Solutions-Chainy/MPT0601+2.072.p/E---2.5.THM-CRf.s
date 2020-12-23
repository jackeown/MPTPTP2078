%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:22 EST 2020

% Result     : Theorem 0.22s
% Output     : CNFRefutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 117 expanded)
%              Number of clauses        :   29 (  49 expanded)
%              Number of leaves         :   12 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  124 ( 293 expanded)
%              Number of equality atoms :   39 (  97 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t204_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> r2_hidden(X2,k11_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t205_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k1_relat_1(X2))
      <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t20_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(X2,k2_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(t166_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(c_0_12,plain,(
    ! [X16,X17] : k1_setfam_1(k2_tarski(X16,X17)) = k3_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_13,plain,(
    ! [X11,X12] : k1_enumset1(X11,X11,X12) = k2_tarski(X11,X12) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_14,plain,(
    ! [X24,X25,X26] :
      ( ( ~ r2_hidden(k4_tarski(X24,X25),X26)
        | r2_hidden(X25,k11_relat_1(X26,X24))
        | ~ v1_relat_1(X26) )
      & ( ~ r2_hidden(X25,k11_relat_1(X26,X24))
        | r2_hidden(k4_tarski(X24,X25),X26)
        | ~ v1_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).

fof(c_0_15,plain,(
    ! [X5] :
      ( X5 = k1_xboole_0
      | r2_hidden(esk1_1(X5),X5) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X1,k1_relat_1(X2))
        <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t205_relat_1])).

fof(c_0_17,plain,(
    ! [X7,X8] : k4_xboole_0(X7,X8) = k5_xboole_0(X7,k3_xboole_0(X7,X8)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_18,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,k11_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & ( ~ r2_hidden(esk3_0,k1_relat_1(esk4_0))
      | k11_relat_1(esk4_0,esk3_0) = k1_xboole_0 )
    & ( r2_hidden(esk3_0,k1_relat_1(esk4_0))
      | k11_relat_1(esk4_0,esk3_0) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_23,plain,(
    ! [X13,X14,X15] :
      ( ( r2_hidden(X13,X14)
        | ~ r2_hidden(X13,k4_xboole_0(X14,k1_tarski(X15))) )
      & ( X13 != X15
        | ~ r2_hidden(X13,k4_xboole_0(X14,k1_tarski(X15))) )
      & ( ~ r2_hidden(X13,X14)
        | X13 = X15
        | r2_hidden(X13,k4_xboole_0(X14,k1_tarski(X15))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

fof(c_0_24,plain,(
    ! [X10] : k2_tarski(X10,X10) = k1_tarski(X10) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_27,plain,(
    ! [X27,X28,X29] :
      ( ( r2_hidden(X27,k1_relat_1(X29))
        | ~ r2_hidden(k4_tarski(X27,X28),X29)
        | ~ v1_relat_1(X29) )
      & ( r2_hidden(X28,k2_relat_1(X29))
        | ~ r2_hidden(k4_tarski(X27,X28),X29)
        | ~ v1_relat_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).

cnf(c_0_28,plain,
    ( k11_relat_1(X1,X2) = k1_xboole_0
    | r2_hidden(k4_tarski(X2,esk1_1(k11_relat_1(X1,X2))),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_33,plain,(
    ! [X9] : k4_xboole_0(k1_xboole_0,X9) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( k11_relat_1(esk4_0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(X1,esk1_1(k11_relat_1(esk4_0,X1))),esk4_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k5_xboole_0(X3,k1_setfam_1(k1_enumset1(X3,X3,k1_enumset1(X2,X2,X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31]),c_0_19]),c_0_32])).

cnf(c_0_37,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( k11_relat_1(esk4_0,esk3_0) = k1_xboole_0
    | ~ r2_hidden(esk3_0,k1_relat_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_39,negated_conjecture,
    ( k11_relat_1(esk4_0,X1) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_29])])).

cnf(c_0_40,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k1_enumset1(X2,X2,k1_enumset1(X1,X1,X1))))) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_41,plain,
    ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_37,c_0_32])).

cnf(c_0_42,plain,
    ( r2_hidden(X2,k11_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_43,negated_conjecture,
    ( k11_relat_1(esk4_0,esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

fof(c_0_45,plain,(
    ! [X18,X19,X20,X22] :
      ( ( r2_hidden(esk2_3(X18,X19,X20),k2_relat_1(X20))
        | ~ r2_hidden(X18,k10_relat_1(X20,X19))
        | ~ v1_relat_1(X20) )
      & ( r2_hidden(k4_tarski(X18,esk2_3(X18,X19,X20)),X20)
        | ~ r2_hidden(X18,k10_relat_1(X20,X19))
        | ~ v1_relat_1(X20) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X19)
        | ~ r2_hidden(X18,k10_relat_1(X20,X19))
        | ~ v1_relat_1(X20) )
      & ( ~ r2_hidden(X22,k2_relat_1(X20))
        | ~ r2_hidden(k4_tarski(X18,X22),X20)
        | ~ r2_hidden(X22,X19)
        | r2_hidden(X18,k10_relat_1(X20,X19))
        | ~ v1_relat_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

cnf(c_0_46,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk3_0,X1),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_29])]),c_0_44])).

cnf(c_0_47,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X1,X2,X3)),X3)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_48,plain,(
    ! [X23] :
      ( ~ v1_relat_1(X23)
      | k10_relat_1(X23,k2_relat_1(X23)) = k1_relat_1(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk3_0,k1_relat_1(esk4_0))
    | k11_relat_1(esk4_0,esk3_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_50,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k10_relat_1(esk4_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_29])])).

cnf(c_0_51,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk3_0,k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_43])])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_29])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 15:40:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  # Version: 2.5pre002
% 0.14/0.36  # No SInE strategy applied
% 0.14/0.36  # Trying AutoSched0 for 299 seconds
% 0.22/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.22/0.41  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.22/0.41  #
% 0.22/0.41  # Preprocessing time       : 0.030 s
% 0.22/0.41  # Presaturation interreduction done
% 0.22/0.41  
% 0.22/0.41  # Proof found!
% 0.22/0.41  # SZS status Theorem
% 0.22/0.41  # SZS output start CNFRefutation
% 0.22/0.41  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.22/0.41  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.22/0.41  fof(t204_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r2_hidden(X2,k11_relat_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 0.22/0.41  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.22/0.41  fof(t205_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 0.22/0.41  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.22/0.41  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 0.22/0.41  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.22/0.41  fof(t20_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(X2,k2_relat_1(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 0.22/0.41  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 0.22/0.41  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 0.22/0.41  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 0.22/0.41  fof(c_0_12, plain, ![X16, X17]:k1_setfam_1(k2_tarski(X16,X17))=k3_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.22/0.41  fof(c_0_13, plain, ![X11, X12]:k1_enumset1(X11,X11,X12)=k2_tarski(X11,X12), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.22/0.41  fof(c_0_14, plain, ![X24, X25, X26]:((~r2_hidden(k4_tarski(X24,X25),X26)|r2_hidden(X25,k11_relat_1(X26,X24))|~v1_relat_1(X26))&(~r2_hidden(X25,k11_relat_1(X26,X24))|r2_hidden(k4_tarski(X24,X25),X26)|~v1_relat_1(X26))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).
% 0.22/0.41  fof(c_0_15, plain, ![X5]:(X5=k1_xboole_0|r2_hidden(esk1_1(X5),X5)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.22/0.41  fof(c_0_16, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t205_relat_1])).
% 0.22/0.41  fof(c_0_17, plain, ![X7, X8]:k4_xboole_0(X7,X8)=k5_xboole_0(X7,k3_xboole_0(X7,X8)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.22/0.41  cnf(c_0_18, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.22/0.41  cnf(c_0_19, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.22/0.41  cnf(c_0_20, plain, (r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,k11_relat_1(X2,X3))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.22/0.41  cnf(c_0_21, plain, (X1=k1_xboole_0|r2_hidden(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.22/0.41  fof(c_0_22, negated_conjecture, (v1_relat_1(esk4_0)&((~r2_hidden(esk3_0,k1_relat_1(esk4_0))|k11_relat_1(esk4_0,esk3_0)=k1_xboole_0)&(r2_hidden(esk3_0,k1_relat_1(esk4_0))|k11_relat_1(esk4_0,esk3_0)!=k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.22/0.41  fof(c_0_23, plain, ![X13, X14, X15]:(((r2_hidden(X13,X14)|~r2_hidden(X13,k4_xboole_0(X14,k1_tarski(X15))))&(X13!=X15|~r2_hidden(X13,k4_xboole_0(X14,k1_tarski(X15)))))&(~r2_hidden(X13,X14)|X13=X15|r2_hidden(X13,k4_xboole_0(X14,k1_tarski(X15))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 0.22/0.41  fof(c_0_24, plain, ![X10]:k2_tarski(X10,X10)=k1_tarski(X10), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.22/0.41  cnf(c_0_25, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.22/0.41  cnf(c_0_26, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.22/0.41  fof(c_0_27, plain, ![X27, X28, X29]:((r2_hidden(X27,k1_relat_1(X29))|~r2_hidden(k4_tarski(X27,X28),X29)|~v1_relat_1(X29))&(r2_hidden(X28,k2_relat_1(X29))|~r2_hidden(k4_tarski(X27,X28),X29)|~v1_relat_1(X29))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).
% 0.22/0.41  cnf(c_0_28, plain, (k11_relat_1(X1,X2)=k1_xboole_0|r2_hidden(k4_tarski(X2,esk1_1(k11_relat_1(X1,X2))),X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.22/0.41  cnf(c_0_29, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.22/0.41  cnf(c_0_30, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.22/0.41  cnf(c_0_31, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.22/0.41  cnf(c_0_32, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.22/0.41  fof(c_0_33, plain, ![X9]:k4_xboole_0(k1_xboole_0,X9)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.22/0.41  cnf(c_0_34, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.22/0.41  cnf(c_0_35, negated_conjecture, (k11_relat_1(esk4_0,X1)=k1_xboole_0|r2_hidden(k4_tarski(X1,esk1_1(k11_relat_1(esk4_0,X1))),esk4_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.22/0.41  cnf(c_0_36, plain, (X1!=X2|~r2_hidden(X1,k5_xboole_0(X3,k1_setfam_1(k1_enumset1(X3,X3,k1_enumset1(X2,X2,X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31]), c_0_19]), c_0_32])).
% 0.22/0.41  cnf(c_0_37, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.22/0.41  cnf(c_0_38, negated_conjecture, (k11_relat_1(esk4_0,esk3_0)=k1_xboole_0|~r2_hidden(esk3_0,k1_relat_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.22/0.41  cnf(c_0_39, negated_conjecture, (k11_relat_1(esk4_0,X1)=k1_xboole_0|r2_hidden(X1,k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_29])])).
% 0.22/0.41  cnf(c_0_40, plain, (~r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k1_enumset1(X2,X2,k1_enumset1(X1,X1,X1)))))), inference(er,[status(thm)],[c_0_36])).
% 0.22/0.41  cnf(c_0_41, plain, (k5_xboole_0(k1_xboole_0,k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,X1)))=k1_xboole_0), inference(rw,[status(thm)],[c_0_37, c_0_32])).
% 0.22/0.41  cnf(c_0_42, plain, (r2_hidden(X2,k11_relat_1(X3,X1))|~r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.22/0.41  cnf(c_0_43, negated_conjecture, (k11_relat_1(esk4_0,esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.22/0.41  cnf(c_0_44, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.22/0.41  fof(c_0_45, plain, ![X18, X19, X20, X22]:((((r2_hidden(esk2_3(X18,X19,X20),k2_relat_1(X20))|~r2_hidden(X18,k10_relat_1(X20,X19))|~v1_relat_1(X20))&(r2_hidden(k4_tarski(X18,esk2_3(X18,X19,X20)),X20)|~r2_hidden(X18,k10_relat_1(X20,X19))|~v1_relat_1(X20)))&(r2_hidden(esk2_3(X18,X19,X20),X19)|~r2_hidden(X18,k10_relat_1(X20,X19))|~v1_relat_1(X20)))&(~r2_hidden(X22,k2_relat_1(X20))|~r2_hidden(k4_tarski(X18,X22),X20)|~r2_hidden(X22,X19)|r2_hidden(X18,k10_relat_1(X20,X19))|~v1_relat_1(X20))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.22/0.41  cnf(c_0_46, negated_conjecture, (~r2_hidden(k4_tarski(esk3_0,X1),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_29])]), c_0_44])).
% 0.22/0.41  cnf(c_0_47, plain, (r2_hidden(k4_tarski(X1,esk2_3(X1,X2,X3)),X3)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.22/0.41  fof(c_0_48, plain, ![X23]:(~v1_relat_1(X23)|k10_relat_1(X23,k2_relat_1(X23))=k1_relat_1(X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.22/0.41  cnf(c_0_49, negated_conjecture, (r2_hidden(esk3_0,k1_relat_1(esk4_0))|k11_relat_1(esk4_0,esk3_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.22/0.41  cnf(c_0_50, negated_conjecture, (~r2_hidden(esk3_0,k10_relat_1(esk4_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_29])])).
% 0.22/0.41  cnf(c_0_51, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.22/0.41  cnf(c_0_52, negated_conjecture, (r2_hidden(esk3_0,k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_43])])).
% 0.22/0.41  cnf(c_0_53, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52]), c_0_29])]), ['proof']).
% 0.22/0.41  # SZS output end CNFRefutation
% 0.22/0.41  # Proof object total steps             : 54
% 0.22/0.41  # Proof object clause steps            : 29
% 0.22/0.41  # Proof object formula steps           : 25
% 0.22/0.41  # Proof object conjectures             : 13
% 0.22/0.41  # Proof object clause conjectures      : 10
% 0.22/0.41  # Proof object formula conjectures     : 3
% 0.22/0.41  # Proof object initial clauses used    : 15
% 0.22/0.41  # Proof object initial formulas used   : 12
% 0.22/0.41  # Proof object generating inferences   : 8
% 0.22/0.41  # Proof object simplifying inferences  : 19
% 0.22/0.41  # Training examples: 0 positive, 0 negative
% 0.22/0.41  # Parsed axioms                        : 12
% 0.22/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.22/0.41  # Initial clauses                      : 21
% 0.22/0.41  # Removed in clause preprocessing      : 4
% 0.22/0.41  # Initial clauses in saturation        : 17
% 0.22/0.41  # Processed clauses                    : 295
% 0.22/0.41  # ...of these trivial                  : 0
% 0.22/0.41  # ...subsumed                          : 206
% 0.22/0.41  # ...remaining for further processing  : 89
% 0.22/0.41  # Other redundant clauses eliminated   : 1
% 0.22/0.41  # Clauses deleted for lack of memory   : 0
% 0.22/0.41  # Backward-subsumed                    : 0
% 0.22/0.41  # Backward-rewritten                   : 2
% 0.22/0.41  # Generated clauses                    : 619
% 0.22/0.41  # ...of the previous two non-trivial   : 607
% 0.22/0.41  # Contextual simplify-reflections      : 1
% 0.22/0.41  # Paramodulations                      : 618
% 0.22/0.41  # Factorizations                       : 0
% 0.22/0.41  # Equation resolutions                 : 1
% 0.22/0.41  # Propositional unsat checks           : 0
% 0.22/0.41  #    Propositional check models        : 0
% 0.22/0.41  #    Propositional check unsatisfiable : 0
% 0.22/0.41  #    Propositional clauses             : 0
% 0.22/0.41  #    Propositional clauses after purity: 0
% 0.22/0.41  #    Propositional unsat core size     : 0
% 0.22/0.41  #    Propositional preprocessing time  : 0.000
% 0.22/0.41  #    Propositional encoding time       : 0.000
% 0.22/0.41  #    Propositional solver time         : 0.000
% 0.22/0.41  #    Success case prop preproc time    : 0.000
% 0.22/0.41  #    Success case prop encoding time   : 0.000
% 0.22/0.41  #    Success case prop solver time     : 0.000
% 0.22/0.41  # Current number of processed clauses  : 69
% 0.22/0.41  #    Positive orientable unit clauses  : 4
% 0.22/0.41  #    Positive unorientable unit clauses: 0
% 0.22/0.41  #    Negative unit clauses             : 4
% 0.22/0.41  #    Non-unit-clauses                  : 61
% 0.22/0.41  # Current number of unprocessed clauses: 343
% 0.22/0.41  # ...number of literals in the above   : 1744
% 0.22/0.41  # Current number of archived formulas  : 0
% 0.22/0.41  # Current number of archived clauses   : 23
% 0.22/0.41  # Clause-clause subsumption calls (NU) : 927
% 0.22/0.41  # Rec. Clause-clause subsumption calls : 327
% 0.22/0.41  # Non-unit clause-clause subsumptions  : 110
% 0.22/0.41  # Unit Clause-clause subsumption calls : 21
% 0.22/0.41  # Rewrite failures with RHS unbound    : 0
% 0.22/0.41  # BW rewrite match attempts            : 1
% 0.22/0.41  # BW rewrite match successes           : 1
% 0.22/0.41  # Condensation attempts                : 0
% 0.22/0.41  # Condensation successes               : 0
% 0.22/0.41  # Termbank termtop insertions          : 12560
% 0.22/0.41  
% 0.22/0.41  # -------------------------------------------------
% 0.22/0.41  # User time                : 0.043 s
% 0.22/0.41  # System time              : 0.008 s
% 0.22/0.41  # Total time               : 0.051 s
% 0.22/0.41  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
