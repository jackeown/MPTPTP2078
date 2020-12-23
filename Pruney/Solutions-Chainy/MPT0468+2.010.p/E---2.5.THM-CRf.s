%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:44 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   41 (  66 expanded)
%              Number of clauses        :   20 (  26 expanded)
%              Number of leaves         :   10 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   90 ( 133 expanded)
%              Number of equality atoms :   35 (  59 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(t91_enumset1,axiom,(
    ! [X1] : k4_enumset1(X1,X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(t56_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ! [X2,X3] : ~ r2_hidden(k4_tarski(X2,X3),X1)
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

fof(fc1_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t22_zfmisc_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k1_tarski(X1),k2_tarski(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_zfmisc_1)).

fof(t88_enumset1,axiom,(
    ! [X1,X2] : k4_enumset1(X1,X1,X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_enumset1)).

fof(d2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( X1 = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X1)
              <=> r2_hidden(k4_tarski(X3,X4),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_relat_1)).

fof(c_0_10,plain,(
    ! [X27,X28,X29] :
      ( ( r2_hidden(X27,X28)
        | ~ r2_hidden(X27,k4_xboole_0(X28,k1_tarski(X29))) )
      & ( X27 != X29
        | ~ r2_hidden(X27,k4_xboole_0(X28,k1_tarski(X29))) )
      & ( ~ r2_hidden(X27,X28)
        | X27 = X29
        | r2_hidden(X27,k4_xboole_0(X28,k1_tarski(X29))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

fof(c_0_11,plain,(
    ! [X24] : k4_enumset1(X24,X24,X24,X24,X24,X24) = k1_tarski(X24) ),
    inference(variable_rename,[status(thm)],[t91_enumset1])).

fof(c_0_12,plain,(
    ! [X9,X10,X11,X12,X13,X14] : k5_enumset1(X9,X9,X10,X11,X12,X13,X14) = k4_enumset1(X9,X10,X11,X12,X13,X14) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_13,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21] : k6_enumset1(X15,X15,X16,X17,X18,X19,X20,X21) = k5_enumset1(X15,X16,X17,X18,X19,X20,X21) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ( ! [X2,X3] : ~ r2_hidden(k4_tarski(X2,X3),X1)
         => X1 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t56_relat_1])).

fof(c_0_15,plain,(
    ! [X38,X39] :
      ( ~ v1_relat_1(X38)
      | v1_relat_1(k3_xboole_0(X38,X39)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).

fof(c_0_16,plain,(
    ! [X8] : k3_xboole_0(X8,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_17,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( k4_enumset1(X1,X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_21,plain,(
    ! [X25,X26] : k4_xboole_0(k1_tarski(X25),k2_tarski(X25,X26)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t22_zfmisc_1])).

fof(c_0_22,plain,(
    ! [X22,X23] : k4_enumset1(X22,X22,X22,X22,X22,X23) = k2_tarski(X22,X23) ),
    inference(variable_rename,[status(thm)],[t88_enumset1])).

fof(c_0_23,plain,(
    ! [X30,X31,X32,X33,X34,X35] :
      ( ( ~ r2_hidden(k4_tarski(X32,X33),X30)
        | r2_hidden(k4_tarski(X32,X33),X31)
        | X30 != X31
        | ~ v1_relat_1(X31)
        | ~ v1_relat_1(X30) )
      & ( ~ r2_hidden(k4_tarski(X34,X35),X31)
        | r2_hidden(k4_tarski(X34,X35),X30)
        | X30 != X31
        | ~ v1_relat_1(X31)
        | ~ v1_relat_1(X30) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X30,X31),esk2_2(X30,X31)),X30)
        | ~ r2_hidden(k4_tarski(esk1_2(X30,X31),esk2_2(X30,X31)),X31)
        | X30 = X31
        | ~ v1_relat_1(X31)
        | ~ v1_relat_1(X30) )
      & ( r2_hidden(k4_tarski(esk1_2(X30,X31),esk2_2(X30,X31)),X30)
        | r2_hidden(k4_tarski(esk1_2(X30,X31),esk2_2(X30,X31)),X31)
        | X30 = X31
        | ~ v1_relat_1(X31)
        | ~ v1_relat_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_relat_1])])])])])])).

fof(c_0_24,negated_conjecture,(
    ! [X41,X42] :
      ( v1_relat_1(esk3_0)
      & ~ r2_hidden(k4_tarski(X41,X42),esk3_0)
      & esk3_0 != k1_xboole_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])])).

cnf(c_0_25,plain,
    ( v1_relat_1(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_28,plain,
    ( k4_xboole_0(k1_tarski(X1),k2_tarski(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k4_enumset1(X1,X1,X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)
    | r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)
    | X1 = X2
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X1,X2),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_18]),c_0_29]),c_0_19]),c_0_19]),c_0_20]),c_0_20])).

cnf(c_0_36,negated_conjecture,
    ( X1 = esk3_0
    | r2_hidden(k4_tarski(esk1_2(X1,esk3_0),esk2_2(X1,esk3_0)),X1)
    | ~ v1_relat_1(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_39,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:47:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.027 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 0.12/0.37  fof(t91_enumset1, axiom, ![X1]:k4_enumset1(X1,X1,X1,X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_enumset1)).
% 0.12/0.37  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.12/0.37  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.12/0.37  fof(t56_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>(![X2, X3]:~(r2_hidden(k4_tarski(X2,X3),X1))=>X1=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_relat_1)).
% 0.12/0.37  fof(fc1_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k3_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 0.12/0.37  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.12/0.37  fof(t22_zfmisc_1, axiom, ![X1, X2]:k4_xboole_0(k1_tarski(X1),k2_tarski(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_zfmisc_1)).
% 0.12/0.37  fof(t88_enumset1, axiom, ![X1, X2]:k4_enumset1(X1,X1,X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_enumset1)).
% 0.12/0.37  fof(d2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(X1=X2<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X1)<=>r2_hidden(k4_tarski(X3,X4),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_relat_1)).
% 0.12/0.37  fof(c_0_10, plain, ![X27, X28, X29]:(((r2_hidden(X27,X28)|~r2_hidden(X27,k4_xboole_0(X28,k1_tarski(X29))))&(X27!=X29|~r2_hidden(X27,k4_xboole_0(X28,k1_tarski(X29)))))&(~r2_hidden(X27,X28)|X27=X29|r2_hidden(X27,k4_xboole_0(X28,k1_tarski(X29))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 0.12/0.37  fof(c_0_11, plain, ![X24]:k4_enumset1(X24,X24,X24,X24,X24,X24)=k1_tarski(X24), inference(variable_rename,[status(thm)],[t91_enumset1])).
% 0.12/0.37  fof(c_0_12, plain, ![X9, X10, X11, X12, X13, X14]:k5_enumset1(X9,X9,X10,X11,X12,X13,X14)=k4_enumset1(X9,X10,X11,X12,X13,X14), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.12/0.37  fof(c_0_13, plain, ![X15, X16, X17, X18, X19, X20, X21]:k6_enumset1(X15,X15,X16,X17,X18,X19,X20,X21)=k5_enumset1(X15,X16,X17,X18,X19,X20,X21), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.12/0.37  fof(c_0_14, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>(![X2, X3]:~(r2_hidden(k4_tarski(X2,X3),X1))=>X1=k1_xboole_0))), inference(assume_negation,[status(cth)],[t56_relat_1])).
% 0.12/0.37  fof(c_0_15, plain, ![X38, X39]:(~v1_relat_1(X38)|v1_relat_1(k3_xboole_0(X38,X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).
% 0.12/0.37  fof(c_0_16, plain, ![X8]:k3_xboole_0(X8,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.12/0.37  cnf(c_0_17, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_18, plain, (k4_enumset1(X1,X1,X1,X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_19, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_20, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  fof(c_0_21, plain, ![X25, X26]:k4_xboole_0(k1_tarski(X25),k2_tarski(X25,X26))=k1_xboole_0, inference(variable_rename,[status(thm)],[t22_zfmisc_1])).
% 0.12/0.37  fof(c_0_22, plain, ![X22, X23]:k4_enumset1(X22,X22,X22,X22,X22,X23)=k2_tarski(X22,X23), inference(variable_rename,[status(thm)],[t88_enumset1])).
% 0.12/0.37  fof(c_0_23, plain, ![X30, X31, X32, X33, X34, X35]:(((~r2_hidden(k4_tarski(X32,X33),X30)|r2_hidden(k4_tarski(X32,X33),X31)|X30!=X31|~v1_relat_1(X31)|~v1_relat_1(X30))&(~r2_hidden(k4_tarski(X34,X35),X31)|r2_hidden(k4_tarski(X34,X35),X30)|X30!=X31|~v1_relat_1(X31)|~v1_relat_1(X30)))&((~r2_hidden(k4_tarski(esk1_2(X30,X31),esk2_2(X30,X31)),X30)|~r2_hidden(k4_tarski(esk1_2(X30,X31),esk2_2(X30,X31)),X31)|X30=X31|~v1_relat_1(X31)|~v1_relat_1(X30))&(r2_hidden(k4_tarski(esk1_2(X30,X31),esk2_2(X30,X31)),X30)|r2_hidden(k4_tarski(esk1_2(X30,X31),esk2_2(X30,X31)),X31)|X30=X31|~v1_relat_1(X31)|~v1_relat_1(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_relat_1])])])])])])).
% 0.12/0.37  fof(c_0_24, negated_conjecture, ![X41, X42]:(v1_relat_1(esk3_0)&(~r2_hidden(k4_tarski(X41,X42),esk3_0)&esk3_0!=k1_xboole_0)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])])).
% 0.12/0.37  cnf(c_0_25, plain, (v1_relat_1(k3_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_26, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_27, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20])).
% 0.12/0.37  cnf(c_0_28, plain, (k4_xboole_0(k1_tarski(X1),k2_tarski(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.37  cnf(c_0_29, plain, (k4_enumset1(X1,X1,X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.37  cnf(c_0_30, plain, (r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)|r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)|X1=X2|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.37  cnf(c_0_31, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.37  cnf(c_0_32, negated_conjecture, (~r2_hidden(k4_tarski(X1,X2),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.37  cnf(c_0_33, plain, (v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.12/0.37  cnf(c_0_34, plain, (~r2_hidden(X1,k4_xboole_0(X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))), inference(er,[status(thm)],[c_0_27])).
% 0.12/0.37  cnf(c_0_35, plain, (k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_18]), c_0_29]), c_0_19]), c_0_19]), c_0_20]), c_0_20])).
% 0.12/0.37  cnf(c_0_36, negated_conjecture, (X1=esk3_0|r2_hidden(k4_tarski(esk1_2(X1,esk3_0),esk2_2(X1,esk3_0)),X1)|~v1_relat_1(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 0.12/0.37  cnf(c_0_37, negated_conjecture, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_33, c_0_31])).
% 0.12/0.37  cnf(c_0_38, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.37  cnf(c_0_39, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.12/0.37  cnf(c_0_40, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_39]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 41
% 0.12/0.37  # Proof object clause steps            : 20
% 0.12/0.37  # Proof object formula steps           : 21
% 0.12/0.37  # Proof object conjectures             : 9
% 0.12/0.37  # Proof object clause conjectures      : 6
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 12
% 0.12/0.37  # Proof object initial formulas used   : 10
% 0.12/0.37  # Proof object generating inferences   : 5
% 0.12/0.37  # Proof object simplifying inferences  : 13
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 10
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 17
% 0.12/0.37  # Removed in clause preprocessing      : 6
% 0.12/0.37  # Initial clauses in saturation        : 11
% 0.12/0.37  # Processed clauses                    : 28
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 1
% 0.12/0.37  # ...remaining for further processing  : 27
% 0.12/0.37  # Other redundant clauses eliminated   : 1
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 1
% 0.12/0.37  # Generated clauses                    : 11
% 0.12/0.37  # ...of the previous two non-trivial   : 10
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 10
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 1
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 14
% 0.12/0.37  #    Positive orientable unit clauses  : 4
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 4
% 0.12/0.37  #    Non-unit-clauses                  : 6
% 0.12/0.37  # Current number of unprocessed clauses: 2
% 0.12/0.37  # ...number of literals in the above   : 8
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 16
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 15
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 4
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.37  # Unit Clause-clause subsumption calls : 5
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 1
% 0.12/0.37  # BW rewrite match successes           : 1
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 1324
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.026 s
% 0.12/0.37  # System time              : 0.005 s
% 0.12/0.37  # Total time               : 0.032 s
% 0.12/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
