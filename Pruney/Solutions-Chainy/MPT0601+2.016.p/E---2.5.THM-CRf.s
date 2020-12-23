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
% DateTime   : Thu Dec  3 10:52:14 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 150 expanded)
%              Number of clauses        :   29 (  69 expanded)
%              Number of leaves         :    9 (  40 expanded)
%              Depth                    :   13
%              Number of atoms          :  117 ( 402 expanded)
%              Number of equality atoms :   36 ( 136 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(fc1_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t205_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k1_relat_1(X2))
      <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(t49_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(t46_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(t19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ~ ( r2_hidden(X1,k2_relat_1(X2))
          & ! [X3] : ~ r2_hidden(X3,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(t204_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> r2_hidden(X2,k11_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(c_0_9,plain,(
    ! [X34,X35] :
      ( ~ v1_relat_1(X34)
      | v1_relat_1(k3_xboole_0(X34,X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).

fof(c_0_10,plain,(
    ! [X14] : k3_xboole_0(X14,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X1,k1_relat_1(X2))
        <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t205_relat_1])).

cnf(c_0_12,plain,
    ( v1_relat_1(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,negated_conjecture,
    ( v1_relat_1(esk8_0)
    & ( ~ r2_hidden(esk7_0,k1_relat_1(esk8_0))
      | k11_relat_1(esk8_0,esk7_0) = k1_xboole_0 )
    & ( r2_hidden(esk7_0,k1_relat_1(esk8_0))
      | k11_relat_1(esk8_0,esk7_0) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_15,plain,(
    ! [X19,X20] : k2_xboole_0(k1_tarski(X19),X20) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

fof(c_0_16,plain,(
    ! [X17,X18] :
      ( ~ r2_hidden(X17,X18)
      | k2_xboole_0(k1_tarski(X17),X18) = X18 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_zfmisc_1])])).

fof(c_0_17,plain,(
    ! [X41,X42] :
      ( ~ v1_relat_1(X42)
      | ~ r2_hidden(X41,k2_relat_1(X42))
      | r2_hidden(esk6_2(X41,X42),k1_relat_1(X42)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t19_relat_1])])])])).

cnf(c_0_18,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( r2_hidden(esk6_2(X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_24,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,plain,
    ( r2_hidden(esk6_2(X1,k1_xboole_0),k1_xboole_0)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25])])).

fof(c_0_28,plain,(
    ! [X23,X24,X25,X27,X28,X29,X30,X32] :
      ( ( ~ r2_hidden(X25,X24)
        | r2_hidden(k4_tarski(X25,esk2_3(X23,X24,X25)),X23)
        | X24 != k1_relat_1(X23) )
      & ( ~ r2_hidden(k4_tarski(X27,X28),X23)
        | r2_hidden(X27,X24)
        | X24 != k1_relat_1(X23) )
      & ( ~ r2_hidden(esk3_2(X29,X30),X30)
        | ~ r2_hidden(k4_tarski(esk3_2(X29,X30),X32),X29)
        | X30 = k1_relat_1(X29) )
      & ( r2_hidden(esk3_2(X29,X30),X30)
        | r2_hidden(k4_tarski(esk3_2(X29,X30),esk4_2(X29,X30)),X29)
        | X30 = k1_relat_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

fof(c_0_29,plain,(
    ! [X44,X45,X46] :
      ( ( ~ r2_hidden(k4_tarski(X44,X45),X46)
        | r2_hidden(X45,k11_relat_1(X46,X44))
        | ~ v1_relat_1(X46) )
      & ( ~ r2_hidden(X45,k11_relat_1(X46,X44))
        | r2_hidden(k4_tarski(X44,X45),X46)
        | ~ v1_relat_1(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)
    | X2 = k1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_32,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,k11_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_33,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_2(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_23])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( k11_relat_1(X1,X2) = k1_xboole_0
    | r2_hidden(k4_tarski(X2,esk3_2(k1_xboole_0,k11_relat_1(X1,X2))),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_36,plain,
    ( r2_hidden(X2,k11_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( k11_relat_1(X1,X2) = k1_xboole_0
    | r2_hidden(X2,X3)
    | X3 != k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),k11_relat_1(X1,X3))
    | X2 != k1_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( k11_relat_1(esk8_0,esk7_0) = k1_xboole_0
    | ~ r2_hidden(esk7_0,k1_relat_1(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk7_0,k1_relat_1(esk8_0))
    | k11_relat_1(esk8_0,esk7_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_42,plain,
    ( k11_relat_1(X1,X2) = k1_xboole_0
    | r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( X1 != k1_relat_1(esk8_0)
    | ~ r2_hidden(esk7_0,k1_relat_1(esk8_0))
    | ~ r2_hidden(esk7_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_19])]),c_0_30])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk7_0,k1_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_19])])).

cnf(c_0_45,negated_conjecture,
    ( X1 != k1_relat_1(esk8_0)
    | ~ r2_hidden(esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44])])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_45,c_0_44]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:51:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 1.84/2.07  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 1.84/2.07  # and selection function SelectMaxLComplexAvoidPosPred.
% 1.84/2.07  #
% 1.84/2.07  # Preprocessing time       : 0.029 s
% 1.84/2.07  # Presaturation interreduction done
% 1.84/2.07  
% 1.84/2.07  # Proof found!
% 1.84/2.07  # SZS status Theorem
% 1.84/2.07  # SZS output start CNFRefutation
% 1.84/2.07  fof(fc1_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k3_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 1.84/2.07  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 1.84/2.07  fof(t205_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 1.84/2.07  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.84/2.07  fof(t46_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 1.84/2.07  fof(t19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>~((r2_hidden(X1,k2_relat_1(X2))&![X3]:~(r2_hidden(X3,k1_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relat_1)).
% 1.84/2.07  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.84/2.07  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 1.84/2.07  fof(t204_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r2_hidden(X2,k11_relat_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 1.84/2.07  fof(c_0_9, plain, ![X34, X35]:(~v1_relat_1(X34)|v1_relat_1(k3_xboole_0(X34,X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).
% 1.84/2.07  fof(c_0_10, plain, ![X14]:k3_xboole_0(X14,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 1.84/2.07  fof(c_0_11, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t205_relat_1])).
% 1.84/2.07  cnf(c_0_12, plain, (v1_relat_1(k3_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.84/2.07  cnf(c_0_13, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.84/2.07  fof(c_0_14, negated_conjecture, (v1_relat_1(esk8_0)&((~r2_hidden(esk7_0,k1_relat_1(esk8_0))|k11_relat_1(esk8_0,esk7_0)=k1_xboole_0)&(r2_hidden(esk7_0,k1_relat_1(esk8_0))|k11_relat_1(esk8_0,esk7_0)!=k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 1.84/2.07  fof(c_0_15, plain, ![X19, X20]:k2_xboole_0(k1_tarski(X19),X20)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 1.84/2.07  fof(c_0_16, plain, ![X17, X18]:(~r2_hidden(X17,X18)|k2_xboole_0(k1_tarski(X17),X18)=X18), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_zfmisc_1])])).
% 1.84/2.07  fof(c_0_17, plain, ![X41, X42]:(~v1_relat_1(X42)|(~r2_hidden(X41,k2_relat_1(X42))|r2_hidden(esk6_2(X41,X42),k1_relat_1(X42)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t19_relat_1])])])])).
% 1.84/2.07  cnf(c_0_18, plain, (v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 1.84/2.07  cnf(c_0_19, negated_conjecture, (v1_relat_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.84/2.07  cnf(c_0_20, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.84/2.07  cnf(c_0_21, plain, (k2_xboole_0(k1_tarski(X1),X2)=X2|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.84/2.07  cnf(c_0_22, plain, (r2_hidden(esk6_2(X2,X1),k1_relat_1(X1))|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.84/2.07  cnf(c_0_23, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 1.84/2.07  cnf(c_0_24, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 1.84/2.07  cnf(c_0_25, negated_conjecture, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 1.84/2.07  cnf(c_0_26, plain, (X1!=k1_xboole_0|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 1.84/2.07  cnf(c_0_27, plain, (r2_hidden(esk6_2(X1,k1_xboole_0),k1_xboole_0)|~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25])])).
% 1.84/2.07  fof(c_0_28, plain, ![X23, X24, X25, X27, X28, X29, X30, X32]:(((~r2_hidden(X25,X24)|r2_hidden(k4_tarski(X25,esk2_3(X23,X24,X25)),X23)|X24!=k1_relat_1(X23))&(~r2_hidden(k4_tarski(X27,X28),X23)|r2_hidden(X27,X24)|X24!=k1_relat_1(X23)))&((~r2_hidden(esk3_2(X29,X30),X30)|~r2_hidden(k4_tarski(esk3_2(X29,X30),X32),X29)|X30=k1_relat_1(X29))&(r2_hidden(esk3_2(X29,X30),X30)|r2_hidden(k4_tarski(esk3_2(X29,X30),esk4_2(X29,X30)),X29)|X30=k1_relat_1(X29)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 1.84/2.07  fof(c_0_29, plain, ![X44, X45, X46]:((~r2_hidden(k4_tarski(X44,X45),X46)|r2_hidden(X45,k11_relat_1(X46,X44))|~v1_relat_1(X46))&(~r2_hidden(X45,k11_relat_1(X46,X44))|r2_hidden(k4_tarski(X44,X45),X46)|~v1_relat_1(X46))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).
% 1.84/2.07  cnf(c_0_30, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 1.84/2.07  cnf(c_0_31, plain, (r2_hidden(esk3_2(X1,X2),X2)|r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)|X2=k1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.84/2.07  cnf(c_0_32, plain, (r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,k11_relat_1(X2,X3))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.84/2.07  cnf(c_0_33, plain, (X1=k1_xboole_0|r2_hidden(esk3_2(k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_23])).
% 1.84/2.07  cnf(c_0_34, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.84/2.07  cnf(c_0_35, plain, (k11_relat_1(X1,X2)=k1_xboole_0|r2_hidden(k4_tarski(X2,esk3_2(k1_xboole_0,k11_relat_1(X1,X2))),X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 1.84/2.07  cnf(c_0_36, plain, (r2_hidden(X2,k11_relat_1(X3,X1))|~r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.84/2.07  cnf(c_0_37, plain, (r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.84/2.07  cnf(c_0_38, plain, (k11_relat_1(X1,X2)=k1_xboole_0|r2_hidden(X2,X3)|X3!=k1_relat_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 1.84/2.07  cnf(c_0_39, plain, (r2_hidden(esk2_3(X1,X2,X3),k11_relat_1(X1,X3))|X2!=k1_relat_1(X1)|~v1_relat_1(X1)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 1.84/2.07  cnf(c_0_40, negated_conjecture, (k11_relat_1(esk8_0,esk7_0)=k1_xboole_0|~r2_hidden(esk7_0,k1_relat_1(esk8_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.84/2.07  cnf(c_0_41, negated_conjecture, (r2_hidden(esk7_0,k1_relat_1(esk8_0))|k11_relat_1(esk8_0,esk7_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.84/2.07  cnf(c_0_42, plain, (k11_relat_1(X1,X2)=k1_xboole_0|r2_hidden(X2,k1_relat_1(X1))|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_38])).
% 1.84/2.07  cnf(c_0_43, negated_conjecture, (X1!=k1_relat_1(esk8_0)|~r2_hidden(esk7_0,k1_relat_1(esk8_0))|~r2_hidden(esk7_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_19])]), c_0_30])).
% 1.84/2.07  cnf(c_0_44, negated_conjecture, (r2_hidden(esk7_0,k1_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_19])])).
% 1.84/2.07  cnf(c_0_45, negated_conjecture, (X1!=k1_relat_1(esk8_0)|~r2_hidden(esk7_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44])])).
% 1.84/2.07  cnf(c_0_46, negated_conjecture, ($false), inference(spm,[status(thm)],[c_0_45, c_0_44]), ['proof']).
% 1.84/2.07  # SZS output end CNFRefutation
% 1.84/2.07  # Proof object total steps             : 47
% 1.84/2.07  # Proof object clause steps            : 29
% 1.84/2.07  # Proof object formula steps           : 18
% 1.84/2.07  # Proof object conjectures             : 11
% 1.84/2.07  # Proof object clause conjectures      : 8
% 1.84/2.07  # Proof object formula conjectures     : 3
% 1.84/2.07  # Proof object initial clauses used    : 15
% 1.84/2.07  # Proof object initial formulas used   : 9
% 1.84/2.07  # Proof object generating inferences   : 13
% 1.84/2.07  # Proof object simplifying inferences  : 11
% 1.84/2.07  # Training examples: 0 positive, 0 negative
% 1.84/2.07  # Parsed axioms                        : 13
% 1.84/2.07  # Removed by relevancy pruning/SinE    : 0
% 1.84/2.07  # Initial clauses                      : 29
% 1.84/2.07  # Removed in clause preprocessing      : 0
% 1.84/2.07  # Initial clauses in saturation        : 29
% 1.84/2.07  # Processed clauses                    : 14273
% 1.84/2.07  # ...of these trivial                  : 47
% 1.84/2.07  # ...subsumed                          : 12638
% 1.84/2.07  # ...remaining for further processing  : 1588
% 1.84/2.07  # Other redundant clauses eliminated   : 75
% 1.84/2.07  # Clauses deleted for lack of memory   : 0
% 1.84/2.07  # Backward-subsumed                    : 32
% 1.84/2.07  # Backward-rewritten                   : 13
% 1.84/2.07  # Generated clauses                    : 192181
% 1.84/2.07  # ...of the previous two non-trivial   : 186483
% 1.84/2.07  # Contextual simplify-reflections      : 25
% 1.84/2.07  # Paramodulations                      : 191608
% 1.84/2.07  # Factorizations                       : 14
% 1.84/2.07  # Equation resolutions                 : 559
% 1.84/2.07  # Propositional unsat checks           : 0
% 1.84/2.07  #    Propositional check models        : 0
% 1.84/2.07  #    Propositional check unsatisfiable : 0
% 1.84/2.07  #    Propositional clauses             : 0
% 1.84/2.07  #    Propositional clauses after purity: 0
% 1.84/2.07  #    Propositional unsat core size     : 0
% 1.84/2.07  #    Propositional preprocessing time  : 0.000
% 1.84/2.07  #    Propositional encoding time       : 0.000
% 1.84/2.07  #    Propositional solver time         : 0.000
% 1.84/2.07  #    Success case prop preproc time    : 0.000
% 1.84/2.07  #    Success case prop encoding time   : 0.000
% 1.84/2.07  #    Success case prop solver time     : 0.000
% 1.84/2.07  # Current number of processed clauses  : 1514
% 1.84/2.07  #    Positive orientable unit clauses  : 14
% 1.84/2.07  #    Positive unorientable unit clauses: 0
% 1.84/2.07  #    Negative unit clauses             : 5
% 1.84/2.07  #    Non-unit-clauses                  : 1495
% 1.84/2.07  # Current number of unprocessed clauses: 172135
% 1.84/2.07  # ...number of literals in the above   : 958588
% 1.84/2.07  # Current number of archived formulas  : 0
% 1.84/2.07  # Current number of archived clauses   : 74
% 1.84/2.07  # Clause-clause subsumption calls (NU) : 438537
% 1.84/2.07  # Rec. Clause-clause subsumption calls : 90817
% 1.84/2.07  # Non-unit clause-clause subsumptions  : 6736
% 1.84/2.07  # Unit Clause-clause subsumption calls : 293
% 1.84/2.07  # Rewrite failures with RHS unbound    : 0
% 1.84/2.07  # BW rewrite match attempts            : 19
% 1.84/2.07  # BW rewrite match successes           : 5
% 1.84/2.07  # Condensation attempts                : 0
% 1.84/2.07  # Condensation successes               : 0
% 1.84/2.07  # Termbank termtop insertions          : 3321544
% 1.84/2.08  
% 1.84/2.08  # -------------------------------------------------
% 1.84/2.08  # User time                : 1.650 s
% 1.84/2.08  # System time              : 0.080 s
% 1.84/2.08  # Total time               : 1.730 s
% 1.84/2.08  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
