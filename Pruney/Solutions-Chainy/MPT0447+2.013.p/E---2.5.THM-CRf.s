%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:23 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 105 expanded)
%              Number of clauses        :   32 (  45 expanded)
%              Number of leaves         :    9 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :  109 ( 270 expanded)
%              Number of equality atoms :   18 (  31 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t31_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

fof(d6_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_tarski(X1,X2)
             => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_relat_1])).

fof(c_0_10,plain,(
    ! [X69] :
      ( ~ v1_relat_1(X69)
      | k3_relat_1(X69) = k2_xboole_0(k1_relat_1(X69),k2_relat_1(X69)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

fof(c_0_11,negated_conjecture,
    ( v1_relat_1(esk9_0)
    & v1_relat_1(esk10_0)
    & r1_tarski(esk9_0,esk10_0)
    & ~ r1_tarski(k3_relat_1(esk9_0),k3_relat_1(esk10_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_12,plain,(
    ! [X72,X73] :
      ( ( r1_tarski(k1_relat_1(X72),k1_relat_1(X73))
        | ~ r1_tarski(X72,X73)
        | ~ v1_relat_1(X73)
        | ~ v1_relat_1(X72) )
      & ( r1_tarski(k2_relat_1(X72),k2_relat_1(X73))
        | ~ r1_tarski(X72,X73)
        | ~ v1_relat_1(X73)
        | ~ v1_relat_1(X72) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

fof(c_0_13,plain,(
    ! [X30,X31,X32] :
      ( ~ r1_tarski(X30,X31)
      | r1_tarski(X30,k2_xboole_0(X32,X31)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

cnf(c_0_14,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( k2_xboole_0(k1_relat_1(esk10_0),k2_relat_1(esk10_0)) = k3_relat_1(esk10_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(esk10_0))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk10_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(esk9_0,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_22,plain,(
    ! [X28,X29] :
      ( ( r1_tarski(X28,X29)
        | X28 != X29 )
      & ( r1_tarski(X29,X28)
        | X28 != X29 )
      & ( ~ r1_tarski(X28,X29)
        | ~ r1_tarski(X29,X28)
        | X28 = X29 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_23,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_24,plain,(
    ! [X36,X37] :
      ( ~ r1_tarski(X36,X37)
      | k2_xboole_0(X36,X37) = X37 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(X1,k3_relat_1(esk10_0))
    | ~ r1_tarski(X1,k2_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk9_0),k2_relat_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

fof(c_0_27,plain,(
    ! [X39,X40,X41] :
      ( ~ r1_tarski(X39,k2_xboole_0(X40,X41))
      | r1_tarski(k4_xboole_0(X39,X40),X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk9_0),k3_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(esk10_0))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk10_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_15])).

cnf(c_0_37,negated_conjecture,
    ( k2_xboole_0(k3_relat_1(esk10_0),k2_relat_1(esk9_0)) = k3_relat_1(esk10_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_29])).

cnf(c_0_38,plain,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(X1,X2),X1),X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( k2_xboole_0(k1_relat_1(esk9_0),k2_relat_1(esk9_0)) = k3_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_21])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(X1,k3_relat_1(esk10_0))
    | ~ r1_tarski(X1,k1_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_18])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk9_0),k1_relat_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_20]),c_0_21])])).

fof(c_0_42,plain,(
    ! [X42,X43,X44] :
      ( ~ r1_tarski(k4_xboole_0(X42,X43),X44)
      | r1_tarski(X42,k2_xboole_0(X43,X44)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(X1,k3_relat_1(esk10_0))
    | ~ r1_tarski(X1,k2_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k3_relat_1(esk9_0),k1_relat_1(esk9_0)),k2_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk9_0),k3_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k3_relat_1(esk9_0),k1_relat_1(esk9_0)),k3_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( k2_xboole_0(k1_relat_1(esk9_0),k3_relat_1(esk10_0)) = k3_relat_1(esk10_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(esk9_0),k3_relat_1(esk10_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_49]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:22:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.43  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S049N
% 0.20/0.43  # and selection function PSelectComplexPreferEQ.
% 0.20/0.43  #
% 0.20/0.43  # Preprocessing time       : 0.029 s
% 0.20/0.43  # Presaturation interreduction done
% 0.20/0.43  
% 0.20/0.43  # Proof found!
% 0.20/0.43  # SZS status Theorem
% 0.20/0.43  # SZS output start CNFRefutation
% 0.20/0.43  fof(t31_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 0.20/0.43  fof(d6_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 0.20/0.43  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 0.20/0.43  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 0.20/0.43  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.43  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.20/0.43  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.20/0.43  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 0.20/0.43  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 0.20/0.43  fof(c_0_9, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2)))))), inference(assume_negation,[status(cth)],[t31_relat_1])).
% 0.20/0.43  fof(c_0_10, plain, ![X69]:(~v1_relat_1(X69)|k3_relat_1(X69)=k2_xboole_0(k1_relat_1(X69),k2_relat_1(X69))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).
% 0.20/0.43  fof(c_0_11, negated_conjecture, (v1_relat_1(esk9_0)&(v1_relat_1(esk10_0)&(r1_tarski(esk9_0,esk10_0)&~r1_tarski(k3_relat_1(esk9_0),k3_relat_1(esk10_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.20/0.43  fof(c_0_12, plain, ![X72, X73]:((r1_tarski(k1_relat_1(X72),k1_relat_1(X73))|~r1_tarski(X72,X73)|~v1_relat_1(X73)|~v1_relat_1(X72))&(r1_tarski(k2_relat_1(X72),k2_relat_1(X73))|~r1_tarski(X72,X73)|~v1_relat_1(X73)|~v1_relat_1(X72))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.20/0.43  fof(c_0_13, plain, ![X30, X31, X32]:(~r1_tarski(X30,X31)|r1_tarski(X30,k2_xboole_0(X32,X31))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 0.20/0.43  cnf(c_0_14, plain, (k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.43  cnf(c_0_15, negated_conjecture, (v1_relat_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.43  cnf(c_0_16, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.43  cnf(c_0_17, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.43  cnf(c_0_18, negated_conjecture, (k2_xboole_0(k1_relat_1(esk10_0),k2_relat_1(esk10_0))=k3_relat_1(esk10_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.20/0.43  cnf(c_0_19, negated_conjecture, (r1_tarski(k2_relat_1(X1),k2_relat_1(esk10_0))|~v1_relat_1(X1)|~r1_tarski(X1,esk10_0)), inference(spm,[status(thm)],[c_0_16, c_0_15])).
% 0.20/0.43  cnf(c_0_20, negated_conjecture, (r1_tarski(esk9_0,esk10_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.43  cnf(c_0_21, negated_conjecture, (v1_relat_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.43  fof(c_0_22, plain, ![X28, X29]:(((r1_tarski(X28,X29)|X28!=X29)&(r1_tarski(X29,X28)|X28!=X29))&(~r1_tarski(X28,X29)|~r1_tarski(X29,X28)|X28=X29)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.43  fof(c_0_23, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.20/0.43  fof(c_0_24, plain, ![X36, X37]:(~r1_tarski(X36,X37)|k2_xboole_0(X36,X37)=X37), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.20/0.43  cnf(c_0_25, negated_conjecture, (r1_tarski(X1,k3_relat_1(esk10_0))|~r1_tarski(X1,k2_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.43  cnf(c_0_26, negated_conjecture, (r1_tarski(k2_relat_1(esk9_0),k2_relat_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])])).
% 0.20/0.43  fof(c_0_27, plain, ![X39, X40, X41]:(~r1_tarski(X39,k2_xboole_0(X40,X41))|r1_tarski(k4_xboole_0(X39,X40),X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 0.20/0.43  cnf(c_0_28, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.43  cnf(c_0_29, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.43  cnf(c_0_30, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.43  cnf(c_0_31, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.43  cnf(c_0_32, negated_conjecture, (r1_tarski(k2_relat_1(esk9_0),k3_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.43  cnf(c_0_33, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.43  cnf(c_0_34, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_28])).
% 0.20/0.43  cnf(c_0_35, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_17, c_0_29])).
% 0.20/0.43  cnf(c_0_36, negated_conjecture, (r1_tarski(k1_relat_1(X1),k1_relat_1(esk10_0))|~v1_relat_1(X1)|~r1_tarski(X1,esk10_0)), inference(spm,[status(thm)],[c_0_30, c_0_15])).
% 0.20/0.43  cnf(c_0_37, negated_conjecture, (k2_xboole_0(k3_relat_1(esk10_0),k2_relat_1(esk9_0))=k3_relat_1(esk10_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_29])).
% 0.20/0.43  cnf(c_0_38, plain, (r1_tarski(k4_xboole_0(k2_xboole_0(X1,X2),X1),X2)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.43  cnf(c_0_39, negated_conjecture, (k2_xboole_0(k1_relat_1(esk9_0),k2_relat_1(esk9_0))=k3_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_14, c_0_21])).
% 0.20/0.43  cnf(c_0_40, negated_conjecture, (r1_tarski(X1,k3_relat_1(esk10_0))|~r1_tarski(X1,k1_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_35, c_0_18])).
% 0.20/0.43  cnf(c_0_41, negated_conjecture, (r1_tarski(k1_relat_1(esk9_0),k1_relat_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_20]), c_0_21])])).
% 0.20/0.43  fof(c_0_42, plain, ![X42, X43, X44]:(~r1_tarski(k4_xboole_0(X42,X43),X44)|r1_tarski(X42,k2_xboole_0(X43,X44))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 0.20/0.43  cnf(c_0_43, negated_conjecture, (r1_tarski(X1,k3_relat_1(esk10_0))|~r1_tarski(X1,k2_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_17, c_0_37])).
% 0.20/0.43  cnf(c_0_44, negated_conjecture, (r1_tarski(k4_xboole_0(k3_relat_1(esk9_0),k1_relat_1(esk9_0)),k2_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.43  cnf(c_0_45, negated_conjecture, (r1_tarski(k1_relat_1(esk9_0),k3_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.43  cnf(c_0_46, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.43  cnf(c_0_47, negated_conjecture, (r1_tarski(k4_xboole_0(k3_relat_1(esk9_0),k1_relat_1(esk9_0)),k3_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.20/0.43  cnf(c_0_48, negated_conjecture, (k2_xboole_0(k1_relat_1(esk9_0),k3_relat_1(esk10_0))=k3_relat_1(esk10_0)), inference(spm,[status(thm)],[c_0_31, c_0_45])).
% 0.20/0.43  cnf(c_0_49, negated_conjecture, (~r1_tarski(k3_relat_1(esk9_0),k3_relat_1(esk10_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.43  cnf(c_0_50, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_49]), ['proof']).
% 0.20/0.43  # SZS output end CNFRefutation
% 0.20/0.43  # Proof object total steps             : 51
% 0.20/0.43  # Proof object clause steps            : 32
% 0.20/0.43  # Proof object formula steps           : 19
% 0.20/0.43  # Proof object conjectures             : 23
% 0.20/0.43  # Proof object clause conjectures      : 20
% 0.20/0.43  # Proof object formula conjectures     : 3
% 0.20/0.43  # Proof object initial clauses used    : 13
% 0.20/0.43  # Proof object initial formulas used   : 9
% 0.20/0.43  # Proof object generating inferences   : 18
% 0.20/0.43  # Proof object simplifying inferences  : 8
% 0.20/0.43  # Training examples: 0 positive, 0 negative
% 0.20/0.43  # Parsed axioms                        : 21
% 0.20/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.43  # Initial clauses                      : 42
% 0.20/0.43  # Removed in clause preprocessing      : 1
% 0.20/0.43  # Initial clauses in saturation        : 41
% 0.20/0.43  # Processed clauses                    : 750
% 0.20/0.43  # ...of these trivial                  : 79
% 0.20/0.43  # ...subsumed                          : 291
% 0.20/0.43  # ...remaining for further processing  : 380
% 0.20/0.43  # Other redundant clauses eliminated   : 10
% 0.20/0.43  # Clauses deleted for lack of memory   : 0
% 0.20/0.43  # Backward-subsumed                    : 2
% 0.20/0.43  # Backward-rewritten                   : 31
% 0.20/0.43  # Generated clauses                    : 3563
% 0.20/0.43  # ...of the previous two non-trivial   : 1925
% 0.20/0.43  # Contextual simplify-reflections      : 1
% 0.20/0.43  # Paramodulations                      : 3552
% 0.20/0.43  # Factorizations                       : 2
% 0.20/0.43  # Equation resolutions                 : 10
% 0.20/0.43  # Propositional unsat checks           : 0
% 0.20/0.43  #    Propositional check models        : 0
% 0.20/0.43  #    Propositional check unsatisfiable : 0
% 0.20/0.43  #    Propositional clauses             : 0
% 0.20/0.43  #    Propositional clauses after purity: 0
% 0.20/0.43  #    Propositional unsat core size     : 0
% 0.20/0.43  #    Propositional preprocessing time  : 0.000
% 0.20/0.43  #    Propositional encoding time       : 0.000
% 0.20/0.43  #    Propositional solver time         : 0.000
% 0.20/0.43  #    Success case prop preproc time    : 0.000
% 0.20/0.43  #    Success case prop encoding time   : 0.000
% 0.20/0.43  #    Success case prop solver time     : 0.000
% 0.20/0.43  # Current number of processed clauses  : 298
% 0.20/0.43  #    Positive orientable unit clauses  : 124
% 0.20/0.43  #    Positive unorientable unit clauses: 1
% 0.20/0.43  #    Negative unit clauses             : 6
% 0.20/0.43  #    Non-unit-clauses                  : 167
% 0.20/0.43  # Current number of unprocessed clauses: 1162
% 0.20/0.43  # ...number of literals in the above   : 1794
% 0.20/0.43  # Current number of archived formulas  : 0
% 0.20/0.43  # Current number of archived clauses   : 74
% 0.20/0.43  # Clause-clause subsumption calls (NU) : 3158
% 0.20/0.43  # Rec. Clause-clause subsumption calls : 2620
% 0.20/0.43  # Non-unit clause-clause subsumptions  : 167
% 0.20/0.43  # Unit Clause-clause subsumption calls : 237
% 0.20/0.43  # Rewrite failures with RHS unbound    : 0
% 0.20/0.43  # BW rewrite match attempts            : 104
% 0.20/0.43  # BW rewrite match successes           : 40
% 0.20/0.43  # Condensation attempts                : 0
% 0.20/0.43  # Condensation successes               : 0
% 0.20/0.43  # Termbank termtop insertions          : 34064
% 0.20/0.43  
% 0.20/0.43  # -------------------------------------------------
% 0.20/0.43  # User time                : 0.079 s
% 0.20/0.43  # System time              : 0.001 s
% 0.20/0.43  # Total time               : 0.080 s
% 0.20/0.43  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
