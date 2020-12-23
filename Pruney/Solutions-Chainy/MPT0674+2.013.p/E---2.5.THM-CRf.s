%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:25 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   40 (  91 expanded)
%              Number of clauses        :   23 (  36 expanded)
%              Number of leaves         :    8 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :  111 ( 224 expanded)
%              Number of equality atoms :   52 ( 107 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t117_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => k11_relat_1(X2,X1) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

fof(t204_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> r2_hidden(X2,k11_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(t41_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_tarski(X2)
        & X1 != k1_xboole_0
        & ! [X3] :
            ~ ( r2_hidden(X3,X1)
              & X3 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(t205_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k1_relat_1(X2))
      <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( r2_hidden(X1,k1_relat_1(X2))
         => k11_relat_1(X2,X1) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t117_funct_1])).

fof(c_0_9,plain,(
    ! [X13,X14,X15] :
      ( ( ~ r2_hidden(k4_tarski(X13,X14),X15)
        | r2_hidden(X14,k11_relat_1(X15,X13))
        | ~ v1_relat_1(X15) )
      & ( ~ r2_hidden(X14,k11_relat_1(X15,X13))
        | r2_hidden(k4_tarski(X13,X14),X15)
        | ~ v1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).

fof(c_0_10,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & r2_hidden(esk2_0,k1_relat_1(esk3_0))
    & k11_relat_1(esk3_0,esk2_0) != k1_tarski(k1_funct_1(esk3_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_11,plain,(
    ! [X10,X11] :
      ( ( r2_hidden(esk1_2(X10,X11),X10)
        | X10 = k1_tarski(X11)
        | X10 = k1_xboole_0 )
      & ( esk1_2(X10,X11) != X11
        | X10 = k1_tarski(X11)
        | X10 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_zfmisc_1])])])])).

fof(c_0_12,plain,(
    ! [X4] : k2_tarski(X4,X4) = k1_tarski(X4) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_13,plain,(
    ! [X5,X6] : k1_enumset1(X5,X5,X6) = k2_tarski(X5,X6) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_14,plain,(
    ! [X7,X8,X9] : k2_enumset1(X7,X7,X8,X9) = k1_enumset1(X7,X8,X9) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_15,plain,(
    ! [X18,X19,X20] :
      ( ( r2_hidden(X18,k1_relat_1(X20))
        | ~ r2_hidden(k4_tarski(X18,X19),X20)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( X19 = k1_funct_1(X20,X18)
        | ~ r2_hidden(k4_tarski(X18,X19),X20)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( ~ r2_hidden(X18,k1_relat_1(X20))
        | X19 != k1_funct_1(X20,X18)
        | r2_hidden(k4_tarski(X18,X19),X20)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

cnf(c_0_16,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,k11_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | X1 = k1_tarski(X2)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),esk3_0)
    | ~ r2_hidden(X2,k11_relat_1(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_25,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_enumset1(X2,X2,X2,X2)
    | r2_hidden(esk1_2(X1,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( k11_relat_1(esk3_0,esk2_0) != k1_tarski(k1_funct_1(esk3_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_27,negated_conjecture,
    ( X1 = k1_funct_1(esk3_0,X2)
    | ~ r2_hidden(k4_tarski(X2,X1),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_17])])).

cnf(c_0_28,negated_conjecture,
    ( k11_relat_1(esk3_0,X1) = k2_enumset1(X2,X2,X2,X2)
    | k11_relat_1(esk3_0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(X1,esk1_2(k11_relat_1(esk3_0,X1),X2)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( k11_relat_1(esk3_0,esk2_0) != k2_enumset1(k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_19]),c_0_20]),c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( esk1_2(k11_relat_1(esk3_0,X1),X2) = k1_funct_1(esk3_0,X1)
    | k11_relat_1(esk3_0,X1) = k2_enumset1(X2,X2,X2,X2)
    | k11_relat_1(esk3_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,plain,
    ( X1 = k1_tarski(X2)
    | X1 = k1_xboole_0
    | esk1_2(X1,X2) != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_32,negated_conjecture,
    ( esk1_2(k11_relat_1(esk3_0,X1),k1_funct_1(esk3_0,esk2_0)) = k1_funct_1(esk3_0,X1)
    | k11_relat_1(esk3_0,X1) = k1_xboole_0
    | k11_relat_1(esk3_0,X1) != k11_relat_1(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_33,plain,(
    ! [X16,X17] :
      ( ( ~ r2_hidden(X16,k1_relat_1(X17))
        | k11_relat_1(X17,X16) != k1_xboole_0
        | ~ v1_relat_1(X17) )
      & ( k11_relat_1(X17,X16) = k1_xboole_0
        | r2_hidden(X16,k1_relat_1(X17))
        | ~ v1_relat_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t205_relat_1])])])).

cnf(c_0_34,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_enumset1(X2,X2,X2,X2)
    | esk1_2(X1,X2) != X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_19]),c_0_20]),c_0_21])).

cnf(c_0_35,negated_conjecture,
    ( esk1_2(k11_relat_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0)) = k1_funct_1(esk3_0,esk2_0)
    | k11_relat_1(esk3_0,esk2_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,k1_relat_1(X2))
    | k11_relat_1(X2,X1) != k1_xboole_0
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( k11_relat_1(esk3_0,esk2_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk2_0,k1_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_17]),c_0_38])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:40:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S074I
% 0.14/0.38  # and selection function SelectCQIArEqFirst.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.027 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t117_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r2_hidden(X1,k1_relat_1(X2))=>k11_relat_1(X2,X1)=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_funct_1)).
% 0.14/0.38  fof(t204_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r2_hidden(X2,k11_relat_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 0.14/0.38  fof(t41_zfmisc_1, axiom, ![X1, X2]:~(((X1!=k1_tarski(X2)&X1!=k1_xboole_0)&![X3]:~((r2_hidden(X3,X1)&X3!=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 0.14/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.14/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.14/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.14/0.38  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 0.14/0.38  fof(t205_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 0.14/0.38  fof(c_0_8, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r2_hidden(X1,k1_relat_1(X2))=>k11_relat_1(X2,X1)=k1_tarski(k1_funct_1(X2,X1))))), inference(assume_negation,[status(cth)],[t117_funct_1])).
% 0.14/0.38  fof(c_0_9, plain, ![X13, X14, X15]:((~r2_hidden(k4_tarski(X13,X14),X15)|r2_hidden(X14,k11_relat_1(X15,X13))|~v1_relat_1(X15))&(~r2_hidden(X14,k11_relat_1(X15,X13))|r2_hidden(k4_tarski(X13,X14),X15)|~v1_relat_1(X15))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).
% 0.14/0.38  fof(c_0_10, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&(r2_hidden(esk2_0,k1_relat_1(esk3_0))&k11_relat_1(esk3_0,esk2_0)!=k1_tarski(k1_funct_1(esk3_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.14/0.38  fof(c_0_11, plain, ![X10, X11]:((r2_hidden(esk1_2(X10,X11),X10)|(X10=k1_tarski(X11)|X10=k1_xboole_0))&(esk1_2(X10,X11)!=X11|(X10=k1_tarski(X11)|X10=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_zfmisc_1])])])])).
% 0.14/0.38  fof(c_0_12, plain, ![X4]:k2_tarski(X4,X4)=k1_tarski(X4), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.14/0.38  fof(c_0_13, plain, ![X5, X6]:k1_enumset1(X5,X5,X6)=k2_tarski(X5,X6), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.14/0.38  fof(c_0_14, plain, ![X7, X8, X9]:k2_enumset1(X7,X7,X8,X9)=k1_enumset1(X7,X8,X9), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.14/0.38  fof(c_0_15, plain, ![X18, X19, X20]:(((r2_hidden(X18,k1_relat_1(X20))|~r2_hidden(k4_tarski(X18,X19),X20)|(~v1_relat_1(X20)|~v1_funct_1(X20)))&(X19=k1_funct_1(X20,X18)|~r2_hidden(k4_tarski(X18,X19),X20)|(~v1_relat_1(X20)|~v1_funct_1(X20))))&(~r2_hidden(X18,k1_relat_1(X20))|X19!=k1_funct_1(X20,X18)|r2_hidden(k4_tarski(X18,X19),X20)|(~v1_relat_1(X20)|~v1_funct_1(X20)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.14/0.38  cnf(c_0_16, plain, (r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,k11_relat_1(X2,X3))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_17, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_18, plain, (r2_hidden(esk1_2(X1,X2),X1)|X1=k1_tarski(X2)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_19, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_20, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_21, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.38  cnf(c_0_22, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  cnf(c_0_23, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_24, negated_conjecture, (r2_hidden(k4_tarski(X1,X2),esk3_0)|~r2_hidden(X2,k11_relat_1(esk3_0,X1))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.14/0.38  cnf(c_0_25, plain, (X1=k1_xboole_0|X1=k2_enumset1(X2,X2,X2,X2)|r2_hidden(esk1_2(X1,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21])).
% 0.14/0.38  cnf(c_0_26, negated_conjecture, (k11_relat_1(esk3_0,esk2_0)!=k1_tarski(k1_funct_1(esk3_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_27, negated_conjecture, (X1=k1_funct_1(esk3_0,X2)|~r2_hidden(k4_tarski(X2,X1),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_17])])).
% 0.14/0.38  cnf(c_0_28, negated_conjecture, (k11_relat_1(esk3_0,X1)=k2_enumset1(X2,X2,X2,X2)|k11_relat_1(esk3_0,X1)=k1_xboole_0|r2_hidden(k4_tarski(X1,esk1_2(k11_relat_1(esk3_0,X1),X2)),esk3_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.14/0.38  cnf(c_0_29, negated_conjecture, (k11_relat_1(esk3_0,esk2_0)!=k2_enumset1(k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_19]), c_0_20]), c_0_21])).
% 0.14/0.38  cnf(c_0_30, negated_conjecture, (esk1_2(k11_relat_1(esk3_0,X1),X2)=k1_funct_1(esk3_0,X1)|k11_relat_1(esk3_0,X1)=k2_enumset1(X2,X2,X2,X2)|k11_relat_1(esk3_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.14/0.38  cnf(c_0_31, plain, (X1=k1_tarski(X2)|X1=k1_xboole_0|esk1_2(X1,X2)!=X2), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_32, negated_conjecture, (esk1_2(k11_relat_1(esk3_0,X1),k1_funct_1(esk3_0,esk2_0))=k1_funct_1(esk3_0,X1)|k11_relat_1(esk3_0,X1)=k1_xboole_0|k11_relat_1(esk3_0,X1)!=k11_relat_1(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.14/0.38  fof(c_0_33, plain, ![X16, X17]:((~r2_hidden(X16,k1_relat_1(X17))|k11_relat_1(X17,X16)!=k1_xboole_0|~v1_relat_1(X17))&(k11_relat_1(X17,X16)=k1_xboole_0|r2_hidden(X16,k1_relat_1(X17))|~v1_relat_1(X17))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t205_relat_1])])])).
% 0.14/0.38  cnf(c_0_34, plain, (X1=k1_xboole_0|X1=k2_enumset1(X2,X2,X2,X2)|esk1_2(X1,X2)!=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_19]), c_0_20]), c_0_21])).
% 0.14/0.38  cnf(c_0_35, negated_conjecture, (esk1_2(k11_relat_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0))=k1_funct_1(esk3_0,esk2_0)|k11_relat_1(esk3_0,esk2_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_32])).
% 0.14/0.38  cnf(c_0_36, plain, (~r2_hidden(X1,k1_relat_1(X2))|k11_relat_1(X2,X1)!=k1_xboole_0|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.14/0.38  cnf(c_0_37, negated_conjecture, (k11_relat_1(esk3_0,esk2_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_29])).
% 0.14/0.38  cnf(c_0_38, negated_conjecture, (r2_hidden(esk2_0,k1_relat_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_39, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_17]), c_0_38])]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 40
% 0.14/0.38  # Proof object clause steps            : 23
% 0.14/0.38  # Proof object formula steps           : 17
% 0.14/0.38  # Proof object conjectures             : 16
% 0.14/0.38  # Proof object clause conjectures      : 13
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 12
% 0.14/0.38  # Proof object initial formulas used   : 8
% 0.14/0.38  # Proof object generating inferences   : 8
% 0.14/0.38  # Proof object simplifying inferences  : 15
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 8
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 16
% 0.14/0.38  # Removed in clause preprocessing      : 3
% 0.14/0.38  # Initial clauses in saturation        : 13
% 0.14/0.38  # Processed clauses                    : 47
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 4
% 0.14/0.38  # ...remaining for further processing  : 43
% 0.14/0.38  # Other redundant clauses eliminated   : 2
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 0
% 0.14/0.38  # Backward-rewritten                   : 4
% 0.14/0.38  # Generated clauses                    : 40
% 0.14/0.38  # ...of the previous two non-trivial   : 34
% 0.14/0.38  # Contextual simplify-reflections      : 1
% 0.14/0.38  # Paramodulations                      : 36
% 0.14/0.38  # Factorizations                       : 1
% 0.14/0.38  # Equation resolutions                 : 3
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
% 0.14/0.38  # Current number of processed clauses  : 25
% 0.14/0.38  #    Positive orientable unit clauses  : 5
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 0
% 0.14/0.38  #    Non-unit-clauses                  : 20
% 0.14/0.38  # Current number of unprocessed clauses: 11
% 0.14/0.38  # ...number of literals in the above   : 42
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 20
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 41
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 22
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 5
% 0.14/0.38  # Unit Clause-clause subsumption calls : 10
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 1
% 0.14/0.38  # BW rewrite match successes           : 1
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 1767
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.031 s
% 0.14/0.38  # System time              : 0.002 s
% 0.14/0.38  # Total time               : 0.033 s
% 0.14/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
