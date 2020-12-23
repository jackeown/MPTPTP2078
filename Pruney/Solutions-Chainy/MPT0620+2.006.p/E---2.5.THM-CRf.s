%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:58 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 110 expanded)
%              Number of clauses        :   28 (  46 expanded)
%              Number of leaves         :    8 (  31 expanded)
%              Depth                    :   11
%              Number of atoms          :  157 ( 401 expanded)
%              Number of equality atoms :   82 ( 197 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t15_funct_1,conjecture,(
    ! [X1] :
      ( X1 != k1_xboole_0
     => ! [X2] :
        ? [X3] :
          ( v1_relat_1(X3)
          & v1_funct_1(X3)
          & k1_relat_1(X3) = X1
          & k2_relat_1(X3) = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).

fof(d5_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( X2 = k2_relat_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                  & X3 = k1_funct_1(X1,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(l44_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_tarski(X2)
        & X1 != k1_xboole_0
        & ! [X3] :
            ~ ( r2_hidden(X3,X1)
              & X3 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(s3_funct_1__e2_24__funct_1,axiom,(
    ! [X1,X2] :
    ? [X3] :
      ( v1_relat_1(X3)
      & v1_funct_1(X3)
      & k1_relat_1(X3) = X1
      & ! [X4] :
          ( r2_hidden(X4,X1)
         => k1_funct_1(X3,X4) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( X1 != k1_xboole_0
       => ! [X2] :
          ? [X3] :
            ( v1_relat_1(X3)
            & v1_funct_1(X3)
            & k1_relat_1(X3) = X1
            & k2_relat_1(X3) = k1_tarski(X2) ) ) ),
    inference(assume_negation,[status(cth)],[t15_funct_1])).

fof(c_0_9,plain,(
    ! [X12,X13,X14,X16,X17,X18,X20] :
      ( ( r2_hidden(esk2_3(X12,X13,X14),k1_relat_1(X12))
        | ~ r2_hidden(X14,X13)
        | X13 != k2_relat_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( X14 = k1_funct_1(X12,esk2_3(X12,X13,X14))
        | ~ r2_hidden(X14,X13)
        | X13 != k2_relat_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( ~ r2_hidden(X17,k1_relat_1(X12))
        | X16 != k1_funct_1(X12,X17)
        | r2_hidden(X16,X13)
        | X13 != k2_relat_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( ~ r2_hidden(esk3_2(X12,X18),X18)
        | ~ r2_hidden(X20,k1_relat_1(X12))
        | esk3_2(X12,X18) != k1_funct_1(X12,X20)
        | X18 = k2_relat_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( r2_hidden(esk4_2(X12,X18),k1_relat_1(X12))
        | r2_hidden(esk3_2(X12,X18),X18)
        | X18 = k2_relat_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( esk3_2(X12,X18) = k1_funct_1(X12,esk4_2(X12,X18))
        | r2_hidden(esk3_2(X12,X18),X18)
        | X18 = k2_relat_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_10,negated_conjecture,(
    ! [X28] :
      ( esk6_0 != k1_xboole_0
      & ( ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28)
        | k1_relat_1(X28) != esk6_0
        | k2_relat_1(X28) != k1_tarski(esk7_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).

fof(c_0_11,plain,(
    ! [X5] : k2_tarski(X5,X5) = k1_tarski(X5) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_12,plain,(
    ! [X6,X7] : k1_enumset1(X6,X6,X7) = k2_tarski(X6,X7) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,plain,(
    ! [X8,X9] :
      ( ( r2_hidden(esk1_2(X8,X9),X8)
        | X8 = k1_tarski(X9)
        | X8 = k1_xboole_0 )
      & ( esk1_2(X8,X9) != X9
        | X8 = k1_tarski(X9)
        | X8 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_zfmisc_1])])])])).

cnf(c_0_14,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_15,plain,(
    ! [X22,X23,X25] :
      ( v1_relat_1(esk5_2(X22,X23))
      & v1_funct_1(esk5_2(X22,X23))
      & k1_relat_1(esk5_2(X22,X23)) = X22
      & ( ~ r2_hidden(X25,X22)
        | k1_funct_1(esk5_2(X22,X23),X25) = X23 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).

cnf(c_0_16,negated_conjecture,
    ( ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_relat_1(X1) != esk6_0
    | k2_relat_1(X1) != k1_tarski(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | X1 = k1_tarski(X2)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( X1 = k1_funct_1(X2,esk2_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,plain,
    ( r2_hidden(esk2_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k1_relat_1(esk5_2(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( v1_funct_1(esk5_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( v1_relat_1(esk5_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( k1_relat_1(X1) != esk6_0
    | k2_relat_1(X1) != k1_enumset1(esk7_0,esk7_0,esk7_0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

cnf(c_0_26,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_enumset1(X2,X2,X2)
    | r2_hidden(esk1_2(X1,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_17]),c_0_18])).

cnf(c_0_27,plain,
    ( k1_funct_1(esk5_2(X2,X3),X1) = X3
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_28,plain,
    ( k1_funct_1(X1,esk2_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( r2_hidden(esk2_3(esk5_2(X1,X2),k2_relat_1(esk5_2(X1,X2)),X3),X1)
    | ~ r2_hidden(X3,k2_relat_1(esk5_2(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24])])).

cnf(c_0_30,negated_conjecture,
    ( k2_relat_1(X1) = k1_xboole_0
    | r2_hidden(esk1_2(k2_relat_1(X1),esk7_0),k2_relat_1(X1))
    | k1_relat_1(X1) != esk6_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26])])).

cnf(c_0_31,plain,
    ( X1 = k1_tarski(X2)
    | X1 = k1_xboole_0
    | esk1_2(X1,X2) != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_32,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_relat_1(esk5_2(X3,X2))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_23]),c_0_24])]),c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( k2_relat_1(esk5_2(esk6_0,X1)) = k1_xboole_0
    | r2_hidden(esk1_2(k2_relat_1(esk5_2(esk6_0,X1)),esk7_0),k2_relat_1(esk5_2(esk6_0,X1))) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_22]),c_0_23]),c_0_24])])])).

cnf(c_0_34,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_enumset1(X2,X2,X2)
    | esk1_2(X1,X2) != X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_17]),c_0_18])).

cnf(c_0_35,negated_conjecture,
    ( esk1_2(k2_relat_1(esk5_2(esk6_0,X1)),esk7_0) = X1
    | k2_relat_1(esk5_2(esk6_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_36,plain,(
    ! [X11] :
      ( ( k1_relat_1(X11) != k1_xboole_0
        | X11 = k1_xboole_0
        | ~ v1_relat_1(X11) )
      & ( k2_relat_1(X11) != k1_xboole_0
        | X11 = k1_xboole_0
        | ~ v1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

cnf(c_0_37,negated_conjecture,
    ( k2_relat_1(esk5_2(esk6_0,esk7_0)) = k1_enumset1(esk7_0,esk7_0,esk7_0)
    | k2_relat_1(esk5_2(esk6_0,esk7_0)) = k1_xboole_0 ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35])])).

cnf(c_0_38,plain,
    ( X1 = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( k2_relat_1(esk5_2(esk6_0,esk7_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_37]),c_0_22]),c_0_23]),c_0_24])])).

cnf(c_0_40,negated_conjecture,
    ( esk5_2(esk6_0,esk7_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_24])])).

cnf(c_0_41,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_42,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_40]),c_0_41]),c_0_42]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:15:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.48  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.20/0.48  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.20/0.48  #
% 0.20/0.48  # Preprocessing time       : 0.027 s
% 0.20/0.48  # Presaturation interreduction done
% 0.20/0.48  
% 0.20/0.48  # Proof found!
% 0.20/0.48  # SZS status Theorem
% 0.20/0.48  # SZS output start CNFRefutation
% 0.20/0.48  fof(t15_funct_1, conjecture, ![X1]:(X1!=k1_xboole_0=>![X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&k2_relat_1(X3)=k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_funct_1)).
% 0.20/0.48  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 0.20/0.48  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.48  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.48  fof(l44_zfmisc_1, axiom, ![X1, X2]:~(((X1!=k1_tarski(X2)&X1!=k1_xboole_0)&![X3]:~((r2_hidden(X3,X1)&X3!=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l44_zfmisc_1)).
% 0.20/0.48  fof(s3_funct_1__e2_24__funct_1, axiom, ![X1, X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&![X4]:(r2_hidden(X4,X1)=>k1_funct_1(X3,X4)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 0.20/0.48  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 0.20/0.48  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.20/0.48  fof(c_0_8, negated_conjecture, ~(![X1]:(X1!=k1_xboole_0=>![X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&k2_relat_1(X3)=k1_tarski(X2)))), inference(assume_negation,[status(cth)],[t15_funct_1])).
% 0.20/0.48  fof(c_0_9, plain, ![X12, X13, X14, X16, X17, X18, X20]:((((r2_hidden(esk2_3(X12,X13,X14),k1_relat_1(X12))|~r2_hidden(X14,X13)|X13!=k2_relat_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12)))&(X14=k1_funct_1(X12,esk2_3(X12,X13,X14))|~r2_hidden(X14,X13)|X13!=k2_relat_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12))))&(~r2_hidden(X17,k1_relat_1(X12))|X16!=k1_funct_1(X12,X17)|r2_hidden(X16,X13)|X13!=k2_relat_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12))))&((~r2_hidden(esk3_2(X12,X18),X18)|(~r2_hidden(X20,k1_relat_1(X12))|esk3_2(X12,X18)!=k1_funct_1(X12,X20))|X18=k2_relat_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12)))&((r2_hidden(esk4_2(X12,X18),k1_relat_1(X12))|r2_hidden(esk3_2(X12,X18),X18)|X18=k2_relat_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12)))&(esk3_2(X12,X18)=k1_funct_1(X12,esk4_2(X12,X18))|r2_hidden(esk3_2(X12,X18),X18)|X18=k2_relat_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.20/0.48  fof(c_0_10, negated_conjecture, ![X28]:(esk6_0!=k1_xboole_0&(~v1_relat_1(X28)|~v1_funct_1(X28)|k1_relat_1(X28)!=esk6_0|k2_relat_1(X28)!=k1_tarski(esk7_0))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).
% 0.20/0.48  fof(c_0_11, plain, ![X5]:k2_tarski(X5,X5)=k1_tarski(X5), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.48  fof(c_0_12, plain, ![X6, X7]:k1_enumset1(X6,X6,X7)=k2_tarski(X6,X7), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.48  fof(c_0_13, plain, ![X8, X9]:((r2_hidden(esk1_2(X8,X9),X8)|(X8=k1_tarski(X9)|X8=k1_xboole_0))&(esk1_2(X8,X9)!=X9|(X8=k1_tarski(X9)|X8=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_zfmisc_1])])])])).
% 0.20/0.48  cnf(c_0_14, plain, (r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.48  fof(c_0_15, plain, ![X22, X23, X25]:(((v1_relat_1(esk5_2(X22,X23))&v1_funct_1(esk5_2(X22,X23)))&k1_relat_1(esk5_2(X22,X23))=X22)&(~r2_hidden(X25,X22)|k1_funct_1(esk5_2(X22,X23),X25)=X23)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).
% 0.20/0.48  cnf(c_0_16, negated_conjecture, (~v1_relat_1(X1)|~v1_funct_1(X1)|k1_relat_1(X1)!=esk6_0|k2_relat_1(X1)!=k1_tarski(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.48  cnf(c_0_17, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.48  cnf(c_0_18, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.48  cnf(c_0_19, plain, (r2_hidden(esk1_2(X1,X2),X1)|X1=k1_tarski(X2)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.48  cnf(c_0_20, plain, (X1=k1_funct_1(X2,esk2_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.48  cnf(c_0_21, plain, (r2_hidden(esk2_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_14])).
% 0.20/0.48  cnf(c_0_22, plain, (k1_relat_1(esk5_2(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.48  cnf(c_0_23, plain, (v1_funct_1(esk5_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.48  cnf(c_0_24, plain, (v1_relat_1(esk5_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.48  cnf(c_0_25, negated_conjecture, (k1_relat_1(X1)!=esk6_0|k2_relat_1(X1)!=k1_enumset1(esk7_0,esk7_0,esk7_0)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_18])).
% 0.20/0.48  cnf(c_0_26, plain, (X1=k1_xboole_0|X1=k1_enumset1(X2,X2,X2)|r2_hidden(esk1_2(X1,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_17]), c_0_18])).
% 0.20/0.48  cnf(c_0_27, plain, (k1_funct_1(esk5_2(X2,X3),X1)=X3|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.48  cnf(c_0_28, plain, (k1_funct_1(X1,esk2_3(X1,k2_relat_1(X1),X2))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_20])).
% 0.20/0.48  cnf(c_0_29, plain, (r2_hidden(esk2_3(esk5_2(X1,X2),k2_relat_1(esk5_2(X1,X2)),X3),X1)|~r2_hidden(X3,k2_relat_1(esk5_2(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24])])).
% 0.20/0.48  cnf(c_0_30, negated_conjecture, (k2_relat_1(X1)=k1_xboole_0|r2_hidden(esk1_2(k2_relat_1(X1),esk7_0),k2_relat_1(X1))|k1_relat_1(X1)!=esk6_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26])])).
% 0.20/0.48  cnf(c_0_31, plain, (X1=k1_tarski(X2)|X1=k1_xboole_0|esk1_2(X1,X2)!=X2), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.48  cnf(c_0_32, plain, (X1=X2|~r2_hidden(X1,k2_relat_1(esk5_2(X3,X2)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_23]), c_0_24])]), c_0_29])).
% 0.20/0.48  cnf(c_0_33, negated_conjecture, (k2_relat_1(esk5_2(esk6_0,X1))=k1_xboole_0|r2_hidden(esk1_2(k2_relat_1(esk5_2(esk6_0,X1)),esk7_0),k2_relat_1(esk5_2(esk6_0,X1)))), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_22]), c_0_23]), c_0_24])])])).
% 0.20/0.48  cnf(c_0_34, plain, (X1=k1_xboole_0|X1=k1_enumset1(X2,X2,X2)|esk1_2(X1,X2)!=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_17]), c_0_18])).
% 0.20/0.48  cnf(c_0_35, negated_conjecture, (esk1_2(k2_relat_1(esk5_2(esk6_0,X1)),esk7_0)=X1|k2_relat_1(esk5_2(esk6_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.48  fof(c_0_36, plain, ![X11]:((k1_relat_1(X11)!=k1_xboole_0|X11=k1_xboole_0|~v1_relat_1(X11))&(k2_relat_1(X11)!=k1_xboole_0|X11=k1_xboole_0|~v1_relat_1(X11))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.20/0.48  cnf(c_0_37, negated_conjecture, (k2_relat_1(esk5_2(esk6_0,esk7_0))=k1_enumset1(esk7_0,esk7_0,esk7_0)|k2_relat_1(esk5_2(esk6_0,esk7_0))=k1_xboole_0), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35])])).
% 0.20/0.48  cnf(c_0_38, plain, (X1=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.48  cnf(c_0_39, negated_conjecture, (k2_relat_1(esk5_2(esk6_0,esk7_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_37]), c_0_22]), c_0_23]), c_0_24])])).
% 0.20/0.48  cnf(c_0_40, negated_conjecture, (esk5_2(esk6_0,esk7_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_24])])).
% 0.20/0.48  cnf(c_0_41, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.20/0.48  cnf(c_0_42, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.48  cnf(c_0_43, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_40]), c_0_41]), c_0_42]), ['proof']).
% 0.20/0.48  # SZS output end CNFRefutation
% 0.20/0.48  # Proof object total steps             : 44
% 0.20/0.48  # Proof object clause steps            : 28
% 0.20/0.48  # Proof object formula steps           : 16
% 0.20/0.48  # Proof object conjectures             : 13
% 0.20/0.48  # Proof object clause conjectures      : 10
% 0.20/0.48  # Proof object formula conjectures     : 3
% 0.20/0.48  # Proof object initial clauses used    : 14
% 0.20/0.48  # Proof object initial formulas used   : 8
% 0.20/0.48  # Proof object generating inferences   : 9
% 0.20/0.48  # Proof object simplifying inferences  : 29
% 0.20/0.48  # Training examples: 0 positive, 0 negative
% 0.20/0.48  # Parsed axioms                        : 8
% 0.20/0.48  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.48  # Initial clauses                      : 20
% 0.20/0.48  # Removed in clause preprocessing      : 2
% 0.20/0.48  # Initial clauses in saturation        : 18
% 0.20/0.48  # Processed clauses                    : 309
% 0.20/0.48  # ...of these trivial                  : 0
% 0.20/0.48  # ...subsumed                          : 171
% 0.20/0.48  # ...remaining for further processing  : 138
% 0.20/0.48  # Other redundant clauses eliminated   : 112
% 0.20/0.48  # Clauses deleted for lack of memory   : 0
% 0.20/0.48  # Backward-subsumed                    : 15
% 0.20/0.48  # Backward-rewritten                   : 2
% 0.20/0.48  # Generated clauses                    : 4206
% 0.20/0.48  # ...of the previous two non-trivial   : 3796
% 0.20/0.48  # Contextual simplify-reflections      : 7
% 0.20/0.48  # Paramodulations                      : 4058
% 0.20/0.48  # Factorizations                       : 35
% 0.20/0.48  # Equation resolutions                 : 113
% 0.20/0.48  # Propositional unsat checks           : 0
% 0.20/0.48  #    Propositional check models        : 0
% 0.20/0.48  #    Propositional check unsatisfiable : 0
% 0.20/0.48  #    Propositional clauses             : 0
% 0.20/0.48  #    Propositional clauses after purity: 0
% 0.20/0.48  #    Propositional unsat core size     : 0
% 0.20/0.48  #    Propositional preprocessing time  : 0.000
% 0.20/0.48  #    Propositional encoding time       : 0.000
% 0.20/0.48  #    Propositional solver time         : 0.000
% 0.20/0.48  #    Success case prop preproc time    : 0.000
% 0.20/0.48  #    Success case prop encoding time   : 0.000
% 0.20/0.48  #    Success case prop solver time     : 0.000
% 0.20/0.48  # Current number of processed clauses  : 99
% 0.20/0.48  #    Positive orientable unit clauses  : 16
% 0.20/0.48  #    Positive unorientable unit clauses: 0
% 0.20/0.48  #    Negative unit clauses             : 2
% 0.20/0.48  #    Non-unit-clauses                  : 81
% 0.20/0.48  # Current number of unprocessed clauses: 3432
% 0.20/0.48  # ...number of literals in the above   : 21783
% 0.20/0.48  # Current number of archived formulas  : 0
% 0.20/0.48  # Current number of archived clauses   : 38
% 0.20/0.48  # Clause-clause subsumption calls (NU) : 3146
% 0.20/0.48  # Rec. Clause-clause subsumption calls : 990
% 0.20/0.48  # Non-unit clause-clause subsumptions  : 185
% 0.20/0.48  # Unit Clause-clause subsumption calls : 78
% 0.20/0.48  # Rewrite failures with RHS unbound    : 0
% 0.20/0.48  # BW rewrite match attempts            : 82
% 0.20/0.48  # BW rewrite match successes           : 6
% 0.20/0.48  # Condensation attempts                : 0
% 0.20/0.48  # Condensation successes               : 0
% 0.20/0.48  # Termbank termtop insertions          : 102708
% 0.20/0.48  
% 0.20/0.48  # -------------------------------------------------
% 0.20/0.48  # User time                : 0.136 s
% 0.20/0.48  # System time              : 0.004 s
% 0.20/0.48  # Total time               : 0.139 s
% 0.20/0.48  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
