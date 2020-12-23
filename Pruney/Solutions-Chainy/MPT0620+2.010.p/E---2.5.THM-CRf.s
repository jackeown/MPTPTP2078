%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:58 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 110 expanded)
%              Number of clauses        :   29 (  47 expanded)
%              Number of leaves         :    7 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :  162 ( 406 expanded)
%              Number of equality atoms :   83 ( 198 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   3 average)
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

fof(t41_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_tarski(X2)
        & X1 != k1_xboole_0
        & ! [X3] :
            ~ ( r2_hidden(X3,X1)
              & X3 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

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

fof(t65_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k1_relat_1(X1) = k1_xboole_0
      <=> k2_relat_1(X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( X1 != k1_xboole_0
       => ! [X2] :
          ? [X3] :
            ( v1_relat_1(X3)
            & v1_funct_1(X3)
            & k1_relat_1(X3) = X1
            & k2_relat_1(X3) = k1_tarski(X2) ) ) ),
    inference(assume_negation,[status(cth)],[t15_funct_1])).

fof(c_0_8,plain,(
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

fof(c_0_9,negated_conjecture,(
    ! [X28] :
      ( esk6_0 != k1_xboole_0
      & ( ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28)
        | k1_relat_1(X28) != esk6_0
        | k2_relat_1(X28) != k1_tarski(esk7_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).

fof(c_0_10,plain,(
    ! [X5] : k2_tarski(X5,X5) = k1_tarski(X5) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_11,plain,(
    ! [X6,X7] : k1_enumset1(X6,X6,X7) = k2_tarski(X6,X7) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_12,plain,(
    ! [X8,X9] :
      ( ( r2_hidden(esk1_2(X8,X9),X8)
        | X8 = k1_tarski(X9)
        | X8 = k1_xboole_0 )
      & ( esk1_2(X8,X9) != X9
        | X8 = k1_tarski(X9)
        | X8 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_zfmisc_1])])])])).

fof(c_0_13,plain,(
    ! [X22,X23,X25] :
      ( v1_relat_1(esk5_2(X22,X23))
      & v1_funct_1(esk5_2(X22,X23))
      & k1_relat_1(esk5_2(X22,X23)) = X22
      & ( ~ r2_hidden(X25,X22)
        | k1_funct_1(esk5_2(X22,X23),X25) = X23 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).

cnf(c_0_14,plain,
    ( X1 = k1_funct_1(X2,esk2_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,negated_conjecture,
    ( ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_relat_1(X1) != esk6_0
    | k2_relat_1(X1) != k1_tarski(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | X1 = k1_tarski(X2)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k1_funct_1(esk5_2(X2,X3),X1) = X3
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k1_funct_1(X1,esk2_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( v1_funct_1(esk5_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( v1_relat_1(esk5_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,plain,
    ( r2_hidden(esk2_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( k1_relat_1(esk5_2(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,negated_conjecture,
    ( k1_relat_1(X1) != esk6_0
    | k2_relat_1(X1) != k1_enumset1(esk7_0,esk7_0,esk7_0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

cnf(c_0_27,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_enumset1(X2,X2,X2)
    | r2_hidden(esk1_2(X1,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_17]),c_0_18])).

cnf(c_0_28,plain,
    ( X1 = X2
    | ~ r2_hidden(esk2_3(esk5_2(X3,X2),k2_relat_1(esk5_2(X3,X2)),X1),X3)
    | ~ r2_hidden(X1,k2_relat_1(esk5_2(X3,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])])).

cnf(c_0_29,plain,
    ( r2_hidden(esk2_3(esk5_2(X1,X2),k2_relat_1(esk5_2(X1,X2)),X3),X1)
    | ~ r2_hidden(X3,k2_relat_1(esk5_2(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_22]),c_0_23])])).

cnf(c_0_30,negated_conjecture,
    ( k2_relat_1(X1) = k1_xboole_0
    | r2_hidden(esk1_2(k2_relat_1(X1),esk7_0),k2_relat_1(X1))
    | k1_relat_1(X1) != esk6_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27])])).

cnf(c_0_31,plain,
    ( X1 = k1_tarski(X2)
    | X1 = k1_xboole_0
    | esk1_2(X1,X2) != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_32,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_relat_1(esk5_2(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( k2_relat_1(esk5_2(esk6_0,X1)) = k1_xboole_0
    | r2_hidden(esk1_2(k2_relat_1(esk5_2(esk6_0,X1)),esk7_0),k2_relat_1(esk5_2(esk6_0,X1))) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_25]),c_0_22]),c_0_23])])])).

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
        | k2_relat_1(X11) = k1_xboole_0
        | ~ v1_relat_1(X11) )
      & ( k2_relat_1(X11) != k1_xboole_0
        | k1_relat_1(X11) = k1_xboole_0
        | ~ v1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).

cnf(c_0_37,negated_conjecture,
    ( k1_enumset1(esk7_0,esk7_0,esk7_0) = k2_relat_1(esk5_2(esk6_0,esk7_0))
    | k2_relat_1(esk5_2(esk6_0,esk7_0)) = k1_xboole_0 ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35])])).

cnf(c_0_38,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( k2_relat_1(esk5_2(esk6_0,esk7_0)) = k1_xboole_0
    | k2_relat_1(X1) != k2_relat_1(esk5_2(esk6_0,esk7_0))
    | k1_relat_1(X1) != esk6_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_37])).

cnf(c_0_40,plain,
    ( k1_xboole_0 = X1
    | k2_relat_1(esk5_2(X1,X2)) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_38]),c_0_23])])).

cnf(c_0_41,negated_conjecture,
    ( k2_relat_1(esk5_2(esk6_0,esk7_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_39]),c_0_25]),c_0_22]),c_0_23])])).

cnf(c_0_42,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:49:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.57  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.19/0.57  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.19/0.57  #
% 0.19/0.57  # Preprocessing time       : 0.027 s
% 0.19/0.57  # Presaturation interreduction done
% 0.19/0.57  
% 0.19/0.57  # Proof found!
% 0.19/0.57  # SZS status Theorem
% 0.19/0.57  # SZS output start CNFRefutation
% 0.19/0.57  fof(t15_funct_1, conjecture, ![X1]:(X1!=k1_xboole_0=>![X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&k2_relat_1(X3)=k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_funct_1)).
% 0.19/0.57  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 0.19/0.57  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.57  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.57  fof(t41_zfmisc_1, axiom, ![X1, X2]:~(((X1!=k1_tarski(X2)&X1!=k1_xboole_0)&![X3]:~((r2_hidden(X3,X1)&X3!=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 0.19/0.57  fof(s3_funct_1__e2_24__funct_1, axiom, ![X1, X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&![X4]:(r2_hidden(X4,X1)=>k1_funct_1(X3,X4)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 0.19/0.57  fof(t65_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k1_relat_1(X1)=k1_xboole_0<=>k2_relat_1(X1)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 0.19/0.57  fof(c_0_7, negated_conjecture, ~(![X1]:(X1!=k1_xboole_0=>![X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&k2_relat_1(X3)=k1_tarski(X2)))), inference(assume_negation,[status(cth)],[t15_funct_1])).
% 0.19/0.57  fof(c_0_8, plain, ![X12, X13, X14, X16, X17, X18, X20]:((((r2_hidden(esk2_3(X12,X13,X14),k1_relat_1(X12))|~r2_hidden(X14,X13)|X13!=k2_relat_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12)))&(X14=k1_funct_1(X12,esk2_3(X12,X13,X14))|~r2_hidden(X14,X13)|X13!=k2_relat_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12))))&(~r2_hidden(X17,k1_relat_1(X12))|X16!=k1_funct_1(X12,X17)|r2_hidden(X16,X13)|X13!=k2_relat_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12))))&((~r2_hidden(esk3_2(X12,X18),X18)|(~r2_hidden(X20,k1_relat_1(X12))|esk3_2(X12,X18)!=k1_funct_1(X12,X20))|X18=k2_relat_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12)))&((r2_hidden(esk4_2(X12,X18),k1_relat_1(X12))|r2_hidden(esk3_2(X12,X18),X18)|X18=k2_relat_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12)))&(esk3_2(X12,X18)=k1_funct_1(X12,esk4_2(X12,X18))|r2_hidden(esk3_2(X12,X18),X18)|X18=k2_relat_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.19/0.57  fof(c_0_9, negated_conjecture, ![X28]:(esk6_0!=k1_xboole_0&(~v1_relat_1(X28)|~v1_funct_1(X28)|k1_relat_1(X28)!=esk6_0|k2_relat_1(X28)!=k1_tarski(esk7_0))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).
% 0.19/0.57  fof(c_0_10, plain, ![X5]:k2_tarski(X5,X5)=k1_tarski(X5), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.57  fof(c_0_11, plain, ![X6, X7]:k1_enumset1(X6,X6,X7)=k2_tarski(X6,X7), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.57  fof(c_0_12, plain, ![X8, X9]:((r2_hidden(esk1_2(X8,X9),X8)|(X8=k1_tarski(X9)|X8=k1_xboole_0))&(esk1_2(X8,X9)!=X9|(X8=k1_tarski(X9)|X8=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_zfmisc_1])])])])).
% 0.19/0.57  fof(c_0_13, plain, ![X22, X23, X25]:(((v1_relat_1(esk5_2(X22,X23))&v1_funct_1(esk5_2(X22,X23)))&k1_relat_1(esk5_2(X22,X23))=X22)&(~r2_hidden(X25,X22)|k1_funct_1(esk5_2(X22,X23),X25)=X23)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).
% 0.19/0.57  cnf(c_0_14, plain, (X1=k1_funct_1(X2,esk2_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.57  cnf(c_0_15, plain, (r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.57  cnf(c_0_16, negated_conjecture, (~v1_relat_1(X1)|~v1_funct_1(X1)|k1_relat_1(X1)!=esk6_0|k2_relat_1(X1)!=k1_tarski(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.57  cnf(c_0_17, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.57  cnf(c_0_18, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.57  cnf(c_0_19, plain, (r2_hidden(esk1_2(X1,X2),X1)|X1=k1_tarski(X2)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.57  cnf(c_0_20, plain, (k1_funct_1(esk5_2(X2,X3),X1)=X3|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.57  cnf(c_0_21, plain, (k1_funct_1(X1,esk2_3(X1,k2_relat_1(X1),X2))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_14])).
% 0.19/0.57  cnf(c_0_22, plain, (v1_funct_1(esk5_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.57  cnf(c_0_23, plain, (v1_relat_1(esk5_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.57  cnf(c_0_24, plain, (r2_hidden(esk2_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_15])).
% 0.19/0.57  cnf(c_0_25, plain, (k1_relat_1(esk5_2(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.57  cnf(c_0_26, negated_conjecture, (k1_relat_1(X1)!=esk6_0|k2_relat_1(X1)!=k1_enumset1(esk7_0,esk7_0,esk7_0)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_18])).
% 0.19/0.57  cnf(c_0_27, plain, (X1=k1_xboole_0|X1=k1_enumset1(X2,X2,X2)|r2_hidden(esk1_2(X1,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_17]), c_0_18])).
% 0.19/0.57  cnf(c_0_28, plain, (X1=X2|~r2_hidden(esk2_3(esk5_2(X3,X2),k2_relat_1(esk5_2(X3,X2)),X1),X3)|~r2_hidden(X1,k2_relat_1(esk5_2(X3,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23])])).
% 0.19/0.57  cnf(c_0_29, plain, (r2_hidden(esk2_3(esk5_2(X1,X2),k2_relat_1(esk5_2(X1,X2)),X3),X1)|~r2_hidden(X3,k2_relat_1(esk5_2(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_22]), c_0_23])])).
% 0.19/0.57  cnf(c_0_30, negated_conjecture, (k2_relat_1(X1)=k1_xboole_0|r2_hidden(esk1_2(k2_relat_1(X1),esk7_0),k2_relat_1(X1))|k1_relat_1(X1)!=esk6_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27])])).
% 0.19/0.57  cnf(c_0_31, plain, (X1=k1_tarski(X2)|X1=k1_xboole_0|esk1_2(X1,X2)!=X2), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.57  cnf(c_0_32, plain, (X1=X2|~r2_hidden(X1,k2_relat_1(esk5_2(X3,X2)))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.57  cnf(c_0_33, negated_conjecture, (k2_relat_1(esk5_2(esk6_0,X1))=k1_xboole_0|r2_hidden(esk1_2(k2_relat_1(esk5_2(esk6_0,X1)),esk7_0),k2_relat_1(esk5_2(esk6_0,X1)))), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_25]), c_0_22]), c_0_23])])])).
% 0.19/0.57  cnf(c_0_34, plain, (X1=k1_xboole_0|X1=k1_enumset1(X2,X2,X2)|esk1_2(X1,X2)!=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_17]), c_0_18])).
% 0.19/0.57  cnf(c_0_35, negated_conjecture, (esk1_2(k2_relat_1(esk5_2(esk6_0,X1)),esk7_0)=X1|k2_relat_1(esk5_2(esk6_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.57  fof(c_0_36, plain, ![X11]:((k1_relat_1(X11)!=k1_xboole_0|k2_relat_1(X11)=k1_xboole_0|~v1_relat_1(X11))&(k2_relat_1(X11)!=k1_xboole_0|k1_relat_1(X11)=k1_xboole_0|~v1_relat_1(X11))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).
% 0.19/0.57  cnf(c_0_37, negated_conjecture, (k1_enumset1(esk7_0,esk7_0,esk7_0)=k2_relat_1(esk5_2(esk6_0,esk7_0))|k2_relat_1(esk5_2(esk6_0,esk7_0))=k1_xboole_0), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35])])).
% 0.19/0.57  cnf(c_0_38, plain, (k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.57  cnf(c_0_39, negated_conjecture, (k2_relat_1(esk5_2(esk6_0,esk7_0))=k1_xboole_0|k2_relat_1(X1)!=k2_relat_1(esk5_2(esk6_0,esk7_0))|k1_relat_1(X1)!=esk6_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_26, c_0_37])).
% 0.19/0.57  cnf(c_0_40, plain, (k1_xboole_0=X1|k2_relat_1(esk5_2(X1,X2))!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_38]), c_0_23])])).
% 0.19/0.57  cnf(c_0_41, negated_conjecture, (k2_relat_1(esk5_2(esk6_0,esk7_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_39]), c_0_25]), c_0_22]), c_0_23])])).
% 0.19/0.57  cnf(c_0_42, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.57  cnf(c_0_43, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42]), ['proof']).
% 0.19/0.57  # SZS output end CNFRefutation
% 0.19/0.57  # Proof object total steps             : 44
% 0.19/0.57  # Proof object clause steps            : 29
% 0.19/0.57  # Proof object formula steps           : 15
% 0.19/0.57  # Proof object conjectures             : 13
% 0.19/0.57  # Proof object clause conjectures      : 10
% 0.19/0.57  # Proof object formula conjectures     : 3
% 0.19/0.57  # Proof object initial clauses used    : 13
% 0.19/0.57  # Proof object initial formulas used   : 7
% 0.19/0.57  # Proof object generating inferences   : 11
% 0.19/0.57  # Proof object simplifying inferences  : 27
% 0.19/0.57  # Training examples: 0 positive, 0 negative
% 0.19/0.57  # Parsed axioms                        : 7
% 0.19/0.57  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.57  # Initial clauses                      : 18
% 0.19/0.57  # Removed in clause preprocessing      : 2
% 0.19/0.57  # Initial clauses in saturation        : 16
% 0.19/0.57  # Processed clauses                    : 328
% 0.19/0.57  # ...of these trivial                  : 1
% 0.19/0.57  # ...subsumed                          : 144
% 0.19/0.57  # ...remaining for further processing  : 183
% 0.19/0.57  # Other redundant clauses eliminated   : 528
% 0.19/0.57  # Clauses deleted for lack of memory   : 0
% 0.19/0.57  # Backward-subsumed                    : 56
% 0.19/0.57  # Backward-rewritten                   : 2
% 0.19/0.57  # Generated clauses                    : 9819
% 0.19/0.57  # ...of the previous two non-trivial   : 8888
% 0.19/0.57  # Contextual simplify-reflections      : 12
% 0.19/0.57  # Paramodulations                      : 9239
% 0.19/0.57  # Factorizations                       : 49
% 0.19/0.57  # Equation resolutions                 : 532
% 0.19/0.57  # Propositional unsat checks           : 0
% 0.19/0.57  #    Propositional check models        : 0
% 0.19/0.57  #    Propositional check unsatisfiable : 0
% 0.19/0.57  #    Propositional clauses             : 0
% 0.19/0.57  #    Propositional clauses after purity: 0
% 0.19/0.57  #    Propositional unsat core size     : 0
% 0.19/0.57  #    Propositional preprocessing time  : 0.000
% 0.19/0.57  #    Propositional encoding time       : 0.000
% 0.19/0.57  #    Propositional solver time         : 0.000
% 0.19/0.57  #    Success case prop preproc time    : 0.000
% 0.19/0.57  #    Success case prop encoding time   : 0.000
% 0.19/0.57  #    Success case prop solver time     : 0.000
% 0.19/0.57  # Current number of processed clauses  : 106
% 0.19/0.57  #    Positive orientable unit clauses  : 11
% 0.19/0.57  #    Positive unorientable unit clauses: 0
% 0.19/0.57  #    Negative unit clauses             : 1
% 0.19/0.57  #    Non-unit-clauses                  : 94
% 0.19/0.57  # Current number of unprocessed clauses: 8215
% 0.19/0.57  # ...number of literals in the above   : 52107
% 0.19/0.57  # Current number of archived formulas  : 0
% 0.19/0.57  # Current number of archived clauses   : 76
% 0.19/0.57  # Clause-clause subsumption calls (NU) : 4855
% 0.19/0.57  # Rec. Clause-clause subsumption calls : 1520
% 0.19/0.57  # Non-unit clause-clause subsumptions  : 198
% 0.19/0.57  # Unit Clause-clause subsumption calls : 39
% 0.19/0.57  # Rewrite failures with RHS unbound    : 0
% 0.19/0.57  # BW rewrite match attempts            : 61
% 0.19/0.57  # BW rewrite match successes           : 6
% 0.19/0.57  # Condensation attempts                : 0
% 0.19/0.57  # Condensation successes               : 0
% 0.19/0.57  # Termbank termtop insertions          : 208921
% 0.19/0.57  
% 0.19/0.57  # -------------------------------------------------
% 0.19/0.57  # User time                : 0.221 s
% 0.19/0.57  # System time              : 0.009 s
% 0.19/0.57  # Total time               : 0.230 s
% 0.19/0.57  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
