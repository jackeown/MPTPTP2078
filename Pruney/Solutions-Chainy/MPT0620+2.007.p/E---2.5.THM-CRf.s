%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:58 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   41 (  98 expanded)
%              Number of clauses        :   28 (  43 expanded)
%              Number of leaves         :    6 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :  160 ( 395 expanded)
%              Number of equality atoms :   80 ( 186 expanded)
%              Maximal formula depth    :   18 (   5 average)
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

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(l44_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_tarski(X2)
        & X1 != k1_xboole_0
        & ! [X3] :
            ~ ( r2_hidden(X3,X1)
              & X3 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).

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

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( X1 != k1_xboole_0
       => ! [X2] :
          ? [X3] :
            ( v1_relat_1(X3)
            & v1_funct_1(X3)
            & k1_relat_1(X3) = X1
            & k2_relat_1(X3) = k1_tarski(X2) ) ) ),
    inference(assume_negation,[status(cth)],[t15_funct_1])).

fof(c_0_7,negated_conjecture,(
    ! [X26] :
      ( esk6_0 != k1_xboole_0
      & ( ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26)
        | k1_relat_1(X26) != esk6_0
        | k2_relat_1(X26) != k1_tarski(esk7_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).

fof(c_0_8,plain,(
    ! [X5] : k2_tarski(X5,X5) = k1_tarski(X5) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_9,plain,(
    ! [X6,X7] :
      ( ( r2_hidden(esk1_2(X6,X7),X6)
        | X6 = k1_tarski(X7)
        | X6 = k1_xboole_0 )
      & ( esk1_2(X6,X7) != X7
        | X6 = k1_tarski(X7)
        | X6 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_zfmisc_1])])])])).

fof(c_0_10,plain,(
    ! [X10,X11,X12,X14,X15,X16,X18] :
      ( ( r2_hidden(esk2_3(X10,X11,X12),k1_relat_1(X10))
        | ~ r2_hidden(X12,X11)
        | X11 != k2_relat_1(X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( X12 = k1_funct_1(X10,esk2_3(X10,X11,X12))
        | ~ r2_hidden(X12,X11)
        | X11 != k2_relat_1(X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( ~ r2_hidden(X15,k1_relat_1(X10))
        | X14 != k1_funct_1(X10,X15)
        | r2_hidden(X14,X11)
        | X11 != k2_relat_1(X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( ~ r2_hidden(esk3_2(X10,X16),X16)
        | ~ r2_hidden(X18,k1_relat_1(X10))
        | esk3_2(X10,X16) != k1_funct_1(X10,X18)
        | X16 = k2_relat_1(X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( r2_hidden(esk4_2(X10,X16),k1_relat_1(X10))
        | r2_hidden(esk3_2(X10,X16),X16)
        | X16 = k2_relat_1(X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( esk3_2(X10,X16) = k1_funct_1(X10,esk4_2(X10,X16))
        | r2_hidden(esk3_2(X10,X16),X16)
        | X16 = k2_relat_1(X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

cnf(c_0_11,negated_conjecture,
    ( ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_relat_1(X1) != esk6_0
    | k2_relat_1(X1) != k1_tarski(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | X1 = k1_tarski(X2)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X20,X21,X23] :
      ( v1_relat_1(esk5_2(X20,X21))
      & v1_funct_1(esk5_2(X20,X21))
      & k1_relat_1(esk5_2(X20,X21)) = X20
      & ( ~ r2_hidden(X23,X20)
        | k1_funct_1(esk5_2(X20,X21),X23) = X21 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).

cnf(c_0_15,plain,
    ( X1 = k1_funct_1(X2,esk2_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( k1_relat_1(X1) != esk6_0
    | k2_relat_1(X1) != k2_tarski(esk7_0,esk7_0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_18,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_tarski(X2,X2)
    | r2_hidden(esk1_2(X1,X2),X1) ),
    inference(rw,[status(thm)],[c_0_13,c_0_12])).

cnf(c_0_19,plain,
    ( k1_funct_1(esk5_2(X2,X3),X1) = X3
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k1_funct_1(X1,esk2_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( v1_funct_1(esk5_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( v1_relat_1(esk5_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( r2_hidden(esk2_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k1_relat_1(esk5_2(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,negated_conjecture,
    ( k2_relat_1(X1) = k1_xboole_0
    | r2_hidden(esk1_2(k2_relat_1(X1),X2),k2_relat_1(X1))
    | k2_tarski(X2,X2) != k2_tarski(esk7_0,esk7_0)
    | k1_relat_1(X1) != esk6_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_26,plain,
    ( X1 = X2
    | ~ r2_hidden(esk2_3(esk5_2(X3,X2),k2_relat_1(esk5_2(X3,X2)),X1),X3)
    | ~ r2_hidden(X1,k2_relat_1(esk5_2(X3,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22])])).

cnf(c_0_27,plain,
    ( r2_hidden(esk2_3(esk5_2(X1,X2),k2_relat_1(esk5_2(X1,X2)),X3),X1)
    | ~ r2_hidden(X3,k2_relat_1(esk5_2(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_21]),c_0_22])])).

cnf(c_0_28,negated_conjecture,
    ( k2_relat_1(X1) = k1_xboole_0
    | r2_hidden(esk1_2(k2_relat_1(X1),esk7_0),k2_relat_1(X1))
    | k1_relat_1(X1) != esk6_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_29,plain,
    ( X1 = k1_tarski(X2)
    | X1 = k1_xboole_0
    | esk1_2(X1,X2) != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_30,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_relat_1(esk5_2(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( k2_relat_1(esk5_2(esk6_0,X1)) = k1_xboole_0
    | r2_hidden(esk1_2(k2_relat_1(esk5_2(esk6_0,X1)),esk7_0),k2_relat_1(esk5_2(esk6_0,X1))) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_24]),c_0_21]),c_0_22])])])).

fof(c_0_32,plain,(
    ! [X9] :
      ( ( k1_relat_1(X9) != k1_xboole_0
        | k2_relat_1(X9) = k1_xboole_0
        | ~ v1_relat_1(X9) )
      & ( k2_relat_1(X9) != k1_xboole_0
        | k1_relat_1(X9) = k1_xboole_0
        | ~ v1_relat_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).

cnf(c_0_33,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_tarski(X2,X2)
    | esk1_2(X1,X2) != X2 ),
    inference(rw,[status(thm)],[c_0_29,c_0_12])).

cnf(c_0_34,negated_conjecture,
    ( esk1_2(k2_relat_1(esk5_2(esk6_0,X1)),esk7_0) = X1
    | k2_relat_1(esk5_2(esk6_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( k2_relat_1(esk5_2(esk6_0,esk7_0)) = k2_tarski(esk7_0,esk7_0)
    | k2_relat_1(esk5_2(esk6_0,esk7_0)) = k1_xboole_0 ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34])])).

cnf(c_0_37,plain,
    ( k1_xboole_0 = X1
    | k2_relat_1(esk5_2(X1,X2)) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_35]),c_0_22])])).

cnf(c_0_38,negated_conjecture,
    ( k2_relat_1(esk5_2(esk6_0,esk7_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_36]),c_0_24]),c_0_21]),c_0_22])])).

cnf(c_0_39,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:57:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.56  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.20/0.56  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.20/0.56  #
% 0.20/0.56  # Preprocessing time       : 0.048 s
% 0.20/0.56  # Presaturation interreduction done
% 0.20/0.56  
% 0.20/0.56  # Proof found!
% 0.20/0.56  # SZS status Theorem
% 0.20/0.56  # SZS output start CNFRefutation
% 0.20/0.56  fof(t15_funct_1, conjecture, ![X1]:(X1!=k1_xboole_0=>![X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&k2_relat_1(X3)=k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_funct_1)).
% 0.20/0.56  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.56  fof(l44_zfmisc_1, axiom, ![X1, X2]:~(((X1!=k1_tarski(X2)&X1!=k1_xboole_0)&![X3]:~((r2_hidden(X3,X1)&X3!=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l44_zfmisc_1)).
% 0.20/0.56  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 0.20/0.56  fof(s3_funct_1__e2_24__funct_1, axiom, ![X1, X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&![X4]:(r2_hidden(X4,X1)=>k1_funct_1(X3,X4)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 0.20/0.56  fof(t65_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k1_relat_1(X1)=k1_xboole_0<=>k2_relat_1(X1)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 0.20/0.56  fof(c_0_6, negated_conjecture, ~(![X1]:(X1!=k1_xboole_0=>![X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&k2_relat_1(X3)=k1_tarski(X2)))), inference(assume_negation,[status(cth)],[t15_funct_1])).
% 0.20/0.56  fof(c_0_7, negated_conjecture, ![X26]:(esk6_0!=k1_xboole_0&(~v1_relat_1(X26)|~v1_funct_1(X26)|k1_relat_1(X26)!=esk6_0|k2_relat_1(X26)!=k1_tarski(esk7_0))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).
% 0.20/0.56  fof(c_0_8, plain, ![X5]:k2_tarski(X5,X5)=k1_tarski(X5), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.56  fof(c_0_9, plain, ![X6, X7]:((r2_hidden(esk1_2(X6,X7),X6)|(X6=k1_tarski(X7)|X6=k1_xboole_0))&(esk1_2(X6,X7)!=X7|(X6=k1_tarski(X7)|X6=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_zfmisc_1])])])])).
% 0.20/0.56  fof(c_0_10, plain, ![X10, X11, X12, X14, X15, X16, X18]:((((r2_hidden(esk2_3(X10,X11,X12),k1_relat_1(X10))|~r2_hidden(X12,X11)|X11!=k2_relat_1(X10)|(~v1_relat_1(X10)|~v1_funct_1(X10)))&(X12=k1_funct_1(X10,esk2_3(X10,X11,X12))|~r2_hidden(X12,X11)|X11!=k2_relat_1(X10)|(~v1_relat_1(X10)|~v1_funct_1(X10))))&(~r2_hidden(X15,k1_relat_1(X10))|X14!=k1_funct_1(X10,X15)|r2_hidden(X14,X11)|X11!=k2_relat_1(X10)|(~v1_relat_1(X10)|~v1_funct_1(X10))))&((~r2_hidden(esk3_2(X10,X16),X16)|(~r2_hidden(X18,k1_relat_1(X10))|esk3_2(X10,X16)!=k1_funct_1(X10,X18))|X16=k2_relat_1(X10)|(~v1_relat_1(X10)|~v1_funct_1(X10)))&((r2_hidden(esk4_2(X10,X16),k1_relat_1(X10))|r2_hidden(esk3_2(X10,X16),X16)|X16=k2_relat_1(X10)|(~v1_relat_1(X10)|~v1_funct_1(X10)))&(esk3_2(X10,X16)=k1_funct_1(X10,esk4_2(X10,X16))|r2_hidden(esk3_2(X10,X16),X16)|X16=k2_relat_1(X10)|(~v1_relat_1(X10)|~v1_funct_1(X10)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.20/0.56  cnf(c_0_11, negated_conjecture, (~v1_relat_1(X1)|~v1_funct_1(X1)|k1_relat_1(X1)!=esk6_0|k2_relat_1(X1)!=k1_tarski(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.56  cnf(c_0_12, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.56  cnf(c_0_13, plain, (r2_hidden(esk1_2(X1,X2),X1)|X1=k1_tarski(X2)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.56  fof(c_0_14, plain, ![X20, X21, X23]:(((v1_relat_1(esk5_2(X20,X21))&v1_funct_1(esk5_2(X20,X21)))&k1_relat_1(esk5_2(X20,X21))=X20)&(~r2_hidden(X23,X20)|k1_funct_1(esk5_2(X20,X21),X23)=X21)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).
% 0.20/0.56  cnf(c_0_15, plain, (X1=k1_funct_1(X2,esk2_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.56  cnf(c_0_16, plain, (r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.56  cnf(c_0_17, negated_conjecture, (k1_relat_1(X1)!=esk6_0|k2_relat_1(X1)!=k2_tarski(esk7_0,esk7_0)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 0.20/0.56  cnf(c_0_18, plain, (X1=k1_xboole_0|X1=k2_tarski(X2,X2)|r2_hidden(esk1_2(X1,X2),X1)), inference(rw,[status(thm)],[c_0_13, c_0_12])).
% 0.20/0.56  cnf(c_0_19, plain, (k1_funct_1(esk5_2(X2,X3),X1)=X3|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.56  cnf(c_0_20, plain, (k1_funct_1(X1,esk2_3(X1,k2_relat_1(X1),X2))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_15])).
% 0.20/0.56  cnf(c_0_21, plain, (v1_funct_1(esk5_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.56  cnf(c_0_22, plain, (v1_relat_1(esk5_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.56  cnf(c_0_23, plain, (r2_hidden(esk2_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_16])).
% 0.20/0.56  cnf(c_0_24, plain, (k1_relat_1(esk5_2(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.56  cnf(c_0_25, negated_conjecture, (k2_relat_1(X1)=k1_xboole_0|r2_hidden(esk1_2(k2_relat_1(X1),X2),k2_relat_1(X1))|k2_tarski(X2,X2)!=k2_tarski(esk7_0,esk7_0)|k1_relat_1(X1)!=esk6_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.56  cnf(c_0_26, plain, (X1=X2|~r2_hidden(esk2_3(esk5_2(X3,X2),k2_relat_1(esk5_2(X3,X2)),X1),X3)|~r2_hidden(X1,k2_relat_1(esk5_2(X3,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22])])).
% 0.20/0.56  cnf(c_0_27, plain, (r2_hidden(esk2_3(esk5_2(X1,X2),k2_relat_1(esk5_2(X1,X2)),X3),X1)|~r2_hidden(X3,k2_relat_1(esk5_2(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_21]), c_0_22])])).
% 0.20/0.56  cnf(c_0_28, negated_conjecture, (k2_relat_1(X1)=k1_xboole_0|r2_hidden(esk1_2(k2_relat_1(X1),esk7_0),k2_relat_1(X1))|k1_relat_1(X1)!=esk6_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_25])).
% 0.20/0.56  cnf(c_0_29, plain, (X1=k1_tarski(X2)|X1=k1_xboole_0|esk1_2(X1,X2)!=X2), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.56  cnf(c_0_30, plain, (X1=X2|~r2_hidden(X1,k2_relat_1(esk5_2(X3,X2)))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.56  cnf(c_0_31, negated_conjecture, (k2_relat_1(esk5_2(esk6_0,X1))=k1_xboole_0|r2_hidden(esk1_2(k2_relat_1(esk5_2(esk6_0,X1)),esk7_0),k2_relat_1(esk5_2(esk6_0,X1)))), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_24]), c_0_21]), c_0_22])])])).
% 0.20/0.56  fof(c_0_32, plain, ![X9]:((k1_relat_1(X9)!=k1_xboole_0|k2_relat_1(X9)=k1_xboole_0|~v1_relat_1(X9))&(k2_relat_1(X9)!=k1_xboole_0|k1_relat_1(X9)=k1_xboole_0|~v1_relat_1(X9))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).
% 0.20/0.56  cnf(c_0_33, plain, (X1=k1_xboole_0|X1=k2_tarski(X2,X2)|esk1_2(X1,X2)!=X2), inference(rw,[status(thm)],[c_0_29, c_0_12])).
% 0.20/0.56  cnf(c_0_34, negated_conjecture, (esk1_2(k2_relat_1(esk5_2(esk6_0,X1)),esk7_0)=X1|k2_relat_1(esk5_2(esk6_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.56  cnf(c_0_35, plain, (k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.56  cnf(c_0_36, negated_conjecture, (k2_relat_1(esk5_2(esk6_0,esk7_0))=k2_tarski(esk7_0,esk7_0)|k2_relat_1(esk5_2(esk6_0,esk7_0))=k1_xboole_0), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34])])).
% 0.20/0.56  cnf(c_0_37, plain, (k1_xboole_0=X1|k2_relat_1(esk5_2(X1,X2))!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_35]), c_0_22])])).
% 0.20/0.56  cnf(c_0_38, negated_conjecture, (k2_relat_1(esk5_2(esk6_0,esk7_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_36]), c_0_24]), c_0_21]), c_0_22])])).
% 0.20/0.56  cnf(c_0_39, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.56  cnf(c_0_40, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), ['proof']).
% 0.20/0.56  # SZS output end CNFRefutation
% 0.20/0.56  # Proof object total steps             : 41
% 0.20/0.56  # Proof object clause steps            : 28
% 0.20/0.56  # Proof object formula steps           : 13
% 0.20/0.56  # Proof object conjectures             : 13
% 0.20/0.56  # Proof object clause conjectures      : 10
% 0.20/0.56  # Proof object formula conjectures     : 3
% 0.20/0.56  # Proof object initial clauses used    : 12
% 0.20/0.56  # Proof object initial formulas used   : 6
% 0.20/0.56  # Proof object generating inferences   : 11
% 0.20/0.56  # Proof object simplifying inferences  : 23
% 0.20/0.56  # Training examples: 0 positive, 0 negative
% 0.20/0.56  # Parsed axioms                        : 6
% 0.20/0.56  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.56  # Initial clauses                      : 17
% 0.20/0.56  # Removed in clause preprocessing      : 1
% 0.20/0.56  # Initial clauses in saturation        : 16
% 0.20/0.56  # Processed clauses                    : 323
% 0.20/0.56  # ...of these trivial                  : 3
% 0.20/0.56  # ...subsumed                          : 143
% 0.20/0.56  # ...remaining for further processing  : 177
% 0.20/0.56  # Other redundant clauses eliminated   : 155
% 0.20/0.56  # Clauses deleted for lack of memory   : 0
% 0.20/0.56  # Backward-subsumed                    : 15
% 0.20/0.56  # Backward-rewritten                   : 1
% 0.20/0.56  # Generated clauses                    : 6936
% 0.20/0.56  # ...of the previous two non-trivial   : 6406
% 0.20/0.56  # Contextual simplify-reflections      : 7
% 0.20/0.56  # Paramodulations                      : 6742
% 0.20/0.56  # Factorizations                       : 36
% 0.20/0.56  # Equation resolutions                 : 158
% 0.20/0.56  # Propositional unsat checks           : 0
% 0.20/0.56  #    Propositional check models        : 0
% 0.20/0.56  #    Propositional check unsatisfiable : 0
% 0.20/0.56  #    Propositional clauses             : 0
% 0.20/0.56  #    Propositional clauses after purity: 0
% 0.20/0.56  #    Propositional unsat core size     : 0
% 0.20/0.56  #    Propositional preprocessing time  : 0.000
% 0.20/0.56  #    Propositional encoding time       : 0.000
% 0.20/0.56  #    Propositional solver time         : 0.000
% 0.20/0.56  #    Success case prop preproc time    : 0.000
% 0.20/0.56  #    Success case prop encoding time   : 0.000
% 0.20/0.56  #    Success case prop solver time     : 0.000
% 0.20/0.56  # Current number of processed clauses  : 141
% 0.20/0.56  #    Positive orientable unit clauses  : 11
% 0.20/0.56  #    Positive unorientable unit clauses: 0
% 0.20/0.56  #    Negative unit clauses             : 2
% 0.20/0.56  #    Non-unit-clauses                  : 128
% 0.20/0.56  # Current number of unprocessed clauses: 6068
% 0.20/0.56  # ...number of literals in the above   : 36441
% 0.20/0.56  # Current number of archived formulas  : 0
% 0.20/0.56  # Current number of archived clauses   : 34
% 0.20/0.56  # Clause-clause subsumption calls (NU) : 4547
% 0.20/0.56  # Rec. Clause-clause subsumption calls : 1406
% 0.20/0.56  # Non-unit clause-clause subsumptions  : 135
% 0.20/0.56  # Unit Clause-clause subsumption calls : 92
% 0.20/0.56  # Rewrite failures with RHS unbound    : 0
% 0.20/0.56  # BW rewrite match attempts            : 107
% 0.20/0.56  # BW rewrite match successes           : 6
% 0.20/0.56  # Condensation attempts                : 0
% 0.20/0.56  # Condensation successes               : 0
% 0.20/0.56  # Termbank termtop insertions          : 157819
% 0.20/0.56  
% 0.20/0.56  # -------------------------------------------------
% 0.20/0.56  # User time                : 0.208 s
% 0.20/0.56  # System time              : 0.007 s
% 0.20/0.56  # Total time               : 0.215 s
% 0.20/0.56  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
