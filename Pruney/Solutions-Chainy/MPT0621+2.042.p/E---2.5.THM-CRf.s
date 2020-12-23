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
% DateTime   : Thu Dec  3 10:53:04 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   32 ( 122 expanded)
%              Number of clauses        :   21 (  49 expanded)
%              Number of leaves         :    5 (  31 expanded)
%              Depth                    :   11
%              Number of atoms          :   91 ( 527 expanded)
%              Number of equality atoms :   53 ( 296 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t16_funct_1,conjecture,(
    ! [X1] :
      ( ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ! [X3] :
              ( ( v1_relat_1(X3)
                & v1_funct_1(X3) )
             => ( ( k1_relat_1(X2) = X1
                  & k1_relat_1(X3) = X1 )
               => X2 = X3 ) ) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).

fof(t15_funct_1,axiom,(
    ! [X1] :
      ( X1 != k1_xboole_0
     => ! [X2] :
        ? [X3] :
          ( v1_relat_1(X3)
          & v1_funct_1(X3)
          & k1_relat_1(X3) = X1
          & k2_relat_1(X3) = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

fof(s3_funct_1__e7_25__funct_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( v1_relat_1(X2)
      & v1_funct_1(X2)
      & k1_relat_1(X2) = X1
      & ! [X3] :
          ( r2_hidden(X3,X1)
         => k1_funct_1(X2,X3) = np__1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t11_setfam_1,axiom,(
    ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ! [X3] :
                ( ( v1_relat_1(X3)
                  & v1_funct_1(X3) )
               => ( ( k1_relat_1(X2) = X1
                    & k1_relat_1(X3) = X1 )
                 => X2 = X3 ) ) )
       => X1 = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t16_funct_1])).

fof(c_0_6,negated_conjecture,(
    ! [X13,X14] :
      ( ( ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14)
        | k1_relat_1(X13) != esk3_0
        | k1_relat_1(X14) != esk3_0
        | X13 = X14 )
      & esk3_0 != k1_xboole_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).

fof(c_0_7,plain,(
    ! [X9,X10] :
      ( ( v1_relat_1(esk2_2(X9,X10))
        | X9 = k1_xboole_0 )
      & ( v1_funct_1(esk2_2(X9,X10))
        | X9 = k1_xboole_0 )
      & ( k1_relat_1(esk2_2(X9,X10)) = X9
        | X9 = k1_xboole_0 )
      & ( k2_relat_1(esk2_2(X9,X10)) = k1_tarski(X10)
        | X9 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_funct_1])])])])])).

cnf(c_0_8,negated_conjecture,
    ( X1 = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k1_relat_1(X1) != esk3_0
    | k1_relat_1(X2) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( k1_relat_1(esk2_2(X1,X2)) = X1
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_11,plain,(
    ! [X6,X8] :
      ( v1_relat_1(esk1_1(X6))
      & v1_funct_1(esk1_1(X6))
      & k1_relat_1(esk1_1(X6)) = X6
      & ( ~ r2_hidden(X8,X6)
        | k1_funct_1(esk1_1(X6),X8) = np__1 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e7_25__funct_1])])])])).

cnf(c_0_12,negated_conjecture,
    ( X1 = esk2_2(esk3_0,X2)
    | k1_relat_1(X1) != esk3_0
    | ~ v1_funct_1(esk2_2(esk3_0,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(esk2_2(esk3_0,X2))
    | ~ v1_relat_1(X1) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9])]),c_0_10])).

cnf(c_0_13,plain,
    ( k1_relat_1(esk1_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,plain,
    ( v1_funct_1(esk1_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( v1_relat_1(esk1_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X4] : k2_tarski(X4,X4) = k1_tarski(X4) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_17,negated_conjecture,
    ( esk1_1(esk3_0) = esk2_2(esk3_0,X1)
    | ~ v1_funct_1(esk2_2(esk3_0,X1))
    | ~ v1_relat_1(esk2_2(esk3_0,X1)) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15])])])).

cnf(c_0_18,plain,
    ( v1_funct_1(esk2_2(X1,X2))
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_19,plain,(
    ! [X5] : k1_setfam_1(k1_tarski(X5)) = X5 ),
    inference(variable_rename,[status(thm)],[t11_setfam_1])).

cnf(c_0_20,plain,
    ( k2_relat_1(esk2_2(X1,X2)) = k1_tarski(X2)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_21,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( esk1_1(esk3_0) = esk2_2(esk3_0,X1)
    | ~ v1_relat_1(esk2_2(esk3_0,X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_10])).

cnf(c_0_23,plain,
    ( v1_relat_1(esk2_2(X1,X2))
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_24,plain,
    ( k1_setfam_1(k1_tarski(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( X1 = k1_xboole_0
    | k2_relat_1(esk2_2(X1,X2)) = k2_tarski(X2,X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( esk1_1(esk3_0) = esk2_2(esk3_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_10])).

cnf(c_0_27,plain,
    ( k1_setfam_1(k2_tarski(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_24,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( k2_relat_1(esk1_1(esk3_0)) = k2_tarski(X1,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_10])).

cnf(c_0_29,negated_conjecture,
    ( k1_setfam_1(k2_relat_1(esk1_1(esk3_0))) = X1 ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_30,negated_conjecture,
    ( X1 = X2 ),
    inference(spm,[status(thm)],[c_0_29,c_0_29])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_10,c_0_30]),
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
% 0.13/0.34  % DateTime   : Tue Dec  1 17:41:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_B00_00_F1_SE_CS_SP_PS_S083N
% 0.13/0.37  # and selection function SelectCQArNT.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.027 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t16_funct_1, conjecture, ![X1]:(![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X2)=X1&k1_relat_1(X3)=X1)=>X2=X3)))=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_1)).
% 0.13/0.37  fof(t15_funct_1, axiom, ![X1]:(X1!=k1_xboole_0=>![X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&k2_relat_1(X3)=k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_funct_1)).
% 0.13/0.37  fof(s3_funct_1__e7_25__funct_1, axiom, ![X1]:?[X2]:(((v1_relat_1(X2)&v1_funct_1(X2))&k1_relat_1(X2)=X1)&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=np__1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e7_25__funct_1)).
% 0.13/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.37  fof(t11_setfam_1, axiom, ![X1]:k1_setfam_1(k1_tarski(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 0.13/0.37  fof(c_0_5, negated_conjecture, ~(![X1]:(![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X2)=X1&k1_relat_1(X3)=X1)=>X2=X3)))=>X1=k1_xboole_0)), inference(assume_negation,[status(cth)],[t16_funct_1])).
% 0.13/0.37  fof(c_0_6, negated_conjecture, ![X13, X14]:((~v1_relat_1(X13)|~v1_funct_1(X13)|(~v1_relat_1(X14)|~v1_funct_1(X14)|(k1_relat_1(X13)!=esk3_0|k1_relat_1(X14)!=esk3_0|X13=X14)))&esk3_0!=k1_xboole_0), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).
% 0.13/0.37  fof(c_0_7, plain, ![X9, X10]:((((v1_relat_1(esk2_2(X9,X10))|X9=k1_xboole_0)&(v1_funct_1(esk2_2(X9,X10))|X9=k1_xboole_0))&(k1_relat_1(esk2_2(X9,X10))=X9|X9=k1_xboole_0))&(k2_relat_1(esk2_2(X9,X10))=k1_tarski(X10)|X9=k1_xboole_0)), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_funct_1])])])])])).
% 0.13/0.37  cnf(c_0_8, negated_conjecture, (X1=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|k1_relat_1(X1)!=esk3_0|k1_relat_1(X2)!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_9, plain, (k1_relat_1(esk2_2(X1,X2))=X1|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_10, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  fof(c_0_11, plain, ![X6, X8]:(((v1_relat_1(esk1_1(X6))&v1_funct_1(esk1_1(X6)))&k1_relat_1(esk1_1(X6))=X6)&(~r2_hidden(X8,X6)|k1_funct_1(esk1_1(X6),X8)=np__1)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e7_25__funct_1])])])])).
% 0.13/0.37  cnf(c_0_12, negated_conjecture, (X1=esk2_2(esk3_0,X2)|k1_relat_1(X1)!=esk3_0|~v1_funct_1(esk2_2(esk3_0,X2))|~v1_funct_1(X1)|~v1_relat_1(esk2_2(esk3_0,X2))|~v1_relat_1(X1)), inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_9])]), c_0_10])).
% 0.13/0.37  cnf(c_0_13, plain, (k1_relat_1(esk1_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  cnf(c_0_14, plain, (v1_funct_1(esk1_1(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  cnf(c_0_15, plain, (v1_relat_1(esk1_1(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  fof(c_0_16, plain, ![X4]:k2_tarski(X4,X4)=k1_tarski(X4), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.37  cnf(c_0_17, negated_conjecture, (esk1_1(esk3_0)=esk2_2(esk3_0,X1)|~v1_funct_1(esk2_2(esk3_0,X1))|~v1_relat_1(esk2_2(esk3_0,X1))), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14]), c_0_15])])])).
% 0.13/0.37  cnf(c_0_18, plain, (v1_funct_1(esk2_2(X1,X2))|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  fof(c_0_19, plain, ![X5]:k1_setfam_1(k1_tarski(X5))=X5, inference(variable_rename,[status(thm)],[t11_setfam_1])).
% 0.13/0.37  cnf(c_0_20, plain, (k2_relat_1(esk2_2(X1,X2))=k1_tarski(X2)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_21, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_22, negated_conjecture, (esk1_1(esk3_0)=esk2_2(esk3_0,X1)|~v1_relat_1(esk2_2(esk3_0,X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_10])).
% 0.13/0.37  cnf(c_0_23, plain, (v1_relat_1(esk2_2(X1,X2))|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_24, plain, (k1_setfam_1(k1_tarski(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.37  cnf(c_0_25, plain, (X1=k1_xboole_0|k2_relat_1(esk2_2(X1,X2))=k2_tarski(X2,X2)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.37  cnf(c_0_26, negated_conjecture, (esk1_1(esk3_0)=esk2_2(esk3_0,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_10])).
% 0.13/0.37  cnf(c_0_27, plain, (k1_setfam_1(k2_tarski(X1,X1))=X1), inference(rw,[status(thm)],[c_0_24, c_0_21])).
% 0.13/0.37  cnf(c_0_28, negated_conjecture, (k2_relat_1(esk1_1(esk3_0))=k2_tarski(X1,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_10])).
% 0.13/0.37  cnf(c_0_29, negated_conjecture, (k1_setfam_1(k2_relat_1(esk1_1(esk3_0)))=X1), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.37  cnf(c_0_30, negated_conjecture, (X1=X2), inference(spm,[status(thm)],[c_0_29, c_0_29])).
% 0.13/0.37  cnf(c_0_31, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_10, c_0_30]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 32
% 0.13/0.37  # Proof object clause steps            : 21
% 0.13/0.37  # Proof object formula steps           : 11
% 0.13/0.37  # Proof object conjectures             : 13
% 0.13/0.37  # Proof object clause conjectures      : 10
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 11
% 0.13/0.37  # Proof object initial formulas used   : 5
% 0.13/0.37  # Proof object generating inferences   : 7
% 0.13/0.37  # Proof object simplifying inferences  : 12
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 5
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 12
% 0.13/0.37  # Removed in clause preprocessing      : 1
% 0.13/0.37  # Initial clauses in saturation        : 11
% 0.13/0.37  # Processed clauses                    : 43
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 7
% 0.13/0.37  # ...remaining for further processing  : 36
% 0.13/0.37  # Other redundant clauses eliminated   : 8
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 17
% 0.13/0.37  # Backward-rewritten                   : 2
% 0.13/0.37  # Generated clauses                    : 97
% 0.13/0.37  # ...of the previous two non-trivial   : 59
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 88
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 8
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 5
% 0.13/0.37  #    Positive orientable unit clauses  : 4
% 0.13/0.37  #    Positive unorientable unit clauses: 1
% 0.13/0.37  #    Negative unit clauses             : 0
% 0.13/0.37  #    Non-unit-clauses                  : 0
% 0.13/0.37  # Current number of unprocessed clauses: 38
% 0.13/0.37  # ...number of literals in the above   : 64
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 32
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 1
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 1
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 1
% 0.13/0.37  # Unit Clause-clause subsumption calls : 23
% 0.13/0.37  # Rewrite failures with RHS unbound    : 71
% 0.13/0.37  # BW rewrite match attempts            : 73
% 0.13/0.37  # BW rewrite match successes           : 70
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 1479
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.029 s
% 0.13/0.37  # System time              : 0.003 s
% 0.13/0.37  # Total time               : 0.032 s
% 0.13/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
