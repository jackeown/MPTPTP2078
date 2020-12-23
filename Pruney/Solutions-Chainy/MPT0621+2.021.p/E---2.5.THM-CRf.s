%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:01 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   31 (  80 expanded)
%              Number of clauses        :   20 (  34 expanded)
%              Number of leaves         :    5 (  21 expanded)
%              Depth                    :   12
%              Number of atoms          :  101 ( 333 expanded)
%              Number of equality atoms :   49 ( 152 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).

fof(s3_funct_1__e7_25__funct_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( v1_relat_1(X2)
      & v1_funct_1(X2)
      & k1_relat_1(X2) = X1
      & ! [X3] :
          ( r2_hidden(X3,X1)
         => k1_funct_1(X2,X3) = np__1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

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

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

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
    ! [X18,X19] :
      ( ( ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19)
        | k1_relat_1(X18) != esk4_0
        | k1_relat_1(X19) != esk4_0
        | X18 = X19 )
      & esk4_0 != k1_xboole_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).

fof(c_0_7,plain,(
    ! [X14,X16] :
      ( v1_relat_1(esk3_1(X14))
      & v1_funct_1(esk3_1(X14))
      & k1_relat_1(esk3_1(X14)) = X14
      & ( ~ r2_hidden(X16,X14)
        | k1_funct_1(esk3_1(X14),X16) = np__1 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e7_25__funct_1])])])])).

cnf(c_0_8,negated_conjecture,
    ( X1 = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k1_relat_1(X1) != esk4_0
    | k1_relat_1(X2) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( v1_funct_1(esk3_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( k1_relat_1(esk3_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( v1_relat_1(esk3_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,plain,(
    ! [X10,X11,X13] :
      ( v1_relat_1(esk2_2(X10,X11))
      & v1_funct_1(esk2_2(X10,X11))
      & k1_relat_1(esk2_2(X10,X11)) = X10
      & ( ~ r2_hidden(X13,X10)
        | k1_funct_1(esk2_2(X10,X11),X13) = X11 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).

cnf(c_0_13,negated_conjecture,
    ( X1 = esk3_1(X2)
    | k1_relat_1(X1) != esk4_0
    | X2 != esk4_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10]),c_0_11])])).

cnf(c_0_14,plain,
    ( v1_funct_1(esk2_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,plain,
    ( k1_relat_1(esk2_2(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( v1_relat_1(esk2_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k1_funct_1(esk2_2(X2,X3),X1) = X3
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( esk2_2(X1,X2) = esk3_1(X3)
    | X1 != esk4_0
    | X3 != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16])])).

fof(c_0_19,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_20,negated_conjecture,
    ( k1_funct_1(esk3_1(X1),X2) = X3
    | X4 != esk4_0
    | X1 != esk4_0
    | ~ r2_hidden(X2,X4) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_21,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( k1_funct_1(esk3_1(X1),esk1_1(X2)) = X3
    | v1_xboole_0(X2)
    | X2 != esk4_0
    | X1 != esk4_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_23,negated_conjecture,
    ( X1 = X2
    | v1_xboole_0(X3)
    | X3 != esk4_0
    | X4 != esk4_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_22])).

fof(c_0_24,plain,(
    ! [X9] :
      ( ~ v1_xboole_0(X9)
      | X9 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_25,negated_conjecture,
    ( X1 = X2
    | v1_xboole_0(X3)
    | X3 != esk4_0 ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_26,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( X1 = X2
    | v1_xboole_0(esk4_0) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_29,negated_conjecture,
    ( X1 = X2 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_28,c_0_29]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:17:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___103_C18_F1_PI_AE_Q4_CS_SP_S0Y
% 0.13/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.042 s
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t16_funct_1, conjecture, ![X1]:(![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X2)=X1&k1_relat_1(X3)=X1)=>X2=X3)))=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_1)).
% 0.13/0.39  fof(s3_funct_1__e7_25__funct_1, axiom, ![X1]:?[X2]:(((v1_relat_1(X2)&v1_funct_1(X2))&k1_relat_1(X2)=X1)&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=np__1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e7_25__funct_1)).
% 0.13/0.39  fof(s3_funct_1__e2_24__funct_1, axiom, ![X1, X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&![X4]:(r2_hidden(X4,X1)=>k1_funct_1(X3,X4)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 0.13/0.39  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.13/0.39  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.13/0.39  fof(c_0_5, negated_conjecture, ~(![X1]:(![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X2)=X1&k1_relat_1(X3)=X1)=>X2=X3)))=>X1=k1_xboole_0)), inference(assume_negation,[status(cth)],[t16_funct_1])).
% 0.13/0.39  fof(c_0_6, negated_conjecture, ![X18, X19]:((~v1_relat_1(X18)|~v1_funct_1(X18)|(~v1_relat_1(X19)|~v1_funct_1(X19)|(k1_relat_1(X18)!=esk4_0|k1_relat_1(X19)!=esk4_0|X18=X19)))&esk4_0!=k1_xboole_0), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).
% 0.13/0.39  fof(c_0_7, plain, ![X14, X16]:(((v1_relat_1(esk3_1(X14))&v1_funct_1(esk3_1(X14)))&k1_relat_1(esk3_1(X14))=X14)&(~r2_hidden(X16,X14)|k1_funct_1(esk3_1(X14),X16)=np__1)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e7_25__funct_1])])])])).
% 0.13/0.39  cnf(c_0_8, negated_conjecture, (X1=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|k1_relat_1(X1)!=esk4_0|k1_relat_1(X2)!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.39  cnf(c_0_9, plain, (v1_funct_1(esk3_1(X1))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.39  cnf(c_0_10, plain, (k1_relat_1(esk3_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.39  cnf(c_0_11, plain, (v1_relat_1(esk3_1(X1))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.39  fof(c_0_12, plain, ![X10, X11, X13]:(((v1_relat_1(esk2_2(X10,X11))&v1_funct_1(esk2_2(X10,X11)))&k1_relat_1(esk2_2(X10,X11))=X10)&(~r2_hidden(X13,X10)|k1_funct_1(esk2_2(X10,X11),X13)=X11)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).
% 0.13/0.39  cnf(c_0_13, negated_conjecture, (X1=esk3_1(X2)|k1_relat_1(X1)!=esk4_0|X2!=esk4_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_9]), c_0_10]), c_0_11])])).
% 0.13/0.39  cnf(c_0_14, plain, (v1_funct_1(esk2_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  cnf(c_0_15, plain, (k1_relat_1(esk2_2(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  cnf(c_0_16, plain, (v1_relat_1(esk2_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  cnf(c_0_17, plain, (k1_funct_1(esk2_2(X2,X3),X1)=X3|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  cnf(c_0_18, negated_conjecture, (esk2_2(X1,X2)=esk3_1(X3)|X1!=esk4_0|X3!=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15]), c_0_16])])).
% 0.13/0.39  fof(c_0_19, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.13/0.39  cnf(c_0_20, negated_conjecture, (k1_funct_1(esk3_1(X1),X2)=X3|X4!=esk4_0|X1!=esk4_0|~r2_hidden(X2,X4)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.39  cnf(c_0_21, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.39  cnf(c_0_22, negated_conjecture, (k1_funct_1(esk3_1(X1),esk1_1(X2))=X3|v1_xboole_0(X2)|X2!=esk4_0|X1!=esk4_0), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.39  cnf(c_0_23, negated_conjecture, (X1=X2|v1_xboole_0(X3)|X3!=esk4_0|X4!=esk4_0), inference(spm,[status(thm)],[c_0_22, c_0_22])).
% 0.13/0.39  fof(c_0_24, plain, ![X9]:(~v1_xboole_0(X9)|X9=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.13/0.39  cnf(c_0_25, negated_conjecture, (X1=X2|v1_xboole_0(X3)|X3!=esk4_0), inference(er,[status(thm)],[c_0_23])).
% 0.13/0.39  cnf(c_0_26, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.39  cnf(c_0_27, negated_conjecture, (X1=X2|v1_xboole_0(esk4_0)), inference(er,[status(thm)],[c_0_25])).
% 0.13/0.39  cnf(c_0_28, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.39  cnf(c_0_29, negated_conjecture, (X1=X2), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 0.13/0.39  cnf(c_0_30, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_28, c_0_29]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 31
% 0.13/0.39  # Proof object clause steps            : 20
% 0.13/0.39  # Proof object formula steps           : 11
% 0.13/0.39  # Proof object conjectures             : 14
% 0.13/0.39  # Proof object clause conjectures      : 11
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 11
% 0.13/0.39  # Proof object initial formulas used   : 5
% 0.13/0.39  # Proof object generating inferences   : 8
% 0.13/0.39  # Proof object simplifying inferences  : 8
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 5
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 13
% 0.13/0.39  # Removed in clause preprocessing      : 0
% 0.13/0.39  # Initial clauses in saturation        : 13
% 0.13/0.39  # Processed clauses                    : 40
% 0.13/0.39  # ...of these trivial                  : 6
% 0.13/0.39  # ...subsumed                          : 8
% 0.13/0.39  # ...remaining for further processing  : 26
% 0.13/0.39  # Other redundant clauses eliminated   : 2
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 18
% 0.13/0.39  # Backward-rewritten                   : 0
% 0.13/0.39  # Generated clauses                    : 114
% 0.13/0.39  # ...of the previous two non-trivial   : 92
% 0.13/0.39  # Contextual simplify-reflections      : 0
% 0.13/0.39  # Paramodulations                      : 108
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 5
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 7
% 0.13/0.39  #    Positive orientable unit clauses  : 4
% 0.13/0.39  #    Positive unorientable unit clauses: 1
% 0.13/0.39  #    Negative unit clauses             : 0
% 0.13/0.39  #    Non-unit-clauses                  : 2
% 0.13/0.39  # Current number of unprocessed clauses: 63
% 0.13/0.39  # ...number of literals in the above   : 226
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 19
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 25
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 20
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 12
% 0.13/0.39  # Unit Clause-clause subsumption calls : 19
% 0.13/0.39  # Rewrite failures with RHS unbound    : 40
% 0.13/0.39  # BW rewrite match attempts            : 34
% 0.13/0.39  # BW rewrite match successes           : 32
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 1315
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.046 s
% 0.13/0.39  # System time              : 0.004 s
% 0.13/0.39  # Total time               : 0.050 s
% 0.13/0.39  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
