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
% DateTime   : Thu Dec  3 10:53:04 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   37 (  92 expanded)
%              Number of clauses        :   22 (  38 expanded)
%              Number of leaves         :    7 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :  102 ( 355 expanded)
%              Number of equality atoms :   70 ( 226 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(t68_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t49_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(t21_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_xboole_0
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

fof(c_0_7,negated_conjecture,(
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

fof(c_0_8,negated_conjecture,(
    ! [X22,X23] :
      ( ( ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23)
        | k1_relat_1(X22) != esk3_0
        | k1_relat_1(X23) != esk3_0
        | X22 = X23 )
      & esk3_0 != k1_xboole_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).

fof(c_0_9,plain,(
    ! [X18,X19] :
      ( ( v1_relat_1(esk2_2(X18,X19))
        | X18 = k1_xboole_0 )
      & ( v1_funct_1(esk2_2(X18,X19))
        | X18 = k1_xboole_0 )
      & ( k1_relat_1(esk2_2(X18,X19)) = X18
        | X18 = k1_xboole_0 )
      & ( k2_relat_1(esk2_2(X18,X19)) = k1_tarski(X19)
        | X18 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_funct_1])])])])])).

cnf(c_0_10,negated_conjecture,
    ( X1 = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k1_relat_1(X1) != esk3_0
    | k1_relat_1(X2) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( k1_relat_1(esk2_2(X1,X2)) = X1
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( v1_relat_1(esk2_2(X1,X2))
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( v1_funct_1(esk2_2(X1,X2))
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( X1 = esk2_2(X2,X3)
    | X2 = k1_xboole_0
    | k1_relat_1(X1) != esk3_0
    | X2 != esk3_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),c_0_13])).

cnf(c_0_15,negated_conjecture,
    ( esk2_2(X1,X2) = esk2_2(X3,X4)
    | X1 = k1_xboole_0
    | X3 = k1_xboole_0
    | X1 != esk3_0
    | X3 != esk3_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_11]),c_0_12]),c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_17,plain,(
    ! [X16,X17] :
      ( ( k4_xboole_0(k1_tarski(X16),X17) != k1_xboole_0
        | r2_hidden(X16,X17) )
      & ( ~ r2_hidden(X16,X17)
        | k4_xboole_0(k1_tarski(X16),X17) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t68_zfmisc_1])])).

fof(c_0_18,plain,(
    ! [X4] :
      ( X4 = k1_xboole_0
      | r2_hidden(esk1_1(X4),X4) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_19,plain,(
    ! [X14,X15] : k2_xboole_0(k1_tarski(X14),X15) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

fof(c_0_20,plain,(
    ! [X6] : k2_xboole_0(X6,k1_xboole_0) = X6 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_21,negated_conjecture,
    ( esk2_2(esk3_0,X1) = esk2_2(X2,X3)
    | X2 = k1_xboole_0
    | X2 != esk3_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_15]),c_0_16])).

fof(c_0_22,plain,(
    ! [X12,X13] :
      ( k4_xboole_0(k1_tarski(X12),k1_tarski(X13)) != k1_xboole_0
      | X12 = X13 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_zfmisc_1])])).

cnf(c_0_23,plain,
    ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k2_relat_1(esk2_2(X1,X2)) = k1_tarski(X2)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_28,negated_conjecture,
    ( esk2_2(esk3_0,X1) = esk2_2(esk3_0,X2) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_21]),c_0_16])).

cnf(c_0_29,plain,
    ( X1 = X2
    | k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( k4_xboole_0(k1_tarski(esk1_1(X1)),X1) = k1_xboole_0
    | X1 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,plain,
    ( k1_tarski(X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( k2_relat_1(esk2_2(esk3_0,X1)) = k1_tarski(X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_16])).

cnf(c_0_33,plain,
    ( esk1_1(k1_tarski(X1)) = X1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( k1_tarski(X1) = k1_tarski(X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_32]),c_0_16])).

cnf(c_0_35,negated_conjecture,
    ( X1 = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_16,c_0_35]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:48:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 0.15/0.38  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0i
% 0.15/0.38  # and selection function SelectDiffNegLit.
% 0.15/0.38  #
% 0.15/0.38  # Preprocessing time       : 0.026 s
% 0.15/0.38  # Presaturation interreduction done
% 0.15/0.38  
% 0.15/0.38  # Proof found!
% 0.15/0.38  # SZS status Theorem
% 0.15/0.38  # SZS output start CNFRefutation
% 0.15/0.38  fof(t16_funct_1, conjecture, ![X1]:(![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X2)=X1&k1_relat_1(X3)=X1)=>X2=X3)))=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_1)).
% 0.15/0.38  fof(t15_funct_1, axiom, ![X1]:(X1!=k1_xboole_0=>![X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&k2_relat_1(X3)=k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_funct_1)).
% 0.15/0.38  fof(t68_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 0.15/0.38  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.15/0.38  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.15/0.38  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.15/0.38  fof(t21_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_xboole_0=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 0.15/0.38  fof(c_0_7, negated_conjecture, ~(![X1]:(![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X2)=X1&k1_relat_1(X3)=X1)=>X2=X3)))=>X1=k1_xboole_0)), inference(assume_negation,[status(cth)],[t16_funct_1])).
% 0.15/0.38  fof(c_0_8, negated_conjecture, ![X22, X23]:((~v1_relat_1(X22)|~v1_funct_1(X22)|(~v1_relat_1(X23)|~v1_funct_1(X23)|(k1_relat_1(X22)!=esk3_0|k1_relat_1(X23)!=esk3_0|X22=X23)))&esk3_0!=k1_xboole_0), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).
% 0.15/0.38  fof(c_0_9, plain, ![X18, X19]:((((v1_relat_1(esk2_2(X18,X19))|X18=k1_xboole_0)&(v1_funct_1(esk2_2(X18,X19))|X18=k1_xboole_0))&(k1_relat_1(esk2_2(X18,X19))=X18|X18=k1_xboole_0))&(k2_relat_1(esk2_2(X18,X19))=k1_tarski(X19)|X18=k1_xboole_0)), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_funct_1])])])])])).
% 0.15/0.38  cnf(c_0_10, negated_conjecture, (X1=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|k1_relat_1(X1)!=esk3_0|k1_relat_1(X2)!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.15/0.38  cnf(c_0_11, plain, (k1_relat_1(esk2_2(X1,X2))=X1|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.15/0.38  cnf(c_0_12, plain, (v1_relat_1(esk2_2(X1,X2))|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.15/0.38  cnf(c_0_13, plain, (v1_funct_1(esk2_2(X1,X2))|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.15/0.38  cnf(c_0_14, negated_conjecture, (X1=esk2_2(X2,X3)|X2=k1_xboole_0|k1_relat_1(X1)!=esk3_0|X2!=esk3_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12]), c_0_13])).
% 0.15/0.38  cnf(c_0_15, negated_conjecture, (esk2_2(X1,X2)=esk2_2(X3,X4)|X1=k1_xboole_0|X3=k1_xboole_0|X1!=esk3_0|X3!=esk3_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_11]), c_0_12]), c_0_13])).
% 0.15/0.38  cnf(c_0_16, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.15/0.38  fof(c_0_17, plain, ![X16, X17]:((k4_xboole_0(k1_tarski(X16),X17)!=k1_xboole_0|r2_hidden(X16,X17))&(~r2_hidden(X16,X17)|k4_xboole_0(k1_tarski(X16),X17)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t68_zfmisc_1])])).
% 0.15/0.38  fof(c_0_18, plain, ![X4]:(X4=k1_xboole_0|r2_hidden(esk1_1(X4),X4)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.15/0.38  fof(c_0_19, plain, ![X14, X15]:k2_xboole_0(k1_tarski(X14),X15)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 0.15/0.38  fof(c_0_20, plain, ![X6]:k2_xboole_0(X6,k1_xboole_0)=X6, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.15/0.38  cnf(c_0_21, negated_conjecture, (esk2_2(esk3_0,X1)=esk2_2(X2,X3)|X2=k1_xboole_0|X2!=esk3_0), inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_15]), c_0_16])).
% 0.15/0.38  fof(c_0_22, plain, ![X12, X13]:(k4_xboole_0(k1_tarski(X12),k1_tarski(X13))!=k1_xboole_0|X12=X13), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_zfmisc_1])])).
% 0.15/0.38  cnf(c_0_23, plain, (k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.15/0.38  cnf(c_0_24, plain, (X1=k1_xboole_0|r2_hidden(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.15/0.38  cnf(c_0_25, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.15/0.38  cnf(c_0_26, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.15/0.38  cnf(c_0_27, plain, (k2_relat_1(esk2_2(X1,X2))=k1_tarski(X2)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.15/0.38  cnf(c_0_28, negated_conjecture, (esk2_2(esk3_0,X1)=esk2_2(esk3_0,X2)), inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_21]), c_0_16])).
% 0.15/0.38  cnf(c_0_29, plain, (X1=X2|k4_xboole_0(k1_tarski(X1),k1_tarski(X2))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.15/0.38  cnf(c_0_30, plain, (k4_xboole_0(k1_tarski(esk1_1(X1)),X1)=k1_xboole_0|X1=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.15/0.38  cnf(c_0_31, plain, (k1_tarski(X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.15/0.38  cnf(c_0_32, negated_conjecture, (k2_relat_1(esk2_2(esk3_0,X1))=k1_tarski(X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_16])).
% 0.15/0.38  cnf(c_0_33, plain, (esk1_1(k1_tarski(X1))=X1), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])).
% 0.15/0.38  cnf(c_0_34, negated_conjecture, (k1_tarski(X1)=k1_tarski(X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_32]), c_0_16])).
% 0.15/0.38  cnf(c_0_35, negated_conjecture, (X1=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_33])).
% 0.15/0.38  cnf(c_0_36, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_16, c_0_35]), ['proof']).
% 0.15/0.38  # SZS output end CNFRefutation
% 0.15/0.38  # Proof object total steps             : 37
% 0.15/0.38  # Proof object clause steps            : 22
% 0.15/0.38  # Proof object formula steps           : 15
% 0.15/0.38  # Proof object conjectures             : 13
% 0.15/0.38  # Proof object clause conjectures      : 10
% 0.15/0.38  # Proof object formula conjectures     : 3
% 0.15/0.38  # Proof object initial clauses used    : 11
% 0.15/0.38  # Proof object initial formulas used   : 7
% 0.15/0.38  # Proof object generating inferences   : 10
% 0.15/0.38  # Proof object simplifying inferences  : 11
% 0.15/0.38  # Training examples: 0 positive, 0 negative
% 0.15/0.38  # Parsed axioms                        : 10
% 0.15/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.38  # Initial clauses                      : 16
% 0.15/0.38  # Removed in clause preprocessing      : 0
% 0.15/0.38  # Initial clauses in saturation        : 16
% 0.15/0.38  # Processed clauses                    : 67
% 0.15/0.38  # ...of these trivial                  : 3
% 0.15/0.38  # ...subsumed                          : 11
% 0.15/0.38  # ...remaining for further processing  : 53
% 0.15/0.38  # Other redundant clauses eliminated   : 0
% 0.15/0.38  # Clauses deleted for lack of memory   : 0
% 0.15/0.38  # Backward-subsumed                    : 23
% 0.15/0.38  # Backward-rewritten                   : 0
% 0.15/0.38  # Generated clauses                    : 117
% 0.15/0.38  # ...of the previous two non-trivial   : 81
% 0.15/0.38  # Contextual simplify-reflections      : 4
% 0.15/0.38  # Paramodulations                      : 108
% 0.15/0.38  # Factorizations                       : 0
% 0.15/0.38  # Equation resolutions                 : 2
% 0.15/0.38  # Propositional unsat checks           : 0
% 0.15/0.38  #    Propositional check models        : 0
% 0.15/0.38  #    Propositional check unsatisfiable : 0
% 0.15/0.38  #    Propositional clauses             : 0
% 0.15/0.38  #    Propositional clauses after purity: 0
% 0.15/0.38  #    Propositional unsat core size     : 0
% 0.15/0.38  #    Propositional preprocessing time  : 0.000
% 0.15/0.38  #    Propositional encoding time       : 0.000
% 0.15/0.38  #    Propositional solver time         : 0.000
% 0.15/0.38  #    Success case prop preproc time    : 0.000
% 0.15/0.38  #    Success case prop encoding time   : 0.000
% 0.15/0.38  #    Success case prop solver time     : 0.000
% 0.15/0.38  # Current number of processed clauses  : 7
% 0.15/0.38  #    Positive orientable unit clauses  : 6
% 0.15/0.38  #    Positive unorientable unit clauses: 1
% 0.15/0.38  #    Negative unit clauses             : 0
% 0.15/0.38  #    Non-unit-clauses                  : 0
% 0.15/0.38  # Current number of unprocessed clauses: 44
% 0.15/0.38  # ...number of literals in the above   : 64
% 0.15/0.38  # Current number of archived formulas  : 0
% 0.15/0.38  # Current number of archived clauses   : 46
% 0.15/0.38  # Clause-clause subsumption calls (NU) : 44
% 0.15/0.38  # Rec. Clause-clause subsumption calls : 22
% 0.15/0.38  # Non-unit clause-clause subsumptions  : 6
% 0.15/0.38  # Unit Clause-clause subsumption calls : 61
% 0.15/0.38  # Rewrite failures with RHS unbound    : 121
% 0.15/0.38  # BW rewrite match attempts            : 75
% 0.15/0.38  # BW rewrite match successes           : 67
% 0.15/0.38  # Condensation attempts                : 0
% 0.15/0.38  # Condensation successes               : 0
% 0.15/0.38  # Termbank termtop insertions          : 1677
% 0.15/0.38  
% 0.15/0.38  # -------------------------------------------------
% 0.15/0.38  # User time                : 0.027 s
% 0.15/0.38  # System time              : 0.005 s
% 0.15/0.38  # Total time               : 0.032 s
% 0.15/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
