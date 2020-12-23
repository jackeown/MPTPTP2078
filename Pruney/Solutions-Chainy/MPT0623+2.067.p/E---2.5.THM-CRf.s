%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:14 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 104 expanded)
%              Number of clauses        :   33 (  44 expanded)
%              Number of leaves         :   13 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :  147 ( 352 expanded)
%              Number of equality atoms :   71 ( 172 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t18_funct_1,conjecture,(
    ! [X1,X2] :
      ~ ( ~ ( X1 = k1_xboole_0
            & X2 != k1_xboole_0 )
        & ! [X3] :
            ( ( v1_relat_1(X3)
              & v1_funct_1(X3) )
           => ~ ( X2 = k1_relat_1(X3)
                & r1_tarski(k2_relat_1(X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

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

fof(t65_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k1_relat_1(X1) = k1_xboole_0
      <=> k2_relat_1(X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(s3_funct_1__e2_25__funct_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( v1_relat_1(X2)
      & v1_funct_1(X2)
      & k1_relat_1(X2) = X1
      & ! [X3] :
          ( r2_hidden(X3,X1)
         => k1_funct_1(X2,X3) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2] :
        ~ ( ~ ( X1 = k1_xboole_0
              & X2 != k1_xboole_0 )
          & ! [X3] :
              ( ( v1_relat_1(X3)
                & v1_funct_1(X3) )
             => ~ ( X2 = k1_relat_1(X3)
                  & r1_tarski(k2_relat_1(X3),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t18_funct_1])).

fof(c_0_10,negated_conjecture,(
    ! [X23] :
      ( ( esk4_0 != k1_xboole_0
        | esk5_0 = k1_xboole_0 )
      & ( ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23)
        | esk5_0 != k1_relat_1(X23)
        | ~ r1_tarski(k2_relat_1(X23),esk4_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).

fof(c_0_11,plain,(
    ! [X18,X19] :
      ( ( v1_relat_1(esk3_2(X18,X19))
        | X18 = k1_xboole_0 )
      & ( v1_funct_1(esk3_2(X18,X19))
        | X18 = k1_xboole_0 )
      & ( k1_relat_1(esk3_2(X18,X19)) = X18
        | X18 = k1_xboole_0 )
      & ( k2_relat_1(esk3_2(X18,X19)) = k1_tarski(X19)
        | X18 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_funct_1])])])])])).

fof(c_0_12,plain,(
    ! [X14] :
      ( ( k1_relat_1(X14) != k1_xboole_0
        | k2_relat_1(X14) = k1_xboole_0
        | ~ v1_relat_1(X14) )
      & ( k2_relat_1(X14) != k1_xboole_0
        | k1_relat_1(X14) = k1_xboole_0
        | ~ v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).

fof(c_0_13,plain,(
    ! [X7] : r1_tarski(k1_xboole_0,X7) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_14,negated_conjecture,
    ( ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | esk5_0 != k1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k2_relat_1(esk3_2(X1,X2)) = k1_tarski(X2)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( v1_relat_1(esk3_2(X1,X2))
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( v1_funct_1(esk3_2(X1,X2))
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_18,plain,(
    ! [X8,X9] :
      ( ( ~ r1_tarski(k1_tarski(X8),X9)
        | r2_hidden(X8,X9) )
      & ( ~ r2_hidden(X8,X9)
        | r1_tarski(k1_tarski(X8),X9) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

cnf(c_0_19,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_21,plain,(
    ! [X15,X17] :
      ( v1_relat_1(esk2_1(X15))
      & v1_funct_1(esk2_1(X15))
      & k1_relat_1(esk2_1(X15)) = X15
      & ( ~ r2_hidden(X17,X15)
        | k1_funct_1(esk2_1(X15),X17) = k1_xboole_0 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_25__funct_1])])])])).

fof(c_0_22,plain,(
    ! [X12,X13] : ~ r2_hidden(X12,k2_zfmisc_1(X12,X13)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

fof(c_0_23,plain,(
    ! [X10,X11] :
      ( ( k2_zfmisc_1(X10,X11) != k1_xboole_0
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0 )
      & ( X10 != k1_xboole_0
        | k2_zfmisc_1(X10,X11) = k1_xboole_0 )
      & ( X11 != k1_xboole_0
        | k2_zfmisc_1(X10,X11) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_24,plain,
    ( ~ epred1_0
  <=> ! [X2] : X2 != k1_xboole_0 ),
    introduced(definition)).

cnf(c_0_25,negated_conjecture,
    ( X1 = k1_xboole_0
    | k1_relat_1(esk3_2(X1,X2)) != esk5_0
    | ~ r1_tarski(k1_tarski(X2),esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17])).

cnf(c_0_26,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( k1_relat_1(X1) != esk5_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_19]),c_0_20])])).

cnf(c_0_28,plain,
    ( v1_funct_1(esk2_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k1_relat_1(esk2_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( v1_relat_1(esk2_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_31,plain,
    ( ~ epred3_0
  <=> ! [X1] : X1 != esk5_0 ),
    introduced(definition)).

fof(c_0_32,plain,
    ( ~ epred2_0
  <=> ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    introduced(definition)).

cnf(c_0_33,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( epred1_0
    | X1 != k1_xboole_0 ),
    inference(split_equiv,[status(thm)],[c_0_24])).

fof(c_0_36,plain,
    ( ~ epred4_0
  <=> ! [X2] : ~ r2_hidden(X2,esk4_0) ),
    introduced(definition)).

cnf(c_0_37,negated_conjecture,
    ( X1 = k1_xboole_0
    | k1_relat_1(esk3_2(X1,X2)) != esk5_0
    | ~ r2_hidden(X2,esk4_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_38,plain,
    ( k1_relat_1(esk3_2(X1,X2)) = X1
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_39,negated_conjecture,
    ( X1 != esk5_0
    | X1 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_29]),c_0_30])])).

cnf(c_0_40,negated_conjecture,
    ( epred3_0
    | X1 != esk5_0 ),
    inference(split_equiv,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( ~ epred2_0
    | ~ epred1_0 ),
    inference(apply_def,[status(thm)],[inference(apply_def,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_24]),c_0_32])).

cnf(c_0_42,plain,
    ( epred1_0 ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( ~ epred4_0
    | ~ epred3_0 ),
    inference(apply_def,[status(thm)],[inference(apply_def,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_31]),c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( epred3_0 ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_45,plain,
    ( ~ epred2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42])])).

fof(c_0_46,plain,(
    ! [X4,X5] :
      ( ( ~ r2_hidden(esk1_2(X4,X5),X4)
        | ~ r2_hidden(esk1_2(X4,X5),X5)
        | X4 = X5 )
      & ( r2_hidden(esk1_2(X4,X5),X4)
        | r2_hidden(esk1_2(X4,X5),X5)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

cnf(c_0_47,negated_conjecture,
    ( ~ epred4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44])])).

cnf(c_0_48,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(split_equiv,[status(thm)],[c_0_32]),c_0_45])).

cnf(c_0_49,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r2_hidden(esk1_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( ~ r2_hidden(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(split_equiv,[status(thm)],[c_0_36]),c_0_47])).

cnf(c_0_51,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk1_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_52,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_53,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_54,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53])]),c_0_54]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:16:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.35  # AutoSched0-Mode selected heuristic G_E___103_C18_F1_PI_AE_Q4_CS_SP_S0Y
% 0.12/0.35  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.35  #
% 0.12/0.35  # Preprocessing time       : 0.018 s
% 0.12/0.35  
% 0.12/0.35  # Proof found!
% 0.12/0.35  # SZS status Theorem
% 0.12/0.35  # SZS output start CNFRefutation
% 0.12/0.35  fof(t18_funct_1, conjecture, ![X1, X2]:~((~((X1=k1_xboole_0&X2!=k1_xboole_0))&![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>~((X2=k1_relat_1(X3)&r1_tarski(k2_relat_1(X3),X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 0.12/0.35  fof(t15_funct_1, axiom, ![X1]:(X1!=k1_xboole_0=>![X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&k2_relat_1(X3)=k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_funct_1)).
% 0.12/0.35  fof(t65_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k1_relat_1(X1)=k1_xboole_0<=>k2_relat_1(X1)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 0.12/0.35  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.12/0.35  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.12/0.35  fof(s3_funct_1__e2_25__funct_1, axiom, ![X1]:?[X2]:(((v1_relat_1(X2)&v1_funct_1(X2))&k1_relat_1(X2)=X1)&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 0.12/0.35  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.12/0.35  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.12/0.35  fof(t2_tarski, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)<=>r2_hidden(X3,X2))=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 0.12/0.35  fof(c_0_9, negated_conjecture, ~(![X1, X2]:~((~((X1=k1_xboole_0&X2!=k1_xboole_0))&![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>~((X2=k1_relat_1(X3)&r1_tarski(k2_relat_1(X3),X1))))))), inference(assume_negation,[status(cth)],[t18_funct_1])).
% 0.12/0.35  fof(c_0_10, negated_conjecture, ![X23]:((esk4_0!=k1_xboole_0|esk5_0=k1_xboole_0)&(~v1_relat_1(X23)|~v1_funct_1(X23)|(esk5_0!=k1_relat_1(X23)|~r1_tarski(k2_relat_1(X23),esk4_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).
% 0.12/0.35  fof(c_0_11, plain, ![X18, X19]:((((v1_relat_1(esk3_2(X18,X19))|X18=k1_xboole_0)&(v1_funct_1(esk3_2(X18,X19))|X18=k1_xboole_0))&(k1_relat_1(esk3_2(X18,X19))=X18|X18=k1_xboole_0))&(k2_relat_1(esk3_2(X18,X19))=k1_tarski(X19)|X18=k1_xboole_0)), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_funct_1])])])])])).
% 0.12/0.35  fof(c_0_12, plain, ![X14]:((k1_relat_1(X14)!=k1_xboole_0|k2_relat_1(X14)=k1_xboole_0|~v1_relat_1(X14))&(k2_relat_1(X14)!=k1_xboole_0|k1_relat_1(X14)=k1_xboole_0|~v1_relat_1(X14))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).
% 0.12/0.35  fof(c_0_13, plain, ![X7]:r1_tarski(k1_xboole_0,X7), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.12/0.35  cnf(c_0_14, negated_conjecture, (~v1_relat_1(X1)|~v1_funct_1(X1)|esk5_0!=k1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.35  cnf(c_0_15, plain, (k2_relat_1(esk3_2(X1,X2))=k1_tarski(X2)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.35  cnf(c_0_16, plain, (v1_relat_1(esk3_2(X1,X2))|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.35  cnf(c_0_17, plain, (v1_funct_1(esk3_2(X1,X2))|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.35  fof(c_0_18, plain, ![X8, X9]:((~r1_tarski(k1_tarski(X8),X9)|r2_hidden(X8,X9))&(~r2_hidden(X8,X9)|r1_tarski(k1_tarski(X8),X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.12/0.35  cnf(c_0_19, plain, (k2_relat_1(X1)=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.35  cnf(c_0_20, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.35  fof(c_0_21, plain, ![X15, X17]:(((v1_relat_1(esk2_1(X15))&v1_funct_1(esk2_1(X15)))&k1_relat_1(esk2_1(X15))=X15)&(~r2_hidden(X17,X15)|k1_funct_1(esk2_1(X15),X17)=k1_xboole_0)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_25__funct_1])])])])).
% 0.12/0.35  fof(c_0_22, plain, ![X12, X13]:~r2_hidden(X12,k2_zfmisc_1(X12,X13)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.12/0.35  fof(c_0_23, plain, ![X10, X11]:((k2_zfmisc_1(X10,X11)!=k1_xboole_0|(X10=k1_xboole_0|X11=k1_xboole_0))&((X10!=k1_xboole_0|k2_zfmisc_1(X10,X11)=k1_xboole_0)&(X11!=k1_xboole_0|k2_zfmisc_1(X10,X11)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.12/0.35  fof(c_0_24, plain, (~epred1_0<=>![X2]:X2!=k1_xboole_0), introduced(definition)).
% 0.12/0.35  cnf(c_0_25, negated_conjecture, (X1=k1_xboole_0|k1_relat_1(esk3_2(X1,X2))!=esk5_0|~r1_tarski(k1_tarski(X2),esk4_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_17])).
% 0.12/0.35  cnf(c_0_26, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.35  cnf(c_0_27, negated_conjecture, (k1_relat_1(X1)!=esk5_0|k1_relat_1(X1)!=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_19]), c_0_20])])).
% 0.12/0.35  cnf(c_0_28, plain, (v1_funct_1(esk2_1(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.35  cnf(c_0_29, plain, (k1_relat_1(esk2_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.35  cnf(c_0_30, plain, (v1_relat_1(esk2_1(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.35  fof(c_0_31, plain, (~epred3_0<=>![X1]:X1!=esk5_0), introduced(definition)).
% 0.12/0.35  fof(c_0_32, plain, (~epred2_0<=>![X1]:~r2_hidden(X1,k1_xboole_0)), introduced(definition)).
% 0.12/0.35  cnf(c_0_33, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.35  cnf(c_0_34, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.35  cnf(c_0_35, plain, (epred1_0|X1!=k1_xboole_0), inference(split_equiv,[status(thm)],[c_0_24])).
% 0.12/0.35  fof(c_0_36, plain, (~epred4_0<=>![X2]:~r2_hidden(X2,esk4_0)), introduced(definition)).
% 0.12/0.35  cnf(c_0_37, negated_conjecture, (X1=k1_xboole_0|k1_relat_1(esk3_2(X1,X2))!=esk5_0|~r2_hidden(X2,esk4_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.12/0.35  cnf(c_0_38, plain, (k1_relat_1(esk3_2(X1,X2))=X1|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.35  cnf(c_0_39, negated_conjecture, (X1!=esk5_0|X1!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_29]), c_0_30])])).
% 0.12/0.35  cnf(c_0_40, negated_conjecture, (epred3_0|X1!=esk5_0), inference(split_equiv,[status(thm)],[c_0_31])).
% 0.12/0.35  cnf(c_0_41, plain, (~epred2_0|~epred1_0), inference(apply_def,[status(thm)],[inference(apply_def,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_24]), c_0_32])).
% 0.12/0.35  cnf(c_0_42, plain, (epred1_0), inference(er,[status(thm)],[c_0_35])).
% 0.12/0.35  cnf(c_0_43, negated_conjecture, (~epred4_0|~epred3_0), inference(apply_def,[status(thm)],[inference(apply_def,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_31]), c_0_36])).
% 0.12/0.35  cnf(c_0_44, negated_conjecture, (epred3_0), inference(er,[status(thm)],[c_0_40])).
% 0.12/0.35  cnf(c_0_45, plain, (~epred2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42])])).
% 0.12/0.35  fof(c_0_46, plain, ![X4, X5]:((~r2_hidden(esk1_2(X4,X5),X4)|~r2_hidden(esk1_2(X4,X5),X5)|X4=X5)&(r2_hidden(esk1_2(X4,X5),X4)|r2_hidden(esk1_2(X4,X5),X5)|X4=X5)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).
% 0.12/0.35  cnf(c_0_47, negated_conjecture, (~epred4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44])])).
% 0.12/0.35  cnf(c_0_48, plain, (~r2_hidden(X1,k1_xboole_0)), inference(sr,[status(thm)],[inference(split_equiv,[status(thm)],[c_0_32]), c_0_45])).
% 0.12/0.35  cnf(c_0_49, plain, (r2_hidden(esk1_2(X1,X2),X1)|r2_hidden(esk1_2(X1,X2),X2)|X1=X2), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.12/0.35  cnf(c_0_50, negated_conjecture, (~r2_hidden(X1,esk4_0)), inference(sr,[status(thm)],[inference(split_equiv,[status(thm)],[c_0_36]), c_0_47])).
% 0.12/0.35  cnf(c_0_51, plain, (k1_xboole_0=X1|r2_hidden(esk1_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.12/0.35  cnf(c_0_52, negated_conjecture, (esk5_0=k1_xboole_0|esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.35  cnf(c_0_53, negated_conjecture, (esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.12/0.35  cnf(c_0_54, negated_conjecture, (esk5_0!=k1_xboole_0), inference(er,[status(thm)],[c_0_39])).
% 0.12/0.35  cnf(c_0_55, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_53])]), c_0_54]), ['proof']).
% 0.12/0.35  # SZS output end CNFRefutation
% 0.12/0.35  # Proof object total steps             : 56
% 0.12/0.35  # Proof object clause steps            : 33
% 0.12/0.35  # Proof object formula steps           : 23
% 0.12/0.35  # Proof object conjectures             : 17
% 0.12/0.35  # Proof object clause conjectures      : 14
% 0.12/0.35  # Proof object formula conjectures     : 3
% 0.12/0.35  # Proof object initial clauses used    : 17
% 0.12/0.35  # Proof object initial formulas used   : 9
% 0.12/0.35  # Proof object generating inferences   : 11
% 0.12/0.35  # Proof object simplifying inferences  : 22
% 0.12/0.35  # Training examples: 0 positive, 0 negative
% 0.12/0.35  # Parsed axioms                        : 9
% 0.12/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.35  # Initial clauses                      : 21
% 0.12/0.35  # Removed in clause preprocessing      : 0
% 0.12/0.35  # Initial clauses in saturation        : 21
% 0.12/0.35  # Processed clauses                    : 44
% 0.12/0.35  # ...of these trivial                  : 0
% 0.12/0.35  # ...subsumed                          : 0
% 0.12/0.35  # ...remaining for further processing  : 44
% 0.12/0.35  # Other redundant clauses eliminated   : 0
% 0.12/0.35  # Clauses deleted for lack of memory   : 0
% 0.12/0.35  # Backward-subsumed                    : 2
% 0.12/0.35  # Backward-rewritten                   : 9
% 0.12/0.35  # Generated clauses                    : 36
% 0.12/0.35  # ...of the previous two non-trivial   : 34
% 0.12/0.35  # Contextual simplify-reflections      : 6
% 0.12/0.35  # Paramodulations                      : 25
% 0.12/0.35  # Factorizations                       : 2
% 0.12/0.35  # Equation resolutions                 : 3
% 0.12/0.35  # Propositional unsat checks           : 0
% 0.12/0.35  #    Propositional check models        : 0
% 0.12/0.35  #    Propositional check unsatisfiable : 0
% 0.12/0.35  #    Propositional clauses             : 0
% 0.12/0.35  #    Propositional clauses after purity: 0
% 0.12/0.35  #    Propositional unsat core size     : 0
% 0.12/0.35  #    Propositional preprocessing time  : 0.000
% 0.12/0.35  #    Propositional encoding time       : 0.000
% 0.12/0.35  #    Propositional solver time         : 0.000
% 0.12/0.35  #    Success case prop preproc time    : 0.000
% 0.12/0.35  #    Success case prop encoding time   : 0.000
% 0.12/0.35  #    Success case prop solver time     : 0.000
% 0.12/0.35  # Current number of processed clauses  : 31
% 0.12/0.35  #    Positive orientable unit clauses  : 7
% 0.12/0.35  #    Positive unorientable unit clauses: 0
% 0.12/0.35  #    Negative unit clauses             : 5
% 0.12/0.35  #    Non-unit-clauses                  : 19
% 0.12/0.35  # Current number of unprocessed clauses: 6
% 0.12/0.35  # ...number of literals in the above   : 14
% 0.12/0.35  # Current number of archived formulas  : 0
% 0.12/0.35  # Current number of archived clauses   : 11
% 0.12/0.35  # Clause-clause subsumption calls (NU) : 190
% 0.12/0.35  # Rec. Clause-clause subsumption calls : 132
% 0.12/0.35  # Non-unit clause-clause subsumptions  : 8
% 0.12/0.35  # Unit Clause-clause subsumption calls : 78
% 0.12/0.35  # Rewrite failures with RHS unbound    : 0
% 0.12/0.35  # BW rewrite match attempts            : 3
% 0.12/0.35  # BW rewrite match successes           : 3
% 0.12/0.35  # Condensation attempts                : 0
% 0.12/0.35  # Condensation successes               : 0
% 0.12/0.35  # Termbank termtop insertions          : 1408
% 0.12/0.35  
% 0.12/0.35  # -------------------------------------------------
% 0.12/0.35  # User time                : 0.017 s
% 0.12/0.35  # System time              : 0.005 s
% 0.12/0.35  # Total time               : 0.023 s
% 0.12/0.35  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
