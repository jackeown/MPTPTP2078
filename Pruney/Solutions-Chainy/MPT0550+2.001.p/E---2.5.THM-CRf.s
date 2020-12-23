%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:50:47 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   59 (  95 expanded)
%              Number of clauses        :   33 (  40 expanded)
%              Number of leaves         :   13 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :  142 ( 258 expanded)
%              Number of equality atoms :   43 (  82 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(rc1_xboole_0,axiom,(
    ? [X1] : v1_xboole_0(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t152_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ~ ( X1 != k1_xboole_0
          & r1_tarski(X1,k1_relat_1(X2))
          & k9_relat_1(X2,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(cc1_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(t21_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(t91_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => k1_relat_1(k7_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(c_0_13,plain,(
    ! [X3] :
      ( ~ v1_xboole_0(X3)
      | X3 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

fof(c_0_14,plain,(
    v1_xboole_0(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_xboole_0])])).

fof(c_0_15,plain,(
    ! [X16,X17] :
      ( ( r1_tarski(k1_relat_1(X16),k1_relat_1(X17))
        | ~ r1_tarski(X16,X17)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16) )
      & ( r1_tarski(k2_relat_1(X16),k2_relat_1(X17))
        | ~ r1_tarski(X16,X17)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

fof(c_0_16,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X14)
      | k2_relat_1(k7_relat_1(X14,X13)) = k9_relat_1(X14,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_17,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X11)
      | v1_relat_1(k7_relat_1(X11,X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ~ ( X1 != k1_xboole_0
            & r1_tarski(X1,k1_relat_1(X2))
            & k9_relat_1(X2,X1) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t152_relat_1])).

cnf(c_0_19,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & esk2_0 != k1_xboole_0
    & r1_tarski(esk2_0,k1_relat_1(esk3_0))
    & k9_relat_1(esk3_0,esk2_0) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

fof(c_0_25,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_26,plain,(
    ! [X10] :
      ( ~ v1_xboole_0(X10)
      | v1_relat_1(X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).

cnf(c_0_27,plain,
    ( esk1_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_28,plain,
    ( r1_tarski(k2_relat_1(X1),k9_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k7_relat_1(X2,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( k9_relat_1(esk3_0,esk2_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_20,c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(k2_relat_1(X1),k1_xboole_0)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,k7_relat_1(esk3_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_31])).

fof(c_0_36,plain,(
    ! [X7] : r1_tarski(k1_xboole_0,X7) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_37,plain,(
    ! [X8,X9] :
      ( ( k2_zfmisc_1(X8,X9) != k1_xboole_0
        | X8 = k1_xboole_0
        | X9 = k1_xboole_0 )
      & ( X8 != k1_xboole_0
        | k2_zfmisc_1(X8,X9) = k1_xboole_0 )
      & ( X9 != k1_xboole_0
        | k2_zfmisc_1(X8,X9) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_38,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_39,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_40,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_41,plain,(
    ! [X15] :
      ( ~ v1_relat_1(X15)
      | r1_tarski(X15,k2_zfmisc_1(k1_relat_1(X15),k2_relat_1(X15))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).

cnf(c_0_42,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k2_relat_1(k7_relat_1(esk3_0,esk2_0)),k1_xboole_0)
    | ~ v1_relat_1(k7_relat_1(esk3_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_44,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_46,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X19)
      | ~ r1_tarski(X18,k1_relat_1(X19))
      | k1_relat_1(k7_relat_1(X19,X18)) = X18 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).

cnf(c_0_47,plain,
    ( r1_tarski(k1_relat_1(X1),k1_xboole_0)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk3_0,esk2_0)) = k1_xboole_0
    | ~ v1_relat_1(k7_relat_1(esk3_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])])).

cnf(c_0_50,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_51,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_47]),c_0_44])])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k7_relat_1(esk3_0,esk2_0),k1_xboole_0)
    | ~ v1_relat_1(k7_relat_1(esk3_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])).

cnf(c_0_54,plain,
    ( k1_xboole_0 = X1
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k7_relat_1(X2,X1),k1_xboole_0)
    | ~ r1_tarski(X1,k1_relat_1(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_23])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k7_relat_1(esk3_0,esk2_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_23]),c_0_30])])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(esk2_0,k1_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_57,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_30]),c_0_56])]),c_0_57]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:27:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.028 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.20/0.39  fof(rc1_xboole_0, axiom, ?[X1]:v1_xboole_0(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 0.20/0.39  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 0.20/0.39  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.20/0.39  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.20/0.39  fof(t152_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>~(((X1!=k1_xboole_0&r1_tarski(X1,k1_relat_1(X2)))&k9_relat_1(X2,X1)=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_relat_1)).
% 0.20/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.39  fof(cc1_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 0.20/0.39  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.39  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.20/0.39  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.20/0.39  fof(t21_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 0.20/0.39  fof(t91_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>k1_relat_1(k7_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 0.20/0.39  fof(c_0_13, plain, ![X3]:(~v1_xboole_0(X3)|X3=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.20/0.39  fof(c_0_14, plain, v1_xboole_0(esk1_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_xboole_0])])).
% 0.20/0.39  fof(c_0_15, plain, ![X16, X17]:((r1_tarski(k1_relat_1(X16),k1_relat_1(X17))|~r1_tarski(X16,X17)|~v1_relat_1(X17)|~v1_relat_1(X16))&(r1_tarski(k2_relat_1(X16),k2_relat_1(X17))|~r1_tarski(X16,X17)|~v1_relat_1(X17)|~v1_relat_1(X16))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.20/0.39  fof(c_0_16, plain, ![X13, X14]:(~v1_relat_1(X14)|k2_relat_1(k7_relat_1(X14,X13))=k9_relat_1(X14,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.20/0.39  fof(c_0_17, plain, ![X11, X12]:(~v1_relat_1(X11)|v1_relat_1(k7_relat_1(X11,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.20/0.39  fof(c_0_18, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>~(((X1!=k1_xboole_0&r1_tarski(X1,k1_relat_1(X2)))&k9_relat_1(X2,X1)=k1_xboole_0)))), inference(assume_negation,[status(cth)],[t152_relat_1])).
% 0.20/0.39  cnf(c_0_19, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.39  cnf(c_0_20, plain, (v1_xboole_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.39  cnf(c_0_21, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.39  cnf(c_0_22, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  cnf(c_0_23, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.39  fof(c_0_24, negated_conjecture, (v1_relat_1(esk3_0)&((esk2_0!=k1_xboole_0&r1_tarski(esk2_0,k1_relat_1(esk3_0)))&k9_relat_1(esk3_0,esk2_0)=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.20/0.39  fof(c_0_25, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.39  fof(c_0_26, plain, ![X10]:(~v1_xboole_0(X10)|v1_relat_1(X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).
% 0.20/0.39  cnf(c_0_27, plain, (esk1_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.39  cnf(c_0_28, plain, (r1_tarski(k2_relat_1(X1),k9_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,k7_relat_1(X2,X3))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])).
% 0.20/0.39  cnf(c_0_29, negated_conjecture, (k9_relat_1(esk3_0,esk2_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.39  cnf(c_0_30, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.39  cnf(c_0_31, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.39  cnf(c_0_32, plain, (v1_relat_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.39  cnf(c_0_33, plain, (v1_xboole_0(k1_xboole_0)), inference(rw,[status(thm)],[c_0_20, c_0_27])).
% 0.20/0.39  cnf(c_0_34, negated_conjecture, (r1_tarski(k2_relat_1(X1),k1_xboole_0)|~v1_relat_1(X1)|~r1_tarski(X1,k7_relat_1(esk3_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])])).
% 0.20/0.39  cnf(c_0_35, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_31])).
% 0.20/0.39  fof(c_0_36, plain, ![X7]:r1_tarski(k1_xboole_0,X7), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.39  fof(c_0_37, plain, ![X8, X9]:((k2_zfmisc_1(X8,X9)!=k1_xboole_0|(X8=k1_xboole_0|X9=k1_xboole_0))&((X8!=k1_xboole_0|k2_zfmisc_1(X8,X9)=k1_xboole_0)&(X9!=k1_xboole_0|k2_zfmisc_1(X8,X9)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.20/0.39  cnf(c_0_38, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.39  cnf(c_0_39, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.20/0.39  cnf(c_0_40, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.39  fof(c_0_41, plain, ![X15]:(~v1_relat_1(X15)|r1_tarski(X15,k2_zfmisc_1(k1_relat_1(X15),k2_relat_1(X15)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).
% 0.20/0.39  cnf(c_0_42, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.39  cnf(c_0_43, negated_conjecture, (r1_tarski(k2_relat_1(k7_relat_1(esk3_0,esk2_0)),k1_xboole_0)|~v1_relat_1(k7_relat_1(esk3_0,esk2_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.39  cnf(c_0_44, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.39  cnf(c_0_45, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.39  fof(c_0_46, plain, ![X18, X19]:(~v1_relat_1(X19)|(~r1_tarski(X18,k1_relat_1(X19))|k1_relat_1(k7_relat_1(X19,X18))=X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).
% 0.20/0.39  cnf(c_0_47, plain, (r1_tarski(k1_relat_1(X1),k1_xboole_0)|~v1_relat_1(X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])])).
% 0.20/0.39  cnf(c_0_48, plain, (r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.39  cnf(c_0_49, negated_conjecture, (k2_relat_1(k7_relat_1(esk3_0,esk2_0))=k1_xboole_0|~v1_relat_1(k7_relat_1(esk3_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])])).
% 0.20/0.39  cnf(c_0_50, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_45])).
% 0.20/0.39  cnf(c_0_51, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.39  cnf(c_0_52, plain, (k1_relat_1(X1)=k1_xboole_0|~v1_relat_1(X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_47]), c_0_44])])).
% 0.20/0.39  cnf(c_0_53, negated_conjecture, (r1_tarski(k7_relat_1(esk3_0,esk2_0),k1_xboole_0)|~v1_relat_1(k7_relat_1(esk3_0,esk2_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])).
% 0.20/0.39  cnf(c_0_54, plain, (k1_xboole_0=X1|~v1_relat_1(X2)|~r1_tarski(k7_relat_1(X2,X1),k1_xboole_0)|~r1_tarski(X1,k1_relat_1(X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_23])).
% 0.20/0.39  cnf(c_0_55, negated_conjecture, (r1_tarski(k7_relat_1(esk3_0,esk2_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_23]), c_0_30])])).
% 0.20/0.39  cnf(c_0_56, negated_conjecture, (r1_tarski(esk2_0,k1_relat_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.39  cnf(c_0_57, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.39  cnf(c_0_58, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_30]), c_0_56])]), c_0_57]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 59
% 0.20/0.39  # Proof object clause steps            : 33
% 0.20/0.39  # Proof object formula steps           : 26
% 0.20/0.39  # Proof object conjectures             : 13
% 0.20/0.39  # Proof object clause conjectures      : 10
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 18
% 0.20/0.39  # Proof object initial formulas used   : 13
% 0.20/0.39  # Proof object generating inferences   : 12
% 0.20/0.39  # Proof object simplifying inferences  : 20
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 13
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 22
% 0.20/0.39  # Removed in clause preprocessing      : 0
% 0.20/0.39  # Initial clauses in saturation        : 22
% 0.20/0.39  # Processed clauses                    : 130
% 0.20/0.39  # ...of these trivial                  : 0
% 0.20/0.39  # ...subsumed                          : 39
% 0.20/0.39  # ...remaining for further processing  : 91
% 0.20/0.39  # Other redundant clauses eliminated   : 4
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 0
% 0.20/0.39  # Backward-rewritten                   : 2
% 0.20/0.39  # Generated clauses                    : 251
% 0.20/0.39  # ...of the previous two non-trivial   : 188
% 0.20/0.39  # Contextual simplify-reflections      : 7
% 0.20/0.39  # Paramodulations                      : 247
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 4
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 64
% 0.20/0.39  #    Positive orientable unit clauses  : 13
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 2
% 0.20/0.39  #    Non-unit-clauses                  : 49
% 0.20/0.39  # Current number of unprocessed clauses: 90
% 0.20/0.39  # ...number of literals in the above   : 542
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 23
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 1161
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 383
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 39
% 0.20/0.39  # Unit Clause-clause subsumption calls : 9
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 4
% 0.20/0.39  # BW rewrite match successes           : 2
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 5811
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.034 s
% 0.20/0.39  # System time              : 0.005 s
% 0.20/0.39  # Total time               : 0.040 s
% 0.20/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
