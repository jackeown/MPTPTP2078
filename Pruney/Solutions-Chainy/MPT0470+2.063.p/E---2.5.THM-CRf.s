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
% DateTime   : Thu Dec  3 10:49:03 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   30 (  81 expanded)
%              Number of clauses        :   18 (  40 expanded)
%              Number of leaves         :    6 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :  111 ( 253 expanded)
%              Number of equality atoms :   36 (  94 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   38 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(cc1_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(d8_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( X3 = k5_relat_1(X1,X2)
              <=> ! [X4,X5] :
                    ( r2_hidden(k4_tarski(X4,X5),X3)
                  <=> ? [X6] :
                        ( r2_hidden(k4_tarski(X4,X6),X1)
                        & r2_hidden(k4_tarski(X6,X5),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t62_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
        & k5_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

fof(c_0_6,plain,(
    ! [X7,X8] :
      ( ( k2_zfmisc_1(X7,X8) != k1_xboole_0
        | X7 = k1_xboole_0
        | X8 = k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k2_zfmisc_1(X7,X8) = k1_xboole_0 )
      & ( X8 != k1_xboole_0
        | k2_zfmisc_1(X7,X8) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_7,plain,(
    ! [X11] :
      ( ~ v1_xboole_0(X11)
      | v1_relat_1(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).

fof(c_0_8,plain,(
    ! [X9,X10] : ~ r2_hidden(X9,k2_zfmisc_1(X9,X10)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_9,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,plain,(
    ! [X12,X13,X14,X15,X16,X18,X19,X20,X23] :
      ( ( r2_hidden(k4_tarski(X15,esk1_5(X12,X13,X14,X15,X16)),X12)
        | ~ r2_hidden(k4_tarski(X15,X16),X14)
        | X14 != k5_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13)
        | ~ v1_relat_1(X12) )
      & ( r2_hidden(k4_tarski(esk1_5(X12,X13,X14,X15,X16),X16),X13)
        | ~ r2_hidden(k4_tarski(X15,X16),X14)
        | X14 != k5_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13)
        | ~ v1_relat_1(X12) )
      & ( ~ r2_hidden(k4_tarski(X18,X20),X12)
        | ~ r2_hidden(k4_tarski(X20,X19),X13)
        | r2_hidden(k4_tarski(X18,X19),X14)
        | X14 != k5_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13)
        | ~ v1_relat_1(X12) )
      & ( ~ r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X14)
        | ~ r2_hidden(k4_tarski(esk2_3(X12,X13,X14),X23),X12)
        | ~ r2_hidden(k4_tarski(X23,esk3_3(X12,X13,X14)),X13)
        | X14 = k5_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13)
        | ~ v1_relat_1(X12) )
      & ( r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk4_3(X12,X13,X14)),X12)
        | r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X14)
        | X14 = k5_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13)
        | ~ v1_relat_1(X12) )
      & ( r2_hidden(k4_tarski(esk4_3(X12,X13,X14),esk3_3(X12,X13,X14)),X13)
        | r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X14)
        | X14 = k5_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13)
        | ~ v1_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).

cnf(c_0_11,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_13,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_9])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
          & k5_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t62_relat_1])).

cnf(c_0_16,plain,
    ( r2_hidden(k4_tarski(esk2_3(X1,X2,X3),esk4_3(X1,X2,X3)),X1)
    | r2_hidden(k4_tarski(esk2_3(X1,X2,X3),esk3_3(X1,X2,X3)),X3)
    | X3 = k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_19,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & ( k5_relat_1(k1_xboole_0,esk5_0) != k1_xboole_0
      | k5_relat_1(esk5_0,k1_xboole_0) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

cnf(c_0_20,plain,
    ( k5_relat_1(X1,X2) = k1_xboole_0
    | r2_hidden(k4_tarski(esk2_3(X1,X2,k1_xboole_0),esk4_3(X1,X2,k1_xboole_0)),X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( k5_relat_1(X1,esk5_0) = k1_xboole_0
    | r2_hidden(k4_tarski(esk2_3(X1,esk5_0,k1_xboole_0),esk4_3(X1,esk5_0,k1_xboole_0)),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_23,plain,
    ( r2_hidden(k4_tarski(esk4_3(X1,X2,X3),esk3_3(X1,X2,X3)),X2)
    | r2_hidden(k4_tarski(esk2_3(X1,X2,X3),esk3_3(X1,X2,X3)),X3)
    | X3 = k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_24,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk5_0) != k1_xboole_0
    | k5_relat_1(esk5_0,k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk5_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_17]),c_0_18])).

cnf(c_0_26,plain,
    ( k5_relat_1(X1,X2) = k1_xboole_0
    | r2_hidden(k4_tarski(esk4_3(X1,X2,k1_xboole_0),esk3_3(X1,X2,k1_xboole_0)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_17]),c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( k5_relat_1(esk5_0,k1_xboole_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25])])).

cnf(c_0_28,plain,
    ( k5_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_17]),c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_21])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:10:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.39  #
% 0.21/0.39  # Preprocessing time       : 0.026 s
% 0.21/0.39  # Presaturation interreduction done
% 0.21/0.39  
% 0.21/0.39  # Proof found!
% 0.21/0.39  # SZS status Theorem
% 0.21/0.39  # SZS output start CNFRefutation
% 0.21/0.39  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.21/0.39  fof(cc1_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 0.21/0.39  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.21/0.39  fof(d8_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(X3=k5_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>?[X6]:(r2_hidden(k4_tarski(X4,X6),X1)&r2_hidden(k4_tarski(X6,X5),X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_relat_1)).
% 0.21/0.39  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.21/0.39  fof(t62_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>(k5_relat_1(k1_xboole_0,X1)=k1_xboole_0&k5_relat_1(X1,k1_xboole_0)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 0.21/0.39  fof(c_0_6, plain, ![X7, X8]:((k2_zfmisc_1(X7,X8)!=k1_xboole_0|(X7=k1_xboole_0|X8=k1_xboole_0))&((X7!=k1_xboole_0|k2_zfmisc_1(X7,X8)=k1_xboole_0)&(X8!=k1_xboole_0|k2_zfmisc_1(X7,X8)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.21/0.39  fof(c_0_7, plain, ![X11]:(~v1_xboole_0(X11)|v1_relat_1(X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).
% 0.21/0.39  fof(c_0_8, plain, ![X9, X10]:~r2_hidden(X9,k2_zfmisc_1(X9,X10)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.21/0.39  cnf(c_0_9, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.39  fof(c_0_10, plain, ![X12, X13, X14, X15, X16, X18, X19, X20, X23]:((((r2_hidden(k4_tarski(X15,esk1_5(X12,X13,X14,X15,X16)),X12)|~r2_hidden(k4_tarski(X15,X16),X14)|X14!=k5_relat_1(X12,X13)|~v1_relat_1(X14)|~v1_relat_1(X13)|~v1_relat_1(X12))&(r2_hidden(k4_tarski(esk1_5(X12,X13,X14,X15,X16),X16),X13)|~r2_hidden(k4_tarski(X15,X16),X14)|X14!=k5_relat_1(X12,X13)|~v1_relat_1(X14)|~v1_relat_1(X13)|~v1_relat_1(X12)))&(~r2_hidden(k4_tarski(X18,X20),X12)|~r2_hidden(k4_tarski(X20,X19),X13)|r2_hidden(k4_tarski(X18,X19),X14)|X14!=k5_relat_1(X12,X13)|~v1_relat_1(X14)|~v1_relat_1(X13)|~v1_relat_1(X12)))&((~r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X14)|(~r2_hidden(k4_tarski(esk2_3(X12,X13,X14),X23),X12)|~r2_hidden(k4_tarski(X23,esk3_3(X12,X13,X14)),X13))|X14=k5_relat_1(X12,X13)|~v1_relat_1(X14)|~v1_relat_1(X13)|~v1_relat_1(X12))&((r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk4_3(X12,X13,X14)),X12)|r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X14)|X14=k5_relat_1(X12,X13)|~v1_relat_1(X14)|~v1_relat_1(X13)|~v1_relat_1(X12))&(r2_hidden(k4_tarski(esk4_3(X12,X13,X14),esk3_3(X12,X13,X14)),X13)|r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X14)|X14=k5_relat_1(X12,X13)|~v1_relat_1(X14)|~v1_relat_1(X13)|~v1_relat_1(X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).
% 0.21/0.39  cnf(c_0_11, plain, (v1_relat_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.39  cnf(c_0_12, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.21/0.39  cnf(c_0_13, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.39  cnf(c_0_14, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_9])).
% 0.21/0.39  fof(c_0_15, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>(k5_relat_1(k1_xboole_0,X1)=k1_xboole_0&k5_relat_1(X1,k1_xboole_0)=k1_xboole_0))), inference(assume_negation,[status(cth)],[t62_relat_1])).
% 0.21/0.39  cnf(c_0_16, plain, (r2_hidden(k4_tarski(esk2_3(X1,X2,X3),esk4_3(X1,X2,X3)),X1)|r2_hidden(k4_tarski(esk2_3(X1,X2,X3),esk3_3(X1,X2,X3)),X3)|X3=k5_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_17, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.21/0.39  cnf(c_0_18, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.21/0.39  fof(c_0_19, negated_conjecture, (v1_relat_1(esk5_0)&(k5_relat_1(k1_xboole_0,esk5_0)!=k1_xboole_0|k5_relat_1(esk5_0,k1_xboole_0)!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.21/0.39  cnf(c_0_20, plain, (k5_relat_1(X1,X2)=k1_xboole_0|r2_hidden(k4_tarski(esk2_3(X1,X2,k1_xboole_0),esk4_3(X1,X2,k1_xboole_0)),X1)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])).
% 0.21/0.39  cnf(c_0_21, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.39  cnf(c_0_22, negated_conjecture, (k5_relat_1(X1,esk5_0)=k1_xboole_0|r2_hidden(k4_tarski(esk2_3(X1,esk5_0,k1_xboole_0),esk4_3(X1,esk5_0,k1_xboole_0)),X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.21/0.39  cnf(c_0_23, plain, (r2_hidden(k4_tarski(esk4_3(X1,X2,X3),esk3_3(X1,X2,X3)),X2)|r2_hidden(k4_tarski(esk2_3(X1,X2,X3),esk3_3(X1,X2,X3)),X3)|X3=k5_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_24, negated_conjecture, (k5_relat_1(k1_xboole_0,esk5_0)!=k1_xboole_0|k5_relat_1(esk5_0,k1_xboole_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.39  cnf(c_0_25, negated_conjecture, (k5_relat_1(k1_xboole_0,esk5_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_17]), c_0_18])).
% 0.21/0.39  cnf(c_0_26, plain, (k5_relat_1(X1,X2)=k1_xboole_0|r2_hidden(k4_tarski(esk4_3(X1,X2,k1_xboole_0),esk3_3(X1,X2,k1_xboole_0)),X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_17]), c_0_18])).
% 0.21/0.39  cnf(c_0_27, negated_conjecture, (k5_relat_1(esk5_0,k1_xboole_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25])])).
% 0.21/0.39  cnf(c_0_28, plain, (k5_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_17]), c_0_18])).
% 0.21/0.39  cnf(c_0_29, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_21])]), ['proof']).
% 0.21/0.39  # SZS output end CNFRefutation
% 0.21/0.39  # Proof object total steps             : 30
% 0.21/0.39  # Proof object clause steps            : 18
% 0.21/0.39  # Proof object formula steps           : 12
% 0.21/0.39  # Proof object conjectures             : 9
% 0.21/0.39  # Proof object clause conjectures      : 6
% 0.21/0.39  # Proof object formula conjectures     : 3
% 0.21/0.39  # Proof object initial clauses used    : 8
% 0.21/0.39  # Proof object initial formulas used   : 6
% 0.21/0.39  # Proof object generating inferences   : 8
% 0.21/0.39  # Proof object simplifying inferences  : 9
% 0.21/0.39  # Training examples: 0 positive, 0 negative
% 0.21/0.39  # Parsed axioms                        : 6
% 0.21/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.39  # Initial clauses                      : 14
% 0.21/0.39  # Removed in clause preprocessing      : 0
% 0.21/0.39  # Initial clauses in saturation        : 14
% 0.21/0.39  # Processed clauses                    : 95
% 0.21/0.39  # ...of these trivial                  : 0
% 0.21/0.39  # ...subsumed                          : 26
% 0.21/0.39  # ...remaining for further processing  : 69
% 0.21/0.39  # Other redundant clauses eliminated   : 5
% 0.21/0.39  # Clauses deleted for lack of memory   : 0
% 0.21/0.39  # Backward-subsumed                    : 1
% 0.21/0.39  # Backward-rewritten                   : 3
% 0.21/0.39  # Generated clauses                    : 124
% 0.21/0.39  # ...of the previous two non-trivial   : 104
% 0.21/0.39  # Contextual simplify-reflections      : 0
% 0.21/0.39  # Paramodulations                      : 119
% 0.21/0.39  # Factorizations                       : 0
% 0.21/0.39  # Equation resolutions                 : 5
% 0.21/0.39  # Propositional unsat checks           : 0
% 0.21/0.39  #    Propositional check models        : 0
% 0.21/0.39  #    Propositional check unsatisfiable : 0
% 0.21/0.39  #    Propositional clauses             : 0
% 0.21/0.39  #    Propositional clauses after purity: 0
% 0.21/0.39  #    Propositional unsat core size     : 0
% 0.21/0.39  #    Propositional preprocessing time  : 0.000
% 0.21/0.39  #    Propositional encoding time       : 0.000
% 0.21/0.39  #    Propositional solver time         : 0.000
% 0.21/0.39  #    Success case prop preproc time    : 0.000
% 0.21/0.39  #    Success case prop encoding time   : 0.000
% 0.21/0.39  #    Success case prop solver time     : 0.000
% 0.21/0.39  # Current number of processed clauses  : 46
% 0.21/0.39  #    Positive orientable unit clauses  : 8
% 0.21/0.39  #    Positive unorientable unit clauses: 0
% 0.21/0.39  #    Negative unit clauses             : 4
% 0.21/0.39  #    Non-unit-clauses                  : 34
% 0.21/0.39  # Current number of unprocessed clauses: 37
% 0.21/0.39  # ...number of literals in the above   : 257
% 0.21/0.39  # Current number of archived formulas  : 0
% 0.21/0.39  # Current number of archived clauses   : 18
% 0.21/0.39  # Clause-clause subsumption calls (NU) : 546
% 0.21/0.39  # Rec. Clause-clause subsumption calls : 52
% 0.21/0.39  # Non-unit clause-clause subsumptions  : 14
% 0.21/0.39  # Unit Clause-clause subsumption calls : 11
% 0.21/0.39  # Rewrite failures with RHS unbound    : 0
% 0.21/0.39  # BW rewrite match attempts            : 3
% 0.21/0.39  # BW rewrite match successes           : 1
% 0.21/0.39  # Condensation attempts                : 0
% 0.21/0.39  # Condensation successes               : 0
% 0.21/0.39  # Termbank termtop insertions          : 5003
% 0.21/0.39  
% 0.21/0.39  # -------------------------------------------------
% 0.21/0.39  # User time                : 0.031 s
% 0.21/0.39  # System time              : 0.005 s
% 0.21/0.39  # Total time               : 0.037 s
% 0.21/0.39  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
