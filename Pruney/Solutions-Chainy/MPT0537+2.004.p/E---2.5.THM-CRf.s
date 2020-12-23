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
% DateTime   : Thu Dec  3 10:50:15 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   32 (  41 expanded)
%              Number of clauses        :   18 (  20 expanded)
%              Number of leaves         :    8 (  13 expanded)
%              Depth                    :    9
%              Number of atoms          :   97 ( 113 expanded)
%              Number of equality atoms :   33 (  39 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(d12_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( X3 = k8_relat_1(X1,X2)
          <=> ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X3)
              <=> ( r2_hidden(X5,X1)
                  & r2_hidden(k4_tarski(X4,X5),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_1)).

fof(t81_relat_1,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(t137_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(k1_xboole_0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(c_0_6,plain,(
    ! [X19] : v1_relat_1(k6_relat_1(X19)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_7,plain,(
    ! [X10,X11,X12,X13,X14,X15,X16] :
      ( ( r2_hidden(X14,X10)
        | ~ r2_hidden(k4_tarski(X13,X14),X12)
        | X12 != k8_relat_1(X10,X11)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(k4_tarski(X13,X14),X11)
        | ~ r2_hidden(k4_tarski(X13,X14),X12)
        | X12 != k8_relat_1(X10,X11)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(X16,X10)
        | ~ r2_hidden(k4_tarski(X15,X16),X11)
        | r2_hidden(k4_tarski(X15,X16),X12)
        | X12 != k8_relat_1(X10,X11)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(k4_tarski(esk1_3(X10,X11,X12),esk2_3(X10,X11,X12)),X12)
        | ~ r2_hidden(esk2_3(X10,X11,X12),X10)
        | ~ r2_hidden(k4_tarski(esk1_3(X10,X11,X12),esk2_3(X10,X11,X12)),X11)
        | X12 = k8_relat_1(X10,X11)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(esk2_3(X10,X11,X12),X10)
        | r2_hidden(k4_tarski(esk1_3(X10,X11,X12),esk2_3(X10,X11,X12)),X12)
        | X12 = k8_relat_1(X10,X11)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(k4_tarski(esk1_3(X10,X11,X12),esk2_3(X10,X11,X12)),X11)
        | r2_hidden(k4_tarski(esk1_3(X10,X11,X12),esk2_3(X10,X11,X12)),X12)
        | X12 = k8_relat_1(X10,X11)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_relat_1])])])])])])).

cnf(c_0_8,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t81_relat_1])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => k8_relat_1(k1_xboole_0,X1) = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t137_relat_1])).

cnf(c_0_11,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X3)
    | X3 = k8_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

fof(c_0_13,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & k8_relat_1(k1_xboole_0,esk3_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_14,plain,(
    ! [X8,X9] : ~ r2_hidden(X8,k2_zfmisc_1(X8,X9)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

fof(c_0_15,plain,(
    ! [X6,X7] :
      ( ( k2_zfmisc_1(X6,X7) != k1_xboole_0
        | X6 = k1_xboole_0
        | X7 = k1_xboole_0 )
      & ( X6 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_16,plain,
    ( ~ epred2_0
  <=> ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    introduced(definition)).

cnf(c_0_17,plain,
    ( k8_relat_1(X1,X2) = k1_xboole_0
    | r2_hidden(k4_tarski(esk1_3(X1,X2,k1_xboole_0),esk2_3(X1,X2,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(esk2_3(X1,X2,k1_xboole_0),X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,
    ( ~ epred1_0
  <=> ! [X2] : X2 != k1_xboole_0 ),
    introduced(definition)).

cnf(c_0_20,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( epred2_0
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(split_equiv,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( k8_relat_1(X1,esk3_0) = k1_xboole_0
    | r2_hidden(k4_tarski(esk1_3(X1,esk3_0,k1_xboole_0),esk2_3(X1,esk3_0,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(esk2_3(X1,esk3_0,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,plain,
    ( ~ epred2_0
    | ~ epred1_0 ),
    inference(apply_def,[status(thm)],[inference(apply_def,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_19]),c_0_16])).

cnf(c_0_25,plain,
    ( epred1_0
    | X1 != k1_xboole_0 ),
    inference(split_equiv,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( k8_relat_1(X1,esk3_0) = k1_xboole_0
    | epred2_0
    | r2_hidden(esk2_3(X1,esk3_0,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( k8_relat_1(k1_xboole_0,esk3_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_28,plain,
    ( X1 != k1_xboole_0
    | ~ epred2_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( epred2_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_26]),c_0_27])).

cnf(c_0_30,plain,
    ( X1 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29])])).

cnf(c_0_31,plain,
    ( $false ),
    inference(sr,[status(thm)],[c_0_9,c_0_30]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.34  % Computer   : n024.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 14:47:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 0.15/0.38  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S070I
% 0.15/0.38  # and selection function SelectVGNonCR.
% 0.15/0.38  #
% 0.15/0.38  # Preprocessing time       : 0.027 s
% 0.15/0.38  # Presaturation interreduction done
% 0.15/0.38  
% 0.15/0.38  # Proof found!
% 0.15/0.38  # SZS status Theorem
% 0.15/0.38  # SZS output start CNFRefutation
% 0.15/0.38  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.15/0.38  fof(d12_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(X3=k8_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>(r2_hidden(X5,X1)&r2_hidden(k4_tarski(X4,X5),X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_relat_1)).
% 0.15/0.38  fof(t81_relat_1, axiom, k6_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 0.15/0.38  fof(t137_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>k8_relat_1(k1_xboole_0,X1)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_relat_1)).
% 0.15/0.38  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.15/0.38  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.15/0.38  fof(c_0_6, plain, ![X19]:v1_relat_1(k6_relat_1(X19)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.15/0.38  fof(c_0_7, plain, ![X10, X11, X12, X13, X14, X15, X16]:((((r2_hidden(X14,X10)|~r2_hidden(k4_tarski(X13,X14),X12)|X12!=k8_relat_1(X10,X11)|~v1_relat_1(X12)|~v1_relat_1(X11))&(r2_hidden(k4_tarski(X13,X14),X11)|~r2_hidden(k4_tarski(X13,X14),X12)|X12!=k8_relat_1(X10,X11)|~v1_relat_1(X12)|~v1_relat_1(X11)))&(~r2_hidden(X16,X10)|~r2_hidden(k4_tarski(X15,X16),X11)|r2_hidden(k4_tarski(X15,X16),X12)|X12!=k8_relat_1(X10,X11)|~v1_relat_1(X12)|~v1_relat_1(X11)))&((~r2_hidden(k4_tarski(esk1_3(X10,X11,X12),esk2_3(X10,X11,X12)),X12)|(~r2_hidden(esk2_3(X10,X11,X12),X10)|~r2_hidden(k4_tarski(esk1_3(X10,X11,X12),esk2_3(X10,X11,X12)),X11))|X12=k8_relat_1(X10,X11)|~v1_relat_1(X12)|~v1_relat_1(X11))&((r2_hidden(esk2_3(X10,X11,X12),X10)|r2_hidden(k4_tarski(esk1_3(X10,X11,X12),esk2_3(X10,X11,X12)),X12)|X12=k8_relat_1(X10,X11)|~v1_relat_1(X12)|~v1_relat_1(X11))&(r2_hidden(k4_tarski(esk1_3(X10,X11,X12),esk2_3(X10,X11,X12)),X11)|r2_hidden(k4_tarski(esk1_3(X10,X11,X12),esk2_3(X10,X11,X12)),X12)|X12=k8_relat_1(X10,X11)|~v1_relat_1(X12)|~v1_relat_1(X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_relat_1])])])])])])).
% 0.15/0.38  cnf(c_0_8, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.15/0.38  cnf(c_0_9, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t81_relat_1])).
% 0.15/0.38  fof(c_0_10, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>k8_relat_1(k1_xboole_0,X1)=k1_xboole_0)), inference(assume_negation,[status(cth)],[t137_relat_1])).
% 0.15/0.38  cnf(c_0_11, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X3)|X3=k8_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.15/0.38  cnf(c_0_12, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.15/0.38  fof(c_0_13, negated_conjecture, (v1_relat_1(esk3_0)&k8_relat_1(k1_xboole_0,esk3_0)!=k1_xboole_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.15/0.38  fof(c_0_14, plain, ![X8, X9]:~r2_hidden(X8,k2_zfmisc_1(X8,X9)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.15/0.38  fof(c_0_15, plain, ![X6, X7]:((k2_zfmisc_1(X6,X7)!=k1_xboole_0|(X6=k1_xboole_0|X7=k1_xboole_0))&((X6!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0)&(X7!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.15/0.38  fof(c_0_16, plain, (~epred2_0<=>![X1]:~r2_hidden(X1,k1_xboole_0)), introduced(definition)).
% 0.15/0.38  cnf(c_0_17, plain, (k8_relat_1(X1,X2)=k1_xboole_0|r2_hidden(k4_tarski(esk1_3(X1,X2,k1_xboole_0),esk2_3(X1,X2,k1_xboole_0)),k1_xboole_0)|r2_hidden(esk2_3(X1,X2,k1_xboole_0),X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.15/0.38  cnf(c_0_18, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.15/0.38  fof(c_0_19, plain, (~epred1_0<=>![X2]:X2!=k1_xboole_0), introduced(definition)).
% 0.15/0.38  cnf(c_0_20, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.15/0.38  cnf(c_0_21, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.15/0.38  cnf(c_0_22, plain, (epred2_0|~r2_hidden(X1,k1_xboole_0)), inference(split_equiv,[status(thm)],[c_0_16])).
% 0.15/0.38  cnf(c_0_23, negated_conjecture, (k8_relat_1(X1,esk3_0)=k1_xboole_0|r2_hidden(k4_tarski(esk1_3(X1,esk3_0,k1_xboole_0),esk2_3(X1,esk3_0,k1_xboole_0)),k1_xboole_0)|r2_hidden(esk2_3(X1,esk3_0,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.15/0.38  cnf(c_0_24, plain, (~epred2_0|~epred1_0), inference(apply_def,[status(thm)],[inference(apply_def,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_19]), c_0_16])).
% 0.15/0.38  cnf(c_0_25, plain, (epred1_0|X1!=k1_xboole_0), inference(split_equiv,[status(thm)],[c_0_19])).
% 0.15/0.38  cnf(c_0_26, negated_conjecture, (k8_relat_1(X1,esk3_0)=k1_xboole_0|epred2_0|r2_hidden(esk2_3(X1,esk3_0,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.15/0.38  cnf(c_0_27, negated_conjecture, (k8_relat_1(k1_xboole_0,esk3_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.15/0.38  cnf(c_0_28, plain, (X1!=k1_xboole_0|~epred2_0), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.15/0.38  cnf(c_0_29, negated_conjecture, (epred2_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_26]), c_0_27])).
% 0.15/0.38  cnf(c_0_30, plain, (X1!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29])])).
% 0.15/0.38  cnf(c_0_31, plain, ($false), inference(sr,[status(thm)],[c_0_9, c_0_30]), ['proof']).
% 0.15/0.38  # SZS output end CNFRefutation
% 0.15/0.38  # Proof object total steps             : 32
% 0.15/0.38  # Proof object clause steps            : 18
% 0.15/0.38  # Proof object formula steps           : 14
% 0.15/0.38  # Proof object conjectures             : 8
% 0.15/0.38  # Proof object clause conjectures      : 5
% 0.15/0.38  # Proof object formula conjectures     : 3
% 0.15/0.38  # Proof object initial clauses used    : 9
% 0.15/0.38  # Proof object initial formulas used   : 6
% 0.15/0.38  # Proof object generating inferences   : 7
% 0.15/0.38  # Proof object simplifying inferences  : 6
% 0.15/0.38  # Training examples: 0 positive, 0 negative
% 0.15/0.38  # Parsed axioms                        : 6
% 0.15/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.38  # Initial clauses                      : 14
% 0.15/0.38  # Removed in clause preprocessing      : 0
% 0.15/0.38  # Initial clauses in saturation        : 14
% 0.15/0.38  # Processed clauses                    : 49
% 0.15/0.38  # ...of these trivial                  : 0
% 0.15/0.38  # ...subsumed                          : 0
% 0.15/0.38  # ...remaining for further processing  : 49
% 0.15/0.38  # Other redundant clauses eliminated   : 0
% 0.15/0.38  # Clauses deleted for lack of memory   : 0
% 0.15/0.38  # Backward-subsumed                    : 0
% 0.15/0.38  # Backward-rewritten                   : 4
% 0.15/0.38  # Generated clauses                    : 47
% 0.15/0.38  # ...of the previous two non-trivial   : 45
% 0.15/0.38  # Contextual simplify-reflections      : 0
% 0.15/0.38  # Paramodulations                      : 37
% 0.15/0.38  # Factorizations                       : 0
% 0.15/0.38  # Equation resolutions                 : 5
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
% 0.15/0.38  # Current number of processed clauses  : 28
% 0.15/0.38  #    Positive orientable unit clauses  : 4
% 0.15/0.38  #    Positive unorientable unit clauses: 0
% 0.15/0.38  #    Negative unit clauses             : 5
% 0.15/0.38  #    Non-unit-clauses                  : 19
% 0.15/0.38  # Current number of unprocessed clauses: 23
% 0.15/0.38  # ...number of literals in the above   : 75
% 0.15/0.38  # Current number of archived formulas  : 0
% 0.15/0.38  # Current number of archived clauses   : 20
% 0.15/0.38  # Clause-clause subsumption calls (NU) : 275
% 0.15/0.38  # Rec. Clause-clause subsumption calls : 130
% 0.15/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.15/0.38  # Unit Clause-clause subsumption calls : 68
% 0.15/0.38  # Rewrite failures with RHS unbound    : 0
% 0.15/0.38  # BW rewrite match attempts            : 1
% 0.15/0.38  # BW rewrite match successes           : 1
% 0.15/0.38  # Condensation attempts                : 0
% 0.15/0.38  # Condensation successes               : 0
% 0.15/0.38  # Termbank termtop insertions          : 2033
% 0.15/0.38  
% 0.15/0.38  # -------------------------------------------------
% 0.15/0.38  # User time                : 0.028 s
% 0.15/0.38  # System time              : 0.005 s
% 0.15/0.38  # Total time               : 0.033 s
% 0.15/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
