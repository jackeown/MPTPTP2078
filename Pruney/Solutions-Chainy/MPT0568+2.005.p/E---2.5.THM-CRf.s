%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:17 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 128 expanded)
%              Number of clauses        :   26 (  66 expanded)
%              Number of leaves         :    8 (  42 expanded)
%              Depth                    :   15
%              Number of atoms          :  115 ( 409 expanded)
%              Number of equality atoms :   42 ( 131 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d14_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k10_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(k4_tarski(X4,X5),X1)
                  & r2_hidden(X5,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

fof(cc1_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t172_relat_1,conjecture,(
    ! [X1] : k10_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

fof(c_0_6,plain,(
    ! [X11,X12,X13,X14,X16,X17,X18,X19,X21] :
      ( ( r2_hidden(k4_tarski(X14,esk1_4(X11,X12,X13,X14)),X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k10_relat_1(X11,X12)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(esk1_4(X11,X12,X13,X14),X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k10_relat_1(X11,X12)
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(k4_tarski(X16,X17),X11)
        | ~ r2_hidden(X17,X12)
        | r2_hidden(X16,X13)
        | X13 != k10_relat_1(X11,X12)
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(esk2_3(X11,X18,X19),X19)
        | ~ r2_hidden(k4_tarski(esk2_3(X11,X18,X19),X21),X11)
        | ~ r2_hidden(X21,X18)
        | X19 = k10_relat_1(X11,X18)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(k4_tarski(esk2_3(X11,X18,X19),esk3_3(X11,X18,X19)),X11)
        | r2_hidden(esk2_3(X11,X18,X19),X19)
        | X19 = k10_relat_1(X11,X18)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(esk3_3(X11,X18,X19),X18)
        | r2_hidden(esk2_3(X11,X18,X19),X19)
        | X19 = k10_relat_1(X11,X18)
        | ~ v1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

fof(c_0_7,plain,(
    ! [X10] :
      ( ~ v1_xboole_0(X10)
      | v1_relat_1(X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).

cnf(c_0_8,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_10,plain,(
    ! [X8,X9] : ~ r2_hidden(X8,k2_zfmisc_1(X8,X9)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

fof(c_0_11,plain,(
    ! [X6,X7] :
      ( ( k2_zfmisc_1(X6,X7) != k1_xboole_0
        | X6 = k1_xboole_0
        | X7 = k1_xboole_0 )
      & ( X6 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_12,plain,
    ( ~ epred2_0
  <=> ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    introduced(definition)).

cnf(c_0_13,plain,
    ( X1 = k10_relat_1(X2,X3)
    | r2_hidden(esk3_3(X2,X3,X1),X3)
    | r2_hidden(esk2_3(X2,X3,X1),X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_14,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_15,plain,
    ( ~ epred1_0
  <=> ! [X2] : X2 != k1_xboole_0 ),
    introduced(definition)).

cnf(c_0_16,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( epred2_0
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(split_equiv,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( X1 = k10_relat_1(k1_xboole_0,X2)
    | r2_hidden(esk2_3(k1_xboole_0,X2,X1),X1)
    | r2_hidden(esk3_3(k1_xboole_0,X2,X1),X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,plain,
    ( ~ epred2_0
    | ~ epred1_0 ),
    inference(apply_def,[status(thm)],[inference(apply_def,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_15]),c_0_12])).

cnf(c_0_21,plain,
    ( epred1_0
    | X1 != k1_xboole_0 ),
    inference(split_equiv,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( X1 = k10_relat_1(k1_xboole_0,k1_xboole_0)
    | epred2_0
    | r2_hidden(esk2_3(k1_xboole_0,k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,plain,
    ( X1 != k1_xboole_0
    | ~ epred2_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_24,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | epred2_0 ),
    inference(spm,[status(thm)],[c_0_18,c_0_22])).

cnf(c_0_25,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_26,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_27,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_28,plain,
    ( r2_hidden(esk1_4(k1_xboole_0,k1_xboole_0,X1,X2),k1_xboole_0)
    | X1 != k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_29,plain,
    ( r2_hidden(esk1_4(k1_xboole_0,k1_xboole_0,X1,X2),k1_xboole_0)
    | X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_9]),c_0_14])])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(esk2_3(X1,X2,X3),esk3_3(X1,X2,X3)),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_31,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_29]),c_0_23])).

fof(c_0_32,negated_conjecture,(
    ~ ! [X1] : k10_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t172_relat_1])).

cnf(c_0_33,plain,
    ( X1 = k10_relat_1(X2,X3)
    | r2_hidden(k4_tarski(esk2_3(X2,X3,X1),esk3_3(X2,X3,X1)),X2)
    | r2_hidden(esk2_3(X2,X3,X1),X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_9])).

cnf(c_0_34,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_31])).

fof(c_0_35,negated_conjecture,(
    k10_relat_1(k1_xboole_0,esk4_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_32])])])).

cnf(c_0_36,plain,
    ( X1 = k10_relat_1(k1_xboole_0,X2)
    | r2_hidden(esk2_3(k1_xboole_0,X2,X1),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_14]),c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( k10_relat_1(k1_xboole_0,esk4_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_38,plain,
    ( k10_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.36  % Computer   : n006.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 11:13:52 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  # Version: 2.5pre002
% 0.14/0.36  # No SInE strategy applied
% 0.14/0.36  # Trying AutoSched0 for 299 seconds
% 0.14/0.39  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S070I
% 0.14/0.39  # and selection function SelectVGNonCR.
% 0.14/0.39  #
% 0.14/0.39  # Preprocessing time       : 0.027 s
% 0.14/0.39  # Presaturation interreduction done
% 0.14/0.39  
% 0.14/0.39  # Proof found!
% 0.14/0.39  # SZS status Theorem
% 0.14/0.39  # SZS output start CNFRefutation
% 0.14/0.39  fof(d14_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X4,X5),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_1)).
% 0.14/0.39  fof(cc1_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 0.14/0.39  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.14/0.39  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.14/0.39  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.14/0.39  fof(t172_relat_1, conjecture, ![X1]:k10_relat_1(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 0.14/0.39  fof(c_0_6, plain, ![X11, X12, X13, X14, X16, X17, X18, X19, X21]:((((r2_hidden(k4_tarski(X14,esk1_4(X11,X12,X13,X14)),X11)|~r2_hidden(X14,X13)|X13!=k10_relat_1(X11,X12)|~v1_relat_1(X11))&(r2_hidden(esk1_4(X11,X12,X13,X14),X12)|~r2_hidden(X14,X13)|X13!=k10_relat_1(X11,X12)|~v1_relat_1(X11)))&(~r2_hidden(k4_tarski(X16,X17),X11)|~r2_hidden(X17,X12)|r2_hidden(X16,X13)|X13!=k10_relat_1(X11,X12)|~v1_relat_1(X11)))&((~r2_hidden(esk2_3(X11,X18,X19),X19)|(~r2_hidden(k4_tarski(esk2_3(X11,X18,X19),X21),X11)|~r2_hidden(X21,X18))|X19=k10_relat_1(X11,X18)|~v1_relat_1(X11))&((r2_hidden(k4_tarski(esk2_3(X11,X18,X19),esk3_3(X11,X18,X19)),X11)|r2_hidden(esk2_3(X11,X18,X19),X19)|X19=k10_relat_1(X11,X18)|~v1_relat_1(X11))&(r2_hidden(esk3_3(X11,X18,X19),X18)|r2_hidden(esk2_3(X11,X18,X19),X19)|X19=k10_relat_1(X11,X18)|~v1_relat_1(X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).
% 0.14/0.39  fof(c_0_7, plain, ![X10]:(~v1_xboole_0(X10)|v1_relat_1(X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).
% 0.14/0.39  cnf(c_0_8, plain, (r2_hidden(esk3_3(X1,X2,X3),X2)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k10_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.39  cnf(c_0_9, plain, (v1_relat_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.39  fof(c_0_10, plain, ![X8, X9]:~r2_hidden(X8,k2_zfmisc_1(X8,X9)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.14/0.39  fof(c_0_11, plain, ![X6, X7]:((k2_zfmisc_1(X6,X7)!=k1_xboole_0|(X6=k1_xboole_0|X7=k1_xboole_0))&((X6!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0)&(X7!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.14/0.39  fof(c_0_12, plain, (~epred2_0<=>![X1]:~r2_hidden(X1,k1_xboole_0)), introduced(definition)).
% 0.14/0.39  cnf(c_0_13, plain, (X1=k10_relat_1(X2,X3)|r2_hidden(esk3_3(X2,X3,X1),X3)|r2_hidden(esk2_3(X2,X3,X1),X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.14/0.39  cnf(c_0_14, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.14/0.39  fof(c_0_15, plain, (~epred1_0<=>![X2]:X2!=k1_xboole_0), introduced(definition)).
% 0.14/0.39  cnf(c_0_16, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_17, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.39  cnf(c_0_18, plain, (epred2_0|~r2_hidden(X1,k1_xboole_0)), inference(split_equiv,[status(thm)],[c_0_12])).
% 0.14/0.39  cnf(c_0_19, plain, (X1=k10_relat_1(k1_xboole_0,X2)|r2_hidden(esk2_3(k1_xboole_0,X2,X1),X1)|r2_hidden(esk3_3(k1_xboole_0,X2,X1),X2)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.14/0.39  cnf(c_0_20, plain, (~epred2_0|~epred1_0), inference(apply_def,[status(thm)],[inference(apply_def,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_15]), c_0_12])).
% 0.14/0.39  cnf(c_0_21, plain, (epred1_0|X1!=k1_xboole_0), inference(split_equiv,[status(thm)],[c_0_15])).
% 0.14/0.39  cnf(c_0_22, plain, (X1=k10_relat_1(k1_xboole_0,k1_xboole_0)|epred2_0|r2_hidden(esk2_3(k1_xboole_0,k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.14/0.39  cnf(c_0_23, plain, (X1!=k1_xboole_0|~epred2_0), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.14/0.39  cnf(c_0_24, plain, (k10_relat_1(k1_xboole_0,k1_xboole_0)=k1_xboole_0|epred2_0), inference(spm,[status(thm)],[c_0_18, c_0_22])).
% 0.14/0.39  cnf(c_0_25, plain, (k10_relat_1(k1_xboole_0,k1_xboole_0)=k1_xboole_0|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.14/0.39  cnf(c_0_26, plain, (r2_hidden(esk1_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k10_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.39  cnf(c_0_27, plain, (k10_relat_1(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_25])).
% 0.14/0.39  cnf(c_0_28, plain, (r2_hidden(esk1_4(k1_xboole_0,k1_xboole_0,X1,X2),k1_xboole_0)|X1!=k1_xboole_0|~v1_relat_1(k1_xboole_0)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.14/0.39  cnf(c_0_29, plain, (r2_hidden(esk1_4(k1_xboole_0,k1_xboole_0,X1,X2),k1_xboole_0)|X1!=k1_xboole_0|~r2_hidden(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_9]), c_0_14])])).
% 0.14/0.39  cnf(c_0_30, plain, (r2_hidden(k4_tarski(esk2_3(X1,X2,X3),esk3_3(X1,X2,X3)),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k10_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.39  cnf(c_0_31, plain, (X1!=k1_xboole_0|~r2_hidden(X2,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_29]), c_0_23])).
% 0.14/0.39  fof(c_0_32, negated_conjecture, ~(![X1]:k10_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(assume_negation,[status(cth)],[t172_relat_1])).
% 0.14/0.39  cnf(c_0_33, plain, (X1=k10_relat_1(X2,X3)|r2_hidden(k4_tarski(esk2_3(X2,X3,X1),esk3_3(X2,X3,X1)),X2)|r2_hidden(esk2_3(X2,X3,X1),X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_30, c_0_9])).
% 0.14/0.39  cnf(c_0_34, plain, (~r2_hidden(X1,k1_xboole_0)), inference(er,[status(thm)],[c_0_31])).
% 0.14/0.39  fof(c_0_35, negated_conjecture, k10_relat_1(k1_xboole_0,esk4_0)!=k1_xboole_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_32])])])).
% 0.14/0.39  cnf(c_0_36, plain, (X1=k10_relat_1(k1_xboole_0,X2)|r2_hidden(esk2_3(k1_xboole_0,X2,X1),X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_14]), c_0_34])).
% 0.14/0.39  cnf(c_0_37, negated_conjecture, (k10_relat_1(k1_xboole_0,esk4_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.14/0.39  cnf(c_0_38, plain, (k10_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_34, c_0_36])).
% 0.14/0.39  cnf(c_0_39, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38])]), ['proof']).
% 0.14/0.39  # SZS output end CNFRefutation
% 0.14/0.39  # Proof object total steps             : 40
% 0.14/0.39  # Proof object clause steps            : 26
% 0.14/0.39  # Proof object formula steps           : 14
% 0.14/0.39  # Proof object conjectures             : 5
% 0.14/0.39  # Proof object clause conjectures      : 2
% 0.14/0.39  # Proof object formula conjectures     : 3
% 0.14/0.39  # Proof object initial clauses used    : 10
% 0.14/0.39  # Proof object initial formulas used   : 6
% 0.14/0.39  # Proof object generating inferences   : 15
% 0.14/0.39  # Proof object simplifying inferences  : 8
% 0.14/0.39  # Training examples: 0 positive, 0 negative
% 0.14/0.39  # Parsed axioms                        : 6
% 0.14/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.39  # Initial clauses                      : 13
% 0.14/0.39  # Removed in clause preprocessing      : 0
% 0.14/0.39  # Initial clauses in saturation        : 13
% 0.14/0.39  # Processed clauses                    : 59
% 0.14/0.39  # ...of these trivial                  : 0
% 0.14/0.39  # ...subsumed                          : 4
% 0.14/0.39  # ...remaining for further processing  : 55
% 0.14/0.39  # Other redundant clauses eliminated   : 0
% 0.14/0.39  # Clauses deleted for lack of memory   : 0
% 0.14/0.39  # Backward-subsumed                    : 6
% 0.14/0.39  # Backward-rewritten                   : 6
% 0.14/0.39  # Generated clauses                    : 56
% 0.14/0.39  # ...of the previous two non-trivial   : 51
% 0.14/0.39  # Contextual simplify-reflections      : 1
% 0.14/0.39  # Paramodulations                      : 47
% 0.14/0.39  # Factorizations                       : 0
% 0.14/0.39  # Equation resolutions                 : 6
% 0.14/0.39  # Propositional unsat checks           : 0
% 0.14/0.39  #    Propositional check models        : 0
% 0.14/0.39  #    Propositional check unsatisfiable : 0
% 0.14/0.39  #    Propositional clauses             : 0
% 0.14/0.39  #    Propositional clauses after purity: 0
% 0.14/0.39  #    Propositional unsat core size     : 0
% 0.14/0.39  #    Propositional preprocessing time  : 0.000
% 0.14/0.39  #    Propositional encoding time       : 0.000
% 0.14/0.39  #    Propositional solver time         : 0.000
% 0.14/0.39  #    Success case prop preproc time    : 0.000
% 0.14/0.39  #    Success case prop encoding time   : 0.000
% 0.14/0.39  #    Success case prop solver time     : 0.000
% 0.14/0.39  # Current number of processed clauses  : 29
% 0.14/0.39  #    Positive orientable unit clauses  : 2
% 0.14/0.39  #    Positive unorientable unit clauses: 0
% 0.14/0.39  #    Negative unit clauses             : 3
% 0.14/0.39  #    Non-unit-clauses                  : 24
% 0.14/0.39  # Current number of unprocessed clauses: 17
% 0.14/0.39  # ...number of literals in the above   : 65
% 0.14/0.39  # Current number of archived formulas  : 0
% 0.14/0.39  # Current number of archived clauses   : 25
% 0.14/0.39  # Clause-clause subsumption calls (NU) : 200
% 0.14/0.39  # Rec. Clause-clause subsumption calls : 140
% 0.14/0.39  # Non-unit clause-clause subsumptions  : 9
% 0.14/0.39  # Unit Clause-clause subsumption calls : 9
% 0.14/0.39  # Rewrite failures with RHS unbound    : 0
% 0.14/0.39  # BW rewrite match attempts            : 4
% 0.14/0.39  # BW rewrite match successes           : 4
% 0.14/0.39  # Condensation attempts                : 0
% 0.14/0.39  # Condensation successes               : 0
% 0.14/0.39  # Termbank termtop insertions          : 1814
% 0.14/0.39  
% 0.14/0.39  # -------------------------------------------------
% 0.14/0.39  # User time                : 0.032 s
% 0.14/0.39  # System time              : 0.001 s
% 0.14/0.39  # Total time               : 0.033 s
% 0.14/0.39  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
