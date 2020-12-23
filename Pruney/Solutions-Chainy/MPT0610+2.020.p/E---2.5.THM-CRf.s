%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:38 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   34 (  46 expanded)
%              Number of clauses        :   19 (  20 expanded)
%              Number of leaves         :    7 (  11 expanded)
%              Depth                    :   10
%              Number of atoms          :   80 ( 122 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t214_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_xboole_0(k1_relat_1(X1),k1_relat_1(X2))
           => r1_xboole_0(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t214_relat_1)).

fof(t21_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(t127_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_xboole_0(X1,X2)
        | r1_xboole_0(X3,X4) )
     => r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_xboole_0(k1_relat_1(X1),k1_relat_1(X2))
             => r1_xboole_0(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t214_relat_1])).

fof(c_0_8,plain,(
    ! [X19] :
      ( ~ v1_relat_1(X19)
      | r1_tarski(X19,k2_zfmisc_1(k1_relat_1(X19),k2_relat_1(X19))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).

fof(c_0_9,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & r1_xboole_0(k1_relat_1(esk1_0),k1_relat_1(esk2_0))
    & ~ r1_xboole_0(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | k2_xboole_0(X8,X9) = X9 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_11,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X10,X11,X12] :
      ( ( r1_xboole_0(X10,k2_xboole_0(X11,X12))
        | ~ r1_xboole_0(X10,X11)
        | ~ r1_xboole_0(X10,X12) )
      & ( r1_xboole_0(X10,X11)
        | ~ r1_xboole_0(X10,k2_xboole_0(X11,X12)) )
      & ( r1_xboole_0(X10,X12)
        | ~ r1_xboole_0(X10,k2_xboole_0(X11,X12)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

cnf(c_0_14,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

fof(c_0_16,plain,(
    ! [X15,X16,X17,X18] :
      ( ( ~ r1_xboole_0(X15,X16)
        | r1_xboole_0(k2_zfmisc_1(X15,X17),k2_zfmisc_1(X16,X18)) )
      & ( ~ r1_xboole_0(X17,X18)
        | r1_xboole_0(k2_zfmisc_1(X15,X17),k2_zfmisc_1(X16,X18)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_zfmisc_1])])])).

cnf(c_0_17,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( k2_xboole_0(esk2_0,k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(esk2_0))) = k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,plain,
    ( r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(esk1_0),k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_21,plain,(
    ! [X13,X14] :
      ( ( ~ r1_xboole_0(X13,X14)
        | k4_xboole_0(X13,X14) = X13 )
      & ( k4_xboole_0(X13,X14) != X13
        | r1_xboole_0(X13,X14) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_22,negated_conjecture,
    ( r1_xboole_0(X1,esk2_0)
    | ~ r1_xboole_0(X1,k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( r1_xboole_0(k2_zfmisc_1(k1_relat_1(esk1_0),X1),k2_zfmisc_1(k1_relat_1(esk2_0),X2)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_24,plain,(
    ! [X5,X6,X7] :
      ( ( r1_tarski(X5,X6)
        | ~ r1_tarski(X5,k4_xboole_0(X6,X7)) )
      & ( r1_xboole_0(X5,X7)
        | ~ r1_tarski(X5,k4_xboole_0(X6,X7)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( r1_xboole_0(k2_zfmisc_1(k1_relat_1(esk1_0),X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( k4_xboole_0(k2_zfmisc_1(k1_relat_1(esk1_0),X1),esk2_0) = k2_zfmisc_1(k1_relat_1(esk1_0),X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_30,negated_conjecture,
    ( r1_xboole_0(X1,esk2_0)
    | ~ r1_tarski(X1,k2_zfmisc_1(k1_relat_1(esk1_0),X2)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_11,c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( ~ r1_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n012.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 09:14:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.36  # AutoSched0-Mode selected heuristic G_E___107_C00_02_nc_F1_PI_AE_Q4_CS_SP_PS_S00EN
% 0.14/0.36  # and selection function PSelectSmallestOrientable.
% 0.14/0.36  #
% 0.14/0.36  # Preprocessing time       : 0.021 s
% 0.14/0.36  # Presaturation interreduction done
% 0.14/0.36  
% 0.14/0.36  # Proof found!
% 0.14/0.36  # SZS status Theorem
% 0.14/0.36  # SZS output start CNFRefutation
% 0.14/0.36  fof(t214_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_xboole_0(k1_relat_1(X1),k1_relat_1(X2))=>r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t214_relat_1)).
% 0.14/0.36  fof(t21_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 0.14/0.36  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.14/0.36  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 0.14/0.36  fof(t127_zfmisc_1, axiom, ![X1, X2, X3, X4]:((r1_xboole_0(X1,X2)|r1_xboole_0(X3,X4))=>r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 0.14/0.36  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.14/0.36  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.14/0.36  fof(c_0_7, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_xboole_0(k1_relat_1(X1),k1_relat_1(X2))=>r1_xboole_0(X1,X2))))), inference(assume_negation,[status(cth)],[t214_relat_1])).
% 0.14/0.36  fof(c_0_8, plain, ![X19]:(~v1_relat_1(X19)|r1_tarski(X19,k2_zfmisc_1(k1_relat_1(X19),k2_relat_1(X19)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).
% 0.14/0.36  fof(c_0_9, negated_conjecture, (v1_relat_1(esk1_0)&(v1_relat_1(esk2_0)&(r1_xboole_0(k1_relat_1(esk1_0),k1_relat_1(esk2_0))&~r1_xboole_0(esk1_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.14/0.36  fof(c_0_10, plain, ![X8, X9]:(~r1_tarski(X8,X9)|k2_xboole_0(X8,X9)=X9), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.14/0.36  cnf(c_0_11, plain, (r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.36  cnf(c_0_12, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.36  fof(c_0_13, plain, ![X10, X11, X12]:((r1_xboole_0(X10,k2_xboole_0(X11,X12))|~r1_xboole_0(X10,X11)|~r1_xboole_0(X10,X12))&((r1_xboole_0(X10,X11)|~r1_xboole_0(X10,k2_xboole_0(X11,X12)))&(r1_xboole_0(X10,X12)|~r1_xboole_0(X10,k2_xboole_0(X11,X12))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 0.14/0.36  cnf(c_0_14, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.36  cnf(c_0_15, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(esk2_0)))), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.14/0.36  fof(c_0_16, plain, ![X15, X16, X17, X18]:((~r1_xboole_0(X15,X16)|r1_xboole_0(k2_zfmisc_1(X15,X17),k2_zfmisc_1(X16,X18)))&(~r1_xboole_0(X17,X18)|r1_xboole_0(k2_zfmisc_1(X15,X17),k2_zfmisc_1(X16,X18)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_zfmisc_1])])])).
% 0.14/0.36  cnf(c_0_17, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.36  cnf(c_0_18, negated_conjecture, (k2_xboole_0(esk2_0,k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(esk2_0)))=k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.14/0.36  cnf(c_0_19, plain, (r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.36  cnf(c_0_20, negated_conjecture, (r1_xboole_0(k1_relat_1(esk1_0),k1_relat_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.36  fof(c_0_21, plain, ![X13, X14]:((~r1_xboole_0(X13,X14)|k4_xboole_0(X13,X14)=X13)&(k4_xboole_0(X13,X14)!=X13|r1_xboole_0(X13,X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.14/0.36  cnf(c_0_22, negated_conjecture, (r1_xboole_0(X1,esk2_0)|~r1_xboole_0(X1,k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(esk2_0)))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.14/0.36  cnf(c_0_23, negated_conjecture, (r1_xboole_0(k2_zfmisc_1(k1_relat_1(esk1_0),X1),k2_zfmisc_1(k1_relat_1(esk2_0),X2))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.14/0.36  fof(c_0_24, plain, ![X5, X6, X7]:((r1_tarski(X5,X6)|~r1_tarski(X5,k4_xboole_0(X6,X7)))&(r1_xboole_0(X5,X7)|~r1_tarski(X5,k4_xboole_0(X6,X7)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 0.14/0.36  cnf(c_0_25, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.36  cnf(c_0_26, negated_conjecture, (r1_xboole_0(k2_zfmisc_1(k1_relat_1(esk1_0),X1),esk2_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.14/0.36  cnf(c_0_27, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.36  cnf(c_0_28, negated_conjecture, (k4_xboole_0(k2_zfmisc_1(k1_relat_1(esk1_0),X1),esk2_0)=k2_zfmisc_1(k1_relat_1(esk1_0),X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.14/0.36  cnf(c_0_29, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.36  cnf(c_0_30, negated_conjecture, (r1_xboole_0(X1,esk2_0)|~r1_tarski(X1,k2_zfmisc_1(k1_relat_1(esk1_0),X2))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.14/0.36  cnf(c_0_31, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))), inference(spm,[status(thm)],[c_0_11, c_0_29])).
% 0.14/0.36  cnf(c_0_32, negated_conjecture, (~r1_xboole_0(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.36  cnf(c_0_33, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), ['proof']).
% 0.14/0.36  # SZS output end CNFRefutation
% 0.14/0.36  # Proof object total steps             : 34
% 0.14/0.36  # Proof object clause steps            : 19
% 0.14/0.36  # Proof object formula steps           : 15
% 0.14/0.36  # Proof object conjectures             : 16
% 0.14/0.36  # Proof object clause conjectures      : 13
% 0.14/0.36  # Proof object formula conjectures     : 3
% 0.14/0.36  # Proof object initial clauses used    : 10
% 0.14/0.36  # Proof object initial formulas used   : 7
% 0.14/0.36  # Proof object generating inferences   : 9
% 0.14/0.36  # Proof object simplifying inferences  : 1
% 0.14/0.36  # Training examples: 0 positive, 0 negative
% 0.14/0.36  # Parsed axioms                        : 7
% 0.14/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.36  # Initial clauses                      : 15
% 0.14/0.36  # Removed in clause preprocessing      : 0
% 0.14/0.36  # Initial clauses in saturation        : 15
% 0.14/0.36  # Processed clauses                    : 52
% 0.14/0.36  # ...of these trivial                  : 0
% 0.14/0.36  # ...subsumed                          : 0
% 0.14/0.36  # ...remaining for further processing  : 52
% 0.14/0.36  # Other redundant clauses eliminated   : 0
% 0.14/0.36  # Clauses deleted for lack of memory   : 0
% 0.14/0.36  # Backward-subsumed                    : 0
% 0.14/0.36  # Backward-rewritten                   : 0
% 0.14/0.36  # Generated clauses                    : 74
% 0.14/0.36  # ...of the previous two non-trivial   : 55
% 0.14/0.36  # Contextual simplify-reflections      : 0
% 0.14/0.36  # Paramodulations                      : 74
% 0.14/0.36  # Factorizations                       : 0
% 0.14/0.36  # Equation resolutions                 : 0
% 0.14/0.36  # Propositional unsat checks           : 0
% 0.14/0.36  #    Propositional check models        : 0
% 0.14/0.36  #    Propositional check unsatisfiable : 0
% 0.14/0.36  #    Propositional clauses             : 0
% 0.14/0.36  #    Propositional clauses after purity: 0
% 0.14/0.36  #    Propositional unsat core size     : 0
% 0.14/0.36  #    Propositional preprocessing time  : 0.000
% 0.14/0.36  #    Propositional encoding time       : 0.000
% 0.14/0.36  #    Propositional solver time         : 0.000
% 0.14/0.36  #    Success case prop preproc time    : 0.000
% 0.14/0.36  #    Success case prop encoding time   : 0.000
% 0.14/0.36  #    Success case prop solver time     : 0.000
% 0.14/0.36  # Current number of processed clauses  : 37
% 0.14/0.36  #    Positive orientable unit clauses  : 19
% 0.14/0.36  #    Positive unorientable unit clauses: 0
% 0.14/0.36  #    Negative unit clauses             : 1
% 0.14/0.36  #    Non-unit-clauses                  : 17
% 0.14/0.36  # Current number of unprocessed clauses: 33
% 0.14/0.36  # ...number of literals in the above   : 42
% 0.14/0.36  # Current number of archived formulas  : 0
% 0.14/0.36  # Current number of archived clauses   : 15
% 0.14/0.36  # Clause-clause subsumption calls (NU) : 19
% 0.14/0.36  # Rec. Clause-clause subsumption calls : 18
% 0.14/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.36  # Unit Clause-clause subsumption calls : 0
% 0.14/0.36  # Rewrite failures with RHS unbound    : 0
% 0.14/0.36  # BW rewrite match attempts            : 0
% 0.14/0.36  # BW rewrite match successes           : 0
% 0.14/0.36  # Condensation attempts                : 0
% 0.14/0.36  # Condensation successes               : 0
% 0.14/0.36  # Termbank termtop insertions          : 2143
% 0.14/0.36  
% 0.14/0.36  # -------------------------------------------------
% 0.14/0.36  # User time                : 0.023 s
% 0.14/0.36  # System time              : 0.004 s
% 0.14/0.36  # Total time               : 0.027 s
% 0.14/0.36  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
