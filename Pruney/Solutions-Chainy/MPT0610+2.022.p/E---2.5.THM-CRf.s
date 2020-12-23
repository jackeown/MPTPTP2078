%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:38 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   32 (  44 expanded)
%              Number of clauses        :   17 (  18 expanded)
%              Number of leaves         :    7 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :   76 ( 118 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(t127_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_xboole_0(X1,X2)
        | r1_xboole_0(X3,X4) )
     => r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(t81_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
     => r1_xboole_0(X2,k4_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

fof(t85_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_xboole_0(X1,k4_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(t21_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(t214_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_xboole_0(k1_relat_1(X1),k1_relat_1(X2))
           => r1_xboole_0(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t214_relat_1)).

fof(t84_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( ~ r1_xboole_0(X1,X2)
        & r1_xboole_0(X1,X3)
        & r1_xboole_0(X1,k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_xboole_1)).

fof(c_0_7,plain,(
    ! [X5,X6,X7] :
      ( ~ r1_tarski(X5,X6)
      | ~ r1_xboole_0(X6,X7)
      | r1_xboole_0(X5,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

fof(c_0_8,plain,(
    ! [X17,X18,X19,X20] :
      ( ( ~ r1_xboole_0(X17,X18)
        | r1_xboole_0(k2_zfmisc_1(X17,X19),k2_zfmisc_1(X18,X20)) )
      & ( ~ r1_xboole_0(X19,X20)
        | r1_xboole_0(k2_zfmisc_1(X17,X19),k2_zfmisc_1(X18,X20)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_zfmisc_1])])])).

fof(c_0_9,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_xboole_0(X8,k4_xboole_0(X9,X10))
      | r1_xboole_0(X9,k4_xboole_0(X8,X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t81_xboole_1])])).

fof(c_0_10,plain,(
    ! [X14,X15,X16] :
      ( ~ r1_tarski(X14,X15)
      | r1_xboole_0(X14,k4_xboole_0(X16,X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).

cnf(c_0_11,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,plain,(
    ! [X21] :
      ( ~ v1_relat_1(X21)
      | r1_tarski(X21,k2_zfmisc_1(k1_relat_1(X21),k2_relat_1(X21))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_xboole_0(k1_relat_1(X1),k1_relat_1(X2))
             => r1_xboole_0(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t214_relat_1])).

fof(c_0_15,plain,(
    ! [X11,X12,X13] :
      ( r1_xboole_0(X11,X12)
      | ~ r1_xboole_0(X11,X13)
      | ~ r1_xboole_0(X11,k4_xboole_0(X12,X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t84_xboole_1])])])).

cnf(c_0_16,plain,
    ( r1_xboole_0(X2,k4_xboole_0(X1,X3))
    | ~ r1_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( r1_xboole_0(X1,k2_zfmisc_1(X2,X3))
    | ~ r1_xboole_0(X4,X2)
    | ~ r1_tarski(X1,k2_zfmisc_1(X4,X5)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_20,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & r1_xboole_0(k1_relat_1(esk1_0),k1_relat_1(esk2_0))
    & ~ r1_xboole_0(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

cnf(c_0_21,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( r1_xboole_0(X1,k2_zfmisc_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(k1_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(esk1_0),k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( r1_xboole_0(esk1_0,k2_zfmisc_1(k1_relat_1(esk2_0),X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

cnf(c_0_28,negated_conjecture,
    ( r1_xboole_0(esk1_0,X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(k1_relat_1(esk2_0),X2)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_29,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( ~ r1_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_19]),c_0_29])]),c_0_30]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:58:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.027 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.12/0.37  fof(t127_zfmisc_1, axiom, ![X1, X2, X3, X4]:((r1_xboole_0(X1,X2)|r1_xboole_0(X3,X4))=>r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 0.12/0.37  fof(t81_xboole_1, axiom, ![X1, X2, X3]:(r1_xboole_0(X1,k4_xboole_0(X2,X3))=>r1_xboole_0(X2,k4_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_xboole_1)).
% 0.12/0.37  fof(t85_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_xboole_0(X1,k4_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 0.12/0.37  fof(t21_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 0.12/0.37  fof(t214_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_xboole_0(k1_relat_1(X1),k1_relat_1(X2))=>r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t214_relat_1)).
% 0.12/0.37  fof(t84_xboole_1, axiom, ![X1, X2, X3]:~(((~(r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3))&r1_xboole_0(X1,k4_xboole_0(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_xboole_1)).
% 0.12/0.37  fof(c_0_7, plain, ![X5, X6, X7]:(~r1_tarski(X5,X6)|~r1_xboole_0(X6,X7)|r1_xboole_0(X5,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.12/0.37  fof(c_0_8, plain, ![X17, X18, X19, X20]:((~r1_xboole_0(X17,X18)|r1_xboole_0(k2_zfmisc_1(X17,X19),k2_zfmisc_1(X18,X20)))&(~r1_xboole_0(X19,X20)|r1_xboole_0(k2_zfmisc_1(X17,X19),k2_zfmisc_1(X18,X20)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_zfmisc_1])])])).
% 0.12/0.37  fof(c_0_9, plain, ![X8, X9, X10]:(~r1_xboole_0(X8,k4_xboole_0(X9,X10))|r1_xboole_0(X9,k4_xboole_0(X8,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t81_xboole_1])])).
% 0.12/0.37  fof(c_0_10, plain, ![X14, X15, X16]:(~r1_tarski(X14,X15)|r1_xboole_0(X14,k4_xboole_0(X16,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).
% 0.12/0.37  cnf(c_0_11, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_12, plain, (r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  fof(c_0_13, plain, ![X21]:(~v1_relat_1(X21)|r1_tarski(X21,k2_zfmisc_1(k1_relat_1(X21),k2_relat_1(X21)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).
% 0.12/0.37  fof(c_0_14, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_xboole_0(k1_relat_1(X1),k1_relat_1(X2))=>r1_xboole_0(X1,X2))))), inference(assume_negation,[status(cth)],[t214_relat_1])).
% 0.12/0.37  fof(c_0_15, plain, ![X11, X12, X13]:(r1_xboole_0(X11,X12)|~r1_xboole_0(X11,X13)|~r1_xboole_0(X11,k4_xboole_0(X12,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t84_xboole_1])])])).
% 0.12/0.37  cnf(c_0_16, plain, (r1_xboole_0(X2,k4_xboole_0(X1,X3))|~r1_xboole_0(X1,k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.37  cnf(c_0_17, plain, (r1_xboole_0(X1,k4_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_18, plain, (r1_xboole_0(X1,k2_zfmisc_1(X2,X3))|~r1_xboole_0(X4,X2)|~r1_tarski(X1,k2_zfmisc_1(X4,X5))), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.12/0.37  cnf(c_0_19, plain, (r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  fof(c_0_20, negated_conjecture, (v1_relat_1(esk1_0)&(v1_relat_1(esk2_0)&(r1_xboole_0(k1_relat_1(esk1_0),k1_relat_1(esk2_0))&~r1_xboole_0(esk1_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.12/0.37  cnf(c_0_21, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)|~r1_xboole_0(X1,k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_22, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X3))|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.12/0.37  cnf(c_0_23, plain, (r1_xboole_0(X1,k2_zfmisc_1(X2,X3))|~v1_relat_1(X1)|~r1_xboole_0(k1_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.12/0.37  cnf(c_0_24, negated_conjecture, (r1_xboole_0(k1_relat_1(esk1_0),k1_relat_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.37  cnf(c_0_25, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.37  cnf(c_0_26, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.12/0.37  cnf(c_0_27, negated_conjecture, (r1_xboole_0(esk1_0,k2_zfmisc_1(k1_relat_1(esk2_0),X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])])).
% 0.12/0.37  cnf(c_0_28, negated_conjecture, (r1_xboole_0(esk1_0,X1)|~r1_tarski(X1,k2_zfmisc_1(k1_relat_1(esk2_0),X2))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.12/0.37  cnf(c_0_29, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.37  cnf(c_0_30, negated_conjecture, (~r1_xboole_0(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.37  cnf(c_0_31, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_19]), c_0_29])]), c_0_30]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 32
% 0.12/0.37  # Proof object clause steps            : 17
% 0.12/0.37  # Proof object formula steps           : 15
% 0.12/0.37  # Proof object conjectures             : 10
% 0.12/0.37  # Proof object clause conjectures      : 7
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 10
% 0.12/0.37  # Proof object initial formulas used   : 7
% 0.12/0.37  # Proof object generating inferences   : 7
% 0.12/0.37  # Proof object simplifying inferences  : 5
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 7
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 11
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 11
% 0.12/0.37  # Processed clauses                    : 48
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 2
% 0.12/0.37  # ...remaining for further processing  : 46
% 0.12/0.37  # Other redundant clauses eliminated   : 0
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 0
% 0.12/0.37  # Generated clauses                    : 38
% 0.12/0.37  # ...of the previous two non-trivial   : 37
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 38
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 0
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 35
% 0.12/0.37  #    Positive orientable unit clauses  : 5
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 1
% 0.12/0.37  #    Non-unit-clauses                  : 29
% 0.12/0.37  # Current number of unprocessed clauses: 11
% 0.12/0.37  # ...number of literals in the above   : 29
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 11
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 103
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 98
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 2
% 0.12/0.37  # Unit Clause-clause subsumption calls : 0
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 0
% 0.12/0.37  # BW rewrite match successes           : 0
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 1420
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.027 s
% 0.12/0.37  # System time              : 0.005 s
% 0.12/0.37  # Total time               : 0.032 s
% 0.12/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
