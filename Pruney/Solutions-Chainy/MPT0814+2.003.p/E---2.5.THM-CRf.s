%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:57:01 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 123 expanded)
%              Number of clauses        :   32 (  52 expanded)
%              Number of leaves         :   11 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  175 ( 417 expanded)
%              Number of equality atoms :   16 (  60 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t6_relset_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
     => ~ ( r2_hidden(X1,X4)
          & ! [X5,X6] :
              ~ ( X1 = k4_tarski(X5,X6)
                & r2_hidden(X5,X2)
                & r2_hidden(X6,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).

fof(t79_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k5_relat_1(X2,k6_relat_1(X1)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(t75_relat_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( v1_relat_1(X4)
     => ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(X4,k6_relat_1(X3)))
      <=> ( r2_hidden(X2,X3)
          & r2_hidden(k4_tarski(X1,X2),X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_relat_1)).

fof(l139_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
        & ! [X4,X5] : k4_tarski(X4,X5) != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(t77_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k5_relat_1(k6_relat_1(X1),X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(t74_relat_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( v1_relat_1(X4)
     => ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(k6_relat_1(X3),X4))
      <=> ( r2_hidden(X1,X3)
          & r2_hidden(k4_tarski(X1,X2),X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_relat_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
       => ~ ( r2_hidden(X1,X4)
            & ! [X5,X6] :
                ~ ( X1 = k4_tarski(X5,X6)
                  & r2_hidden(X5,X2)
                  & r2_hidden(X6,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t6_relset_1])).

fof(c_0_12,plain,(
    ! [X29,X30] :
      ( ~ v1_relat_1(X30)
      | ~ r1_tarski(k2_relat_1(X30),X29)
      | k5_relat_1(X30,k6_relat_1(X29)) = X30 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_relat_1])])).

fof(c_0_13,plain,(
    ! [X17,X18] :
      ( ( ~ v5_relat_1(X18,X17)
        | r1_tarski(k2_relat_1(X18),X17)
        | ~ v1_relat_1(X18) )
      & ( ~ r1_tarski(k2_relat_1(X18),X17)
        | v5_relat_1(X18,X17)
        | ~ v1_relat_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

fof(c_0_14,plain,(
    ! [X12,X13,X14] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(X12))
      | ~ r2_hidden(X14,X13)
      | r2_hidden(X14,X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_15,negated_conjecture,(
    ! [X41,X42] :
      ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
      & r2_hidden(esk3_0,esk6_0)
      & ( esk3_0 != k4_tarski(X41,X42)
        | ~ r2_hidden(X41,esk4_0)
        | ~ r2_hidden(X42,esk5_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).

fof(c_0_16,plain,(
    ! [X23,X24,X25,X26] :
      ( ( r2_hidden(X24,X25)
        | ~ r2_hidden(k4_tarski(X23,X24),k5_relat_1(X26,k6_relat_1(X25)))
        | ~ v1_relat_1(X26) )
      & ( r2_hidden(k4_tarski(X23,X24),X26)
        | ~ r2_hidden(k4_tarski(X23,X24),k5_relat_1(X26,k6_relat_1(X25)))
        | ~ v1_relat_1(X26) )
      & ( ~ r2_hidden(X24,X25)
        | ~ r2_hidden(k4_tarski(X23,X24),X26)
        | r2_hidden(k4_tarski(X23,X24),k5_relat_1(X26,k6_relat_1(X25)))
        | ~ v1_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t75_relat_1])])])).

cnf(c_0_17,plain,
    ( k5_relat_1(X1,k6_relat_1(X2)) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X7,X8,X9] :
      ( ~ r2_hidden(X7,k2_zfmisc_1(X8,X9))
      | k4_tarski(esk1_1(X7),esk2_1(X7)) = X7 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).

cnf(c_0_20,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X27,X28] :
      ( ~ v1_relat_1(X28)
      | ~ r1_tarski(k1_relat_1(X28),X27)
      | k5_relat_1(k6_relat_1(X27),X28) = X28 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).

fof(c_0_23,plain,(
    ! [X15,X16] :
      ( ( ~ v4_relat_1(X16,X15)
        | r1_tarski(k1_relat_1(X16),X15)
        | ~ v1_relat_1(X16) )
      & ( ~ r1_tarski(k1_relat_1(X16),X15)
        | v4_relat_1(X16,X15)
        | ~ v1_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,k6_relat_1(X2)))
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( k5_relat_1(X1,k6_relat_1(X2)) = X1
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_26,plain,
    ( k4_tarski(esk1_1(X1),esk2_1(X1)) = X1
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk4_0,esk5_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_28,plain,(
    ! [X19,X20,X21,X22] :
      ( ( r2_hidden(X19,X21)
        | ~ r2_hidden(k4_tarski(X19,X20),k5_relat_1(k6_relat_1(X21),X22))
        | ~ v1_relat_1(X22) )
      & ( r2_hidden(k4_tarski(X19,X20),X22)
        | ~ r2_hidden(k4_tarski(X19,X20),k5_relat_1(k6_relat_1(X21),X22))
        | ~ v1_relat_1(X22) )
      & ( ~ r2_hidden(X19,X21)
        | ~ r2_hidden(k4_tarski(X19,X20),X22)
        | r2_hidden(k4_tarski(X19,X20),k5_relat_1(k6_relat_1(X21),X22))
        | ~ v1_relat_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_relat_1])])])).

cnf(c_0_29,plain,
    ( k5_relat_1(k6_relat_1(X2),X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X2)
    | ~ v5_relat_1(X3,X2)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X4,X1),X3) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( k4_tarski(esk1_1(X1),esk2_1(X1)) = X1
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_33,plain,(
    ! [X31,X32,X33] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | v1_relat_1(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k5_relat_1(k6_relat_1(X2),X4))
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( k5_relat_1(k6_relat_1(X1),X2) = X2
    | ~ v4_relat_1(X2,X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk2_1(X1),X2)
    | ~ v5_relat_1(X3,X2)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk3_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_38,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_39,plain,(
    ! [X34,X35,X36] :
      ( ( v4_relat_1(X36,X34)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( v5_relat_1(X36,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X2)
    | ~ v4_relat_1(X3,X2)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X1,X4),X3) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( esk3_0 != k4_tarski(X1,X2)
    | ~ r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X2,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk2_1(esk3_0),X1)
    | ~ v5_relat_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(esk3_0,X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_21])).

cnf(c_0_44,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk1_1(X1),X2)
    | ~ v4_relat_1(X3,X2)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_40,c_0_32])).

cnf(c_0_46,negated_conjecture,
    ( ~ r2_hidden(esk2_1(esk3_0),esk5_0)
    | ~ r2_hidden(esk1_1(esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_32])]),c_0_37])])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk2_1(esk3_0),X1)
    | ~ v5_relat_1(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_37]),c_0_43])])).

cnf(c_0_48,negated_conjecture,
    ( v5_relat_1(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_21])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk1_1(esk3_0),X1)
    | ~ v4_relat_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(esk3_0,X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_37])).

cnf(c_0_50,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_51,negated_conjecture,
    ( ~ r2_hidden(esk1_1(esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk1_1(esk3_0),X1)
    | ~ v4_relat_1(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_37]),c_0_43])])).

cnf(c_0_53,negated_conjecture,
    ( v4_relat_1(esk6_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_21])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:55:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.028 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t6_relset_1, conjecture, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))=>~((r2_hidden(X1,X4)&![X5, X6]:~(((X1=k4_tarski(X5,X6)&r2_hidden(X5,X2))&r2_hidden(X6,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_relset_1)).
% 0.14/0.38  fof(t79_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X2),X1)=>k5_relat_1(X2,k6_relat_1(X1))=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 0.14/0.38  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 0.14/0.38  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.14/0.38  fof(t75_relat_1, axiom, ![X1, X2, X3, X4]:(v1_relat_1(X4)=>(r2_hidden(k4_tarski(X1,X2),k5_relat_1(X4,k6_relat_1(X3)))<=>(r2_hidden(X2,X3)&r2_hidden(k4_tarski(X1,X2),X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_relat_1)).
% 0.14/0.38  fof(l139_zfmisc_1, axiom, ![X1, X2, X3]:~((r2_hidden(X1,k2_zfmisc_1(X2,X3))&![X4, X5]:k4_tarski(X4,X5)!=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 0.14/0.38  fof(t77_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k5_relat_1(k6_relat_1(X1),X2)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 0.14/0.38  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 0.14/0.38  fof(t74_relat_1, axiom, ![X1, X2, X3, X4]:(v1_relat_1(X4)=>(r2_hidden(k4_tarski(X1,X2),k5_relat_1(k6_relat_1(X3),X4))<=>(r2_hidden(X1,X3)&r2_hidden(k4_tarski(X1,X2),X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_relat_1)).
% 0.14/0.38  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.14/0.38  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.14/0.38  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))=>~((r2_hidden(X1,X4)&![X5, X6]:~(((X1=k4_tarski(X5,X6)&r2_hidden(X5,X2))&r2_hidden(X6,X3))))))), inference(assume_negation,[status(cth)],[t6_relset_1])).
% 0.14/0.38  fof(c_0_12, plain, ![X29, X30]:(~v1_relat_1(X30)|(~r1_tarski(k2_relat_1(X30),X29)|k5_relat_1(X30,k6_relat_1(X29))=X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_relat_1])])).
% 0.14/0.38  fof(c_0_13, plain, ![X17, X18]:((~v5_relat_1(X18,X17)|r1_tarski(k2_relat_1(X18),X17)|~v1_relat_1(X18))&(~r1_tarski(k2_relat_1(X18),X17)|v5_relat_1(X18,X17)|~v1_relat_1(X18))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.14/0.38  fof(c_0_14, plain, ![X12, X13, X14]:(~m1_subset_1(X13,k1_zfmisc_1(X12))|(~r2_hidden(X14,X13)|r2_hidden(X14,X12))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.14/0.38  fof(c_0_15, negated_conjecture, ![X41, X42]:(m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))&(r2_hidden(esk3_0,esk6_0)&(esk3_0!=k4_tarski(X41,X42)|~r2_hidden(X41,esk4_0)|~r2_hidden(X42,esk5_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).
% 0.14/0.38  fof(c_0_16, plain, ![X23, X24, X25, X26]:(((r2_hidden(X24,X25)|~r2_hidden(k4_tarski(X23,X24),k5_relat_1(X26,k6_relat_1(X25)))|~v1_relat_1(X26))&(r2_hidden(k4_tarski(X23,X24),X26)|~r2_hidden(k4_tarski(X23,X24),k5_relat_1(X26,k6_relat_1(X25)))|~v1_relat_1(X26)))&(~r2_hidden(X24,X25)|~r2_hidden(k4_tarski(X23,X24),X26)|r2_hidden(k4_tarski(X23,X24),k5_relat_1(X26,k6_relat_1(X25)))|~v1_relat_1(X26))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t75_relat_1])])])).
% 0.14/0.38  cnf(c_0_17, plain, (k5_relat_1(X1,k6_relat_1(X2))=X1|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_18, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  fof(c_0_19, plain, ![X7, X8, X9]:(~r2_hidden(X7,k2_zfmisc_1(X8,X9))|k4_tarski(esk1_1(X7),esk2_1(X7))=X7), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).
% 0.14/0.38  cnf(c_0_20, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.38  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  fof(c_0_22, plain, ![X27, X28]:(~v1_relat_1(X28)|(~r1_tarski(k1_relat_1(X28),X27)|k5_relat_1(k6_relat_1(X27),X28)=X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).
% 0.14/0.38  fof(c_0_23, plain, ![X15, X16]:((~v4_relat_1(X16,X15)|r1_tarski(k1_relat_1(X16),X15)|~v1_relat_1(X16))&(~r1_tarski(k1_relat_1(X16),X15)|v4_relat_1(X16,X15)|~v1_relat_1(X16))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.14/0.38  cnf(c_0_24, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,k6_relat_1(X2)))|~v1_relat_1(X4)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.38  cnf(c_0_25, plain, (k5_relat_1(X1,k6_relat_1(X2))=X1|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.14/0.38  cnf(c_0_26, plain, (k4_tarski(esk1_1(X1),esk2_1(X1))=X1|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.38  cnf(c_0_27, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(esk4_0,esk5_0))|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.14/0.38  fof(c_0_28, plain, ![X19, X20, X21, X22]:(((r2_hidden(X19,X21)|~r2_hidden(k4_tarski(X19,X20),k5_relat_1(k6_relat_1(X21),X22))|~v1_relat_1(X22))&(r2_hidden(k4_tarski(X19,X20),X22)|~r2_hidden(k4_tarski(X19,X20),k5_relat_1(k6_relat_1(X21),X22))|~v1_relat_1(X22)))&(~r2_hidden(X19,X21)|~r2_hidden(k4_tarski(X19,X20),X22)|r2_hidden(k4_tarski(X19,X20),k5_relat_1(k6_relat_1(X21),X22))|~v1_relat_1(X22))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_relat_1])])])).
% 0.14/0.38  cnf(c_0_29, plain, (k5_relat_1(k6_relat_1(X2),X1)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.38  cnf(c_0_30, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.38  cnf(c_0_31, plain, (r2_hidden(X1,X2)|~v5_relat_1(X3,X2)|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X4,X1),X3)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.14/0.38  cnf(c_0_32, negated_conjecture, (k4_tarski(esk1_1(X1),esk2_1(X1))=X1|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.14/0.38  fof(c_0_33, plain, ![X31, X32, X33]:(~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|v1_relat_1(X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.14/0.38  cnf(c_0_34, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k5_relat_1(k6_relat_1(X2),X4))|~v1_relat_1(X4)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.14/0.38  cnf(c_0_35, plain, (k5_relat_1(k6_relat_1(X1),X2)=X2|~v4_relat_1(X2,X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.14/0.38  cnf(c_0_36, negated_conjecture, (r2_hidden(esk2_1(X1),X2)|~v5_relat_1(X3,X2)|~v1_relat_1(X3)|~r2_hidden(X1,esk6_0)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.14/0.38  cnf(c_0_37, negated_conjecture, (r2_hidden(esk3_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  cnf(c_0_38, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.14/0.38  fof(c_0_39, plain, ![X34, X35, X36]:((v4_relat_1(X36,X34)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))&(v5_relat_1(X36,X35)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.14/0.38  cnf(c_0_40, plain, (r2_hidden(X1,X2)|~v4_relat_1(X3,X2)|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X1,X4),X3)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.14/0.38  cnf(c_0_41, negated_conjecture, (esk3_0!=k4_tarski(X1,X2)|~r2_hidden(X1,esk4_0)|~r2_hidden(X2,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  cnf(c_0_42, negated_conjecture, (r2_hidden(esk2_1(esk3_0),X1)|~v5_relat_1(X2,X1)|~v1_relat_1(X2)|~r2_hidden(esk3_0,X2)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.14/0.38  cnf(c_0_43, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_38, c_0_21])).
% 0.14/0.38  cnf(c_0_44, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.14/0.38  cnf(c_0_45, negated_conjecture, (r2_hidden(esk1_1(X1),X2)|~v4_relat_1(X3,X2)|~v1_relat_1(X3)|~r2_hidden(X1,esk6_0)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_40, c_0_32])).
% 0.14/0.38  cnf(c_0_46, negated_conjecture, (~r2_hidden(esk2_1(esk3_0),esk5_0)|~r2_hidden(esk1_1(esk3_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_32])]), c_0_37])])).
% 0.14/0.38  cnf(c_0_47, negated_conjecture, (r2_hidden(esk2_1(esk3_0),X1)|~v5_relat_1(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_37]), c_0_43])])).
% 0.14/0.38  cnf(c_0_48, negated_conjecture, (v5_relat_1(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_44, c_0_21])).
% 0.14/0.38  cnf(c_0_49, negated_conjecture, (r2_hidden(esk1_1(esk3_0),X1)|~v4_relat_1(X2,X1)|~v1_relat_1(X2)|~r2_hidden(esk3_0,X2)), inference(spm,[status(thm)],[c_0_45, c_0_37])).
% 0.14/0.38  cnf(c_0_50, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.14/0.38  cnf(c_0_51, negated_conjecture, (~r2_hidden(esk1_1(esk3_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])])).
% 0.14/0.38  cnf(c_0_52, negated_conjecture, (r2_hidden(esk1_1(esk3_0),X1)|~v4_relat_1(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_37]), c_0_43])])).
% 0.14/0.38  cnf(c_0_53, negated_conjecture, (v4_relat_1(esk6_0,esk4_0)), inference(spm,[status(thm)],[c_0_50, c_0_21])).
% 0.14/0.38  cnf(c_0_54, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 55
% 0.14/0.38  # Proof object clause steps            : 32
% 0.14/0.38  # Proof object formula steps           : 23
% 0.14/0.38  # Proof object conjectures             : 20
% 0.14/0.38  # Proof object clause conjectures      : 17
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 14
% 0.14/0.38  # Proof object initial formulas used   : 11
% 0.14/0.38  # Proof object generating inferences   : 18
% 0.14/0.38  # Proof object simplifying inferences  : 11
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 11
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 20
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 20
% 0.14/0.38  # Processed clauses                    : 64
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 0
% 0.14/0.38  # ...remaining for further processing  : 64
% 0.14/0.38  # Other redundant clauses eliminated   : 1
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 0
% 0.14/0.38  # Backward-rewritten                   : 0
% 0.14/0.38  # Generated clauses                    : 73
% 0.14/0.38  # ...of the previous two non-trivial   : 57
% 0.14/0.38  # Contextual simplify-reflections      : 0
% 0.14/0.38  # Paramodulations                      : 72
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 1
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 44
% 0.14/0.38  #    Positive orientable unit clauses  : 5
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 1
% 0.14/0.38  #    Non-unit-clauses                  : 38
% 0.14/0.38  # Current number of unprocessed clauses: 28
% 0.14/0.38  # ...number of literals in the above   : 145
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 20
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 320
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 161
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.38  # Unit Clause-clause subsumption calls : 28
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 0
% 0.14/0.38  # BW rewrite match successes           : 0
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 3123
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.029 s
% 0.14/0.38  # System time              : 0.006 s
% 0.14/0.38  # Total time               : 0.035 s
% 0.14/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
