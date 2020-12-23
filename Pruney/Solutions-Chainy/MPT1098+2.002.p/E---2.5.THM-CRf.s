%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:08:30 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 149 expanded)
%              Number of clauses        :   38 (  65 expanded)
%              Number of leaves         :   11 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :  187 ( 496 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t33_finset_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( v1_finset_1(X1)
        & r1_tarski(X1,k2_zfmisc_1(X2,X3))
        & ! [X4] :
            ~ ( v1_finset_1(X4)
              & r1_tarski(X4,X2)
              & r1_tarski(X1,k2_zfmisc_1(X4,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_finset_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t13_finset_1,axiom,(
    ! [X1,X2] :
      ( ( r1_tarski(X1,X2)
        & v1_finset_1(X2) )
     => v1_finset_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_finset_1)).

fof(t32_finset_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( v1_finset_1(X1)
        & r1_tarski(X1,k2_zfmisc_1(X2,X3))
        & ! [X4,X5] :
            ~ ( v1_finset_1(X4)
              & r1_tarski(X4,X2)
              & v1_finset_1(X5)
              & r1_tarski(X5,X3)
              & r1_tarski(X1,k2_zfmisc_1(X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_finset_1)).

fof(c_0_11,plain,(
    ! [X8,X9] :
      ( ( ~ m1_subset_1(X8,k1_zfmisc_1(X9))
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | m1_subset_1(X8,k1_zfmisc_1(X9)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_12,plain,(
    ! [X21,X22,X23] :
      ( ~ v1_relat_1(X23)
      | ~ r1_tarski(k1_relat_1(X23),X21)
      | ~ r1_tarski(k2_relat_1(X23),X22)
      | m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_15,plain,(
    ! [X12,X13] :
      ( ( ~ v4_relat_1(X13,X12)
        | r1_tarski(k1_relat_1(X13),X12)
        | ~ v1_relat_1(X13) )
      & ( ~ r1_tarski(k1_relat_1(X13),X12)
        | v4_relat_1(X13,X12)
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

fof(c_0_16,plain,(
    ! [X18,X19,X20] :
      ( ( v4_relat_1(X20,X18)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) )
      & ( v5_relat_1(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( v1_finset_1(X1)
          & r1_tarski(X1,k2_zfmisc_1(X2,X3))
          & ! [X4] :
              ~ ( v1_finset_1(X4)
                & r1_tarski(X4,X2)
                & r1_tarski(X1,k2_zfmisc_1(X4,X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t33_finset_1])).

fof(c_0_18,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(X10))
      | v1_relat_1(X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X14,X15] :
      ( ( ~ v5_relat_1(X15,X14)
        | r1_tarski(k2_relat_1(X15),X14)
        | ~ v1_relat_1(X15) )
      & ( ~ r1_tarski(k2_relat_1(X15),X14)
        | v5_relat_1(X15,X14)
        | ~ v1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_22,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_24,negated_conjecture,(
    ! [X34] :
      ( v1_finset_1(esk3_0)
      & r1_tarski(esk3_0,k2_zfmisc_1(esk4_0,esk5_0))
      & ( ~ v1_finset_1(X34)
        | ~ r1_tarski(X34,esk4_0)
        | ~ r1_tarski(esk3_0,k2_zfmisc_1(X34,esk5_0)) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])])).

cnf(c_0_25,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_26,plain,(
    ! [X16,X17] : v1_relat_1(k2_zfmisc_1(X16,X17)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_27,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_29,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( v5_relat_1(X1,X2)
    | ~ r1_tarski(X1,k2_zfmisc_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk3_0,k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_23])).

cnf(c_0_33,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_35,plain,(
    ! [X24,X25] :
      ( ~ r1_tarski(X24,X25)
      | ~ v1_finset_1(X25)
      | v1_finset_1(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_finset_1])])).

cnf(c_0_36,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_37,plain,(
    ! [X26,X27,X28] :
      ( ( v1_finset_1(esk1_3(X26,X27,X28))
        | ~ v1_finset_1(X26)
        | ~ r1_tarski(X26,k2_zfmisc_1(X27,X28)) )
      & ( r1_tarski(esk1_3(X26,X27,X28),X27)
        | ~ v1_finset_1(X26)
        | ~ r1_tarski(X26,k2_zfmisc_1(X27,X28)) )
      & ( v1_finset_1(esk2_3(X26,X27,X28))
        | ~ v1_finset_1(X26)
        | ~ r1_tarski(X26,k2_zfmisc_1(X27,X28)) )
      & ( r1_tarski(esk2_3(X26,X27,X28),X28)
        | ~ v1_finset_1(X26)
        | ~ r1_tarski(X26,k2_zfmisc_1(X27,X28)) )
      & ( r1_tarski(X26,k2_zfmisc_1(esk1_3(X26,X27,X28),esk2_3(X26,X27,X28)))
        | ~ v1_finset_1(X26)
        | ~ r1_tarski(X26,k2_zfmisc_1(X27,X28)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_finset_1])])])])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ v5_relat_1(X1,X3)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_39,negated_conjecture,
    ( v5_relat_1(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_31]),c_0_33])])).

cnf(c_0_41,plain,
    ( v4_relat_1(X1,X2)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_43,plain,
    ( v1_finset_1(X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_finset_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( v4_relat_1(X1,X2)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_23])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,k2_zfmisc_1(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)))
    | ~ v1_finset_1(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(esk3_0,k2_zfmisc_1(X1,esk5_0))
    | ~ v4_relat_1(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])])).

cnf(c_0_47,plain,
    ( v4_relat_1(X1,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,plain,
    ( v1_finset_1(k1_relat_1(X1))
    | ~ v1_finset_1(X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_20])).

cnf(c_0_49,plain,
    ( v4_relat_1(X1,esk1_3(X1,X2,X3))
    | ~ v1_finset_1(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,plain,
    ( v1_relat_1(X1)
    | ~ v1_finset_1(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_45]),c_0_33])])).

cnf(c_0_51,plain,
    ( v1_finset_1(esk1_3(X1,X2,X3))
    | ~ v1_finset_1(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_52,negated_conjecture,
    ( ~ v1_finset_1(X1)
    | ~ r1_tarski(X1,esk4_0)
    | ~ r1_tarski(esk3_0,k2_zfmisc_1(X1,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(esk3_0,k2_zfmisc_1(k1_relat_1(esk3_0),esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_40])])).

cnf(c_0_54,plain,
    ( v1_finset_1(k1_relat_1(X1))
    | ~ v1_finset_1(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( v1_finset_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_56,negated_conjecture,
    ( ~ v1_finset_1(k1_relat_1(esk3_0))
    | ~ r1_tarski(k1_relat_1(esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( v1_finset_1(k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_31]),c_0_55])])).

cnf(c_0_58,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57])])).

cnf(c_0_59,negated_conjecture,
    ( v4_relat_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_31])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_20]),c_0_59]),c_0_40])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:49:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.028 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.38  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 0.19/0.38  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 0.19/0.38  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.38  fof(t33_finset_1, conjecture, ![X1, X2, X3]:~(((v1_finset_1(X1)&r1_tarski(X1,k2_zfmisc_1(X2,X3)))&![X4]:~(((v1_finset_1(X4)&r1_tarski(X4,X2))&r1_tarski(X1,k2_zfmisc_1(X4,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_finset_1)).
% 0.19/0.38  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.19/0.38  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 0.19/0.38  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.19/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.38  fof(t13_finset_1, axiom, ![X1, X2]:((r1_tarski(X1,X2)&v1_finset_1(X2))=>v1_finset_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_finset_1)).
% 0.19/0.38  fof(t32_finset_1, axiom, ![X1, X2, X3]:~(((v1_finset_1(X1)&r1_tarski(X1,k2_zfmisc_1(X2,X3)))&![X4, X5]:~(((((v1_finset_1(X4)&r1_tarski(X4,X2))&v1_finset_1(X5))&r1_tarski(X5,X3))&r1_tarski(X1,k2_zfmisc_1(X4,X5)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_finset_1)).
% 0.19/0.38  fof(c_0_11, plain, ![X8, X9]:((~m1_subset_1(X8,k1_zfmisc_1(X9))|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|m1_subset_1(X8,k1_zfmisc_1(X9)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.38  fof(c_0_12, plain, ![X21, X22, X23]:(~v1_relat_1(X23)|(~r1_tarski(k1_relat_1(X23),X21)|~r1_tarski(k2_relat_1(X23),X22)|m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 0.19/0.38  cnf(c_0_13, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_14, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  fof(c_0_15, plain, ![X12, X13]:((~v4_relat_1(X13,X12)|r1_tarski(k1_relat_1(X13),X12)|~v1_relat_1(X13))&(~r1_tarski(k1_relat_1(X13),X12)|v4_relat_1(X13,X12)|~v1_relat_1(X13))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.19/0.38  fof(c_0_16, plain, ![X18, X19, X20]:((v4_relat_1(X20,X18)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))))&(v5_relat_1(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.38  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3]:~(((v1_finset_1(X1)&r1_tarski(X1,k2_zfmisc_1(X2,X3)))&![X4]:~(((v1_finset_1(X4)&r1_tarski(X4,X2))&r1_tarski(X1,k2_zfmisc_1(X4,X3))))))), inference(assume_negation,[status(cth)],[t33_finset_1])).
% 0.19/0.38  fof(c_0_18, plain, ![X10, X11]:(~v1_relat_1(X10)|(~m1_subset_1(X11,k1_zfmisc_1(X10))|v1_relat_1(X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.19/0.38  cnf(c_0_19, plain, (r1_tarski(X1,k2_zfmisc_1(X2,X3))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.38  cnf(c_0_20, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  fof(c_0_21, plain, ![X14, X15]:((~v5_relat_1(X15,X14)|r1_tarski(k2_relat_1(X15),X14)|~v1_relat_1(X15))&(~r1_tarski(k2_relat_1(X15),X14)|v5_relat_1(X15,X14)|~v1_relat_1(X15))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.19/0.38  cnf(c_0_22, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_23, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  fof(c_0_24, negated_conjecture, ![X34]:((v1_finset_1(esk3_0)&r1_tarski(esk3_0,k2_zfmisc_1(esk4_0,esk5_0)))&(~v1_finset_1(X34)|~r1_tarski(X34,esk4_0)|~r1_tarski(esk3_0,k2_zfmisc_1(X34,esk5_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])])).
% 0.19/0.38  cnf(c_0_25, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.38  fof(c_0_26, plain, ![X16, X17]:v1_relat_1(k2_zfmisc_1(X16,X17)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.19/0.38  fof(c_0_27, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.38  cnf(c_0_28, plain, (r1_tarski(X1,k2_zfmisc_1(X2,X3))|~v4_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X3)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.38  cnf(c_0_29, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.38  cnf(c_0_30, plain, (v5_relat_1(X1,X2)|~r1_tarski(X1,k2_zfmisc_1(X3,X2))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.38  cnf(c_0_31, negated_conjecture, (r1_tarski(esk3_0,k2_zfmisc_1(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.38  cnf(c_0_32, plain, (v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_25, c_0_23])).
% 0.19/0.38  cnf(c_0_33, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.38  cnf(c_0_34, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.38  fof(c_0_35, plain, ![X24, X25]:(~r1_tarski(X24,X25)|~v1_finset_1(X25)|v1_finset_1(X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_finset_1])])).
% 0.19/0.38  cnf(c_0_36, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  fof(c_0_37, plain, ![X26, X27, X28]:(((((v1_finset_1(esk1_3(X26,X27,X28))|(~v1_finset_1(X26)|~r1_tarski(X26,k2_zfmisc_1(X27,X28))))&(r1_tarski(esk1_3(X26,X27,X28),X27)|(~v1_finset_1(X26)|~r1_tarski(X26,k2_zfmisc_1(X27,X28)))))&(v1_finset_1(esk2_3(X26,X27,X28))|(~v1_finset_1(X26)|~r1_tarski(X26,k2_zfmisc_1(X27,X28)))))&(r1_tarski(esk2_3(X26,X27,X28),X28)|(~v1_finset_1(X26)|~r1_tarski(X26,k2_zfmisc_1(X27,X28)))))&(r1_tarski(X26,k2_zfmisc_1(esk1_3(X26,X27,X28),esk2_3(X26,X27,X28)))|(~v1_finset_1(X26)|~r1_tarski(X26,k2_zfmisc_1(X27,X28))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_finset_1])])])])).
% 0.19/0.38  cnf(c_0_38, plain, (r1_tarski(X1,k2_zfmisc_1(X2,X3))|~v5_relat_1(X1,X3)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.38  cnf(c_0_39, negated_conjecture, (v5_relat_1(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.38  cnf(c_0_40, negated_conjecture, (v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_31]), c_0_33])])).
% 0.19/0.38  cnf(c_0_41, plain, (v4_relat_1(X1,X2)|~r1_tarski(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_42, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_34])).
% 0.19/0.38  cnf(c_0_43, plain, (v1_finset_1(X1)|~r1_tarski(X1,X2)|~v1_finset_1(X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.38  cnf(c_0_44, plain, (v4_relat_1(X1,X2)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_36, c_0_23])).
% 0.19/0.38  cnf(c_0_45, plain, (r1_tarski(X1,k2_zfmisc_1(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)))|~v1_finset_1(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.38  cnf(c_0_46, negated_conjecture, (r1_tarski(esk3_0,k2_zfmisc_1(X1,esk5_0))|~v4_relat_1(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])])).
% 0.19/0.38  cnf(c_0_47, plain, (v4_relat_1(X1,k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.38  cnf(c_0_48, plain, (v1_finset_1(k1_relat_1(X1))|~v1_finset_1(X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_43, c_0_20])).
% 0.19/0.38  cnf(c_0_49, plain, (v4_relat_1(X1,esk1_3(X1,X2,X3))|~v1_finset_1(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.38  cnf(c_0_50, plain, (v1_relat_1(X1)|~v1_finset_1(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_45]), c_0_33])])).
% 0.19/0.38  cnf(c_0_51, plain, (v1_finset_1(esk1_3(X1,X2,X3))|~v1_finset_1(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.38  cnf(c_0_52, negated_conjecture, (~v1_finset_1(X1)|~r1_tarski(X1,esk4_0)|~r1_tarski(esk3_0,k2_zfmisc_1(X1,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.38  cnf(c_0_53, negated_conjecture, (r1_tarski(esk3_0,k2_zfmisc_1(k1_relat_1(esk3_0),esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_40])])).
% 0.19/0.38  cnf(c_0_54, plain, (v1_finset_1(k1_relat_1(X1))|~v1_finset_1(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_51])).
% 0.19/0.38  cnf(c_0_55, negated_conjecture, (v1_finset_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.38  cnf(c_0_56, negated_conjecture, (~v1_finset_1(k1_relat_1(esk3_0))|~r1_tarski(k1_relat_1(esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.19/0.38  cnf(c_0_57, negated_conjecture, (v1_finset_1(k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_31]), c_0_55])])).
% 0.19/0.38  cnf(c_0_58, negated_conjecture, (~r1_tarski(k1_relat_1(esk3_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57])])).
% 0.19/0.38  cnf(c_0_59, negated_conjecture, (v4_relat_1(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_44, c_0_31])).
% 0.19/0.38  cnf(c_0_60, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_20]), c_0_59]), c_0_40])]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 61
% 0.19/0.38  # Proof object clause steps            : 38
% 0.19/0.38  # Proof object formula steps           : 23
% 0.19/0.38  # Proof object conjectures             : 15
% 0.19/0.38  # Proof object clause conjectures      : 12
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 17
% 0.19/0.38  # Proof object initial formulas used   : 11
% 0.19/0.38  # Proof object generating inferences   : 19
% 0.19/0.38  # Proof object simplifying inferences  : 18
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 11
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 23
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 23
% 0.19/0.38  # Processed clauses                    : 123
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 12
% 0.19/0.38  # ...remaining for further processing  : 111
% 0.19/0.38  # Other redundant clauses eliminated   : 2
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 1
% 0.19/0.38  # Generated clauses                    : 200
% 0.19/0.38  # ...of the previous two non-trivial   : 165
% 0.19/0.38  # Contextual simplify-reflections      : 2
% 0.19/0.38  # Paramodulations                      : 198
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 2
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 86
% 0.19/0.38  #    Positive orientable unit clauses  : 18
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 2
% 0.19/0.38  #    Non-unit-clauses                  : 66
% 0.19/0.38  # Current number of unprocessed clauses: 87
% 0.19/0.38  # ...number of literals in the above   : 323
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 23
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 540
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 340
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 13
% 0.19/0.38  # Unit Clause-clause subsumption calls : 79
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 7
% 0.19/0.38  # BW rewrite match successes           : 1
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 4957
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.034 s
% 0.19/0.38  # System time              : 0.005 s
% 0.19/0.38  # Total time               : 0.039 s
% 0.19/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
