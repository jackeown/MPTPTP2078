%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:05:26 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 120 expanded)
%              Number of clauses        :   33 (  50 expanded)
%              Number of leaves         :   13 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :  190 ( 334 expanded)
%              Number of equality atoms :   72 ( 126 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t65_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,k1_tarski(X2))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
     => ( r2_hidden(X3,X1)
       => k1_funct_1(X4,X3) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t129_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k1_tarski(X4)))
    <=> ( r2_hidden(X1,X3)
        & X2 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(d1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
         => ( v1_funct_2(X3,X1,X2)
          <=> X1 = k1_relset_1(X1,X2,X3) ) )
        & ( X2 = k1_xboole_0
         => ( X1 = k1_xboole_0
            | ( v1_funct_2(X3,X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,k1_tarski(X2))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
       => ( r2_hidden(X3,X1)
         => k1_funct_1(X4,X3) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t65_funct_2])).

fof(c_0_14,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk2_0,k1_tarski(esk3_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_tarski(esk3_0))))
    & r2_hidden(esk4_0,esk2_0)
    & k1_funct_1(esk5_0,esk4_0) != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_15,plain,(
    ! [X15] : k2_tarski(X15,X15) = k1_tarski(X15) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_16,plain,(
    ! [X16,X17] : k1_enumset1(X16,X16,X17) = k2_tarski(X16,X17) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_17,plain,(
    ! [X18,X19,X20,X21] :
      ( ( r2_hidden(X18,X20)
        | ~ r2_hidden(k4_tarski(X18,X19),k2_zfmisc_1(X20,k1_tarski(X21))) )
      & ( X19 = X21
        | ~ r2_hidden(k4_tarski(X18,X19),k2_zfmisc_1(X20,k1_tarski(X21))) )
      & ( ~ r2_hidden(X18,X20)
        | X19 != X21
        | r2_hidden(k4_tarski(X18,X19),k2_zfmisc_1(X20,k1_tarski(X21))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t129_zfmisc_1])])])).

fof(c_0_18,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(X22))
      | ~ r2_hidden(X24,X23)
      | r2_hidden(X24,X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_tarski(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12,X13] :
      ( ( ~ r2_hidden(X9,X8)
        | X9 = X6
        | X9 = X7
        | X8 != k2_tarski(X6,X7) )
      & ( X10 != X6
        | r2_hidden(X10,X8)
        | X8 != k2_tarski(X6,X7) )
      & ( X10 != X7
        | r2_hidden(X10,X8)
        | X8 != k2_tarski(X6,X7) )
      & ( esk1_3(X11,X12,X13) != X11
        | ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k2_tarski(X11,X12) )
      & ( esk1_3(X11,X12,X13) != X12
        | ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k2_tarski(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X13)
        | esk1_3(X11,X12,X13) = X11
        | esk1_3(X11,X12,X13) = X12
        | X13 = k2_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_23,plain,(
    ! [X34,X35,X36] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
      | k1_relset_1(X34,X35,X36) = k1_relat_1(X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_24,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

fof(c_0_27,plain,(
    ! [X29,X30,X31] :
      ( ( r2_hidden(X29,k1_relat_1(X31))
        | ~ r2_hidden(k4_tarski(X29,X30),X31)
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) )
      & ( X30 = k1_funct_1(X31,X29)
        | ~ r2_hidden(k4_tarski(X29,X30),X31)
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) )
      & ( ~ r2_hidden(X29,k1_relat_1(X31))
        | X30 != k1_funct_1(X31,X29)
        | r2_hidden(k4_tarski(X29,X30),X31)
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

fof(c_0_28,plain,(
    ! [X25,X26] :
      ( ~ v1_relat_1(X25)
      | ~ m1_subset_1(X26,k1_zfmisc_1(X25))
      | v1_relat_1(X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_29,plain,(
    ! [X27,X28] : v1_relat_1(k2_zfmisc_1(X27,X28)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_31,plain,(
    ! [X37,X38,X39] :
      ( ( ~ v1_funct_2(X39,X37,X38)
        | X37 = k1_relset_1(X37,X38,X39)
        | X38 = k1_xboole_0
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( X37 != k1_relset_1(X37,X38,X39)
        | v1_funct_2(X39,X37,X38)
        | X38 = k1_xboole_0
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( ~ v1_funct_2(X39,X37,X38)
        | X37 = k1_relset_1(X37,X38,X39)
        | X37 != k1_xboole_0
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( X37 != k1_relset_1(X37,X38,X39)
        | v1_funct_2(X39,X37,X38)
        | X37 != k1_xboole_0
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( ~ v1_funct_2(X39,X37,X38)
        | X39 = k1_xboole_0
        | X37 = k1_xboole_0
        | X38 != k1_xboole_0
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( X39 != k1_xboole_0
        | v1_funct_2(X39,X37,X38)
        | X37 = k1_xboole_0
        | X38 != k1_xboole_0
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_32,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_2(esk5_0,esk2_0,k1_tarski(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_34,plain,(
    ! [X32,X33] :
      ( ~ r2_hidden(X32,X33)
      | ~ r1_tarski(X33,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_35,plain,(
    ! [X5] : r1_tarski(k1_xboole_0,X5) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_36,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,k1_enumset1(X2,X2,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_20]),c_0_21])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0)))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_38,plain,
    ( r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X2,X4) ),
    inference(rw,[status(thm)],[c_0_30,c_0_21])).

cnf(c_0_42,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,negated_conjecture,
    ( k1_relset_1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0),esk5_0) = k1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_26])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_2(esk5_0,esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_20]),c_0_21])).

cnf(c_0_45,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_47,negated_conjecture,
    ( X1 = esk3_0
    | ~ r2_hidden(k4_tarski(X2,X1),esk5_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_48,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_50,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_26]),c_0_40])])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,k1_enumset1(X1,X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_41])])).

cnf(c_0_52,negated_conjecture,
    ( k1_enumset1(esk3_0,esk3_0,esk3_0) = k1_xboole_0
    | k1_relat_1(esk5_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_26]),c_0_43]),c_0_44])])).

cnf(c_0_53,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( k1_funct_1(esk5_0,X1) = esk3_0
    | ~ r2_hidden(X1,k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_50])])).

cnf(c_0_55,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk2_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( k1_funct_1(esk5_0,esk4_0) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_57,negated_conjecture,
    ( k1_funct_1(esk5_0,X1) = esk3_0
    | ~ r2_hidden(X1,esk2_0) ),
    inference(rw,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 19:28:51 EST 2020
% 0.21/0.36  % CPUTime    : 
% 0.21/0.36  # Version: 2.5pre002
% 0.21/0.36  # No SInE strategy applied
% 0.21/0.36  # Trying AutoSched0 for 299 seconds
% 0.21/0.41  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.21/0.41  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.21/0.41  #
% 0.21/0.41  # Preprocessing time       : 0.028 s
% 0.21/0.41  
% 0.21/0.41  # Proof found!
% 0.21/0.41  # SZS status Theorem
% 0.21/0.41  # SZS output start CNFRefutation
% 0.21/0.41  fof(t65_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>(r2_hidden(X3,X1)=>k1_funct_1(X4,X3)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 0.21/0.41  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.21/0.41  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.41  fof(t129_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k1_tarski(X4)))<=>(r2_hidden(X1,X3)&X2=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 0.21/0.41  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.21/0.41  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.21/0.41  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.21/0.41  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 0.21/0.41  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.21/0.41  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.21/0.41  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.21/0.41  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.21/0.41  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.21/0.41  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>(r2_hidden(X3,X1)=>k1_funct_1(X4,X3)=X2))), inference(assume_negation,[status(cth)],[t65_funct_2])).
% 0.21/0.41  fof(c_0_14, negated_conjecture, (((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk2_0,k1_tarski(esk3_0)))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_tarski(esk3_0)))))&(r2_hidden(esk4_0,esk2_0)&k1_funct_1(esk5_0,esk4_0)!=esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.21/0.41  fof(c_0_15, plain, ![X15]:k2_tarski(X15,X15)=k1_tarski(X15), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.41  fof(c_0_16, plain, ![X16, X17]:k1_enumset1(X16,X16,X17)=k2_tarski(X16,X17), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.41  fof(c_0_17, plain, ![X18, X19, X20, X21]:(((r2_hidden(X18,X20)|~r2_hidden(k4_tarski(X18,X19),k2_zfmisc_1(X20,k1_tarski(X21))))&(X19=X21|~r2_hidden(k4_tarski(X18,X19),k2_zfmisc_1(X20,k1_tarski(X21)))))&(~r2_hidden(X18,X20)|X19!=X21|r2_hidden(k4_tarski(X18,X19),k2_zfmisc_1(X20,k1_tarski(X21))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t129_zfmisc_1])])])).
% 0.21/0.41  fof(c_0_18, plain, ![X22, X23, X24]:(~m1_subset_1(X23,k1_zfmisc_1(X22))|(~r2_hidden(X24,X23)|r2_hidden(X24,X22))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.21/0.41  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_tarski(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.41  cnf(c_0_20, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.41  cnf(c_0_21, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.41  fof(c_0_22, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:(((~r2_hidden(X9,X8)|(X9=X6|X9=X7)|X8!=k2_tarski(X6,X7))&((X10!=X6|r2_hidden(X10,X8)|X8!=k2_tarski(X6,X7))&(X10!=X7|r2_hidden(X10,X8)|X8!=k2_tarski(X6,X7))))&(((esk1_3(X11,X12,X13)!=X11|~r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k2_tarski(X11,X12))&(esk1_3(X11,X12,X13)!=X12|~r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k2_tarski(X11,X12)))&(r2_hidden(esk1_3(X11,X12,X13),X13)|(esk1_3(X11,X12,X13)=X11|esk1_3(X11,X12,X13)=X12)|X13=k2_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.21/0.41  fof(c_0_23, plain, ![X34, X35, X36]:(~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|k1_relset_1(X34,X35,X36)=k1_relat_1(X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.21/0.41  cnf(c_0_24, plain, (X1=X2|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.41  cnf(c_0_25, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.41  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20]), c_0_21])).
% 0.21/0.41  fof(c_0_27, plain, ![X29, X30, X31]:(((r2_hidden(X29,k1_relat_1(X31))|~r2_hidden(k4_tarski(X29,X30),X31)|(~v1_relat_1(X31)|~v1_funct_1(X31)))&(X30=k1_funct_1(X31,X29)|~r2_hidden(k4_tarski(X29,X30),X31)|(~v1_relat_1(X31)|~v1_funct_1(X31))))&(~r2_hidden(X29,k1_relat_1(X31))|X30!=k1_funct_1(X31,X29)|r2_hidden(k4_tarski(X29,X30),X31)|(~v1_relat_1(X31)|~v1_funct_1(X31)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.21/0.41  fof(c_0_28, plain, ![X25, X26]:(~v1_relat_1(X25)|(~m1_subset_1(X26,k1_zfmisc_1(X25))|v1_relat_1(X26))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.21/0.41  fof(c_0_29, plain, ![X27, X28]:v1_relat_1(k2_zfmisc_1(X27,X28)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.21/0.41  cnf(c_0_30, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.41  fof(c_0_31, plain, ![X37, X38, X39]:((((~v1_funct_2(X39,X37,X38)|X37=k1_relset_1(X37,X38,X39)|X38=k1_xboole_0|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))&(X37!=k1_relset_1(X37,X38,X39)|v1_funct_2(X39,X37,X38)|X38=k1_xboole_0|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))))&((~v1_funct_2(X39,X37,X38)|X37=k1_relset_1(X37,X38,X39)|X37!=k1_xboole_0|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))&(X37!=k1_relset_1(X37,X38,X39)|v1_funct_2(X39,X37,X38)|X37!=k1_xboole_0|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))))&((~v1_funct_2(X39,X37,X38)|X39=k1_xboole_0|X37=k1_xboole_0|X38!=k1_xboole_0|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))&(X39!=k1_xboole_0|v1_funct_2(X39,X37,X38)|X37=k1_xboole_0|X38!=k1_xboole_0|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.21/0.41  cnf(c_0_32, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.41  cnf(c_0_33, negated_conjecture, (v1_funct_2(esk5_0,esk2_0,k1_tarski(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.41  fof(c_0_34, plain, ![X32, X33]:(~r2_hidden(X32,X33)|~r1_tarski(X33,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.21/0.41  fof(c_0_35, plain, ![X5]:r1_tarski(k1_xboole_0,X5), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.21/0.41  cnf(c_0_36, plain, (X1=X2|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,k1_enumset1(X2,X2,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_20]), c_0_21])).
% 0.21/0.41  cnf(c_0_37, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0)))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.21/0.41  cnf(c_0_38, plain, (r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.41  cnf(c_0_39, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.41  cnf(c_0_40, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.41  cnf(c_0_41, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X2,X4)), inference(rw,[status(thm)],[c_0_30, c_0_21])).
% 0.21/0.41  cnf(c_0_42, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.41  cnf(c_0_43, negated_conjecture, (k1_relset_1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0),esk5_0)=k1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_32, c_0_26])).
% 0.21/0.41  cnf(c_0_44, negated_conjecture, (v1_funct_2(esk5_0,esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_20]), c_0_21])).
% 0.21/0.41  cnf(c_0_45, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.41  cnf(c_0_46, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.41  cnf(c_0_47, negated_conjecture, (X1=esk3_0|~r2_hidden(k4_tarski(X2,X1),esk5_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.21/0.41  cnf(c_0_48, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_38])).
% 0.21/0.41  cnf(c_0_49, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.41  cnf(c_0_50, negated_conjecture, (v1_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_26]), c_0_40])])).
% 0.21/0.41  cnf(c_0_51, plain, (r2_hidden(X1,k1_enumset1(X1,X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_41])])).
% 0.21/0.41  cnf(c_0_52, negated_conjecture, (k1_enumset1(esk3_0,esk3_0,esk3_0)=k1_xboole_0|k1_relat_1(esk5_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_26]), c_0_43]), c_0_44])])).
% 0.21/0.41  cnf(c_0_53, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.21/0.41  cnf(c_0_54, negated_conjecture, (k1_funct_1(esk5_0,X1)=esk3_0|~r2_hidden(X1,k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49]), c_0_50])])).
% 0.21/0.41  cnf(c_0_55, negated_conjecture, (k1_relat_1(esk5_0)=esk2_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])).
% 0.21/0.41  cnf(c_0_56, negated_conjecture, (k1_funct_1(esk5_0,esk4_0)!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.41  cnf(c_0_57, negated_conjecture, (k1_funct_1(esk5_0,X1)=esk3_0|~r2_hidden(X1,esk2_0)), inference(rw,[status(thm)],[c_0_54, c_0_55])).
% 0.21/0.41  cnf(c_0_58, negated_conjecture, (r2_hidden(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.41  cnf(c_0_59, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])]), ['proof']).
% 0.21/0.41  # SZS output end CNFRefutation
% 0.21/0.41  # Proof object total steps             : 60
% 0.21/0.41  # Proof object clause steps            : 33
% 0.21/0.41  # Proof object formula steps           : 27
% 0.21/0.41  # Proof object conjectures             : 19
% 0.21/0.41  # Proof object clause conjectures      : 16
% 0.21/0.41  # Proof object formula conjectures     : 3
% 0.21/0.41  # Proof object initial clauses used    : 17
% 0.21/0.41  # Proof object initial formulas used   : 13
% 0.21/0.41  # Proof object generating inferences   : 9
% 0.21/0.41  # Proof object simplifying inferences  : 22
% 0.21/0.41  # Training examples: 0 positive, 0 negative
% 0.21/0.41  # Parsed axioms                        : 13
% 0.21/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.41  # Initial clauses                      : 31
% 0.21/0.41  # Removed in clause preprocessing      : 2
% 0.21/0.41  # Initial clauses in saturation        : 29
% 0.21/0.41  # Processed clauses                    : 81
% 0.21/0.41  # ...of these trivial                  : 1
% 0.21/0.41  # ...subsumed                          : 4
% 0.21/0.41  # ...remaining for further processing  : 76
% 0.21/0.41  # Other redundant clauses eliminated   : 14
% 0.21/0.41  # Clauses deleted for lack of memory   : 0
% 0.21/0.41  # Backward-subsumed                    : 0
% 0.21/0.41  # Backward-rewritten                   : 11
% 0.21/0.41  # Generated clauses                    : 296
% 0.21/0.41  # ...of the previous two non-trivial   : 296
% 0.21/0.41  # Contextual simplify-reflections      : 1
% 0.21/0.41  # Paramodulations                      : 283
% 0.21/0.41  # Factorizations                       : 2
% 0.21/0.41  # Equation resolutions                 : 14
% 0.21/0.41  # Propositional unsat checks           : 0
% 0.21/0.41  #    Propositional check models        : 0
% 0.21/0.41  #    Propositional check unsatisfiable : 0
% 0.21/0.41  #    Propositional clauses             : 0
% 0.21/0.41  #    Propositional clauses after purity: 0
% 0.21/0.41  #    Propositional unsat core size     : 0
% 0.21/0.41  #    Propositional preprocessing time  : 0.000
% 0.21/0.41  #    Propositional encoding time       : 0.000
% 0.21/0.41  #    Propositional solver time         : 0.000
% 0.21/0.41  #    Success case prop preproc time    : 0.000
% 0.21/0.41  #    Success case prop encoding time   : 0.000
% 0.21/0.41  #    Success case prop solver time     : 0.000
% 0.21/0.41  # Current number of processed clauses  : 56
% 0.21/0.41  #    Positive orientable unit clauses  : 12
% 0.21/0.41  #    Positive unorientable unit clauses: 0
% 0.21/0.41  #    Negative unit clauses             : 2
% 0.21/0.41  #    Non-unit-clauses                  : 42
% 0.21/0.41  # Current number of unprocessed clauses: 239
% 0.21/0.41  # ...number of literals in the above   : 2315
% 0.21/0.41  # Current number of archived formulas  : 0
% 0.21/0.41  # Current number of archived clauses   : 13
% 0.21/0.41  # Clause-clause subsumption calls (NU) : 970
% 0.21/0.41  # Rec. Clause-clause subsumption calls : 89
% 0.21/0.41  # Non-unit clause-clause subsumptions  : 5
% 0.21/0.41  # Unit Clause-clause subsumption calls : 17
% 0.21/0.41  # Rewrite failures with RHS unbound    : 0
% 0.21/0.41  # BW rewrite match attempts            : 8
% 0.21/0.41  # BW rewrite match successes           : 2
% 0.21/0.41  # Condensation attempts                : 0
% 0.21/0.41  # Condensation successes               : 0
% 0.21/0.41  # Termbank termtop insertions          : 14246
% 0.21/0.41  
% 0.21/0.41  # -------------------------------------------------
% 0.21/0.41  # User time                : 0.045 s
% 0.21/0.41  # System time              : 0.004 s
% 0.21/0.41  # Total time               : 0.049 s
% 0.21/0.41  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
