%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:34 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 876 expanded)
%              Number of clauses        :   55 ( 354 expanded)
%              Number of leaves         :   12 ( 219 expanded)
%              Depth                    :   14
%              Number of atoms          :  240 (3583 expanded)
%              Number of equality atoms :   68 ( 624 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t115_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X5] :
          ~ ( r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))
            & ! [X6] :
                ~ ( r2_hidden(X6,X1)
                  & r2_hidden(X6,X3)
                  & X5 = k1_funct_1(X4,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

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

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t22_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
     => ( ! [X4] :
            ~ ( r2_hidden(X4,X2)
              & ! [X5] : ~ r2_hidden(k4_tarski(X4,X5),X3) )
      <=> k1_relset_1(X2,X1,X3) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X5] :
            ~ ( r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))
              & ! [X6] :
                  ~ ( r2_hidden(X6,X1)
                    & r2_hidden(X6,X3)
                    & X5 = k1_funct_1(X4,X6) ) ) ) ),
    inference(assume_negation,[status(cth)],[t115_funct_2])).

fof(c_0_13,plain,(
    ! [X19,X20,X21] :
      ( ( r2_hidden(X19,k1_relat_1(X21))
        | ~ r2_hidden(k4_tarski(X19,X20),X21)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( X20 = k1_funct_1(X21,X19)
        | ~ r2_hidden(k4_tarski(X19,X20),X21)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( ~ r2_hidden(X19,k1_relat_1(X21))
        | X20 != k1_funct_1(X21,X19)
        | r2_hidden(k4_tarski(X19,X20),X21)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

fof(c_0_14,plain,(
    ! [X14,X15,X16,X18] :
      ( ( r2_hidden(esk1_3(X14,X15,X16),k1_relat_1(X16))
        | ~ r2_hidden(X14,k9_relat_1(X16,X15))
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(k4_tarski(esk1_3(X14,X15,X16),X14),X16)
        | ~ r2_hidden(X14,k9_relat_1(X16,X15))
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(esk1_3(X14,X15,X16),X15)
        | ~ r2_hidden(X14,k9_relat_1(X16,X15))
        | ~ v1_relat_1(X16) )
      & ( ~ r2_hidden(X18,k1_relat_1(X16))
        | ~ r2_hidden(k4_tarski(X18,X14),X16)
        | ~ r2_hidden(X18,X15)
        | r2_hidden(X14,k9_relat_1(X16,X15))
        | ~ v1_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

fof(c_0_15,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(X10))
      | v1_relat_1(X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_16,negated_conjecture,(
    ! [X46] :
      ( v1_funct_1(esk7_0)
      & v1_funct_2(esk7_0,esk4_0,esk5_0)
      & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
      & r2_hidden(esk8_0,k7_relset_1(esk4_0,esk5_0,esk7_0,esk6_0))
      & ( ~ r2_hidden(X46,esk4_0)
        | ~ r2_hidden(X46,esk6_0)
        | esk8_0 != k1_funct_1(esk7_0,X46) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])).

fof(c_0_17,plain,(
    ! [X12,X13] : v1_relat_1(k2_zfmisc_1(X12,X13)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_18,plain,(
    ! [X24,X25,X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
      | k1_relset_1(X24,X25,X26) = k1_relat_1(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_19,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(esk1_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X27,X28,X29,X30] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | k7_relset_1(X27,X28,X29,X30) = k9_relat_1(X29,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

cnf(c_0_25,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_26,plain,(
    ! [X38,X39,X40] :
      ( ( ~ v1_funct_2(X40,X38,X39)
        | X38 = k1_relset_1(X38,X39,X40)
        | X39 = k1_xboole_0
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( X38 != k1_relset_1(X38,X39,X40)
        | v1_funct_2(X40,X38,X39)
        | X39 = k1_xboole_0
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( ~ v1_funct_2(X40,X38,X39)
        | X38 = k1_relset_1(X38,X39,X40)
        | X38 != k1_xboole_0
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( X38 != k1_relset_1(X38,X39,X40)
        | v1_funct_2(X40,X38,X39)
        | X38 != k1_xboole_0
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( ~ v1_funct_2(X40,X38,X39)
        | X40 = k1_xboole_0
        | X38 = k1_xboole_0
        | X39 != k1_xboole_0
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( X40 != k1_xboole_0
        | v1_funct_2(X40,X38,X39)
        | X38 = k1_xboole_0
        | X39 != k1_xboole_0
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_27,negated_conjecture,
    ( ~ r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk6_0)
    | esk8_0 != k1_funct_1(esk7_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,plain,
    ( k1_funct_1(X1,esk1_3(X2,X3,X1)) = X2
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_30,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk8_0,k7_relset_1(esk4_0,esk5_0,esk7_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_32,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),k1_relat_1(X3))
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_34,negated_conjecture,
    ( k1_relat_1(esk7_0) = k1_relset_1(esk4_0,esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_22])).

cnf(c_0_35,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_2(esk7_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_37,plain,(
    ! [X8,X9] :
      ( ( ~ m1_subset_1(X8,k1_zfmisc_1(X9))
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | m1_subset_1(X8,k1_zfmisc_1(X9)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_38,plain,(
    ! [X7] : r1_tarski(k1_xboole_0,X7) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_39,negated_conjecture,
    ( ~ r2_hidden(esk1_3(esk8_0,X1,esk7_0),esk4_0)
    | ~ r2_hidden(esk1_3(esk8_0,X1,esk7_0),esk6_0)
    | ~ r2_hidden(esk8_0,k9_relat_1(esk7_0,X1)) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30])])])).

cnf(c_0_40,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk8_0,k9_relat_1(esk7_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_22])])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk1_3(X1,X2,esk7_0),k1_relset_1(esk4_0,esk5_0,esk7_0))
    | ~ r2_hidden(X1,k9_relat_1(esk7_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_30])])).

cnf(c_0_43,negated_conjecture,
    ( k1_relset_1(esk4_0,esk5_0,esk7_0) = esk4_0
    | esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_22])])).

cnf(c_0_44,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_46,plain,(
    ! [X22,X23] :
      ( ~ r2_hidden(X22,X23)
      | ~ r1_tarski(X23,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_47,negated_conjecture,
    ( ~ r2_hidden(esk1_3(esk8_0,esk6_0,esk7_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_30])])).

cnf(c_0_48,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r2_hidden(esk1_3(X1,X2,esk7_0),esk4_0)
    | ~ r2_hidden(X1,k9_relat_1(esk7_0,X2)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_51,plain,(
    ! [X31,X32,X33,X35,X36] :
      ( ( r2_hidden(esk2_3(X31,X32,X33),X32)
        | k1_relset_1(X32,X31,X33) = X32
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X32,X31))) )
      & ( ~ r2_hidden(k4_tarski(esk2_3(X31,X32,X33),X35),X33)
        | k1_relset_1(X32,X31,X33) = X32
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X32,X31))) )
      & ( k1_relset_1(X32,X31,X33) != X32
        | ~ r2_hidden(X36,X32)
        | r2_hidden(k4_tarski(X36,esk3_4(X31,X32,X33,X36)),X33)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X32,X31))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_relset_1])])])])])])).

cnf(c_0_52,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_53,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_41])])).

cnf(c_0_54,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_49])).

cnf(c_0_55,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_45])).

cnf(c_0_56,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | k1_relset_1(X2,X1,X3) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_57,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,k1_xboole_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( v1_funct_2(esk7_0,esk4_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_36,c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_22,c_0_53])).

cnf(c_0_60,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_49])).

cnf(c_0_61,negated_conjecture,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_30])).

cnf(c_0_62,plain,
    ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_63,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])])).

cnf(c_0_64,plain,
    ( r2_hidden(esk1_3(X1,X2,k1_xboole_0),k1_relset_1(X3,X4,k1_xboole_0))
    | ~ r2_hidden(X1,k9_relat_1(k1_xboole_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_60]),c_0_61])])).

cnf(c_0_65,plain,
    ( k1_relset_1(k1_xboole_0,X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_49])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk1_3(X1,X2,esk7_0),k1_relset_1(esk4_0,k1_xboole_0,esk7_0))
    | ~ r2_hidden(X1,k9_relat_1(esk7_0,X2)) ),
    inference(rw,[status(thm)],[c_0_42,c_0_53])).

cnf(c_0_67,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_63])).

cnf(c_0_68,plain,
    ( r2_hidden(esk1_3(X1,X2,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ r2_hidden(X1,k9_relat_1(k1_xboole_0,X2)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_60])).

cnf(c_0_69,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_60,c_0_65])).

cnf(c_0_70,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk1_3(X1,X2,esk7_0),k1_relset_1(k1_xboole_0,k1_xboole_0,esk7_0))
    | ~ r2_hidden(X1,k9_relat_1(esk7_0,X2)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_63])).

cnf(c_0_71,negated_conjecture,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,esk7_0) = k1_xboole_0
    | esk7_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_67])).

cnf(c_0_72,plain,
    ( ~ r2_hidden(X1,k9_relat_1(k1_xboole_0,X2)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_69]),c_0_55])).

cnf(c_0_73,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) = k1_relset_1(X3,X4,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_60])).

cnf(c_0_74,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | ~ r2_hidden(X1,k9_relat_1(esk7_0,X2)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_55])).

cnf(c_0_75,plain,
    ( k1_relset_1(k9_relat_1(k1_xboole_0,X1),X2,X3) = k9_relat_1(k1_xboole_0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k9_relat_1(k1_xboole_0,X1),X2))) ),
    inference(spm,[status(thm)],[c_0_72,c_0_56])).

cnf(c_0_76,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_73,c_0_65])).

cnf(c_0_77,negated_conjecture,
    ( esk7_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_74,c_0_41])).

cnf(c_0_78,plain,
    ( k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_49]),c_0_76])).

cnf(c_0_79,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_77]),c_0_78]),c_0_55]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:45:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.13/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.028 s
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t115_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:~(((r2_hidden(X6,X1)&r2_hidden(X6,X3))&X5=k1_funct_1(X4,X6)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_funct_2)).
% 0.13/0.39  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 0.13/0.39  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 0.13/0.39  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.13/0.39  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.13/0.39  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.13/0.39  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.13/0.39  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.13/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.39  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.13/0.39  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.13/0.39  fof(t22_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~(r2_hidden(k4_tarski(X4,X5),X3))))<=>k1_relset_1(X2,X1,X3)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relset_1)).
% 0.13/0.39  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:~(((r2_hidden(X6,X1)&r2_hidden(X6,X3))&X5=k1_funct_1(X4,X6))))))), inference(assume_negation,[status(cth)],[t115_funct_2])).
% 0.13/0.39  fof(c_0_13, plain, ![X19, X20, X21]:(((r2_hidden(X19,k1_relat_1(X21))|~r2_hidden(k4_tarski(X19,X20),X21)|(~v1_relat_1(X21)|~v1_funct_1(X21)))&(X20=k1_funct_1(X21,X19)|~r2_hidden(k4_tarski(X19,X20),X21)|(~v1_relat_1(X21)|~v1_funct_1(X21))))&(~r2_hidden(X19,k1_relat_1(X21))|X20!=k1_funct_1(X21,X19)|r2_hidden(k4_tarski(X19,X20),X21)|(~v1_relat_1(X21)|~v1_funct_1(X21)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.13/0.39  fof(c_0_14, plain, ![X14, X15, X16, X18]:((((r2_hidden(esk1_3(X14,X15,X16),k1_relat_1(X16))|~r2_hidden(X14,k9_relat_1(X16,X15))|~v1_relat_1(X16))&(r2_hidden(k4_tarski(esk1_3(X14,X15,X16),X14),X16)|~r2_hidden(X14,k9_relat_1(X16,X15))|~v1_relat_1(X16)))&(r2_hidden(esk1_3(X14,X15,X16),X15)|~r2_hidden(X14,k9_relat_1(X16,X15))|~v1_relat_1(X16)))&(~r2_hidden(X18,k1_relat_1(X16))|~r2_hidden(k4_tarski(X18,X14),X16)|~r2_hidden(X18,X15)|r2_hidden(X14,k9_relat_1(X16,X15))|~v1_relat_1(X16))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.13/0.39  fof(c_0_15, plain, ![X10, X11]:(~v1_relat_1(X10)|(~m1_subset_1(X11,k1_zfmisc_1(X10))|v1_relat_1(X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.13/0.39  fof(c_0_16, negated_conjecture, ![X46]:(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,esk4_0,esk5_0))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))))&(r2_hidden(esk8_0,k7_relset_1(esk4_0,esk5_0,esk7_0,esk6_0))&(~r2_hidden(X46,esk4_0)|~r2_hidden(X46,esk6_0)|esk8_0!=k1_funct_1(esk7_0,X46)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])).
% 0.13/0.39  fof(c_0_17, plain, ![X12, X13]:v1_relat_1(k2_zfmisc_1(X12,X13)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.13/0.39  fof(c_0_18, plain, ![X24, X25, X26]:(~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))|k1_relset_1(X24,X25,X26)=k1_relat_1(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.13/0.39  cnf(c_0_19, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_20, plain, (r2_hidden(k4_tarski(esk1_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.39  cnf(c_0_21, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_23, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  fof(c_0_24, plain, ![X27, X28, X29, X30]:(~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))|k7_relset_1(X27,X28,X29,X30)=k9_relat_1(X29,X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.13/0.39  cnf(c_0_25, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  fof(c_0_26, plain, ![X38, X39, X40]:((((~v1_funct_2(X40,X38,X39)|X38=k1_relset_1(X38,X39,X40)|X39=k1_xboole_0|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))))&(X38!=k1_relset_1(X38,X39,X40)|v1_funct_2(X40,X38,X39)|X39=k1_xboole_0|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))))&((~v1_funct_2(X40,X38,X39)|X38=k1_relset_1(X38,X39,X40)|X38!=k1_xboole_0|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))))&(X38!=k1_relset_1(X38,X39,X40)|v1_funct_2(X40,X38,X39)|X38!=k1_xboole_0|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))))))&((~v1_funct_2(X40,X38,X39)|X40=k1_xboole_0|X38=k1_xboole_0|X39!=k1_xboole_0|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))))&(X40!=k1_xboole_0|v1_funct_2(X40,X38,X39)|X38=k1_xboole_0|X39!=k1_xboole_0|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.13/0.39  cnf(c_0_27, negated_conjecture, (~r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk6_0)|esk8_0!=k1_funct_1(esk7_0,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_28, plain, (k1_funct_1(X1,esk1_3(X2,X3,X1))=X2|~v1_funct_1(X1)|~r2_hidden(X2,k9_relat_1(X1,X3))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.13/0.39  cnf(c_0_29, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_30, negated_conjecture, (v1_relat_1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])])).
% 0.13/0.39  cnf(c_0_31, negated_conjecture, (r2_hidden(esk8_0,k7_relset_1(esk4_0,esk5_0,esk7_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_32, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.39  cnf(c_0_33, plain, (r2_hidden(esk1_3(X1,X2,X3),k1_relat_1(X3))|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.39  cnf(c_0_34, negated_conjecture, (k1_relat_1(esk7_0)=k1_relset_1(esk4_0,esk5_0,esk7_0)), inference(spm,[status(thm)],[c_0_25, c_0_22])).
% 0.13/0.39  cnf(c_0_35, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.39  cnf(c_0_36, negated_conjecture, (v1_funct_2(esk7_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  fof(c_0_37, plain, ![X8, X9]:((~m1_subset_1(X8,k1_zfmisc_1(X9))|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|m1_subset_1(X8,k1_zfmisc_1(X9)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.39  fof(c_0_38, plain, ![X7]:r1_tarski(k1_xboole_0,X7), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.13/0.39  cnf(c_0_39, negated_conjecture, (~r2_hidden(esk1_3(esk8_0,X1,esk7_0),esk4_0)|~r2_hidden(esk1_3(esk8_0,X1,esk7_0),esk6_0)|~r2_hidden(esk8_0,k9_relat_1(esk7_0,X1))), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_30])])])).
% 0.13/0.39  cnf(c_0_40, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.39  cnf(c_0_41, negated_conjecture, (r2_hidden(esk8_0,k9_relat_1(esk7_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_22])])).
% 0.13/0.39  cnf(c_0_42, negated_conjecture, (r2_hidden(esk1_3(X1,X2,esk7_0),k1_relset_1(esk4_0,esk5_0,esk7_0))|~r2_hidden(X1,k9_relat_1(esk7_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_30])])).
% 0.13/0.39  cnf(c_0_43, negated_conjecture, (k1_relset_1(esk4_0,esk5_0,esk7_0)=esk4_0|esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_22])])).
% 0.13/0.39  cnf(c_0_44, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.39  cnf(c_0_45, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.39  fof(c_0_46, plain, ![X22, X23]:(~r2_hidden(X22,X23)|~r1_tarski(X23,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.13/0.39  cnf(c_0_47, negated_conjecture, (~r2_hidden(esk1_3(esk8_0,esk6_0,esk7_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_30])])).
% 0.13/0.39  cnf(c_0_48, negated_conjecture, (esk5_0=k1_xboole_0|r2_hidden(esk1_3(X1,X2,esk7_0),esk4_0)|~r2_hidden(X1,k9_relat_1(esk7_0,X2))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.13/0.39  cnf(c_0_49, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.13/0.39  cnf(c_0_50, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.13/0.39  fof(c_0_51, plain, ![X31, X32, X33, X35, X36]:(((r2_hidden(esk2_3(X31,X32,X33),X32)|k1_relset_1(X32,X31,X33)=X32|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X32,X31))))&(~r2_hidden(k4_tarski(esk2_3(X31,X32,X33),X35),X33)|k1_relset_1(X32,X31,X33)=X32|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X32,X31)))))&(k1_relset_1(X32,X31,X33)!=X32|(~r2_hidden(X36,X32)|r2_hidden(k4_tarski(X36,esk3_4(X31,X32,X33,X36)),X33))|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X32,X31))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_relset_1])])])])])])).
% 0.13/0.39  cnf(c_0_52, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X1,X2,X3)|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.39  cnf(c_0_53, negated_conjecture, (esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_41])])).
% 0.13/0.39  cnf(c_0_54, plain, (v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_21, c_0_49])).
% 0.13/0.39  cnf(c_0_55, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_50, c_0_45])).
% 0.13/0.39  cnf(c_0_56, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|k1_relset_1(X2,X1,X3)=X2|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.13/0.39  cnf(c_0_57, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X2,X1,k1_xboole_0)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))), inference(er,[status(thm)],[c_0_52])).
% 0.13/0.39  cnf(c_0_58, negated_conjecture, (v1_funct_2(esk7_0,esk4_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_36, c_0_53])).
% 0.13/0.39  cnf(c_0_59, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_xboole_0)))), inference(rw,[status(thm)],[c_0_22, c_0_53])).
% 0.13/0.39  cnf(c_0_60, plain, (k1_relset_1(X1,X2,k1_xboole_0)=k1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_25, c_0_49])).
% 0.13/0.39  cnf(c_0_61, negated_conjecture, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_54, c_0_30])).
% 0.13/0.39  cnf(c_0_62, plain, (k1_relset_1(k1_xboole_0,X1,X2)=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.13/0.39  cnf(c_0_63, negated_conjecture, (esk7_0=k1_xboole_0|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])])).
% 0.13/0.39  cnf(c_0_64, plain, (r2_hidden(esk1_3(X1,X2,k1_xboole_0),k1_relset_1(X3,X4,k1_xboole_0))|~r2_hidden(X1,k9_relat_1(k1_xboole_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_60]), c_0_61])])).
% 0.13/0.39  cnf(c_0_65, plain, (k1_relset_1(k1_xboole_0,X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_62, c_0_49])).
% 0.13/0.39  cnf(c_0_66, negated_conjecture, (r2_hidden(esk1_3(X1,X2,esk7_0),k1_relset_1(esk4_0,k1_xboole_0,esk7_0))|~r2_hidden(X1,k9_relat_1(esk7_0,X2))), inference(rw,[status(thm)],[c_0_42, c_0_53])).
% 0.13/0.39  cnf(c_0_67, negated_conjecture, (esk7_0=k1_xboole_0|m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_59, c_0_63])).
% 0.13/0.39  cnf(c_0_68, plain, (r2_hidden(esk1_3(X1,X2,k1_xboole_0),k1_relat_1(k1_xboole_0))|~r2_hidden(X1,k9_relat_1(k1_xboole_0,X2))), inference(spm,[status(thm)],[c_0_64, c_0_60])).
% 0.13/0.39  cnf(c_0_69, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_60, c_0_65])).
% 0.13/0.39  cnf(c_0_70, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk1_3(X1,X2,esk7_0),k1_relset_1(k1_xboole_0,k1_xboole_0,esk7_0))|~r2_hidden(X1,k9_relat_1(esk7_0,X2))), inference(spm,[status(thm)],[c_0_66, c_0_63])).
% 0.13/0.39  cnf(c_0_71, negated_conjecture, (k1_relset_1(k1_xboole_0,k1_xboole_0,esk7_0)=k1_xboole_0|esk7_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_62, c_0_67])).
% 0.13/0.39  cnf(c_0_72, plain, (~r2_hidden(X1,k9_relat_1(k1_xboole_0,X2))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_69]), c_0_55])).
% 0.13/0.39  cnf(c_0_73, plain, (k1_relset_1(X1,X2,k1_xboole_0)=k1_relset_1(X3,X4,k1_xboole_0)), inference(spm,[status(thm)],[c_0_60, c_0_60])).
% 0.13/0.39  cnf(c_0_74, negated_conjecture, (esk7_0=k1_xboole_0|~r2_hidden(X1,k9_relat_1(esk7_0,X2))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_55])).
% 0.13/0.39  cnf(c_0_75, plain, (k1_relset_1(k9_relat_1(k1_xboole_0,X1),X2,X3)=k9_relat_1(k1_xboole_0,X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k9_relat_1(k1_xboole_0,X1),X2)))), inference(spm,[status(thm)],[c_0_72, c_0_56])).
% 0.13/0.39  cnf(c_0_76, plain, (k1_relset_1(X1,X2,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_73, c_0_65])).
% 0.13/0.39  cnf(c_0_77, negated_conjecture, (esk7_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_74, c_0_41])).
% 0.13/0.39  cnf(c_0_78, plain, (k9_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_49]), c_0_76])).
% 0.13/0.39  cnf(c_0_79, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_77]), c_0_78]), c_0_55]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 80
% 0.13/0.39  # Proof object clause steps            : 55
% 0.13/0.39  # Proof object formula steps           : 25
% 0.13/0.39  # Proof object conjectures             : 28
% 0.13/0.39  # Proof object clause conjectures      : 25
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 19
% 0.13/0.39  # Proof object initial formulas used   : 12
% 0.13/0.39  # Proof object generating inferences   : 30
% 0.13/0.39  # Proof object simplifying inferences  : 32
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 12
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 29
% 0.13/0.39  # Removed in clause preprocessing      : 0
% 0.13/0.39  # Initial clauses in saturation        : 29
% 0.13/0.39  # Processed clauses                    : 140
% 0.13/0.39  # ...of these trivial                  : 2
% 0.13/0.39  # ...subsumed                          : 47
% 0.13/0.39  # ...remaining for further processing  : 91
% 0.13/0.39  # Other redundant clauses eliminated   : 7
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 2
% 0.13/0.39  # Backward-rewritten                   : 41
% 0.13/0.39  # Generated clauses                    : 184
% 0.13/0.39  # ...of the previous two non-trivial   : 197
% 0.13/0.39  # Contextual simplify-reflections      : 1
% 0.13/0.39  # Paramodulations                      : 178
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 7
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 43
% 0.13/0.39  #    Positive orientable unit clauses  : 9
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 1
% 0.13/0.39  #    Non-unit-clauses                  : 33
% 0.13/0.39  # Current number of unprocessed clauses: 76
% 0.13/0.39  # ...number of literals in the above   : 421
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 43
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 522
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 114
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 24
% 0.13/0.39  # Unit Clause-clause subsumption calls : 18
% 0.13/0.39  # Rewrite failures with RHS unbound    : 24
% 0.13/0.39  # BW rewrite match attempts            : 26
% 0.13/0.39  # BW rewrite match successes           : 15
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 5495
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.038 s
% 0.13/0.39  # System time              : 0.003 s
% 0.13/0.39  # Total time               : 0.041 s
% 0.13/0.39  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
