%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:36 EST 2020

% Result     : Theorem 41.42s
% Output     : CNFRefutation 41.42s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 479 expanded)
%              Number of clauses        :   43 ( 202 expanded)
%              Number of leaves         :   12 ( 122 expanded)
%              Depth                    :   12
%              Number of atoms          :  264 (1924 expanded)
%              Number of equality atoms :   28 ( 213 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t116_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X5] :
          ~ ( r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))
            & ! [X6] :
                ( m1_subset_1(X6,X1)
               => ~ ( r2_hidden(X6,X3)
                    & X5 = k1_funct_1(X4,X6) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(dt_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(t52_relset_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ~ v1_xboole_0(X3)
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                 => ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))
                      <=> ? [X6] :
                            ( m1_subset_1(X6,X3)
                            & r2_hidden(k4_tarski(X6,X5),X4)
                            & r2_hidden(X6,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).

fof(t22_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
     => ( ! [X4] :
            ~ ( r2_hidden(X4,X2)
              & ! [X5] : ~ r2_hidden(k4_tarski(X4,X5),X3) )
      <=> k1_relset_1(X2,X1,X3) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X5] :
            ~ ( r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))
              & ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ~ ( r2_hidden(X6,X3)
                      & X5 = k1_funct_1(X4,X6) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t116_funct_2])).

fof(c_0_13,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_14,plain,(
    ! [X16,X17,X18,X20] :
      ( ( r2_hidden(esk2_3(X16,X17,X18),k1_relat_1(X18))
        | ~ r2_hidden(X16,k9_relat_1(X18,X17))
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(k4_tarski(esk2_3(X16,X17,X18),X16),X18)
        | ~ r2_hidden(X16,k9_relat_1(X18,X17))
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X17)
        | ~ r2_hidden(X16,k9_relat_1(X18,X17))
        | ~ v1_relat_1(X18) )
      & ( ~ r2_hidden(X20,k1_relat_1(X18))
        | ~ r2_hidden(k4_tarski(X20,X16),X18)
        | ~ r2_hidden(X20,X17)
        | r2_hidden(X16,k9_relat_1(X18,X17))
        | ~ v1_relat_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

fof(c_0_15,negated_conjecture,(
    ! [X57] :
      ( v1_funct_1(esk9_0)
      & v1_funct_2(esk9_0,esk6_0,esk7_0)
      & m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))
      & r2_hidden(esk10_0,k7_relset_1(esk6_0,esk7_0,esk9_0,esk8_0))
      & ( ~ m1_subset_1(X57,esk6_0)
        | ~ r2_hidden(X57,esk8_0)
        | esk10_0 != k1_funct_1(esk9_0,X57) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])).

fof(c_0_16,plain,(
    ! [X34,X35,X36,X37] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
      | k7_relset_1(X34,X35,X36,X37) = k9_relat_1(X36,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_17,plain,(
    ! [X13,X14,X15] :
      ( ~ r2_hidden(X13,X14)
      | ~ m1_subset_1(X14,k1_zfmisc_1(X15))
      | m1_subset_1(X13,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_18,plain,(
    ! [X27,X28,X29,X30] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | m1_subset_1(k7_relset_1(X27,X28,X29,X30),k1_zfmisc_1(X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).

cnf(c_0_19,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_21,plain,(
    ! [X24,X25,X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
      | v1_relat_1(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk10_0,k7_relset_1(esk6_0,esk7_0,esk9_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_24,plain,(
    ! [X11,X12] :
      ( ~ v1_xboole_0(X11)
      | ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | v1_xboole_0(X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

fof(c_0_25,plain,(
    ! [X21,X22,X23] :
      ( ( r2_hidden(X21,k1_relat_1(X23))
        | ~ r2_hidden(k4_tarski(X21,X22),X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( X22 = k1_funct_1(X23,X21)
        | ~ r2_hidden(k4_tarski(X21,X22),X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( ~ r2_hidden(X21,k1_relat_1(X23))
        | X22 != k1_funct_1(X23,X21)
        | r2_hidden(k4_tarski(X21,X22),X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

fof(c_0_26,plain,(
    ! [X45,X46,X47,X48,X49,X51] :
      ( ( m1_subset_1(esk5_5(X45,X46,X47,X48,X49),X47)
        | ~ r2_hidden(X49,k7_relset_1(X47,X45,X48,X46))
        | ~ m1_subset_1(X49,X45)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X47,X45)))
        | v1_xboole_0(X47)
        | v1_xboole_0(X46)
        | v1_xboole_0(X45) )
      & ( r2_hidden(k4_tarski(esk5_5(X45,X46,X47,X48,X49),X49),X48)
        | ~ r2_hidden(X49,k7_relset_1(X47,X45,X48,X46))
        | ~ m1_subset_1(X49,X45)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X47,X45)))
        | v1_xboole_0(X47)
        | v1_xboole_0(X46)
        | v1_xboole_0(X45) )
      & ( r2_hidden(esk5_5(X45,X46,X47,X48,X49),X46)
        | ~ r2_hidden(X49,k7_relset_1(X47,X45,X48,X46))
        | ~ m1_subset_1(X49,X45)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X47,X45)))
        | v1_xboole_0(X47)
        | v1_xboole_0(X46)
        | v1_xboole_0(X45) )
      & ( ~ m1_subset_1(X51,X47)
        | ~ r2_hidden(k4_tarski(X51,X49),X48)
        | ~ r2_hidden(X51,X46)
        | r2_hidden(X49,k7_relset_1(X47,X45,X48,X46))
        | ~ m1_subset_1(X49,X45)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X47,X45)))
        | v1_xboole_0(X47)
        | v1_xboole_0(X46)
        | v1_xboole_0(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t52_relset_1])])])])])])).

cnf(c_0_27,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(X1,X3))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_30,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( ~ v1_xboole_0(k7_relset_1(esk6_0,esk7_0,esk9_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_22])).

cnf(c_0_32,plain,
    ( k7_relset_1(X1,X2,X3,X4) = k7_relset_1(X5,X6,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_34,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( r2_hidden(k4_tarski(esk5_5(X1,X2,X3,X4,X5),X5),X4)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))
    | ~ m1_subset_1(X5,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( m1_subset_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ r2_hidden(X1,k7_relset_1(X4,X2,X3,X5)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_38,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,k7_relset_1(X2,X3,X1,X5))
    | ~ v1_xboole_0(X5) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_23]),c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( ~ m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(k7_relset_1(X1,X2,esk9_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_40,plain,
    ( v1_xboole_0(k7_relset_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_28])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk10_0,k7_relset_1(X1,X2,esk9_0,esk8_0))
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_32]),c_0_33])])).

fof(c_0_42,plain,(
    ! [X38,X39,X40,X42,X43] :
      ( ( r2_hidden(esk3_3(X38,X39,X40),X39)
        | k1_relset_1(X39,X38,X40) = X39
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X39,X38))) )
      & ( ~ r2_hidden(k4_tarski(esk3_3(X38,X39,X40),X42),X40)
        | k1_relset_1(X39,X38,X40) = X39
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X39,X38))) )
      & ( k1_relset_1(X39,X38,X40) != X39
        | ~ r2_hidden(X43,X39)
        | r2_hidden(k4_tarski(X43,esk4_4(X38,X39,X40,X43)),X40)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X39,X38))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_relset_1])])])])])])).

cnf(c_0_43,negated_conjecture,
    ( ~ m1_subset_1(X1,esk6_0)
    | ~ r2_hidden(X1,esk8_0)
    | esk10_0 != k1_funct_1(esk9_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_44,plain,
    ( k1_funct_1(X1,esk5_5(X2,X3,X4,X1,X5)) = X5
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ r2_hidden(X5,k7_relset_1(X4,X2,X1,X3)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_30]),c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_46,negated_conjecture,
    ( ~ m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk10_0,k9_relat_1(esk9_0,esk8_0))
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_23])).

fof(c_0_48,plain,(
    ! [X31,X32,X33] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | k1_relset_1(X31,X32,X33) = k1_relat_1(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_49,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
    | k1_relset_1(X2,X1,X3) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( v1_xboole_0(X1)
    | esk10_0 != X2
    | ~ m1_subset_1(esk5_5(X3,X4,X1,esk9_0,X2),esk6_0)
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r2_hidden(esk5_5(X3,X4,X1,esk9_0,X2),esk8_0)
    | ~ r2_hidden(X2,k7_relset_1(X1,X3,esk9_0,X4)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])]),c_0_46])).

cnf(c_0_51,plain,
    ( m1_subset_1(esk5_5(X1,X2,X3,X4,X5),X3)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))
    | ~ m1_subset_1(X5,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk10_0,k9_relat_1(esk9_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_33])).

cnf(c_0_53,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_33])).

cnf(c_0_54,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_55,plain,
    ( k1_relset_1(X1,X2,X3) = X1
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( v1_xboole_0(esk6_0)
    | esk10_0 != X1
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,X2)))
    | ~ r2_hidden(esk5_5(X2,X3,esk6_0,esk9_0,X1),esk8_0)
    | ~ r2_hidden(X1,k7_relset_1(esk6_0,X2,esk9_0,X3)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_37]),c_0_46]),c_0_38])).

cnf(c_0_57,plain,
    ( r2_hidden(esk5_5(X1,X2,X3,X4,X5),X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))
    | ~ m1_subset_1(X5,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_58,negated_conjecture,
    ( ~ v1_xboole_0(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_52]),c_0_53])])).

cnf(c_0_59,plain,
    ( X1 = k1_relat_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( v1_xboole_0(esk6_0)
    | esk10_0 != X1
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,X2)))
    | ~ r2_hidden(X1,k7_relset_1(esk6_0,X2,esk9_0,esk8_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58]),c_0_37]),c_0_46])).

cnf(c_0_61,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X3))
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_62,negated_conjecture,
    ( esk6_0 = k1_relat_1(esk9_0)
    | ~ v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_33])).

cnf(c_0_63,negated_conjecture,
    ( v1_xboole_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_22]),c_0_33])])).

cnf(c_0_64,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(X1,X3))
    | ~ v1_xboole_0(k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( esk6_0 = k1_relat_1(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63])])).

cnf(c_0_66,negated_conjecture,
    ( ~ v1_xboole_0(k1_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_52]),c_0_53])])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_65]),c_0_66]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:19:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 41.42/41.65  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 41.42/41.65  # and selection function SelectMaxLComplexAvoidPosPred.
% 41.42/41.65  #
% 41.42/41.65  # Preprocessing time       : 0.029 s
% 41.42/41.65  # Presaturation interreduction done
% 41.42/41.65  
% 41.42/41.65  # Proof found!
% 41.42/41.65  # SZS status Theorem
% 41.42/41.65  # SZS output start CNFRefutation
% 41.42/41.65  fof(t116_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:(m1_subset_1(X6,X1)=>~((r2_hidden(X6,X3)&X5=k1_funct_1(X4,X6))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_funct_2)).
% 41.42/41.65  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 41.42/41.65  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 41.42/41.65  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 41.42/41.65  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 41.42/41.65  fof(dt_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 41.42/41.65  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 41.42/41.65  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 41.42/41.65  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 41.42/41.65  fof(t52_relset_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))<=>?[X6]:((m1_subset_1(X6,X3)&r2_hidden(k4_tarski(X6,X5),X4))&r2_hidden(X6,X2)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relset_1)).
% 41.42/41.65  fof(t22_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~(r2_hidden(k4_tarski(X4,X5),X3))))<=>k1_relset_1(X2,X1,X3)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relset_1)).
% 41.42/41.65  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 41.42/41.65  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:(m1_subset_1(X6,X1)=>~((r2_hidden(X6,X3)&X5=k1_funct_1(X4,X6)))))))), inference(assume_negation,[status(cth)],[t116_funct_2])).
% 41.42/41.65  fof(c_0_13, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 41.42/41.65  fof(c_0_14, plain, ![X16, X17, X18, X20]:((((r2_hidden(esk2_3(X16,X17,X18),k1_relat_1(X18))|~r2_hidden(X16,k9_relat_1(X18,X17))|~v1_relat_1(X18))&(r2_hidden(k4_tarski(esk2_3(X16,X17,X18),X16),X18)|~r2_hidden(X16,k9_relat_1(X18,X17))|~v1_relat_1(X18)))&(r2_hidden(esk2_3(X16,X17,X18),X17)|~r2_hidden(X16,k9_relat_1(X18,X17))|~v1_relat_1(X18)))&(~r2_hidden(X20,k1_relat_1(X18))|~r2_hidden(k4_tarski(X20,X16),X18)|~r2_hidden(X20,X17)|r2_hidden(X16,k9_relat_1(X18,X17))|~v1_relat_1(X18))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 41.42/41.65  fof(c_0_15, negated_conjecture, ![X57]:(((v1_funct_1(esk9_0)&v1_funct_2(esk9_0,esk6_0,esk7_0))&m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))))&(r2_hidden(esk10_0,k7_relset_1(esk6_0,esk7_0,esk9_0,esk8_0))&(~m1_subset_1(X57,esk6_0)|(~r2_hidden(X57,esk8_0)|esk10_0!=k1_funct_1(esk9_0,X57))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])).
% 41.42/41.65  fof(c_0_16, plain, ![X34, X35, X36, X37]:(~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|k7_relset_1(X34,X35,X36,X37)=k9_relat_1(X36,X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 41.42/41.65  fof(c_0_17, plain, ![X13, X14, X15]:(~r2_hidden(X13,X14)|~m1_subset_1(X14,k1_zfmisc_1(X15))|m1_subset_1(X13,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 41.42/41.65  fof(c_0_18, plain, ![X27, X28, X29, X30]:(~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))|m1_subset_1(k7_relset_1(X27,X28,X29,X30),k1_zfmisc_1(X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).
% 41.42/41.65  cnf(c_0_19, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 41.42/41.65  cnf(c_0_20, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 41.42/41.65  fof(c_0_21, plain, ![X24, X25, X26]:(~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))|v1_relat_1(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 41.42/41.65  cnf(c_0_22, negated_conjecture, (r2_hidden(esk10_0,k7_relset_1(esk6_0,esk7_0,esk9_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 41.42/41.65  cnf(c_0_23, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 41.42/41.65  fof(c_0_24, plain, ![X11, X12]:(~v1_xboole_0(X11)|(~m1_subset_1(X12,k1_zfmisc_1(X11))|v1_xboole_0(X12))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 41.42/41.65  fof(c_0_25, plain, ![X21, X22, X23]:(((r2_hidden(X21,k1_relat_1(X23))|~r2_hidden(k4_tarski(X21,X22),X23)|(~v1_relat_1(X23)|~v1_funct_1(X23)))&(X22=k1_funct_1(X23,X21)|~r2_hidden(k4_tarski(X21,X22),X23)|(~v1_relat_1(X23)|~v1_funct_1(X23))))&(~r2_hidden(X21,k1_relat_1(X23))|X22!=k1_funct_1(X23,X21)|r2_hidden(k4_tarski(X21,X22),X23)|(~v1_relat_1(X23)|~v1_funct_1(X23)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 41.42/41.65  fof(c_0_26, plain, ![X45, X46, X47, X48, X49, X51]:((((m1_subset_1(esk5_5(X45,X46,X47,X48,X49),X47)|~r2_hidden(X49,k7_relset_1(X47,X45,X48,X46))|~m1_subset_1(X49,X45)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X47,X45)))|v1_xboole_0(X47)|v1_xboole_0(X46)|v1_xboole_0(X45))&(r2_hidden(k4_tarski(esk5_5(X45,X46,X47,X48,X49),X49),X48)|~r2_hidden(X49,k7_relset_1(X47,X45,X48,X46))|~m1_subset_1(X49,X45)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X47,X45)))|v1_xboole_0(X47)|v1_xboole_0(X46)|v1_xboole_0(X45)))&(r2_hidden(esk5_5(X45,X46,X47,X48,X49),X46)|~r2_hidden(X49,k7_relset_1(X47,X45,X48,X46))|~m1_subset_1(X49,X45)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X47,X45)))|v1_xboole_0(X47)|v1_xboole_0(X46)|v1_xboole_0(X45)))&(~m1_subset_1(X51,X47)|~r2_hidden(k4_tarski(X51,X49),X48)|~r2_hidden(X51,X46)|r2_hidden(X49,k7_relset_1(X47,X45,X48,X46))|~m1_subset_1(X49,X45)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X47,X45)))|v1_xboole_0(X47)|v1_xboole_0(X46)|v1_xboole_0(X45))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t52_relset_1])])])])])])).
% 41.42/41.65  cnf(c_0_27, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 41.42/41.65  cnf(c_0_28, plain, (m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 41.42/41.65  cnf(c_0_29, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k9_relat_1(X1,X3))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 41.42/41.65  cnf(c_0_30, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 41.42/41.65  cnf(c_0_31, negated_conjecture, (~v1_xboole_0(k7_relset_1(esk6_0,esk7_0,esk9_0,esk8_0))), inference(spm,[status(thm)],[c_0_19, c_0_22])).
% 41.42/41.65  cnf(c_0_32, plain, (k7_relset_1(X1,X2,X3,X4)=k7_relset_1(X5,X6,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(spm,[status(thm)],[c_0_23, c_0_23])).
% 41.42/41.65  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 41.42/41.65  cnf(c_0_34, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 41.42/41.65  cnf(c_0_35, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 41.42/41.65  cnf(c_0_36, plain, (r2_hidden(k4_tarski(esk5_5(X1,X2,X3,X4,X5),X5),X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|~r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))|~m1_subset_1(X5,X1)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 41.42/41.65  cnf(c_0_37, plain, (m1_subset_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~r2_hidden(X1,k7_relset_1(X4,X2,X3,X5))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 41.42/41.65  cnf(c_0_38, plain, (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,k7_relset_1(X2,X3,X1,X5))|~v1_xboole_0(X5)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_23]), c_0_30])).
% 41.42/41.65  cnf(c_0_39, negated_conjecture, (~m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_xboole_0(k7_relset_1(X1,X2,esk9_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])])).
% 41.42/41.65  cnf(c_0_40, plain, (v1_xboole_0(k7_relset_1(X1,X2,X3,X4))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_34, c_0_28])).
% 41.42/41.65  cnf(c_0_41, negated_conjecture, (r2_hidden(esk10_0,k7_relset_1(X1,X2,esk9_0,esk8_0))|~m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_32]), c_0_33])])).
% 41.42/41.65  fof(c_0_42, plain, ![X38, X39, X40, X42, X43]:(((r2_hidden(esk3_3(X38,X39,X40),X39)|k1_relset_1(X39,X38,X40)=X39|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X39,X38))))&(~r2_hidden(k4_tarski(esk3_3(X38,X39,X40),X42),X40)|k1_relset_1(X39,X38,X40)=X39|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X39,X38)))))&(k1_relset_1(X39,X38,X40)!=X39|(~r2_hidden(X43,X39)|r2_hidden(k4_tarski(X43,esk4_4(X38,X39,X40,X43)),X40))|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X39,X38))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_relset_1])])])])])])).
% 41.42/41.65  cnf(c_0_43, negated_conjecture, (~m1_subset_1(X1,esk6_0)|~r2_hidden(X1,esk8_0)|esk10_0!=k1_funct_1(esk9_0,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 41.42/41.65  cnf(c_0_44, plain, (k1_funct_1(X1,esk5_5(X2,X3,X4,X1,X5))=X5|v1_xboole_0(X2)|v1_xboole_0(X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~r2_hidden(X5,k7_relset_1(X4,X2,X1,X3))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_30]), c_0_38])).
% 41.42/41.65  cnf(c_0_45, negated_conjecture, (v1_funct_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 41.42/41.65  cnf(c_0_46, negated_conjecture, (~m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 41.42/41.65  cnf(c_0_47, negated_conjecture, (r2_hidden(esk10_0,k9_relat_1(esk9_0,esk8_0))|~m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_41, c_0_23])).
% 41.42/41.65  fof(c_0_48, plain, ![X31, X32, X33]:(~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|k1_relset_1(X31,X32,X33)=k1_relat_1(X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 41.42/41.65  cnf(c_0_49, plain, (r2_hidden(esk3_3(X1,X2,X3),X2)|k1_relset_1(X2,X1,X3)=X2|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 41.42/41.65  cnf(c_0_50, negated_conjecture, (v1_xboole_0(X1)|esk10_0!=X2|~m1_subset_1(esk5_5(X3,X4,X1,esk9_0,X2),esk6_0)|~m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~r2_hidden(esk5_5(X3,X4,X1,esk9_0,X2),esk8_0)|~r2_hidden(X2,k7_relset_1(X1,X3,esk9_0,X4))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])]), c_0_46])).
% 41.42/41.65  cnf(c_0_51, plain, (m1_subset_1(esk5_5(X1,X2,X3,X4,X5),X3)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|~r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))|~m1_subset_1(X5,X1)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 41.42/41.65  cnf(c_0_52, negated_conjecture, (r2_hidden(esk10_0,k9_relat_1(esk9_0,esk8_0))), inference(spm,[status(thm)],[c_0_47, c_0_33])).
% 41.42/41.65  cnf(c_0_53, negated_conjecture, (v1_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_30, c_0_33])).
% 41.42/41.65  cnf(c_0_54, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 41.42/41.65  cnf(c_0_55, plain, (k1_relset_1(X1,X2,X3)=X1|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_19, c_0_49])).
% 41.42/41.65  cnf(c_0_56, negated_conjecture, (v1_xboole_0(esk6_0)|esk10_0!=X1|~m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,X2)))|~r2_hidden(esk5_5(X2,X3,esk6_0,esk9_0,X1),esk8_0)|~r2_hidden(X1,k7_relset_1(esk6_0,X2,esk9_0,X3))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_37]), c_0_46]), c_0_38])).
% 41.42/41.65  cnf(c_0_57, plain, (r2_hidden(esk5_5(X1,X2,X3,X4,X5),X2)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|~r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))|~m1_subset_1(X5,X1)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 41.42/41.65  cnf(c_0_58, negated_conjecture, (~v1_xboole_0(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_52]), c_0_53])])).
% 41.42/41.65  cnf(c_0_59, plain, (X1=k1_relat_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 41.42/41.65  cnf(c_0_60, negated_conjecture, (v1_xboole_0(esk6_0)|esk10_0!=X1|~m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,X2)))|~r2_hidden(X1,k7_relset_1(esk6_0,X2,esk9_0,esk8_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58]), c_0_37]), c_0_46])).
% 41.42/41.65  cnf(c_0_61, plain, (r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X3))|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 41.42/41.65  cnf(c_0_62, negated_conjecture, (esk6_0=k1_relat_1(esk9_0)|~v1_xboole_0(esk6_0)), inference(spm,[status(thm)],[c_0_59, c_0_33])).
% 41.42/41.65  cnf(c_0_63, negated_conjecture, (v1_xboole_0(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_22]), c_0_33])])).
% 41.42/41.65  cnf(c_0_64, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k9_relat_1(X1,X3))|~v1_xboole_0(k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_19, c_0_61])).
% 41.42/41.65  cnf(c_0_65, negated_conjecture, (esk6_0=k1_relat_1(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_63])])).
% 41.42/41.65  cnf(c_0_66, negated_conjecture, (~v1_xboole_0(k1_relat_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_52]), c_0_53])])).
% 41.42/41.65  cnf(c_0_67, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_65]), c_0_66]), ['proof']).
% 41.42/41.65  # SZS output end CNFRefutation
% 41.42/41.65  # Proof object total steps             : 68
% 41.42/41.65  # Proof object clause steps            : 43
% 41.42/41.65  # Proof object formula steps           : 25
% 41.42/41.65  # Proof object conjectures             : 23
% 41.42/41.65  # Proof object clause conjectures      : 20
% 41.42/41.65  # Proof object formula conjectures     : 3
% 41.42/41.65  # Proof object initial clauses used    : 18
% 41.42/41.65  # Proof object initial formulas used   : 12
% 41.42/41.65  # Proof object generating inferences   : 23
% 41.42/41.65  # Proof object simplifying inferences  : 27
% 41.42/41.65  # Training examples: 0 positive, 0 negative
% 41.42/41.65  # Parsed axioms                        : 12
% 41.42/41.65  # Removed by relevancy pruning/SinE    : 0
% 41.42/41.65  # Initial clauses                      : 27
% 41.42/41.65  # Removed in clause preprocessing      : 0
% 41.42/41.65  # Initial clauses in saturation        : 27
% 41.42/41.65  # Processed clauses                    : 88163
% 41.42/41.65  # ...of these trivial                  : 481
% 41.42/41.65  # ...subsumed                          : 71466
% 41.42/41.65  # ...remaining for further processing  : 16216
% 41.42/41.65  # Other redundant clauses eliminated   : 206
% 41.42/41.65  # Clauses deleted for lack of memory   : 0
% 41.42/41.65  # Backward-subsumed                    : 2115
% 41.42/41.65  # Backward-rewritten                   : 3899
% 41.42/41.65  # Generated clauses                    : 1148459
% 41.42/41.65  # ...of the previous two non-trivial   : 1148177
% 41.42/41.65  # Contextual simplify-reflections      : 2220
% 41.42/41.65  # Paramodulations                      : 1148249
% 41.42/41.65  # Factorizations                       : 0
% 41.42/41.65  # Equation resolutions                 : 210
% 41.42/41.65  # Propositional unsat checks           : 0
% 41.42/41.65  #    Propositional check models        : 0
% 41.42/41.65  #    Propositional check unsatisfiable : 0
% 41.42/41.65  #    Propositional clauses             : 0
% 41.42/41.65  #    Propositional clauses after purity: 0
% 41.42/41.65  #    Propositional unsat core size     : 0
% 41.42/41.65  #    Propositional preprocessing time  : 0.000
% 41.42/41.65  #    Propositional encoding time       : 0.000
% 41.42/41.65  #    Propositional solver time         : 0.000
% 41.42/41.65  #    Success case prop preproc time    : 0.000
% 41.42/41.65  #    Success case prop encoding time   : 0.000
% 41.42/41.65  #    Success case prop solver time     : 0.000
% 41.42/41.65  # Current number of processed clauses  : 10175
% 41.42/41.65  #    Positive orientable unit clauses  : 7
% 41.42/41.65  #    Positive unorientable unit clauses: 0
% 41.42/41.65  #    Negative unit clauses             : 6
% 41.42/41.65  #    Non-unit-clauses                  : 10162
% 41.42/41.65  # Current number of unprocessed clauses: 1056042
% 41.42/41.65  # ...number of literals in the above   : 11132693
% 41.42/41.65  # Current number of archived formulas  : 0
% 41.42/41.65  # Current number of archived clauses   : 6041
% 41.42/41.65  # Clause-clause subsumption calls (NU) : 39863206
% 41.42/41.65  # Rec. Clause-clause subsumption calls : 1725824
% 41.42/41.65  # Non-unit clause-clause subsumptions  : 59151
% 41.42/41.65  # Unit Clause-clause subsumption calls : 2767
% 41.42/41.65  # Rewrite failures with RHS unbound    : 0
% 41.42/41.65  # BW rewrite match attempts            : 3
% 41.42/41.65  # BW rewrite match successes           : 3
% 41.42/41.65  # Condensation attempts                : 0
% 41.42/41.65  # Condensation successes               : 0
% 41.42/41.65  # Termbank termtop insertions          : 62058983
% 41.52/41.71  
% 41.52/41.71  # -------------------------------------------------
% 41.52/41.71  # User time                : 40.624 s
% 41.52/41.71  # System time              : 0.723 s
% 41.52/41.71  # Total time               : 41.346 s
% 41.52/41.71  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
