%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:29 EST 2020

% Result     : Theorem 20.14s
% Output     : CNFRefutation 20.14s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 383 expanded)
%              Number of clauses        :   46 ( 160 expanded)
%              Number of leaves         :   13 (  98 expanded)
%              Depth                    :   12
%              Number of atoms          :  284 (1674 expanded)
%              Number of equality atoms :   28 ( 159 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(dt_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(t22_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
     => ( ! [X4] :
            ~ ( r2_hidden(X4,X2)
              & ! [X5] : ~ r2_hidden(k4_tarski(X4,X5),X3) )
      <=> k1_relset_1(X2,X1,X3) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

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

fof(c_0_15,plain,(
    ! [X13,X14,X15] :
      ( ~ r2_hidden(X13,X14)
      | ~ m1_subset_1(X14,k1_zfmisc_1(X15))
      | m1_subset_1(X13,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_16,plain,(
    ! [X30,X31,X32,X33] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
      | m1_subset_1(k7_relset_1(X30,X31,X32,X33),k1_zfmisc_1(X31)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).

cnf(c_0_17,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X37,X38,X39,X40] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
      | k7_relset_1(X37,X38,X39,X40) = k9_relat_1(X39,X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_20,plain,(
    ! [X24,X25,X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
      | v1_relat_1(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_21,negated_conjecture,(
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

fof(c_0_22,plain,(
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

fof(c_0_23,plain,(
    ! [X48,X49,X50,X51,X52,X54] :
      ( ( m1_subset_1(esk5_5(X48,X49,X50,X51,X52),X50)
        | ~ r2_hidden(X52,k7_relset_1(X50,X48,X51,X49))
        | ~ m1_subset_1(X52,X48)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X50,X48)))
        | v1_xboole_0(X50)
        | v1_xboole_0(X49)
        | v1_xboole_0(X48) )
      & ( r2_hidden(k4_tarski(esk5_5(X48,X49,X50,X51,X52),X52),X51)
        | ~ r2_hidden(X52,k7_relset_1(X50,X48,X51,X49))
        | ~ m1_subset_1(X52,X48)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X50,X48)))
        | v1_xboole_0(X50)
        | v1_xboole_0(X49)
        | v1_xboole_0(X48) )
      & ( r2_hidden(esk5_5(X48,X49,X50,X51,X52),X49)
        | ~ r2_hidden(X52,k7_relset_1(X50,X48,X51,X49))
        | ~ m1_subset_1(X52,X48)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X50,X48)))
        | v1_xboole_0(X50)
        | v1_xboole_0(X49)
        | v1_xboole_0(X48) )
      & ( ~ m1_subset_1(X54,X50)
        | ~ r2_hidden(k4_tarski(X54,X52),X51)
        | ~ r2_hidden(X54,X49)
        | r2_hidden(X52,k7_relset_1(X50,X48,X51,X49))
        | ~ m1_subset_1(X52,X48)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X50,X48)))
        | v1_xboole_0(X50)
        | v1_xboole_0(X49)
        | v1_xboole_0(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t52_relset_1])])])])])])).

cnf(c_0_24,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(X1,X3))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_27,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_29,negated_conjecture,(
    ! [X60] :
      ( v1_funct_1(esk9_0)
      & v1_funct_2(esk9_0,esk6_0,esk7_0)
      & m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))
      & r2_hidden(esk10_0,k7_relset_1(esk6_0,esk7_0,esk9_0,esk8_0))
      & ( ~ r2_hidden(X60,esk6_0)
        | ~ r2_hidden(X60,esk8_0)
        | esk10_0 != k1_funct_1(esk9_0,X60) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])])).

cnf(c_0_30,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( r2_hidden(k4_tarski(esk5_5(X1,X2,X3,X4,X5),X5),X4)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))
    | ~ m1_subset_1(X5,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( m1_subset_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ r2_hidden(X1,k7_relset_1(X4,X2,X3,X5)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,k7_relset_1(X2,X3,X1,X5))
    | ~ v1_xboole_0(X5) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( ~ r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk8_0)
    | esk10_0 != k1_funct_1(esk9_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( k1_funct_1(X1,esk5_5(X2,X3,X4,X1,X5)) = X5
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ r2_hidden(X5,k7_relset_1(X4,X2,X1,X3)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_28]),c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk10_0,k7_relset_1(esk6_0,esk7_0,esk9_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_39,plain,(
    ! [X11,X12] :
      ( ~ m1_subset_1(X11,X12)
      | v1_xboole_0(X12)
      | r2_hidden(X11,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_40,plain,
    ( k7_relset_1(X1,X2,X3,X4) = k7_relset_1(X5,X6,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_27])).

fof(c_0_41,plain,(
    ! [X41,X42,X43,X45,X46] :
      ( ( r2_hidden(esk3_3(X41,X42,X43),X42)
        | k1_relset_1(X42,X41,X43) = X42
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X42,X41))) )
      & ( ~ r2_hidden(k4_tarski(esk3_3(X41,X42,X43),X45),X43)
        | k1_relset_1(X42,X41,X43) = X42
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X42,X41))) )
      & ( k1_relset_1(X42,X41,X43) != X42
        | ~ r2_hidden(X46,X42)
        | r2_hidden(k4_tarski(X46,esk4_4(X41,X42,X43,X46)),X43)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X42,X41))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_relset_1])])])])])])).

cnf(c_0_42,negated_conjecture,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | esk10_0 != X3
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(esk5_5(X2,X4,X1,esk9_0,X3),esk6_0)
    | ~ r2_hidden(esk5_5(X2,X4,X1,esk9_0,X3),esk8_0)
    | ~ r2_hidden(X3,k7_relset_1(X1,X2,esk9_0,X4)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])])).

cnf(c_0_43,plain,
    ( r2_hidden(esk5_5(X1,X2,X3,X4,X5),X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))
    | ~ m1_subset_1(X5,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_44,negated_conjecture,
    ( ~ v1_xboole_0(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_37]),c_0_38])])).

cnf(c_0_45,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( m1_subset_1(esk5_5(X1,X2,X3,X4,X5),X3)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))
    | ~ m1_subset_1(X5,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk10_0,k7_relset_1(X1,X2,esk9_0,esk8_0))
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_40]),c_0_38])])).

fof(c_0_48,plain,(
    ! [X34,X35,X36] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
      | k1_relset_1(X34,X35,X36) = k1_relat_1(X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_49,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
    | k1_relset_1(X2,X1,X3) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_50,plain,(
    ! [X27,X28,X29] :
      ( ~ v1_xboole_0(X27)
      | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X28,X27)))
      | v1_xboole_0(X29) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

cnf(c_0_51,negated_conjecture,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | esk10_0 != X3
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ r2_hidden(esk5_5(X1,esk8_0,X2,esk9_0,X3),esk6_0)
    | ~ r2_hidden(X3,k7_relset_1(X2,X1,esk9_0,esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_32])).

cnf(c_0_52,plain,
    ( r2_hidden(esk5_5(X1,X2,X3,X4,X5),X3)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r2_hidden(X5,k7_relset_1(X3,X1,X4,X2)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_32]),c_0_33])).

cnf(c_0_53,plain,
    ( r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk10_0,k9_relat_1(esk9_0,esk8_0))
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_27])).

cnf(c_0_55,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,plain,
    ( k1_relset_1(X1,X2,X3) = X1
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_49])).

cnf(c_0_57,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( v1_xboole_0(esk6_0)
    | v1_xboole_0(X1)
    | esk10_0 != X2
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,X1)))
    | ~ r2_hidden(X2,k7_relset_1(esk6_0,X1,esk9_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_59,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(X1,X3))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk10_0,k9_relat_1(esk9_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_38])).

cnf(c_0_61,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_38])).

cnf(c_0_62,plain,
    ( X1 = k1_relat_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_63,negated_conjecture,
    ( v1_xboole_0(esk9_0)
    | ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_38])).

cnf(c_0_64,negated_conjecture,
    ( v1_xboole_0(esk7_0)
    | v1_xboole_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_37]),c_0_38])])).

cnf(c_0_65,negated_conjecture,
    ( ~ v1_xboole_0(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])])).

cnf(c_0_66,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X3))
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_67,negated_conjecture,
    ( esk6_0 = k1_relat_1(esk9_0)
    | ~ v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_38])).

cnf(c_0_68,negated_conjecture,
    ( v1_xboole_0(esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])).

cnf(c_0_69,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(X1,X3))
    | ~ v1_xboole_0(k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_66])).

cnf(c_0_70,negated_conjecture,
    ( esk6_0 = k1_relat_1(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_68])])).

cnf(c_0_71,negated_conjecture,
    ( ~ v1_xboole_0(k1_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_60]),c_0_61])])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_70]),c_0_71]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:27:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 20.14/20.32  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 20.14/20.32  # and selection function SelectMaxLComplexAvoidPosPred.
% 20.14/20.32  #
% 20.14/20.32  # Preprocessing time       : 0.029 s
% 20.14/20.32  # Presaturation interreduction done
% 20.14/20.32  
% 20.14/20.32  # Proof found!
% 20.14/20.32  # SZS status Theorem
% 20.14/20.32  # SZS output start CNFRefutation
% 20.14/20.32  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 20.14/20.32  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 20.14/20.32  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 20.14/20.32  fof(dt_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 20.14/20.32  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 20.14/20.32  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 20.14/20.32  fof(t115_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:~(((r2_hidden(X6,X1)&r2_hidden(X6,X3))&X5=k1_funct_1(X4,X6)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_funct_2)).
% 20.14/20.32  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 20.14/20.32  fof(t52_relset_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))<=>?[X6]:((m1_subset_1(X6,X3)&r2_hidden(k4_tarski(X6,X5),X4))&r2_hidden(X6,X2)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relset_1)).
% 20.14/20.32  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 20.14/20.32  fof(t22_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~(r2_hidden(k4_tarski(X4,X5),X3))))<=>k1_relset_1(X2,X1,X3)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relset_1)).
% 20.14/20.32  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 20.14/20.32  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 20.14/20.32  fof(c_0_13, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 20.14/20.32  fof(c_0_14, plain, ![X16, X17, X18, X20]:((((r2_hidden(esk2_3(X16,X17,X18),k1_relat_1(X18))|~r2_hidden(X16,k9_relat_1(X18,X17))|~v1_relat_1(X18))&(r2_hidden(k4_tarski(esk2_3(X16,X17,X18),X16),X18)|~r2_hidden(X16,k9_relat_1(X18,X17))|~v1_relat_1(X18)))&(r2_hidden(esk2_3(X16,X17,X18),X17)|~r2_hidden(X16,k9_relat_1(X18,X17))|~v1_relat_1(X18)))&(~r2_hidden(X20,k1_relat_1(X18))|~r2_hidden(k4_tarski(X20,X16),X18)|~r2_hidden(X20,X17)|r2_hidden(X16,k9_relat_1(X18,X17))|~v1_relat_1(X18))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 20.14/20.32  fof(c_0_15, plain, ![X13, X14, X15]:(~r2_hidden(X13,X14)|~m1_subset_1(X14,k1_zfmisc_1(X15))|m1_subset_1(X13,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 20.14/20.32  fof(c_0_16, plain, ![X30, X31, X32, X33]:(~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|m1_subset_1(k7_relset_1(X30,X31,X32,X33),k1_zfmisc_1(X31))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).
% 20.14/20.32  cnf(c_0_17, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 20.14/20.32  cnf(c_0_18, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 20.14/20.32  fof(c_0_19, plain, ![X37, X38, X39, X40]:(~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))|k7_relset_1(X37,X38,X39,X40)=k9_relat_1(X39,X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 20.14/20.32  fof(c_0_20, plain, ![X24, X25, X26]:(~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))|v1_relat_1(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 20.14/20.32  fof(c_0_21, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:~(((r2_hidden(X6,X1)&r2_hidden(X6,X3))&X5=k1_funct_1(X4,X6))))))), inference(assume_negation,[status(cth)],[t115_funct_2])).
% 20.14/20.32  fof(c_0_22, plain, ![X21, X22, X23]:(((r2_hidden(X21,k1_relat_1(X23))|~r2_hidden(k4_tarski(X21,X22),X23)|(~v1_relat_1(X23)|~v1_funct_1(X23)))&(X22=k1_funct_1(X23,X21)|~r2_hidden(k4_tarski(X21,X22),X23)|(~v1_relat_1(X23)|~v1_funct_1(X23))))&(~r2_hidden(X21,k1_relat_1(X23))|X22!=k1_funct_1(X23,X21)|r2_hidden(k4_tarski(X21,X22),X23)|(~v1_relat_1(X23)|~v1_funct_1(X23)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 20.14/20.32  fof(c_0_23, plain, ![X48, X49, X50, X51, X52, X54]:((((m1_subset_1(esk5_5(X48,X49,X50,X51,X52),X50)|~r2_hidden(X52,k7_relset_1(X50,X48,X51,X49))|~m1_subset_1(X52,X48)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X50,X48)))|v1_xboole_0(X50)|v1_xboole_0(X49)|v1_xboole_0(X48))&(r2_hidden(k4_tarski(esk5_5(X48,X49,X50,X51,X52),X52),X51)|~r2_hidden(X52,k7_relset_1(X50,X48,X51,X49))|~m1_subset_1(X52,X48)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X50,X48)))|v1_xboole_0(X50)|v1_xboole_0(X49)|v1_xboole_0(X48)))&(r2_hidden(esk5_5(X48,X49,X50,X51,X52),X49)|~r2_hidden(X52,k7_relset_1(X50,X48,X51,X49))|~m1_subset_1(X52,X48)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X50,X48)))|v1_xboole_0(X50)|v1_xboole_0(X49)|v1_xboole_0(X48)))&(~m1_subset_1(X54,X50)|~r2_hidden(k4_tarski(X54,X52),X51)|~r2_hidden(X54,X49)|r2_hidden(X52,k7_relset_1(X50,X48,X51,X49))|~m1_subset_1(X52,X48)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X50,X48)))|v1_xboole_0(X50)|v1_xboole_0(X49)|v1_xboole_0(X48))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t52_relset_1])])])])])])).
% 20.14/20.32  cnf(c_0_24, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 20.14/20.32  cnf(c_0_25, plain, (m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 20.14/20.32  cnf(c_0_26, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k9_relat_1(X1,X3))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 20.14/20.32  cnf(c_0_27, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 20.14/20.32  cnf(c_0_28, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 20.14/20.32  fof(c_0_29, negated_conjecture, ![X60]:(((v1_funct_1(esk9_0)&v1_funct_2(esk9_0,esk6_0,esk7_0))&m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))))&(r2_hidden(esk10_0,k7_relset_1(esk6_0,esk7_0,esk9_0,esk8_0))&(~r2_hidden(X60,esk6_0)|~r2_hidden(X60,esk8_0)|esk10_0!=k1_funct_1(esk9_0,X60)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])])).
% 20.14/20.32  cnf(c_0_30, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 20.14/20.32  cnf(c_0_31, plain, (r2_hidden(k4_tarski(esk5_5(X1,X2,X3,X4,X5),X5),X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|~r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))|~m1_subset_1(X5,X1)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 20.14/20.32  cnf(c_0_32, plain, (m1_subset_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~r2_hidden(X1,k7_relset_1(X4,X2,X3,X5))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 20.14/20.32  cnf(c_0_33, plain, (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,k7_relset_1(X2,X3,X1,X5))|~v1_xboole_0(X5)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 20.14/20.32  cnf(c_0_34, negated_conjecture, (~r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk8_0)|esk10_0!=k1_funct_1(esk9_0,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 20.14/20.32  cnf(c_0_35, plain, (k1_funct_1(X1,esk5_5(X2,X3,X4,X1,X5))=X5|v1_xboole_0(X2)|v1_xboole_0(X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~r2_hidden(X5,k7_relset_1(X4,X2,X1,X3))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_28]), c_0_33])).
% 20.14/20.32  cnf(c_0_36, negated_conjecture, (v1_funct_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 20.14/20.32  cnf(c_0_37, negated_conjecture, (r2_hidden(esk10_0,k7_relset_1(esk6_0,esk7_0,esk9_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 20.14/20.32  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 20.14/20.32  fof(c_0_39, plain, ![X11, X12]:(~m1_subset_1(X11,X12)|(v1_xboole_0(X12)|r2_hidden(X11,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 20.14/20.32  cnf(c_0_40, plain, (k7_relset_1(X1,X2,X3,X4)=k7_relset_1(X5,X6,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(spm,[status(thm)],[c_0_27, c_0_27])).
% 20.14/20.32  fof(c_0_41, plain, ![X41, X42, X43, X45, X46]:(((r2_hidden(esk3_3(X41,X42,X43),X42)|k1_relset_1(X42,X41,X43)=X42|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X42,X41))))&(~r2_hidden(k4_tarski(esk3_3(X41,X42,X43),X45),X43)|k1_relset_1(X42,X41,X43)=X42|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X42,X41)))))&(k1_relset_1(X42,X41,X43)!=X42|(~r2_hidden(X46,X42)|r2_hidden(k4_tarski(X46,esk4_4(X41,X42,X43,X46)),X43))|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X42,X41))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_relset_1])])])])])])).
% 20.14/20.32  cnf(c_0_42, negated_conjecture, (v1_xboole_0(X1)|v1_xboole_0(X2)|esk10_0!=X3|~m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r2_hidden(esk5_5(X2,X4,X1,esk9_0,X3),esk6_0)|~r2_hidden(esk5_5(X2,X4,X1,esk9_0,X3),esk8_0)|~r2_hidden(X3,k7_relset_1(X1,X2,esk9_0,X4))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])])).
% 20.14/20.32  cnf(c_0_43, plain, (r2_hidden(esk5_5(X1,X2,X3,X4,X5),X2)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|~r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))|~m1_subset_1(X5,X1)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 20.14/20.32  cnf(c_0_44, negated_conjecture, (~v1_xboole_0(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_37]), c_0_38])])).
% 20.14/20.32  cnf(c_0_45, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 20.14/20.32  cnf(c_0_46, plain, (m1_subset_1(esk5_5(X1,X2,X3,X4,X5),X3)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|~r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))|~m1_subset_1(X5,X1)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 20.14/20.32  cnf(c_0_47, negated_conjecture, (r2_hidden(esk10_0,k7_relset_1(X1,X2,esk9_0,esk8_0))|~m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_40]), c_0_38])])).
% 20.14/20.32  fof(c_0_48, plain, ![X34, X35, X36]:(~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|k1_relset_1(X34,X35,X36)=k1_relat_1(X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 20.14/20.32  cnf(c_0_49, plain, (r2_hidden(esk3_3(X1,X2,X3),X2)|k1_relset_1(X2,X1,X3)=X2|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 20.14/20.32  fof(c_0_50, plain, ![X27, X28, X29]:(~v1_xboole_0(X27)|(~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X28,X27)))|v1_xboole_0(X29))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 20.14/20.32  cnf(c_0_51, negated_conjecture, (v1_xboole_0(X1)|v1_xboole_0(X2)|esk10_0!=X3|~m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|~r2_hidden(esk5_5(X1,esk8_0,X2,esk9_0,X3),esk6_0)|~r2_hidden(X3,k7_relset_1(X2,X1,esk9_0,esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_32])).
% 20.14/20.32  cnf(c_0_52, plain, (r2_hidden(esk5_5(X1,X2,X3,X4,X5),X3)|v1_xboole_0(X1)|v1_xboole_0(X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_32]), c_0_33])).
% 20.14/20.32  cnf(c_0_53, plain, (r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 20.14/20.32  cnf(c_0_54, negated_conjecture, (r2_hidden(esk10_0,k9_relat_1(esk9_0,esk8_0))|~m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_47, c_0_27])).
% 20.14/20.32  cnf(c_0_55, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 20.14/20.32  cnf(c_0_56, plain, (k1_relset_1(X1,X2,X3)=X1|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_17, c_0_49])).
% 20.14/20.32  cnf(c_0_57, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 20.14/20.32  cnf(c_0_58, negated_conjecture, (v1_xboole_0(esk6_0)|v1_xboole_0(X1)|esk10_0!=X2|~m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,X1)))|~r2_hidden(X2,k7_relset_1(esk6_0,X1,esk9_0,esk8_0))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 20.14/20.32  cnf(c_0_59, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k9_relat_1(X1,X3))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_17, c_0_53])).
% 20.14/20.32  cnf(c_0_60, negated_conjecture, (r2_hidden(esk10_0,k9_relat_1(esk9_0,esk8_0))), inference(spm,[status(thm)],[c_0_54, c_0_38])).
% 20.14/20.32  cnf(c_0_61, negated_conjecture, (v1_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_28, c_0_38])).
% 20.14/20.32  cnf(c_0_62, plain, (X1=k1_relat_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 20.14/20.32  cnf(c_0_63, negated_conjecture, (v1_xboole_0(esk9_0)|~v1_xboole_0(esk7_0)), inference(spm,[status(thm)],[c_0_57, c_0_38])).
% 20.14/20.32  cnf(c_0_64, negated_conjecture, (v1_xboole_0(esk7_0)|v1_xboole_0(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_37]), c_0_38])])).
% 20.14/20.32  cnf(c_0_65, negated_conjecture, (~v1_xboole_0(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61])])).
% 20.14/20.32  cnf(c_0_66, plain, (r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X3))|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 20.14/20.32  cnf(c_0_67, negated_conjecture, (esk6_0=k1_relat_1(esk9_0)|~v1_xboole_0(esk6_0)), inference(spm,[status(thm)],[c_0_62, c_0_38])).
% 20.14/20.32  cnf(c_0_68, negated_conjecture, (v1_xboole_0(esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65])).
% 20.14/20.32  cnf(c_0_69, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k9_relat_1(X1,X3))|~v1_xboole_0(k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_17, c_0_66])).
% 20.14/20.32  cnf(c_0_70, negated_conjecture, (esk6_0=k1_relat_1(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_68])])).
% 20.14/20.32  cnf(c_0_71, negated_conjecture, (~v1_xboole_0(k1_relat_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_60]), c_0_61])])).
% 20.14/20.32  cnf(c_0_72, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_70]), c_0_71]), ['proof']).
% 20.14/20.32  # SZS output end CNFRefutation
% 20.14/20.32  # Proof object total steps             : 73
% 20.14/20.32  # Proof object clause steps            : 46
% 20.14/20.32  # Proof object formula steps           : 27
% 20.14/20.32  # Proof object conjectures             : 23
% 20.14/20.32  # Proof object clause conjectures      : 20
% 20.14/20.32  # Proof object formula conjectures     : 3
% 20.14/20.32  # Proof object initial clauses used    : 20
% 20.14/20.32  # Proof object initial formulas used   : 13
% 20.14/20.32  # Proof object generating inferences   : 24
% 20.14/20.32  # Proof object simplifying inferences  : 25
% 20.14/20.32  # Training examples: 0 positive, 0 negative
% 20.14/20.32  # Parsed axioms                        : 13
% 20.14/20.32  # Removed by relevancy pruning/SinE    : 0
% 20.14/20.32  # Initial clauses                      : 28
% 20.14/20.32  # Removed in clause preprocessing      : 0
% 20.14/20.32  # Initial clauses in saturation        : 28
% 20.14/20.32  # Processed clauses                    : 50890
% 20.14/20.32  # ...of these trivial                  : 323
% 20.14/20.32  # ...subsumed                          : 40085
% 20.14/20.32  # ...remaining for further processing  : 10482
% 20.14/20.32  # Other redundant clauses eliminated   : 20
% 20.14/20.32  # Clauses deleted for lack of memory   : 0
% 20.14/20.32  # Backward-subsumed                    : 2160
% 20.14/20.32  # Backward-rewritten                   : 2231
% 20.14/20.32  # Generated clauses                    : 565648
% 20.14/20.32  # ...of the previous two non-trivial   : 560953
% 20.14/20.32  # Contextual simplify-reflections      : 1474
% 20.14/20.32  # Paramodulations                      : 565622
% 20.14/20.32  # Factorizations                       : 0
% 20.14/20.32  # Equation resolutions                 : 25
% 20.14/20.32  # Propositional unsat checks           : 0
% 20.14/20.32  #    Propositional check models        : 0
% 20.14/20.32  #    Propositional check unsatisfiable : 0
% 20.14/20.32  #    Propositional clauses             : 0
% 20.14/20.32  #    Propositional clauses after purity: 0
% 20.14/20.32  #    Propositional unsat core size     : 0
% 20.14/20.32  #    Propositional preprocessing time  : 0.000
% 20.14/20.32  #    Propositional encoding time       : 0.000
% 20.14/20.32  #    Propositional solver time         : 0.000
% 20.14/20.32  #    Success case prop preproc time    : 0.000
% 20.14/20.32  #    Success case prop encoding time   : 0.000
% 20.14/20.32  #    Success case prop solver time     : 0.000
% 20.14/20.32  # Current number of processed clauses  : 6062
% 20.14/20.32  #    Positive orientable unit clauses  : 7
% 20.14/20.32  #    Positive unorientable unit clauses: 0
% 20.14/20.32  #    Negative unit clauses             : 5
% 20.14/20.32  #    Non-unit-clauses                  : 6050
% 20.14/20.32  # Current number of unprocessed clauses: 507322
% 20.14/20.32  # ...number of literals in the above   : 4881016
% 20.14/20.32  # Current number of archived formulas  : 0
% 20.14/20.32  # Current number of archived clauses   : 4420
% 20.14/20.32  # Clause-clause subsumption calls (NU) : 18495242
% 20.14/20.32  # Rec. Clause-clause subsumption calls : 616060
% 20.14/20.32  # Non-unit clause-clause subsumptions  : 34765
% 20.14/20.32  # Unit Clause-clause subsumption calls : 1457
% 20.14/20.32  # Rewrite failures with RHS unbound    : 0
% 20.14/20.32  # BW rewrite match attempts            : 3
% 20.14/20.32  # BW rewrite match successes           : 3
% 20.14/20.32  # Condensation attempts                : 0
% 20.14/20.32  # Condensation successes               : 0
% 20.14/20.32  # Termbank termtop insertions          : 25744443
% 20.14/20.35  
% 20.14/20.35  # -------------------------------------------------
% 20.14/20.35  # User time                : 19.655 s
% 20.14/20.35  # System time              : 0.350 s
% 20.14/20.35  # Total time               : 20.005 s
% 20.14/20.35  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
