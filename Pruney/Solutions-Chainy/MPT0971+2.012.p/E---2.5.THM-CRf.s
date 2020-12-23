%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:01:38 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   71 (1104 expanded)
%              Number of clauses        :   43 ( 450 expanded)
%              Number of leaves         :   14 ( 261 expanded)
%              Depth                    :   10
%              Number of atoms          :  270 (4862 expanded)
%              Number of equality atoms :   88 (1189 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t17_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ~ ( r2_hidden(X3,k2_relset_1(X1,X2,X4))
          & ! [X5] :
              ~ ( r2_hidden(X5,X1)
                & k1_funct_1(X4,X5) = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_2)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(d5_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( X2 = k2_relat_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                  & X3 = k1_funct_1(X1,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

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

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t62_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
        & k5_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

fof(t6_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
     => ~ ( r2_hidden(X1,X4)
          & ! [X5,X6] :
              ~ ( X1 = k4_tarski(X5,X6)
                & r2_hidden(X5,X2)
                & r2_hidden(X6,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).

fof(t10_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ~ ( X2 != k1_xboole_0
          & ! [X3] :
              ( m1_subset_1(X3,X1)
             => ~ r2_hidden(X3,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(l35_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(t25_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k2_relat_1(k5_relat_1(X3,X2)))
           => r2_hidden(X1,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_funct_1)).

fof(t45_ordinal1,axiom,(
    ! [X1] :
      ( v1_relat_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X1)
      & v1_funct_1(k1_xboole_0)
      & v5_ordinal1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ~ ( r2_hidden(X3,k2_relset_1(X1,X2,X4))
            & ! [X5] :
                ~ ( r2_hidden(X5,X1)
                  & k1_funct_1(X4,X5) = X3 ) ) ) ),
    inference(assume_negation,[status(cth)],[t17_funct_2])).

fof(c_0_15,plain,(
    ! [X42,X43,X44] :
      ( ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
      | k2_relset_1(X42,X43,X44) = k2_relat_1(X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_16,negated_conjecture,(
    ! [X58] :
      ( v1_funct_1(esk11_0)
      & v1_funct_2(esk11_0,esk8_0,esk9_0)
      & m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0)))
      & r2_hidden(esk10_0,k2_relset_1(esk8_0,esk9_0,esk11_0))
      & ( ~ r2_hidden(X58,esk8_0)
        | k1_funct_1(esk11_0,X58) != esk10_0 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])])).

fof(c_0_17,plain,(
    ! [X22,X23,X24,X26,X27,X28,X30] :
      ( ( r2_hidden(esk3_3(X22,X23,X24),k1_relat_1(X22))
        | ~ r2_hidden(X24,X23)
        | X23 != k2_relat_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( X24 = k1_funct_1(X22,esk3_3(X22,X23,X24))
        | ~ r2_hidden(X24,X23)
        | X23 != k2_relat_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( ~ r2_hidden(X27,k1_relat_1(X22))
        | X26 != k1_funct_1(X22,X27)
        | r2_hidden(X26,X23)
        | X23 != k2_relat_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( ~ r2_hidden(esk4_2(X22,X28),X28)
        | ~ r2_hidden(X30,k1_relat_1(X22))
        | esk4_2(X22,X28) != k1_funct_1(X22,X30)
        | X28 = k2_relat_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( r2_hidden(esk5_2(X22,X28),k1_relat_1(X22))
        | r2_hidden(esk4_2(X22,X28),X28)
        | X28 = k2_relat_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( esk4_2(X22,X28) = k1_funct_1(X22,esk5_2(X22,X28))
        | r2_hidden(esk4_2(X22,X28),X28)
        | X28 = k2_relat_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

cnf(c_0_18,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X36,X37,X38] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
      | v1_relat_1(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_21,plain,(
    ! [X51,X52,X53] :
      ( ( ~ v1_funct_2(X53,X51,X52)
        | X51 = k1_relset_1(X51,X52,X53)
        | X52 = k1_xboole_0
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) )
      & ( X51 != k1_relset_1(X51,X52,X53)
        | v1_funct_2(X53,X51,X52)
        | X52 = k1_xboole_0
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) )
      & ( ~ v1_funct_2(X53,X51,X52)
        | X51 = k1_relset_1(X51,X52,X53)
        | X51 != k1_xboole_0
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) )
      & ( X51 != k1_relset_1(X51,X52,X53)
        | v1_funct_2(X53,X51,X52)
        | X51 != k1_xboole_0
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) )
      & ( ~ v1_funct_2(X53,X51,X52)
        | X53 = k1_xboole_0
        | X51 = k1_xboole_0
        | X52 != k1_xboole_0
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) )
      & ( X53 != k1_xboole_0
        | v1_funct_2(X53,X51,X52)
        | X51 = k1_xboole_0
        | X52 != k1_xboole_0
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_22,plain,(
    ! [X39,X40,X41] :
      ( ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
      | k1_relset_1(X39,X40,X41) = k1_relat_1(X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_23,plain,
    ( X1 = k1_funct_1(X2,esk3_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk10_0,k2_relset_1(esk8_0,esk9_0,esk11_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( k2_relset_1(esk8_0,esk9_0,esk11_0) = k2_relat_1(esk11_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,plain,(
    ! [X21] :
      ( ( k5_relat_1(k1_xboole_0,X21) = k1_xboole_0
        | ~ v1_relat_1(X21) )
      & ( k5_relat_1(X21,k1_xboole_0) = k1_xboole_0
        | ~ v1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_relat_1])])])).

fof(c_0_28,plain,(
    ! [X45,X46,X47,X48] :
      ( ( X45 = k4_tarski(esk6_4(X45,X46,X47,X48),esk7_4(X45,X46,X47,X48))
        | ~ r2_hidden(X45,X48)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) )
      & ( r2_hidden(esk6_4(X45,X46,X47,X48),X46)
        | ~ r2_hidden(X45,X48)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) )
      & ( r2_hidden(esk7_4(X45,X46,X47,X48),X47)
        | ~ r2_hidden(X45,X48)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_relset_1])])])])).

fof(c_0_29,plain,(
    ! [X18,X19] :
      ( ( m1_subset_1(esk2_2(X18,X19),X18)
        | X19 = k1_xboole_0
        | ~ m1_subset_1(X19,k1_zfmisc_1(X18)) )
      & ( r2_hidden(esk2_2(X18,X19),X19)
        | X19 = k1_xboole_0
        | ~ m1_subset_1(X19,k1_zfmisc_1(X18)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_subset_1])])])])])).

cnf(c_0_30,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_31,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_2(esk11_0,esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_33,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( k1_funct_1(X1,esk3_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk10_0,k2_relat_1(esk11_0)) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_1(esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_37,negated_conjecture,
    ( v1_relat_1(esk11_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_19])).

fof(c_0_38,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( r2_hidden(X10,X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k4_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k4_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k4_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_39,plain,(
    ! [X16,X17] :
      ( ( k4_xboole_0(k1_tarski(X16),X17) != k1_xboole_0
        | r2_hidden(X16,X17) )
      & ( ~ r2_hidden(X16,X17)
        | k4_xboole_0(k1_tarski(X16),X17) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l35_zfmisc_1])])).

fof(c_0_40,plain,(
    ! [X32,X33,X34] :
      ( ~ v1_relat_1(X33)
      | ~ v1_funct_1(X33)
      | ~ v1_relat_1(X34)
      | ~ v1_funct_1(X34)
      | ~ r2_hidden(X32,k2_relat_1(k5_relat_1(X34,X33)))
      | r2_hidden(X32,k2_relat_1(X33)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_funct_1])])])).

cnf(c_0_41,plain,
    ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_42,plain,(
    ! [X35] :
      ( v1_relat_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X35)
      & v1_funct_1(k1_xboole_0)
      & v5_ordinal1(k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[t45_ordinal1])).

cnf(c_0_43,plain,
    ( r2_hidden(esk7_4(X1,X2,X3,X4),X3)
    | ~ r2_hidden(X1,X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_44,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | X2 = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_45,plain,
    ( r2_hidden(esk3_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_46,negated_conjecture,
    ( k1_relset_1(esk8_0,esk9_0,esk11_0) = esk8_0
    | esk9_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_19]),c_0_32])])).

cnf(c_0_47,negated_conjecture,
    ( k1_relset_1(esk8_0,esk9_0,esk11_0) = k1_relat_1(esk11_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_19])).

cnf(c_0_48,negated_conjecture,
    ( ~ r2_hidden(X1,esk8_0)
    | k1_funct_1(esk11_0,X1) != esk10_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_49,negated_conjecture,
    ( k1_funct_1(esk11_0,esk3_3(esk11_0,k2_relat_1(esk11_0),esk10_0)) = esk10_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37])])).

cnf(c_0_50,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_51,plain,
    ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_52,plain,
    ( r2_hidden(X3,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,k2_relat_1(k5_relat_1(X2,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_53,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk11_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_37])).

cnf(c_0_54,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_55,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_56,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk7_4(X1,esk8_0,esk9_0,esk11_0),esk9_0)
    | ~ r2_hidden(X1,esk11_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_19])).

cnf(c_0_58,negated_conjecture,
    ( esk11_0 = k1_xboole_0
    | r2_hidden(esk2_2(k2_zfmisc_1(esk8_0,esk9_0),esk11_0),esk11_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_19])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk3_3(esk11_0,k2_relat_1(esk11_0),esk10_0),k1_relat_1(esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_35]),c_0_36]),c_0_37])])).

cnf(c_0_60,negated_conjecture,
    ( k1_relat_1(esk11_0) = esk8_0
    | esk9_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_61,negated_conjecture,
    ( ~ r2_hidden(esk3_3(esk11_0,k2_relat_1(esk11_0),esk10_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_62,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_63,negated_conjecture,
    ( k4_xboole_0(k1_tarski(esk10_0),k2_relat_1(esk11_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_35])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(X1,k2_relat_1(esk11_0))
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_36]),c_0_55]),c_0_37]),c_0_56])])).

cnf(c_0_65,negated_conjecture,
    ( esk11_0 = k1_xboole_0
    | r2_hidden(esk7_4(esk2_2(k2_zfmisc_1(esk8_0,esk9_0),esk11_0),esk8_0,esk9_0,esk11_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_66,negated_conjecture,
    ( esk9_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])).

cnf(c_0_68,negated_conjecture,
    ( esk11_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_66]),c_0_66]),c_0_66]),c_0_67])).

cnf(c_0_69,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_68]),c_0_68]),c_0_56]),c_0_68]),c_0_69]),c_0_67]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:17:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.20/0.39  # and selection function SelectNewComplexAHP.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.028 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t17_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>~((r2_hidden(X3,k2_relset_1(X1,X2,X4))&![X5]:~((r2_hidden(X5,X1)&k1_funct_1(X4,X5)=X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_funct_2)).
% 0.20/0.39  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.20/0.39  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 0.20/0.39  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.20/0.39  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.20/0.39  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.39  fof(t62_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k5_relat_1(k1_xboole_0,X1)=k1_xboole_0&k5_relat_1(X1,k1_xboole_0)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 0.20/0.39  fof(t6_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))=>~((r2_hidden(X1,X4)&![X5, X6]:~(((X1=k4_tarski(X5,X6)&r2_hidden(X5,X2))&r2_hidden(X6,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_relset_1)).
% 0.20/0.39  fof(t10_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>~((X2!=k1_xboole_0&![X3]:(m1_subset_1(X3,X1)=>~(r2_hidden(X3,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_subset_1)).
% 0.20/0.39  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.20/0.39  fof(l35_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 0.20/0.39  fof(t25_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k2_relat_1(k5_relat_1(X3,X2)))=>r2_hidden(X1,k2_relat_1(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_funct_1)).
% 0.20/0.39  fof(t45_ordinal1, axiom, ![X1]:(((v1_relat_1(k1_xboole_0)&v5_relat_1(k1_xboole_0,X1))&v1_funct_1(k1_xboole_0))&v5_ordinal1(k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_ordinal1)).
% 0.20/0.39  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.20/0.39  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>~((r2_hidden(X3,k2_relset_1(X1,X2,X4))&![X5]:~((r2_hidden(X5,X1)&k1_funct_1(X4,X5)=X3)))))), inference(assume_negation,[status(cth)],[t17_funct_2])).
% 0.20/0.39  fof(c_0_15, plain, ![X42, X43, X44]:(~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))|k2_relset_1(X42,X43,X44)=k2_relat_1(X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.20/0.39  fof(c_0_16, negated_conjecture, ![X58]:(((v1_funct_1(esk11_0)&v1_funct_2(esk11_0,esk8_0,esk9_0))&m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0))))&(r2_hidden(esk10_0,k2_relset_1(esk8_0,esk9_0,esk11_0))&(~r2_hidden(X58,esk8_0)|k1_funct_1(esk11_0,X58)!=esk10_0))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])])).
% 0.20/0.39  fof(c_0_17, plain, ![X22, X23, X24, X26, X27, X28, X30]:((((r2_hidden(esk3_3(X22,X23,X24),k1_relat_1(X22))|~r2_hidden(X24,X23)|X23!=k2_relat_1(X22)|(~v1_relat_1(X22)|~v1_funct_1(X22)))&(X24=k1_funct_1(X22,esk3_3(X22,X23,X24))|~r2_hidden(X24,X23)|X23!=k2_relat_1(X22)|(~v1_relat_1(X22)|~v1_funct_1(X22))))&(~r2_hidden(X27,k1_relat_1(X22))|X26!=k1_funct_1(X22,X27)|r2_hidden(X26,X23)|X23!=k2_relat_1(X22)|(~v1_relat_1(X22)|~v1_funct_1(X22))))&((~r2_hidden(esk4_2(X22,X28),X28)|(~r2_hidden(X30,k1_relat_1(X22))|esk4_2(X22,X28)!=k1_funct_1(X22,X30))|X28=k2_relat_1(X22)|(~v1_relat_1(X22)|~v1_funct_1(X22)))&((r2_hidden(esk5_2(X22,X28),k1_relat_1(X22))|r2_hidden(esk4_2(X22,X28),X28)|X28=k2_relat_1(X22)|(~v1_relat_1(X22)|~v1_funct_1(X22)))&(esk4_2(X22,X28)=k1_funct_1(X22,esk5_2(X22,X28))|r2_hidden(esk4_2(X22,X28),X28)|X28=k2_relat_1(X22)|(~v1_relat_1(X22)|~v1_funct_1(X22)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.20/0.39  cnf(c_0_18, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.39  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  fof(c_0_20, plain, ![X36, X37, X38]:(~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))|v1_relat_1(X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.20/0.39  fof(c_0_21, plain, ![X51, X52, X53]:((((~v1_funct_2(X53,X51,X52)|X51=k1_relset_1(X51,X52,X53)|X52=k1_xboole_0|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))))&(X51!=k1_relset_1(X51,X52,X53)|v1_funct_2(X53,X51,X52)|X52=k1_xboole_0|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))))&((~v1_funct_2(X53,X51,X52)|X51=k1_relset_1(X51,X52,X53)|X51!=k1_xboole_0|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))))&(X51!=k1_relset_1(X51,X52,X53)|v1_funct_2(X53,X51,X52)|X51!=k1_xboole_0|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))))))&((~v1_funct_2(X53,X51,X52)|X53=k1_xboole_0|X51=k1_xboole_0|X52!=k1_xboole_0|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))))&(X53!=k1_xboole_0|v1_funct_2(X53,X51,X52)|X51=k1_xboole_0|X52!=k1_xboole_0|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.20/0.39  fof(c_0_22, plain, ![X39, X40, X41]:(~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))|k1_relset_1(X39,X40,X41)=k1_relat_1(X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.39  cnf(c_0_23, plain, (X1=k1_funct_1(X2,esk3_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.39  cnf(c_0_24, negated_conjecture, (r2_hidden(esk10_0,k2_relset_1(esk8_0,esk9_0,esk11_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  cnf(c_0_25, negated_conjecture, (k2_relset_1(esk8_0,esk9_0,esk11_0)=k2_relat_1(esk11_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.39  cnf(c_0_26, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.39  fof(c_0_27, plain, ![X21]:((k5_relat_1(k1_xboole_0,X21)=k1_xboole_0|~v1_relat_1(X21))&(k5_relat_1(X21,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X21))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_relat_1])])])).
% 0.20/0.39  fof(c_0_28, plain, ![X45, X46, X47, X48]:(((X45=k4_tarski(esk6_4(X45,X46,X47,X48),esk7_4(X45,X46,X47,X48))|~r2_hidden(X45,X48)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))))&(r2_hidden(esk6_4(X45,X46,X47,X48),X46)|~r2_hidden(X45,X48)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))))&(r2_hidden(esk7_4(X45,X46,X47,X48),X47)|~r2_hidden(X45,X48)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_relset_1])])])])).
% 0.20/0.39  fof(c_0_29, plain, ![X18, X19]:((m1_subset_1(esk2_2(X18,X19),X18)|X19=k1_xboole_0|~m1_subset_1(X19,k1_zfmisc_1(X18)))&(r2_hidden(esk2_2(X18,X19),X19)|X19=k1_xboole_0|~m1_subset_1(X19,k1_zfmisc_1(X18)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_subset_1])])])])])).
% 0.20/0.39  cnf(c_0_30, plain, (r2_hidden(esk3_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.39  cnf(c_0_31, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.39  cnf(c_0_32, negated_conjecture, (v1_funct_2(esk11_0,esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  cnf(c_0_33, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.39  cnf(c_0_34, plain, (k1_funct_1(X1,esk3_3(X1,k2_relat_1(X1),X2))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_23])).
% 0.20/0.39  cnf(c_0_35, negated_conjecture, (r2_hidden(esk10_0,k2_relat_1(esk11_0))), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.39  cnf(c_0_36, negated_conjecture, (v1_funct_1(esk11_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  cnf(c_0_37, negated_conjecture, (v1_relat_1(esk11_0)), inference(spm,[status(thm)],[c_0_26, c_0_19])).
% 0.20/0.39  fof(c_0_38, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:((((r2_hidden(X10,X7)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8))&(~r2_hidden(X10,X8)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8)))&(~r2_hidden(X11,X7)|r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k4_xboole_0(X7,X8)))&((~r2_hidden(esk1_3(X12,X13,X14),X14)|(~r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k4_xboole_0(X12,X13))&((r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))&(~r2_hidden(esk1_3(X12,X13,X14),X13)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.20/0.39  fof(c_0_39, plain, ![X16, X17]:((k4_xboole_0(k1_tarski(X16),X17)!=k1_xboole_0|r2_hidden(X16,X17))&(~r2_hidden(X16,X17)|k4_xboole_0(k1_tarski(X16),X17)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l35_zfmisc_1])])).
% 0.20/0.39  fof(c_0_40, plain, ![X32, X33, X34]:(~v1_relat_1(X33)|~v1_funct_1(X33)|(~v1_relat_1(X34)|~v1_funct_1(X34)|(~r2_hidden(X32,k2_relat_1(k5_relat_1(X34,X33)))|r2_hidden(X32,k2_relat_1(X33))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_funct_1])])])).
% 0.20/0.39  cnf(c_0_41, plain, (k5_relat_1(k1_xboole_0,X1)=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.39  fof(c_0_42, plain, ![X35]:(((v1_relat_1(k1_xboole_0)&v5_relat_1(k1_xboole_0,X35))&v1_funct_1(k1_xboole_0))&v5_ordinal1(k1_xboole_0)), inference(variable_rename,[status(thm)],[t45_ordinal1])).
% 0.20/0.39  cnf(c_0_43, plain, (r2_hidden(esk7_4(X1,X2,X3,X4),X3)|~r2_hidden(X1,X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.39  cnf(c_0_44, plain, (r2_hidden(esk2_2(X1,X2),X2)|X2=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.39  cnf(c_0_45, plain, (r2_hidden(esk3_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_30])).
% 0.20/0.39  cnf(c_0_46, negated_conjecture, (k1_relset_1(esk8_0,esk9_0,esk11_0)=esk8_0|esk9_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_19]), c_0_32])])).
% 0.20/0.39  cnf(c_0_47, negated_conjecture, (k1_relset_1(esk8_0,esk9_0,esk11_0)=k1_relat_1(esk11_0)), inference(spm,[status(thm)],[c_0_33, c_0_19])).
% 0.20/0.39  cnf(c_0_48, negated_conjecture, (~r2_hidden(X1,esk8_0)|k1_funct_1(esk11_0,X1)!=esk10_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  cnf(c_0_49, negated_conjecture, (k1_funct_1(esk11_0,esk3_3(esk11_0,k2_relat_1(esk11_0),esk10_0))=esk10_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_37])])).
% 0.20/0.39  cnf(c_0_50, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.39  cnf(c_0_51, plain, (k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.39  cnf(c_0_52, plain, (r2_hidden(X3,k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~r2_hidden(X3,k2_relat_1(k5_relat_1(X2,X1)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.39  cnf(c_0_53, negated_conjecture, (k5_relat_1(k1_xboole_0,esk11_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_41, c_0_37])).
% 0.20/0.39  cnf(c_0_54, plain, (v1_funct_1(k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.39  cnf(c_0_55, plain, (v1_relat_1(k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.39  cnf(c_0_56, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.20/0.39  cnf(c_0_57, negated_conjecture, (r2_hidden(esk7_4(X1,esk8_0,esk9_0,esk11_0),esk9_0)|~r2_hidden(X1,esk11_0)), inference(spm,[status(thm)],[c_0_43, c_0_19])).
% 0.20/0.39  cnf(c_0_58, negated_conjecture, (esk11_0=k1_xboole_0|r2_hidden(esk2_2(k2_zfmisc_1(esk8_0,esk9_0),esk11_0),esk11_0)), inference(spm,[status(thm)],[c_0_44, c_0_19])).
% 0.20/0.39  cnf(c_0_59, negated_conjecture, (r2_hidden(esk3_3(esk11_0,k2_relat_1(esk11_0),esk10_0),k1_relat_1(esk11_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_35]), c_0_36]), c_0_37])])).
% 0.20/0.39  cnf(c_0_60, negated_conjecture, (k1_relat_1(esk11_0)=esk8_0|esk9_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.39  cnf(c_0_61, negated_conjecture, (~r2_hidden(esk3_3(esk11_0,k2_relat_1(esk11_0),esk10_0),esk8_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.39  cnf(c_0_62, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_50])).
% 0.20/0.39  cnf(c_0_63, negated_conjecture, (k4_xboole_0(k1_tarski(esk10_0),k2_relat_1(esk11_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_51, c_0_35])).
% 0.20/0.39  cnf(c_0_64, negated_conjecture, (r2_hidden(X1,k2_relat_1(esk11_0))|~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), c_0_36]), c_0_55]), c_0_37]), c_0_56])])).
% 0.20/0.39  cnf(c_0_65, negated_conjecture, (esk11_0=k1_xboole_0|r2_hidden(esk7_4(esk2_2(k2_zfmisc_1(esk8_0,esk9_0),esk11_0),esk8_0,esk9_0,esk11_0),esk9_0)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.20/0.39  cnf(c_0_66, negated_conjecture, (esk9_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61])).
% 0.20/0.39  cnf(c_0_67, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])).
% 0.20/0.39  cnf(c_0_68, negated_conjecture, (esk11_0=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_66]), c_0_66]), c_0_66]), c_0_67])).
% 0.20/0.39  cnf(c_0_69, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.20/0.39  cnf(c_0_70, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_68]), c_0_68]), c_0_56]), c_0_68]), c_0_69]), c_0_67]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 71
% 0.20/0.39  # Proof object clause steps            : 43
% 0.20/0.39  # Proof object formula steps           : 28
% 0.20/0.39  # Proof object conjectures             : 27
% 0.20/0.39  # Proof object clause conjectures      : 24
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 21
% 0.20/0.39  # Proof object initial formulas used   : 14
% 0.20/0.39  # Proof object generating inferences   : 16
% 0.20/0.39  # Proof object simplifying inferences  : 30
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 14
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 42
% 0.20/0.39  # Removed in clause preprocessing      : 0
% 0.20/0.39  # Initial clauses in saturation        : 42
% 0.20/0.39  # Processed clauses                    : 136
% 0.20/0.39  # ...of these trivial                  : 3
% 0.20/0.39  # ...subsumed                          : 4
% 0.20/0.39  # ...remaining for further processing  : 129
% 0.20/0.39  # Other redundant clauses eliminated   : 12
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 0
% 0.20/0.39  # Backward-rewritten                   : 27
% 0.20/0.39  # Generated clauses                    : 160
% 0.20/0.39  # ...of the previous two non-trivial   : 164
% 0.20/0.39  # Contextual simplify-reflections      : 1
% 0.20/0.39  # Paramodulations                      : 148
% 0.20/0.39  # Factorizations                       : 2
% 0.20/0.39  # Equation resolutions                 : 12
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 50
% 0.20/0.39  #    Positive orientable unit clauses  : 12
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 1
% 0.20/0.39  #    Non-unit-clauses                  : 37
% 0.20/0.39  # Current number of unprocessed clauses: 109
% 0.20/0.39  # ...number of literals in the above   : 360
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 69
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 334
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 167
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 1
% 0.20/0.39  # Unit Clause-clause subsumption calls : 148
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 11
% 0.20/0.39  # BW rewrite match successes           : 4
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 5758
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.035 s
% 0.20/0.39  # System time              : 0.005 s
% 0.20/0.39  # Total time               : 0.040 s
% 0.20/0.39  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
