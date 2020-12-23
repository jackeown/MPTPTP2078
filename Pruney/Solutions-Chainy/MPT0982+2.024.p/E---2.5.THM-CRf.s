%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:02:06 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 418 expanded)
%              Number of clauses        :   55 ( 158 expanded)
%              Number of leaves         :   16 ( 101 expanded)
%              Depth                    :   12
%              Number of atoms          :  264 (2357 expanded)
%              Number of equality atoms :   76 ( 682 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t28_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X5] :
          ( ( v1_funct_1(X5)
            & v1_funct_2(X5,X2,X3)
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
         => ( ( k2_relset_1(X1,X3,k1_partfun1(X1,X2,X2,X3,X4,X5)) = X3
              & v2_funct_1(X5) )
           => ( X3 = k1_xboole_0
              | k2_relset_1(X1,X2,X4) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_funct_2)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(dt_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
        & m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t160_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k2_relat_1(k5_relat_1(X1,X2)) = k9_relat_1(X2,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(t147_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,X1),k9_relat_1(X2,k1_relat_1(X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_relat_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(t60_xboole_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_tarski(X1,X2)
        & r2_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

fof(t51_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( k2_relat_1(k5_relat_1(X2,X1)) = k2_relat_1(X1)
              & v2_funct_1(X1) )
           => r1_tarski(k1_relat_1(X1),k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_funct_1)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X5] :
            ( ( v1_funct_1(X5)
              & v1_funct_2(X5,X2,X3)
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
           => ( ( k2_relset_1(X1,X3,k1_partfun1(X1,X2,X2,X3,X4,X5)) = X3
                & v2_funct_1(X5) )
             => ( X3 = k1_xboole_0
                | k2_relset_1(X1,X2,X4) = X2 ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t28_funct_2])).

fof(c_0_17,plain,(
    ! [X48,X49,X50,X51,X52,X53] :
      ( ~ v1_funct_1(X52)
      | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))
      | ~ v1_funct_1(X53)
      | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))
      | k1_partfun1(X48,X49,X50,X51,X52,X53) = k5_relat_1(X52,X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

fof(c_0_18,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk1_0,esk2_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk2_0,esk3_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    & k2_relset_1(esk1_0,esk3_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk3_0,esk4_0,esk5_0)) = esk3_0
    & v2_funct_1(esk5_0)
    & esk3_0 != k1_xboole_0
    & k2_relset_1(esk1_0,esk2_0,esk4_0) != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_19,plain,(
    ! [X42,X43,X44,X45,X46,X47] :
      ( ( v1_funct_1(k1_partfun1(X42,X43,X44,X45,X46,X47))
        | ~ v1_funct_1(X46)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
        | ~ v1_funct_1(X47)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) )
      & ( m1_subset_1(k1_partfun1(X42,X43,X44,X45,X46,X47),k1_zfmisc_1(k2_zfmisc_1(X42,X45)))
        | ~ v1_funct_1(X46)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
        | ~ v1_funct_1(X47)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).

cnf(c_0_20,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,plain,(
    ! [X27,X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | v1_relat_1(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_24,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( k1_partfun1(X1,X2,esk2_0,esk3_0,X3,esk5_0) = k5_relat_1(X3,esk5_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_28,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X21)
      | ~ v1_relat_1(X22)
      | k2_relat_1(k5_relat_1(X21,X22)) = k9_relat_1(X22,k2_relat_1(X21)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t160_relat_1])])])).

cnf(c_0_29,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_30,plain,(
    ! [X36,X37,X38] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
      | k2_relset_1(X36,X37,X38) = k2_relat_1(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(k1_partfun1(X1,X2,esk2_0,esk3_0,X3,esk5_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_21]),c_0_22])])).

cnf(c_0_32,negated_conjecture,
    ( k1_partfun1(esk1_0,esk2_0,esk2_0,esk3_0,esk4_0,esk5_0) = k5_relat_1(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

cnf(c_0_33,negated_conjecture,
    ( k2_relset_1(esk1_0,esk3_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk3_0,esk4_0,esk5_0)) = esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_34,plain,(
    ! [X39,X40,X41] :
      ( ( ~ v1_funct_2(X41,X39,X40)
        | X39 = k1_relset_1(X39,X40,X41)
        | X40 = k1_xboole_0
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( X39 != k1_relset_1(X39,X40,X41)
        | v1_funct_2(X41,X39,X40)
        | X40 = k1_xboole_0
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( ~ v1_funct_2(X41,X39,X40)
        | X39 = k1_relset_1(X39,X40,X41)
        | X39 != k1_xboole_0
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( X39 != k1_relset_1(X39,X40,X41)
        | v1_funct_2(X41,X39,X40)
        | X39 != k1_xboole_0
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( ~ v1_funct_2(X41,X39,X40)
        | X41 = k1_xboole_0
        | X39 = k1_xboole_0
        | X40 != k1_xboole_0
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( X41 != k1_xboole_0
        | v1_funct_2(X41,X39,X40)
        | X39 = k1_xboole_0
        | X40 != k1_xboole_0
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_35,plain,(
    ! [X30,X31,X32] :
      ( ( v4_relat_1(X32,X30)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( v5_relat_1(X32,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_36,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | ~ r2_xboole_0(X7,X8) )
      & ( X7 != X8
        | ~ r2_xboole_0(X7,X8) )
      & ( ~ r1_tarski(X7,X8)
        | X7 = X8
        | r2_xboole_0(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

fof(c_0_37,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X18)
      | r1_tarski(k9_relat_1(X18,X17),k9_relat_1(X18,k1_relat_1(X18))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_relat_1])])).

cnf(c_0_38,plain,
    ( k2_relat_1(k5_relat_1(X1,X2)) = k9_relat_1(X2,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_26])).

cnf(c_0_40,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(k5_relat_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_26]),c_0_32]),c_0_27])])).

cnf(c_0_42,negated_conjecture,
    ( k2_relset_1(esk1_0,esk3_0,k5_relat_1(esk4_0,esk5_0)) = esk3_0 ),
    inference(rw,[status(thm)],[c_0_33,c_0_32])).

fof(c_0_43,plain,(
    ! [X33,X34,X35] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | k1_relset_1(X33,X34,X35) = k1_relat_1(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_44,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_2(esk5_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_46,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_47,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X20)
      | k2_relat_1(k7_relat_1(X20,X19)) = k9_relat_1(X20,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_48,plain,(
    ! [X23,X24] :
      ( ~ v1_relat_1(X24)
      | ~ v4_relat_1(X24,X23)
      | X24 = k7_relat_1(X24,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_49,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_50,plain,(
    ! [X11,X12] :
      ( ( ~ v5_relat_1(X12,X11)
        | r1_tarski(k2_relat_1(X12),X11)
        | ~ v1_relat_1(X12) )
      & ( ~ r1_tarski(k2_relat_1(X12),X11)
        | v5_relat_1(X12,X11)
        | ~ v1_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_51,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_52,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_53,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,k1_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_54,negated_conjecture,
    ( k2_relat_1(k5_relat_1(esk4_0,X1)) = k9_relat_1(X1,k2_relat_1(esk4_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_55,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_21])).

cnf(c_0_56,negated_conjecture,
    ( k2_relat_1(k5_relat_1(esk4_0,esk5_0)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_57,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_58,negated_conjecture,
    ( k1_relset_1(esk2_0,esk3_0,esk5_0) = esk2_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_21]),c_0_45])]),c_0_46])).

cnf(c_0_59,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_60,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_61,negated_conjecture,
    ( v4_relat_1(esk5_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_21])).

fof(c_0_62,plain,(
    ! [X9,X10] :
      ( ~ r1_tarski(X9,X10)
      | ~ r2_xboole_0(X10,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_xboole_1])])).

cnf(c_0_63,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_64,negated_conjecture,
    ( v5_relat_1(esk5_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_21])).

fof(c_0_65,plain,(
    ! [X25,X26] :
      ( ~ v1_relat_1(X25)
      | ~ v1_funct_1(X25)
      | ~ v1_relat_1(X26)
      | ~ v1_funct_1(X26)
      | k2_relat_1(k5_relat_1(X26,X25)) != k2_relat_1(X25)
      | ~ v2_funct_1(X25)
      | r1_tarski(k1_relat_1(X25),k2_relat_1(X26)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t51_funct_1])])])).

cnf(c_0_66,plain,
    ( k9_relat_1(X1,X2) = k9_relat_1(X1,k1_relat_1(X1))
    | r2_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,k1_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_67,negated_conjecture,
    ( k9_relat_1(esk5_0,k2_relat_1(esk4_0)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])).

cnf(c_0_68,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_21]),c_0_58])).

cnf(c_0_69,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk5_0,X1)) = k9_relat_1(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_55])).

cnf(c_0_70,negated_conjecture,
    ( k7_relat_1(esk5_0,esk2_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_55])])).

cnf(c_0_71,plain,
    ( ~ r1_tarski(X1,X2)
    | ~ r2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk5_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_55])])).

cnf(c_0_73,plain,
    ( r1_tarski(k1_relat_1(X1),k2_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k2_relat_1(k5_relat_1(X2,X1)) != k2_relat_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_74,negated_conjecture,
    ( v2_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_75,negated_conjecture,
    ( k9_relat_1(esk5_0,esk2_0) = esk3_0
    | r2_xboole_0(esk3_0,k9_relat_1(esk5_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68]),c_0_68]),c_0_55])])).

cnf(c_0_76,negated_conjecture,
    ( k9_relat_1(esk5_0,esk2_0) = k2_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_77,negated_conjecture,
    ( ~ r2_xboole_0(esk3_0,k2_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_78,negated_conjecture,
    ( v5_relat_1(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_26])).

cnf(c_0_79,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk4_0) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_80,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk4_0) = k2_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_26])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(esk2_0,k2_relat_1(esk4_0))
    | k2_relat_1(esk5_0) != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_56]),c_0_68]),c_0_74]),c_0_27]),c_0_22]),c_0_39]),c_0_55])])).

cnf(c_0_82,negated_conjecture,
    ( k2_relat_1(esk5_0) = esk3_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_76]),c_0_76]),c_0_77])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_78]),c_0_39])])).

cnf(c_0_84,negated_conjecture,
    ( k2_relat_1(esk4_0) != esk2_0 ),
    inference(rw,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(esk2_0,k2_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_82])])).

cnf(c_0_86,negated_conjecture,
    ( r2_xboole_0(k2_relat_1(esk4_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_83]),c_0_84])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_85]),c_0_86])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:48:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.13/0.37  # and selection function SelectNewComplexAHP.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.020 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t28_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X2,X3))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>((k2_relset_1(X1,X3,k1_partfun1(X1,X2,X2,X3,X4,X5))=X3&v2_funct_1(X5))=>(X3=k1_xboole_0|k2_relset_1(X1,X2,X4)=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_funct_2)).
% 0.13/0.37  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 0.13/0.37  fof(dt_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))&m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 0.13/0.37  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.13/0.37  fof(t160_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k2_relat_1(k5_relat_1(X1,X2))=k9_relat_1(X2,k2_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 0.13/0.37  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.13/0.37  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.13/0.37  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.13/0.37  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.13/0.37  fof(t147_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k9_relat_1(X2,X1),k9_relat_1(X2,k1_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_relat_1)).
% 0.13/0.37  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.13/0.37  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.13/0.37  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 0.13/0.37  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.13/0.37  fof(t60_xboole_1, axiom, ![X1, X2]:~((r1_tarski(X1,X2)&r2_xboole_0(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_xboole_1)).
% 0.13/0.37  fof(t51_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((k2_relat_1(k5_relat_1(X2,X1))=k2_relat_1(X1)&v2_funct_1(X1))=>r1_tarski(k1_relat_1(X1),k2_relat_1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_funct_1)).
% 0.13/0.37  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X2,X3))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>((k2_relset_1(X1,X3,k1_partfun1(X1,X2,X2,X3,X4,X5))=X3&v2_funct_1(X5))=>(X3=k1_xboole_0|k2_relset_1(X1,X2,X4)=X2))))), inference(assume_negation,[status(cth)],[t28_funct_2])).
% 0.13/0.37  fof(c_0_17, plain, ![X48, X49, X50, X51, X52, X53]:(~v1_funct_1(X52)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))|~v1_funct_1(X53)|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))|k1_partfun1(X48,X49,X50,X51,X52,X53)=k5_relat_1(X52,X53)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 0.13/0.37  fof(c_0_18, negated_conjecture, (((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk1_0,esk2_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk2_0,esk3_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))&((k2_relset_1(esk1_0,esk3_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk3_0,esk4_0,esk5_0))=esk3_0&v2_funct_1(esk5_0))&(esk3_0!=k1_xboole_0&k2_relset_1(esk1_0,esk2_0,esk4_0)!=esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.13/0.37  fof(c_0_19, plain, ![X42, X43, X44, X45, X46, X47]:((v1_funct_1(k1_partfun1(X42,X43,X44,X45,X46,X47))|(~v1_funct_1(X46)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))|~v1_funct_1(X47)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))))&(m1_subset_1(k1_partfun1(X42,X43,X44,X45,X46,X47),k1_zfmisc_1(k2_zfmisc_1(X42,X45)))|(~v1_funct_1(X46)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))|~v1_funct_1(X47)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).
% 0.13/0.37  cnf(c_0_20, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.37  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.37  cnf(c_0_22, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.37  fof(c_0_23, plain, ![X27, X28, X29]:(~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))|v1_relat_1(X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.13/0.37  cnf(c_0_24, plain, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.37  cnf(c_0_25, negated_conjecture, (k1_partfun1(X1,X2,esk2_0,esk3_0,X3,esk5_0)=k5_relat_1(X3,esk5_0)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])])).
% 0.13/0.37  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.37  cnf(c_0_27, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.37  fof(c_0_28, plain, ![X21, X22]:(~v1_relat_1(X21)|(~v1_relat_1(X22)|k2_relat_1(k5_relat_1(X21,X22))=k9_relat_1(X22,k2_relat_1(X21)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t160_relat_1])])])).
% 0.13/0.37  cnf(c_0_29, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.37  fof(c_0_30, plain, ![X36, X37, X38]:(~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))|k2_relset_1(X36,X37,X38)=k2_relat_1(X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.13/0.37  cnf(c_0_31, negated_conjecture, (m1_subset_1(k1_partfun1(X1,X2,esk2_0,esk3_0,X3,esk5_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_21]), c_0_22])])).
% 0.13/0.37  cnf(c_0_32, negated_conjecture, (k1_partfun1(esk1_0,esk2_0,esk2_0,esk3_0,esk4_0,esk5_0)=k5_relat_1(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])])).
% 0.13/0.37  cnf(c_0_33, negated_conjecture, (k2_relset_1(esk1_0,esk3_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk3_0,esk4_0,esk5_0))=esk3_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.37  fof(c_0_34, plain, ![X39, X40, X41]:((((~v1_funct_2(X41,X39,X40)|X39=k1_relset_1(X39,X40,X41)|X40=k1_xboole_0|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))&(X39!=k1_relset_1(X39,X40,X41)|v1_funct_2(X41,X39,X40)|X40=k1_xboole_0|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))))&((~v1_funct_2(X41,X39,X40)|X39=k1_relset_1(X39,X40,X41)|X39!=k1_xboole_0|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))&(X39!=k1_relset_1(X39,X40,X41)|v1_funct_2(X41,X39,X40)|X39!=k1_xboole_0|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))))&((~v1_funct_2(X41,X39,X40)|X41=k1_xboole_0|X39=k1_xboole_0|X40!=k1_xboole_0|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))&(X41!=k1_xboole_0|v1_funct_2(X41,X39,X40)|X39=k1_xboole_0|X40!=k1_xboole_0|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.13/0.37  fof(c_0_35, plain, ![X30, X31, X32]:((v4_relat_1(X32,X30)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))&(v5_relat_1(X32,X31)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.13/0.37  fof(c_0_36, plain, ![X7, X8]:(((r1_tarski(X7,X8)|~r2_xboole_0(X7,X8))&(X7!=X8|~r2_xboole_0(X7,X8)))&(~r1_tarski(X7,X8)|X7=X8|r2_xboole_0(X7,X8))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.13/0.37  fof(c_0_37, plain, ![X17, X18]:(~v1_relat_1(X18)|r1_tarski(k9_relat_1(X18,X17),k9_relat_1(X18,k1_relat_1(X18)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_relat_1])])).
% 0.13/0.37  cnf(c_0_38, plain, (k2_relat_1(k5_relat_1(X1,X2))=k9_relat_1(X2,k2_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.37  cnf(c_0_39, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_29, c_0_26])).
% 0.13/0.37  cnf(c_0_40, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.37  cnf(c_0_41, negated_conjecture, (m1_subset_1(k5_relat_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_26]), c_0_32]), c_0_27])])).
% 0.13/0.37  cnf(c_0_42, negated_conjecture, (k2_relset_1(esk1_0,esk3_0,k5_relat_1(esk4_0,esk5_0))=esk3_0), inference(rw,[status(thm)],[c_0_33, c_0_32])).
% 0.13/0.37  fof(c_0_43, plain, ![X33, X34, X35]:(~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|k1_relset_1(X33,X34,X35)=k1_relat_1(X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.13/0.37  cnf(c_0_44, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.37  cnf(c_0_45, negated_conjecture, (v1_funct_2(esk5_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.37  cnf(c_0_46, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.37  fof(c_0_47, plain, ![X19, X20]:(~v1_relat_1(X20)|k2_relat_1(k7_relat_1(X20,X19))=k9_relat_1(X20,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.13/0.37  fof(c_0_48, plain, ![X23, X24]:(~v1_relat_1(X24)|~v4_relat_1(X24,X23)|X24=k7_relat_1(X24,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.13/0.37  cnf(c_0_49, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.37  fof(c_0_50, plain, ![X11, X12]:((~v5_relat_1(X12,X11)|r1_tarski(k2_relat_1(X12),X11)|~v1_relat_1(X12))&(~r1_tarski(k2_relat_1(X12),X11)|v5_relat_1(X12,X11)|~v1_relat_1(X12))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.13/0.37  cnf(c_0_51, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.37  cnf(c_0_52, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.37  cnf(c_0_53, plain, (r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,k1_relat_1(X1)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.37  cnf(c_0_54, negated_conjecture, (k2_relat_1(k5_relat_1(esk4_0,X1))=k9_relat_1(X1,k2_relat_1(esk4_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.13/0.37  cnf(c_0_55, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_29, c_0_21])).
% 0.13/0.37  cnf(c_0_56, negated_conjecture, (k2_relat_1(k5_relat_1(esk4_0,esk5_0))=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 0.13/0.37  cnf(c_0_57, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.37  cnf(c_0_58, negated_conjecture, (k1_relset_1(esk2_0,esk3_0,esk5_0)=esk2_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_21]), c_0_45])]), c_0_46])).
% 0.13/0.37  cnf(c_0_59, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.13/0.37  cnf(c_0_60, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.13/0.37  cnf(c_0_61, negated_conjecture, (v4_relat_1(esk5_0,esk2_0)), inference(spm,[status(thm)],[c_0_49, c_0_21])).
% 0.13/0.37  fof(c_0_62, plain, ![X9, X10]:(~r1_tarski(X9,X10)|~r2_xboole_0(X10,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_xboole_1])])).
% 0.13/0.37  cnf(c_0_63, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.13/0.37  cnf(c_0_64, negated_conjecture, (v5_relat_1(esk5_0,esk3_0)), inference(spm,[status(thm)],[c_0_51, c_0_21])).
% 0.13/0.37  fof(c_0_65, plain, ![X25, X26]:(~v1_relat_1(X25)|~v1_funct_1(X25)|(~v1_relat_1(X26)|~v1_funct_1(X26)|(k2_relat_1(k5_relat_1(X26,X25))!=k2_relat_1(X25)|~v2_funct_1(X25)|r1_tarski(k1_relat_1(X25),k2_relat_1(X26))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t51_funct_1])])])).
% 0.13/0.37  cnf(c_0_66, plain, (k9_relat_1(X1,X2)=k9_relat_1(X1,k1_relat_1(X1))|r2_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,k1_relat_1(X1)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.13/0.37  cnf(c_0_67, negated_conjecture, (k9_relat_1(esk5_0,k2_relat_1(esk4_0))=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])).
% 0.13/0.37  cnf(c_0_68, negated_conjecture, (k1_relat_1(esk5_0)=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_21]), c_0_58])).
% 0.13/0.37  cnf(c_0_69, negated_conjecture, (k2_relat_1(k7_relat_1(esk5_0,X1))=k9_relat_1(esk5_0,X1)), inference(spm,[status(thm)],[c_0_59, c_0_55])).
% 0.13/0.37  cnf(c_0_70, negated_conjecture, (k7_relat_1(esk5_0,esk2_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_55])])).
% 0.13/0.37  cnf(c_0_71, plain, (~r1_tarski(X1,X2)|~r2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.13/0.37  cnf(c_0_72, negated_conjecture, (r1_tarski(k2_relat_1(esk5_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_55])])).
% 0.13/0.37  cnf(c_0_73, plain, (r1_tarski(k1_relat_1(X1),k2_relat_1(X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|k2_relat_1(k5_relat_1(X2,X1))!=k2_relat_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.13/0.37  cnf(c_0_74, negated_conjecture, (v2_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.37  cnf(c_0_75, negated_conjecture, (k9_relat_1(esk5_0,esk2_0)=esk3_0|r2_xboole_0(esk3_0,k9_relat_1(esk5_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68]), c_0_68]), c_0_55])])).
% 0.13/0.37  cnf(c_0_76, negated_conjecture, (k9_relat_1(esk5_0,esk2_0)=k2_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.13/0.37  cnf(c_0_77, negated_conjecture, (~r2_xboole_0(esk3_0,k2_relat_1(esk5_0))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.13/0.37  cnf(c_0_78, negated_conjecture, (v5_relat_1(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_51, c_0_26])).
% 0.13/0.37  cnf(c_0_79, negated_conjecture, (k2_relset_1(esk1_0,esk2_0,esk4_0)!=esk2_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.37  cnf(c_0_80, negated_conjecture, (k2_relset_1(esk1_0,esk2_0,esk4_0)=k2_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_40, c_0_26])).
% 0.13/0.37  cnf(c_0_81, negated_conjecture, (r1_tarski(esk2_0,k2_relat_1(esk4_0))|k2_relat_1(esk5_0)!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_56]), c_0_68]), c_0_74]), c_0_27]), c_0_22]), c_0_39]), c_0_55])])).
% 0.13/0.37  cnf(c_0_82, negated_conjecture, (k2_relat_1(esk5_0)=esk3_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_76]), c_0_76]), c_0_77])).
% 0.13/0.37  cnf(c_0_83, negated_conjecture, (r1_tarski(k2_relat_1(esk4_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_78]), c_0_39])])).
% 0.13/0.37  cnf(c_0_84, negated_conjecture, (k2_relat_1(esk4_0)!=esk2_0), inference(rw,[status(thm)],[c_0_79, c_0_80])).
% 0.13/0.37  cnf(c_0_85, negated_conjecture, (r1_tarski(esk2_0,k2_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_82])])).
% 0.13/0.37  cnf(c_0_86, negated_conjecture, (r2_xboole_0(k2_relat_1(esk4_0),esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_83]), c_0_84])).
% 0.13/0.37  cnf(c_0_87, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_85]), c_0_86])]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 88
% 0.13/0.37  # Proof object clause steps            : 55
% 0.13/0.37  # Proof object formula steps           : 33
% 0.13/0.37  # Proof object conjectures             : 41
% 0.13/0.37  # Proof object clause conjectures      : 38
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 25
% 0.13/0.37  # Proof object initial formulas used   : 16
% 0.13/0.37  # Proof object generating inferences   : 26
% 0.13/0.37  # Proof object simplifying inferences  : 42
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 18
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 37
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 37
% 0.13/0.37  # Processed clauses                    : 227
% 0.13/0.37  # ...of these trivial                  : 3
% 0.13/0.37  # ...subsumed                          : 38
% 0.13/0.37  # ...remaining for further processing  : 186
% 0.13/0.37  # Other redundant clauses eliminated   : 6
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 16
% 0.13/0.37  # Generated clauses                    : 313
% 0.13/0.37  # ...of the previous two non-trivial   : 306
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 307
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 6
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 127
% 0.13/0.37  #    Positive orientable unit clauses  : 66
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 6
% 0.13/0.37  #    Non-unit-clauses                  : 55
% 0.13/0.37  # Current number of unprocessed clauses: 151
% 0.13/0.37  # ...number of literals in the above   : 245
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 54
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 732
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 306
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 18
% 0.13/0.37  # Unit Clause-clause subsumption calls : 98
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 13
% 0.13/0.37  # BW rewrite match successes           : 5
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 8671
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.028 s
% 0.13/0.37  # System time              : 0.004 s
% 0.13/0.37  # Total time               : 0.032 s
% 0.13/0.37  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
