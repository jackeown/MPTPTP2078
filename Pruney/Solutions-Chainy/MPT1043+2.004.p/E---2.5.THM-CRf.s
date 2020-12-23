%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:08 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  108 (3081 expanded)
%              Number of clauses        :   76 (1256 expanded)
%              Number of leaves         :   16 ( 779 expanded)
%              Depth                    :   17
%              Number of atoms          :  281 (10139 expanded)
%              Number of equality atoms :   39 ( 610 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t159_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => r1_tarski(k5_partfun1(X1,X2,X3),k1_funct_2(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_funct_2)).

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

fof(t158_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( r2_hidden(X4,k5_partfun1(X1,X2,X3))
         => ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_2)).

fof(cc3_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_funct_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(t11_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( X2 = k1_xboole_0
         => X1 = k1_xboole_0 )
       => r2_hidden(X3,k1_funct_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_funct_2)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(fc2_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v1_xboole_0(X1)
        & v1_xboole_0(X2)
        & v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => v1_xboole_0(k5_partfun1(X1,X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_partfun1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t14_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
     => ( r1_tarski(k2_relat_1(X4),X2)
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => r1_tarski(k5_partfun1(X1,X2,X3),k1_funct_2(X1,X2)) ) ),
    inference(assume_negation,[status(cth)],[t159_funct_2])).

fof(c_0_17,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(X26))
      | v1_relat_1(X27) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_18,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    & ~ r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),k1_funct_2(esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_19,plain,(
    ! [X28,X29] : v1_relat_1(k2_zfmisc_1(X28,X29)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_20,plain,(
    ! [X42,X43,X44,X45] :
      ( ( v1_funct_1(X45)
        | ~ r2_hidden(X45,k5_partfun1(X42,X43,X44))
        | ~ v1_funct_1(X44)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) )
      & ( v1_funct_2(X45,X42,X43)
        | ~ r2_hidden(X45,k5_partfun1(X42,X43,X44))
        | ~ v1_funct_1(X44)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) )
      & ( m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
        | ~ r2_hidden(X45,k5_partfun1(X42,X43,X44))
        | ~ v1_funct_1(X44)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_funct_2])])])])).

fof(c_0_21,plain,(
    ! [X30,X31] :
      ( ~ v1_relat_1(X30)
      | ~ v1_funct_1(X30)
      | ~ m1_subset_1(X31,k1_zfmisc_1(X30))
      | v1_funct_1(X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_funct_1])])])).

cnf(c_0_22,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_27,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_28,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

fof(c_0_32,plain,(
    ! [X20] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X20)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_33,plain,(
    ! [X39,X40,X41] :
      ( ( X40 = k1_xboole_0
        | r2_hidden(X41,k1_funct_2(X39,X40))
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,X39,X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( X39 != k1_xboole_0
        | r2_hidden(X41,k1_funct_2(X39,X40))
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,X39,X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_funct_2])])])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_2(X1,esk3_0,esk4_0)
    | ~ r2_hidden(X1,k5_partfun1(esk3_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_23]),c_0_26])])).

cnf(c_0_35,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    | ~ r2_hidden(X1,k5_partfun1(esk3_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_23]),c_0_26])])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k5_partfun1(esk3_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_23]),c_0_26])])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_26]),c_0_31])])).

cnf(c_0_39,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_40,plain,(
    ! [X18,X19] :
      ( ( k2_zfmisc_1(X18,X19) != k1_xboole_0
        | X18 = k1_xboole_0
        | X19 = k1_xboole_0 )
      & ( X18 != k1_xboole_0
        | k2_zfmisc_1(X18,X19) = k1_xboole_0 )
      & ( X19 != k1_xboole_0
        | k2_zfmisc_1(X18,X19) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_41,plain,(
    ! [X21,X22] :
      ( ~ v1_xboole_0(X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(X21))
      | v1_xboole_0(X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,k1_funct_2(X3,X1))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( v1_funct_2(esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1),esk3_0,esk4_0)
    | r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    | r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_1(esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1))
    | r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_35])).

cnf(c_0_46,negated_conjecture,
    ( v1_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_47,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_50,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),X1)
    | r2_hidden(esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1),k1_funct_2(esk3_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( ~ r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),k1_funct_2(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_52,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_53,plain,(
    ! [X36,X37,X38] :
      ( v1_xboole_0(X36)
      | ~ v1_xboole_0(X37)
      | ~ v1_funct_1(X38)
      | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
      | v1_xboole_0(k5_partfun1(X36,X37,X38)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_partfun1])])])).

fof(c_0_54,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_55,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_39]),c_0_46])])).

cnf(c_0_56,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_47])).

fof(c_0_57,plain,(
    ! [X15] :
      ( ~ v1_xboole_0(X15)
      | X15 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_58,negated_conjecture,
    ( v1_xboole_0(esk5_0)
    | ~ v1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_23])).

cnf(c_0_59,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_60,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_61,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_62,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(k5_partfun1(X1,X2,X3))
    | ~ v1_xboole_0(X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_63,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_64,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | ~ r2_hidden(X1,k5_partfun1(k1_xboole_0,X2,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_65,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

fof(c_0_66,plain,(
    ! [X32,X33,X34,X35] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X34,X32)))
      | ~ r1_tarski(k2_relat_1(X35),X33)
      | m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X34,X33))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_relset_1])])).

fof(c_0_67,plain,(
    ! [X16,X17] :
      ( ( r1_tarski(X16,X17)
        | X16 != X17 )
      & ( r1_tarski(X17,X16)
        | X16 != X17 )
      & ( ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X17,X16)
        | X16 = X17 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_68,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_69,negated_conjecture,
    ( v1_xboole_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59]),c_0_60]),c_0_61])])).

cnf(c_0_70,plain,
    ( v1_xboole_0(k5_partfun1(X1,X2,k1_xboole_0))
    | v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_39]),c_0_46])])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_35])).

cnf(c_0_72,plain,
    ( m1_subset_1(esk1_1(k5_partfun1(k1_xboole_0,X1,k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | v1_xboole_0(k5_partfun1(k1_xboole_0,X1,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_73,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(k2_relat_1(X1),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_74,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_75,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_76,plain,
    ( v1_xboole_0(k5_partfun1(X1,k1_xboole_0,k1_xboole_0))
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_61])).

cnf(c_0_77,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_78,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_61])).

cnf(c_0_79,plain,
    ( v1_xboole_0(esk1_1(k5_partfun1(k1_xboole_0,X1,k1_xboole_0)))
    | v1_xboole_0(k5_partfun1(k1_xboole_0,X1,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_72]),c_0_61])])).

cnf(c_0_80,negated_conjecture,
    ( m1_subset_1(esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1),k1_zfmisc_1(k2_zfmisc_1(esk3_0,X2)))
    | r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),X1)
    | ~ r1_tarski(k2_relat_1(esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1)),X2) ),
    inference(spm,[status(thm)],[c_0_73,c_0_44])).

cnf(c_0_81,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_74])).

cnf(c_0_82,negated_conjecture,
    ( ~ r1_tarski(k5_partfun1(esk3_0,k1_xboole_0,k1_xboole_0),k1_funct_2(esk3_0,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_59]),c_0_59]),c_0_75])).

cnf(c_0_83,plain,
    ( k5_partfun1(X1,k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_76])).

cnf(c_0_84,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_39]),c_0_46])])).

cnf(c_0_85,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_86,plain,
    ( r1_tarski(esk1_1(k5_partfun1(k1_xboole_0,X1,k1_xboole_0)),X2)
    | v1_xboole_0(k5_partfun1(k1_xboole_0,X1,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_79])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1),k1_zfmisc_1(k2_zfmisc_1(esk3_0,k2_relat_1(esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1)))))
    | r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_88,negated_conjecture,
    ( v1_xboole_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_78])])).

cnf(c_0_89,plain,
    ( r2_hidden(X2,k1_funct_2(X1,X3))
    | X1 != k1_xboole_0
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_90,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_60])).

cnf(c_0_91,plain,
    ( v1_funct_2(esk1_1(k5_partfun1(X1,X2,k1_xboole_0)),X1,X2)
    | v1_xboole_0(k5_partfun1(X1,X2,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_65])).

cnf(c_0_92,plain,
    ( esk1_1(k5_partfun1(k1_xboole_0,X1,k1_xboole_0)) = k1_xboole_0
    | v1_xboole_0(k5_partfun1(k1_xboole_0,X1,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_93,negated_conjecture,
    ( r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),X1)
    | v1_xboole_0(esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1))
    | ~ v1_xboole_0(k2_zfmisc_1(esk3_0,k2_relat_1(esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1)))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_87])).

cnf(c_0_94,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_68,c_0_88])).

cnf(c_0_95,plain,
    ( r2_hidden(X1,k1_funct_2(k1_xboole_0,X2))
    | ~ v1_funct_2(X1,k1_xboole_0,X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_89]),c_0_56])).

cnf(c_0_96,negated_conjecture,
    ( v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_46]),c_0_90])])).

cnf(c_0_97,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X1)
    | v1_xboole_0(k5_partfun1(k1_xboole_0,X1,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_98,negated_conjecture,
    ( r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1)
    | v1_xboole_0(esk2_2(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_59]),c_0_59]),c_0_59]),c_0_94]),c_0_75]),c_0_94]),c_0_75]),c_0_94]),c_0_94]),c_0_75]),c_0_56]),c_0_61])])).

cnf(c_0_99,plain,
    ( r2_hidden(X1,k1_funct_2(k1_xboole_0,X2))
    | ~ v1_funct_2(X1,k1_xboole_0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(csr,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_100,negated_conjecture,
    ( ~ r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_94]),c_0_94])).

cnf(c_0_101,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X1)
    | r1_tarski(k5_partfun1(k1_xboole_0,X1,k1_xboole_0),X2) ),
    inference(spm,[status(thm)],[c_0_71,c_0_97])).

cnf(c_0_102,negated_conjecture,
    ( esk2_2(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1) = k1_xboole_0
    | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_98])).

cnf(c_0_103,plain,
    ( r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,X1))
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_99,c_0_39])).

cnf(c_0_104,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_105,negated_conjecture,
    ( r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1)
    | ~ r2_hidden(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_102])).

cnf(c_0_106,negated_conjecture,
    ( r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_107,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_100]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:38:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S049N
% 0.20/0.39  # and selection function PSelectComplexPreferEQ.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.028 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t159_funct_2, conjecture, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>r1_tarski(k5_partfun1(X1,X2,X3),k1_funct_2(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t159_funct_2)).
% 0.20/0.39  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.20/0.39  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.20/0.39  fof(t158_funct_2, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(r2_hidden(X4,k5_partfun1(X1,X2,X3))=>((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_2)).
% 0.20/0.39  fof(cc3_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_funct_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_funct_1)).
% 0.20/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.39  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.20/0.39  fof(t11_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0=>X1=k1_xboole_0)=>r2_hidden(X3,k1_funct_2(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_funct_2)).
% 0.20/0.39  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.20/0.39  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.20/0.39  fof(fc2_partfun1, axiom, ![X1, X2, X3]:((((~(v1_xboole_0(X1))&v1_xboole_0(X2))&v1_funct_1(X3))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>v1_xboole_0(k5_partfun1(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_partfun1)).
% 0.20/0.39  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.39  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.20/0.39  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.39  fof(t14_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>(r1_tarski(k2_relat_1(X4),X2)=>m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relset_1)).
% 0.20/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.39  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>r1_tarski(k5_partfun1(X1,X2,X3),k1_funct_2(X1,X2)))), inference(assume_negation,[status(cth)],[t159_funct_2])).
% 0.20/0.39  fof(c_0_17, plain, ![X26, X27]:(~v1_relat_1(X26)|(~m1_subset_1(X27,k1_zfmisc_1(X26))|v1_relat_1(X27))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.20/0.39  fof(c_0_18, negated_conjecture, ((v1_funct_1(esk5_0)&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))))&~r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),k1_funct_2(esk3_0,esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.20/0.39  fof(c_0_19, plain, ![X28, X29]:v1_relat_1(k2_zfmisc_1(X28,X29)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.20/0.39  fof(c_0_20, plain, ![X42, X43, X44, X45]:(((v1_funct_1(X45)|~r2_hidden(X45,k5_partfun1(X42,X43,X44))|(~v1_funct_1(X44)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))))&(v1_funct_2(X45,X42,X43)|~r2_hidden(X45,k5_partfun1(X42,X43,X44))|(~v1_funct_1(X44)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))))))&(m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))|~r2_hidden(X45,k5_partfun1(X42,X43,X44))|(~v1_funct_1(X44)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_funct_2])])])])).
% 0.20/0.39  fof(c_0_21, plain, ![X30, X31]:(~v1_relat_1(X30)|~v1_funct_1(X30)|(~m1_subset_1(X31,k1_zfmisc_1(X30))|v1_funct_1(X31))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_funct_1])])])).
% 0.20/0.39  cnf(c_0_22, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.39  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_24, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.39  cnf(c_0_25, plain, (v1_funct_2(X1,X2,X3)|~r2_hidden(X1,k5_partfun1(X2,X3,X4))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.39  cnf(c_0_26, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  fof(c_0_27, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.39  cnf(c_0_28, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X1,k5_partfun1(X2,X3,X4))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.39  cnf(c_0_29, plain, (v1_funct_1(X1)|~r2_hidden(X1,k5_partfun1(X2,X3,X4))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.39  cnf(c_0_30, plain, (v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.39  cnf(c_0_31, negated_conjecture, (v1_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 0.20/0.39  fof(c_0_32, plain, ![X20]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X20)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.20/0.39  fof(c_0_33, plain, ![X39, X40, X41]:((X40=k1_xboole_0|r2_hidden(X41,k1_funct_2(X39,X40))|(~v1_funct_1(X41)|~v1_funct_2(X41,X39,X40)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))))&(X39!=k1_xboole_0|r2_hidden(X41,k1_funct_2(X39,X40))|(~v1_funct_1(X41)|~v1_funct_2(X41,X39,X40)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_funct_2])])])).
% 0.20/0.39  cnf(c_0_34, negated_conjecture, (v1_funct_2(X1,esk3_0,esk4_0)|~r2_hidden(X1,k5_partfun1(esk3_0,esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_23]), c_0_26])])).
% 0.20/0.39  cnf(c_0_35, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.39  cnf(c_0_36, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))|~r2_hidden(X1,k5_partfun1(esk3_0,esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_23]), c_0_26])])).
% 0.20/0.39  cnf(c_0_37, negated_conjecture, (v1_funct_1(X1)|~r2_hidden(X1,k5_partfun1(esk3_0,esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_23]), c_0_26])])).
% 0.20/0.39  cnf(c_0_38, negated_conjecture, (v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_26]), c_0_31])])).
% 0.20/0.39  cnf(c_0_39, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.39  fof(c_0_40, plain, ![X18, X19]:((k2_zfmisc_1(X18,X19)!=k1_xboole_0|(X18=k1_xboole_0|X19=k1_xboole_0))&((X18!=k1_xboole_0|k2_zfmisc_1(X18,X19)=k1_xboole_0)&(X19!=k1_xboole_0|k2_zfmisc_1(X18,X19)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.20/0.39  fof(c_0_41, plain, ![X21, X22]:(~v1_xboole_0(X21)|(~m1_subset_1(X22,k1_zfmisc_1(X21))|v1_xboole_0(X22))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.20/0.39  cnf(c_0_42, plain, (X1=k1_xboole_0|r2_hidden(X2,k1_funct_2(X3,X1))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.39  cnf(c_0_43, negated_conjecture, (v1_funct_2(esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1),esk3_0,esk4_0)|r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.39  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))|r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),X1)), inference(spm,[status(thm)],[c_0_36, c_0_35])).
% 0.20/0.39  cnf(c_0_45, negated_conjecture, (v1_funct_1(esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1))|r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),X1)), inference(spm,[status(thm)],[c_0_37, c_0_35])).
% 0.20/0.39  cnf(c_0_46, negated_conjecture, (v1_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.39  cnf(c_0_47, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.39  cnf(c_0_48, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.39  cnf(c_0_49, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.39  cnf(c_0_50, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),X1)|r2_hidden(esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1),k1_funct_2(esk3_0,esk4_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_45])).
% 0.20/0.39  cnf(c_0_51, negated_conjecture, (~r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),k1_funct_2(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_52, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.39  fof(c_0_53, plain, ![X36, X37, X38]:(v1_xboole_0(X36)|~v1_xboole_0(X37)|~v1_funct_1(X38)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))|v1_xboole_0(k5_partfun1(X36,X37,X38))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_partfun1])])])).
% 0.20/0.39  fof(c_0_54, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.39  cnf(c_0_55, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X1,k5_partfun1(X2,X3,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_39]), c_0_46])])).
% 0.20/0.39  cnf(c_0_56, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_47])).
% 0.20/0.39  fof(c_0_57, plain, ![X15]:(~v1_xboole_0(X15)|X15=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.20/0.39  cnf(c_0_58, negated_conjecture, (v1_xboole_0(esk5_0)|~v1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_48, c_0_23])).
% 0.20/0.39  cnf(c_0_59, negated_conjecture, (esk4_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])).
% 0.20/0.39  cnf(c_0_60, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_52])).
% 0.20/0.39  cnf(c_0_61, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.39  cnf(c_0_62, plain, (v1_xboole_0(X1)|v1_xboole_0(k5_partfun1(X1,X2,X3))|~v1_xboole_0(X2)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.20/0.39  cnf(c_0_63, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.39  cnf(c_0_64, plain, (m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))|~r2_hidden(X1,k5_partfun1(k1_xboole_0,X2,k1_xboole_0))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.20/0.39  cnf(c_0_65, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.39  fof(c_0_66, plain, ![X32, X33, X34, X35]:(~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X34,X32)))|(~r1_tarski(k2_relat_1(X35),X33)|m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X34,X33))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_relset_1])])).
% 0.20/0.39  fof(c_0_67, plain, ![X16, X17]:(((r1_tarski(X16,X17)|X16!=X17)&(r1_tarski(X17,X16)|X16!=X17))&(~r1_tarski(X16,X17)|~r1_tarski(X17,X16)|X16=X17)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.39  cnf(c_0_68, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.20/0.39  cnf(c_0_69, negated_conjecture, (v1_xboole_0(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59]), c_0_60]), c_0_61])])).
% 0.20/0.39  cnf(c_0_70, plain, (v1_xboole_0(k5_partfun1(X1,X2,k1_xboole_0))|v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_39]), c_0_46])])).
% 0.20/0.39  cnf(c_0_71, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_63, c_0_35])).
% 0.20/0.39  cnf(c_0_72, plain, (m1_subset_1(esk1_1(k5_partfun1(k1_xboole_0,X1,k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))|v1_xboole_0(k5_partfun1(k1_xboole_0,X1,k1_xboole_0))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.20/0.39  cnf(c_0_73, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(k2_relat_1(X1),X4)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.20/0.39  cnf(c_0_74, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.20/0.39  cnf(c_0_75, negated_conjecture, (esk5_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.20/0.39  cnf(c_0_76, plain, (v1_xboole_0(k5_partfun1(X1,k1_xboole_0,k1_xboole_0))|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_70, c_0_61])).
% 0.20/0.39  cnf(c_0_77, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.20/0.39  cnf(c_0_78, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_71, c_0_61])).
% 0.20/0.39  cnf(c_0_79, plain, (v1_xboole_0(esk1_1(k5_partfun1(k1_xboole_0,X1,k1_xboole_0)))|v1_xboole_0(k5_partfun1(k1_xboole_0,X1,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_72]), c_0_61])])).
% 0.20/0.39  cnf(c_0_80, negated_conjecture, (m1_subset_1(esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1),k1_zfmisc_1(k2_zfmisc_1(esk3_0,X2)))|r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),X1)|~r1_tarski(k2_relat_1(esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1)),X2)), inference(spm,[status(thm)],[c_0_73, c_0_44])).
% 0.20/0.39  cnf(c_0_81, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_74])).
% 0.20/0.39  cnf(c_0_82, negated_conjecture, (~r1_tarski(k5_partfun1(esk3_0,k1_xboole_0,k1_xboole_0),k1_funct_2(esk3_0,k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_59]), c_0_59]), c_0_75])).
% 0.20/0.39  cnf(c_0_83, plain, (k5_partfun1(X1,k1_xboole_0,k1_xboole_0)=k1_xboole_0|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_68, c_0_76])).
% 0.20/0.39  cnf(c_0_84, plain, (v1_funct_2(X1,X2,X3)|~r2_hidden(X1,k5_partfun1(X2,X3,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_39]), c_0_46])])).
% 0.20/0.39  cnf(c_0_85, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.20/0.39  cnf(c_0_86, plain, (r1_tarski(esk1_1(k5_partfun1(k1_xboole_0,X1,k1_xboole_0)),X2)|v1_xboole_0(k5_partfun1(k1_xboole_0,X1,k1_xboole_0))), inference(spm,[status(thm)],[c_0_71, c_0_79])).
% 0.20/0.39  cnf(c_0_87, negated_conjecture, (m1_subset_1(esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1),k1_zfmisc_1(k2_zfmisc_1(esk3_0,k2_relat_1(esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1)))))|r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),X1)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.20/0.39  cnf(c_0_88, negated_conjecture, (v1_xboole_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_78])])).
% 0.20/0.39  cnf(c_0_89, plain, (r2_hidden(X2,k1_funct_2(X1,X3))|X1!=k1_xboole_0|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.39  cnf(c_0_90, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_24, c_0_60])).
% 0.20/0.39  cnf(c_0_91, plain, (v1_funct_2(esk1_1(k5_partfun1(X1,X2,k1_xboole_0)),X1,X2)|v1_xboole_0(k5_partfun1(X1,X2,k1_xboole_0))), inference(spm,[status(thm)],[c_0_84, c_0_65])).
% 0.20/0.39  cnf(c_0_92, plain, (esk1_1(k5_partfun1(k1_xboole_0,X1,k1_xboole_0))=k1_xboole_0|v1_xboole_0(k5_partfun1(k1_xboole_0,X1,k1_xboole_0))), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.20/0.39  cnf(c_0_93, negated_conjecture, (r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),X1)|v1_xboole_0(esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1))|~v1_xboole_0(k2_zfmisc_1(esk3_0,k2_relat_1(esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1))))), inference(spm,[status(thm)],[c_0_48, c_0_87])).
% 0.20/0.39  cnf(c_0_94, negated_conjecture, (esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_68, c_0_88])).
% 0.20/0.39  cnf(c_0_95, plain, (r2_hidden(X1,k1_funct_2(k1_xboole_0,X2))|~v1_funct_2(X1,k1_xboole_0,X2)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_89]), c_0_56])).
% 0.20/0.39  cnf(c_0_96, negated_conjecture, (v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_46]), c_0_90])])).
% 0.20/0.39  cnf(c_0_97, plain, (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)|v1_xboole_0(k5_partfun1(k1_xboole_0,X1,k1_xboole_0))), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.20/0.39  cnf(c_0_98, negated_conjecture, (r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1)|v1_xboole_0(esk2_2(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_59]), c_0_59]), c_0_59]), c_0_94]), c_0_75]), c_0_94]), c_0_75]), c_0_94]), c_0_94]), c_0_75]), c_0_56]), c_0_61])])).
% 0.20/0.39  cnf(c_0_99, plain, (r2_hidden(X1,k1_funct_2(k1_xboole_0,X2))|~v1_funct_2(X1,k1_xboole_0,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(csr,[status(thm)],[c_0_95, c_0_96])).
% 0.20/0.39  cnf(c_0_100, negated_conjecture, (~r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_94]), c_0_94])).
% 0.20/0.39  cnf(c_0_101, plain, (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)|r1_tarski(k5_partfun1(k1_xboole_0,X1,k1_xboole_0),X2)), inference(spm,[status(thm)],[c_0_71, c_0_97])).
% 0.20/0.39  cnf(c_0_102, negated_conjecture, (esk2_2(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1)=k1_xboole_0|r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_68, c_0_98])).
% 0.20/0.39  cnf(c_0_103, plain, (r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,X1))|~v1_funct_2(k1_xboole_0,k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_99, c_0_39])).
% 0.20/0.39  cnf(c_0_104, negated_conjecture, (v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_100, c_0_101])).
% 0.20/0.39  cnf(c_0_105, negated_conjecture, (r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1)|~r2_hidden(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_49, c_0_102])).
% 0.20/0.39  cnf(c_0_106, negated_conjecture, (r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 0.20/0.39  cnf(c_0_107, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_100]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 108
% 0.20/0.39  # Proof object clause steps            : 76
% 0.20/0.39  # Proof object formula steps           : 32
% 0.20/0.39  # Proof object conjectures             : 34
% 0.20/0.39  # Proof object clause conjectures      : 31
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 25
% 0.20/0.39  # Proof object initial formulas used   : 16
% 0.20/0.39  # Proof object generating inferences   : 42
% 0.20/0.39  # Proof object simplifying inferences  : 54
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 17
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 29
% 0.20/0.39  # Removed in clause preprocessing      : 0
% 0.20/0.39  # Initial clauses in saturation        : 29
% 0.20/0.39  # Processed clauses                    : 362
% 0.20/0.39  # ...of these trivial                  : 8
% 0.20/0.39  # ...subsumed                          : 122
% 0.20/0.39  # ...remaining for further processing  : 232
% 0.20/0.39  # Other redundant clauses eliminated   : 7
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 2
% 0.20/0.39  # Backward-rewritten                   : 90
% 0.20/0.39  # Generated clauses                    : 713
% 0.20/0.39  # ...of the previous two non-trivial   : 511
% 0.20/0.39  # Contextual simplify-reflections      : 24
% 0.20/0.39  # Paramodulations                      : 694
% 0.20/0.39  # Factorizations                       : 12
% 0.20/0.39  # Equation resolutions                 : 7
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
% 0.20/0.39  # Current number of processed clauses  : 107
% 0.20/0.39  #    Positive orientable unit clauses  : 16
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 3
% 0.20/0.39  #    Non-unit-clauses                  : 88
% 0.20/0.39  # Current number of unprocessed clauses: 196
% 0.20/0.39  # ...number of literals in the above   : 681
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 120
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 3785
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 2300
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 147
% 0.20/0.39  # Unit Clause-clause subsumption calls : 332
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 13
% 0.20/0.39  # BW rewrite match successes           : 5
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 15089
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.053 s
% 0.20/0.39  # System time              : 0.005 s
% 0.20/0.39  # Total time               : 0.058 s
% 0.20/0.39  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
