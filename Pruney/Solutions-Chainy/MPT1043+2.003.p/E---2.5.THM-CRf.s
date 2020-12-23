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
% DateTime   : Thu Dec  3 11:07:08 EST 2020

% Result     : Theorem 0.69s
% Output     : CNFRefutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :  128 (10348 expanded)
%              Number of clauses        :   94 (4817 expanded)
%              Number of leaves         :   17 (2507 expanded)
%              Depth                    :   20
%              Number of atoms          :  383 (32006 expanded)
%              Number of equality atoms :   49 (2454 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t159_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => r1_tarski(k5_partfun1(X1,X2,X3),k1_funct_2(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_funct_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(fc2_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v1_xboole_0(X1)
        & v1_xboole_0(X2)
        & v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => v1_xboole_0(k5_partfun1(X1,X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_partfun1)).

fof(t158_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( r2_hidden(X4,k5_partfun1(X1,X2,X3))
         => ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_2)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(t11_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( X2 = k1_xboole_0
         => X1 = k1_xboole_0 )
       => r2_hidden(X3,k1_funct_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_funct_2)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => r1_tarski(k5_partfun1(X1,X2,X3),k1_funct_2(X1,X2)) ) ),
    inference(assume_negation,[status(cth)],[t159_funct_2])).

fof(c_0_18,plain,(
    ! [X21,X22] :
      ( ( ~ m1_subset_1(X21,k1_zfmisc_1(X22))
        | r1_tarski(X21,X22) )
      & ( ~ r1_tarski(X21,X22)
        | m1_subset_1(X21,k1_zfmisc_1(X22)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_19,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    & ~ r1_tarski(k5_partfun1(esk2_0,esk3_0,esk4_0),k1_funct_2(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_20,plain,(
    ! [X26,X27,X28] :
      ( ~ r2_hidden(X26,X27)
      | ~ m1_subset_1(X27,k1_zfmisc_1(X28))
      | ~ v1_xboole_0(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_21,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(X13,X14)
      | ~ r1_tarski(X14,X15)
      | r1_tarski(X13,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_26,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_27,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_28,plain,(
    ! [X37,X38,X39] :
      ( ~ v1_xboole_0(X37)
      | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X38,X37)))
      | v1_xboole_0(X39) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(esk4_0,k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X3)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(X1,k2_zfmisc_1(esk2_0,esk3_0))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_33])).

fof(c_0_39,plain,(
    ! [X29,X30] :
      ( ( ~ v4_relat_1(X30,X29)
        | r1_tarski(k1_relat_1(X30),X29)
        | ~ v1_relat_1(X30) )
      & ( ~ r1_tarski(k1_relat_1(X30),X29)
        | v4_relat_1(X30,X29)
        | ~ v1_relat_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

fof(c_0_40,plain,(
    ! [X34,X35,X36] :
      ( ( v4_relat_1(X36,X34)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( v5_relat_1(X36,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_41,plain,(
    ! [X31,X32,X33] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | v1_relat_1(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_42,plain,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(X2)
    | ~ r1_tarski(X1,k2_zfmisc_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_25])).

cnf(c_0_43,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk3_0) = X1
    | ~ r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),X1)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_48,plain,(
    ! [X40,X41,X42] :
      ( v1_xboole_0(X40)
      | ~ v1_xboole_0(X41)
      | ~ v1_funct_1(X42)
      | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
      | v1_xboole_0(k5_partfun1(X40,X41,X42)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_partfun1])])])).

cnf(c_0_49,negated_conjecture,
    ( ~ r1_tarski(k5_partfun1(esk2_0,esk3_0,esk4_0),k1_funct_2(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | ~ v1_xboole_0(k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_30])).

cnf(c_0_51,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_38])).

cnf(c_0_52,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk3_0) = X1
    | ~ v1_xboole_0(k2_zfmisc_1(esk2_0,esk3_0))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_53,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_37,c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( v4_relat_1(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_23])).

cnf(c_0_55,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_23])).

cnf(c_0_56,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(k5_partfun1(X1,X2,X3))
    | ~ v1_xboole_0(X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_57,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_58,negated_conjecture,
    ( ~ v1_xboole_0(k5_partfun1(esk2_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_44])).

cnf(c_0_59,plain,
    ( v4_relat_1(X1,X2)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_25])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_61,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk3_0) = X1
    | ~ v1_xboole_0(esk3_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_51])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk4_0),X1)
    | ~ v1_xboole_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])])).

cnf(c_0_63,negated_conjecture,
    ( v1_xboole_0(esk2_0)
    | ~ v1_xboole_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_23]),c_0_57])]),c_0_58])).

fof(c_0_64,plain,(
    ! [X46,X47,X48,X49] :
      ( ( v1_funct_1(X49)
        | ~ r2_hidden(X49,k5_partfun1(X46,X47,X48))
        | ~ v1_funct_1(X48)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) )
      & ( v1_funct_2(X49,X46,X47)
        | ~ r2_hidden(X49,k5_partfun1(X46,X47,X48))
        | ~ v1_funct_1(X48)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) )
      & ( m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))
        | ~ r2_hidden(X49,k5_partfun1(X46,X47,X48))
        | ~ v1_funct_1(X48)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_funct_2])])])])).

fof(c_0_65,plain,(
    ! [X18,X19] :
      ( ( ~ m1_subset_1(X19,X18)
        | r2_hidden(X19,X18)
        | v1_xboole_0(X18) )
      & ( ~ r2_hidden(X19,X18)
        | m1_subset_1(X19,X18)
        | v1_xboole_0(X18) )
      & ( ~ m1_subset_1(X19,X18)
        | v1_xboole_0(X19)
        | ~ v1_xboole_0(X18) )
      & ( ~ v1_xboole_0(X19)
        | m1_subset_1(X19,X18)
        | ~ v1_xboole_0(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_66,negated_conjecture,
    ( v4_relat_1(esk4_0,X1)
    | ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk3_0) = k1_relat_1(esk4_0)
    | ~ v1_xboole_0(esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])).

cnf(c_0_68,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk4_0),X1)
    | ~ v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_66]),c_0_55])])).

cnf(c_0_71,negated_conjecture,
    ( v1_xboole_0(k1_relat_1(esk4_0))
    | ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_67])).

fof(c_0_72,plain,(
    ! [X43,X44,X45] :
      ( ( X44 = k1_xboole_0
        | r2_hidden(X45,k1_funct_2(X43,X44))
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,X43,X44)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) )
      & ( X43 != k1_xboole_0
        | r2_hidden(X45,k1_funct_2(X43,X44))
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,X43,X44)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_funct_2])])])).

cnf(c_0_73,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | v1_xboole_0(k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k5_partfun1(X2,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(X1,k2_zfmisc_1(esk2_0,esk3_0))
    | ~ r1_tarski(X2,esk4_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_36])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk4_0),X1)
    | ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_76,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_44])).

cnf(c_0_77,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,k1_funct_2(X3,X1))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    | ~ m1_subset_1(X1,k5_partfun1(esk2_0,esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_23]),c_0_57])]),c_0_58])).

cnf(c_0_79,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

fof(c_0_80,plain,(
    ! [X20] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X20)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(X1,k2_zfmisc_1(esk2_0,esk3_0))
    | ~ v1_xboole_0(esk3_0)
    | ~ r1_tarski(X1,k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_82,plain,
    ( k1_relat_1(X1) = X2
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_76,c_0_45])).

cnf(c_0_83,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_84,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,k1_funct_2(X3,X1))
    | ~ v1_funct_2(X2,X3,X1)
    | ~ v1_funct_1(X2)
    | ~ r1_tarski(X2,k2_zfmisc_1(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_25])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(X1,k2_zfmisc_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k5_partfun1(esk2_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_78])).

cnf(c_0_86,plain,
    ( m1_subset_1(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_32]),c_0_44])).

cnf(c_0_87,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_88,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk3_0) = esk4_0
    | ~ r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_30])).

cnf(c_0_89,negated_conjecture,
    ( X1 = k2_zfmisc_1(esk2_0,esk3_0)
    | ~ v1_xboole_0(esk3_0)
    | ~ r1_tarski(X1,k1_relat_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_81]),c_0_51])).

cnf(c_0_90,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk2_0
    | ~ v1_xboole_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_54]),c_0_55])])).

cnf(c_0_91,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(X2,k1_funct_2(X3,X1))
    | ~ v1_funct_2(esk1_2(X2,k1_funct_2(X3,X1)),X3,X1)
    | ~ v1_funct_1(esk1_2(X2,k1_funct_2(X3,X1)))
    | ~ r1_tarski(esk1_2(X2,k1_funct_2(X3,X1)),k2_zfmisc_1(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(esk1_2(k5_partfun1(esk2_0,esk3_0,esk4_0),X1),k2_zfmisc_1(esk2_0,esk3_0))
    | r1_tarski(k5_partfun1(esk2_0,esk3_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_93,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

fof(c_0_94,plain,(
    ! [X16,X17] :
      ( ( k2_zfmisc_1(X16,X17) != k1_xboole_0
        | X16 = k1_xboole_0
        | X17 = k1_xboole_0 )
      & ( X16 != k1_xboole_0
        | k2_zfmisc_1(X16,X17) = k1_xboole_0 )
      & ( X17 != k1_xboole_0
        | k2_zfmisc_1(X16,X17) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_95,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_87])).

cnf(c_0_96,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk3_0) = esk4_0
    | ~ v1_xboole_0(k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_44])).

cnf(c_0_97,negated_conjecture,
    ( X1 = k2_zfmisc_1(esk2_0,esk3_0)
    | ~ v1_xboole_0(esk3_0)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_63])).

cnf(c_0_98,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ v1_funct_2(esk1_2(k5_partfun1(esk2_0,esk3_0,esk4_0),k1_funct_2(esk2_0,esk3_0)),esk2_0,esk3_0)
    | ~ v1_funct_1(esk1_2(k5_partfun1(esk2_0,esk3_0,esk4_0),k1_funct_2(esk2_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_49])).

cnf(c_0_99,plain,
    ( v1_funct_2(esk1_2(k5_partfun1(X1,X2,X3),X4),X1,X2)
    | r1_tarski(k5_partfun1(X1,X2,X3),X4)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_93,c_0_32])).

cnf(c_0_100,plain,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_101,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_102,plain,
    ( k1_xboole_0 = X1
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_95])).

cnf(c_0_103,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk3_0) = esk4_0
    | ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_96,c_0_51])).

cnf(c_0_104,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk3_0) = esk2_0
    | ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_97,c_0_38])).

cnf(c_0_105,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ v1_funct_1(esk1_2(k5_partfun1(esk2_0,esk3_0,esk4_0),k1_funct_2(esk2_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_57]),c_0_23])]),c_0_49])).

cnf(c_0_106,plain,
    ( v1_funct_1(esk1_2(k5_partfun1(X1,X2,X3),X4))
    | r1_tarski(k5_partfun1(X1,X2,X3),X4)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_100,c_0_32])).

cnf(c_0_107,plain,
    ( r2_hidden(X2,k1_funct_2(X1,X3))
    | X1 != k1_xboole_0
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_108,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_101])).

cnf(c_0_109,plain,
    ( v1_funct_1(X1)
    | v1_xboole_0(k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k5_partfun1(X2,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_69])).

cnf(c_0_110,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_102,c_0_51])).

cnf(c_0_111,negated_conjecture,
    ( esk2_0 = esk4_0
    | ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_112,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_57]),c_0_23])]),c_0_49])).

cnf(c_0_113,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_114,plain,
    ( r2_hidden(X1,k1_funct_2(k1_xboole_0,X2))
    | ~ v1_funct_2(X1,k1_xboole_0,X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_107]),c_0_108])).

cnf(c_0_115,plain,
    ( m1_subset_1(esk1_2(k5_partfun1(X1,X2,X3),X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k5_partfun1(X1,X2,X3),X4)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_32])).

cnf(c_0_116,negated_conjecture,
    ( v1_funct_1(X1)
    | ~ m1_subset_1(X1,k5_partfun1(esk2_0,esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_23]),c_0_57])]),c_0_58])).

cnf(c_0_117,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_110,c_0_104])).

cnf(c_0_118,negated_conjecture,
    ( esk2_0 = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111,c_0_112]),c_0_113])])).

cnf(c_0_119,plain,
    ( r1_tarski(X1,k1_funct_2(k1_xboole_0,X2))
    | ~ v1_funct_2(esk1_2(X1,k1_funct_2(k1_xboole_0,X2)),k1_xboole_0,X2)
    | ~ v1_funct_1(esk1_2(X1,k1_funct_2(k1_xboole_0,X2)))
    | ~ m1_subset_1(esk1_2(X1,k1_funct_2(k1_xboole_0,X2)),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_114])).

cnf(c_0_120,plain,
    ( m1_subset_1(esk1_2(k5_partfun1(k1_xboole_0,X1,X2),X3),k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(k5_partfun1(k1_xboole_0,X1,X2),X3)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_115,c_0_108])).

cnf(c_0_121,negated_conjecture,
    ( v1_funct_1(esk1_2(k5_partfun1(esk2_0,esk3_0,esk4_0),X1))
    | r1_tarski(k5_partfun1(esk2_0,esk3_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_116,c_0_86])).

cnf(c_0_122,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_117,c_0_112]),c_0_113])]),c_0_118])).

cnf(c_0_123,plain,
    ( r1_tarski(k5_partfun1(k1_xboole_0,X1,X2),k1_funct_2(k1_xboole_0,X1))
    | ~ v1_funct_1(esk1_2(k5_partfun1(k1_xboole_0,X1,X2),k1_funct_2(k1_xboole_0,X1)))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_99]),c_0_108]),c_0_120])).

cnf(c_0_124,negated_conjecture,
    ( v1_funct_1(esk1_2(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1))
    | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_121,c_0_112]),c_0_112]),c_0_118]),c_0_122]),c_0_122]),c_0_118]),c_0_122]),c_0_122])).

cnf(c_0_125,negated_conjecture,
    ( v1_funct_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_57,c_0_122])).

cnf(c_0_126,negated_conjecture,
    ( ~ r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_112]),c_0_112]),c_0_118]),c_0_122]),c_0_122]),c_0_118]),c_0_122])).

cnf(c_0_127,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_124]),c_0_125]),c_0_87])]),c_0_126]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:49:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.69/0.85  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.69/0.85  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.69/0.85  #
% 0.69/0.85  # Preprocessing time       : 0.029 s
% 0.69/0.85  
% 0.69/0.85  # Proof found!
% 0.69/0.85  # SZS status Theorem
% 0.69/0.85  # SZS output start CNFRefutation
% 0.69/0.85  fof(t159_funct_2, conjecture, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>r1_tarski(k5_partfun1(X1,X2,X3),k1_funct_2(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t159_funct_2)).
% 0.69/0.85  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.69/0.85  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.69/0.85  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.69/0.85  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.69/0.85  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.69/0.85  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 0.69/0.85  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 0.69/0.85  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.69/0.85  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.69/0.85  fof(fc2_partfun1, axiom, ![X1, X2, X3]:((((~(v1_xboole_0(X1))&v1_xboole_0(X2))&v1_funct_1(X3))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>v1_xboole_0(k5_partfun1(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_partfun1)).
% 0.69/0.85  fof(t158_funct_2, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(r2_hidden(X4,k5_partfun1(X1,X2,X3))=>((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t158_funct_2)).
% 0.69/0.85  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.69/0.85  fof(t11_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0=>X1=k1_xboole_0)=>r2_hidden(X3,k1_funct_2(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_funct_2)).
% 0.69/0.85  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.69/0.85  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.69/0.85  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.69/0.85  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>r1_tarski(k5_partfun1(X1,X2,X3),k1_funct_2(X1,X2)))), inference(assume_negation,[status(cth)],[t159_funct_2])).
% 0.69/0.85  fof(c_0_18, plain, ![X21, X22]:((~m1_subset_1(X21,k1_zfmisc_1(X22))|r1_tarski(X21,X22))&(~r1_tarski(X21,X22)|m1_subset_1(X21,k1_zfmisc_1(X22)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.69/0.85  fof(c_0_19, negated_conjecture, ((v1_funct_1(esk4_0)&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))&~r1_tarski(k5_partfun1(esk2_0,esk3_0,esk4_0),k1_funct_2(esk2_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.69/0.85  fof(c_0_20, plain, ![X26, X27, X28]:(~r2_hidden(X26,X27)|~m1_subset_1(X27,k1_zfmisc_1(X28))|~v1_xboole_0(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.69/0.85  fof(c_0_21, plain, ![X13, X14, X15]:(~r1_tarski(X13,X14)|~r1_tarski(X14,X15)|r1_tarski(X13,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.69/0.85  cnf(c_0_22, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.69/0.85  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.69/0.85  cnf(c_0_24, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.69/0.85  cnf(c_0_25, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.69/0.85  fof(c_0_26, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.69/0.85  fof(c_0_27, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.69/0.85  fof(c_0_28, plain, ![X37, X38, X39]:(~v1_xboole_0(X37)|(~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X38,X37)))|v1_xboole_0(X39))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 0.69/0.85  cnf(c_0_29, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.69/0.85  cnf(c_0_30, negated_conjecture, (r1_tarski(esk4_0,k2_zfmisc_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.69/0.85  cnf(c_0_31, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X3)|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.69/0.85  cnf(c_0_32, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.69/0.85  cnf(c_0_33, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.69/0.85  cnf(c_0_34, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.69/0.85  cnf(c_0_35, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.69/0.85  cnf(c_0_36, negated_conjecture, (r1_tarski(X1,k2_zfmisc_1(esk2_0,esk3_0))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.69/0.85  cnf(c_0_37, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.69/0.85  cnf(c_0_38, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_33])).
% 0.69/0.85  fof(c_0_39, plain, ![X29, X30]:((~v4_relat_1(X30,X29)|r1_tarski(k1_relat_1(X30),X29)|~v1_relat_1(X30))&(~r1_tarski(k1_relat_1(X30),X29)|v4_relat_1(X30,X29)|~v1_relat_1(X30))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.69/0.85  fof(c_0_40, plain, ![X34, X35, X36]:((v4_relat_1(X36,X34)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))&(v5_relat_1(X36,X35)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.69/0.85  fof(c_0_41, plain, ![X31, X32, X33]:(~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|v1_relat_1(X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.69/0.85  cnf(c_0_42, plain, (v1_xboole_0(X1)|~v1_xboole_0(X2)|~r1_tarski(X1,k2_zfmisc_1(X3,X2))), inference(spm,[status(thm)],[c_0_34, c_0_25])).
% 0.69/0.85  cnf(c_0_43, negated_conjecture, (k2_zfmisc_1(esk2_0,esk3_0)=X1|~r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),X1)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.69/0.85  cnf(c_0_44, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.69/0.85  cnf(c_0_45, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.69/0.85  cnf(c_0_46, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.69/0.85  cnf(c_0_47, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.69/0.85  fof(c_0_48, plain, ![X40, X41, X42]:(v1_xboole_0(X40)|~v1_xboole_0(X41)|~v1_funct_1(X42)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))|v1_xboole_0(k5_partfun1(X40,X41,X42))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_partfun1])])])).
% 0.69/0.85  cnf(c_0_49, negated_conjecture, (~r1_tarski(k5_partfun1(esk2_0,esk3_0,esk4_0),k1_funct_2(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.69/0.85  cnf(c_0_50, negated_conjecture, (r1_tarski(esk4_0,X1)|~v1_xboole_0(k2_zfmisc_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_37, c_0_30])).
% 0.69/0.85  cnf(c_0_51, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_42, c_0_38])).
% 0.69/0.85  cnf(c_0_52, negated_conjecture, (k2_zfmisc_1(esk2_0,esk3_0)=X1|~v1_xboole_0(k2_zfmisc_1(esk2_0,esk3_0))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.69/0.85  cnf(c_0_53, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X3)|~v1_relat_1(X1)|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_37, c_0_45])).
% 0.69/0.85  cnf(c_0_54, negated_conjecture, (v4_relat_1(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_46, c_0_23])).
% 0.69/0.85  cnf(c_0_55, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_47, c_0_23])).
% 0.69/0.85  cnf(c_0_56, plain, (v1_xboole_0(X1)|v1_xboole_0(k5_partfun1(X1,X2,X3))|~v1_xboole_0(X2)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.69/0.85  cnf(c_0_57, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.69/0.85  cnf(c_0_58, negated_conjecture, (~v1_xboole_0(k5_partfun1(esk2_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_49, c_0_44])).
% 0.69/0.85  cnf(c_0_59, plain, (v4_relat_1(X1,X2)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_46, c_0_25])).
% 0.69/0.85  cnf(c_0_60, negated_conjecture, (r1_tarski(esk4_0,X1)|~v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.69/0.85  cnf(c_0_61, negated_conjecture, (k2_zfmisc_1(esk2_0,esk3_0)=X1|~v1_xboole_0(esk3_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_52, c_0_51])).
% 0.69/0.85  cnf(c_0_62, negated_conjecture, (r1_tarski(k1_relat_1(esk4_0),X1)|~v1_xboole_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])])).
% 0.69/0.85  cnf(c_0_63, negated_conjecture, (v1_xboole_0(esk2_0)|~v1_xboole_0(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_23]), c_0_57])]), c_0_58])).
% 0.69/0.85  fof(c_0_64, plain, ![X46, X47, X48, X49]:(((v1_funct_1(X49)|~r2_hidden(X49,k5_partfun1(X46,X47,X48))|(~v1_funct_1(X48)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))))&(v1_funct_2(X49,X46,X47)|~r2_hidden(X49,k5_partfun1(X46,X47,X48))|(~v1_funct_1(X48)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))))))&(m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))|~r2_hidden(X49,k5_partfun1(X46,X47,X48))|(~v1_funct_1(X48)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_funct_2])])])])).
% 0.69/0.85  fof(c_0_65, plain, ![X18, X19]:(((~m1_subset_1(X19,X18)|r2_hidden(X19,X18)|v1_xboole_0(X18))&(~r2_hidden(X19,X18)|m1_subset_1(X19,X18)|v1_xboole_0(X18)))&((~m1_subset_1(X19,X18)|v1_xboole_0(X19)|~v1_xboole_0(X18))&(~v1_xboole_0(X19)|m1_subset_1(X19,X18)|~v1_xboole_0(X18)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.69/0.85  cnf(c_0_66, negated_conjecture, (v4_relat_1(esk4_0,X1)|~v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.69/0.85  cnf(c_0_67, negated_conjecture, (k2_zfmisc_1(esk2_0,esk3_0)=k1_relat_1(esk4_0)|~v1_xboole_0(esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63])).
% 0.69/0.85  cnf(c_0_68, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X1,k5_partfun1(X2,X3,X4))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.69/0.85  cnf(c_0_69, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.69/0.85  cnf(c_0_70, negated_conjecture, (r1_tarski(k1_relat_1(esk4_0),X1)|~v1_xboole_0(esk3_0)|~v1_xboole_0(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_66]), c_0_55])])).
% 0.69/0.85  cnf(c_0_71, negated_conjecture, (v1_xboole_0(k1_relat_1(esk4_0))|~v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_51, c_0_67])).
% 0.69/0.85  fof(c_0_72, plain, ![X43, X44, X45]:((X44=k1_xboole_0|r2_hidden(X45,k1_funct_2(X43,X44))|(~v1_funct_1(X45)|~v1_funct_2(X45,X43,X44)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))))&(X43!=k1_xboole_0|r2_hidden(X45,k1_funct_2(X43,X44))|(~v1_funct_1(X45)|~v1_funct_2(X45,X43,X44)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_funct_2])])])).
% 0.69/0.85  cnf(c_0_73, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|v1_xboole_0(k5_partfun1(X2,X3,X4))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X1,k5_partfun1(X2,X3,X4))), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.69/0.85  cnf(c_0_74, negated_conjecture, (r1_tarski(X1,k2_zfmisc_1(esk2_0,esk3_0))|~r1_tarski(X2,esk4_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_29, c_0_36])).
% 0.69/0.85  cnf(c_0_75, negated_conjecture, (r1_tarski(k1_relat_1(esk4_0),X1)|~v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.69/0.85  cnf(c_0_76, plain, (X1=X2|~v1_xboole_0(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_35, c_0_44])).
% 0.69/0.85  cnf(c_0_77, plain, (X1=k1_xboole_0|r2_hidden(X2,k1_funct_2(X3,X1))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.69/0.85  cnf(c_0_78, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))|~m1_subset_1(X1,k5_partfun1(esk2_0,esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_23]), c_0_57])]), c_0_58])).
% 0.69/0.85  cnf(c_0_79, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.69/0.85  fof(c_0_80, plain, ![X20]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X20)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.69/0.85  cnf(c_0_81, negated_conjecture, (r1_tarski(X1,k2_zfmisc_1(esk2_0,esk3_0))|~v1_xboole_0(esk3_0)|~r1_tarski(X1,k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.69/0.85  cnf(c_0_82, plain, (k1_relat_1(X1)=X2|~v4_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_76, c_0_45])).
% 0.69/0.85  cnf(c_0_83, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.69/0.85  cnf(c_0_84, plain, (X1=k1_xboole_0|r2_hidden(X2,k1_funct_2(X3,X1))|~v1_funct_2(X2,X3,X1)|~v1_funct_1(X2)|~r1_tarski(X2,k2_zfmisc_1(X3,X1))), inference(spm,[status(thm)],[c_0_77, c_0_25])).
% 0.69/0.85  cnf(c_0_85, negated_conjecture, (r1_tarski(X1,k2_zfmisc_1(esk2_0,esk3_0))|~m1_subset_1(X1,k5_partfun1(esk2_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_22, c_0_78])).
% 0.69/0.85  cnf(c_0_86, plain, (m1_subset_1(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_32]), c_0_44])).
% 0.69/0.85  cnf(c_0_87, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.69/0.85  cnf(c_0_88, negated_conjecture, (k2_zfmisc_1(esk2_0,esk3_0)=esk4_0|~r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_35, c_0_30])).
% 0.69/0.85  cnf(c_0_89, negated_conjecture, (X1=k2_zfmisc_1(esk2_0,esk3_0)|~v1_xboole_0(esk3_0)|~r1_tarski(X1,k1_relat_1(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_81]), c_0_51])).
% 0.69/0.85  cnf(c_0_90, negated_conjecture, (k1_relat_1(esk4_0)=esk2_0|~v1_xboole_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_54]), c_0_55])])).
% 0.69/0.85  cnf(c_0_91, plain, (X1=k1_xboole_0|r1_tarski(X2,k1_funct_2(X3,X1))|~v1_funct_2(esk1_2(X2,k1_funct_2(X3,X1)),X3,X1)|~v1_funct_1(esk1_2(X2,k1_funct_2(X3,X1)))|~r1_tarski(esk1_2(X2,k1_funct_2(X3,X1)),k2_zfmisc_1(X3,X1))), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.69/0.85  cnf(c_0_92, negated_conjecture, (r1_tarski(esk1_2(k5_partfun1(esk2_0,esk3_0,esk4_0),X1),k2_zfmisc_1(esk2_0,esk3_0))|r1_tarski(k5_partfun1(esk2_0,esk3_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.69/0.85  cnf(c_0_93, plain, (v1_funct_2(X1,X2,X3)|~r2_hidden(X1,k5_partfun1(X2,X3,X4))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.69/0.85  fof(c_0_94, plain, ![X16, X17]:((k2_zfmisc_1(X16,X17)!=k1_xboole_0|(X16=k1_xboole_0|X17=k1_xboole_0))&((X16!=k1_xboole_0|k2_zfmisc_1(X16,X17)=k1_xboole_0)&(X17!=k1_xboole_0|k2_zfmisc_1(X16,X17)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.69/0.85  cnf(c_0_95, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_22, c_0_87])).
% 0.69/0.85  cnf(c_0_96, negated_conjecture, (k2_zfmisc_1(esk2_0,esk3_0)=esk4_0|~v1_xboole_0(k2_zfmisc_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_88, c_0_44])).
% 0.69/0.85  cnf(c_0_97, negated_conjecture, (X1=k2_zfmisc_1(esk2_0,esk3_0)|~v1_xboole_0(esk3_0)|~r1_tarski(X1,esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_63])).
% 0.69/0.85  cnf(c_0_98, negated_conjecture, (esk3_0=k1_xboole_0|~v1_funct_2(esk1_2(k5_partfun1(esk2_0,esk3_0,esk4_0),k1_funct_2(esk2_0,esk3_0)),esk2_0,esk3_0)|~v1_funct_1(esk1_2(k5_partfun1(esk2_0,esk3_0,esk4_0),k1_funct_2(esk2_0,esk3_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_49])).
% 0.69/0.85  cnf(c_0_99, plain, (v1_funct_2(esk1_2(k5_partfun1(X1,X2,X3),X4),X1,X2)|r1_tarski(k5_partfun1(X1,X2,X3),X4)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_93, c_0_32])).
% 0.69/0.85  cnf(c_0_100, plain, (v1_funct_1(X1)|~r2_hidden(X1,k5_partfun1(X2,X3,X4))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.69/0.85  cnf(c_0_101, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_94])).
% 0.69/0.85  cnf(c_0_102, plain, (k1_xboole_0=X1|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_76, c_0_95])).
% 0.69/0.85  cnf(c_0_103, negated_conjecture, (k2_zfmisc_1(esk2_0,esk3_0)=esk4_0|~v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_96, c_0_51])).
% 0.69/0.85  cnf(c_0_104, negated_conjecture, (k2_zfmisc_1(esk2_0,esk3_0)=esk2_0|~v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_97, c_0_38])).
% 0.69/0.85  cnf(c_0_105, negated_conjecture, (esk3_0=k1_xboole_0|~v1_funct_1(esk1_2(k5_partfun1(esk2_0,esk3_0,esk4_0),k1_funct_2(esk2_0,esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_57]), c_0_23])]), c_0_49])).
% 0.69/0.85  cnf(c_0_106, plain, (v1_funct_1(esk1_2(k5_partfun1(X1,X2,X3),X4))|r1_tarski(k5_partfun1(X1,X2,X3),X4)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_100, c_0_32])).
% 0.69/0.85  cnf(c_0_107, plain, (r2_hidden(X2,k1_funct_2(X1,X3))|X1!=k1_xboole_0|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.69/0.85  cnf(c_0_108, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_101])).
% 0.69/0.85  cnf(c_0_109, plain, (v1_funct_1(X1)|v1_xboole_0(k5_partfun1(X2,X3,X4))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X1,k5_partfun1(X2,X3,X4))), inference(spm,[status(thm)],[c_0_100, c_0_69])).
% 0.69/0.85  cnf(c_0_110, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_102, c_0_51])).
% 0.69/0.85  cnf(c_0_111, negated_conjecture, (esk2_0=esk4_0|~v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 0.69/0.85  cnf(c_0_112, negated_conjecture, (esk3_0=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_57]), c_0_23])]), c_0_49])).
% 0.69/0.85  cnf(c_0_113, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.69/0.85  cnf(c_0_114, plain, (r2_hidden(X1,k1_funct_2(k1_xboole_0,X2))|~v1_funct_2(X1,k1_xboole_0,X2)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_107]), c_0_108])).
% 0.69/0.85  cnf(c_0_115, plain, (m1_subset_1(esk1_2(k5_partfun1(X1,X2,X3),X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|r1_tarski(k5_partfun1(X1,X2,X3),X4)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_68, c_0_32])).
% 0.69/0.85  cnf(c_0_116, negated_conjecture, (v1_funct_1(X1)|~m1_subset_1(X1,k5_partfun1(esk2_0,esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_23]), c_0_57])]), c_0_58])).
% 0.69/0.85  cnf(c_0_117, negated_conjecture, (esk2_0=k1_xboole_0|~v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_110, c_0_104])).
% 0.69/0.85  cnf(c_0_118, negated_conjecture, (esk2_0=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111, c_0_112]), c_0_113])])).
% 0.69/0.85  cnf(c_0_119, plain, (r1_tarski(X1,k1_funct_2(k1_xboole_0,X2))|~v1_funct_2(esk1_2(X1,k1_funct_2(k1_xboole_0,X2)),k1_xboole_0,X2)|~v1_funct_1(esk1_2(X1,k1_funct_2(k1_xboole_0,X2)))|~m1_subset_1(esk1_2(X1,k1_funct_2(k1_xboole_0,X2)),k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_83, c_0_114])).
% 0.69/0.85  cnf(c_0_120, plain, (m1_subset_1(esk1_2(k5_partfun1(k1_xboole_0,X1,X2),X3),k1_zfmisc_1(k1_xboole_0))|r1_tarski(k5_partfun1(k1_xboole_0,X1,X2),X3)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_115, c_0_108])).
% 0.69/0.85  cnf(c_0_121, negated_conjecture, (v1_funct_1(esk1_2(k5_partfun1(esk2_0,esk3_0,esk4_0),X1))|r1_tarski(k5_partfun1(esk2_0,esk3_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_116, c_0_86])).
% 0.69/0.85  cnf(c_0_122, negated_conjecture, (esk4_0=k1_xboole_0), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_117, c_0_112]), c_0_113])]), c_0_118])).
% 0.69/0.85  cnf(c_0_123, plain, (r1_tarski(k5_partfun1(k1_xboole_0,X1,X2),k1_funct_2(k1_xboole_0,X1))|~v1_funct_1(esk1_2(k5_partfun1(k1_xboole_0,X1,X2),k1_funct_2(k1_xboole_0,X1)))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_99]), c_0_108]), c_0_120])).
% 0.69/0.85  cnf(c_0_124, negated_conjecture, (v1_funct_1(esk1_2(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1))|r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_121, c_0_112]), c_0_112]), c_0_118]), c_0_122]), c_0_122]), c_0_118]), c_0_122]), c_0_122])).
% 0.69/0.85  cnf(c_0_125, negated_conjecture, (v1_funct_1(k1_xboole_0)), inference(rw,[status(thm)],[c_0_57, c_0_122])).
% 0.69/0.85  cnf(c_0_126, negated_conjecture, (~r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_112]), c_0_112]), c_0_118]), c_0_122]), c_0_122]), c_0_118]), c_0_122])).
% 0.69/0.85  cnf(c_0_127, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_124]), c_0_125]), c_0_87])]), c_0_126]), ['proof']).
% 0.69/0.85  # SZS output end CNFRefutation
% 0.69/0.85  # Proof object total steps             : 128
% 0.69/0.85  # Proof object clause steps            : 94
% 0.69/0.85  # Proof object formula steps           : 34
% 0.69/0.85  # Proof object conjectures             : 48
% 0.69/0.85  # Proof object clause conjectures      : 45
% 0.69/0.85  # Proof object formula conjectures     : 3
% 0.69/0.85  # Proof object initial clauses used    : 26
% 0.69/0.85  # Proof object initial formulas used   : 17
% 0.69/0.85  # Proof object generating inferences   : 60
% 0.69/0.85  # Proof object simplifying inferences  : 61
% 0.69/0.85  # Training examples: 0 positive, 0 negative
% 0.69/0.85  # Parsed axioms                        : 18
% 0.69/0.85  # Removed by relevancy pruning/SinE    : 0
% 0.69/0.85  # Initial clauses                      : 35
% 0.69/0.85  # Removed in clause preprocessing      : 0
% 0.69/0.85  # Initial clauses in saturation        : 35
% 0.69/0.85  # Processed clauses                    : 8440
% 0.69/0.85  # ...of these trivial                  : 135
% 0.69/0.85  # ...subsumed                          : 7362
% 0.69/0.85  # ...remaining for further processing  : 943
% 0.69/0.85  # Other redundant clauses eliminated   : 5
% 0.69/0.85  # Clauses deleted for lack of memory   : 0
% 0.69/0.85  # Backward-subsumed                    : 101
% 0.69/0.85  # Backward-rewritten                   : 525
% 0.69/0.85  # Generated clauses                    : 26490
% 0.69/0.85  # ...of the previous two non-trivial   : 23758
% 0.69/0.85  # Contextual simplify-reflections      : 90
% 0.69/0.85  # Paramodulations                      : 26485
% 0.69/0.85  # Factorizations                       : 0
% 0.69/0.85  # Equation resolutions                 : 5
% 0.69/0.85  # Propositional unsat checks           : 0
% 0.69/0.85  #    Propositional check models        : 0
% 0.69/0.85  #    Propositional check unsatisfiable : 0
% 0.69/0.85  #    Propositional clauses             : 0
% 0.69/0.85  #    Propositional clauses after purity: 0
% 0.69/0.85  #    Propositional unsat core size     : 0
% 0.69/0.85  #    Propositional preprocessing time  : 0.000
% 0.69/0.85  #    Propositional encoding time       : 0.000
% 0.69/0.85  #    Propositional solver time         : 0.000
% 0.69/0.85  #    Success case prop preproc time    : 0.000
% 0.69/0.85  #    Success case prop encoding time   : 0.000
% 0.69/0.85  #    Success case prop solver time     : 0.000
% 0.69/0.85  # Current number of processed clauses  : 312
% 0.69/0.85  #    Positive orientable unit clauses  : 20
% 0.69/0.85  #    Positive unorientable unit clauses: 0
% 0.69/0.85  #    Negative unit clauses             : 3
% 0.69/0.85  #    Non-unit-clauses                  : 289
% 0.69/0.85  # Current number of unprocessed clauses: 9594
% 0.69/0.85  # ...number of literals in the above   : 48176
% 0.69/0.85  # Current number of archived formulas  : 0
% 0.69/0.85  # Current number of archived clauses   : 626
% 0.69/0.85  # Clause-clause subsumption calls (NU) : 431501
% 0.69/0.85  # Rec. Clause-clause subsumption calls : 244387
% 0.69/0.85  # Non-unit clause-clause subsumptions  : 7483
% 0.69/0.85  # Unit Clause-clause subsumption calls : 797
% 0.69/0.85  # Rewrite failures with RHS unbound    : 0
% 0.69/0.85  # BW rewrite match attempts            : 15
% 0.69/0.85  # BW rewrite match successes           : 5
% 0.69/0.85  # Condensation attempts                : 0
% 0.69/0.85  # Condensation successes               : 0
% 0.69/0.85  # Termbank termtop insertions          : 322431
% 0.69/0.86  
% 0.69/0.86  # -------------------------------------------------
% 0.69/0.86  # User time                : 0.504 s
% 0.69/0.86  # System time              : 0.010 s
% 0.69/0.86  # Total time               : 0.514 s
% 0.69/0.86  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
