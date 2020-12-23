%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:05:24 EST 2020

% Result     : Theorem 0.48s
% Output     : CNFRefutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 119 expanded)
%              Number of clauses        :   36 (  50 expanded)
%              Number of leaves         :   15 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :  218 ( 342 expanded)
%              Number of equality atoms :   85 ( 133 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t65_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,k1_tarski(X2))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
     => ( r2_hidden(X3,X1)
       => k1_funct_1(X4,X3) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(t176_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v5_relat_1(X3,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,k1_relat_1(X3))
       => m1_subset_1(k1_funct_1(X3,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).

fof(fc2_xboole_0,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_15,plain,(
    ! [X18,X19,X20,X21,X22,X23] :
      ( ( ~ r2_hidden(X20,X19)
        | X20 = X18
        | X19 != k1_tarski(X18) )
      & ( X21 != X18
        | r2_hidden(X21,X19)
        | X19 != k1_tarski(X18) )
      & ( ~ r2_hidden(esk2_2(X22,X23),X23)
        | esk2_2(X22,X23) != X22
        | X23 = k1_tarski(X22) )
      & ( r2_hidden(esk2_2(X22,X23),X23)
        | esk2_2(X22,X23) = X22
        | X23 = k1_tarski(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_16,plain,(
    ! [X25] : k2_tarski(X25,X25) = k1_tarski(X25) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_17,plain,(
    ! [X26,X27] : k1_enumset1(X26,X26,X27) = k2_tarski(X26,X27) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,k1_tarski(X2))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
       => ( r2_hidden(X3,X1)
         => k1_funct_1(X4,X3) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t65_funct_2])).

cnf(c_0_19,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X29,X30] :
      ( ~ m1_subset_1(X29,X30)
      | v1_xboole_0(X30)
      | r2_hidden(X29,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_23,plain,(
    ! [X35,X36,X37] :
      ( ~ v1_relat_1(X37)
      | ~ v5_relat_1(X37,X35)
      | ~ v1_funct_1(X37)
      | ~ r2_hidden(X36,k1_relat_1(X37))
      | m1_subset_1(k1_funct_1(X37,X36),X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t176_funct_1])])).

fof(c_0_24,plain,(
    ! [X28] : ~ v1_xboole_0(k1_tarski(X28)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

fof(c_0_25,negated_conjecture,
    ( v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk3_0,k1_tarski(esk4_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_tarski(esk4_0))))
    & r2_hidden(esk5_0,esk3_0)
    & k1_funct_1(esk6_0,esk5_0) != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

cnf(c_0_26,plain,
    ( X1 = X3
    | X2 != k1_enumset1(X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

cnf(c_0_27,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( m1_subset_1(k1_funct_1(X1,X3),X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_30,plain,(
    ! [X40,X41,X42] :
      ( ( v4_relat_1(X42,X40)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) )
      & ( v5_relat_1(X42,X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_tarski(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_32,plain,(
    ! [X31,X32] :
      ( ~ v1_relat_1(X31)
      | ~ m1_subset_1(X32,k1_zfmisc_1(X31))
      | v1_relat_1(X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_33,plain,(
    ! [X33,X34] : v1_relat_1(k2_zfmisc_1(X33,X34)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_34,plain,(
    ! [X43,X44,X45] :
      ( ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
      | k1_relset_1(X43,X44,X45) = k1_relat_1(X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_35,plain,(
    ! [X46,X47,X48] :
      ( ( ~ v1_funct_2(X48,X46,X47)
        | X46 = k1_relset_1(X46,X47,X48)
        | X47 = k1_xboole_0
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) )
      & ( X46 != k1_relset_1(X46,X47,X48)
        | v1_funct_2(X48,X46,X47)
        | X47 = k1_xboole_0
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) )
      & ( ~ v1_funct_2(X48,X46,X47)
        | X46 = k1_relset_1(X46,X47,X48)
        | X46 != k1_xboole_0
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) )
      & ( X46 != k1_relset_1(X46,X47,X48)
        | v1_funct_2(X48,X46,X47)
        | X46 != k1_xboole_0
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) )
      & ( ~ v1_funct_2(X48,X46,X47)
        | X48 = k1_xboole_0
        | X46 = k1_xboole_0
        | X47 != k1_xboole_0
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) )
      & ( X48 != k1_xboole_0
        | v1_funct_2(X48,X46,X47)
        | X46 = k1_xboole_0
        | X47 != k1_xboole_0
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_36,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_enumset1(X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(k1_funct_1(X2,X3),X1)
    | ~ v1_funct_1(X2)
    | ~ v5_relat_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_38,plain,
    ( ~ v1_xboole_0(k1_enumset1(X1,X1,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_20]),c_0_21])).

cnf(c_0_39,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_20]),c_0_21])).

cnf(c_0_41,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_2(esk6_0,esk3_0,k1_tarski(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_46,plain,
    ( k1_funct_1(X1,X2) = X3
    | ~ v1_funct_1(X1)
    | ~ v5_relat_1(X1,k1_enumset1(X3,X3,X3))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( v5_relat_1(esk6_0,k1_enumset1(esk4_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_49,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_40]),c_0_42])])).

cnf(c_0_50,plain,
    ( X1 = k1_relat_1(X2)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( v1_funct_2(esk6_0,esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_20]),c_0_21])).

fof(c_0_52,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14,X15,X16] :
      ( ( ~ r2_hidden(X11,X10)
        | X11 = X7
        | X11 = X8
        | X11 = X9
        | X10 != k1_enumset1(X7,X8,X9) )
      & ( X12 != X7
        | r2_hidden(X12,X10)
        | X10 != k1_enumset1(X7,X8,X9) )
      & ( X12 != X8
        | r2_hidden(X12,X10)
        | X10 != k1_enumset1(X7,X8,X9) )
      & ( X12 != X9
        | r2_hidden(X12,X10)
        | X10 != k1_enumset1(X7,X8,X9) )
      & ( esk1_4(X13,X14,X15,X16) != X13
        | ~ r2_hidden(esk1_4(X13,X14,X15,X16),X16)
        | X16 = k1_enumset1(X13,X14,X15) )
      & ( esk1_4(X13,X14,X15,X16) != X14
        | ~ r2_hidden(esk1_4(X13,X14,X15,X16),X16)
        | X16 = k1_enumset1(X13,X14,X15) )
      & ( esk1_4(X13,X14,X15,X16) != X15
        | ~ r2_hidden(esk1_4(X13,X14,X15,X16),X16)
        | X16 = k1_enumset1(X13,X14,X15) )
      & ( r2_hidden(esk1_4(X13,X14,X15,X16),X16)
        | esk1_4(X13,X14,X15,X16) = X13
        | esk1_4(X13,X14,X15,X16) = X14
        | esk1_4(X13,X14,X15,X16) = X15
        | X16 = k1_enumset1(X13,X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_53,negated_conjecture,
    ( k1_funct_1(esk6_0,X1) = esk4_0
    | ~ r2_hidden(X1,k1_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_49])])).

cnf(c_0_54,negated_conjecture,
    ( k1_enumset1(esk4_0,esk4_0,esk4_0) = k1_xboole_0
    | k1_relat_1(esk6_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_40]),c_0_51])])).

fof(c_0_55,plain,(
    ! [X38,X39] :
      ( ~ r2_hidden(X38,X39)
      | ~ r1_tarski(X39,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_56,plain,(
    ! [X6] : r1_tarski(k1_xboole_0,X6) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( k1_funct_1(esk6_0,esk5_0) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_59,negated_conjecture,
    ( k1_enumset1(esk4_0,esk4_0,esk4_0) = k1_xboole_0
    | k1_funct_1(esk6_0,X1) = esk4_0
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_61,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_62,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,k1_enumset1(X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_57])])).

cnf(c_0_64,negated_conjecture,
    ( k1_enumset1(esk4_0,esk4_0,esk4_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])])).

cnf(c_0_65,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:37:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.48/0.66  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.48/0.66  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.48/0.66  #
% 0.48/0.66  # Preprocessing time       : 0.029 s
% 0.48/0.66  
% 0.48/0.66  # Proof found!
% 0.48/0.66  # SZS status Theorem
% 0.48/0.66  # SZS output start CNFRefutation
% 0.48/0.66  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.48/0.66  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.48/0.66  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.48/0.66  fof(t65_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>(r2_hidden(X3,X1)=>k1_funct_1(X4,X3)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 0.48/0.66  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.48/0.66  fof(t176_funct_1, axiom, ![X1, X2, X3]:(((v1_relat_1(X3)&v5_relat_1(X3,X1))&v1_funct_1(X3))=>(r2_hidden(X2,k1_relat_1(X3))=>m1_subset_1(k1_funct_1(X3,X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_1)).
% 0.48/0.66  fof(fc2_xboole_0, axiom, ![X1]:~(v1_xboole_0(k1_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 0.48/0.66  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.48/0.66  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.48/0.66  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.48/0.66  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.48/0.66  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.48/0.66  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 0.48/0.66  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.48/0.66  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.48/0.66  fof(c_0_15, plain, ![X18, X19, X20, X21, X22, X23]:(((~r2_hidden(X20,X19)|X20=X18|X19!=k1_tarski(X18))&(X21!=X18|r2_hidden(X21,X19)|X19!=k1_tarski(X18)))&((~r2_hidden(esk2_2(X22,X23),X23)|esk2_2(X22,X23)!=X22|X23=k1_tarski(X22))&(r2_hidden(esk2_2(X22,X23),X23)|esk2_2(X22,X23)=X22|X23=k1_tarski(X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.48/0.66  fof(c_0_16, plain, ![X25]:k2_tarski(X25,X25)=k1_tarski(X25), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.48/0.66  fof(c_0_17, plain, ![X26, X27]:k1_enumset1(X26,X26,X27)=k2_tarski(X26,X27), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.48/0.66  fof(c_0_18, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>(r2_hidden(X3,X1)=>k1_funct_1(X4,X3)=X2))), inference(assume_negation,[status(cth)],[t65_funct_2])).
% 0.48/0.66  cnf(c_0_19, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.48/0.66  cnf(c_0_20, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.48/0.66  cnf(c_0_21, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.48/0.66  fof(c_0_22, plain, ![X29, X30]:(~m1_subset_1(X29,X30)|(v1_xboole_0(X30)|r2_hidden(X29,X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.48/0.66  fof(c_0_23, plain, ![X35, X36, X37]:(~v1_relat_1(X37)|~v5_relat_1(X37,X35)|~v1_funct_1(X37)|(~r2_hidden(X36,k1_relat_1(X37))|m1_subset_1(k1_funct_1(X37,X36),X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t176_funct_1])])).
% 0.48/0.66  fof(c_0_24, plain, ![X28]:~v1_xboole_0(k1_tarski(X28)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).
% 0.48/0.66  fof(c_0_25, negated_conjecture, (((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk3_0,k1_tarski(esk4_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_tarski(esk4_0)))))&(r2_hidden(esk5_0,esk3_0)&k1_funct_1(esk6_0,esk5_0)!=esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.48/0.66  cnf(c_0_26, plain, (X1=X3|X2!=k1_enumset1(X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20]), c_0_21])).
% 0.48/0.66  cnf(c_0_27, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.48/0.66  cnf(c_0_28, plain, (m1_subset_1(k1_funct_1(X1,X3),X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)|~v1_funct_1(X1)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.48/0.66  cnf(c_0_29, plain, (~v1_xboole_0(k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.48/0.66  fof(c_0_30, plain, ![X40, X41, X42]:((v4_relat_1(X42,X40)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))))&(v5_relat_1(X42,X41)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.48/0.66  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_tarski(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.48/0.66  fof(c_0_32, plain, ![X31, X32]:(~v1_relat_1(X31)|(~m1_subset_1(X32,k1_zfmisc_1(X31))|v1_relat_1(X32))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.48/0.66  fof(c_0_33, plain, ![X33, X34]:v1_relat_1(k2_zfmisc_1(X33,X34)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.48/0.66  fof(c_0_34, plain, ![X43, X44, X45]:(~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))|k1_relset_1(X43,X44,X45)=k1_relat_1(X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.48/0.66  fof(c_0_35, plain, ![X46, X47, X48]:((((~v1_funct_2(X48,X46,X47)|X46=k1_relset_1(X46,X47,X48)|X47=k1_xboole_0|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))))&(X46!=k1_relset_1(X46,X47,X48)|v1_funct_2(X48,X46,X47)|X47=k1_xboole_0|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))))&((~v1_funct_2(X48,X46,X47)|X46=k1_relset_1(X46,X47,X48)|X46!=k1_xboole_0|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))))&(X46!=k1_relset_1(X46,X47,X48)|v1_funct_2(X48,X46,X47)|X46!=k1_xboole_0|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))))))&((~v1_funct_2(X48,X46,X47)|X48=k1_xboole_0|X46=k1_xboole_0|X47!=k1_xboole_0|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))))&(X48!=k1_xboole_0|v1_funct_2(X48,X46,X47)|X46=k1_xboole_0|X47!=k1_xboole_0|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.51/0.66  cnf(c_0_36, plain, (X1=X2|~r2_hidden(X1,k1_enumset1(X2,X2,X2))), inference(er,[status(thm)],[c_0_26])).
% 0.51/0.66  cnf(c_0_37, plain, (v1_xboole_0(X1)|r2_hidden(k1_funct_1(X2,X3),X1)|~v1_funct_1(X2)|~v5_relat_1(X2,X1)|~v1_relat_1(X2)|~r2_hidden(X3,k1_relat_1(X2))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.51/0.66  cnf(c_0_38, plain, (~v1_xboole_0(k1_enumset1(X1,X1,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_20]), c_0_21])).
% 0.51/0.66  cnf(c_0_39, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.51/0.66  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_20]), c_0_21])).
% 0.51/0.66  cnf(c_0_41, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.51/0.66  cnf(c_0_42, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.51/0.66  cnf(c_0_43, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.51/0.66  cnf(c_0_44, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.51/0.66  cnf(c_0_45, negated_conjecture, (v1_funct_2(esk6_0,esk3_0,k1_tarski(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.51/0.66  cnf(c_0_46, plain, (k1_funct_1(X1,X2)=X3|~v1_funct_1(X1)|~v5_relat_1(X1,k1_enumset1(X3,X3,X3))|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])).
% 0.51/0.66  cnf(c_0_47, negated_conjecture, (v5_relat_1(esk6_0,k1_enumset1(esk4_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.51/0.66  cnf(c_0_48, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.51/0.66  cnf(c_0_49, negated_conjecture, (v1_relat_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_40]), c_0_42])])).
% 0.51/0.66  cnf(c_0_50, plain, (X1=k1_relat_1(X2)|X3=k1_xboole_0|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.51/0.66  cnf(c_0_51, negated_conjecture, (v1_funct_2(esk6_0,esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_20]), c_0_21])).
% 0.51/0.66  fof(c_0_52, plain, ![X7, X8, X9, X10, X11, X12, X13, X14, X15, X16]:(((~r2_hidden(X11,X10)|(X11=X7|X11=X8|X11=X9)|X10!=k1_enumset1(X7,X8,X9))&(((X12!=X7|r2_hidden(X12,X10)|X10!=k1_enumset1(X7,X8,X9))&(X12!=X8|r2_hidden(X12,X10)|X10!=k1_enumset1(X7,X8,X9)))&(X12!=X9|r2_hidden(X12,X10)|X10!=k1_enumset1(X7,X8,X9))))&((((esk1_4(X13,X14,X15,X16)!=X13|~r2_hidden(esk1_4(X13,X14,X15,X16),X16)|X16=k1_enumset1(X13,X14,X15))&(esk1_4(X13,X14,X15,X16)!=X14|~r2_hidden(esk1_4(X13,X14,X15,X16),X16)|X16=k1_enumset1(X13,X14,X15)))&(esk1_4(X13,X14,X15,X16)!=X15|~r2_hidden(esk1_4(X13,X14,X15,X16),X16)|X16=k1_enumset1(X13,X14,X15)))&(r2_hidden(esk1_4(X13,X14,X15,X16),X16)|(esk1_4(X13,X14,X15,X16)=X13|esk1_4(X13,X14,X15,X16)=X14|esk1_4(X13,X14,X15,X16)=X15)|X16=k1_enumset1(X13,X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.51/0.66  cnf(c_0_53, negated_conjecture, (k1_funct_1(esk6_0,X1)=esk4_0|~r2_hidden(X1,k1_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_49])])).
% 0.51/0.66  cnf(c_0_54, negated_conjecture, (k1_enumset1(esk4_0,esk4_0,esk4_0)=k1_xboole_0|k1_relat_1(esk6_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_40]), c_0_51])])).
% 0.51/0.66  fof(c_0_55, plain, ![X38, X39]:(~r2_hidden(X38,X39)|~r1_tarski(X39,X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.51/0.66  fof(c_0_56, plain, ![X6]:r1_tarski(k1_xboole_0,X6), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.51/0.66  cnf(c_0_57, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.51/0.66  cnf(c_0_58, negated_conjecture, (k1_funct_1(esk6_0,esk5_0)!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.51/0.66  cnf(c_0_59, negated_conjecture, (k1_enumset1(esk4_0,esk4_0,esk4_0)=k1_xboole_0|k1_funct_1(esk6_0,X1)=esk4_0|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.51/0.66  cnf(c_0_60, negated_conjecture, (r2_hidden(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.51/0.66  cnf(c_0_61, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.51/0.66  cnf(c_0_62, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.51/0.66  cnf(c_0_63, plain, (r2_hidden(X1,k1_enumset1(X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_57])])).
% 0.51/0.66  cnf(c_0_64, negated_conjecture, (k1_enumset1(esk4_0,esk4_0,esk4_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])])).
% 0.51/0.66  cnf(c_0_65, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.51/0.66  cnf(c_0_66, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65]), ['proof']).
% 0.51/0.66  # SZS output end CNFRefutation
% 0.51/0.66  # Proof object total steps             : 67
% 0.51/0.66  # Proof object clause steps            : 36
% 0.51/0.66  # Proof object formula steps           : 31
% 0.51/0.66  # Proof object conjectures             : 17
% 0.51/0.66  # Proof object clause conjectures      : 14
% 0.51/0.66  # Proof object formula conjectures     : 3
% 0.51/0.66  # Proof object initial clauses used    : 19
% 0.51/0.66  # Proof object initial formulas used   : 15
% 0.51/0.66  # Proof object generating inferences   : 11
% 0.51/0.66  # Proof object simplifying inferences  : 22
% 0.51/0.66  # Training examples: 0 positive, 0 negative
% 0.51/0.66  # Parsed axioms                        : 15
% 0.51/0.66  # Removed by relevancy pruning/SinE    : 0
% 0.51/0.66  # Initial clauses                      : 35
% 0.51/0.66  # Removed in clause preprocessing      : 2
% 0.51/0.66  # Initial clauses in saturation        : 33
% 0.51/0.66  # Processed clauses                    : 395
% 0.51/0.66  # ...of these trivial                  : 0
% 0.51/0.66  # ...subsumed                          : 200
% 0.51/0.66  # ...remaining for further processing  : 195
% 0.51/0.66  # Other redundant clauses eliminated   : 363
% 0.51/0.66  # Clauses deleted for lack of memory   : 0
% 0.51/0.66  # Backward-subsumed                    : 6
% 0.51/0.66  # Backward-rewritten                   : 37
% 0.51/0.66  # Generated clauses                    : 7575
% 0.51/0.66  # ...of the previous two non-trivial   : 6644
% 0.51/0.66  # Contextual simplify-reflections      : 3
% 0.51/0.66  # Paramodulations                      : 7144
% 0.51/0.66  # Factorizations                       : 70
% 0.51/0.66  # Equation resolutions                 : 366
% 0.51/0.66  # Propositional unsat checks           : 0
% 0.51/0.66  #    Propositional check models        : 0
% 0.51/0.66  #    Propositional check unsatisfiable : 0
% 0.51/0.66  #    Propositional clauses             : 0
% 0.51/0.66  #    Propositional clauses after purity: 0
% 0.51/0.66  #    Propositional unsat core size     : 0
% 0.51/0.66  #    Propositional preprocessing time  : 0.000
% 0.51/0.66  #    Propositional encoding time       : 0.000
% 0.51/0.66  #    Propositional solver time         : 0.000
% 0.51/0.66  #    Success case prop preproc time    : 0.000
% 0.51/0.66  #    Success case prop encoding time   : 0.000
% 0.51/0.66  #    Success case prop solver time     : 0.000
% 0.51/0.66  # Current number of processed clauses  : 142
% 0.51/0.66  #    Positive orientable unit clauses  : 11
% 0.51/0.66  #    Positive unorientable unit clauses: 0
% 0.51/0.66  #    Negative unit clauses             : 3
% 0.51/0.66  #    Non-unit-clauses                  : 128
% 0.51/0.66  # Current number of unprocessed clauses: 6251
% 0.51/0.66  # ...number of literals in the above   : 48618
% 0.51/0.66  # Current number of archived formulas  : 0
% 0.51/0.66  # Current number of archived clauses   : 45
% 0.51/0.66  # Clause-clause subsumption calls (NU) : 5546
% 0.51/0.66  # Rec. Clause-clause subsumption calls : 1366
% 0.51/0.66  # Non-unit clause-clause subsumptions  : 171
% 0.51/0.66  # Unit Clause-clause subsumption calls : 14
% 0.51/0.66  # Rewrite failures with RHS unbound    : 0
% 0.51/0.66  # BW rewrite match attempts            : 5
% 0.51/0.66  # BW rewrite match successes           : 2
% 0.51/0.66  # Condensation attempts                : 0
% 0.51/0.66  # Condensation successes               : 0
% 0.51/0.66  # Termbank termtop insertions          : 170962
% 0.51/0.67  
% 0.51/0.67  # -------------------------------------------------
% 0.51/0.67  # User time                : 0.310 s
% 0.51/0.67  # System time              : 0.010 s
% 0.51/0.67  # Total time               : 0.319 s
% 0.51/0.67  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
