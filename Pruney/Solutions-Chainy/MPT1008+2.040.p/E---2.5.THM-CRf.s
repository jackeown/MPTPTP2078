%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:04:35 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 786 expanded)
%              Number of clauses        :   60 ( 311 expanded)
%              Number of leaves         :   18 ( 224 expanded)
%              Depth                    :   16
%              Number of atoms          :  273 (1584 expanded)
%              Number of equality atoms :  105 ( 836 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l45_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_tarski(X2,X3))
    <=> ~ ( X1 != k1_xboole_0
          & X1 != k1_tarski(X2)
          & X1 != k1_tarski(X3)
          & X1 != k2_tarski(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(t62_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,k1_tarski(X1),X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
     => ( X2 != k1_xboole_0
       => k2_relset_1(k1_tarski(X1),X2,X3) = k1_tarski(k1_funct_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

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

fof(t14_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( k1_relat_1(X2) = k1_tarski(X1)
       => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t22_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
     => ( ! [X4] :
            ~ ( r2_hidden(X4,X2)
              & ! [X5] : ~ r2_hidden(k4_tarski(X4,X5),X3) )
      <=> k1_relset_1(X2,X1,X3) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

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

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(c_0_18,plain,(
    ! [X20,X21,X22] :
      ( ( ~ r1_tarski(X20,k2_tarski(X21,X22))
        | X20 = k1_xboole_0
        | X20 = k1_tarski(X21)
        | X20 = k1_tarski(X22)
        | X20 = k2_tarski(X21,X22) )
      & ( X20 != k1_xboole_0
        | r1_tarski(X20,k2_tarski(X21,X22)) )
      & ( X20 != k1_tarski(X21)
        | r1_tarski(X20,k2_tarski(X21,X22)) )
      & ( X20 != k1_tarski(X22)
        | r1_tarski(X20,k2_tarski(X21,X22)) )
      & ( X20 != k2_tarski(X21,X22)
        | r1_tarski(X20,k2_tarski(X21,X22)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l45_zfmisc_1])])])).

fof(c_0_19,plain,(
    ! [X14] : k2_tarski(X14,X14) = k1_tarski(X14) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_20,plain,(
    ! [X15,X16] : k1_enumset1(X15,X15,X16) = k2_tarski(X15,X16) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_21,plain,(
    ! [X17,X18,X19] : k2_enumset1(X17,X17,X18,X19) = k1_enumset1(X17,X18,X19) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,k2_tarski(X3,X2))
    | X1 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_26,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_27,plain,(
    ! [X27,X28] :
      ( ( ~ v4_relat_1(X28,X27)
        | r1_tarski(k1_relat_1(X28),X27)
        | ~ v1_relat_1(X28) )
      & ( ~ r1_tarski(k1_relat_1(X28),X27)
        | v4_relat_1(X28,X27)
        | ~ v1_relat_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

fof(c_0_28,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
       => ( X2 != k1_xboole_0
         => k2_relset_1(k1_tarski(X1),X2,X3) = k1_tarski(k1_funct_1(X3,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t62_funct_2])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,k2_enumset1(X3,X3,X3,X2))
    | X1 != k2_enumset1(X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_24]),c_0_25]),c_0_25])).

cnf(c_0_30,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_32,negated_conjecture,
    ( v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,k1_tarski(esk4_0),esk5_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk4_0),esk5_0)))
    & esk5_0 != k1_xboole_0
    & k2_relset_1(k1_tarski(esk4_0),esk5_0,esk6_0) != k1_tarski(k1_funct_1(esk6_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,k2_tarski(X2,X3))
    | X1 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_34,plain,
    ( r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X1)) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X2)
    | ~ v4_relat_1(X3,X2)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k1_relat_1(X3)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_37,plain,(
    ! [X37,X38,X39] :
      ( ( v4_relat_1(X39,X37)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( v5_relat_1(X39,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk4_0),esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_39,plain,(
    ! [X34,X35,X36] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
      | v1_relat_1(X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,k2_enumset1(X2,X2,X2,X3))
    | X1 != k2_enumset1(X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_23]),c_0_24]),c_0_24]),c_0_25]),c_0_25])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X2,X3))
    | ~ r2_hidden(X1,k2_enumset1(X3,X3,X3,X3)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_34])).

cnf(c_0_42,plain,
    ( r2_hidden(esk1_2(k1_relat_1(X1),X2),X3)
    | r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_45,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_46,plain,(
    ! [X30,X31] :
      ( ~ v1_relat_1(X31)
      | ~ v1_funct_1(X31)
      | k1_relat_1(X31) != k1_tarski(X30)
      | k2_relat_1(X31) = k1_tarski(k1_funct_1(X31,X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_funct_1])])).

cnf(c_0_47,plain,
    ( r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2)) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( r2_hidden(esk1_2(k1_relat_1(X1),X2),k2_enumset1(X3,X3,X3,X4))
    | r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,k2_enumset1(X4,X4,X4,X4))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( v4_relat_1(esk6_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( k2_relset_1(k1_tarski(esk4_0),esk5_0,esk6_0) != k1_tarski(k1_funct_1(esk6_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_52,plain,
    ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_relat_1(X1) != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_53,plain,(
    ! [X12] : r1_tarski(k1_xboole_0,X12) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X2,X3))
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk1_2(k1_relat_1(esk6_0),X1),k2_enumset1(X2,X2,X2,esk4_0))
    | r1_tarski(k1_relat_1(esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])])).

cnf(c_0_56,negated_conjecture,
    ( k2_relset_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0,esk6_0) != k2_enumset1(k1_funct_1(esk6_0,esk4_0),k1_funct_1(esk6_0,esk4_0),k1_funct_1(esk6_0,esk4_0),k1_funct_1(esk6_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_23]),c_0_23]),c_0_24]),c_0_24]),c_0_25]),c_0_25])).

cnf(c_0_57,plain,
    ( k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2))
    | k1_relat_1(X1) != k2_enumset1(X2,X2,X2,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_23]),c_0_23]),c_0_24]),c_0_24]),c_0_25]),c_0_25])).

cnf(c_0_58,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_59,plain,(
    ! [X40,X41,X42] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
      | k2_relset_1(X40,X41,X42) = k2_relat_1(X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_60,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_61,plain,(
    ! [X43,X44,X45,X47,X48] :
      ( ( r2_hidden(esk2_3(X43,X44,X45),X44)
        | k1_relset_1(X44,X43,X45) = X44
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X44,X43))) )
      & ( ~ r2_hidden(k4_tarski(esk2_3(X43,X44,X45),X47),X45)
        | k1_relset_1(X44,X43,X45) = X44
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X44,X43))) )
      & ( k1_relset_1(X44,X43,X45) != X44
        | ~ r2_hidden(X48,X44)
        | r2_hidden(k4_tarski(X48,esk3_4(X43,X44,X45,X48)),X45)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X44,X43))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_relset_1])])])])])])).

fof(c_0_62,plain,(
    ! [X23] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X23)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_63,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | X1 = k1_tarski(X3)
    | X1 = k2_tarski(X2,X3)
    | ~ r1_tarski(X1,k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk1_2(k1_relat_1(esk6_0),X1),k2_enumset1(esk4_0,esk4_0,esk4_0,X2))
    | r1_tarski(k1_relat_1(esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_66,negated_conjecture,
    ( k2_relset_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0,esk6_0) != k2_relat_1(esk6_0)
    | k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) != k1_relat_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58]),c_0_50])])).

cnf(c_0_67,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

fof(c_0_68,plain,(
    ! [X32,X33] :
      ( ~ r2_hidden(X32,X33)
      | ~ r1_tarski(X33,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_60])).

cnf(c_0_70,plain,
    ( r2_hidden(k4_tarski(X4,esk3_4(X2,X1,X3,X4)),X3)
    | k1_relset_1(X1,X2,X3) != X1
    | ~ r2_hidden(X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_71,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_72,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_enumset1(X3,X3,X3,X3)
    | X1 = k2_enumset1(X2,X2,X2,X3)
    | X1 = k2_enumset1(X2,X2,X2,X2)
    | ~ r1_tarski(X1,k2_enumset1(X2,X2,X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_23]),c_0_23]),c_0_24]),c_0_24]),c_0_24]),c_0_24]),c_0_25]),c_0_25]),c_0_25]),c_0_25])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk6_0),k2_enumset1(esk4_0,esk4_0,esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_74,negated_conjecture,
    ( k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) != k1_relat_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_44])])).

cnf(c_0_75,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_76,plain,
    ( r2_hidden(k4_tarski(X1,esk3_4(X2,X3,k1_xboole_0,X1)),X4)
    | k1_relset_1(X3,X2,k1_xboole_0) != X3
    | ~ r2_hidden(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])])).

fof(c_0_77,plain,(
    ! [X29] :
      ( ( k1_relat_1(X29) != k1_xboole_0
        | X29 = k1_xboole_0
        | ~ v1_relat_1(X29) )
      & ( k2_relat_1(X29) != k1_xboole_0
        | X29 = k1_xboole_0
        | ~ v1_relat_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

cnf(c_0_78,negated_conjecture,
    ( k2_enumset1(esk4_0,esk4_0,esk4_0,X1) = k1_relat_1(esk6_0)
    | k2_enumset1(X1,X1,X1,X1) = k1_relat_1(esk6_0)
    | k1_relat_1(esk6_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74])).

cnf(c_0_79,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) != X1
    | ~ r2_hidden(X3,X1)
    | ~ r1_tarski(X4,k4_tarski(X3,esk3_4(X2,X1,k1_xboole_0,X3))) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

fof(c_0_80,plain,(
    ! [X50,X51,X52] :
      ( ( ~ v1_funct_2(X52,X50,X51)
        | X50 = k1_relset_1(X50,X51,X52)
        | X51 = k1_xboole_0
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))) )
      & ( X50 != k1_relset_1(X50,X51,X52)
        | v1_funct_2(X52,X50,X51)
        | X51 = k1_xboole_0
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))) )
      & ( ~ v1_funct_2(X52,X50,X51)
        | X50 = k1_relset_1(X50,X51,X52)
        | X50 != k1_xboole_0
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))) )
      & ( X50 != k1_relset_1(X50,X51,X52)
        | v1_funct_2(X52,X50,X51)
        | X50 != k1_xboole_0
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))) )
      & ( ~ v1_funct_2(X52,X50,X51)
        | X52 = k1_xboole_0
        | X50 = k1_xboole_0
        | X51 != k1_xboole_0
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))) )
      & ( X52 != k1_xboole_0
        | v1_funct_2(X52,X50,X51)
        | X50 = k1_xboole_0
        | X51 != k1_xboole_0
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_81,negated_conjecture,
    ( v1_funct_2(esk6_0,k1_tarski(esk4_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_82,plain,
    ( X1 = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_83,negated_conjecture,
    ( k1_relat_1(esk6_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_78]),c_0_74])).

cnf(c_0_84,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) != X1
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_79,c_0_60])).

cnf(c_0_85,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_86,negated_conjecture,
    ( v1_funct_2(esk6_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_87,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_50])])).

cnf(c_0_88,plain,
    ( X1 = k1_xboole_0
    | ~ v1_funct_2(k1_xboole_0,X2,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_71])])).

cnf(c_0_89,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0) ),
    inference(rw,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_90,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_91,plain,(
    ! [X13] :
      ( ~ r1_tarski(X13,k1_xboole_0)
      | X13 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_92,negated_conjecture,
    ( ~ r2_hidden(X1,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_90])).

cnf(c_0_93,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_94,negated_conjecture,
    ( r1_tarski(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_92,c_0_36])).

cnf(c_0_95,negated_conjecture,
    ( k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_74,c_0_83])).

cnf(c_0_96,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_95]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:43:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.20/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.029 s
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(l45_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_tarski(X2,X3))<=>~((((X1!=k1_xboole_0&X1!=k1_tarski(X2))&X1!=k1_tarski(X3))&X1!=k2_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 0.20/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.38  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 0.20/0.38  fof(t62_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>k2_relset_1(k1_tarski(X1),X2,X3)=k1_tarski(k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 0.20/0.38  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.20/0.38  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.20/0.38  fof(t14_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 0.20/0.38  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.38  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.20/0.38  fof(t22_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~(r2_hidden(k4_tarski(X4,X5),X3))))<=>k1_relset_1(X2,X1,X3)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relset_1)).
% 0.20/0.38  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.20/0.38  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.20/0.38  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 0.20/0.38  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.20/0.38  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.20/0.38  fof(c_0_18, plain, ![X20, X21, X22]:((~r1_tarski(X20,k2_tarski(X21,X22))|(X20=k1_xboole_0|X20=k1_tarski(X21)|X20=k1_tarski(X22)|X20=k2_tarski(X21,X22)))&((((X20!=k1_xboole_0|r1_tarski(X20,k2_tarski(X21,X22)))&(X20!=k1_tarski(X21)|r1_tarski(X20,k2_tarski(X21,X22))))&(X20!=k1_tarski(X22)|r1_tarski(X20,k2_tarski(X21,X22))))&(X20!=k2_tarski(X21,X22)|r1_tarski(X20,k2_tarski(X21,X22))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l45_zfmisc_1])])])).
% 0.20/0.38  fof(c_0_19, plain, ![X14]:k2_tarski(X14,X14)=k1_tarski(X14), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.38  fof(c_0_20, plain, ![X15, X16]:k1_enumset1(X15,X15,X16)=k2_tarski(X15,X16), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.38  fof(c_0_21, plain, ![X17, X18, X19]:k2_enumset1(X17,X17,X18,X19)=k1_enumset1(X17,X18,X19), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.38  cnf(c_0_22, plain, (r1_tarski(X1,k2_tarski(X3,X2))|X1!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_23, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  cnf(c_0_24, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.38  cnf(c_0_25, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.38  fof(c_0_26, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.38  fof(c_0_27, plain, ![X27, X28]:((~v4_relat_1(X28,X27)|r1_tarski(k1_relat_1(X28),X27)|~v1_relat_1(X28))&(~r1_tarski(k1_relat_1(X28),X27)|v4_relat_1(X28,X27)|~v1_relat_1(X28))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.20/0.38  fof(c_0_28, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>k2_relset_1(k1_tarski(X1),X2,X3)=k1_tarski(k1_funct_1(X3,X1))))), inference(assume_negation,[status(cth)],[t62_funct_2])).
% 0.20/0.38  cnf(c_0_29, plain, (r1_tarski(X1,k2_enumset1(X3,X3,X3,X2))|X1!=k2_enumset1(X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_24]), c_0_25]), c_0_25])).
% 0.20/0.38  cnf(c_0_30, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.38  cnf(c_0_31, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.38  fof(c_0_32, negated_conjecture, (((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,k1_tarski(esk4_0),esk5_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk4_0),esk5_0))))&(esk5_0!=k1_xboole_0&k2_relset_1(k1_tarski(esk4_0),esk5_0,esk6_0)!=k1_tarski(k1_funct_1(esk6_0,esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).
% 0.20/0.38  cnf(c_0_33, plain, (r1_tarski(X1,k2_tarski(X2,X3))|X1!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_34, plain, (r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X1))), inference(er,[status(thm)],[c_0_29])).
% 0.20/0.38  cnf(c_0_35, plain, (r2_hidden(X1,X2)|~v4_relat_1(X3,X2)|~v1_relat_1(X3)|~r2_hidden(X1,k1_relat_1(X3))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.38  cnf(c_0_36, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.38  fof(c_0_37, plain, ![X37, X38, X39]:((v4_relat_1(X39,X37)|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))&(v5_relat_1(X39,X38)|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.20/0.38  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk4_0),esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.38  fof(c_0_39, plain, ![X34, X35, X36]:(~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|v1_relat_1(X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.20/0.38  cnf(c_0_40, plain, (r1_tarski(X1,k2_enumset1(X2,X2,X2,X3))|X1!=k2_enumset1(X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_23]), c_0_24]), c_0_24]), c_0_25]), c_0_25])).
% 0.20/0.38  cnf(c_0_41, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X2,X3))|~r2_hidden(X1,k2_enumset1(X3,X3,X3,X3))), inference(spm,[status(thm)],[c_0_30, c_0_34])).
% 0.20/0.38  cnf(c_0_42, plain, (r2_hidden(esk1_2(k1_relat_1(X1),X2),X3)|r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X3)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.38  cnf(c_0_43, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.38  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_23]), c_0_24]), c_0_25])).
% 0.20/0.38  cnf(c_0_45, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.38  fof(c_0_46, plain, ![X30, X31]:(~v1_relat_1(X31)|~v1_funct_1(X31)|(k1_relat_1(X31)!=k1_tarski(X30)|k2_relat_1(X31)=k1_tarski(k1_funct_1(X31,X30)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_funct_1])])).
% 0.20/0.38  cnf(c_0_47, plain, (r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2))), inference(er,[status(thm)],[c_0_40])).
% 0.20/0.38  cnf(c_0_48, plain, (r2_hidden(esk1_2(k1_relat_1(X1),X2),k2_enumset1(X3,X3,X3,X4))|r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,k2_enumset1(X4,X4,X4,X4))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.38  cnf(c_0_49, negated_conjecture, (v4_relat_1(esk6_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.20/0.38  cnf(c_0_50, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_45, c_0_44])).
% 0.20/0.38  cnf(c_0_51, negated_conjecture, (k2_relset_1(k1_tarski(esk4_0),esk5_0,esk6_0)!=k1_tarski(k1_funct_1(esk6_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.38  cnf(c_0_52, plain, (k2_relat_1(X1)=k1_tarski(k1_funct_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|k1_relat_1(X1)!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.38  fof(c_0_53, plain, ![X12]:r1_tarski(k1_xboole_0,X12), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.38  cnf(c_0_54, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X2,X3))|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))), inference(spm,[status(thm)],[c_0_30, c_0_47])).
% 0.20/0.38  cnf(c_0_55, negated_conjecture, (r2_hidden(esk1_2(k1_relat_1(esk6_0),X1),k2_enumset1(X2,X2,X2,esk4_0))|r1_tarski(k1_relat_1(esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])])).
% 0.20/0.38  cnf(c_0_56, negated_conjecture, (k2_relset_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0,esk6_0)!=k2_enumset1(k1_funct_1(esk6_0,esk4_0),k1_funct_1(esk6_0,esk4_0),k1_funct_1(esk6_0,esk4_0),k1_funct_1(esk6_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_23]), c_0_23]), c_0_24]), c_0_24]), c_0_25]), c_0_25])).
% 0.20/0.38  cnf(c_0_57, plain, (k2_relat_1(X1)=k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2))|k1_relat_1(X1)!=k2_enumset1(X2,X2,X2,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_23]), c_0_23]), c_0_24]), c_0_24]), c_0_25]), c_0_25])).
% 0.20/0.38  cnf(c_0_58, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.38  fof(c_0_59, plain, ![X40, X41, X42]:(~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))|k2_relset_1(X40,X41,X42)=k2_relat_1(X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.20/0.38  cnf(c_0_60, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.20/0.38  fof(c_0_61, plain, ![X43, X44, X45, X47, X48]:(((r2_hidden(esk2_3(X43,X44,X45),X44)|k1_relset_1(X44,X43,X45)=X44|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X44,X43))))&(~r2_hidden(k4_tarski(esk2_3(X43,X44,X45),X47),X45)|k1_relset_1(X44,X43,X45)=X44|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X44,X43)))))&(k1_relset_1(X44,X43,X45)!=X44|(~r2_hidden(X48,X44)|r2_hidden(k4_tarski(X48,esk3_4(X43,X44,X45,X48)),X45))|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X44,X43))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_relset_1])])])])])])).
% 0.20/0.38  fof(c_0_62, plain, ![X23]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X23)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.20/0.38  cnf(c_0_63, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|X1=k1_tarski(X3)|X1=k2_tarski(X2,X3)|~r1_tarski(X1,k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_64, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.38  cnf(c_0_65, negated_conjecture, (r2_hidden(esk1_2(k1_relat_1(esk6_0),X1),k2_enumset1(esk4_0,esk4_0,esk4_0,X2))|r1_tarski(k1_relat_1(esk6_0),X1)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.20/0.38  cnf(c_0_66, negated_conjecture, (k2_relset_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0,esk6_0)!=k2_relat_1(esk6_0)|k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)!=k1_relat_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58]), c_0_50])])).
% 0.20/0.38  cnf(c_0_67, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.38  fof(c_0_68, plain, ![X32, X33]:(~r2_hidden(X32,X33)|~r1_tarski(X33,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.20/0.38  cnf(c_0_69, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_30, c_0_60])).
% 0.20/0.38  cnf(c_0_70, plain, (r2_hidden(k4_tarski(X4,esk3_4(X2,X1,X3,X4)),X3)|k1_relset_1(X1,X2,X3)!=X1|~r2_hidden(X4,X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.20/0.38  cnf(c_0_71, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.20/0.38  cnf(c_0_72, plain, (X1=k1_xboole_0|X1=k2_enumset1(X3,X3,X3,X3)|X1=k2_enumset1(X2,X2,X2,X3)|X1=k2_enumset1(X2,X2,X2,X2)|~r1_tarski(X1,k2_enumset1(X2,X2,X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_23]), c_0_23]), c_0_24]), c_0_24]), c_0_24]), c_0_24]), c_0_25]), c_0_25]), c_0_25]), c_0_25])).
% 0.20/0.38  cnf(c_0_73, negated_conjecture, (r1_tarski(k1_relat_1(esk6_0),k2_enumset1(esk4_0,esk4_0,esk4_0,X1))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.20/0.38  cnf(c_0_74, negated_conjecture, (k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)!=k1_relat_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_44])])).
% 0.20/0.38  cnf(c_0_75, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.20/0.38  cnf(c_0_76, plain, (r2_hidden(k4_tarski(X1,esk3_4(X2,X3,k1_xboole_0,X1)),X4)|k1_relset_1(X3,X2,k1_xboole_0)!=X3|~r2_hidden(X1,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71])])).
% 0.20/0.38  fof(c_0_77, plain, ![X29]:((k1_relat_1(X29)!=k1_xboole_0|X29=k1_xboole_0|~v1_relat_1(X29))&(k2_relat_1(X29)!=k1_xboole_0|X29=k1_xboole_0|~v1_relat_1(X29))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.20/0.38  cnf(c_0_78, negated_conjecture, (k2_enumset1(esk4_0,esk4_0,esk4_0,X1)=k1_relat_1(esk6_0)|k2_enumset1(X1,X1,X1,X1)=k1_relat_1(esk6_0)|k1_relat_1(esk6_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_74])).
% 0.20/0.38  cnf(c_0_79, plain, (k1_relset_1(X1,X2,k1_xboole_0)!=X1|~r2_hidden(X3,X1)|~r1_tarski(X4,k4_tarski(X3,esk3_4(X2,X1,k1_xboole_0,X3)))), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.20/0.38  fof(c_0_80, plain, ![X50, X51, X52]:((((~v1_funct_2(X52,X50,X51)|X50=k1_relset_1(X50,X51,X52)|X51=k1_xboole_0|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))))&(X50!=k1_relset_1(X50,X51,X52)|v1_funct_2(X52,X50,X51)|X51=k1_xboole_0|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))))&((~v1_funct_2(X52,X50,X51)|X50=k1_relset_1(X50,X51,X52)|X50!=k1_xboole_0|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))))&(X50!=k1_relset_1(X50,X51,X52)|v1_funct_2(X52,X50,X51)|X50!=k1_xboole_0|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))))))&((~v1_funct_2(X52,X50,X51)|X52=k1_xboole_0|X50=k1_xboole_0|X51!=k1_xboole_0|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))))&(X52!=k1_xboole_0|v1_funct_2(X52,X50,X51)|X50=k1_xboole_0|X51!=k1_xboole_0|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.20/0.38  cnf(c_0_81, negated_conjecture, (v1_funct_2(esk6_0,k1_tarski(esk4_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.38  cnf(c_0_82, plain, (X1=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.20/0.38  cnf(c_0_83, negated_conjecture, (k1_relat_1(esk6_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_78]), c_0_74])).
% 0.20/0.38  cnf(c_0_84, plain, (k1_relset_1(X1,X2,k1_xboole_0)!=X1|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_79, c_0_60])).
% 0.20/0.38  cnf(c_0_85, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.20/0.38  cnf(c_0_86, negated_conjecture, (v1_funct_2(esk6_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_23]), c_0_24]), c_0_25])).
% 0.20/0.38  cnf(c_0_87, negated_conjecture, (esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_50])])).
% 0.20/0.38  cnf(c_0_88, plain, (X1=k1_xboole_0|~v1_funct_2(k1_xboole_0,X2,X1)|~r2_hidden(X3,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_71])])).
% 0.20/0.38  cnf(c_0_89, negated_conjecture, (v1_funct_2(k1_xboole_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)), inference(rw,[status(thm)],[c_0_86, c_0_87])).
% 0.20/0.38  cnf(c_0_90, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.38  fof(c_0_91, plain, ![X13]:(~r1_tarski(X13,k1_xboole_0)|X13=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.20/0.38  cnf(c_0_92, negated_conjecture, (~r2_hidden(X1,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_90])).
% 0.20/0.38  cnf(c_0_93, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_91])).
% 0.20/0.38  cnf(c_0_94, negated_conjecture, (r1_tarski(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_92, c_0_36])).
% 0.20/0.38  cnf(c_0_95, negated_conjecture, (k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_74, c_0_83])).
% 0.20/0.38  cnf(c_0_96, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_95]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 97
% 0.20/0.38  # Proof object clause steps            : 60
% 0.20/0.38  # Proof object formula steps           : 37
% 0.20/0.38  # Proof object conjectures             : 26
% 0.20/0.38  # Proof object clause conjectures      : 23
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 26
% 0.20/0.38  # Proof object initial formulas used   : 18
% 0.20/0.38  # Proof object generating inferences   : 23
% 0.20/0.38  # Proof object simplifying inferences  : 59
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 19
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 39
% 0.20/0.38  # Removed in clause preprocessing      : 3
% 0.20/0.38  # Initial clauses in saturation        : 36
% 0.20/0.38  # Processed clauses                    : 170
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 50
% 0.20/0.38  # ...remaining for further processing  : 120
% 0.20/0.38  # Other redundant clauses eliminated   : 9
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 14
% 0.20/0.38  # Backward-rewritten                   : 26
% 0.20/0.38  # Generated clauses                    : 271
% 0.20/0.38  # ...of the previous two non-trivial   : 242
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 261
% 0.20/0.38  # Factorizations                       : 2
% 0.20/0.38  # Equation resolutions                 : 9
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 72
% 0.20/0.38  #    Positive orientable unit clauses  : 13
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 7
% 0.20/0.38  #    Non-unit-clauses                  : 52
% 0.20/0.38  # Current number of unprocessed clauses: 64
% 0.20/0.38  # ...number of literals in the above   : 268
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 43
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 951
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 604
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 51
% 0.20/0.38  # Unit Clause-clause subsumption calls : 65
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 10
% 0.20/0.38  # BW rewrite match successes           : 3
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 6485
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.037 s
% 0.20/0.38  # System time              : 0.006 s
% 0.20/0.38  # Total time               : 0.042 s
% 0.20/0.38  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
