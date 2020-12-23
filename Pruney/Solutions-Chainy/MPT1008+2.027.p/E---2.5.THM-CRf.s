%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:04:33 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 583 expanded)
%              Number of clauses        :   56 ( 235 expanded)
%              Number of leaves         :   20 ( 165 expanded)
%              Depth                    :   18
%              Number of atoms          :  281 (1169 expanded)
%              Number of equality atoms :  130 ( 621 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   25 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t62_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,k1_tarski(X1),X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
     => ( X2 != k1_xboole_0
       => k2_relset_1(k1_tarski(X1),X2,X3) = k1_tarski(k1_funct_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

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

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t142_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r1_tarski(X4,k1_enumset1(X1,X2,X3))
    <=> ~ ( X4 != k1_xboole_0
          & X4 != k1_tarski(X1)
          & X4 != k1_tarski(X2)
          & X4 != k1_tarski(X3)
          & X4 != k2_tarski(X1,X2)
          & X4 != k2_tarski(X2,X3)
          & X4 != k2_tarski(X1,X3)
          & X4 != k1_enumset1(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_zfmisc_1)).

fof(t87_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(t6_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_hidden(X3,X1)
       => ( X2 = k1_xboole_0
          | r2_hidden(k1_funct_1(X4,X3),k2_relset_1(X1,X2,X4)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
       => ( X2 != k1_xboole_0
         => k2_relset_1(k1_tarski(X1),X2,X3) = k1_tarski(k1_funct_1(X3,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t62_funct_2])).

fof(c_0_21,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,k1_tarski(esk3_0),esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk3_0),esk4_0)))
    & esk4_0 != k1_xboole_0
    & k2_relset_1(k1_tarski(esk3_0),esk4_0,esk5_0) != k1_tarski(k1_funct_1(esk5_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

fof(c_0_22,plain,(
    ! [X18] : k2_tarski(X18,X18) = k1_tarski(X18) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_23,plain,(
    ! [X19,X20] : k1_enumset1(X19,X19,X20) = k2_tarski(X19,X20) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_24,plain,(
    ! [X21,X22,X23] : k2_enumset1(X21,X21,X22,X23) = k1_enumset1(X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_25,plain,(
    ! [X47,X48,X49] :
      ( ( v4_relat_1(X49,X47)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))) )
      & ( v5_relat_1(X49,X48)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk3_0),esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_30,plain,(
    ! [X44,X45,X46] :
      ( ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))
      | v1_relat_1(X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_31,plain,(
    ! [X40,X41] :
      ( ~ v1_relat_1(X41)
      | ~ v1_funct_1(X41)
      | k1_relat_1(X41) != k1_tarski(X40)
      | k2_relat_1(X41) = k1_tarski(k1_funct_1(X41,X40)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_funct_1])])).

fof(c_0_32,plain,(
    ! [X36,X37] :
      ( ~ v1_relat_1(X37)
      | ~ v4_relat_1(X37,X36)
      | X37 = k7_relat_1(X37,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_33,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_35,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( k2_relset_1(k1_tarski(esk3_0),esk4_0,esk5_0) != k1_tarski(k1_funct_1(esk5_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_37,plain,
    ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_relat_1(X1) != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_38,plain,(
    ! [X53,X54,X55] :
      ( ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54)))
      | k2_relset_1(X53,X54,X55) = k2_relat_1(X55) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_39,plain,(
    ! [X26,X27,X28,X29] :
      ( ( ~ r1_tarski(X29,k1_enumset1(X26,X27,X28))
        | X29 = k1_xboole_0
        | X29 = k1_tarski(X26)
        | X29 = k1_tarski(X27)
        | X29 = k1_tarski(X28)
        | X29 = k2_tarski(X26,X27)
        | X29 = k2_tarski(X27,X28)
        | X29 = k2_tarski(X26,X28)
        | X29 = k1_enumset1(X26,X27,X28) )
      & ( X29 != k1_xboole_0
        | r1_tarski(X29,k1_enumset1(X26,X27,X28)) )
      & ( X29 != k1_tarski(X26)
        | r1_tarski(X29,k1_enumset1(X26,X27,X28)) )
      & ( X29 != k1_tarski(X27)
        | r1_tarski(X29,k1_enumset1(X26,X27,X28)) )
      & ( X29 != k1_tarski(X28)
        | r1_tarski(X29,k1_enumset1(X26,X27,X28)) )
      & ( X29 != k2_tarski(X26,X27)
        | r1_tarski(X29,k1_enumset1(X26,X27,X28)) )
      & ( X29 != k2_tarski(X27,X28)
        | r1_tarski(X29,k1_enumset1(X26,X27,X28)) )
      & ( X29 != k2_tarski(X26,X28)
        | r1_tarski(X29,k1_enumset1(X26,X27,X28)) )
      & ( X29 != k1_enumset1(X26,X27,X28)
        | r1_tarski(X29,k1_enumset1(X26,X27,X28)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t142_zfmisc_1])])])).

fof(c_0_40,plain,(
    ! [X38,X39] :
      ( ~ v1_relat_1(X39)
      | r1_tarski(k1_relat_1(k7_relat_1(X39,X38)),X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

cnf(c_0_41,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( v4_relat_1(esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( k2_relset_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0,esk5_0) != k2_enumset1(k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_27]),c_0_27]),c_0_28]),c_0_28]),c_0_29]),c_0_29])).

cnf(c_0_45,plain,
    ( k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2))
    | k1_relat_1(X1) != k2_enumset1(X2,X2,X2,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_27]),c_0_27]),c_0_28]),c_0_28]),c_0_29]),c_0_29])).

cnf(c_0_46,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_47,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_48,plain,(
    ! [X56,X57,X58] :
      ( ~ v1_relat_1(X58)
      | ~ r1_tarski(k1_relat_1(X58),X56)
      | ~ r1_tarski(k2_relat_1(X58),X57)
      | m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

fof(c_0_49,plain,(
    ! [X24,X25] :
      ( ( k2_zfmisc_1(X24,X25) != k1_xboole_0
        | X24 = k1_xboole_0
        | X25 = k1_xboole_0 )
      & ( X24 != k1_xboole_0
        | k2_zfmisc_1(X24,X25) = k1_xboole_0 )
      & ( X25 != k1_xboole_0
        | k2_zfmisc_1(X24,X25) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_50,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | X1 = k1_tarski(X3)
    | X1 = k1_tarski(X4)
    | X1 = k2_tarski(X2,X3)
    | X1 = k2_tarski(X3,X4)
    | X1 = k2_tarski(X2,X4)
    | X1 = k1_enumset1(X2,X3,X4)
    | ~ r1_tarski(X1,k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_51,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_52,negated_conjecture,
    ( k7_relat_1(esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])])).

cnf(c_0_53,negated_conjecture,
    ( k2_relset_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0,esk5_0) != k2_relat_1(esk5_0)
    | k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) != k1_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])]),c_0_43])])).

cnf(c_0_54,negated_conjecture,
    ( k2_relset_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0,esk5_0) = k2_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_34])).

fof(c_0_55,plain,(
    ! [X31,X32] :
      ( ( ~ m1_subset_1(X31,k1_zfmisc_1(X32))
        | r1_tarski(X31,X32) )
      & ( ~ r1_tarski(X31,X32)
        | m1_subset_1(X31,k1_zfmisc_1(X32)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_56,plain,(
    ! [X30] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X30)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_57,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_58,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_enumset1(X4,X4,X4,X4)
    | X1 = k2_enumset1(X3,X3,X3,X4)
    | X1 = k2_enumset1(X3,X3,X3,X3)
    | X1 = k2_enumset1(X2,X2,X3,X4)
    | X1 = k2_enumset1(X2,X2,X2,X4)
    | X1 = k2_enumset1(X2,X2,X2,X3)
    | X1 = k2_enumset1(X2,X2,X2,X2)
    | ~ r1_tarski(X1,k2_enumset1(X2,X2,X3,X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_27]),c_0_27]),c_0_27]),c_0_28]),c_0_28]),c_0_28]),c_0_28]),c_0_28]),c_0_28]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_29])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk5_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_43])])).

cnf(c_0_61,negated_conjecture,
    ( k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) != k1_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_54])])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_63,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

fof(c_0_64,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_65,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | X2 != k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_66,negated_conjecture,
    ( k1_relat_1(esk5_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])).

cnf(c_0_67,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))
    | X1 != k1_xboole_0
    | ~ r1_tarski(k2_relat_1(esk5_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_43]),c_0_67])])).

cnf(c_0_70,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_68])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(er,[status(thm)],[c_0_71])).

cnf(c_0_73,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(esk5_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_72])).

fof(c_0_75,plain,(
    ! [X9,X10,X11,X12,X13,X14,X15,X16] :
      ( ( ~ r2_hidden(X12,X11)
        | X12 = X9
        | X12 = X10
        | X11 != k2_tarski(X9,X10) )
      & ( X13 != X9
        | r2_hidden(X13,X11)
        | X11 != k2_tarski(X9,X10) )
      & ( X13 != X10
        | r2_hidden(X13,X11)
        | X11 != k2_tarski(X9,X10) )
      & ( esk1_3(X14,X15,X16) != X14
        | ~ r2_hidden(esk1_3(X14,X15,X16),X16)
        | X16 = k2_tarski(X14,X15) )
      & ( esk1_3(X14,X15,X16) != X15
        | ~ r2_hidden(esk1_3(X14,X15,X16),X16)
        | X16 = k2_tarski(X14,X15) )
      & ( r2_hidden(esk1_3(X14,X15,X16),X16)
        | esk1_3(X14,X15,X16) = X14
        | esk1_3(X14,X15,X16) = X15
        | X16 = k2_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_76,plain,(
    ! [X62,X63,X64,X65] :
      ( ~ v1_funct_1(X65)
      | ~ v1_funct_2(X65,X62,X63)
      | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X62,X63)))
      | ~ r2_hidden(X64,X62)
      | X63 = k1_xboole_0
      | r2_hidden(k1_funct_1(X65,X64),k2_relset_1(X62,X63,X65)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_funct_2])])).

cnf(c_0_77,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_78,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_67])])).

cnf(c_0_79,negated_conjecture,
    ( v1_funct_2(esk5_0,k1_tarski(esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_80,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_81,plain,
    ( X3 = k1_xboole_0
    | r2_hidden(k1_funct_1(X1,X4),k2_relset_1(X2,X3,X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_82,plain,
    ( k2_relset_1(X1,X2,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_63]),c_0_77])).

cnf(c_0_83,negated_conjecture,
    ( v1_funct_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_46,c_0_78])).

cnf(c_0_84,negated_conjecture,
    ( v1_funct_2(esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_85,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X4,X4,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_28]),c_0_29])).

cnf(c_0_86,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(k1_funct_1(k1_xboole_0,X2),k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,X3,X1)
    | ~ r2_hidden(X2,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_63])]),c_0_83])])).

cnf(c_0_87,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[c_0_84,c_0_78])).

cnf(c_0_88,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_89,plain,
    ( r2_hidden(X1,X2)
    | X2 != k2_enumset1(X3,X3,X3,X1) ),
    inference(er,[status(thm)],[c_0_85])).

fof(c_0_90,plain,(
    ! [X42,X43] :
      ( ~ r2_hidden(X42,X43)
      | ~ r1_tarski(X43,X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(k1_funct_1(k1_xboole_0,X1),k1_xboole_0)
    | ~ r2_hidden(X1,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88])).

cnf(c_0_92,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X2,X1)) ),
    inference(er,[status(thm)],[c_0_89])).

cnf(c_0_93,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_94,negated_conjecture,
    ( r2_hidden(k1_funct_1(k1_xboole_0,esk3_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_95,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_67])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:49:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.49  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_URBAN_S0Y
% 0.20/0.49  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.49  #
% 0.20/0.49  # Preprocessing time       : 0.043 s
% 0.20/0.49  
% 0.20/0.49  # Proof found!
% 0.20/0.49  # SZS status Theorem
% 0.20/0.49  # SZS output start CNFRefutation
% 0.20/0.49  fof(t62_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>k2_relset_1(k1_tarski(X1),X2,X3)=k1_tarski(k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 0.20/0.49  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.49  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.49  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.49  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.20/0.49  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.20/0.49  fof(t14_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 0.20/0.49  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 0.20/0.49  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.20/0.49  fof(t142_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r1_tarski(X4,k1_enumset1(X1,X2,X3))<=>~((((((((X4!=k1_xboole_0&X4!=k1_tarski(X1))&X4!=k1_tarski(X2))&X4!=k1_tarski(X3))&X4!=k2_tarski(X1,X2))&X4!=k2_tarski(X2,X3))&X4!=k2_tarski(X1,X3))&X4!=k1_enumset1(X1,X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 0.20/0.49  fof(t87_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 0.20/0.49  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 0.20/0.49  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.20/0.49  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.49  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.20/0.49  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.49  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.20/0.49  fof(t6_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_hidden(X3,X1)=>(X2=k1_xboole_0|r2_hidden(k1_funct_1(X4,X3),k2_relset_1(X1,X2,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 0.20/0.49  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.20/0.49  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.20/0.49  fof(c_0_20, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>k2_relset_1(k1_tarski(X1),X2,X3)=k1_tarski(k1_funct_1(X3,X1))))), inference(assume_negation,[status(cth)],[t62_funct_2])).
% 0.20/0.49  fof(c_0_21, negated_conjecture, (((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,k1_tarski(esk3_0),esk4_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk3_0),esk4_0))))&(esk4_0!=k1_xboole_0&k2_relset_1(k1_tarski(esk3_0),esk4_0,esk5_0)!=k1_tarski(k1_funct_1(esk5_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.20/0.49  fof(c_0_22, plain, ![X18]:k2_tarski(X18,X18)=k1_tarski(X18), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.49  fof(c_0_23, plain, ![X19, X20]:k1_enumset1(X19,X19,X20)=k2_tarski(X19,X20), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.49  fof(c_0_24, plain, ![X21, X22, X23]:k2_enumset1(X21,X21,X22,X23)=k1_enumset1(X21,X22,X23), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.49  fof(c_0_25, plain, ![X47, X48, X49]:((v4_relat_1(X49,X47)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))))&(v5_relat_1(X49,X48)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.20/0.49  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk3_0),esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.49  cnf(c_0_27, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.49  cnf(c_0_28, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.49  cnf(c_0_29, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.49  fof(c_0_30, plain, ![X44, X45, X46]:(~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))|v1_relat_1(X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.20/0.49  fof(c_0_31, plain, ![X40, X41]:(~v1_relat_1(X41)|~v1_funct_1(X41)|(k1_relat_1(X41)!=k1_tarski(X40)|k2_relat_1(X41)=k1_tarski(k1_funct_1(X41,X40)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_funct_1])])).
% 0.20/0.49  fof(c_0_32, plain, ![X36, X37]:(~v1_relat_1(X37)|~v4_relat_1(X37,X36)|X37=k7_relat_1(X37,X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.20/0.49  cnf(c_0_33, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.49  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])).
% 0.20/0.49  cnf(c_0_35, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.49  cnf(c_0_36, negated_conjecture, (k2_relset_1(k1_tarski(esk3_0),esk4_0,esk5_0)!=k1_tarski(k1_funct_1(esk5_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.49  cnf(c_0_37, plain, (k2_relat_1(X1)=k1_tarski(k1_funct_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|k1_relat_1(X1)!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.49  fof(c_0_38, plain, ![X53, X54, X55]:(~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54)))|k2_relset_1(X53,X54,X55)=k2_relat_1(X55)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.20/0.49  fof(c_0_39, plain, ![X26, X27, X28, X29]:((~r1_tarski(X29,k1_enumset1(X26,X27,X28))|(X29=k1_xboole_0|X29=k1_tarski(X26)|X29=k1_tarski(X27)|X29=k1_tarski(X28)|X29=k2_tarski(X26,X27)|X29=k2_tarski(X27,X28)|X29=k2_tarski(X26,X28)|X29=k1_enumset1(X26,X27,X28)))&((((((((X29!=k1_xboole_0|r1_tarski(X29,k1_enumset1(X26,X27,X28)))&(X29!=k1_tarski(X26)|r1_tarski(X29,k1_enumset1(X26,X27,X28))))&(X29!=k1_tarski(X27)|r1_tarski(X29,k1_enumset1(X26,X27,X28))))&(X29!=k1_tarski(X28)|r1_tarski(X29,k1_enumset1(X26,X27,X28))))&(X29!=k2_tarski(X26,X27)|r1_tarski(X29,k1_enumset1(X26,X27,X28))))&(X29!=k2_tarski(X27,X28)|r1_tarski(X29,k1_enumset1(X26,X27,X28))))&(X29!=k2_tarski(X26,X28)|r1_tarski(X29,k1_enumset1(X26,X27,X28))))&(X29!=k1_enumset1(X26,X27,X28)|r1_tarski(X29,k1_enumset1(X26,X27,X28))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t142_zfmisc_1])])])).
% 0.20/0.49  fof(c_0_40, plain, ![X38, X39]:(~v1_relat_1(X39)|r1_tarski(k1_relat_1(k7_relat_1(X39,X38)),X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).
% 0.20/0.49  cnf(c_0_41, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.49  cnf(c_0_42, negated_conjecture, (v4_relat_1(esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.49  cnf(c_0_43, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_35, c_0_34])).
% 0.20/0.49  cnf(c_0_44, negated_conjecture, (k2_relset_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0,esk5_0)!=k2_enumset1(k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_27]), c_0_27]), c_0_28]), c_0_28]), c_0_29]), c_0_29])).
% 0.20/0.49  cnf(c_0_45, plain, (k2_relat_1(X1)=k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2))|k1_relat_1(X1)!=k2_enumset1(X2,X2,X2,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_27]), c_0_27]), c_0_28]), c_0_28]), c_0_29]), c_0_29])).
% 0.20/0.49  cnf(c_0_46, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.49  cnf(c_0_47, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.49  fof(c_0_48, plain, ![X56, X57, X58]:(~v1_relat_1(X58)|(~r1_tarski(k1_relat_1(X58),X56)|~r1_tarski(k2_relat_1(X58),X57)|m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 0.20/0.49  fof(c_0_49, plain, ![X24, X25]:((k2_zfmisc_1(X24,X25)!=k1_xboole_0|(X24=k1_xboole_0|X25=k1_xboole_0))&((X24!=k1_xboole_0|k2_zfmisc_1(X24,X25)=k1_xboole_0)&(X25!=k1_xboole_0|k2_zfmisc_1(X24,X25)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.20/0.49  cnf(c_0_50, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|X1=k1_tarski(X3)|X1=k1_tarski(X4)|X1=k2_tarski(X2,X3)|X1=k2_tarski(X3,X4)|X1=k2_tarski(X2,X4)|X1=k1_enumset1(X2,X3,X4)|~r1_tarski(X1,k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.49  cnf(c_0_51, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.49  cnf(c_0_52, negated_conjecture, (k7_relat_1(esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])])).
% 0.20/0.49  cnf(c_0_53, negated_conjecture, (k2_relset_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0,esk5_0)!=k2_relat_1(esk5_0)|k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)!=k1_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])]), c_0_43])])).
% 0.20/0.49  cnf(c_0_54, negated_conjecture, (k2_relset_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0,esk5_0)=k2_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_47, c_0_34])).
% 0.20/0.49  fof(c_0_55, plain, ![X31, X32]:((~m1_subset_1(X31,k1_zfmisc_1(X32))|r1_tarski(X31,X32))&(~r1_tarski(X31,X32)|m1_subset_1(X31,k1_zfmisc_1(X32)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.49  fof(c_0_56, plain, ![X30]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X30)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.20/0.49  cnf(c_0_57, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.49  cnf(c_0_58, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.49  cnf(c_0_59, plain, (X1=k1_xboole_0|X1=k2_enumset1(X4,X4,X4,X4)|X1=k2_enumset1(X3,X3,X3,X4)|X1=k2_enumset1(X3,X3,X3,X3)|X1=k2_enumset1(X2,X2,X3,X4)|X1=k2_enumset1(X2,X2,X2,X4)|X1=k2_enumset1(X2,X2,X2,X3)|X1=k2_enumset1(X2,X2,X2,X2)|~r1_tarski(X1,k2_enumset1(X2,X2,X3,X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_27]), c_0_27]), c_0_27]), c_0_28]), c_0_28]), c_0_28]), c_0_28]), c_0_28]), c_0_28]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_29])).
% 0.20/0.49  cnf(c_0_60, negated_conjecture, (r1_tarski(k1_relat_1(esk5_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_43])])).
% 0.20/0.49  cnf(c_0_61, negated_conjecture, (k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)!=k1_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_54])])).
% 0.20/0.49  cnf(c_0_62, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.49  cnf(c_0_63, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.20/0.49  fof(c_0_64, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.49  cnf(c_0_65, plain, (m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))|X2!=k1_xboole_0|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.20/0.49  cnf(c_0_66, negated_conjecture, (k1_relat_1(esk5_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61])).
% 0.20/0.49  cnf(c_0_67, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.20/0.49  cnf(c_0_68, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.20/0.49  cnf(c_0_69, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))|X1!=k1_xboole_0|~r1_tarski(k2_relat_1(esk5_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_43]), c_0_67])])).
% 0.20/0.49  cnf(c_0_70, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_68])).
% 0.20/0.49  cnf(c_0_71, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.20/0.49  cnf(c_0_72, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))), inference(er,[status(thm)],[c_0_71])).
% 0.20/0.49  cnf(c_0_73, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.20/0.49  cnf(c_0_74, negated_conjecture, (r1_tarski(esk5_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_62, c_0_72])).
% 0.20/0.49  fof(c_0_75, plain, ![X9, X10, X11, X12, X13, X14, X15, X16]:(((~r2_hidden(X12,X11)|(X12=X9|X12=X10)|X11!=k2_tarski(X9,X10))&((X13!=X9|r2_hidden(X13,X11)|X11!=k2_tarski(X9,X10))&(X13!=X10|r2_hidden(X13,X11)|X11!=k2_tarski(X9,X10))))&(((esk1_3(X14,X15,X16)!=X14|~r2_hidden(esk1_3(X14,X15,X16),X16)|X16=k2_tarski(X14,X15))&(esk1_3(X14,X15,X16)!=X15|~r2_hidden(esk1_3(X14,X15,X16),X16)|X16=k2_tarski(X14,X15)))&(r2_hidden(esk1_3(X14,X15,X16),X16)|(esk1_3(X14,X15,X16)=X14|esk1_3(X14,X15,X16)=X15)|X16=k2_tarski(X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.20/0.49  fof(c_0_76, plain, ![X62, X63, X64, X65]:(~v1_funct_1(X65)|~v1_funct_2(X65,X62,X63)|~m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X62,X63)))|(~r2_hidden(X64,X62)|(X63=k1_xboole_0|r2_hidden(k1_funct_1(X65,X64),k2_relset_1(X62,X63,X65))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_funct_2])])).
% 0.20/0.49  cnf(c_0_77, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.20/0.49  cnf(c_0_78, negated_conjecture, (esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_67])])).
% 0.20/0.49  cnf(c_0_79, negated_conjecture, (v1_funct_2(esk5_0,k1_tarski(esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.49  cnf(c_0_80, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.20/0.49  cnf(c_0_81, plain, (X3=k1_xboole_0|r2_hidden(k1_funct_1(X1,X4),k2_relset_1(X2,X3,X1))|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.20/0.49  cnf(c_0_82, plain, (k2_relset_1(X1,X2,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_63]), c_0_77])).
% 0.20/0.49  cnf(c_0_83, negated_conjecture, (v1_funct_1(k1_xboole_0)), inference(rw,[status(thm)],[c_0_46, c_0_78])).
% 0.20/0.49  cnf(c_0_84, negated_conjecture, (v1_funct_2(esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_27]), c_0_28]), c_0_29])).
% 0.20/0.49  cnf(c_0_85, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X4,X4,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_28]), c_0_29])).
% 0.20/0.49  cnf(c_0_86, plain, (X1=k1_xboole_0|r2_hidden(k1_funct_1(k1_xboole_0,X2),k1_xboole_0)|~v1_funct_2(k1_xboole_0,X3,X1)|~r2_hidden(X2,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_63])]), c_0_83])])).
% 0.20/0.49  cnf(c_0_87, negated_conjecture, (v1_funct_2(k1_xboole_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)), inference(rw,[status(thm)],[c_0_84, c_0_78])).
% 0.20/0.49  cnf(c_0_88, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.49  cnf(c_0_89, plain, (r2_hidden(X1,X2)|X2!=k2_enumset1(X3,X3,X3,X1)), inference(er,[status(thm)],[c_0_85])).
% 0.20/0.49  fof(c_0_90, plain, ![X42, X43]:(~r2_hidden(X42,X43)|~r1_tarski(X43,X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.20/0.49  cnf(c_0_91, negated_conjecture, (r2_hidden(k1_funct_1(k1_xboole_0,X1),k1_xboole_0)|~r2_hidden(X1,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_88])).
% 0.20/0.49  cnf(c_0_92, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X2,X1))), inference(er,[status(thm)],[c_0_89])).
% 0.20/0.49  cnf(c_0_93, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.20/0.49  cnf(c_0_94, negated_conjecture, (r2_hidden(k1_funct_1(k1_xboole_0,esk3_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.20/0.49  cnf(c_0_95, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_67])]), ['proof']).
% 0.20/0.49  # SZS output end CNFRefutation
% 0.20/0.49  # Proof object total steps             : 96
% 0.20/0.49  # Proof object clause steps            : 56
% 0.20/0.49  # Proof object formula steps           : 40
% 0.20/0.49  # Proof object conjectures             : 29
% 0.20/0.49  # Proof object clause conjectures      : 26
% 0.20/0.49  # Proof object formula conjectures     : 3
% 0.20/0.49  # Proof object initial clauses used    : 25
% 0.20/0.49  # Proof object initial formulas used   : 20
% 0.20/0.49  # Proof object generating inferences   : 20
% 0.20/0.49  # Proof object simplifying inferences  : 65
% 0.20/0.49  # Training examples: 0 positive, 0 negative
% 0.20/0.49  # Parsed axioms                        : 25
% 0.20/0.49  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.49  # Initial clauses                      : 52
% 0.20/0.49  # Removed in clause preprocessing      : 3
% 0.20/0.49  # Initial clauses in saturation        : 49
% 0.20/0.49  # Processed clauses                    : 248
% 0.20/0.49  # ...of these trivial                  : 1
% 0.20/0.49  # ...subsumed                          : 46
% 0.20/0.49  # ...remaining for further processing  : 201
% 0.20/0.49  # Other redundant clauses eliminated   : 84
% 0.20/0.49  # Clauses deleted for lack of memory   : 0
% 0.20/0.49  # Backward-subsumed                    : 15
% 0.20/0.49  # Backward-rewritten                   : 34
% 0.20/0.49  # Generated clauses                    : 2173
% 0.20/0.49  # ...of the previous two non-trivial   : 1986
% 0.20/0.49  # Contextual simplify-reflections      : 0
% 0.20/0.49  # Paramodulations                      : 2058
% 0.20/0.49  # Factorizations                       : 10
% 0.20/0.49  # Equation resolutions                 : 105
% 0.20/0.49  # Propositional unsat checks           : 0
% 0.20/0.49  #    Propositional check models        : 0
% 0.20/0.49  #    Propositional check unsatisfiable : 0
% 0.20/0.49  #    Propositional clauses             : 0
% 0.20/0.49  #    Propositional clauses after purity: 0
% 0.20/0.49  #    Propositional unsat core size     : 0
% 0.20/0.49  #    Propositional preprocessing time  : 0.000
% 0.20/0.49  #    Propositional encoding time       : 0.000
% 0.20/0.49  #    Propositional solver time         : 0.000
% 0.20/0.49  #    Success case prop preproc time    : 0.000
% 0.20/0.49  #    Success case prop encoding time   : 0.000
% 0.20/0.49  #    Success case prop solver time     : 0.000
% 0.20/0.49  # Current number of processed clauses  : 148
% 0.20/0.49  #    Positive orientable unit clauses  : 29
% 0.20/0.49  #    Positive unorientable unit clauses: 0
% 0.20/0.49  #    Negative unit clauses             : 7
% 0.20/0.49  #    Non-unit-clauses                  : 112
% 0.20/0.49  # Current number of unprocessed clauses: 1769
% 0.20/0.49  # ...number of literals in the above   : 12525
% 0.20/0.49  # Current number of archived formulas  : 0
% 0.20/0.49  # Current number of archived clauses   : 52
% 0.20/0.49  # Clause-clause subsumption calls (NU) : 1444
% 0.20/0.49  # Rec. Clause-clause subsumption calls : 693
% 0.20/0.49  # Non-unit clause-clause subsumptions  : 50
% 0.20/0.49  # Unit Clause-clause subsumption calls : 122
% 0.20/0.49  # Rewrite failures with RHS unbound    : 0
% 0.20/0.49  # BW rewrite match attempts            : 27
% 0.20/0.49  # BW rewrite match successes           : 8
% 0.20/0.49  # Condensation attempts                : 0
% 0.20/0.49  # Condensation successes               : 0
% 0.20/0.49  # Termbank termtop insertions          : 42821
% 0.20/0.49  
% 0.20/0.49  # -------------------------------------------------
% 0.20/0.49  # User time                : 0.139 s
% 0.20/0.49  # System time              : 0.007 s
% 0.20/0.49  # Total time               : 0.146 s
% 0.20/0.49  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
