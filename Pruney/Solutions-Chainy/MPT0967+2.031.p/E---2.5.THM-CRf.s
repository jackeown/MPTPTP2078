%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:01:25 EST 2020

% Result     : Theorem 4.73s
% Output     : CNFRefutation 4.73s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 520 expanded)
%              Number of clauses        :   66 ( 224 expanded)
%              Number of leaves         :   16 ( 130 expanded)
%              Depth                    :   14
%              Number of atoms          :  278 (2214 expanded)
%              Number of equality atoms :   95 ( 574 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t9_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r1_tarski(X2,X3)
       => ( ( X2 = k1_xboole_0
            & X1 != k1_xboole_0 )
          | ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t79_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

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

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t118_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => ( r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
        & r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(fc10_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( r1_tarski(X2,X3)
         => ( ( X2 = k1_xboole_0
              & X1 != k1_xboole_0 )
            | ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t9_funct_2])).

fof(c_0_17,plain,(
    ! [X33,X34,X35] :
      ( ~ r2_hidden(X33,X34)
      | ~ m1_subset_1(X34,k1_zfmisc_1(X35))
      | m1_subset_1(X33,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_18,plain,(
    ! [X31,X32] :
      ( ( ~ m1_subset_1(X31,k1_zfmisc_1(X32))
        | r1_tarski(X31,X32) )
      & ( ~ r1_tarski(X31,X32)
        | m1_subset_1(X31,k1_zfmisc_1(X32)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_19,negated_conjecture,
    ( v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,esk4_0,esk5_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
    & r1_tarski(esk5_0,esk6_0)
    & ( esk5_0 != k1_xboole_0
      | esk4_0 = k1_xboole_0 )
    & ( ~ v1_funct_1(esk7_0)
      | ~ v1_funct_2(esk7_0,esk4_0,esk6_0)
      | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk6_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_20,plain,(
    ! [X21,X22] :
      ( ( k2_zfmisc_1(X21,X22) != k1_xboole_0
        | X21 = k1_xboole_0
        | X22 = k1_xboole_0 )
      & ( X21 != k1_xboole_0
        | k2_zfmisc_1(X21,X22) = k1_xboole_0 )
      & ( X22 != k1_xboole_0
        | k2_zfmisc_1(X21,X22) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_21,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,plain,(
    ! [X26,X27] :
      ( ~ r1_tarski(X26,X27)
      | r1_tarski(k1_zfmisc_1(X26),k1_zfmisc_1(X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).

fof(c_0_24,plain,(
    ! [X29,X30] :
      ( ~ m1_subset_1(X29,X30)
      | v1_xboole_0(X30)
      | r2_hidden(X29,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_25,plain,(
    ! [X28] : ~ v1_xboole_0(k1_zfmisc_1(X28)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( m1_subset_1(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,plain,
    ( r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_32,plain,(
    ! [X43,X44,X45] :
      ( ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
      | k1_relset_1(X43,X44,X45) = k1_relat_1(X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_33,plain,(
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

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k1_xboole_0))
    | esk5_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_35,plain,(
    ! [X18] : r1_tarski(k1_xboole_0,X18) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_36,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X3,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_26]),c_0_31])).

fof(c_0_38,plain,(
    ! [X23,X24,X25] :
      ( ( r1_tarski(k2_zfmisc_1(X23,X25),k2_zfmisc_1(X24,X25))
        | ~ r1_tarski(X23,X24) )
      & ( r1_tarski(k2_zfmisc_1(X25,X23),k2_zfmisc_1(X25,X24))
        | ~ r1_tarski(X23,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).

cnf(c_0_39,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_41,plain,(
    ! [X16,X17] :
      ( ( r1_tarski(X16,X17)
        | X16 != X17 )
      & ( r1_tarski(X17,X16)
        | X16 != X17 )
      & ( ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X17,X16)
        | X16 = X17 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_42,negated_conjecture,
    ( ~ v1_funct_1(esk7_0)
    | ~ v1_funct_2(esk7_0,esk4_0,esk6_0)
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_43,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk7_0,k1_zfmisc_1(k1_xboole_0))
    | esk5_0 != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_34]),c_0_31])).

cnf(c_0_45,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(X1))
    | ~ r1_tarski(k2_zfmisc_1(esk4_0,esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_48,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,plain,
    ( X1 = k1_relat_1(X2)
    | X1 != k1_xboole_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( v1_funct_2(esk7_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_51,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_52,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_53,plain,(
    ! [X15] :
      ( ~ v1_xboole_0(X15)
      | X15 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

fof(c_0_54,plain,(
    ! [X39] :
      ( ~ v1_xboole_0(X39)
      | v1_xboole_0(k1_relat_1(X39)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_relat_1])])).

cnf(c_0_55,negated_conjecture,
    ( ~ v1_funct_2(esk7_0,esk4_0,esk6_0)
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43])])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(X1))
    | esk5_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_44]),c_0_45])])).

cnf(c_0_57,plain,
    ( v1_funct_2(X1,X2,X3)
    | k1_relat_1(X1) != X2
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_39])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))
    | ~ r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_59,negated_conjecture,
    ( k1_relat_1(esk7_0) = esk4_0
    | esk4_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_26]),c_0_50])])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk7_0,k1_zfmisc_1(k1_xboole_0))
    | esk4_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_51])).

cnf(c_0_61,plain,
    ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X1,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_52,c_0_48])).

cnf(c_0_62,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_63,plain,
    ( v1_xboole_0(k1_relat_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_64,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_65,negated_conjecture,
    ( esk5_0 != k1_xboole_0
    | ~ v1_funct_2(esk7_0,esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_66,negated_conjecture,
    ( v1_funct_2(esk7_0,esk4_0,X1)
    | esk4_0 != k1_xboole_0
    | ~ r1_tarski(esk5_0,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_68,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(X1))
    | esk4_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_60]),c_0_45])])).

fof(c_0_70,plain,(
    ! [X40,X41,X42] :
      ( ~ v1_xboole_0(X40)
      | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X41,X40)))
      | v1_xboole_0(X42) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

cnf(c_0_71,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X3 != k1_xboole_0
    | ~ r1_tarski(X2,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_27]),c_0_45])])).

cnf(c_0_72,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_73,negated_conjecture,
    ( k1_relset_1(esk4_0,esk5_0,esk7_0) = esk4_0
    | esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_26]),c_0_50])])).

cnf(c_0_74,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])]),c_0_68])).

cnf(c_0_75,negated_conjecture,
    ( esk4_0 != k1_xboole_0
    | ~ v1_funct_2(esk7_0,esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_69])).

cnf(c_0_76,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_77,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_71,c_0_45])).

cnf(c_0_78,plain,
    ( k1_relset_1(X1,X2,X3) = k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_39,c_0_72])).

cnf(c_0_79,negated_conjecture,
    ( k1_relset_1(esk4_0,esk5_0,esk7_0) = esk4_0 ),
    inference(sr,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_66]),c_0_67])])).

cnf(c_0_81,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_76,c_0_22])).

cnf(c_0_82,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_77])).

cnf(c_0_83,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_84,plain,
    ( k1_relset_1(X1,X2,X3) = k1_relset_1(X4,X5,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_39])).

cnf(c_0_85,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_86,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_26])]),c_0_80])).

cnf(c_0_87,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_83])])).

cnf(c_0_88,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_89,negated_conjecture,
    ( k1_relset_1(X1,X2,esk7_0) = esk4_0
    | esk5_0 = k1_xboole_0
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_84]),c_0_26])])).

cnf(c_0_90,negated_conjecture,
    ( r1_tarski(esk7_0,k2_zfmisc_1(esk4_0,X1))
    | ~ r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_85,c_0_58])).

cnf(c_0_91,negated_conjecture,
    ( ~ r1_tarski(esk7_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_92,negated_conjecture,
    ( X1 = k1_xboole_0
    | v1_funct_2(esk7_0,esk4_0,X1)
    | k1_relset_1(esk4_0,X1,esk7_0) != esk4_0
    | ~ r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_88,c_0_58])).

cnf(c_0_93,negated_conjecture,
    ( k1_relset_1(esk4_0,X1,esk7_0) = esk4_0
    | ~ r1_tarski(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_58]),c_0_74])).

cnf(c_0_94,negated_conjecture,
    ( X1 != k1_xboole_0
    | ~ r1_tarski(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_27]),c_0_91])).

cnf(c_0_95,negated_conjecture,
    ( ~ v1_funct_2(esk7_0,esk4_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_58]),c_0_67])])).

cnf(c_0_96,negated_conjecture,
    ( v1_funct_2(esk7_0,esk4_0,X1)
    | ~ r1_tarski(esk5_0,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_94])).

cnf(c_0_97,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_67])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:02:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 4.73/4.95  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 4.73/4.95  # and selection function PSelectComplexExceptUniqMaxHorn.
% 4.73/4.95  #
% 4.73/4.95  # Preprocessing time       : 0.029 s
% 4.73/4.95  
% 4.73/4.95  # Proof found!
% 4.73/4.95  # SZS status Theorem
% 4.73/4.95  # SZS output start CNFRefutation
% 4.73/4.95  fof(t9_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X2,X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_2)).
% 4.73/4.95  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 4.73/4.95  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.73/4.95  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.73/4.95  fof(t79_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 4.73/4.95  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.73/4.95  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 4.73/4.95  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.73/4.95  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.73/4.95  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.73/4.95  fof(t118_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>(r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 4.73/4.95  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.73/4.95  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.73/4.95  fof(fc10_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_xboole_0(k1_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_relat_1)).
% 4.73/4.95  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 4.73/4.95  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.73/4.95  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X2,X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))))))), inference(assume_negation,[status(cth)],[t9_funct_2])).
% 4.73/4.95  fof(c_0_17, plain, ![X33, X34, X35]:(~r2_hidden(X33,X34)|~m1_subset_1(X34,k1_zfmisc_1(X35))|m1_subset_1(X33,X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 4.73/4.95  fof(c_0_18, plain, ![X31, X32]:((~m1_subset_1(X31,k1_zfmisc_1(X32))|r1_tarski(X31,X32))&(~r1_tarski(X31,X32)|m1_subset_1(X31,k1_zfmisc_1(X32)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 4.73/4.95  fof(c_0_19, negated_conjecture, (((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,esk4_0,esk5_0))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))))&(r1_tarski(esk5_0,esk6_0)&((esk5_0!=k1_xboole_0|esk4_0=k1_xboole_0)&(~v1_funct_1(esk7_0)|~v1_funct_2(esk7_0,esk4_0,esk6_0)|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk6_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 4.73/4.95  fof(c_0_20, plain, ![X21, X22]:((k2_zfmisc_1(X21,X22)!=k1_xboole_0|(X21=k1_xboole_0|X22=k1_xboole_0))&((X21!=k1_xboole_0|k2_zfmisc_1(X21,X22)=k1_xboole_0)&(X22!=k1_xboole_0|k2_zfmisc_1(X21,X22)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 4.73/4.95  cnf(c_0_21, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 4.73/4.95  cnf(c_0_22, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 4.73/4.95  fof(c_0_23, plain, ![X26, X27]:(~r1_tarski(X26,X27)|r1_tarski(k1_zfmisc_1(X26),k1_zfmisc_1(X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).
% 4.73/4.95  fof(c_0_24, plain, ![X29, X30]:(~m1_subset_1(X29,X30)|(v1_xboole_0(X30)|r2_hidden(X29,X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 4.73/4.95  fof(c_0_25, plain, ![X28]:~v1_xboole_0(k1_zfmisc_1(X28)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 4.73/4.95  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 4.73/4.95  cnf(c_0_27, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 4.73/4.95  cnf(c_0_28, plain, (m1_subset_1(X1,X2)|~r1_tarski(X3,X2)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 4.73/4.95  cnf(c_0_29, plain, (r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 4.73/4.95  cnf(c_0_30, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 4.73/4.95  cnf(c_0_31, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 4.73/4.95  fof(c_0_32, plain, ![X43, X44, X45]:(~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))|k1_relset_1(X43,X44,X45)=k1_relat_1(X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 4.73/4.95  fof(c_0_33, plain, ![X46, X47, X48]:((((~v1_funct_2(X48,X46,X47)|X46=k1_relset_1(X46,X47,X48)|X47=k1_xboole_0|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))))&(X46!=k1_relset_1(X46,X47,X48)|v1_funct_2(X48,X46,X47)|X47=k1_xboole_0|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))))&((~v1_funct_2(X48,X46,X47)|X46=k1_relset_1(X46,X47,X48)|X46!=k1_xboole_0|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))))&(X46!=k1_relset_1(X46,X47,X48)|v1_funct_2(X48,X46,X47)|X46!=k1_xboole_0|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))))))&((~v1_funct_2(X48,X46,X47)|X48=k1_xboole_0|X46=k1_xboole_0|X47!=k1_xboole_0|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))))&(X48!=k1_xboole_0|v1_funct_2(X48,X46,X47)|X46=k1_xboole_0|X47!=k1_xboole_0|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 4.73/4.95  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k1_xboole_0))|esk5_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 4.73/4.95  fof(c_0_35, plain, ![X18]:r1_tarski(k1_xboole_0,X18), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 4.73/4.95  cnf(c_0_36, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X3,X2)|~r2_hidden(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 4.73/4.95  cnf(c_0_37, negated_conjecture, (r2_hidden(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_26]), c_0_31])).
% 4.73/4.95  fof(c_0_38, plain, ![X23, X24, X25]:((r1_tarski(k2_zfmisc_1(X23,X25),k2_zfmisc_1(X24,X25))|~r1_tarski(X23,X24))&(r1_tarski(k2_zfmisc_1(X25,X23),k2_zfmisc_1(X25,X24))|~r1_tarski(X23,X24))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).
% 4.73/4.95  cnf(c_0_39, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 4.73/4.95  cnf(c_0_40, plain, (X2=k1_relset_1(X2,X3,X1)|~v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 4.73/4.95  fof(c_0_41, plain, ![X16, X17]:(((r1_tarski(X16,X17)|X16!=X17)&(r1_tarski(X17,X16)|X16!=X17))&(~r1_tarski(X16,X17)|~r1_tarski(X17,X16)|X16=X17)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 4.73/4.95  cnf(c_0_42, negated_conjecture, (~v1_funct_1(esk7_0)|~v1_funct_2(esk7_0,esk4_0,esk6_0)|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 4.73/4.95  cnf(c_0_43, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 4.73/4.95  cnf(c_0_44, negated_conjecture, (r2_hidden(esk7_0,k1_zfmisc_1(k1_xboole_0))|esk5_0!=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_34]), c_0_31])).
% 4.73/4.95  cnf(c_0_45, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 4.73/4.95  cnf(c_0_46, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 4.73/4.95  cnf(c_0_47, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(X1))|~r1_tarski(k2_zfmisc_1(esk4_0,esk5_0),X1)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 4.73/4.95  cnf(c_0_48, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 4.73/4.95  cnf(c_0_49, plain, (X1=k1_relat_1(X2)|X1!=k1_xboole_0|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 4.73/4.95  cnf(c_0_50, negated_conjecture, (v1_funct_2(esk7_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 4.73/4.95  cnf(c_0_51, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 4.73/4.95  cnf(c_0_52, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 4.73/4.95  fof(c_0_53, plain, ![X15]:(~v1_xboole_0(X15)|X15=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 4.73/4.95  fof(c_0_54, plain, ![X39]:(~v1_xboole_0(X39)|v1_xboole_0(k1_relat_1(X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_relat_1])])).
% 4.73/4.95  cnf(c_0_55, negated_conjecture, (~v1_funct_2(esk7_0,esk4_0,esk6_0)|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43])])).
% 4.73/4.95  cnf(c_0_56, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(X1))|esk5_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_44]), c_0_45])])).
% 4.73/4.95  cnf(c_0_57, plain, (v1_funct_2(X1,X2,X3)|k1_relat_1(X1)!=X2|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_46, c_0_39])).
% 4.73/4.95  cnf(c_0_58, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))|~r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 4.73/4.95  cnf(c_0_59, negated_conjecture, (k1_relat_1(esk7_0)=esk4_0|esk4_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_26]), c_0_50])])).
% 4.73/4.95  cnf(c_0_60, negated_conjecture, (r2_hidden(esk7_0,k1_zfmisc_1(k1_xboole_0))|esk4_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_37, c_0_51])).
% 4.73/4.95  cnf(c_0_61, plain, (k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X1,X3)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_52, c_0_48])).
% 4.73/4.95  cnf(c_0_62, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 4.73/4.95  cnf(c_0_63, plain, (v1_xboole_0(k1_relat_1(X1))|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 4.73/4.95  cnf(c_0_64, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 4.73/4.95  cnf(c_0_65, negated_conjecture, (esk5_0!=k1_xboole_0|~v1_funct_2(esk7_0,esk4_0,esk6_0)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 4.73/4.95  cnf(c_0_66, negated_conjecture, (v1_funct_2(esk7_0,esk4_0,X1)|esk4_0!=k1_xboole_0|~r1_tarski(esk5_0,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])).
% 4.73/4.95  cnf(c_0_67, negated_conjecture, (r1_tarski(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 4.73/4.95  cnf(c_0_68, negated_conjecture, (esk4_0=k1_xboole_0|esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 4.73/4.95  cnf(c_0_69, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(X1))|esk4_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_60]), c_0_45])])).
% 4.73/4.95  fof(c_0_70, plain, ![X40, X41, X42]:(~v1_xboole_0(X40)|(~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X41,X40)))|v1_xboole_0(X42))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 4.73/4.95  cnf(c_0_71, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X3!=k1_xboole_0|~r1_tarski(X2,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_27]), c_0_45])])).
% 4.73/4.95  cnf(c_0_72, plain, (k1_relat_1(X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 4.73/4.95  cnf(c_0_73, negated_conjecture, (k1_relset_1(esk4_0,esk5_0,esk7_0)=esk4_0|esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_26]), c_0_50])])).
% 4.73/4.95  cnf(c_0_74, negated_conjecture, (esk5_0!=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67])]), c_0_68])).
% 4.73/4.95  cnf(c_0_75, negated_conjecture, (esk4_0!=k1_xboole_0|~v1_funct_2(esk7_0,esk4_0,esk6_0)), inference(spm,[status(thm)],[c_0_55, c_0_69])).
% 4.73/4.95  cnf(c_0_76, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 4.73/4.95  cnf(c_0_77, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_71, c_0_45])).
% 4.73/4.95  cnf(c_0_78, plain, (k1_relset_1(X1,X2,X3)=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_39, c_0_72])).
% 4.73/4.95  cnf(c_0_79, negated_conjecture, (k1_relset_1(esk4_0,esk5_0,esk7_0)=esk4_0), inference(sr,[status(thm)],[c_0_73, c_0_74])).
% 4.73/4.95  cnf(c_0_80, negated_conjecture, (esk4_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_66]), c_0_67])])).
% 4.73/4.95  cnf(c_0_81, plain, (v1_xboole_0(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_76, c_0_22])).
% 4.73/4.95  cnf(c_0_82, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_77])).
% 4.73/4.95  cnf(c_0_83, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 4.73/4.95  cnf(c_0_84, plain, (k1_relset_1(X1,X2,X3)=k1_relset_1(X4,X5,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))), inference(spm,[status(thm)],[c_0_39, c_0_39])).
% 4.73/4.95  cnf(c_0_85, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 4.73/4.95  cnf(c_0_86, negated_conjecture, (~v1_xboole_0(esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_26])]), c_0_80])).
% 4.73/4.95  cnf(c_0_87, plain, (v1_xboole_0(X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_83])])).
% 4.73/4.95  cnf(c_0_88, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 4.73/4.95  cnf(c_0_89, negated_conjecture, (k1_relset_1(X1,X2,esk7_0)=esk4_0|esk5_0=k1_xboole_0|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_84]), c_0_26])])).
% 4.73/4.95  cnf(c_0_90, negated_conjecture, (r1_tarski(esk7_0,k2_zfmisc_1(esk4_0,X1))|~r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_85, c_0_58])).
% 4.73/4.95  cnf(c_0_91, negated_conjecture, (~r1_tarski(esk7_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 4.73/4.95  cnf(c_0_92, negated_conjecture, (X1=k1_xboole_0|v1_funct_2(esk7_0,esk4_0,X1)|k1_relset_1(esk4_0,X1,esk7_0)!=esk4_0|~r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_88, c_0_58])).
% 4.73/4.95  cnf(c_0_93, negated_conjecture, (k1_relset_1(esk4_0,X1,esk7_0)=esk4_0|~r1_tarski(esk5_0,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_58]), c_0_74])).
% 4.73/4.95  cnf(c_0_94, negated_conjecture, (X1!=k1_xboole_0|~r1_tarski(esk5_0,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_27]), c_0_91])).
% 4.73/4.95  cnf(c_0_95, negated_conjecture, (~v1_funct_2(esk7_0,esk4_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_58]), c_0_67])])).
% 4.73/4.95  cnf(c_0_96, negated_conjecture, (v1_funct_2(esk7_0,esk4_0,X1)|~r1_tarski(esk5_0,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_94])).
% 4.73/4.95  cnf(c_0_97, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_67])]), ['proof']).
% 4.73/4.95  # SZS output end CNFRefutation
% 4.73/4.95  # Proof object total steps             : 98
% 4.73/4.95  # Proof object clause steps            : 66
% 4.73/4.95  # Proof object formula steps           : 32
% 4.73/4.95  # Proof object conjectures             : 36
% 4.73/4.95  # Proof object clause conjectures      : 33
% 4.73/4.95  # Proof object formula conjectures     : 3
% 4.73/4.95  # Proof object initial clauses used    : 26
% 4.73/4.95  # Proof object initial formulas used   : 16
% 4.73/4.95  # Proof object generating inferences   : 38
% 4.73/4.95  # Proof object simplifying inferences  : 35
% 4.73/4.95  # Training examples: 0 positive, 0 negative
% 4.73/4.95  # Parsed axioms                        : 21
% 4.73/4.95  # Removed by relevancy pruning/SinE    : 0
% 4.73/4.95  # Initial clauses                      : 45
% 4.73/4.95  # Removed in clause preprocessing      : 0
% 4.73/4.95  # Initial clauses in saturation        : 45
% 4.73/4.95  # Processed clauses                    : 36193
% 4.73/4.95  # ...of these trivial                  : 161
% 4.73/4.95  # ...subsumed                          : 32486
% 4.73/4.95  # ...remaining for further processing  : 3546
% 4.73/4.95  # Other redundant clauses eliminated   : 189
% 4.73/4.95  # Clauses deleted for lack of memory   : 0
% 4.73/4.95  # Backward-subsumed                    : 374
% 4.73/4.95  # Backward-rewritten                   : 7
% 4.73/4.95  # Generated clauses                    : 494376
% 4.73/4.95  # ...of the previous two non-trivial   : 376945
% 4.73/4.95  # Contextual simplify-reflections      : 245
% 4.73/4.95  # Paramodulations                      : 493596
% 4.73/4.95  # Factorizations                       : 385
% 4.73/4.95  # Equation resolutions                 : 392
% 4.73/4.95  # Propositional unsat checks           : 0
% 4.73/4.95  #    Propositional check models        : 0
% 4.73/4.95  #    Propositional check unsatisfiable : 0
% 4.73/4.95  #    Propositional clauses             : 0
% 4.73/4.95  #    Propositional clauses after purity: 0
% 4.73/4.95  #    Propositional unsat core size     : 0
% 4.73/4.95  #    Propositional preprocessing time  : 0.000
% 4.73/4.95  #    Propositional encoding time       : 0.000
% 4.73/4.95  #    Propositional solver time         : 0.000
% 4.73/4.95  #    Success case prop preproc time    : 0.000
% 4.73/4.95  #    Success case prop encoding time   : 0.000
% 4.73/4.95  #    Success case prop solver time     : 0.000
% 4.73/4.95  # Current number of processed clauses  : 3160
% 4.73/4.95  #    Positive orientable unit clauses  : 45
% 4.73/4.95  #    Positive unorientable unit clauses: 0
% 4.73/4.95  #    Negative unit clauses             : 25
% 4.73/4.95  #    Non-unit-clauses                  : 3090
% 4.73/4.95  # Current number of unprocessed clauses: 335777
% 4.73/4.95  # ...number of literals in the above   : 1411444
% 4.73/4.95  # Current number of archived formulas  : 0
% 4.73/4.95  # Current number of archived clauses   : 384
% 4.73/4.95  # Clause-clause subsumption calls (NU) : 1277198
% 4.73/4.95  # Rec. Clause-clause subsumption calls : 497210
% 4.73/4.95  # Non-unit clause-clause subsumptions  : 8813
% 4.73/4.95  # Unit Clause-clause subsumption calls : 4489
% 4.73/4.95  # Rewrite failures with RHS unbound    : 0
% 4.73/4.95  # BW rewrite match attempts            : 76
% 4.73/4.95  # BW rewrite match successes           : 11
% 4.73/4.95  # Condensation attempts                : 0
% 4.73/4.95  # Condensation successes               : 0
% 4.73/4.95  # Termbank termtop insertions          : 6465551
% 4.73/4.96  
% 4.73/4.96  # -------------------------------------------------
% 4.73/4.96  # User time                : 4.492 s
% 4.73/4.96  # System time              : 0.139 s
% 4.73/4.96  # Total time               : 4.631 s
% 4.73/4.96  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
