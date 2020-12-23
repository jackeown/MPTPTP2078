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
% DateTime   : Thu Dec  3 11:04:30 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 899 expanded)
%              Number of clauses        :   67 ( 373 expanded)
%              Number of leaves         :   24 ( 259 expanded)
%              Depth                    :   13
%              Number of atoms          :  338 (1803 expanded)
%              Number of equality atoms :  121 ( 913 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   44 (   2 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t14_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( k1_relat_1(X2) = k1_tarski(X1)
       => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(t63_subset_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(fc2_xboole_0,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(cc3_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_funct_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d12_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( X3 = k9_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(X5,k1_relat_1(X1))
                  & r2_hidden(X5,X2)
                  & X4 = k1_funct_1(X1,X5) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

fof(t6_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_hidden(X3,X1)
       => ( X2 = k1_xboole_0
          | r2_hidden(k1_funct_1(X4,X3),k2_relset_1(X1,X2,X4)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
       => ( X2 != k1_xboole_0
         => k2_relset_1(k1_tarski(X1),X2,X3) = k1_tarski(k1_funct_1(X3,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t62_funct_2])).

fof(c_0_25,negated_conjecture,
    ( v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,k1_tarski(esk5_0),esk6_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk5_0),esk6_0)))
    & esk6_0 != k1_xboole_0
    & k2_relset_1(k1_tarski(esk5_0),esk6_0,esk7_0) != k1_tarski(k1_funct_1(esk7_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

fof(c_0_26,plain,(
    ! [X10] : k2_tarski(X10,X10) = k1_tarski(X10) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_27,plain,(
    ! [X11,X12] : k1_enumset1(X11,X11,X12) = k2_tarski(X11,X12) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_28,plain,(
    ! [X13,X14,X15] : k2_enumset1(X13,X13,X14,X15) = k1_enumset1(X13,X14,X15) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_29,plain,(
    ! [X65,X66,X67] :
      ( ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X65,X66)))
      | k2_relset_1(X65,X66,X67) = k2_relat_1(X67) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk5_0),esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_34,plain,(
    ! [X59,X60,X61] :
      ( ( v4_relat_1(X61,X59)
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X60))) )
      & ( v5_relat_1(X61,X60)
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X60))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_35,plain,(
    ! [X56,X57,X58] :
      ( ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))
      | v1_relat_1(X58) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_36,negated_conjecture,
    ( k2_relset_1(k1_tarski(esk5_0),esk6_0,esk7_0) != k1_tarski(k1_funct_1(esk7_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33])).

fof(c_0_39,plain,(
    ! [X54,X55] :
      ( ~ v1_relat_1(X55)
      | ~ v1_funct_1(X55)
      | k1_relat_1(X55) != k1_tarski(X54)
      | k2_relat_1(X55) = k1_tarski(k1_funct_1(X55,X54)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_funct_1])])).

fof(c_0_40,plain,(
    ! [X6] :
      ( ~ v1_xboole_0(X6)
      | X6 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

fof(c_0_41,plain,(
    ! [X19,X20,X21,X22] :
      ( ( ~ r1_tarski(X22,k1_enumset1(X19,X20,X21))
        | X22 = k1_xboole_0
        | X22 = k1_tarski(X19)
        | X22 = k1_tarski(X20)
        | X22 = k1_tarski(X21)
        | X22 = k2_tarski(X19,X20)
        | X22 = k2_tarski(X20,X21)
        | X22 = k2_tarski(X19,X21)
        | X22 = k1_enumset1(X19,X20,X21) )
      & ( X22 != k1_xboole_0
        | r1_tarski(X22,k1_enumset1(X19,X20,X21)) )
      & ( X22 != k1_tarski(X19)
        | r1_tarski(X22,k1_enumset1(X19,X20,X21)) )
      & ( X22 != k1_tarski(X20)
        | r1_tarski(X22,k1_enumset1(X19,X20,X21)) )
      & ( X22 != k1_tarski(X21)
        | r1_tarski(X22,k1_enumset1(X19,X20,X21)) )
      & ( X22 != k2_tarski(X19,X20)
        | r1_tarski(X22,k1_enumset1(X19,X20,X21)) )
      & ( X22 != k2_tarski(X20,X21)
        | r1_tarski(X22,k1_enumset1(X19,X20,X21)) )
      & ( X22 != k2_tarski(X19,X21)
        | r1_tarski(X22,k1_enumset1(X19,X20,X21)) )
      & ( X22 != k1_enumset1(X19,X20,X21)
        | r1_tarski(X22,k1_enumset1(X19,X20,X21)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t142_zfmisc_1])])])).

fof(c_0_42,plain,(
    ! [X31,X32] :
      ( ( ~ v4_relat_1(X32,X31)
        | r1_tarski(k1_relat_1(X32),X31)
        | ~ v1_relat_1(X32) )
      & ( ~ r1_tarski(k1_relat_1(X32),X31)
        | v4_relat_1(X32,X31)
        | ~ v1_relat_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_43,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( k2_relset_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0,esk7_0) != k2_enumset1(k1_funct_1(esk7_0,esk5_0),k1_funct_1(esk7_0,esk5_0),k1_funct_1(esk7_0,esk5_0),k1_funct_1(esk7_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_33]),c_0_33])).

cnf(c_0_46,negated_conjecture,
    ( k2_relset_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0,esk7_0) = k2_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_47,plain,
    ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_relat_1(X1) != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_48,plain,(
    ! [X24,X25] :
      ( ~ r2_hidden(X24,X25)
      | m1_subset_1(k1_tarski(X24),k1_zfmisc_1(X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).

fof(c_0_49,plain,(
    ! [X16] : ~ v1_xboole_0(k1_tarski(X16)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

fof(c_0_50,plain,(
    ! [X17,X18] :
      ( ( k2_zfmisc_1(X17,X18) != k1_xboole_0
        | X17 = k1_xboole_0
        | X18 = k1_xboole_0 )
      & ( X17 != k1_xboole_0
        | k2_zfmisc_1(X17,X18) = k1_xboole_0 )
      & ( X18 != k1_xboole_0
        | k2_zfmisc_1(X17,X18) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_51,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_52,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_53,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | X1 = k1_tarski(X3)
    | X1 = k1_tarski(X4)
    | X1 = k2_tarski(X2,X3)
    | X1 = k2_tarski(X3,X4)
    | X1 = k2_tarski(X2,X4)
    | X1 = k1_enumset1(X2,X3,X4)
    | ~ r1_tarski(X1,k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_54,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_55,negated_conjecture,
    ( v4_relat_1(esk7_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_38])).

cnf(c_0_56,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_38])).

cnf(c_0_57,negated_conjecture,
    ( k2_enumset1(k1_funct_1(esk7_0,esk5_0),k1_funct_1(esk7_0,esk5_0),k1_funct_1(esk7_0,esk5_0),k1_funct_1(esk7_0,esk5_0)) != k2_relat_1(esk7_0) ),
    inference(rw,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_58,plain,
    ( k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2))
    | k1_relat_1(X1) != k2_enumset1(X2,X2,X2,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_33]),c_0_33])).

cnf(c_0_59,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_60,plain,(
    ! [X37,X38] :
      ( ~ v1_relat_1(X37)
      | ~ v1_funct_1(X37)
      | ~ m1_subset_1(X38,k1_zfmisc_1(X37))
      | v1_funct_1(X38) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_funct_1])])])).

fof(c_0_61,plain,(
    ! [X23] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X23)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_62,plain,(
    ! [X62,X63,X64] :
      ( ~ v1_xboole_0(X62)
      | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X63,X62)))
      | v1_xboole_0(X64) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

cnf(c_0_63,plain,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_64,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_65,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_66,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

fof(c_0_67,plain,(
    ! [X68] :
      ( ( v1_funct_1(X68)
        | ~ v1_relat_1(X68)
        | ~ v1_funct_1(X68) )
      & ( v1_funct_2(X68,k1_relat_1(X68),k2_relat_1(X68))
        | ~ v1_relat_1(X68)
        | ~ v1_funct_1(X68) )
      & ( m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X68),k2_relat_1(X68))))
        | ~ v1_relat_1(X68)
        | ~ v1_funct_1(X68) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

cnf(c_0_68,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_enumset1(X4,X4,X4,X4)
    | X1 = k2_enumset1(X3,X3,X3,X4)
    | X1 = k2_enumset1(X3,X3,X3,X3)
    | X1 = k2_enumset1(X2,X2,X3,X4)
    | X1 = k2_enumset1(X2,X2,X2,X4)
    | X1 = k2_enumset1(X2,X2,X2,X3)
    | X1 = k2_enumset1(X2,X2,X2,X2)
    | ~ r1_tarski(X1,k2_enumset1(X2,X2,X3,X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_31]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_32]),c_0_32]),c_0_32]),c_0_32]),c_0_33]),c_0_33]),c_0_33]),c_0_33]),c_0_33]),c_0_33]),c_0_33]),c_0_33])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk7_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])])).

cnf(c_0_70,negated_conjecture,
    ( k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0) != k1_relat_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59]),c_0_56])])).

cnf(c_0_71,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_72,plain,
    ( v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_73,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_74,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_75,plain,
    ( m1_subset_1(k2_enumset1(X1,X1,X1,X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_31]),c_0_32]),c_0_33])).

cnf(c_0_76,plain,
    ( ~ v1_xboole_0(k2_enumset1(X1,X1,X1,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_31]),c_0_32]),c_0_33])).

cnf(c_0_77,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_65])).

cnf(c_0_78,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_52,c_0_66])).

fof(c_0_79,plain,(
    ! [X26,X27] :
      ( ( ~ m1_subset_1(X26,k1_zfmisc_1(X27))
        | r1_tarski(X26,X27) )
      & ( ~ r1_tarski(X26,X27)
        | m1_subset_1(X26,k1_zfmisc_1(X27)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_80,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_81,negated_conjecture,
    ( k1_relat_1(esk7_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70])).

cnf(c_0_82,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_71])).

fof(c_0_83,plain,(
    ! [X39,X40,X41,X42,X44,X45,X46,X47,X49] :
      ( ( r2_hidden(esk1_4(X39,X40,X41,X42),k1_relat_1(X39))
        | ~ r2_hidden(X42,X41)
        | X41 != k9_relat_1(X39,X40)
        | ~ v1_relat_1(X39)
        | ~ v1_funct_1(X39) )
      & ( r2_hidden(esk1_4(X39,X40,X41,X42),X40)
        | ~ r2_hidden(X42,X41)
        | X41 != k9_relat_1(X39,X40)
        | ~ v1_relat_1(X39)
        | ~ v1_funct_1(X39) )
      & ( X42 = k1_funct_1(X39,esk1_4(X39,X40,X41,X42))
        | ~ r2_hidden(X42,X41)
        | X41 != k9_relat_1(X39,X40)
        | ~ v1_relat_1(X39)
        | ~ v1_funct_1(X39) )
      & ( ~ r2_hidden(X45,k1_relat_1(X39))
        | ~ r2_hidden(X45,X40)
        | X44 != k1_funct_1(X39,X45)
        | r2_hidden(X44,X41)
        | X41 != k9_relat_1(X39,X40)
        | ~ v1_relat_1(X39)
        | ~ v1_funct_1(X39) )
      & ( ~ r2_hidden(esk2_3(X39,X46,X47),X47)
        | ~ r2_hidden(X49,k1_relat_1(X39))
        | ~ r2_hidden(X49,X46)
        | esk2_3(X39,X46,X47) != k1_funct_1(X39,X49)
        | X47 = k9_relat_1(X39,X46)
        | ~ v1_relat_1(X39)
        | ~ v1_funct_1(X39) )
      & ( r2_hidden(esk3_3(X39,X46,X47),k1_relat_1(X39))
        | r2_hidden(esk2_3(X39,X46,X47),X47)
        | X47 = k9_relat_1(X39,X46)
        | ~ v1_relat_1(X39)
        | ~ v1_funct_1(X39) )
      & ( r2_hidden(esk3_3(X39,X46,X47),X46)
        | r2_hidden(esk2_3(X39,X46,X47),X47)
        | X47 = k9_relat_1(X39,X46)
        | ~ v1_relat_1(X39)
        | ~ v1_funct_1(X39) )
      & ( esk2_3(X39,X46,X47) = k1_funct_1(X39,esk3_3(X39,X46,X47))
        | r2_hidden(esk2_3(X39,X46,X47),X47)
        | X47 = k9_relat_1(X39,X46)
        | ~ v1_relat_1(X39)
        | ~ v1_funct_1(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).

cnf(c_0_84,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_85,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X2,X3))
    | ~ v1_xboole_0(X3) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76])).

cnf(c_0_86,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_77]),c_0_78])])).

cnf(c_0_87,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

fof(c_0_88,plain,(
    ! [X69,X70,X71,X72] :
      ( ~ v1_funct_1(X72)
      | ~ v1_funct_2(X72,X69,X70)
      | ~ m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X69,X70)))
      | ~ r2_hidden(X71,X69)
      | X70 = k1_xboole_0
      | r2_hidden(k1_funct_1(X72,X71),k2_relset_1(X69,X70,X72)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_funct_2])])).

cnf(c_0_89,negated_conjecture,
    ( v1_funct_2(esk7_0,k1_tarski(esk5_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_90,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82]),c_0_59]),c_0_56])])).

cnf(c_0_91,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),k1_relat_1(X1))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_92,negated_conjecture,
    ( v1_funct_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_59]),c_0_56])])).

cnf(c_0_93,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_94,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_73])).

cnf(c_0_95,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_77]),c_0_78])])).

cnf(c_0_96,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_97,plain,
    ( X3 = k1_xboole_0
    | r2_hidden(k1_funct_1(X1,X4),k2_relset_1(X2,X3,X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_98,negated_conjecture,
    ( v1_funct_2(esk7_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_31]),c_0_32]),c_0_33])).

cnf(c_0_99,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_100,negated_conjecture,
    ( v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_86,c_0_90])).

cnf(c_0_101,negated_conjecture,
    ( X1 = k9_relat_1(k1_xboole_0,X2)
    | r2_hidden(esk2_3(k1_xboole_0,X2,X1),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_93]),c_0_94])]),c_0_95])).

cnf(c_0_102,plain,
    ( ~ r1_tarski(k2_enumset1(X1,X1,X1,X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_96])).

fof(c_0_103,plain,(
    ! [X9] : r1_tarski(k1_xboole_0,X9) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_104,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk7_0,X1),k2_relat_1(esk7_0))
    | ~ r2_hidden(X1,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_38]),c_0_46]),c_0_98]),c_0_59])]),c_0_99])).

cnf(c_0_105,negated_conjecture,
    ( esk7_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_100])).

cnf(c_0_106,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_107,negated_conjecture,
    ( k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_95,c_0_101])).

cnf(c_0_108,plain,
    ( k1_relat_1(X1) != k2_enumset1(X2,X2,X2,X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_102,c_0_58])).

cnf(c_0_109,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_110,negated_conjecture,
    ( ~ r2_hidden(X1,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_104,c_0_105]),c_0_105]),c_0_106]),c_0_95])).

cnf(c_0_111,negated_conjecture,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_3(k1_xboole_0,X2,X1),X1) ),
    inference(rw,[status(thm)],[c_0_101,c_0_107])).

cnf(c_0_112,plain,
    ( k2_enumset1(X1,X1,X1,X1) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_106]),c_0_93]),c_0_92]),c_0_94]),c_0_109])])).

cnf(c_0_113,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_112]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:46:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.13/0.39  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.029 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t62_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>k2_relset_1(k1_tarski(X1),X2,X3)=k1_tarski(k1_funct_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 0.13/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.39  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.13/0.39  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.13/0.39  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.13/0.39  fof(t14_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 0.13/0.39  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.13/0.39  fof(t142_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r1_tarski(X4,k1_enumset1(X1,X2,X3))<=>~((((((((X4!=k1_xboole_0&X4!=k1_tarski(X1))&X4!=k1_tarski(X2))&X4!=k1_tarski(X3))&X4!=k2_tarski(X1,X2))&X4!=k2_tarski(X2,X3))&X4!=k2_tarski(X1,X3))&X4!=k1_enumset1(X1,X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 0.13/0.39  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 0.13/0.39  fof(t63_subset_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 0.13/0.39  fof(fc2_xboole_0, axiom, ![X1]:~(v1_xboole_0(k1_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 0.13/0.39  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.13/0.39  fof(dt_o_0_0_xboole_0, axiom, v1_xboole_0(o_0_0_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_o_0_0_xboole_0)).
% 0.13/0.39  fof(cc3_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_funct_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_funct_1)).
% 0.13/0.39  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.13/0.39  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 0.13/0.39  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 0.13/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.39  fof(d12_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(X3=k9_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((r2_hidden(X5,k1_relat_1(X1))&r2_hidden(X5,X2))&X4=k1_funct_1(X1,X5))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_1)).
% 0.13/0.39  fof(t6_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_hidden(X3,X1)=>(X2=k1_xboole_0|r2_hidden(k1_funct_1(X4,X3),k2_relset_1(X1,X2,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 0.13/0.39  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.13/0.39  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.13/0.39  fof(c_0_24, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>k2_relset_1(k1_tarski(X1),X2,X3)=k1_tarski(k1_funct_1(X3,X1))))), inference(assume_negation,[status(cth)],[t62_funct_2])).
% 0.13/0.39  fof(c_0_25, negated_conjecture, (((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,k1_tarski(esk5_0),esk6_0))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk5_0),esk6_0))))&(esk6_0!=k1_xboole_0&k2_relset_1(k1_tarski(esk5_0),esk6_0,esk7_0)!=k1_tarski(k1_funct_1(esk7_0,esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).
% 0.13/0.39  fof(c_0_26, plain, ![X10]:k2_tarski(X10,X10)=k1_tarski(X10), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.39  fof(c_0_27, plain, ![X11, X12]:k1_enumset1(X11,X11,X12)=k2_tarski(X11,X12), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.39  fof(c_0_28, plain, ![X13, X14, X15]:k2_enumset1(X13,X13,X14,X15)=k1_enumset1(X13,X14,X15), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.39  fof(c_0_29, plain, ![X65, X66, X67]:(~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X65,X66)))|k2_relset_1(X65,X66,X67)=k2_relat_1(X67)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.13/0.39  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk5_0),esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.39  cnf(c_0_31, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.39  cnf(c_0_32, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.39  cnf(c_0_33, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.39  fof(c_0_34, plain, ![X59, X60, X61]:((v4_relat_1(X61,X59)|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X60))))&(v5_relat_1(X61,X60)|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X60))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.13/0.39  fof(c_0_35, plain, ![X56, X57, X58]:(~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))|v1_relat_1(X58)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.13/0.39  cnf(c_0_36, negated_conjecture, (k2_relset_1(k1_tarski(esk5_0),esk6_0,esk7_0)!=k1_tarski(k1_funct_1(esk7_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.39  cnf(c_0_37, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.39  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33])).
% 0.13/0.39  fof(c_0_39, plain, ![X54, X55]:(~v1_relat_1(X55)|~v1_funct_1(X55)|(k1_relat_1(X55)!=k1_tarski(X54)|k2_relat_1(X55)=k1_tarski(k1_funct_1(X55,X54)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_funct_1])])).
% 0.13/0.39  fof(c_0_40, plain, ![X6]:(~v1_xboole_0(X6)|X6=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.13/0.39  fof(c_0_41, plain, ![X19, X20, X21, X22]:((~r1_tarski(X22,k1_enumset1(X19,X20,X21))|(X22=k1_xboole_0|X22=k1_tarski(X19)|X22=k1_tarski(X20)|X22=k1_tarski(X21)|X22=k2_tarski(X19,X20)|X22=k2_tarski(X20,X21)|X22=k2_tarski(X19,X21)|X22=k1_enumset1(X19,X20,X21)))&((((((((X22!=k1_xboole_0|r1_tarski(X22,k1_enumset1(X19,X20,X21)))&(X22!=k1_tarski(X19)|r1_tarski(X22,k1_enumset1(X19,X20,X21))))&(X22!=k1_tarski(X20)|r1_tarski(X22,k1_enumset1(X19,X20,X21))))&(X22!=k1_tarski(X21)|r1_tarski(X22,k1_enumset1(X19,X20,X21))))&(X22!=k2_tarski(X19,X20)|r1_tarski(X22,k1_enumset1(X19,X20,X21))))&(X22!=k2_tarski(X20,X21)|r1_tarski(X22,k1_enumset1(X19,X20,X21))))&(X22!=k2_tarski(X19,X21)|r1_tarski(X22,k1_enumset1(X19,X20,X21))))&(X22!=k1_enumset1(X19,X20,X21)|r1_tarski(X22,k1_enumset1(X19,X20,X21))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t142_zfmisc_1])])])).
% 0.13/0.39  fof(c_0_42, plain, ![X31, X32]:((~v4_relat_1(X32,X31)|r1_tarski(k1_relat_1(X32),X31)|~v1_relat_1(X32))&(~r1_tarski(k1_relat_1(X32),X31)|v4_relat_1(X32,X31)|~v1_relat_1(X32))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.13/0.39  cnf(c_0_43, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.39  cnf(c_0_44, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.39  cnf(c_0_45, negated_conjecture, (k2_relset_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0,esk7_0)!=k2_enumset1(k1_funct_1(esk7_0,esk5_0),k1_funct_1(esk7_0,esk5_0),k1_funct_1(esk7_0,esk5_0),k1_funct_1(esk7_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_33]), c_0_33])).
% 0.13/0.39  cnf(c_0_46, negated_conjecture, (k2_relset_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0,esk7_0)=k2_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.13/0.39  cnf(c_0_47, plain, (k2_relat_1(X1)=k1_tarski(k1_funct_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|k1_relat_1(X1)!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.39  fof(c_0_48, plain, ![X24, X25]:(~r2_hidden(X24,X25)|m1_subset_1(k1_tarski(X24),k1_zfmisc_1(X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).
% 0.13/0.39  fof(c_0_49, plain, ![X16]:~v1_xboole_0(k1_tarski(X16)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).
% 0.13/0.39  fof(c_0_50, plain, ![X17, X18]:((k2_zfmisc_1(X17,X18)!=k1_xboole_0|(X17=k1_xboole_0|X18=k1_xboole_0))&((X17!=k1_xboole_0|k2_zfmisc_1(X17,X18)=k1_xboole_0)&(X18!=k1_xboole_0|k2_zfmisc_1(X17,X18)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.13/0.39  cnf(c_0_51, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.13/0.39  cnf(c_0_52, plain, (v1_xboole_0(o_0_0_xboole_0)), inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).
% 0.13/0.39  cnf(c_0_53, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|X1=k1_tarski(X3)|X1=k1_tarski(X4)|X1=k2_tarski(X2,X3)|X1=k2_tarski(X3,X4)|X1=k2_tarski(X2,X4)|X1=k1_enumset1(X2,X3,X4)|~r1_tarski(X1,k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.13/0.39  cnf(c_0_54, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.13/0.39  cnf(c_0_55, negated_conjecture, (v4_relat_1(esk7_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_43, c_0_38])).
% 0.13/0.39  cnf(c_0_56, negated_conjecture, (v1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_44, c_0_38])).
% 0.13/0.39  cnf(c_0_57, negated_conjecture, (k2_enumset1(k1_funct_1(esk7_0,esk5_0),k1_funct_1(esk7_0,esk5_0),k1_funct_1(esk7_0,esk5_0),k1_funct_1(esk7_0,esk5_0))!=k2_relat_1(esk7_0)), inference(rw,[status(thm)],[c_0_45, c_0_46])).
% 0.13/0.39  cnf(c_0_58, plain, (k2_relat_1(X1)=k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2))|k1_relat_1(X1)!=k2_enumset1(X2,X2,X2,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_33]), c_0_33])).
% 0.13/0.39  cnf(c_0_59, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.39  fof(c_0_60, plain, ![X37, X38]:(~v1_relat_1(X37)|~v1_funct_1(X37)|(~m1_subset_1(X38,k1_zfmisc_1(X37))|v1_funct_1(X38))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_funct_1])])])).
% 0.13/0.39  fof(c_0_61, plain, ![X23]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X23)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.13/0.39  fof(c_0_62, plain, ![X62, X63, X64]:(~v1_xboole_0(X62)|(~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X63,X62)))|v1_xboole_0(X64))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 0.13/0.39  cnf(c_0_63, plain, (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.13/0.39  cnf(c_0_64, plain, (~v1_xboole_0(k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.13/0.39  cnf(c_0_65, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.13/0.39  cnf(c_0_66, plain, (o_0_0_xboole_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.13/0.39  fof(c_0_67, plain, ![X68]:(((v1_funct_1(X68)|(~v1_relat_1(X68)|~v1_funct_1(X68)))&(v1_funct_2(X68,k1_relat_1(X68),k2_relat_1(X68))|(~v1_relat_1(X68)|~v1_funct_1(X68))))&(m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X68),k2_relat_1(X68))))|(~v1_relat_1(X68)|~v1_funct_1(X68)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.13/0.39  cnf(c_0_68, plain, (X1=k1_xboole_0|X1=k2_enumset1(X4,X4,X4,X4)|X1=k2_enumset1(X3,X3,X3,X4)|X1=k2_enumset1(X3,X3,X3,X3)|X1=k2_enumset1(X2,X2,X3,X4)|X1=k2_enumset1(X2,X2,X2,X4)|X1=k2_enumset1(X2,X2,X2,X3)|X1=k2_enumset1(X2,X2,X2,X2)|~r1_tarski(X1,k2_enumset1(X2,X2,X3,X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_31]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_32]), c_0_32]), c_0_32]), c_0_32]), c_0_33]), c_0_33]), c_0_33]), c_0_33]), c_0_33]), c_0_33]), c_0_33]), c_0_33])).
% 0.13/0.39  cnf(c_0_69, negated_conjecture, (r1_tarski(k1_relat_1(esk7_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])])).
% 0.13/0.39  cnf(c_0_70, negated_conjecture, (k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)!=k1_relat_1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59]), c_0_56])])).
% 0.13/0.39  cnf(c_0_71, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.13/0.39  cnf(c_0_72, plain, (v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.13/0.39  cnf(c_0_73, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.13/0.39  cnf(c_0_74, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.13/0.39  cnf(c_0_75, plain, (m1_subset_1(k2_enumset1(X1,X1,X1,X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_31]), c_0_32]), c_0_33])).
% 0.13/0.39  cnf(c_0_76, plain, (~v1_xboole_0(k2_enumset1(X1,X1,X1,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_31]), c_0_32]), c_0_33])).
% 0.13/0.39  cnf(c_0_77, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_65])).
% 0.13/0.39  cnf(c_0_78, plain, (v1_xboole_0(k1_xboole_0)), inference(rw,[status(thm)],[c_0_52, c_0_66])).
% 0.13/0.39  fof(c_0_79, plain, ![X26, X27]:((~m1_subset_1(X26,k1_zfmisc_1(X27))|r1_tarski(X26,X27))&(~r1_tarski(X26,X27)|m1_subset_1(X26,k1_zfmisc_1(X27)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.39  cnf(c_0_80, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.13/0.39  cnf(c_0_81, negated_conjecture, (k1_relat_1(esk7_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70])).
% 0.13/0.39  cnf(c_0_82, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_71])).
% 0.13/0.39  fof(c_0_83, plain, ![X39, X40, X41, X42, X44, X45, X46, X47, X49]:(((((r2_hidden(esk1_4(X39,X40,X41,X42),k1_relat_1(X39))|~r2_hidden(X42,X41)|X41!=k9_relat_1(X39,X40)|(~v1_relat_1(X39)|~v1_funct_1(X39)))&(r2_hidden(esk1_4(X39,X40,X41,X42),X40)|~r2_hidden(X42,X41)|X41!=k9_relat_1(X39,X40)|(~v1_relat_1(X39)|~v1_funct_1(X39))))&(X42=k1_funct_1(X39,esk1_4(X39,X40,X41,X42))|~r2_hidden(X42,X41)|X41!=k9_relat_1(X39,X40)|(~v1_relat_1(X39)|~v1_funct_1(X39))))&(~r2_hidden(X45,k1_relat_1(X39))|~r2_hidden(X45,X40)|X44!=k1_funct_1(X39,X45)|r2_hidden(X44,X41)|X41!=k9_relat_1(X39,X40)|(~v1_relat_1(X39)|~v1_funct_1(X39))))&((~r2_hidden(esk2_3(X39,X46,X47),X47)|(~r2_hidden(X49,k1_relat_1(X39))|~r2_hidden(X49,X46)|esk2_3(X39,X46,X47)!=k1_funct_1(X39,X49))|X47=k9_relat_1(X39,X46)|(~v1_relat_1(X39)|~v1_funct_1(X39)))&(((r2_hidden(esk3_3(X39,X46,X47),k1_relat_1(X39))|r2_hidden(esk2_3(X39,X46,X47),X47)|X47=k9_relat_1(X39,X46)|(~v1_relat_1(X39)|~v1_funct_1(X39)))&(r2_hidden(esk3_3(X39,X46,X47),X46)|r2_hidden(esk2_3(X39,X46,X47),X47)|X47=k9_relat_1(X39,X46)|(~v1_relat_1(X39)|~v1_funct_1(X39))))&(esk2_3(X39,X46,X47)=k1_funct_1(X39,esk3_3(X39,X46,X47))|r2_hidden(esk2_3(X39,X46,X47),X47)|X47=k9_relat_1(X39,X46)|(~v1_relat_1(X39)|~v1_funct_1(X39)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).
% 0.13/0.39  cnf(c_0_84, plain, (v1_funct_1(k1_xboole_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.13/0.39  cnf(c_0_85, plain, (~r2_hidden(X1,k2_zfmisc_1(X2,X3))|~v1_xboole_0(X3)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76])).
% 0.13/0.39  cnf(c_0_86, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_77]), c_0_78])])).
% 0.13/0.39  cnf(c_0_87, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.13/0.39  fof(c_0_88, plain, ![X69, X70, X71, X72]:(~v1_funct_1(X72)|~v1_funct_2(X72,X69,X70)|~m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X69,X70)))|(~r2_hidden(X71,X69)|(X70=k1_xboole_0|r2_hidden(k1_funct_1(X72,X71),k2_relset_1(X69,X70,X72))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_funct_2])])).
% 0.13/0.39  cnf(c_0_89, negated_conjecture, (v1_funct_2(esk7_0,k1_tarski(esk5_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.39  cnf(c_0_90, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_82]), c_0_59]), c_0_56])])).
% 0.13/0.39  cnf(c_0_91, plain, (r2_hidden(esk3_3(X1,X2,X3),k1_relat_1(X1))|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.13/0.39  cnf(c_0_92, negated_conjecture, (v1_funct_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_59]), c_0_56])])).
% 0.13/0.39  cnf(c_0_93, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.13/0.39  cnf(c_0_94, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_44, c_0_73])).
% 0.13/0.39  cnf(c_0_95, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_77]), c_0_78])])).
% 0.13/0.39  cnf(c_0_96, plain, (v1_xboole_0(X1)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.13/0.39  cnf(c_0_97, plain, (X3=k1_xboole_0|r2_hidden(k1_funct_1(X1,X4),k2_relset_1(X2,X3,X1))|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.13/0.39  cnf(c_0_98, negated_conjecture, (v1_funct_2(esk7_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_31]), c_0_32]), c_0_33])).
% 0.13/0.39  cnf(c_0_99, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.39  cnf(c_0_100, negated_conjecture, (v1_xboole_0(esk7_0)), inference(spm,[status(thm)],[c_0_86, c_0_90])).
% 0.13/0.39  cnf(c_0_101, negated_conjecture, (X1=k9_relat_1(k1_xboole_0,X2)|r2_hidden(esk2_3(k1_xboole_0,X2,X1),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_93]), c_0_94])]), c_0_95])).
% 0.13/0.39  cnf(c_0_102, plain, (~r1_tarski(k2_enumset1(X1,X1,X1,X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_76, c_0_96])).
% 0.13/0.39  fof(c_0_103, plain, ![X9]:r1_tarski(k1_xboole_0,X9), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.13/0.39  cnf(c_0_104, negated_conjecture, (r2_hidden(k1_funct_1(esk7_0,X1),k2_relat_1(esk7_0))|~r2_hidden(X1,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_38]), c_0_46]), c_0_98]), c_0_59])]), c_0_99])).
% 0.13/0.39  cnf(c_0_105, negated_conjecture, (esk7_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_51, c_0_100])).
% 0.13/0.39  cnf(c_0_106, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.13/0.39  cnf(c_0_107, negated_conjecture, (k9_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_95, c_0_101])).
% 0.13/0.39  cnf(c_0_108, plain, (k1_relat_1(X1)!=k2_enumset1(X2,X2,X2,X2)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_102, c_0_58])).
% 0.13/0.39  cnf(c_0_109, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_103])).
% 0.13/0.39  cnf(c_0_110, negated_conjecture, (~r2_hidden(X1,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_104, c_0_105]), c_0_105]), c_0_106]), c_0_95])).
% 0.13/0.39  cnf(c_0_111, negated_conjecture, (X1=k1_xboole_0|r2_hidden(esk2_3(k1_xboole_0,X2,X1),X1)), inference(rw,[status(thm)],[c_0_101, c_0_107])).
% 0.13/0.39  cnf(c_0_112, plain, (k2_enumset1(X1,X1,X1,X1)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_106]), c_0_93]), c_0_92]), c_0_94]), c_0_109])])).
% 0.13/0.39  cnf(c_0_113, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_112]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 114
% 0.13/0.39  # Proof object clause steps            : 67
% 0.13/0.39  # Proof object formula steps           : 47
% 0.13/0.39  # Proof object conjectures             : 28
% 0.13/0.39  # Proof object clause conjectures      : 25
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 30
% 0.13/0.39  # Proof object initial formulas used   : 24
% 0.13/0.39  # Proof object generating inferences   : 24
% 0.13/0.39  # Proof object simplifying inferences  : 82
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 29
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 61
% 0.13/0.39  # Removed in clause preprocessing      : 4
% 0.13/0.39  # Initial clauses in saturation        : 57
% 0.13/0.39  # Processed clauses                    : 254
% 0.13/0.39  # ...of these trivial                  : 1
% 0.13/0.39  # ...subsumed                          : 45
% 0.13/0.39  # ...remaining for further processing  : 208
% 0.13/0.39  # Other redundant clauses eliminated   : 19
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 4
% 0.13/0.39  # Backward-rewritten                   : 32
% 0.13/0.39  # Generated clauses                    : 516
% 0.13/0.39  # ...of the previous two non-trivial   : 387
% 0.13/0.39  # Contextual simplify-reflections      : 0
% 0.13/0.39  # Paramodulations                      : 307
% 0.13/0.39  # Factorizations                       : 190
% 0.13/0.39  # Equation resolutions                 : 20
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 102
% 0.13/0.39  #    Positive orientable unit clauses  : 29
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 7
% 0.13/0.39  #    Non-unit-clauses                  : 66
% 0.13/0.39  # Current number of unprocessed clauses: 236
% 0.13/0.39  # ...number of literals in the above   : 1190
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 93
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 1091
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 290
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 28
% 0.13/0.39  # Unit Clause-clause subsumption calls : 134
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 42
% 0.13/0.39  # BW rewrite match successes           : 9
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 11438
% 0.13/0.40  
% 0.13/0.40  # -------------------------------------------------
% 0.13/0.40  # User time                : 0.049 s
% 0.13/0.40  # System time              : 0.004 s
% 0.13/0.40  # Total time               : 0.053 s
% 0.13/0.40  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
