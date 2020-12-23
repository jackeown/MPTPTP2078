%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:04:40 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  104 (3079 expanded)
%              Number of clauses        :   60 (1188 expanded)
%              Number of leaves         :   22 ( 890 expanded)
%              Depth                    :   17
%              Number of atoms          :  374 (6319 expanded)
%              Number of equality atoms :  139 (3544 expanded)
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

fof(t14_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( k1_relat_1(X2) = k1_tarski(X1)
       => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(dt_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

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

fof(t5_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( k1_relat_1(X3) = X1
          & ! [X4] :
              ( r2_hidden(X4,X1)
             => r2_hidden(k1_funct_1(X3,X4),X2) ) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

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

fof(d4_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( ( r2_hidden(X2,k1_relat_1(X1))
           => ( X3 = k1_funct_1(X1,X2)
            <=> r2_hidden(k4_tarski(X2,X3),X1) ) )
          & ( ~ r2_hidden(X2,k1_relat_1(X1))
           => ( X3 = k1_funct_1(X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

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

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
       => ( X2 != k1_xboole_0
         => k2_relset_1(k1_tarski(X1),X2,X3) = k1_tarski(k1_funct_1(X3,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t62_funct_2])).

fof(c_0_23,negated_conjecture,
    ( v1_funct_1(esk8_0)
    & v1_funct_2(esk8_0,k1_tarski(esk6_0),esk7_0)
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk6_0),esk7_0)))
    & esk7_0 != k1_xboole_0
    & k2_relset_1(k1_tarski(esk6_0),esk7_0,esk8_0) != k1_tarski(k1_funct_1(esk8_0,esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).

fof(c_0_24,plain,(
    ! [X8] : k2_tarski(X8,X8) = k1_tarski(X8) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_25,plain,(
    ! [X9,X10] : k1_enumset1(X9,X9,X10) = k2_tarski(X9,X10) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_26,plain,(
    ! [X11,X12,X13] : k2_enumset1(X11,X11,X12,X13) = k1_enumset1(X11,X12,X13) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_27,plain,(
    ! [X47,X48] :
      ( ~ v1_relat_1(X48)
      | ~ v1_funct_1(X48)
      | k1_relat_1(X48) != k1_tarski(X47)
      | k2_relat_1(X48) = k1_tarski(k1_funct_1(X48,X47)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_funct_1])])).

fof(c_0_28,plain,(
    ! [X51,X52,X53] :
      ( ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))
      | v1_relat_1(X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk6_0),esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_33,plain,(
    ! [X25,X26] :
      ( ( ~ m1_subset_1(X25,k1_zfmisc_1(X26))
        | r1_tarski(X25,X26) )
      & ( ~ r1_tarski(X25,X26)
        | m1_subset_1(X25,k1_zfmisc_1(X26)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_34,plain,(
    ! [X54,X55,X56] :
      ( ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))
      | m1_subset_1(k1_relset_1(X54,X55,X56),k1_zfmisc_1(X54)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).

fof(c_0_35,plain,(
    ! [X57,X58,X59] :
      ( ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58)))
      | k1_relset_1(X57,X58,X59) = k1_relat_1(X59) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_36,negated_conjecture,
    ( k2_relset_1(k1_tarski(esk6_0),esk7_0,esk8_0) != k1_tarski(k1_funct_1(esk8_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_37,plain,
    ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_relat_1(X1) != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32])).

fof(c_0_40,plain,(
    ! [X60,X61,X62] :
      ( ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))
      | k2_relset_1(X60,X61,X62) = k2_relat_1(X62) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_41,plain,(
    ! [X17,X18,X19,X20] :
      ( ( ~ r1_tarski(X20,k1_enumset1(X17,X18,X19))
        | X20 = k1_xboole_0
        | X20 = k1_tarski(X17)
        | X20 = k1_tarski(X18)
        | X20 = k1_tarski(X19)
        | X20 = k2_tarski(X17,X18)
        | X20 = k2_tarski(X18,X19)
        | X20 = k2_tarski(X17,X19)
        | X20 = k1_enumset1(X17,X18,X19) )
      & ( X20 != k1_xboole_0
        | r1_tarski(X20,k1_enumset1(X17,X18,X19)) )
      & ( X20 != k1_tarski(X17)
        | r1_tarski(X20,k1_enumset1(X17,X18,X19)) )
      & ( X20 != k1_tarski(X18)
        | r1_tarski(X20,k1_enumset1(X17,X18,X19)) )
      & ( X20 != k1_tarski(X19)
        | r1_tarski(X20,k1_enumset1(X17,X18,X19)) )
      & ( X20 != k2_tarski(X17,X18)
        | r1_tarski(X20,k1_enumset1(X17,X18,X19)) )
      & ( X20 != k2_tarski(X18,X19)
        | r1_tarski(X20,k1_enumset1(X17,X18,X19)) )
      & ( X20 != k2_tarski(X17,X19)
        | r1_tarski(X20,k1_enumset1(X17,X18,X19)) )
      & ( X20 != k1_enumset1(X17,X18,X19)
        | r1_tarski(X20,k1_enumset1(X17,X18,X19)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t142_zfmisc_1])])])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,plain,
    ( m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( k2_relset_1(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0,esk8_0) != k2_enumset1(k1_funct_1(esk8_0,esk6_0),k1_funct_1(esk8_0,esk6_0),k1_funct_1(esk8_0,esk6_0),k1_funct_1(esk8_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_32]),c_0_32])).

cnf(c_0_46,plain,
    ( k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2))
    | k1_relat_1(X1) != k2_enumset1(X2,X2,X2,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_32]),c_0_32])).

cnf(c_0_47,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_48,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_49,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_50,plain,(
    ! [X66,X67,X68] :
      ( ( v1_funct_1(X68)
        | r2_hidden(esk5_3(X66,X67,X68),X66)
        | k1_relat_1(X68) != X66
        | ~ v1_relat_1(X68)
        | ~ v1_funct_1(X68) )
      & ( v1_funct_2(X68,X66,X67)
        | r2_hidden(esk5_3(X66,X67,X68),X66)
        | k1_relat_1(X68) != X66
        | ~ v1_relat_1(X68)
        | ~ v1_funct_1(X68) )
      & ( m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67)))
        | r2_hidden(esk5_3(X66,X67,X68),X66)
        | k1_relat_1(X68) != X66
        | ~ v1_relat_1(X68)
        | ~ v1_funct_1(X68) )
      & ( v1_funct_1(X68)
        | ~ r2_hidden(k1_funct_1(X68,esk5_3(X66,X67,X68)),X67)
        | k1_relat_1(X68) != X66
        | ~ v1_relat_1(X68)
        | ~ v1_funct_1(X68) )
      & ( v1_funct_2(X68,X66,X67)
        | ~ r2_hidden(k1_funct_1(X68,esk5_3(X66,X67,X68)),X67)
        | k1_relat_1(X68) != X66
        | ~ v1_relat_1(X68)
        | ~ v1_funct_1(X68) )
      & ( m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67)))
        | ~ r2_hidden(k1_funct_1(X68,esk5_3(X66,X67,X68)),X67)
        | k1_relat_1(X68) != X66
        | ~ v1_relat_1(X68)
        | ~ v1_funct_1(X68) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_funct_2])])])])).

cnf(c_0_51,plain,
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

cnf(c_0_52,plain,
    ( r1_tarski(k1_relset_1(X1,X2,X3),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_53,negated_conjecture,
    ( k1_relset_1(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0,esk8_0) = k1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_39])).

cnf(c_0_54,negated_conjecture,
    ( k2_relset_1(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0,esk8_0) != k2_relat_1(esk8_0)
    | k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0) != k1_relat_1(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])]),c_0_48])])).

cnf(c_0_55,negated_conjecture,
    ( k2_relset_1(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0,esk8_0) = k2_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_39])).

fof(c_0_56,plain,(
    ! [X49,X50] :
      ( ~ r2_hidden(X49,X50)
      | ~ r1_tarski(X50,X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_57,plain,(
    ! [X7] : r1_tarski(k1_xboole_0,X7) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_58,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | r2_hidden(esk5_3(X2,X3,X1),X2)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

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
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_30]),c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_31]),c_0_31]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_32]),c_0_32]),c_0_32]),c_0_32]),c_0_32]),c_0_32])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk8_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_39])])).

cnf(c_0_61,negated_conjecture,
    ( k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0) != k1_relat_1(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55])])).

cnf(c_0_62,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_63,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_64,plain,
    ( r2_hidden(esk5_3(k1_relat_1(X1),X2,X1),k1_relat_1(X1))
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( k1_relat_1(esk8_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])).

cnf(c_0_66,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

fof(c_0_67,plain,(
    ! [X15,X16] :
      ( ( k2_zfmisc_1(X15,X16) != k1_xboole_0
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0 )
      & ( X15 != k1_xboole_0
        | k2_zfmisc_1(X15,X16) = k1_xboole_0 )
      & ( X16 != k1_xboole_0
        | k2_zfmisc_1(X15,X16) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_68,plain,(
    ! [X21,X22,X23] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(X21))
      | ~ r2_hidden(X23,X22)
      | r2_hidden(X23,X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_47]),c_0_48])]),c_0_66])).

cnf(c_0_70,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

fof(c_0_71,plain,(
    ! [X32,X33,X34,X35,X37,X38,X39,X40,X42] :
      ( ( r2_hidden(esk1_4(X32,X33,X34,X35),k1_relat_1(X32))
        | ~ r2_hidden(X35,X34)
        | X34 != k9_relat_1(X32,X33)
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( r2_hidden(esk1_4(X32,X33,X34,X35),X33)
        | ~ r2_hidden(X35,X34)
        | X34 != k9_relat_1(X32,X33)
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( X35 = k1_funct_1(X32,esk1_4(X32,X33,X34,X35))
        | ~ r2_hidden(X35,X34)
        | X34 != k9_relat_1(X32,X33)
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( ~ r2_hidden(X38,k1_relat_1(X32))
        | ~ r2_hidden(X38,X33)
        | X37 != k1_funct_1(X32,X38)
        | r2_hidden(X37,X34)
        | X34 != k9_relat_1(X32,X33)
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( ~ r2_hidden(esk2_3(X32,X39,X40),X40)
        | ~ r2_hidden(X42,k1_relat_1(X32))
        | ~ r2_hidden(X42,X39)
        | esk2_3(X32,X39,X40) != k1_funct_1(X32,X42)
        | X40 = k9_relat_1(X32,X39)
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( r2_hidden(esk3_3(X32,X39,X40),k1_relat_1(X32))
        | r2_hidden(esk2_3(X32,X39,X40),X40)
        | X40 = k9_relat_1(X32,X39)
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( r2_hidden(esk3_3(X32,X39,X40),X39)
        | r2_hidden(esk2_3(X32,X39,X40),X40)
        | X40 = k9_relat_1(X32,X39)
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( esk2_3(X32,X39,X40) = k1_funct_1(X32,esk3_3(X32,X39,X40))
        | r2_hidden(esk2_3(X32,X39,X40),X40)
        | X40 = k9_relat_1(X32,X39)
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).

cnf(c_0_72,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_74,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),k1_relat_1(X1))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_75,negated_conjecture,
    ( ~ r2_hidden(X1,esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_66])).

cnf(c_0_76,negated_conjecture,
    ( X1 = k9_relat_1(esk8_0,X2)
    | r2_hidden(esk2_3(esk8_0,X2,X1),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_47]),c_0_65]),c_0_48])]),c_0_66])).

fof(c_0_77,plain,(
    ! [X70,X71,X72,X73] :
      ( ~ v1_funct_1(X73)
      | ~ v1_funct_2(X73,X70,X71)
      | ~ m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(X70,X71)))
      | ~ r2_hidden(X72,X70)
      | X71 = k1_xboole_0
      | r2_hidden(k1_funct_1(X73,X72),k2_relset_1(X70,X71,X73)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_funct_2])])).

cnf(c_0_78,negated_conjecture,
    ( v1_funct_2(esk8_0,k1_tarski(esk6_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_79,plain,(
    ! [X44,X45,X46] :
      ( ( X46 != k1_funct_1(X44,X45)
        | r2_hidden(k4_tarski(X45,X46),X44)
        | ~ r2_hidden(X45,k1_relat_1(X44))
        | ~ v1_relat_1(X44)
        | ~ v1_funct_1(X44) )
      & ( ~ r2_hidden(k4_tarski(X45,X46),X44)
        | X46 = k1_funct_1(X44,X45)
        | ~ r2_hidden(X45,k1_relat_1(X44))
        | ~ v1_relat_1(X44)
        | ~ v1_funct_1(X44) )
      & ( X46 != k1_funct_1(X44,X45)
        | X46 = k1_xboole_0
        | r2_hidden(X45,k1_relat_1(X44))
        | ~ v1_relat_1(X44)
        | ~ v1_funct_1(X44) )
      & ( X46 != k1_xboole_0
        | X46 = k1_funct_1(X44,X45)
        | r2_hidden(X45,k1_relat_1(X44))
        | ~ v1_relat_1(X44)
        | ~ v1_funct_1(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).

fof(c_0_80,plain,(
    ! [X30,X31] :
      ( ~ v1_relat_1(X30)
      | ~ v1_funct_1(X30)
      | ~ m1_subset_1(X31,k1_zfmisc_1(X30))
      | v1_funct_1(X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_funct_1])])])).

fof(c_0_81,plain,(
    ! [X24] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X24)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_82,negated_conjecture,
    ( k9_relat_1(esk8_0,X1) = esk8_0 ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_83,plain,
    ( X3 = k1_xboole_0
    | r2_hidden(k1_funct_1(X1,X4),k2_relset_1(X2,X3,X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_84,negated_conjecture,
    ( v1_funct_2(esk8_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_85,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_86,plain,
    ( X1 = k1_funct_1(X2,X3)
    | r2_hidden(X3,k1_relat_1(X2))
    | X1 != k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_87,plain,
    ( v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_88,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_89,negated_conjecture,
    ( X1 = esk8_0
    | r2_hidden(esk2_3(esk8_0,X2,X1),X1) ),
    inference(rw,[status(thm)],[c_0_76,c_0_82])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk8_0,X1),k2_relat_1(esk8_0))
    | ~ r2_hidden(X1,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_55]),c_0_84]),c_0_47]),c_0_39])]),c_0_85])).

cnf(c_0_91,plain,
    ( k1_funct_1(X1,X2) = k1_xboole_0
    | r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_86])).

cnf(c_0_92,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_93,negated_conjecture,
    ( esk8_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_66,c_0_89])).

cnf(c_0_94,negated_conjecture,
    ( r2_hidden(k1_xboole_0,k2_relat_1(esk8_0))
    | ~ r2_hidden(X1,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_65]),c_0_47]),c_0_48])]),c_0_66])).

cnf(c_0_95,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_96,negated_conjecture,
    ( v1_funct_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_48]),c_0_47])])).

cnf(c_0_97,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_98,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_88])).

cnf(c_0_99,negated_conjecture,
    ( k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_93]),c_0_93])).

cnf(c_0_100,negated_conjecture,
    ( ~ r2_hidden(X1,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_93]),c_0_95]),c_0_66])).

cnf(c_0_101,negated_conjecture,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_3(k1_xboole_0,X2,X1),X1) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_96]),c_0_97]),c_0_98])]),c_0_99]),c_0_66])).

cnf(c_0_102,negated_conjecture,
    ( k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_61,c_0_65])).

cnf(c_0_103,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_102]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:29:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.43  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_URBAN_S0Y
% 0.21/0.43  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.21/0.43  #
% 0.21/0.43  # Preprocessing time       : 0.042 s
% 0.21/0.43  
% 0.21/0.43  # Proof found!
% 0.21/0.43  # SZS status Theorem
% 0.21/0.43  # SZS output start CNFRefutation
% 0.21/0.43  fof(t62_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>k2_relset_1(k1_tarski(X1),X2,X3)=k1_tarski(k1_funct_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 0.21/0.43  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.21/0.43  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.43  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.21/0.43  fof(t14_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 0.21/0.43  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.21/0.43  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.21/0.43  fof(dt_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 0.21/0.43  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.21/0.43  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.21/0.43  fof(t142_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r1_tarski(X4,k1_enumset1(X1,X2,X3))<=>~((((((((X4!=k1_xboole_0&X4!=k1_tarski(X1))&X4!=k1_tarski(X2))&X4!=k1_tarski(X3))&X4!=k2_tarski(X1,X2))&X4!=k2_tarski(X2,X3))&X4!=k2_tarski(X1,X3))&X4!=k1_enumset1(X1,X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 0.21/0.43  fof(t5_funct_2, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X3)=X1&![X4]:(r2_hidden(X4,X1)=>r2_hidden(k1_funct_1(X3,X4),X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_funct_2)).
% 0.21/0.43  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.21/0.43  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.21/0.43  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.21/0.43  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.21/0.43  fof(d12_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(X3=k9_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((r2_hidden(X5,k1_relat_1(X1))&r2_hidden(X5,X2))&X4=k1_funct_1(X1,X5))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_1)).
% 0.21/0.43  fof(t6_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_hidden(X3,X1)=>(X2=k1_xboole_0|r2_hidden(k1_funct_1(X4,X3),k2_relset_1(X1,X2,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 0.21/0.43  fof(d4_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:((r2_hidden(X2,k1_relat_1(X1))=>(X3=k1_funct_1(X1,X2)<=>r2_hidden(k4_tarski(X2,X3),X1)))&(~(r2_hidden(X2,k1_relat_1(X1)))=>(X3=k1_funct_1(X1,X2)<=>X3=k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 0.21/0.43  fof(cc3_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_funct_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_funct_1)).
% 0.21/0.43  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.21/0.43  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.21/0.43  fof(c_0_22, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>k2_relset_1(k1_tarski(X1),X2,X3)=k1_tarski(k1_funct_1(X3,X1))))), inference(assume_negation,[status(cth)],[t62_funct_2])).
% 0.21/0.43  fof(c_0_23, negated_conjecture, (((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,k1_tarski(esk6_0),esk7_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk6_0),esk7_0))))&(esk7_0!=k1_xboole_0&k2_relset_1(k1_tarski(esk6_0),esk7_0,esk8_0)!=k1_tarski(k1_funct_1(esk8_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).
% 0.21/0.43  fof(c_0_24, plain, ![X8]:k2_tarski(X8,X8)=k1_tarski(X8), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.43  fof(c_0_25, plain, ![X9, X10]:k1_enumset1(X9,X9,X10)=k2_tarski(X9,X10), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.43  fof(c_0_26, plain, ![X11, X12, X13]:k2_enumset1(X11,X11,X12,X13)=k1_enumset1(X11,X12,X13), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.21/0.43  fof(c_0_27, plain, ![X47, X48]:(~v1_relat_1(X48)|~v1_funct_1(X48)|(k1_relat_1(X48)!=k1_tarski(X47)|k2_relat_1(X48)=k1_tarski(k1_funct_1(X48,X47)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_funct_1])])).
% 0.21/0.43  fof(c_0_28, plain, ![X51, X52, X53]:(~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))|v1_relat_1(X53)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.21/0.43  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk6_0),esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.43  cnf(c_0_30, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.43  cnf(c_0_31, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.43  cnf(c_0_32, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.43  fof(c_0_33, plain, ![X25, X26]:((~m1_subset_1(X25,k1_zfmisc_1(X26))|r1_tarski(X25,X26))&(~r1_tarski(X25,X26)|m1_subset_1(X25,k1_zfmisc_1(X26)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.21/0.43  fof(c_0_34, plain, ![X54, X55, X56]:(~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))|m1_subset_1(k1_relset_1(X54,X55,X56),k1_zfmisc_1(X54))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).
% 0.21/0.43  fof(c_0_35, plain, ![X57, X58, X59]:(~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58)))|k1_relset_1(X57,X58,X59)=k1_relat_1(X59)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.21/0.43  cnf(c_0_36, negated_conjecture, (k2_relset_1(k1_tarski(esk6_0),esk7_0,esk8_0)!=k1_tarski(k1_funct_1(esk8_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.43  cnf(c_0_37, plain, (k2_relat_1(X1)=k1_tarski(k1_funct_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|k1_relat_1(X1)!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.43  cnf(c_0_38, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.43  cnf(c_0_39, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32])).
% 0.21/0.43  fof(c_0_40, plain, ![X60, X61, X62]:(~m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))|k2_relset_1(X60,X61,X62)=k2_relat_1(X62)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.21/0.43  fof(c_0_41, plain, ![X17, X18, X19, X20]:((~r1_tarski(X20,k1_enumset1(X17,X18,X19))|(X20=k1_xboole_0|X20=k1_tarski(X17)|X20=k1_tarski(X18)|X20=k1_tarski(X19)|X20=k2_tarski(X17,X18)|X20=k2_tarski(X18,X19)|X20=k2_tarski(X17,X19)|X20=k1_enumset1(X17,X18,X19)))&((((((((X20!=k1_xboole_0|r1_tarski(X20,k1_enumset1(X17,X18,X19)))&(X20!=k1_tarski(X17)|r1_tarski(X20,k1_enumset1(X17,X18,X19))))&(X20!=k1_tarski(X18)|r1_tarski(X20,k1_enumset1(X17,X18,X19))))&(X20!=k1_tarski(X19)|r1_tarski(X20,k1_enumset1(X17,X18,X19))))&(X20!=k2_tarski(X17,X18)|r1_tarski(X20,k1_enumset1(X17,X18,X19))))&(X20!=k2_tarski(X18,X19)|r1_tarski(X20,k1_enumset1(X17,X18,X19))))&(X20!=k2_tarski(X17,X19)|r1_tarski(X20,k1_enumset1(X17,X18,X19))))&(X20!=k1_enumset1(X17,X18,X19)|r1_tarski(X20,k1_enumset1(X17,X18,X19))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t142_zfmisc_1])])])).
% 0.21/0.43  cnf(c_0_42, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.43  cnf(c_0_43, plain, (m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.43  cnf(c_0_44, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.43  cnf(c_0_45, negated_conjecture, (k2_relset_1(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0,esk8_0)!=k2_enumset1(k1_funct_1(esk8_0,esk6_0),k1_funct_1(esk8_0,esk6_0),k1_funct_1(esk8_0,esk6_0),k1_funct_1(esk8_0,esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_30]), c_0_30]), c_0_31]), c_0_31]), c_0_32]), c_0_32])).
% 0.21/0.43  cnf(c_0_46, plain, (k2_relat_1(X1)=k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2))|k1_relat_1(X1)!=k2_enumset1(X2,X2,X2,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_30]), c_0_30]), c_0_31]), c_0_31]), c_0_32]), c_0_32])).
% 0.21/0.43  cnf(c_0_47, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.43  cnf(c_0_48, negated_conjecture, (v1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.21/0.43  cnf(c_0_49, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.21/0.43  fof(c_0_50, plain, ![X66, X67, X68]:((((v1_funct_1(X68)|(r2_hidden(esk5_3(X66,X67,X68),X66)|k1_relat_1(X68)!=X66)|(~v1_relat_1(X68)|~v1_funct_1(X68)))&(v1_funct_2(X68,X66,X67)|(r2_hidden(esk5_3(X66,X67,X68),X66)|k1_relat_1(X68)!=X66)|(~v1_relat_1(X68)|~v1_funct_1(X68))))&(m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67)))|(r2_hidden(esk5_3(X66,X67,X68),X66)|k1_relat_1(X68)!=X66)|(~v1_relat_1(X68)|~v1_funct_1(X68))))&(((v1_funct_1(X68)|(~r2_hidden(k1_funct_1(X68,esk5_3(X66,X67,X68)),X67)|k1_relat_1(X68)!=X66)|(~v1_relat_1(X68)|~v1_funct_1(X68)))&(v1_funct_2(X68,X66,X67)|(~r2_hidden(k1_funct_1(X68,esk5_3(X66,X67,X68)),X67)|k1_relat_1(X68)!=X66)|(~v1_relat_1(X68)|~v1_funct_1(X68))))&(m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67)))|(~r2_hidden(k1_funct_1(X68,esk5_3(X66,X67,X68)),X67)|k1_relat_1(X68)!=X66)|(~v1_relat_1(X68)|~v1_funct_1(X68))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_funct_2])])])])).
% 0.21/0.43  cnf(c_0_51, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|X1=k1_tarski(X3)|X1=k1_tarski(X4)|X1=k2_tarski(X2,X3)|X1=k2_tarski(X3,X4)|X1=k2_tarski(X2,X4)|X1=k1_enumset1(X2,X3,X4)|~r1_tarski(X1,k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.21/0.43  cnf(c_0_52, plain, (r1_tarski(k1_relset_1(X1,X2,X3),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.21/0.43  cnf(c_0_53, negated_conjecture, (k1_relset_1(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0,esk8_0)=k1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_44, c_0_39])).
% 0.21/0.43  cnf(c_0_54, negated_conjecture, (k2_relset_1(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0,esk8_0)!=k2_relat_1(esk8_0)|k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)!=k1_relat_1(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])]), c_0_48])])).
% 0.21/0.43  cnf(c_0_55, negated_conjecture, (k2_relset_1(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0,esk8_0)=k2_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_49, c_0_39])).
% 0.21/0.43  fof(c_0_56, plain, ![X49, X50]:(~r2_hidden(X49,X50)|~r1_tarski(X50,X49)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.21/0.43  fof(c_0_57, plain, ![X7]:r1_tarski(k1_xboole_0,X7), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.21/0.43  cnf(c_0_58, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|r2_hidden(esk5_3(X2,X3,X1),X2)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.21/0.43  cnf(c_0_59, plain, (X1=k1_xboole_0|X1=k2_enumset1(X4,X4,X4,X4)|X1=k2_enumset1(X3,X3,X3,X4)|X1=k2_enumset1(X3,X3,X3,X3)|X1=k2_enumset1(X2,X2,X3,X4)|X1=k2_enumset1(X2,X2,X2,X4)|X1=k2_enumset1(X2,X2,X2,X3)|X1=k2_enumset1(X2,X2,X2,X2)|~r1_tarski(X1,k2_enumset1(X2,X2,X3,X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_30]), c_0_30]), c_0_30]), c_0_31]), c_0_31]), c_0_31]), c_0_31]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_32]), c_0_32]), c_0_32]), c_0_32]), c_0_32]), c_0_32])).
% 0.21/0.43  cnf(c_0_60, negated_conjecture, (r1_tarski(k1_relat_1(esk8_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_39])])).
% 0.21/0.43  cnf(c_0_61, negated_conjecture, (k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)!=k1_relat_1(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55])])).
% 0.21/0.43  cnf(c_0_62, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.21/0.43  cnf(c_0_63, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.21/0.43  cnf(c_0_64, plain, (r2_hidden(esk5_3(k1_relat_1(X1),X2,X1),k1_relat_1(X1))|m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_58])).
% 0.21/0.43  cnf(c_0_65, negated_conjecture, (k1_relat_1(esk8_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61])).
% 0.21/0.43  cnf(c_0_66, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.21/0.43  fof(c_0_67, plain, ![X15, X16]:((k2_zfmisc_1(X15,X16)!=k1_xboole_0|(X15=k1_xboole_0|X16=k1_xboole_0))&((X15!=k1_xboole_0|k2_zfmisc_1(X15,X16)=k1_xboole_0)&(X16!=k1_xboole_0|k2_zfmisc_1(X15,X16)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.21/0.43  fof(c_0_68, plain, ![X21, X22, X23]:(~m1_subset_1(X22,k1_zfmisc_1(X21))|(~r2_hidden(X23,X22)|r2_hidden(X23,X21))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.21/0.43  cnf(c_0_69, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_47]), c_0_48])]), c_0_66])).
% 0.21/0.43  cnf(c_0_70, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.21/0.43  fof(c_0_71, plain, ![X32, X33, X34, X35, X37, X38, X39, X40, X42]:(((((r2_hidden(esk1_4(X32,X33,X34,X35),k1_relat_1(X32))|~r2_hidden(X35,X34)|X34!=k9_relat_1(X32,X33)|(~v1_relat_1(X32)|~v1_funct_1(X32)))&(r2_hidden(esk1_4(X32,X33,X34,X35),X33)|~r2_hidden(X35,X34)|X34!=k9_relat_1(X32,X33)|(~v1_relat_1(X32)|~v1_funct_1(X32))))&(X35=k1_funct_1(X32,esk1_4(X32,X33,X34,X35))|~r2_hidden(X35,X34)|X34!=k9_relat_1(X32,X33)|(~v1_relat_1(X32)|~v1_funct_1(X32))))&(~r2_hidden(X38,k1_relat_1(X32))|~r2_hidden(X38,X33)|X37!=k1_funct_1(X32,X38)|r2_hidden(X37,X34)|X34!=k9_relat_1(X32,X33)|(~v1_relat_1(X32)|~v1_funct_1(X32))))&((~r2_hidden(esk2_3(X32,X39,X40),X40)|(~r2_hidden(X42,k1_relat_1(X32))|~r2_hidden(X42,X39)|esk2_3(X32,X39,X40)!=k1_funct_1(X32,X42))|X40=k9_relat_1(X32,X39)|(~v1_relat_1(X32)|~v1_funct_1(X32)))&(((r2_hidden(esk3_3(X32,X39,X40),k1_relat_1(X32))|r2_hidden(esk2_3(X32,X39,X40),X40)|X40=k9_relat_1(X32,X39)|(~v1_relat_1(X32)|~v1_funct_1(X32)))&(r2_hidden(esk3_3(X32,X39,X40),X39)|r2_hidden(esk2_3(X32,X39,X40),X40)|X40=k9_relat_1(X32,X39)|(~v1_relat_1(X32)|~v1_funct_1(X32))))&(esk2_3(X32,X39,X40)=k1_funct_1(X32,esk3_3(X32,X39,X40))|r2_hidden(esk2_3(X32,X39,X40),X40)|X40=k9_relat_1(X32,X39)|(~v1_relat_1(X32)|~v1_funct_1(X32)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).
% 0.21/0.43  cnf(c_0_72, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.21/0.43  cnf(c_0_73, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.21/0.43  cnf(c_0_74, plain, (r2_hidden(esk3_3(X1,X2,X3),k1_relat_1(X1))|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.21/0.43  cnf(c_0_75, negated_conjecture, (~r2_hidden(X1,esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_66])).
% 0.21/0.43  cnf(c_0_76, negated_conjecture, (X1=k9_relat_1(esk8_0,X2)|r2_hidden(esk2_3(esk8_0,X2,X1),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_47]), c_0_65]), c_0_48])]), c_0_66])).
% 0.21/0.43  fof(c_0_77, plain, ![X70, X71, X72, X73]:(~v1_funct_1(X73)|~v1_funct_2(X73,X70,X71)|~m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(X70,X71)))|(~r2_hidden(X72,X70)|(X71=k1_xboole_0|r2_hidden(k1_funct_1(X73,X72),k2_relset_1(X70,X71,X73))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_funct_2])])).
% 0.21/0.43  cnf(c_0_78, negated_conjecture, (v1_funct_2(esk8_0,k1_tarski(esk6_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.43  fof(c_0_79, plain, ![X44, X45, X46]:(((X46!=k1_funct_1(X44,X45)|r2_hidden(k4_tarski(X45,X46),X44)|~r2_hidden(X45,k1_relat_1(X44))|(~v1_relat_1(X44)|~v1_funct_1(X44)))&(~r2_hidden(k4_tarski(X45,X46),X44)|X46=k1_funct_1(X44,X45)|~r2_hidden(X45,k1_relat_1(X44))|(~v1_relat_1(X44)|~v1_funct_1(X44))))&((X46!=k1_funct_1(X44,X45)|X46=k1_xboole_0|r2_hidden(X45,k1_relat_1(X44))|(~v1_relat_1(X44)|~v1_funct_1(X44)))&(X46!=k1_xboole_0|X46=k1_funct_1(X44,X45)|r2_hidden(X45,k1_relat_1(X44))|(~v1_relat_1(X44)|~v1_funct_1(X44))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).
% 0.21/0.43  fof(c_0_80, plain, ![X30, X31]:(~v1_relat_1(X30)|~v1_funct_1(X30)|(~m1_subset_1(X31,k1_zfmisc_1(X30))|v1_funct_1(X31))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_funct_1])])])).
% 0.21/0.43  fof(c_0_81, plain, ![X24]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X24)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.21/0.43  cnf(c_0_82, negated_conjecture, (k9_relat_1(esk8_0,X1)=esk8_0), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.21/0.43  cnf(c_0_83, plain, (X3=k1_xboole_0|r2_hidden(k1_funct_1(X1,X4),k2_relset_1(X2,X3,X1))|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.21/0.43  cnf(c_0_84, negated_conjecture, (v1_funct_2(esk8_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_30]), c_0_31]), c_0_32])).
% 0.21/0.43  cnf(c_0_85, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.43  cnf(c_0_86, plain, (X1=k1_funct_1(X2,X3)|r2_hidden(X3,k1_relat_1(X2))|X1!=k1_xboole_0|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.21/0.43  cnf(c_0_87, plain, (v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.21/0.43  cnf(c_0_88, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.21/0.43  cnf(c_0_89, negated_conjecture, (X1=esk8_0|r2_hidden(esk2_3(esk8_0,X2,X1),X1)), inference(rw,[status(thm)],[c_0_76, c_0_82])).
% 0.21/0.43  cnf(c_0_90, negated_conjecture, (r2_hidden(k1_funct_1(esk8_0,X1),k2_relat_1(esk8_0))|~r2_hidden(X1,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_55]), c_0_84]), c_0_47]), c_0_39])]), c_0_85])).
% 0.21/0.43  cnf(c_0_91, plain, (k1_funct_1(X1,X2)=k1_xboole_0|r2_hidden(X2,k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_86])).
% 0.21/0.43  cnf(c_0_92, plain, (v1_funct_1(k1_xboole_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.21/0.43  cnf(c_0_93, negated_conjecture, (esk8_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_66, c_0_89])).
% 0.21/0.43  cnf(c_0_94, negated_conjecture, (r2_hidden(k1_xboole_0,k2_relat_1(esk8_0))|~r2_hidden(X1,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_65]), c_0_47]), c_0_48])]), c_0_66])).
% 0.21/0.43  cnf(c_0_95, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.21/0.43  cnf(c_0_96, negated_conjecture, (v1_funct_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_48]), c_0_47])])).
% 0.21/0.43  cnf(c_0_97, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.21/0.43  cnf(c_0_98, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_38, c_0_88])).
% 0.21/0.43  cnf(c_0_99, negated_conjecture, (k9_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_93]), c_0_93])).
% 0.21/0.43  cnf(c_0_100, negated_conjecture, (~r2_hidden(X1,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_93]), c_0_95]), c_0_66])).
% 0.21/0.43  cnf(c_0_101, negated_conjecture, (X1=k1_xboole_0|r2_hidden(esk2_3(k1_xboole_0,X2,X1),X1)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_96]), c_0_97]), c_0_98])]), c_0_99]), c_0_66])).
% 0.21/0.43  cnf(c_0_102, negated_conjecture, (k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_61, c_0_65])).
% 0.21/0.43  cnf(c_0_103, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_102]), ['proof']).
% 0.21/0.43  # SZS output end CNFRefutation
% 0.21/0.43  # Proof object total steps             : 104
% 0.21/0.43  # Proof object clause steps            : 60
% 0.21/0.43  # Proof object formula steps           : 44
% 0.21/0.43  # Proof object conjectures             : 33
% 0.21/0.43  # Proof object clause conjectures      : 30
% 0.21/0.43  # Proof object formula conjectures     : 3
% 0.21/0.43  # Proof object initial clauses used    : 27
% 0.21/0.43  # Proof object initial formulas used   : 22
% 0.21/0.43  # Proof object generating inferences   : 23
% 0.21/0.43  # Proof object simplifying inferences  : 78
% 0.21/0.43  # Training examples: 0 positive, 0 negative
% 0.21/0.43  # Parsed axioms                        : 27
% 0.21/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.43  # Initial clauses                      : 61
% 0.21/0.43  # Removed in clause preprocessing      : 5
% 0.21/0.43  # Initial clauses in saturation        : 56
% 0.21/0.43  # Processed clauses                    : 341
% 0.21/0.43  # ...of these trivial                  : 3
% 0.21/0.43  # ...subsumed                          : 118
% 0.21/0.43  # ...remaining for further processing  : 220
% 0.21/0.43  # Other redundant clauses eliminated   : 12
% 0.21/0.43  # Clauses deleted for lack of memory   : 0
% 0.21/0.43  # Backward-subsumed                    : 9
% 0.21/0.43  # Backward-rewritten                   : 45
% 0.21/0.43  # Generated clauses                    : 1070
% 0.21/0.43  # ...of the previous two non-trivial   : 989
% 0.21/0.43  # Contextual simplify-reflections      : 3
% 0.21/0.43  # Paramodulations                      : 1038
% 0.21/0.43  # Factorizations                       : 0
% 0.21/0.43  # Equation resolutions                 : 32
% 0.21/0.43  # Propositional unsat checks           : 0
% 0.21/0.43  #    Propositional check models        : 0
% 0.21/0.43  #    Propositional check unsatisfiable : 0
% 0.21/0.43  #    Propositional clauses             : 0
% 0.21/0.43  #    Propositional clauses after purity: 0
% 0.21/0.43  #    Propositional unsat core size     : 0
% 0.21/0.43  #    Propositional preprocessing time  : 0.000
% 0.21/0.43  #    Propositional encoding time       : 0.000
% 0.21/0.43  #    Propositional solver time         : 0.000
% 0.21/0.43  #    Success case prop preproc time    : 0.000
% 0.21/0.43  #    Success case prop encoding time   : 0.000
% 0.21/0.43  #    Success case prop solver time     : 0.000
% 0.21/0.43  # Current number of processed clauses  : 166
% 0.21/0.43  #    Positive orientable unit clauses  : 24
% 0.21/0.43  #    Positive unorientable unit clauses: 0
% 0.21/0.43  #    Negative unit clauses             : 8
% 0.21/0.43  #    Non-unit-clauses                  : 134
% 0.21/0.43  # Current number of unprocessed clauses: 673
% 0.21/0.43  # ...number of literals in the above   : 2784
% 0.21/0.43  # Current number of archived formulas  : 0
% 0.21/0.43  # Current number of archived clauses   : 57
% 0.21/0.43  # Clause-clause subsumption calls (NU) : 5014
% 0.21/0.43  # Rec. Clause-clause subsumption calls : 2324
% 0.21/0.43  # Non-unit clause-clause subsumptions  : 65
% 0.21/0.43  # Unit Clause-clause subsumption calls : 317
% 0.21/0.43  # Rewrite failures with RHS unbound    : 0
% 0.21/0.43  # BW rewrite match attempts            : 30
% 0.21/0.43  # BW rewrite match successes           : 10
% 0.21/0.43  # Condensation attempts                : 0
% 0.21/0.43  # Condensation successes               : 0
% 0.21/0.43  # Termbank termtop insertions          : 20014
% 0.21/0.43  
% 0.21/0.43  # -------------------------------------------------
% 0.21/0.43  # User time                : 0.083 s
% 0.21/0.43  # System time              : 0.005 s
% 0.21/0.43  # Total time               : 0.088 s
% 0.21/0.43  # Maximum resident set size: 1612 pages
%------------------------------------------------------------------------------
