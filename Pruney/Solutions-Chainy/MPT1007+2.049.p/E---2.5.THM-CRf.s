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
% DateTime   : Thu Dec  3 11:04:21 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 217 expanded)
%              Number of clauses        :   47 (  89 expanded)
%              Number of leaves         :   21 (  59 expanded)
%              Depth                    :   14
%              Number of atoms          :  258 ( 518 expanded)
%              Number of equality atoms :   73 ( 176 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t61_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,k1_tarski(X1),X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
     => ( X2 != k1_xboole_0
       => r2_hidden(k1_funct_1(X3,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t128_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),X4))
    <=> ( X1 = X3
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t166_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(t6_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5,X6,X7] :
                  ( ( r2_hidden(X3,X4)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X6,X7)
                    & r2_hidden(X7,X2) )
                 => r1_xboole_0(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(t172_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k1_relat_1(X2))
         => r2_hidden(k1_funct_1(X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t22_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
     => ( ! [X4] :
            ~ ( r2_hidden(X4,X2)
              & ! [X5] : ~ r2_hidden(k4_tarski(X4,X5),X3) )
      <=> k1_relset_1(X2,X1,X3) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

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

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(fc2_xboole_0,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
       => ( X2 != k1_xboole_0
         => r2_hidden(k1_funct_1(X3,X1),X2) ) ) ),
    inference(assume_negation,[status(cth)],[t61_funct_2])).

fof(c_0_22,negated_conjecture,
    ( v1_funct_1(esk8_0)
    & v1_funct_2(esk8_0,k1_tarski(esk6_0),esk7_0)
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk6_0),esk7_0)))
    & esk7_0 != k1_xboole_0
    & ~ r2_hidden(k1_funct_1(esk8_0,esk6_0),esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

fof(c_0_23,plain,(
    ! [X9] : k2_tarski(X9,X9) = k1_tarski(X9) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_24,plain,(
    ! [X10,X11] : k1_enumset1(X10,X10,X11) = k2_tarski(X10,X11) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_25,plain,(
    ! [X12,X13,X14] : k2_enumset1(X12,X12,X13,X14) = k1_enumset1(X12,X13,X14) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_26,plain,(
    ! [X16,X17,X18,X19] :
      ( ( X16 = X18
        | ~ r2_hidden(k4_tarski(X16,X17),k2_zfmisc_1(k1_tarski(X18),X19)) )
      & ( r2_hidden(X17,X19)
        | ~ r2_hidden(k4_tarski(X16,X17),k2_zfmisc_1(k1_tarski(X18),X19)) )
      & ( X16 != X18
        | ~ r2_hidden(X17,X19)
        | r2_hidden(k4_tarski(X16,X17),k2_zfmisc_1(k1_tarski(X18),X19)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t128_zfmisc_1])])])).

fof(c_0_27,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(X22))
      | ~ r2_hidden(X24,X23)
      | r2_hidden(X24,X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk6_0),esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_tarski(X2),X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31])).

fof(c_0_35,plain,(
    ! [X43,X44,X45] :
      ( ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
      | v1_relat_1(X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_36,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_29]),c_0_30]),c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_38,plain,(
    ! [X31,X32,X33,X35] :
      ( ( r2_hidden(esk2_3(X31,X32,X33),k2_relat_1(X33))
        | ~ r2_hidden(X31,k10_relat_1(X33,X32))
        | ~ v1_relat_1(X33) )
      & ( r2_hidden(k4_tarski(X31,esk2_3(X31,X32,X33)),X33)
        | ~ r2_hidden(X31,k10_relat_1(X33,X32))
        | ~ v1_relat_1(X33) )
      & ( r2_hidden(esk2_3(X31,X32,X33),X32)
        | ~ r2_hidden(X31,k10_relat_1(X33,X32))
        | ~ v1_relat_1(X33) )
      & ( ~ r2_hidden(X35,k2_relat_1(X33))
        | ~ r2_hidden(k4_tarski(X31,X35),X33)
        | ~ r2_hidden(X35,X32)
        | r2_hidden(X31,k10_relat_1(X33,X32))
        | ~ v1_relat_1(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

cnf(c_0_39,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( X1 = esk6_0
    | ~ r2_hidden(k4_tarski(X1,X2),esk8_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X1,X2,X3)),X3)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_34])).

fof(c_0_43,plain,(
    ! [X56,X58,X59,X60,X61,X62] :
      ( ( r2_hidden(esk5_1(X56),X56)
        | X56 = k1_xboole_0 )
      & ( ~ r2_hidden(X58,X59)
        | ~ r2_hidden(X59,X60)
        | ~ r2_hidden(X60,X61)
        | ~ r2_hidden(X61,X62)
        | ~ r2_hidden(X62,esk5_1(X56))
        | r1_xboole_0(X58,X56)
        | X56 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_mcart_1])])])])])])).

fof(c_0_44,plain,(
    ! [X46,X47,X48] :
      ( ( v4_relat_1(X48,X46)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) )
      & ( v5_relat_1(X48,X47)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_45,negated_conjecture,
    ( X1 = esk6_0
    | ~ r2_hidden(X1,k10_relat_1(esk8_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])])).

cnf(c_0_46,plain,
    ( r2_hidden(esk5_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_47,plain,(
    ! [X36] :
      ( ~ v1_relat_1(X36)
      | k10_relat_1(X36,k2_relat_1(X36)) = k1_relat_1(X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

fof(c_0_48,plain,(
    ! [X38,X39,X40] :
      ( ~ v1_relat_1(X39)
      | ~ v5_relat_1(X39,X38)
      | ~ v1_funct_1(X39)
      | ~ r2_hidden(X40,k1_relat_1(X39))
      | r2_hidden(k1_funct_1(X39,X40),X38) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t172_funct_1])])])).

cnf(c_0_49,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_50,plain,(
    ! [X41,X42] :
      ( ~ r2_hidden(X41,X42)
      | ~ r1_tarski(X42,X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_51,plain,(
    ! [X8] : r1_tarski(k1_xboole_0,X8) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_52,negated_conjecture,
    ( esk5_1(k10_relat_1(esk8_0,X1)) = esk6_0
    | k10_relat_1(esk8_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk8_0,esk6_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_55,plain,
    ( r2_hidden(k1_funct_1(X1,X3),X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_57,negated_conjecture,
    ( v5_relat_1(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_34])).

cnf(c_0_58,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_59,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_60,plain,(
    ! [X49,X50,X51,X53,X54] :
      ( ( r2_hidden(esk3_3(X49,X50,X51),X50)
        | k1_relset_1(X50,X49,X51) = X50
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X50,X49))) )
      & ( ~ r2_hidden(k4_tarski(esk3_3(X49,X50,X51),X53),X51)
        | k1_relset_1(X50,X49,X51) = X50
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X50,X49))) )
      & ( k1_relset_1(X50,X49,X51) != X50
        | ~ r2_hidden(X54,X50)
        | r2_hidden(k4_tarski(X54,esk4_4(X49,X50,X51,X54)),X51)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X50,X49))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_relset_1])])])])])])).

fof(c_0_61,plain,(
    ! [X25] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X25)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_62,plain,(
    ! [X63,X64,X65] :
      ( ( ~ v1_funct_2(X65,X63,X64)
        | X63 = k1_relset_1(X63,X64,X65)
        | X64 = k1_xboole_0
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))) )
      & ( X63 != k1_relset_1(X63,X64,X65)
        | v1_funct_2(X65,X63,X64)
        | X64 = k1_xboole_0
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))) )
      & ( ~ v1_funct_2(X65,X63,X64)
        | X63 = k1_relset_1(X63,X64,X65)
        | X63 != k1_xboole_0
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))) )
      & ( X63 != k1_relset_1(X63,X64,X65)
        | v1_funct_2(X65,X63,X64)
        | X63 != k1_xboole_0
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))) )
      & ( ~ v1_funct_2(X65,X63,X64)
        | X65 = k1_xboole_0
        | X63 = k1_xboole_0
        | X64 != k1_xboole_0
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))) )
      & ( X65 != k1_xboole_0
        | v1_funct_2(X65,X63,X64)
        | X63 = k1_xboole_0
        | X64 != k1_xboole_0
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_63,plain,(
    ! [X37] :
      ( ( k1_relat_1(X37) != k1_xboole_0
        | X37 = k1_xboole_0
        | ~ v1_relat_1(X37) )
      & ( k2_relat_1(X37) != k1_xboole_0
        | X37 = k1_xboole_0
        | ~ v1_relat_1(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

cnf(c_0_64,negated_conjecture,
    ( esk5_1(k1_relat_1(esk8_0)) = esk6_0
    | k1_relat_1(esk8_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_42])])).

cnf(c_0_65,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k1_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_57]),c_0_42])])).

cnf(c_0_66,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_67,plain,
    ( r2_hidden(k4_tarski(X4,esk4_4(X2,X1,X3,X4)),X3)
    | k1_relset_1(X1,X2,X3) != X1
    | ~ r2_hidden(X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_68,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_69,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_70,negated_conjecture,
    ( v1_funct_2(esk8_0,k1_tarski(esk6_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_71,plain,
    ( X1 = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_72,negated_conjecture,
    ( k1_relat_1(esk8_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_64]),c_0_65])).

cnf(c_0_73,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) != X1
    | ~ r2_hidden(X3,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68])])).

cnf(c_0_74,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) = X1
    | X2 = k1_xboole_0
    | ~ v1_funct_2(k1_xboole_0,X1,X2) ),
    inference(spm,[status(thm)],[c_0_69,c_0_68])).

cnf(c_0_75,negated_conjecture,
    ( v1_funct_2(esk8_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_29]),c_0_30]),c_0_31])).

cnf(c_0_76,negated_conjecture,
    ( esk8_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_42])])).

fof(c_0_77,plain,(
    ! [X26,X27] :
      ( ~ m1_subset_1(X26,X27)
      | v1_xboole_0(X27)
      | r2_hidden(X26,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_78,plain,(
    ! [X20] : m1_subset_1(esk1_1(X20),X20) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_79,plain,(
    ! [X15] : ~ v1_xboole_0(k1_tarski(X15)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

cnf(c_0_80,plain,
    ( X1 = k1_xboole_0
    | ~ v1_funct_2(k1_xboole_0,X2,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_81,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0) ),
    inference(rw,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_82,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_83,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_84,plain,
    ( m1_subset_1(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_85,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_86,negated_conjecture,
    ( ~ r2_hidden(X1,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82])).

cnf(c_0_87,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_88,plain,
    ( ~ v1_xboole_0(k2_enumset1(X1,X1,X1,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_29]),c_0_30]),c_0_31])).

cnf(c_0_89,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:07:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.20/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.030 s
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(t61_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r2_hidden(k1_funct_1(X3,X1),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 0.20/0.40  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.40  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.40  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.40  fof(t128_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),X4))<=>(X1=X3&r2_hidden(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 0.20/0.40  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.20/0.40  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.20/0.40  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 0.20/0.40  fof(t6_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5, X6, X7]:(((((r2_hidden(X3,X4)&r2_hidden(X4,X5))&r2_hidden(X5,X6))&r2_hidden(X6,X7))&r2_hidden(X7,X2))=>r1_xboole_0(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_mcart_1)).
% 0.20/0.40  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.20/0.40  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 0.20/0.40  fof(t172_funct_1, axiom, ![X1, X2]:(((v1_relat_1(X2)&v5_relat_1(X2,X1))&v1_funct_1(X2))=>![X3]:(r2_hidden(X3,k1_relat_1(X2))=>r2_hidden(k1_funct_1(X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 0.20/0.40  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.20/0.40  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.40  fof(t22_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~(r2_hidden(k4_tarski(X4,X5),X3))))<=>k1_relset_1(X2,X1,X3)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relset_1)).
% 0.20/0.40  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.20/0.40  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.20/0.40  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 0.20/0.40  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.20/0.40  fof(existence_m1_subset_1, axiom, ![X1]:?[X2]:m1_subset_1(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 0.20/0.40  fof(fc2_xboole_0, axiom, ![X1]:~(v1_xboole_0(k1_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 0.20/0.40  fof(c_0_21, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r2_hidden(k1_funct_1(X3,X1),X2)))), inference(assume_negation,[status(cth)],[t61_funct_2])).
% 0.20/0.40  fof(c_0_22, negated_conjecture, (((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,k1_tarski(esk6_0),esk7_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk6_0),esk7_0))))&(esk7_0!=k1_xboole_0&~r2_hidden(k1_funct_1(esk8_0,esk6_0),esk7_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.20/0.40  fof(c_0_23, plain, ![X9]:k2_tarski(X9,X9)=k1_tarski(X9), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.40  fof(c_0_24, plain, ![X10, X11]:k1_enumset1(X10,X10,X11)=k2_tarski(X10,X11), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.40  fof(c_0_25, plain, ![X12, X13, X14]:k2_enumset1(X12,X12,X13,X14)=k1_enumset1(X12,X13,X14), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.40  fof(c_0_26, plain, ![X16, X17, X18, X19]:(((X16=X18|~r2_hidden(k4_tarski(X16,X17),k2_zfmisc_1(k1_tarski(X18),X19)))&(r2_hidden(X17,X19)|~r2_hidden(k4_tarski(X16,X17),k2_zfmisc_1(k1_tarski(X18),X19))))&(X16!=X18|~r2_hidden(X17,X19)|r2_hidden(k4_tarski(X16,X17),k2_zfmisc_1(k1_tarski(X18),X19)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t128_zfmisc_1])])])).
% 0.20/0.40  fof(c_0_27, plain, ![X22, X23, X24]:(~m1_subset_1(X23,k1_zfmisc_1(X22))|(~r2_hidden(X24,X23)|r2_hidden(X24,X22))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.20/0.40  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk6_0),esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.40  cnf(c_0_29, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.40  cnf(c_0_30, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.40  cnf(c_0_31, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.40  cnf(c_0_32, plain, (X1=X2|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_tarski(X2),X4))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.40  cnf(c_0_33, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.40  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_31])).
% 0.20/0.40  fof(c_0_35, plain, ![X43, X44, X45]:(~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))|v1_relat_1(X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.20/0.40  cnf(c_0_36, plain, (X1=X2|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_29]), c_0_30]), c_0_31])).
% 0.20/0.40  cnf(c_0_37, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0))|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.40  fof(c_0_38, plain, ![X31, X32, X33, X35]:((((r2_hidden(esk2_3(X31,X32,X33),k2_relat_1(X33))|~r2_hidden(X31,k10_relat_1(X33,X32))|~v1_relat_1(X33))&(r2_hidden(k4_tarski(X31,esk2_3(X31,X32,X33)),X33)|~r2_hidden(X31,k10_relat_1(X33,X32))|~v1_relat_1(X33)))&(r2_hidden(esk2_3(X31,X32,X33),X32)|~r2_hidden(X31,k10_relat_1(X33,X32))|~v1_relat_1(X33)))&(~r2_hidden(X35,k2_relat_1(X33))|~r2_hidden(k4_tarski(X31,X35),X33)|~r2_hidden(X35,X32)|r2_hidden(X31,k10_relat_1(X33,X32))|~v1_relat_1(X33))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.20/0.40  cnf(c_0_39, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.40  cnf(c_0_40, negated_conjecture, (X1=esk6_0|~r2_hidden(k4_tarski(X1,X2),esk8_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.40  cnf(c_0_41, plain, (r2_hidden(k4_tarski(X1,esk2_3(X1,X2,X3)),X3)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.40  cnf(c_0_42, negated_conjecture, (v1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_39, c_0_34])).
% 0.20/0.40  fof(c_0_43, plain, ![X56, X58, X59, X60, X61, X62]:((r2_hidden(esk5_1(X56),X56)|X56=k1_xboole_0)&(~r2_hidden(X58,X59)|~r2_hidden(X59,X60)|~r2_hidden(X60,X61)|~r2_hidden(X61,X62)|~r2_hidden(X62,esk5_1(X56))|r1_xboole_0(X58,X56)|X56=k1_xboole_0)), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_mcart_1])])])])])])).
% 0.20/0.40  fof(c_0_44, plain, ![X46, X47, X48]:((v4_relat_1(X48,X46)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))))&(v5_relat_1(X48,X47)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.20/0.40  cnf(c_0_45, negated_conjecture, (X1=esk6_0|~r2_hidden(X1,k10_relat_1(esk8_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])])).
% 0.20/0.40  cnf(c_0_46, plain, (r2_hidden(esk5_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.40  fof(c_0_47, plain, ![X36]:(~v1_relat_1(X36)|k10_relat_1(X36,k2_relat_1(X36))=k1_relat_1(X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.20/0.40  fof(c_0_48, plain, ![X38, X39, X40]:(~v1_relat_1(X39)|~v5_relat_1(X39,X38)|~v1_funct_1(X39)|(~r2_hidden(X40,k1_relat_1(X39))|r2_hidden(k1_funct_1(X39,X40),X38))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t172_funct_1])])])).
% 0.20/0.40  cnf(c_0_49, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.40  fof(c_0_50, plain, ![X41, X42]:(~r2_hidden(X41,X42)|~r1_tarski(X42,X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.20/0.40  fof(c_0_51, plain, ![X8]:r1_tarski(k1_xboole_0,X8), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.40  cnf(c_0_52, negated_conjecture, (esk5_1(k10_relat_1(esk8_0,X1))=esk6_0|k10_relat_1(esk8_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.40  cnf(c_0_53, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.40  cnf(c_0_54, negated_conjecture, (~r2_hidden(k1_funct_1(esk8_0,esk6_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.40  cnf(c_0_55, plain, (r2_hidden(k1_funct_1(X1,X3),X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)|~v1_funct_1(X1)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.40  cnf(c_0_56, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.40  cnf(c_0_57, negated_conjecture, (v5_relat_1(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_49, c_0_34])).
% 0.20/0.40  cnf(c_0_58, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.40  cnf(c_0_59, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.40  fof(c_0_60, plain, ![X49, X50, X51, X53, X54]:(((r2_hidden(esk3_3(X49,X50,X51),X50)|k1_relset_1(X50,X49,X51)=X50|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X50,X49))))&(~r2_hidden(k4_tarski(esk3_3(X49,X50,X51),X53),X51)|k1_relset_1(X50,X49,X51)=X50|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X50,X49)))))&(k1_relset_1(X50,X49,X51)!=X50|(~r2_hidden(X54,X50)|r2_hidden(k4_tarski(X54,esk4_4(X49,X50,X51,X54)),X51))|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X50,X49))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_relset_1])])])])])])).
% 0.20/0.40  fof(c_0_61, plain, ![X25]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X25)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.20/0.40  fof(c_0_62, plain, ![X63, X64, X65]:((((~v1_funct_2(X65,X63,X64)|X63=k1_relset_1(X63,X64,X65)|X64=k1_xboole_0|~m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))))&(X63!=k1_relset_1(X63,X64,X65)|v1_funct_2(X65,X63,X64)|X64=k1_xboole_0|~m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64)))))&((~v1_funct_2(X65,X63,X64)|X63=k1_relset_1(X63,X64,X65)|X63!=k1_xboole_0|~m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))))&(X63!=k1_relset_1(X63,X64,X65)|v1_funct_2(X65,X63,X64)|X63!=k1_xboole_0|~m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))))))&((~v1_funct_2(X65,X63,X64)|X65=k1_xboole_0|X63=k1_xboole_0|X64!=k1_xboole_0|~m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))))&(X65!=k1_xboole_0|v1_funct_2(X65,X63,X64)|X63=k1_xboole_0|X64!=k1_xboole_0|~m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.20/0.40  fof(c_0_63, plain, ![X37]:((k1_relat_1(X37)!=k1_xboole_0|X37=k1_xboole_0|~v1_relat_1(X37))&(k2_relat_1(X37)!=k1_xboole_0|X37=k1_xboole_0|~v1_relat_1(X37))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.20/0.40  cnf(c_0_64, negated_conjecture, (esk5_1(k1_relat_1(esk8_0))=esk6_0|k1_relat_1(esk8_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_42])])).
% 0.20/0.40  cnf(c_0_65, negated_conjecture, (~r2_hidden(esk6_0,k1_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), c_0_57]), c_0_42])])).
% 0.20/0.40  cnf(c_0_66, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.20/0.40  cnf(c_0_67, plain, (r2_hidden(k4_tarski(X4,esk4_4(X2,X1,X3,X4)),X3)|k1_relset_1(X1,X2,X3)!=X1|~r2_hidden(X4,X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.40  cnf(c_0_68, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.20/0.40  cnf(c_0_69, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.20/0.40  cnf(c_0_70, negated_conjecture, (v1_funct_2(esk8_0,k1_tarski(esk6_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.40  cnf(c_0_71, plain, (X1=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.20/0.40  cnf(c_0_72, negated_conjecture, (k1_relat_1(esk8_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_64]), c_0_65])).
% 0.20/0.40  cnf(c_0_73, plain, (k1_relset_1(X1,X2,k1_xboole_0)!=X1|~r2_hidden(X3,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68])])).
% 0.20/0.40  cnf(c_0_74, plain, (k1_relset_1(X1,X2,k1_xboole_0)=X1|X2=k1_xboole_0|~v1_funct_2(k1_xboole_0,X1,X2)), inference(spm,[status(thm)],[c_0_69, c_0_68])).
% 0.20/0.40  cnf(c_0_75, negated_conjecture, (v1_funct_2(esk8_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_29]), c_0_30]), c_0_31])).
% 0.20/0.40  cnf(c_0_76, negated_conjecture, (esk8_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_42])])).
% 0.20/0.40  fof(c_0_77, plain, ![X26, X27]:(~m1_subset_1(X26,X27)|(v1_xboole_0(X27)|r2_hidden(X26,X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.20/0.40  fof(c_0_78, plain, ![X20]:m1_subset_1(esk1_1(X20),X20), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).
% 0.20/0.40  fof(c_0_79, plain, ![X15]:~v1_xboole_0(k1_tarski(X15)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).
% 0.20/0.40  cnf(c_0_80, plain, (X1=k1_xboole_0|~v1_funct_2(k1_xboole_0,X2,X1)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.20/0.40  cnf(c_0_81, negated_conjecture, (v1_funct_2(k1_xboole_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0)), inference(rw,[status(thm)],[c_0_75, c_0_76])).
% 0.20/0.40  cnf(c_0_82, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.40  cnf(c_0_83, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.20/0.40  cnf(c_0_84, plain, (m1_subset_1(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.20/0.40  cnf(c_0_85, plain, (~v1_xboole_0(k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.20/0.40  cnf(c_0_86, negated_conjecture, (~r2_hidden(X1,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_82])).
% 0.20/0.40  cnf(c_0_87, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.20/0.40  cnf(c_0_88, plain, (~v1_xboole_0(k2_enumset1(X1,X1,X1,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_29]), c_0_30]), c_0_31])).
% 0.20/0.40  cnf(c_0_89, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_88]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 90
% 0.20/0.40  # Proof object clause steps            : 47
% 0.20/0.40  # Proof object formula steps           : 43
% 0.20/0.40  # Proof object conjectures             : 23
% 0.20/0.40  # Proof object clause conjectures      : 20
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 25
% 0.20/0.40  # Proof object initial formulas used   : 21
% 0.20/0.40  # Proof object generating inferences   : 17
% 0.20/0.40  # Proof object simplifying inferences  : 28
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 22
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 41
% 0.20/0.40  # Removed in clause preprocessing      : 3
% 0.20/0.40  # Initial clauses in saturation        : 38
% 0.20/0.40  # Processed clauses                    : 267
% 0.20/0.40  # ...of these trivial                  : 0
% 0.20/0.40  # ...subsumed                          : 89
% 0.20/0.40  # ...remaining for further processing  : 178
% 0.20/0.40  # Other redundant clauses eliminated   : 6
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 11
% 0.20/0.40  # Backward-rewritten                   : 39
% 0.20/0.40  # Generated clauses                    : 805
% 0.20/0.40  # ...of the previous two non-trivial   : 602
% 0.20/0.40  # Contextual simplify-reflections      : 0
% 0.20/0.40  # Paramodulations                      : 800
% 0.20/0.40  # Factorizations                       : 0
% 0.20/0.40  # Equation resolutions                 : 6
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 123
% 0.20/0.40  #    Positive orientable unit clauses  : 20
% 0.20/0.40  #    Positive unorientable unit clauses: 0
% 0.20/0.40  #    Negative unit clauses             : 5
% 0.20/0.40  #    Non-unit-clauses                  : 98
% 0.20/0.40  # Current number of unprocessed clauses: 314
% 0.20/0.40  # ...number of literals in the above   : 1405
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 53
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 1611
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 737
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 51
% 0.20/0.40  # Unit Clause-clause subsumption calls : 271
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 16
% 0.20/0.40  # BW rewrite match successes           : 10
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 18101
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.053 s
% 0.20/0.40  # System time              : 0.004 s
% 0.20/0.40  # Total time               : 0.057 s
% 0.20/0.40  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
