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
% DateTime   : Thu Dec  3 11:05:21 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 432 expanded)
%              Number of clauses        :   41 ( 177 expanded)
%              Number of leaves         :   14 ( 114 expanded)
%              Depth                    :   13
%              Number of atoms          :  215 (1160 expanded)
%              Number of equality atoms :   83 ( 418 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t65_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,k1_tarski(X2))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
     => ( r2_hidden(X3,X1)
       => k1_funct_1(X4,X3) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t129_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k1_tarski(X4)))
    <=> ( r2_hidden(X1,X3)
        & X2 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

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

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(t31_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

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

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,k1_tarski(X2))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
       => ( r2_hidden(X3,X1)
         => k1_funct_1(X4,X3) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t65_funct_2])).

fof(c_0_15,negated_conjecture,
    ( v1_funct_1(esk8_0)
    & v1_funct_2(esk8_0,esk5_0,k1_tarski(esk6_0))
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0))))
    & r2_hidden(esk7_0,esk5_0)
    & k1_funct_1(esk8_0,esk7_0) != esk6_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_16,plain,(
    ! [X9] : k2_tarski(X9,X9) = k1_tarski(X9) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_17,plain,(
    ! [X10,X11] : k1_enumset1(X10,X10,X11) = k2_tarski(X10,X11) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_18,plain,(
    ! [X12,X13,X14] : k2_enumset1(X12,X12,X13,X14) = k1_enumset1(X12,X13,X14) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_19,plain,(
    ! [X26,X27,X28,X29] :
      ( ( r2_hidden(X26,X28)
        | ~ r2_hidden(k4_tarski(X26,X27),k2_zfmisc_1(X28,k1_tarski(X29))) )
      & ( X27 = X29
        | ~ r2_hidden(k4_tarski(X26,X27),k2_zfmisc_1(X28,k1_tarski(X29))) )
      & ( ~ r2_hidden(X26,X28)
        | X27 != X29
        | r2_hidden(k4_tarski(X26,X27),k2_zfmisc_1(X28,k1_tarski(X29))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t129_zfmisc_1])])])).

fof(c_0_20,plain,(
    ! [X31,X32,X33] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(X31))
      | ~ r2_hidden(X33,X32)
      | r2_hidden(X33,X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24])).

fof(c_0_28,plain,(
    ! [X34,X35,X36] :
      ( ( X36 != k1_funct_1(X34,X35)
        | r2_hidden(k4_tarski(X35,X36),X34)
        | ~ r2_hidden(X35,k1_relat_1(X34))
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) )
      & ( ~ r2_hidden(k4_tarski(X35,X36),X34)
        | X36 = k1_funct_1(X34,X35)
        | ~ r2_hidden(X35,k1_relat_1(X34))
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) )
      & ( X36 != k1_funct_1(X34,X35)
        | X36 = k1_xboole_0
        | r2_hidden(X35,k1_relat_1(X34))
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) )
      & ( X36 != k1_xboole_0
        | X36 = k1_funct_1(X34,X35)
        | r2_hidden(X35,k1_relat_1(X34))
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).

fof(c_0_29,plain,(
    ! [X39,X40,X41] :
      ( ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
      | v1_relat_1(X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_30,plain,(
    ! [X37,X38] :
      ( ~ r2_hidden(X37,X38)
      | ~ r1_tarski(X38,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_31,plain,(
    ! [X8] : r1_tarski(k1_xboole_0,X8) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_32,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,k2_enumset1(X2,X2,X2,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_22]),c_0_23]),c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | X1 != k1_funct_1(X2,X3)
    | ~ r2_hidden(X3,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_36,plain,(
    ! [X42,X43,X44] :
      ( ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
      | k1_relset_1(X42,X43,X44) = k1_relat_1(X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_37,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_39,plain,(
    ! [X15,X16,X17,X19,X20,X21,X22,X24] :
      ( ( r2_hidden(X17,esk1_3(X15,X16,X17))
        | ~ r2_hidden(X17,X16)
        | X16 != k3_tarski(X15) )
      & ( r2_hidden(esk1_3(X15,X16,X17),X15)
        | ~ r2_hidden(X17,X16)
        | X16 != k3_tarski(X15) )
      & ( ~ r2_hidden(X19,X20)
        | ~ r2_hidden(X20,X15)
        | r2_hidden(X19,X16)
        | X16 != k3_tarski(X15) )
      & ( ~ r2_hidden(esk2_2(X21,X22),X22)
        | ~ r2_hidden(esk2_2(X21,X22),X24)
        | ~ r2_hidden(X24,X21)
        | X22 = k3_tarski(X21) )
      & ( r2_hidden(esk2_2(X21,X22),esk3_2(X21,X22))
        | r2_hidden(esk2_2(X21,X22),X22)
        | X22 = k3_tarski(X21) )
      & ( r2_hidden(esk3_2(X21,X22),X21)
        | r2_hidden(esk2_2(X21,X22),X22)
        | X22 = k3_tarski(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_40,negated_conjecture,
    ( X1 = esk6_0
    | ~ r2_hidden(k4_tarski(X2,X1),esk8_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_41,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_43,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_27])).

cnf(c_0_44,plain,
    ( X1 = k1_funct_1(X2,X3)
    | r2_hidden(X3,k1_relat_1(X2))
    | X1 != k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_45,plain,(
    ! [X30] : k3_tarski(k1_tarski(X30)) = X30 ),
    inference(variable_rename,[status(thm)],[t31_zfmisc_1])).

fof(c_0_46,plain,(
    ! [X52,X53,X54] :
      ( ( ~ v1_funct_2(X54,X52,X53)
        | X52 = k1_relset_1(X52,X53,X54)
        | X53 = k1_xboole_0
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) )
      & ( X52 != k1_relset_1(X52,X53,X54)
        | v1_funct_2(X54,X52,X53)
        | X53 = k1_xboole_0
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) )
      & ( ~ v1_funct_2(X54,X52,X53)
        | X52 = k1_relset_1(X52,X53,X54)
        | X52 != k1_xboole_0
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) )
      & ( X52 != k1_relset_1(X52,X53,X54)
        | v1_funct_2(X54,X52,X53)
        | X52 != k1_xboole_0
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) )
      & ( ~ v1_funct_2(X54,X52,X53)
        | X54 = k1_xboole_0
        | X52 = k1_xboole_0
        | X53 != k1_xboole_0
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) )
      & ( X54 != k1_xboole_0
        | v1_funct_2(X54,X52,X53)
        | X52 = k1_xboole_0
        | X53 != k1_xboole_0
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_47,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_2(esk8_0,esk5_0,k1_tarski(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_49,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_50,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r2_hidden(esk2_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_51,negated_conjecture,
    ( k1_funct_1(esk8_0,X1) = esk6_0
    | ~ r2_hidden(X1,k1_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_43])])).

cnf(c_0_52,plain,
    ( k1_funct_1(X1,X2) = k1_xboole_0
    | r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_53,plain,
    ( k3_tarski(k1_tarski(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( k1_relset_1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk8_0) = k1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_27])).

cnf(c_0_56,negated_conjecture,
    ( v1_funct_2(esk8_0,esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_22]),c_0_23]),c_0_24])).

cnf(c_0_57,plain,
    ( X1 = k3_tarski(k1_xboole_0)
    | r2_hidden(esk2_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( k1_funct_1(esk8_0,esk7_0) != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_59,negated_conjecture,
    ( k1_funct_1(esk8_0,X1) = k1_xboole_0
    | k1_funct_1(esk8_0,X1) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_42]),c_0_43])])).

cnf(c_0_60,plain,
    ( k3_tarski(k2_enumset1(X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_22]),c_0_23]),c_0_24])).

cnf(c_0_61,negated_conjecture,
    ( k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0) = k1_xboole_0
    | k1_relat_1(esk8_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_27]),c_0_55]),c_0_56])])).

cnf(c_0_62,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( k1_funct_1(esk8_0,esk7_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( k1_relat_1(esk8_0) = esk5_0
    | esk6_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_58,c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( k1_relat_1(esk8_0) = esk5_0 ),
    inference(sr,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_67,negated_conjecture,
    ( k1_funct_1(esk8_0,X1) = esk6_0
    | ~ r2_hidden(X1,esk5_0) ),
    inference(rw,[status(thm)],[c_0_51,c_0_66])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk7_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_67]),c_0_68])]),c_0_65]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:14:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.39  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.12/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.39  #
% 0.12/0.39  # Preprocessing time       : 0.028 s
% 0.12/0.39  
% 0.12/0.39  # Proof found!
% 0.12/0.39  # SZS status Theorem
% 0.12/0.39  # SZS output start CNFRefutation
% 0.12/0.39  fof(t65_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>(r2_hidden(X3,X1)=>k1_funct_1(X4,X3)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 0.12/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.12/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.12/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.12/0.39  fof(t129_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k1_tarski(X4)))<=>(r2_hidden(X1,X3)&X2=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 0.12/0.39  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.12/0.39  fof(d4_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:((r2_hidden(X2,k1_relat_1(X1))=>(X3=k1_funct_1(X1,X2)<=>r2_hidden(k4_tarski(X2,X3),X1)))&(~(r2_hidden(X2,k1_relat_1(X1)))=>(X3=k1_funct_1(X1,X2)<=>X3=k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 0.12/0.39  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.12/0.39  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.12/0.39  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.12/0.39  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.12/0.39  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 0.12/0.39  fof(t31_zfmisc_1, axiom, ![X1]:k3_tarski(k1_tarski(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 0.12/0.39  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.12/0.39  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>(r2_hidden(X3,X1)=>k1_funct_1(X4,X3)=X2))), inference(assume_negation,[status(cth)],[t65_funct_2])).
% 0.12/0.39  fof(c_0_15, negated_conjecture, (((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,esk5_0,k1_tarski(esk6_0)))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0)))))&(r2_hidden(esk7_0,esk5_0)&k1_funct_1(esk8_0,esk7_0)!=esk6_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.12/0.39  fof(c_0_16, plain, ![X9]:k2_tarski(X9,X9)=k1_tarski(X9), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.12/0.39  fof(c_0_17, plain, ![X10, X11]:k1_enumset1(X10,X10,X11)=k2_tarski(X10,X11), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.12/0.39  fof(c_0_18, plain, ![X12, X13, X14]:k2_enumset1(X12,X12,X13,X14)=k1_enumset1(X12,X13,X14), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.12/0.39  fof(c_0_19, plain, ![X26, X27, X28, X29]:(((r2_hidden(X26,X28)|~r2_hidden(k4_tarski(X26,X27),k2_zfmisc_1(X28,k1_tarski(X29))))&(X27=X29|~r2_hidden(k4_tarski(X26,X27),k2_zfmisc_1(X28,k1_tarski(X29)))))&(~r2_hidden(X26,X28)|X27!=X29|r2_hidden(k4_tarski(X26,X27),k2_zfmisc_1(X28,k1_tarski(X29))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t129_zfmisc_1])])])).
% 0.12/0.39  fof(c_0_20, plain, ![X31, X32, X33]:(~m1_subset_1(X32,k1_zfmisc_1(X31))|(~r2_hidden(X33,X32)|r2_hidden(X33,X31))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.12/0.39  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0))))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.39  cnf(c_0_22, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.39  cnf(c_0_23, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.39  cnf(c_0_24, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.39  cnf(c_0_25, plain, (X1=X2|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.39  cnf(c_0_26, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.39  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24])).
% 0.12/0.39  fof(c_0_28, plain, ![X34, X35, X36]:(((X36!=k1_funct_1(X34,X35)|r2_hidden(k4_tarski(X35,X36),X34)|~r2_hidden(X35,k1_relat_1(X34))|(~v1_relat_1(X34)|~v1_funct_1(X34)))&(~r2_hidden(k4_tarski(X35,X36),X34)|X36=k1_funct_1(X34,X35)|~r2_hidden(X35,k1_relat_1(X34))|(~v1_relat_1(X34)|~v1_funct_1(X34))))&((X36!=k1_funct_1(X34,X35)|X36=k1_xboole_0|r2_hidden(X35,k1_relat_1(X34))|(~v1_relat_1(X34)|~v1_funct_1(X34)))&(X36!=k1_xboole_0|X36=k1_funct_1(X34,X35)|r2_hidden(X35,k1_relat_1(X34))|(~v1_relat_1(X34)|~v1_funct_1(X34))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).
% 0.12/0.39  fof(c_0_29, plain, ![X39, X40, X41]:(~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))|v1_relat_1(X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.12/0.39  fof(c_0_30, plain, ![X37, X38]:(~r2_hidden(X37,X38)|~r1_tarski(X38,X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.12/0.39  fof(c_0_31, plain, ![X8]:r1_tarski(k1_xboole_0,X8), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.12/0.39  cnf(c_0_32, plain, (X1=X2|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,k2_enumset1(X2,X2,X2,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_22]), c_0_23]), c_0_24])).
% 0.12/0.39  cnf(c_0_33, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)))|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.12/0.39  cnf(c_0_34, plain, (r2_hidden(k4_tarski(X3,X1),X2)|X1!=k1_funct_1(X2,X3)|~r2_hidden(X3,k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.39  cnf(c_0_35, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.39  fof(c_0_36, plain, ![X42, X43, X44]:(~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))|k1_relset_1(X42,X43,X44)=k1_relat_1(X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.12/0.39  cnf(c_0_37, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.39  cnf(c_0_38, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.39  fof(c_0_39, plain, ![X15, X16, X17, X19, X20, X21, X22, X24]:((((r2_hidden(X17,esk1_3(X15,X16,X17))|~r2_hidden(X17,X16)|X16!=k3_tarski(X15))&(r2_hidden(esk1_3(X15,X16,X17),X15)|~r2_hidden(X17,X16)|X16!=k3_tarski(X15)))&(~r2_hidden(X19,X20)|~r2_hidden(X20,X15)|r2_hidden(X19,X16)|X16!=k3_tarski(X15)))&((~r2_hidden(esk2_2(X21,X22),X22)|(~r2_hidden(esk2_2(X21,X22),X24)|~r2_hidden(X24,X21))|X22=k3_tarski(X21))&((r2_hidden(esk2_2(X21,X22),esk3_2(X21,X22))|r2_hidden(esk2_2(X21,X22),X22)|X22=k3_tarski(X21))&(r2_hidden(esk3_2(X21,X22),X21)|r2_hidden(esk2_2(X21,X22),X22)|X22=k3_tarski(X21))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 0.12/0.39  cnf(c_0_40, negated_conjecture, (X1=esk6_0|~r2_hidden(k4_tarski(X2,X1),esk8_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.12/0.39  cnf(c_0_41, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_34])).
% 0.12/0.39  cnf(c_0_42, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.39  cnf(c_0_43, negated_conjecture, (v1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_35, c_0_27])).
% 0.12/0.39  cnf(c_0_44, plain, (X1=k1_funct_1(X2,X3)|r2_hidden(X3,k1_relat_1(X2))|X1!=k1_xboole_0|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.39  fof(c_0_45, plain, ![X30]:k3_tarski(k1_tarski(X30))=X30, inference(variable_rename,[status(thm)],[t31_zfmisc_1])).
% 0.12/0.39  fof(c_0_46, plain, ![X52, X53, X54]:((((~v1_funct_2(X54,X52,X53)|X52=k1_relset_1(X52,X53,X54)|X53=k1_xboole_0|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))))&(X52!=k1_relset_1(X52,X53,X54)|v1_funct_2(X54,X52,X53)|X53=k1_xboole_0|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))))&((~v1_funct_2(X54,X52,X53)|X52=k1_relset_1(X52,X53,X54)|X52!=k1_xboole_0|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))))&(X52!=k1_relset_1(X52,X53,X54)|v1_funct_2(X54,X52,X53)|X52!=k1_xboole_0|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))))))&((~v1_funct_2(X54,X52,X53)|X54=k1_xboole_0|X52=k1_xboole_0|X53!=k1_xboole_0|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))))&(X54!=k1_xboole_0|v1_funct_2(X54,X52,X53)|X52=k1_xboole_0|X53!=k1_xboole_0|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.12/0.39  cnf(c_0_47, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.12/0.39  cnf(c_0_48, negated_conjecture, (v1_funct_2(esk8_0,esk5_0,k1_tarski(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.39  cnf(c_0_49, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.12/0.39  cnf(c_0_50, plain, (r2_hidden(esk3_2(X1,X2),X1)|r2_hidden(esk2_2(X1,X2),X2)|X2=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.12/0.39  cnf(c_0_51, negated_conjecture, (k1_funct_1(esk8_0,X1)=esk6_0|~r2_hidden(X1,k1_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42]), c_0_43])])).
% 0.12/0.39  cnf(c_0_52, plain, (k1_funct_1(X1,X2)=k1_xboole_0|r2_hidden(X2,k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_44])).
% 0.12/0.39  cnf(c_0_53, plain, (k3_tarski(k1_tarski(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.12/0.39  cnf(c_0_54, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.12/0.39  cnf(c_0_55, negated_conjecture, (k1_relset_1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk8_0)=k1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_47, c_0_27])).
% 0.12/0.39  cnf(c_0_56, negated_conjecture, (v1_funct_2(esk8_0,esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_22]), c_0_23]), c_0_24])).
% 0.12/0.39  cnf(c_0_57, plain, (X1=k3_tarski(k1_xboole_0)|r2_hidden(esk2_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.12/0.39  cnf(c_0_58, negated_conjecture, (k1_funct_1(esk8_0,esk7_0)!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.39  cnf(c_0_59, negated_conjecture, (k1_funct_1(esk8_0,X1)=k1_xboole_0|k1_funct_1(esk8_0,X1)=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_42]), c_0_43])])).
% 0.12/0.39  cnf(c_0_60, plain, (k3_tarski(k2_enumset1(X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_22]), c_0_23]), c_0_24])).
% 0.12/0.39  cnf(c_0_61, negated_conjecture, (k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)=k1_xboole_0|k1_relat_1(esk8_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_27]), c_0_55]), c_0_56])])).
% 0.12/0.39  cnf(c_0_62, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_49, c_0_57])).
% 0.12/0.39  cnf(c_0_63, negated_conjecture, (k1_funct_1(esk8_0,esk7_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.12/0.39  cnf(c_0_64, negated_conjecture, (k1_relat_1(esk8_0)=esk5_0|esk6_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62])).
% 0.12/0.39  cnf(c_0_65, negated_conjecture, (esk6_0!=k1_xboole_0), inference(rw,[status(thm)],[c_0_58, c_0_63])).
% 0.12/0.39  cnf(c_0_66, negated_conjecture, (k1_relat_1(esk8_0)=esk5_0), inference(sr,[status(thm)],[c_0_64, c_0_65])).
% 0.12/0.39  cnf(c_0_67, negated_conjecture, (k1_funct_1(esk8_0,X1)=esk6_0|~r2_hidden(X1,esk5_0)), inference(rw,[status(thm)],[c_0_51, c_0_66])).
% 0.12/0.39  cnf(c_0_68, negated_conjecture, (r2_hidden(esk7_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.39  cnf(c_0_69, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_67]), c_0_68])]), c_0_65]), ['proof']).
% 0.12/0.39  # SZS output end CNFRefutation
% 0.12/0.39  # Proof object total steps             : 70
% 0.12/0.39  # Proof object clause steps            : 41
% 0.12/0.39  # Proof object formula steps           : 29
% 0.12/0.39  # Proof object conjectures             : 23
% 0.12/0.39  # Proof object clause conjectures      : 20
% 0.12/0.39  # Proof object formula conjectures     : 3
% 0.12/0.39  # Proof object initial clauses used    : 19
% 0.12/0.39  # Proof object initial formulas used   : 14
% 0.12/0.39  # Proof object generating inferences   : 13
% 0.12/0.39  # Proof object simplifying inferences  : 30
% 0.12/0.39  # Training examples: 0 positive, 0 negative
% 0.12/0.39  # Parsed axioms                        : 15
% 0.12/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.39  # Initial clauses                      : 35
% 0.12/0.39  # Removed in clause preprocessing      : 3
% 0.12/0.39  # Initial clauses in saturation        : 32
% 0.12/0.39  # Processed clauses                    : 254
% 0.12/0.39  # ...of these trivial                  : 0
% 0.12/0.39  # ...subsumed                          : 136
% 0.12/0.39  # ...remaining for further processing  : 118
% 0.12/0.39  # Other redundant clauses eliminated   : 12
% 0.12/0.39  # Clauses deleted for lack of memory   : 0
% 0.12/0.39  # Backward-subsumed                    : 7
% 0.12/0.39  # Backward-rewritten                   : 38
% 0.12/0.39  # Generated clauses                    : 466
% 0.12/0.39  # ...of the previous two non-trivial   : 448
% 0.12/0.39  # Contextual simplify-reflections      : 1
% 0.12/0.39  # Paramodulations                      : 452
% 0.12/0.39  # Factorizations                       : 1
% 0.12/0.39  # Equation resolutions                 : 12
% 0.12/0.39  # Propositional unsat checks           : 0
% 0.12/0.39  #    Propositional check models        : 0
% 0.12/0.39  #    Propositional check unsatisfiable : 0
% 0.12/0.39  #    Propositional clauses             : 0
% 0.12/0.39  #    Propositional clauses after purity: 0
% 0.12/0.39  #    Propositional unsat core size     : 0
% 0.12/0.39  #    Propositional preprocessing time  : 0.000
% 0.12/0.39  #    Propositional encoding time       : 0.000
% 0.12/0.39  #    Propositional solver time         : 0.000
% 0.12/0.39  #    Success case prop preproc time    : 0.000
% 0.12/0.39  #    Success case prop encoding time   : 0.000
% 0.12/0.39  #    Success case prop solver time     : 0.000
% 0.12/0.39  # Current number of processed clauses  : 60
% 0.12/0.39  #    Positive orientable unit clauses  : 10
% 0.12/0.39  #    Positive unorientable unit clauses: 0
% 0.12/0.39  #    Negative unit clauses             : 2
% 0.12/0.39  #    Non-unit-clauses                  : 48
% 0.12/0.39  # Current number of unprocessed clauses: 225
% 0.12/0.39  # ...number of literals in the above   : 936
% 0.12/0.39  # Current number of archived formulas  : 0
% 0.12/0.39  # Current number of archived clauses   : 50
% 0.12/0.39  # Clause-clause subsumption calls (NU) : 1064
% 0.12/0.39  # Rec. Clause-clause subsumption calls : 593
% 0.12/0.39  # Non-unit clause-clause subsumptions  : 115
% 0.12/0.39  # Unit Clause-clause subsumption calls : 40
% 0.12/0.39  # Rewrite failures with RHS unbound    : 0
% 0.12/0.39  # BW rewrite match attempts            : 3
% 0.12/0.39  # BW rewrite match successes           : 3
% 0.12/0.39  # Condensation attempts                : 0
% 0.12/0.39  # Condensation successes               : 0
% 0.12/0.39  # Termbank termtop insertions          : 8467
% 0.12/0.39  
% 0.12/0.39  # -------------------------------------------------
% 0.12/0.39  # User time                : 0.041 s
% 0.12/0.39  # System time              : 0.004 s
% 0.12/0.39  # Total time               : 0.045 s
% 0.12/0.39  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
