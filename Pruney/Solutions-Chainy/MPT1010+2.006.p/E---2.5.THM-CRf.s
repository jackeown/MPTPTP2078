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
% DateTime   : Thu Dec  3 11:05:12 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  103 (1207 expanded)
%              Number of clauses        :   71 ( 511 expanded)
%              Number of leaves         :   16 ( 322 expanded)
%              Depth                    :   20
%              Number of atoms          :  353 (3746 expanded)
%              Number of equality atoms :  126 (1576 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   32 (   2 average)
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

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

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

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(d5_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( X2 = k2_relat_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                  & X3 = k1_funct_1(X1,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,k1_tarski(X2))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
       => ( r2_hidden(X3,X1)
         => k1_funct_1(X4,X3) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t65_funct_2])).

fof(c_0_17,plain,(
    ! [X10,X11,X12,X13,X14,X15,X16,X17,X18,X19] :
      ( ( ~ r2_hidden(X14,X13)
        | X14 = X10
        | X14 = X11
        | X14 = X12
        | X13 != k1_enumset1(X10,X11,X12) )
      & ( X15 != X10
        | r2_hidden(X15,X13)
        | X13 != k1_enumset1(X10,X11,X12) )
      & ( X15 != X11
        | r2_hidden(X15,X13)
        | X13 != k1_enumset1(X10,X11,X12) )
      & ( X15 != X12
        | r2_hidden(X15,X13)
        | X13 != k1_enumset1(X10,X11,X12) )
      & ( esk2_4(X16,X17,X18,X19) != X16
        | ~ r2_hidden(esk2_4(X16,X17,X18,X19),X19)
        | X19 = k1_enumset1(X16,X17,X18) )
      & ( esk2_4(X16,X17,X18,X19) != X17
        | ~ r2_hidden(esk2_4(X16,X17,X18,X19),X19)
        | X19 = k1_enumset1(X16,X17,X18) )
      & ( esk2_4(X16,X17,X18,X19) != X18
        | ~ r2_hidden(esk2_4(X16,X17,X18,X19),X19)
        | X19 = k1_enumset1(X16,X17,X18) )
      & ( r2_hidden(esk2_4(X16,X17,X18,X19),X19)
        | esk2_4(X16,X17,X18,X19) = X16
        | esk2_4(X16,X17,X18,X19) = X17
        | esk2_4(X16,X17,X18,X19) = X18
        | X19 = k1_enumset1(X16,X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_18,plain,(
    ! [X24,X25,X26] : k2_enumset1(X24,X24,X25,X26) = k1_enumset1(X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_19,negated_conjecture,
    ( v1_funct_1(esk9_0)
    & v1_funct_2(esk9_0,esk6_0,k1_tarski(esk7_0))
    & m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_tarski(esk7_0))))
    & r2_hidden(esk8_0,esk6_0)
    & k1_funct_1(esk9_0,esk8_0) != esk7_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_20,plain,(
    ! [X21] : k2_tarski(X21,X21) = k1_tarski(X21) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_21,plain,(
    ! [X22,X23] : k1_enumset1(X22,X22,X23) = k2_tarski(X22,X23) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X55,X56,X57] :
      ( ( ~ v1_funct_2(X57,X55,X56)
        | X55 = k1_relset_1(X55,X56,X57)
        | X56 = k1_xboole_0
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))) )
      & ( X55 != k1_relset_1(X55,X56,X57)
        | v1_funct_2(X57,X55,X56)
        | X56 = k1_xboole_0
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))) )
      & ( ~ v1_funct_2(X57,X55,X56)
        | X55 = k1_relset_1(X55,X56,X57)
        | X55 != k1_xboole_0
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))) )
      & ( X55 != k1_relset_1(X55,X56,X57)
        | v1_funct_2(X57,X55,X56)
        | X55 != k1_xboole_0
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))) )
      & ( ~ v1_funct_2(X57,X55,X56)
        | X57 = k1_xboole_0
        | X55 = k1_xboole_0
        | X56 != k1_xboole_0
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))) )
      & ( X57 != k1_xboole_0
        | v1_funct_2(X57,X55,X56)
        | X55 = k1_xboole_0
        | X56 != k1_xboole_0
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_tarski(esk7_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_2(esk9_0,esk6_0,k1_tarski(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_29,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_31,plain,(
    ! [X52,X53,X54] :
      ( ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))
      | k1_relset_1(X52,X53,X54) = k1_relat_1(X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_32,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_2(esk9_0,esk6_0,k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_26]),c_0_27]),c_0_23])).

fof(c_0_35,plain,(
    ! [X46,X47,X48] :
      ( ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))
      | v1_relat_1(X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_36,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_30])])).

cnf(c_0_38,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( k1_relset_1(esk6_0,k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),esk9_0) = esk6_0
    | k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

fof(c_0_40,plain,(
    ! [X29,X30] :
      ( ( ~ m1_subset_1(X29,k1_zfmisc_1(X30))
        | r1_tarski(X29,X30) )
      & ( ~ r1_tarski(X29,X30)
        | m1_subset_1(X29,k1_zfmisc_1(X30)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_41,plain,(
    ! [X34,X35] :
      ( ( ~ v5_relat_1(X35,X34)
        | r1_tarski(k2_relat_1(X35),X34)
        | ~ v1_relat_1(X35) )
      & ( ~ r1_tarski(k2_relat_1(X35),X34)
        | v5_relat_1(X35,X34)
        | ~ v1_relat_1(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

fof(c_0_42,plain,(
    ! [X36,X37,X38,X40,X41,X42,X44] :
      ( ( r2_hidden(esk3_3(X36,X37,X38),k1_relat_1(X36))
        | ~ r2_hidden(X38,X37)
        | X37 != k2_relat_1(X36)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) )
      & ( X38 = k1_funct_1(X36,esk3_3(X36,X37,X38))
        | ~ r2_hidden(X38,X37)
        | X37 != k2_relat_1(X36)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) )
      & ( ~ r2_hidden(X41,k1_relat_1(X36))
        | X40 != k1_funct_1(X36,X41)
        | r2_hidden(X40,X37)
        | X37 != k2_relat_1(X36)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) )
      & ( ~ r2_hidden(esk4_2(X36,X42),X42)
        | ~ r2_hidden(X44,k1_relat_1(X36))
        | esk4_2(X36,X42) != k1_funct_1(X36,X44)
        | X42 = k2_relat_1(X36)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) )
      & ( r2_hidden(esk5_2(X36,X42),k1_relat_1(X36))
        | r2_hidden(esk4_2(X36,X42),X42)
        | X42 = k2_relat_1(X36)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) )
      & ( esk4_2(X36,X42) = k1_funct_1(X36,esk5_2(X36,X42))
        | r2_hidden(esk4_2(X36,X42),X42)
        | X42 = k2_relat_1(X36)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

cnf(c_0_43,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( ~ v1_xboole_0(k2_enumset1(X1,X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0) = k1_xboole_0
    | k1_relat_1(esk9_0) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_33])])).

cnf(c_0_46,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_47,plain,(
    ! [X31,X32,X33] :
      ( ~ r2_hidden(X31,X32)
      | ~ m1_subset_1(X32,k1_zfmisc_1(X33))
      | m1_subset_1(X31,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_48,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_50,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_51,plain,
    ( esk4_2(X1,X2) = k1_funct_1(X1,esk5_2(X1,X2))
    | r2_hidden(esk4_2(X1,X2),X2)
    | X2 = k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_53,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_33])).

cnf(c_0_54,plain,
    ( r2_hidden(esk5_2(X1,X2),k1_relat_1(X1))
    | r2_hidden(esk4_2(X1,X2),X2)
    | X2 = k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_55,negated_conjecture,
    ( k1_relat_1(esk9_0) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])])).

cnf(c_0_56,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_57,plain,
    ( m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2))
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_58,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_50])])).

cnf(c_0_59,negated_conjecture,
    ( k1_funct_1(esk9_0,esk5_2(esk9_0,X1)) = esk4_2(esk9_0,X1)
    | X1 = k2_relat_1(esk9_0)
    | r2_hidden(esk4_2(esk9_0,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])])).

cnf(c_0_60,negated_conjecture,
    ( X1 = k2_relat_1(esk9_0)
    | r2_hidden(esk5_2(esk9_0,X1),esk6_0)
    | r2_hidden(esk4_2(esk9_0,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_52]),c_0_55]),c_0_53])])).

fof(c_0_61,plain,(
    ! [X49,X50,X51] :
      ( ( v4_relat_1(X51,X49)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))) )
      & ( v5_relat_1(X51,X50)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_62,plain,
    ( m1_subset_1(X1,X2)
    | ~ v5_relat_1(X3,X2)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k2_relat_1(X3)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( X1 = k2_relat_1(esk9_0)
    | r2_hidden(esk4_2(esk9_0,X1),k2_relat_1(esk9_0))
    | r2_hidden(esk4_2(esk9_0,X1),X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_52]),c_0_53]),c_0_55])]),c_0_60])).

cnf(c_0_64,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_65,plain,
    ( ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_xboole_0(k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_58])).

cnf(c_0_66,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk8_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_68,plain,(
    ! [X27,X28] :
      ( ~ m1_subset_1(X27,X28)
      | v1_xboole_0(X28)
      | r2_hidden(X27,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_69,negated_conjecture,
    ( X1 = k2_relat_1(esk9_0)
    | m1_subset_1(esk4_2(esk9_0,X1),X2)
    | r2_hidden(esk4_2(esk9_0,X1),X1)
    | ~ v5_relat_1(esk9_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_53])])).

cnf(c_0_70,negated_conjecture,
    ( v5_relat_1(esk9_0,k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_33])).

cnf(c_0_71,plain,
    ( v1_xboole_0(k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_67])).

cnf(c_0_73,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_74,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_75,negated_conjecture,
    ( X1 = k2_relat_1(esk9_0)
    | m1_subset_1(esk4_2(esk9_0,X1),k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0))
    | r2_hidden(esk4_2(esk9_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_76,plain,
    ( m1_subset_1(esk1_1(k2_relat_1(X1)),X2)
    | v1_xboole_0(k2_relat_1(X1))
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_66])).

cnf(c_0_77,negated_conjecture,
    ( ~ v1_xboole_0(k2_relat_1(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_55]),c_0_52]),c_0_53])]),c_0_72])).

cnf(c_0_78,plain,
    ( X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k2_enumset1(X3,X3,X4,X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_73,c_0_23])).

cnf(c_0_79,negated_conjecture,
    ( X1 = k2_relat_1(esk9_0)
    | r2_hidden(esk4_2(esk9_0,X1),k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0))
    | r2_hidden(esk4_2(esk9_0,X1),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_44])).

cnf(c_0_80,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_81,negated_conjecture,
    ( m1_subset_1(esk1_1(k2_relat_1(esk9_0)),k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_70]),c_0_53])]),c_0_77])).

cnf(c_0_82,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k2_enumset1(X4,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_78])).

cnf(c_0_83,negated_conjecture,
    ( k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0) = k2_relat_1(esk9_0)
    | r2_hidden(esk4_2(esk9_0,k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)),k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)) ),
    inference(ef,[status(thm)],[c_0_79])).

cnf(c_0_84,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X4,X5) ),
    inference(rw,[status(thm)],[c_0_80,c_0_23])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(esk1_1(k2_relat_1(esk9_0)),k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_81]),c_0_44])).

cnf(c_0_86,plain,
    ( X2 = k2_relat_1(X1)
    | ~ r2_hidden(esk4_2(X1,X2),X2)
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | esk4_2(X1,X2) != k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_87,negated_conjecture,
    ( esk4_2(esk9_0,k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)) = esk7_0
    | k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0) = k2_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_88,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_84])])).

cnf(c_0_89,plain,
    ( X1 = k1_funct_1(X2,esk3_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_90,negated_conjecture,
    ( esk1_1(k2_relat_1(esk9_0)) = esk7_0 ),
    inference(spm,[status(thm)],[c_0_82,c_0_85])).

cnf(c_0_91,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_92,negated_conjecture,
    ( k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0) = k2_relat_1(esk9_0)
    | k1_funct_1(esk9_0,X1) != esk7_0
    | ~ r2_hidden(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_52]),c_0_53]),c_0_88]),c_0_55])])).

cnf(c_0_93,plain,
    ( k1_funct_1(X1,esk3_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_89])).

cnf(c_0_94,negated_conjecture,
    ( r2_hidden(esk7_0,k2_relat_1(esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_90]),c_0_77])).

cnf(c_0_95,plain,
    ( r2_hidden(esk3_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_91])).

cnf(c_0_96,negated_conjecture,
    ( k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0) = k2_relat_1(esk9_0)
    | ~ r2_hidden(esk3_3(esk9_0,k2_relat_1(esk9_0),esk7_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_52]),c_0_53])])]),c_0_94])])).

cnf(c_0_97,negated_conjecture,
    ( r2_hidden(esk3_3(esk9_0,k2_relat_1(esk9_0),X1),esk6_0)
    | ~ r2_hidden(X1,k2_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_55]),c_0_52]),c_0_53])])).

cnf(c_0_98,negated_conjecture,
    ( k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0) = k2_relat_1(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_94])])).

cnf(c_0_99,negated_conjecture,
    ( X1 = esk7_0
    | ~ r2_hidden(X1,k2_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_98])).

cnf(c_0_100,negated_conjecture,
    ( k1_funct_1(esk9_0,esk8_0) != esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_101,negated_conjecture,
    ( k1_funct_1(esk9_0,X1) = esk7_0
    | ~ r2_hidden(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_58]),c_0_52]),c_0_53]),c_0_55])])).

cnf(c_0_102,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_67])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:13:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.48  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.48  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.48  #
% 0.19/0.48  # Preprocessing time       : 0.029 s
% 0.19/0.48  # Presaturation interreduction done
% 0.19/0.48  
% 0.19/0.48  # Proof found!
% 0.19/0.48  # SZS status Theorem
% 0.19/0.48  # SZS output start CNFRefutation
% 0.19/0.48  fof(t65_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>(r2_hidden(X3,X1)=>k1_funct_1(X4,X3)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 0.19/0.48  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 0.19/0.48  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.48  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.48  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.48  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.19/0.48  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.48  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.19/0.48  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.48  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.48  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 0.19/0.48  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 0.19/0.48  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.48  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.19/0.48  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.48  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.19/0.48  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>(r2_hidden(X3,X1)=>k1_funct_1(X4,X3)=X2))), inference(assume_negation,[status(cth)],[t65_funct_2])).
% 0.19/0.48  fof(c_0_17, plain, ![X10, X11, X12, X13, X14, X15, X16, X17, X18, X19]:(((~r2_hidden(X14,X13)|(X14=X10|X14=X11|X14=X12)|X13!=k1_enumset1(X10,X11,X12))&(((X15!=X10|r2_hidden(X15,X13)|X13!=k1_enumset1(X10,X11,X12))&(X15!=X11|r2_hidden(X15,X13)|X13!=k1_enumset1(X10,X11,X12)))&(X15!=X12|r2_hidden(X15,X13)|X13!=k1_enumset1(X10,X11,X12))))&((((esk2_4(X16,X17,X18,X19)!=X16|~r2_hidden(esk2_4(X16,X17,X18,X19),X19)|X19=k1_enumset1(X16,X17,X18))&(esk2_4(X16,X17,X18,X19)!=X17|~r2_hidden(esk2_4(X16,X17,X18,X19),X19)|X19=k1_enumset1(X16,X17,X18)))&(esk2_4(X16,X17,X18,X19)!=X18|~r2_hidden(esk2_4(X16,X17,X18,X19),X19)|X19=k1_enumset1(X16,X17,X18)))&(r2_hidden(esk2_4(X16,X17,X18,X19),X19)|(esk2_4(X16,X17,X18,X19)=X16|esk2_4(X16,X17,X18,X19)=X17|esk2_4(X16,X17,X18,X19)=X18)|X19=k1_enumset1(X16,X17,X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.19/0.48  fof(c_0_18, plain, ![X24, X25, X26]:k2_enumset1(X24,X24,X25,X26)=k1_enumset1(X24,X25,X26), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.48  fof(c_0_19, negated_conjecture, (((v1_funct_1(esk9_0)&v1_funct_2(esk9_0,esk6_0,k1_tarski(esk7_0)))&m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_tarski(esk7_0)))))&(r2_hidden(esk8_0,esk6_0)&k1_funct_1(esk9_0,esk8_0)!=esk7_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.19/0.48  fof(c_0_20, plain, ![X21]:k2_tarski(X21,X21)=k1_tarski(X21), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.48  fof(c_0_21, plain, ![X22, X23]:k1_enumset1(X22,X22,X23)=k2_tarski(X22,X23), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.48  cnf(c_0_22, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.48  cnf(c_0_23, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.48  fof(c_0_24, plain, ![X55, X56, X57]:((((~v1_funct_2(X57,X55,X56)|X55=k1_relset_1(X55,X56,X57)|X56=k1_xboole_0|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))))&(X55!=k1_relset_1(X55,X56,X57)|v1_funct_2(X57,X55,X56)|X56=k1_xboole_0|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56)))))&((~v1_funct_2(X57,X55,X56)|X55=k1_relset_1(X55,X56,X57)|X55!=k1_xboole_0|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))))&(X55!=k1_relset_1(X55,X56,X57)|v1_funct_2(X57,X55,X56)|X55!=k1_xboole_0|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))))))&((~v1_funct_2(X57,X55,X56)|X57=k1_xboole_0|X55=k1_xboole_0|X56!=k1_xboole_0|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))))&(X57!=k1_xboole_0|v1_funct_2(X57,X55,X56)|X55=k1_xboole_0|X56!=k1_xboole_0|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.19/0.48  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_tarski(esk7_0))))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.48  cnf(c_0_26, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.48  cnf(c_0_27, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.48  cnf(c_0_28, negated_conjecture, (v1_funct_2(esk9_0,esk6_0,k1_tarski(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.48  fof(c_0_29, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.48  cnf(c_0_30, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X4,X5,X2)), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.48  fof(c_0_31, plain, ![X52, X53, X54]:(~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))|k1_relset_1(X52,X53,X54)=k1_relat_1(X54)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.19/0.48  cnf(c_0_32, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.48  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_23])).
% 0.19/0.48  cnf(c_0_34, negated_conjecture, (v1_funct_2(esk9_0,esk6_0,k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_26]), c_0_27]), c_0_23])).
% 0.19/0.48  fof(c_0_35, plain, ![X46, X47, X48]:(~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))|v1_relat_1(X48)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.48  cnf(c_0_36, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.48  cnf(c_0_37, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_30])])).
% 0.19/0.48  cnf(c_0_38, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.48  cnf(c_0_39, negated_conjecture, (k1_relset_1(esk6_0,k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),esk9_0)=esk6_0|k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])])).
% 0.19/0.48  fof(c_0_40, plain, ![X29, X30]:((~m1_subset_1(X29,k1_zfmisc_1(X30))|r1_tarski(X29,X30))&(~r1_tarski(X29,X30)|m1_subset_1(X29,k1_zfmisc_1(X30)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.48  fof(c_0_41, plain, ![X34, X35]:((~v5_relat_1(X35,X34)|r1_tarski(k2_relat_1(X35),X34)|~v1_relat_1(X35))&(~r1_tarski(k2_relat_1(X35),X34)|v5_relat_1(X35,X34)|~v1_relat_1(X35))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.19/0.48  fof(c_0_42, plain, ![X36, X37, X38, X40, X41, X42, X44]:((((r2_hidden(esk3_3(X36,X37,X38),k1_relat_1(X36))|~r2_hidden(X38,X37)|X37!=k2_relat_1(X36)|(~v1_relat_1(X36)|~v1_funct_1(X36)))&(X38=k1_funct_1(X36,esk3_3(X36,X37,X38))|~r2_hidden(X38,X37)|X37!=k2_relat_1(X36)|(~v1_relat_1(X36)|~v1_funct_1(X36))))&(~r2_hidden(X41,k1_relat_1(X36))|X40!=k1_funct_1(X36,X41)|r2_hidden(X40,X37)|X37!=k2_relat_1(X36)|(~v1_relat_1(X36)|~v1_funct_1(X36))))&((~r2_hidden(esk4_2(X36,X42),X42)|(~r2_hidden(X44,k1_relat_1(X36))|esk4_2(X36,X42)!=k1_funct_1(X36,X44))|X42=k2_relat_1(X36)|(~v1_relat_1(X36)|~v1_funct_1(X36)))&((r2_hidden(esk5_2(X36,X42),k1_relat_1(X36))|r2_hidden(esk4_2(X36,X42),X42)|X42=k2_relat_1(X36)|(~v1_relat_1(X36)|~v1_funct_1(X36)))&(esk4_2(X36,X42)=k1_funct_1(X36,esk5_2(X36,X42))|r2_hidden(esk4_2(X36,X42),X42)|X42=k2_relat_1(X36)|(~v1_relat_1(X36)|~v1_funct_1(X36)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.19/0.48  cnf(c_0_43, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.48  cnf(c_0_44, plain, (~v1_xboole_0(k2_enumset1(X1,X1,X2,X3))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.48  cnf(c_0_45, negated_conjecture, (k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)=k1_xboole_0|k1_relat_1(esk9_0)=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_33])])).
% 0.19/0.48  cnf(c_0_46, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.48  fof(c_0_47, plain, ![X31, X32, X33]:(~r2_hidden(X31,X32)|~m1_subset_1(X32,k1_zfmisc_1(X33))|m1_subset_1(X31,X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.19/0.48  cnf(c_0_48, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.48  cnf(c_0_49, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.48  cnf(c_0_50, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.48  cnf(c_0_51, plain, (esk4_2(X1,X2)=k1_funct_1(X1,esk5_2(X1,X2))|r2_hidden(esk4_2(X1,X2),X2)|X2=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.48  cnf(c_0_52, negated_conjecture, (v1_funct_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.48  cnf(c_0_53, negated_conjecture, (v1_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_43, c_0_33])).
% 0.19/0.48  cnf(c_0_54, plain, (r2_hidden(esk5_2(X1,X2),k1_relat_1(X1))|r2_hidden(esk4_2(X1,X2),X2)|X2=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.48  cnf(c_0_55, negated_conjecture, (k1_relat_1(esk9_0)=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])])).
% 0.19/0.48  cnf(c_0_56, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.48  cnf(c_0_57, plain, (m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2))|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.48  cnf(c_0_58, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_50])])).
% 0.19/0.48  cnf(c_0_59, negated_conjecture, (k1_funct_1(esk9_0,esk5_2(esk9_0,X1))=esk4_2(esk9_0,X1)|X1=k2_relat_1(esk9_0)|r2_hidden(esk4_2(esk9_0,X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])])).
% 0.19/0.48  cnf(c_0_60, negated_conjecture, (X1=k2_relat_1(esk9_0)|r2_hidden(esk5_2(esk9_0,X1),esk6_0)|r2_hidden(esk4_2(esk9_0,X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_52]), c_0_55]), c_0_53])])).
% 0.19/0.48  fof(c_0_61, plain, ![X49, X50, X51]:((v4_relat_1(X51,X49)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))))&(v5_relat_1(X51,X50)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.48  cnf(c_0_62, plain, (m1_subset_1(X1,X2)|~v5_relat_1(X3,X2)|~v1_relat_1(X3)|~r2_hidden(X1,k2_relat_1(X3))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.48  cnf(c_0_63, negated_conjecture, (X1=k2_relat_1(esk9_0)|r2_hidden(esk4_2(esk9_0,X1),k2_relat_1(esk9_0))|r2_hidden(esk4_2(esk9_0,X1),X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_52]), c_0_53]), c_0_55])]), c_0_60])).
% 0.19/0.48  cnf(c_0_64, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.48  cnf(c_0_65, plain, (~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~v1_xboole_0(k2_relat_1(X1))), inference(spm,[status(thm)],[c_0_36, c_0_58])).
% 0.19/0.48  cnf(c_0_66, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.48  cnf(c_0_67, negated_conjecture, (r2_hidden(esk8_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.48  fof(c_0_68, plain, ![X27, X28]:(~m1_subset_1(X27,X28)|(v1_xboole_0(X28)|r2_hidden(X27,X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.19/0.48  cnf(c_0_69, negated_conjecture, (X1=k2_relat_1(esk9_0)|m1_subset_1(esk4_2(esk9_0,X1),X2)|r2_hidden(esk4_2(esk9_0,X1),X1)|~v5_relat_1(esk9_0,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_53])])).
% 0.19/0.48  cnf(c_0_70, negated_conjecture, (v5_relat_1(esk9_0,k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0))), inference(spm,[status(thm)],[c_0_64, c_0_33])).
% 0.19/0.48  cnf(c_0_71, plain, (v1_xboole_0(k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~v1_xboole_0(k2_relat_1(X1))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.19/0.48  cnf(c_0_72, negated_conjecture, (~v1_xboole_0(esk6_0)), inference(spm,[status(thm)],[c_0_36, c_0_67])).
% 0.19/0.48  cnf(c_0_73, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.48  cnf(c_0_74, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.19/0.48  cnf(c_0_75, negated_conjecture, (X1=k2_relat_1(esk9_0)|m1_subset_1(esk4_2(esk9_0,X1),k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0))|r2_hidden(esk4_2(esk9_0,X1),X1)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.19/0.48  cnf(c_0_76, plain, (m1_subset_1(esk1_1(k2_relat_1(X1)),X2)|v1_xboole_0(k2_relat_1(X1))|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_62, c_0_66])).
% 0.19/0.48  cnf(c_0_77, negated_conjecture, (~v1_xboole_0(k2_relat_1(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_55]), c_0_52]), c_0_53])]), c_0_72])).
% 0.19/0.48  cnf(c_0_78, plain, (X1=X5|X1=X4|X1=X3|X2!=k2_enumset1(X3,X3,X4,X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_73, c_0_23])).
% 0.19/0.48  cnf(c_0_79, negated_conjecture, (X1=k2_relat_1(esk9_0)|r2_hidden(esk4_2(esk9_0,X1),k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0))|r2_hidden(esk4_2(esk9_0,X1),X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_44])).
% 0.19/0.48  cnf(c_0_80, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.48  cnf(c_0_81, negated_conjecture, (m1_subset_1(esk1_1(k2_relat_1(esk9_0)),k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_70]), c_0_53])]), c_0_77])).
% 0.19/0.48  cnf(c_0_82, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k2_enumset1(X4,X4,X3,X2))), inference(er,[status(thm)],[c_0_78])).
% 0.19/0.48  cnf(c_0_83, negated_conjecture, (k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)=k2_relat_1(esk9_0)|r2_hidden(esk4_2(esk9_0,k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)),k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0))), inference(ef,[status(thm)],[c_0_79])).
% 0.19/0.48  cnf(c_0_84, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X4,X5)), inference(rw,[status(thm)],[c_0_80, c_0_23])).
% 0.19/0.48  cnf(c_0_85, negated_conjecture, (r2_hidden(esk1_1(k2_relat_1(esk9_0)),k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_81]), c_0_44])).
% 0.19/0.48  cnf(c_0_86, plain, (X2=k2_relat_1(X1)|~r2_hidden(esk4_2(X1,X2),X2)|~r2_hidden(X3,k1_relat_1(X1))|esk4_2(X1,X2)!=k1_funct_1(X1,X3)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.48  cnf(c_0_87, negated_conjecture, (esk4_2(esk9_0,k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0))=esk7_0|k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)=k2_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.19/0.48  cnf(c_0_88, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_84])])).
% 0.19/0.48  cnf(c_0_89, plain, (X1=k1_funct_1(X2,esk3_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.48  cnf(c_0_90, negated_conjecture, (esk1_1(k2_relat_1(esk9_0))=esk7_0), inference(spm,[status(thm)],[c_0_82, c_0_85])).
% 0.19/0.48  cnf(c_0_91, plain, (r2_hidden(esk3_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.48  cnf(c_0_92, negated_conjecture, (k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)=k2_relat_1(esk9_0)|k1_funct_1(esk9_0,X1)!=esk7_0|~r2_hidden(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_52]), c_0_53]), c_0_88]), c_0_55])])).
% 0.19/0.48  cnf(c_0_93, plain, (k1_funct_1(X1,esk3_3(X1,k2_relat_1(X1),X2))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_89])).
% 0.19/0.48  cnf(c_0_94, negated_conjecture, (r2_hidden(esk7_0,k2_relat_1(esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_90]), c_0_77])).
% 0.19/0.48  cnf(c_0_95, plain, (r2_hidden(esk3_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_91])).
% 0.19/0.48  cnf(c_0_96, negated_conjecture, (k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)=k2_relat_1(esk9_0)|~r2_hidden(esk3_3(esk9_0,k2_relat_1(esk9_0),esk7_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_52]), c_0_53])])]), c_0_94])])).
% 0.19/0.48  cnf(c_0_97, negated_conjecture, (r2_hidden(esk3_3(esk9_0,k2_relat_1(esk9_0),X1),esk6_0)|~r2_hidden(X1,k2_relat_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_55]), c_0_52]), c_0_53])])).
% 0.19/0.48  cnf(c_0_98, negated_conjecture, (k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)=k2_relat_1(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_94])])).
% 0.19/0.48  cnf(c_0_99, negated_conjecture, (X1=esk7_0|~r2_hidden(X1,k2_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_82, c_0_98])).
% 0.19/0.48  cnf(c_0_100, negated_conjecture, (k1_funct_1(esk9_0,esk8_0)!=esk7_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.48  cnf(c_0_101, negated_conjecture, (k1_funct_1(esk9_0,X1)=esk7_0|~r2_hidden(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_58]), c_0_52]), c_0_53]), c_0_55])])).
% 0.19/0.48  cnf(c_0_102, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_67])]), ['proof']).
% 0.19/0.48  # SZS output end CNFRefutation
% 0.19/0.48  # Proof object total steps             : 103
% 0.19/0.48  # Proof object clause steps            : 71
% 0.19/0.48  # Proof object formula steps           : 32
% 0.19/0.48  # Proof object conjectures             : 36
% 0.19/0.48  # Proof object clause conjectures      : 33
% 0.19/0.48  # Proof object formula conjectures     : 3
% 0.19/0.48  # Proof object initial clauses used    : 28
% 0.19/0.48  # Proof object initial formulas used   : 16
% 0.19/0.48  # Proof object generating inferences   : 32
% 0.19/0.48  # Proof object simplifying inferences  : 68
% 0.19/0.48  # Training examples: 0 positive, 0 negative
% 0.19/0.48  # Parsed axioms                        : 16
% 0.19/0.48  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.48  # Initial clauses                      : 41
% 0.19/0.48  # Removed in clause preprocessing      : 3
% 0.19/0.48  # Initial clauses in saturation        : 38
% 0.19/0.48  # Processed clauses                    : 499
% 0.19/0.48  # ...of these trivial                  : 1
% 0.19/0.48  # ...subsumed                          : 183
% 0.19/0.48  # ...remaining for further processing  : 315
% 0.19/0.48  # Other redundant clauses eliminated   : 263
% 0.19/0.48  # Clauses deleted for lack of memory   : 0
% 0.19/0.48  # Backward-subsumed                    : 3
% 0.19/0.48  # Backward-rewritten                   : 77
% 0.19/0.48  # Generated clauses                    : 3592
% 0.19/0.48  # ...of the previous two non-trivial   : 3172
% 0.19/0.48  # Contextual simplify-reflections      : 5
% 0.19/0.48  # Paramodulations                      : 3278
% 0.19/0.48  # Factorizations                       : 54
% 0.19/0.48  # Equation resolutions                 : 265
% 0.19/0.48  # Propositional unsat checks           : 0
% 0.19/0.48  #    Propositional check models        : 0
% 0.19/0.48  #    Propositional check unsatisfiable : 0
% 0.19/0.48  #    Propositional clauses             : 0
% 0.19/0.48  #    Propositional clauses after purity: 0
% 0.19/0.48  #    Propositional unsat core size     : 0
% 0.19/0.48  #    Propositional preprocessing time  : 0.000
% 0.19/0.48  #    Propositional encoding time       : 0.000
% 0.19/0.48  #    Propositional solver time         : 0.000
% 0.19/0.48  #    Success case prop preproc time    : 0.000
% 0.19/0.48  #    Success case prop encoding time   : 0.000
% 0.19/0.48  #    Success case prop solver time     : 0.000
% 0.19/0.48  # Current number of processed clauses  : 186
% 0.19/0.48  #    Positive orientable unit clauses  : 16
% 0.19/0.48  #    Positive unorientable unit clauses: 0
% 0.19/0.48  #    Negative unit clauses             : 5
% 0.19/0.48  #    Non-unit-clauses                  : 165
% 0.19/0.48  # Current number of unprocessed clauses: 2735
% 0.19/0.48  # ...number of literals in the above   : 20754
% 0.19/0.48  # Current number of archived formulas  : 0
% 0.19/0.48  # Current number of archived clauses   : 121
% 0.19/0.48  # Clause-clause subsumption calls (NU) : 7395
% 0.19/0.48  # Rec. Clause-clause subsumption calls : 1687
% 0.19/0.48  # Non-unit clause-clause subsumptions  : 118
% 0.19/0.48  # Unit Clause-clause subsumption calls : 219
% 0.19/0.48  # Rewrite failures with RHS unbound    : 0
% 0.19/0.48  # BW rewrite match attempts            : 20
% 0.19/0.48  # BW rewrite match successes           : 3
% 0.19/0.48  # Condensation attempts                : 0
% 0.19/0.48  # Condensation successes               : 0
% 0.19/0.48  # Termbank termtop insertions          : 82999
% 0.19/0.48  
% 0.19/0.48  # -------------------------------------------------
% 0.19/0.48  # User time                : 0.139 s
% 0.19/0.48  # System time              : 0.004 s
% 0.19/0.48  # Total time               : 0.143 s
% 0.19/0.48  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
