%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:04:27 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 177 expanded)
%              Number of clauses        :   39 (  71 expanded)
%              Number of leaves         :   17 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :  204 ( 422 expanded)
%              Number of equality atoms :   57 ( 148 expanded)
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

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(t12_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))
     => ( k1_mcart_1(X1) = X2
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(t7_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_hidden(X3,X1)
       => ( X2 = k1_xboole_0
          | r2_hidden(k1_funct_1(X4,X3),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

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

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

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

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
       => ( X2 != k1_xboole_0
         => r2_hidden(k1_funct_1(X3,X1),X2) ) ) ),
    inference(assume_negation,[status(cth)],[t61_funct_2])).

fof(c_0_18,negated_conjecture,
    ( v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,k1_tarski(esk5_0),esk6_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk5_0),esk6_0)))
    & esk6_0 != k1_xboole_0
    & ~ r2_hidden(k1_funct_1(esk7_0,esk5_0),esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_19,plain,(
    ! [X9] : k2_tarski(X9,X9) = k1_tarski(X9) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_20,plain,(
    ! [X10,X11] : k1_enumset1(X10,X10,X11) = k2_tarski(X10,X11) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_21,plain,(
    ! [X12,X13,X14] : k2_enumset1(X12,X12,X13,X14) = k1_enumset1(X12,X13,X14) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_22,plain,(
    ! [X18,X19,X20] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(X18))
      | ~ r2_hidden(X20,X19)
      | r2_hidden(X20,X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk5_0),esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_27,plain,(
    ! [X39,X40,X41] :
      ( ( k1_mcart_1(X39) = X40
        | ~ r2_hidden(X39,k2_zfmisc_1(k1_tarski(X40),X41)) )
      & ( r2_hidden(k2_mcart_1(X39),X41)
        | ~ r2_hidden(X39,k2_zfmisc_1(k1_tarski(X40),X41)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_mcart_1])])])).

fof(c_0_28,plain,(
    ! [X36,X37,X38] :
      ( ( r2_hidden(k1_mcart_1(X36),X37)
        | ~ r2_hidden(X36,k2_zfmisc_1(X37,X38)) )
      & ( r2_hidden(k2_mcart_1(X36),X38)
        | ~ r2_hidden(X36,k2_zfmisc_1(X37,X38)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_29,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_31,plain,
    ( k1_mcart_1(X1) = X2
    | ~ r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,plain,
    ( k1_mcart_1(X1) = X2
    | ~ r2_hidden(X1,k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_24]),c_0_25]),c_0_26])).

fof(c_0_35,plain,(
    ! [X52,X53,X54,X55] :
      ( ~ v1_funct_1(X55)
      | ~ v1_funct_2(X55,X52,X53)
      | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))
      | ~ r2_hidden(X54,X52)
      | X53 = k1_xboole_0
      | r2_hidden(k1_funct_1(X55,X54),X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_2(esk7_0,k1_tarski(esk5_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(k1_mcart_1(X1),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( k1_mcart_1(X1) = esk5_0
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_33])).

fof(c_0_39,plain,(
    ! [X42,X44,X45,X46,X47,X48] :
      ( ( r2_hidden(esk4_1(X42),X42)
        | X42 = k1_xboole_0 )
      & ( ~ r2_hidden(X44,X45)
        | ~ r2_hidden(X45,X46)
        | ~ r2_hidden(X46,X47)
        | ~ r2_hidden(X47,X48)
        | ~ r2_hidden(X48,esk4_1(X42))
        | r1_xboole_0(X44,X42)
        | X42 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_mcart_1])])])])])])).

fof(c_0_40,plain,(
    ! [X27,X28] :
      ( ~ r2_hidden(X27,X28)
      | ~ r1_tarski(X28,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_41,plain,(
    ! [X8] : r1_tarski(k1_xboole_0,X8) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_42,plain,(
    ! [X49,X50,X51] :
      ( ( ~ v1_funct_2(X51,X49,X50)
        | X49 = k1_relset_1(X49,X50,X51)
        | X50 = k1_xboole_0
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))) )
      & ( X49 != k1_relset_1(X49,X50,X51)
        | v1_funct_2(X51,X49,X50)
        | X50 = k1_xboole_0
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))) )
      & ( ~ v1_funct_2(X51,X49,X50)
        | X49 = k1_relset_1(X49,X50,X51)
        | X49 != k1_xboole_0
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))) )
      & ( X49 != k1_relset_1(X49,X50,X51)
        | v1_funct_2(X51,X49,X50)
        | X49 != k1_xboole_0
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))) )
      & ( ~ v1_funct_2(X51,X49,X50)
        | X51 = k1_xboole_0
        | X49 = k1_xboole_0
        | X50 != k1_xboole_0
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))) )
      & ( X51 != k1_xboole_0
        | v1_funct_2(X51,X49,X50)
        | X49 = k1_xboole_0
        | X50 != k1_xboole_0
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_43,plain,
    ( X3 = k1_xboole_0
    | r2_hidden(k1_funct_1(X1,X4),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_2(esk7_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_46,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk5_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_48,plain,
    ( r2_hidden(esk4_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_51,plain,(
    ! [X29,X30,X31,X33,X34] :
      ( ( r2_hidden(esk2_3(X29,X30,X31),X30)
        | k1_relset_1(X30,X29,X31) = X30
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X30,X29))) )
      & ( ~ r2_hidden(k4_tarski(esk2_3(X29,X30,X31),X33),X31)
        | k1_relset_1(X30,X29,X31) = X30
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X30,X29))) )
      & ( k1_relset_1(X30,X29,X31) != X30
        | ~ r2_hidden(X34,X30)
        | r2_hidden(k4_tarski(X34,esk3_4(X29,X30,X31,X34)),X31)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X30,X29))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_relset_1])])])])])])).

fof(c_0_52,plain,(
    ! [X21] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X21)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_53,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk7_0,X1),esk6_0)
    | ~ r2_hidden(X1,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_30]),c_0_44]),c_0_45])]),c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk5_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk7_0,esk5_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_57,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_58,plain,
    ( r2_hidden(k4_tarski(X4,esk3_4(X2,X1,X3,X4)),X3)
    | k1_relset_1(X1,X2,X3) != X1
    | ~ r2_hidden(X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_59,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( k1_relset_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0,esk7_0) = k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_30]),c_0_45])]),c_0_46])).

cnf(c_0_61,negated_conjecture,
    ( esk7_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])).

fof(c_0_62,plain,(
    ! [X22,X23] :
      ( ~ m1_subset_1(X22,X23)
      | v1_xboole_0(X23)
      | r2_hidden(X22,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_63,plain,(
    ! [X16] : m1_subset_1(esk1_1(X16),X16) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_64,plain,(
    ! [X15] : ~ v1_xboole_0(k1_tarski(X15)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

cnf(c_0_65,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) != X1
    | ~ r2_hidden(X3,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])])).

cnf(c_0_66,negated_conjecture,
    ( k1_relset_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0,k1_xboole_0) = k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_67,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_68,plain,
    ( m1_subset_1(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_69,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( ~ r2_hidden(X1,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_71,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_72,plain,
    ( ~ v1_xboole_0(k2_enumset1(X1,X1,X1,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:58:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.13/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.028 s
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t61_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r2_hidden(k1_funct_1(X3,X1),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 0.13/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.39  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.13/0.39  fof(t12_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))=>(k1_mcart_1(X1)=X2&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_mcart_1)).
% 0.13/0.39  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.13/0.39  fof(t7_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_hidden(X3,X1)=>(X2=k1_xboole_0|r2_hidden(k1_funct_1(X4,X3),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 0.13/0.39  fof(t6_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5, X6, X7]:(((((r2_hidden(X3,X4)&r2_hidden(X4,X5))&r2_hidden(X5,X6))&r2_hidden(X6,X7))&r2_hidden(X7,X2))=>r1_xboole_0(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_mcart_1)).
% 0.13/0.39  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.13/0.39  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.13/0.39  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.13/0.39  fof(t22_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~(r2_hidden(k4_tarski(X4,X5),X3))))<=>k1_relset_1(X2,X1,X3)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relset_1)).
% 0.13/0.39  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.13/0.39  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.13/0.39  fof(existence_m1_subset_1, axiom, ![X1]:?[X2]:m1_subset_1(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 0.13/0.39  fof(fc2_xboole_0, axiom, ![X1]:~(v1_xboole_0(k1_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 0.13/0.39  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r2_hidden(k1_funct_1(X3,X1),X2)))), inference(assume_negation,[status(cth)],[t61_funct_2])).
% 0.13/0.39  fof(c_0_18, negated_conjecture, (((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,k1_tarski(esk5_0),esk6_0))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk5_0),esk6_0))))&(esk6_0!=k1_xboole_0&~r2_hidden(k1_funct_1(esk7_0,esk5_0),esk6_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.13/0.39  fof(c_0_19, plain, ![X9]:k2_tarski(X9,X9)=k1_tarski(X9), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.39  fof(c_0_20, plain, ![X10, X11]:k1_enumset1(X10,X10,X11)=k2_tarski(X10,X11), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.39  fof(c_0_21, plain, ![X12, X13, X14]:k2_enumset1(X12,X12,X13,X14)=k1_enumset1(X12,X13,X14), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.39  fof(c_0_22, plain, ![X18, X19, X20]:(~m1_subset_1(X19,k1_zfmisc_1(X18))|(~r2_hidden(X20,X19)|r2_hidden(X20,X18))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.13/0.39  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk5_0),esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  cnf(c_0_24, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.39  cnf(c_0_25, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.39  cnf(c_0_26, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.39  fof(c_0_27, plain, ![X39, X40, X41]:((k1_mcart_1(X39)=X40|~r2_hidden(X39,k2_zfmisc_1(k1_tarski(X40),X41)))&(r2_hidden(k2_mcart_1(X39),X41)|~r2_hidden(X39,k2_zfmisc_1(k1_tarski(X40),X41)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_mcart_1])])])).
% 0.13/0.39  fof(c_0_28, plain, ![X36, X37, X38]:((r2_hidden(k1_mcart_1(X36),X37)|~r2_hidden(X36,k2_zfmisc_1(X37,X38)))&(r2_hidden(k2_mcart_1(X36),X38)|~r2_hidden(X36,k2_zfmisc_1(X37,X38)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.13/0.39  cnf(c_0_29, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26])).
% 0.13/0.39  cnf(c_0_31, plain, (k1_mcart_1(X1)=X2|~r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.39  cnf(c_0_32, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.39  cnf(c_0_33, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.13/0.39  cnf(c_0_34, plain, (k1_mcart_1(X1)=X2|~r2_hidden(X1,k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_24]), c_0_25]), c_0_26])).
% 0.13/0.39  fof(c_0_35, plain, ![X52, X53, X54, X55]:(~v1_funct_1(X55)|~v1_funct_2(X55,X52,X53)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))|(~r2_hidden(X54,X52)|(X53=k1_xboole_0|r2_hidden(k1_funct_1(X55,X54),X53)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).
% 0.13/0.39  cnf(c_0_36, negated_conjecture, (v1_funct_2(esk7_0,k1_tarski(esk5_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  cnf(c_0_37, negated_conjecture, (r2_hidden(k1_mcart_1(X1),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.13/0.39  cnf(c_0_38, negated_conjecture, (k1_mcart_1(X1)=esk5_0|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_34, c_0_33])).
% 0.13/0.39  fof(c_0_39, plain, ![X42, X44, X45, X46, X47, X48]:((r2_hidden(esk4_1(X42),X42)|X42=k1_xboole_0)&(~r2_hidden(X44,X45)|~r2_hidden(X45,X46)|~r2_hidden(X46,X47)|~r2_hidden(X47,X48)|~r2_hidden(X48,esk4_1(X42))|r1_xboole_0(X44,X42)|X42=k1_xboole_0)), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_mcart_1])])])])])])).
% 0.13/0.39  fof(c_0_40, plain, ![X27, X28]:(~r2_hidden(X27,X28)|~r1_tarski(X28,X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.13/0.39  fof(c_0_41, plain, ![X8]:r1_tarski(k1_xboole_0,X8), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.13/0.39  fof(c_0_42, plain, ![X49, X50, X51]:((((~v1_funct_2(X51,X49,X50)|X49=k1_relset_1(X49,X50,X51)|X50=k1_xboole_0|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))))&(X49!=k1_relset_1(X49,X50,X51)|v1_funct_2(X51,X49,X50)|X50=k1_xboole_0|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))))&((~v1_funct_2(X51,X49,X50)|X49=k1_relset_1(X49,X50,X51)|X49!=k1_xboole_0|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))))&(X49!=k1_relset_1(X49,X50,X51)|v1_funct_2(X51,X49,X50)|X49!=k1_xboole_0|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))))))&((~v1_funct_2(X51,X49,X50)|X51=k1_xboole_0|X49=k1_xboole_0|X50!=k1_xboole_0|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))))&(X51!=k1_xboole_0|v1_funct_2(X51,X49,X50)|X49=k1_xboole_0|X50!=k1_xboole_0|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.13/0.39  cnf(c_0_43, plain, (X3=k1_xboole_0|r2_hidden(k1_funct_1(X1,X4),X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.39  cnf(c_0_44, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  cnf(c_0_45, negated_conjecture, (v1_funct_2(esk7_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_24]), c_0_25]), c_0_26])).
% 0.13/0.39  cnf(c_0_46, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  cnf(c_0_47, negated_conjecture, (r2_hidden(esk5_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.13/0.39  cnf(c_0_48, plain, (r2_hidden(esk4_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.39  cnf(c_0_49, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.13/0.39  cnf(c_0_50, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.13/0.39  fof(c_0_51, plain, ![X29, X30, X31, X33, X34]:(((r2_hidden(esk2_3(X29,X30,X31),X30)|k1_relset_1(X30,X29,X31)=X30|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X30,X29))))&(~r2_hidden(k4_tarski(esk2_3(X29,X30,X31),X33),X31)|k1_relset_1(X30,X29,X31)=X30|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X30,X29)))))&(k1_relset_1(X30,X29,X31)!=X30|(~r2_hidden(X34,X30)|r2_hidden(k4_tarski(X34,esk3_4(X29,X30,X31,X34)),X31))|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X30,X29))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_relset_1])])])])])])).
% 0.13/0.39  fof(c_0_52, plain, ![X21]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X21)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.13/0.39  cnf(c_0_53, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.13/0.39  cnf(c_0_54, negated_conjecture, (r2_hidden(k1_funct_1(esk7_0,X1),esk6_0)|~r2_hidden(X1,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_30]), c_0_44]), c_0_45])]), c_0_46])).
% 0.13/0.39  cnf(c_0_55, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk5_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.13/0.39  cnf(c_0_56, negated_conjecture, (~r2_hidden(k1_funct_1(esk7_0,esk5_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  cnf(c_0_57, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.13/0.39  cnf(c_0_58, plain, (r2_hidden(k4_tarski(X4,esk3_4(X2,X1,X3,X4)),X3)|k1_relset_1(X1,X2,X3)!=X1|~r2_hidden(X4,X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.13/0.39  cnf(c_0_59, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.13/0.39  cnf(c_0_60, negated_conjecture, (k1_relset_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0,esk7_0)=k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_30]), c_0_45])]), c_0_46])).
% 0.13/0.39  cnf(c_0_61, negated_conjecture, (esk7_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])).
% 0.13/0.39  fof(c_0_62, plain, ![X22, X23]:(~m1_subset_1(X22,X23)|(v1_xboole_0(X23)|r2_hidden(X22,X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.13/0.39  fof(c_0_63, plain, ![X16]:m1_subset_1(esk1_1(X16),X16), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).
% 0.13/0.39  fof(c_0_64, plain, ![X15]:~v1_xboole_0(k1_tarski(X15)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).
% 0.13/0.39  cnf(c_0_65, plain, (k1_relset_1(X1,X2,k1_xboole_0)!=X1|~r2_hidden(X3,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])])).
% 0.13/0.39  cnf(c_0_66, negated_conjecture, (k1_relset_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0,k1_xboole_0)=k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[c_0_60, c_0_61])).
% 0.13/0.39  cnf(c_0_67, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.13/0.39  cnf(c_0_68, plain, (m1_subset_1(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.13/0.39  cnf(c_0_69, plain, (~v1_xboole_0(k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.13/0.39  cnf(c_0_70, negated_conjecture, (~r2_hidden(X1,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.13/0.39  cnf(c_0_71, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.13/0.39  cnf(c_0_72, plain, (~v1_xboole_0(k2_enumset1(X1,X1,X1,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_24]), c_0_25]), c_0_26])).
% 0.13/0.39  cnf(c_0_73, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 74
% 0.13/0.39  # Proof object clause steps            : 39
% 0.13/0.39  # Proof object formula steps           : 35
% 0.13/0.39  # Proof object conjectures             : 21
% 0.13/0.39  # Proof object clause conjectures      : 18
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 21
% 0.13/0.39  # Proof object initial formulas used   : 17
% 0.13/0.39  # Proof object generating inferences   : 13
% 0.13/0.39  # Proof object simplifying inferences  : 24
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 18
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 32
% 0.13/0.39  # Removed in clause preprocessing      : 3
% 0.13/0.39  # Initial clauses in saturation        : 29
% 0.13/0.39  # Processed clauses                    : 177
% 0.13/0.39  # ...of these trivial                  : 1
% 0.13/0.39  # ...subsumed                          : 41
% 0.13/0.39  # ...remaining for further processing  : 135
% 0.13/0.39  # Other redundant clauses eliminated   : 5
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 5
% 0.13/0.39  # Backward-rewritten                   : 35
% 0.13/0.39  # Generated clauses                    : 729
% 0.13/0.39  # ...of the previous two non-trivial   : 590
% 0.13/0.39  # Contextual simplify-reflections      : 0
% 0.13/0.39  # Paramodulations                      : 725
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 5
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
% 0.13/0.39  # Current number of processed clauses  : 91
% 0.13/0.39  #    Positive orientable unit clauses  : 14
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 5
% 0.13/0.39  #    Non-unit-clauses                  : 72
% 0.13/0.39  # Current number of unprocessed clauses: 404
% 0.13/0.39  # ...number of literals in the above   : 1501
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 43
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 1020
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 578
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 18
% 0.13/0.39  # Unit Clause-clause subsumption calls : 30
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 9
% 0.13/0.39  # BW rewrite match successes           : 6
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 16190
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.043 s
% 0.13/0.39  # System time              : 0.007 s
% 0.13/0.39  # Total time               : 0.050 s
% 0.13/0.39  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
