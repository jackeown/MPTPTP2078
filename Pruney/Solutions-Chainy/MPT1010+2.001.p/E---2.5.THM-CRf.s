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
% DateTime   : Thu Dec  3 11:05:11 EST 2020

% Result     : Theorem 4.31s
% Output     : CNFRefutation 4.31s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 146 expanded)
%              Number of clauses        :   37 (  62 expanded)
%              Number of leaves         :   14 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :  212 ( 443 expanded)
%              Number of equality atoms :   86 ( 205 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t65_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,k1_tarski(X2))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
     => ( r2_hidden(X3,X1)
       => k1_funct_1(X4,X3) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

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

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_14,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( ~ r2_hidden(X15,X14)
        | X15 = X11
        | X15 = X12
        | X15 = X13
        | X14 != k1_enumset1(X11,X12,X13) )
      & ( X16 != X11
        | r2_hidden(X16,X14)
        | X14 != k1_enumset1(X11,X12,X13) )
      & ( X16 != X12
        | r2_hidden(X16,X14)
        | X14 != k1_enumset1(X11,X12,X13) )
      & ( X16 != X13
        | r2_hidden(X16,X14)
        | X14 != k1_enumset1(X11,X12,X13) )
      & ( esk2_4(X17,X18,X19,X20) != X17
        | ~ r2_hidden(esk2_4(X17,X18,X19,X20),X20)
        | X20 = k1_enumset1(X17,X18,X19) )
      & ( esk2_4(X17,X18,X19,X20) != X18
        | ~ r2_hidden(esk2_4(X17,X18,X19,X20),X20)
        | X20 = k1_enumset1(X17,X18,X19) )
      & ( esk2_4(X17,X18,X19,X20) != X19
        | ~ r2_hidden(esk2_4(X17,X18,X19,X20),X20)
        | X20 = k1_enumset1(X17,X18,X19) )
      & ( r2_hidden(esk2_4(X17,X18,X19,X20),X20)
        | esk2_4(X17,X18,X19,X20) = X17
        | esk2_4(X17,X18,X19,X20) = X18
        | esk2_4(X17,X18,X19,X20) = X19
        | X20 = k1_enumset1(X17,X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_15,plain,(
    ! [X25,X26,X27] : k2_enumset1(X25,X25,X26,X27) = k1_enumset1(X25,X26,X27) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,k1_tarski(X2))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
       => ( r2_hidden(X3,X1)
         => k1_funct_1(X4,X3) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t65_funct_2])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,negated_conjecture,
    ( v1_funct_1(esk10_0)
    & v1_funct_2(esk10_0,esk7_0,k1_tarski(esk8_0))
    & m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,k1_tarski(esk8_0))))
    & r2_hidden(esk9_0,esk7_0)
    & k1_funct_1(esk10_0,esk9_0) != esk8_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_20,plain,(
    ! [X22] : k2_tarski(X22,X22) = k1_tarski(X22) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_21,plain,(
    ! [X23,X24] : k1_enumset1(X23,X23,X24) = k2_tarski(X23,X24) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_23,plain,(
    ! [X67,X68,X69] :
      ( ~ m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(X67,X68)))
      | k1_relset_1(X67,X68,X69) = k1_relat_1(X69) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,k1_tarski(esk8_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_28,plain,(
    ! [X40,X41] :
      ( ~ m1_subset_1(X40,X41)
      | v1_xboole_0(X41)
      | r2_hidden(X40,X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_29,plain,(
    ! [X45,X46,X47] :
      ( ~ v1_relat_1(X47)
      | ~ v5_relat_1(X47,X45)
      | ~ v1_funct_1(X47)
      | ~ r2_hidden(X46,k1_relat_1(X47))
      | m1_subset_1(k1_funct_1(X47,X46),X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t176_funct_1])])).

fof(c_0_30,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X2)
    | X2 != k2_enumset1(X3,X3,X4,X1) ),
    inference(er,[status(thm)],[c_0_22])).

fof(c_0_32,plain,(
    ! [X56,X57] :
      ( ~ r2_hidden(X56,X57)
      | ~ r1_tarski(X57,X56) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_33,plain,(
    ! [X70,X71,X72] :
      ( ( ~ v1_funct_2(X72,X70,X71)
        | X70 = k1_relset_1(X70,X71,X72)
        | X71 = k1_xboole_0
        | ~ m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X70,X71))) )
      & ( X70 != k1_relset_1(X70,X71,X72)
        | v1_funct_2(X72,X70,X71)
        | X71 = k1_xboole_0
        | ~ m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X70,X71))) )
      & ( ~ v1_funct_2(X72,X70,X71)
        | X70 = k1_relset_1(X70,X71,X72)
        | X70 != k1_xboole_0
        | ~ m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X70,X71))) )
      & ( X70 != k1_relset_1(X70,X71,X72)
        | v1_funct_2(X72,X70,X71)
        | X70 != k1_xboole_0
        | ~ m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X70,X71))) )
      & ( ~ v1_funct_2(X72,X70,X71)
        | X72 = k1_xboole_0
        | X70 = k1_xboole_0
        | X71 != k1_xboole_0
        | ~ m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X70,X71))) )
      & ( X72 != k1_xboole_0
        | v1_funct_2(X72,X70,X71)
        | X70 = k1_xboole_0
        | X71 != k1_xboole_0
        | ~ m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X70,X71))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_2(esk10_0,esk7_0,k1_tarski(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_35,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_18])).

cnf(c_0_37,plain,
    ( X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k2_enumset1(X3,X3,X4,X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_27,c_0_18])).

cnf(c_0_38,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( m1_subset_1(k1_funct_1(X1,X3),X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[c_0_31])).

fof(c_0_42,plain,(
    ! [X61,X62,X63] :
      ( ( v4_relat_1(X63,X61)
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X61,X62))) )
      & ( v5_relat_1(X63,X62)
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X61,X62))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_43,plain,(
    ! [X58,X59,X60] :
      ( ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X59)))
      | v1_relat_1(X60) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,negated_conjecture,
    ( v1_funct_2(esk10_0,esk7_0,k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_25]),c_0_26]),c_0_18])).

cnf(c_0_47,negated_conjecture,
    ( k1_relset_1(esk7_0,k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0),esk10_0) = k1_relat_1(esk10_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_48,plain,(
    ! [X10] : r1_tarski(k1_xboole_0,X10) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_49,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X3,X4)) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_50,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | v1_xboole_0(X3)
    | ~ v5_relat_1(X1,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_51,plain,
    ( ~ v1_xboole_0(k2_enumset1(X1,X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_52,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,plain,
    ( ~ r1_tarski(k2_enumset1(X1,X1,X2,X3),X3) ),
    inference(spm,[status(thm)],[c_0_44,c_0_41])).

cnf(c_0_55,negated_conjecture,
    ( k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0) = k1_xboole_0
    | k1_relat_1(esk10_0) = esk7_0 ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_36]),c_0_46])]),c_0_47])).

cnf(c_0_56,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_57,plain,
    ( k1_funct_1(X1,X2) = X3
    | k1_funct_1(X1,X2) = X4
    | k1_funct_1(X1,X2) = X5
    | ~ v5_relat_1(X1,k2_enumset1(X5,X5,X4,X3))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( v5_relat_1(esk10_0,k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_36])).

cnf(c_0_59,negated_conjecture,
    ( v1_funct_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_60,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_36])).

cnf(c_0_61,negated_conjecture,
    ( k1_relat_1(esk10_0) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])])).

cnf(c_0_62,negated_conjecture,
    ( k1_funct_1(esk10_0,esk9_0) != esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_63,negated_conjecture,
    ( k1_funct_1(esk10_0,X1) = esk8_0
    | ~ r2_hidden(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59]),c_0_60]),c_0_61])])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk9_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:21:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 4.31/4.49  # AutoSched0-Mode selected heuristic G_E___107_C36_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 4.31/4.49  # and selection function SelectMaxLComplexAvoidPosPred.
% 4.31/4.49  #
% 4.31/4.49  # Preprocessing time       : 0.047 s
% 4.31/4.49  # Presaturation interreduction done
% 4.31/4.49  
% 4.31/4.49  # Proof found!
% 4.31/4.49  # SZS status Theorem
% 4.31/4.49  # SZS output start CNFRefutation
% 4.31/4.49  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 4.31/4.49  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 4.31/4.49  fof(t65_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>(r2_hidden(X3,X1)=>k1_funct_1(X4,X3)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 4.31/4.49  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.31/4.49  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.31/4.49  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.31/4.49  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.31/4.49  fof(t176_funct_1, axiom, ![X1, X2, X3]:(((v1_relat_1(X3)&v5_relat_1(X3,X1))&v1_funct_1(X3))=>(r2_hidden(X2,k1_relat_1(X3))=>m1_subset_1(k1_funct_1(X3,X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_1)).
% 4.31/4.49  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.31/4.49  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.31/4.49  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.31/4.49  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.31/4.49  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.31/4.49  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.31/4.49  fof(c_0_14, plain, ![X11, X12, X13, X14, X15, X16, X17, X18, X19, X20]:(((~r2_hidden(X15,X14)|(X15=X11|X15=X12|X15=X13)|X14!=k1_enumset1(X11,X12,X13))&(((X16!=X11|r2_hidden(X16,X14)|X14!=k1_enumset1(X11,X12,X13))&(X16!=X12|r2_hidden(X16,X14)|X14!=k1_enumset1(X11,X12,X13)))&(X16!=X13|r2_hidden(X16,X14)|X14!=k1_enumset1(X11,X12,X13))))&((((esk2_4(X17,X18,X19,X20)!=X17|~r2_hidden(esk2_4(X17,X18,X19,X20),X20)|X20=k1_enumset1(X17,X18,X19))&(esk2_4(X17,X18,X19,X20)!=X18|~r2_hidden(esk2_4(X17,X18,X19,X20),X20)|X20=k1_enumset1(X17,X18,X19)))&(esk2_4(X17,X18,X19,X20)!=X19|~r2_hidden(esk2_4(X17,X18,X19,X20),X20)|X20=k1_enumset1(X17,X18,X19)))&(r2_hidden(esk2_4(X17,X18,X19,X20),X20)|(esk2_4(X17,X18,X19,X20)=X17|esk2_4(X17,X18,X19,X20)=X18|esk2_4(X17,X18,X19,X20)=X19)|X20=k1_enumset1(X17,X18,X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 4.31/4.49  fof(c_0_15, plain, ![X25, X26, X27]:k2_enumset1(X25,X25,X26,X27)=k1_enumset1(X25,X26,X27), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 4.31/4.49  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>(r2_hidden(X3,X1)=>k1_funct_1(X4,X3)=X2))), inference(assume_negation,[status(cth)],[t65_funct_2])).
% 4.31/4.49  cnf(c_0_17, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 4.31/4.49  cnf(c_0_18, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 4.31/4.49  fof(c_0_19, negated_conjecture, (((v1_funct_1(esk10_0)&v1_funct_2(esk10_0,esk7_0,k1_tarski(esk8_0)))&m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,k1_tarski(esk8_0)))))&(r2_hidden(esk9_0,esk7_0)&k1_funct_1(esk10_0,esk9_0)!=esk8_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 4.31/4.49  fof(c_0_20, plain, ![X22]:k2_tarski(X22,X22)=k1_tarski(X22), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 4.31/4.49  fof(c_0_21, plain, ![X23, X24]:k1_enumset1(X23,X23,X24)=k2_tarski(X23,X24), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 4.31/4.49  cnf(c_0_22, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X4,X5,X2)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 4.31/4.49  fof(c_0_23, plain, ![X67, X68, X69]:(~m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(X67,X68)))|k1_relset_1(X67,X68,X69)=k1_relat_1(X69)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 4.31/4.49  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,k1_tarski(esk8_0))))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 4.31/4.49  cnf(c_0_25, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 4.31/4.49  cnf(c_0_26, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.31/4.49  cnf(c_0_27, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 4.31/4.49  fof(c_0_28, plain, ![X40, X41]:(~m1_subset_1(X40,X41)|(v1_xboole_0(X41)|r2_hidden(X40,X41))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 4.31/4.49  fof(c_0_29, plain, ![X45, X46, X47]:(~v1_relat_1(X47)|~v5_relat_1(X47,X45)|~v1_funct_1(X47)|(~r2_hidden(X46,k1_relat_1(X47))|m1_subset_1(k1_funct_1(X47,X46),X45))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t176_funct_1])])).
% 4.31/4.49  fof(c_0_30, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 4.31/4.49  cnf(c_0_31, plain, (r2_hidden(X1,X2)|X2!=k2_enumset1(X3,X3,X4,X1)), inference(er,[status(thm)],[c_0_22])).
% 4.31/4.49  fof(c_0_32, plain, ![X56, X57]:(~r2_hidden(X56,X57)|~r1_tarski(X57,X56)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 4.31/4.49  fof(c_0_33, plain, ![X70, X71, X72]:((((~v1_funct_2(X72,X70,X71)|X70=k1_relset_1(X70,X71,X72)|X71=k1_xboole_0|~m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X70,X71))))&(X70!=k1_relset_1(X70,X71,X72)|v1_funct_2(X72,X70,X71)|X71=k1_xboole_0|~m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X70,X71)))))&((~v1_funct_2(X72,X70,X71)|X70=k1_relset_1(X70,X71,X72)|X70!=k1_xboole_0|~m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X70,X71))))&(X70!=k1_relset_1(X70,X71,X72)|v1_funct_2(X72,X70,X71)|X70!=k1_xboole_0|~m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X70,X71))))))&((~v1_funct_2(X72,X70,X71)|X72=k1_xboole_0|X70=k1_xboole_0|X71!=k1_xboole_0|~m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X70,X71))))&(X72!=k1_xboole_0|v1_funct_2(X72,X70,X71)|X70=k1_xboole_0|X71!=k1_xboole_0|~m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X70,X71)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 4.31/4.49  cnf(c_0_34, negated_conjecture, (v1_funct_2(esk10_0,esk7_0,k1_tarski(esk8_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 4.31/4.49  cnf(c_0_35, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 4.31/4.49  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_18])).
% 4.31/4.49  cnf(c_0_37, plain, (X1=X5|X1=X4|X1=X3|X2!=k2_enumset1(X3,X3,X4,X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_27, c_0_18])).
% 4.31/4.49  cnf(c_0_38, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 4.31/4.49  cnf(c_0_39, plain, (m1_subset_1(k1_funct_1(X1,X3),X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)|~v1_funct_1(X1)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 4.31/4.49  cnf(c_0_40, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 4.31/4.49  cnf(c_0_41, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X3,X1))), inference(er,[status(thm)],[c_0_31])).
% 4.31/4.49  fof(c_0_42, plain, ![X61, X62, X63]:((v4_relat_1(X63,X61)|~m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X61,X62))))&(v5_relat_1(X63,X62)|~m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X61,X62))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 4.31/4.49  fof(c_0_43, plain, ![X58, X59, X60]:(~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X59)))|v1_relat_1(X60)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 4.31/4.49  cnf(c_0_44, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 4.31/4.49  cnf(c_0_45, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 4.31/4.49  cnf(c_0_46, negated_conjecture, (v1_funct_2(esk10_0,esk7_0,k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_25]), c_0_26]), c_0_18])).
% 4.31/4.49  cnf(c_0_47, negated_conjecture, (k1_relset_1(esk7_0,k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0),esk10_0)=k1_relat_1(esk10_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 4.31/4.49  fof(c_0_48, plain, ![X10]:r1_tarski(k1_xboole_0,X10), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 4.31/4.49  cnf(c_0_49, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k2_enumset1(X2,X2,X3,X4))), inference(er,[status(thm)],[c_0_37])).
% 4.31/4.49  cnf(c_0_50, plain, (r2_hidden(k1_funct_1(X1,X2),X3)|v1_xboole_0(X3)|~v5_relat_1(X1,X3)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 4.31/4.49  cnf(c_0_51, plain, (~v1_xboole_0(k2_enumset1(X1,X1,X2,X3))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 4.31/4.49  cnf(c_0_52, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 4.31/4.49  cnf(c_0_53, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 4.31/4.49  cnf(c_0_54, plain, (~r1_tarski(k2_enumset1(X1,X1,X2,X3),X3)), inference(spm,[status(thm)],[c_0_44, c_0_41])).
% 4.31/4.49  cnf(c_0_55, negated_conjecture, (k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)=k1_xboole_0|k1_relat_1(esk10_0)=esk7_0), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_36]), c_0_46])]), c_0_47])).
% 4.31/4.49  cnf(c_0_56, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 4.31/4.49  cnf(c_0_57, plain, (k1_funct_1(X1,X2)=X3|k1_funct_1(X1,X2)=X4|k1_funct_1(X1,X2)=X5|~v5_relat_1(X1,k2_enumset1(X5,X5,X4,X3))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])).
% 4.31/4.49  cnf(c_0_58, negated_conjecture, (v5_relat_1(esk10_0,k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))), inference(spm,[status(thm)],[c_0_52, c_0_36])).
% 4.31/4.49  cnf(c_0_59, negated_conjecture, (v1_funct_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 4.31/4.49  cnf(c_0_60, negated_conjecture, (v1_relat_1(esk10_0)), inference(spm,[status(thm)],[c_0_53, c_0_36])).
% 4.31/4.49  cnf(c_0_61, negated_conjecture, (k1_relat_1(esk10_0)=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])])).
% 4.31/4.49  cnf(c_0_62, negated_conjecture, (k1_funct_1(esk10_0,esk9_0)!=esk8_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 4.31/4.49  cnf(c_0_63, negated_conjecture, (k1_funct_1(esk10_0,X1)=esk8_0|~r2_hidden(X1,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59]), c_0_60]), c_0_61])])).
% 4.31/4.49  cnf(c_0_64, negated_conjecture, (r2_hidden(esk9_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 4.31/4.49  cnf(c_0_65, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])]), ['proof']).
% 4.31/4.49  # SZS output end CNFRefutation
% 4.31/4.49  # Proof object total steps             : 66
% 4.31/4.49  # Proof object clause steps            : 37
% 4.31/4.49  # Proof object formula steps           : 29
% 4.31/4.49  # Proof object conjectures             : 17
% 4.31/4.49  # Proof object clause conjectures      : 14
% 4.31/4.49  # Proof object formula conjectures     : 3
% 4.31/4.49  # Proof object initial clauses used    : 19
% 4.31/4.49  # Proof object initial formulas used   : 14
% 4.31/4.49  # Proof object generating inferences   : 13
% 4.31/4.49  # Proof object simplifying inferences  : 21
% 4.31/4.49  # Training examples: 0 positive, 0 negative
% 4.31/4.49  # Parsed axioms                        : 22
% 4.31/4.49  # Removed by relevancy pruning/SinE    : 0
% 4.31/4.49  # Initial clauses                      : 51
% 4.31/4.49  # Removed in clause preprocessing      : 3
% 4.31/4.49  # Initial clauses in saturation        : 48
% 4.31/4.49  # Processed clauses                    : 3935
% 4.31/4.49  # ...of these trivial                  : 22
% 4.31/4.49  # ...subsumed                          : 1474
% 4.31/4.49  # ...remaining for further processing  : 2439
% 4.31/4.49  # Other redundant clauses eliminated   : 2365
% 4.31/4.49  # Clauses deleted for lack of memory   : 0
% 4.31/4.49  # Backward-subsumed                    : 229
% 4.31/4.49  # Backward-rewritten                   : 33
% 4.31/4.49  # Generated clauses                    : 83923
% 4.31/4.49  # ...of the previous two non-trivial   : 76448
% 4.31/4.49  # Contextual simplify-reflections      : 25
% 4.31/4.49  # Paramodulations                      : 80950
% 4.31/4.49  # Factorizations                       : 74
% 4.31/4.49  # Equation resolutions                 : 2896
% 4.31/4.49  # Propositional unsat checks           : 0
% 4.31/4.49  #    Propositional check models        : 0
% 4.31/4.49  #    Propositional check unsatisfiable : 0
% 4.31/4.49  #    Propositional clauses             : 0
% 4.31/4.49  #    Propositional clauses after purity: 0
% 4.31/4.49  #    Propositional unsat core size     : 0
% 4.31/4.49  #    Propositional preprocessing time  : 0.000
% 4.31/4.49  #    Propositional encoding time       : 0.000
% 4.31/4.49  #    Propositional solver time         : 0.000
% 4.31/4.49  #    Success case prop preproc time    : 0.000
% 4.31/4.49  #    Success case prop encoding time   : 0.000
% 4.31/4.49  #    Success case prop solver time     : 0.000
% 4.31/4.49  # Current number of processed clauses  : 2125
% 4.31/4.49  #    Positive orientable unit clauses  : 35
% 4.31/4.49  #    Positive unorientable unit clauses: 0
% 4.31/4.49  #    Negative unit clauses             : 17
% 4.31/4.49  #    Non-unit-clauses                  : 2073
% 4.31/4.49  # Current number of unprocessed clauses: 71517
% 4.31/4.49  # ...number of literals in the above   : 634374
% 4.31/4.49  # Current number of archived formulas  : 0
% 4.31/4.49  # Current number of archived clauses   : 313
% 4.31/4.49  # Clause-clause subsumption calls (NU) : 717695
% 4.31/4.49  # Rec. Clause-clause subsumption calls : 137096
% 4.31/4.49  # Non-unit clause-clause subsumptions  : 1424
% 4.31/4.49  # Unit Clause-clause subsumption calls : 2667
% 4.31/4.49  # Rewrite failures with RHS unbound    : 0
% 4.31/4.49  # BW rewrite match attempts            : 74
% 4.31/4.49  # BW rewrite match successes           : 16
% 4.31/4.49  # Condensation attempts                : 0
% 4.31/4.49  # Condensation successes               : 0
% 4.31/4.49  # Termbank termtop insertions          : 2192781
% 4.31/4.50  
% 4.31/4.50  # -------------------------------------------------
% 4.31/4.50  # User time                : 4.084 s
% 4.31/4.50  # System time              : 0.071 s
% 4.31/4.50  # Total time               : 4.155 s
% 4.31/4.50  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
