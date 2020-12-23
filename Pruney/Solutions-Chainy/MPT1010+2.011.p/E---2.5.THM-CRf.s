%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:05:12 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 167 expanded)
%              Number of clauses        :   42 (  70 expanded)
%              Number of leaves         :   17 (  44 expanded)
%              Depth                    :   12
%              Number of atoms          :  288 ( 477 expanded)
%              Number of equality atoms :  114 ( 192 expanded)
%              Maximal formula depth    :   27 (   5 average)
%              Maximal clause size      :   36 (   2 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

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

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

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

fof(d2_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( X5 = k2_enumset1(X1,X2,X3,X4)
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X6 != X1
              & X6 != X2
              & X6 != X3
              & X6 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,k1_tarski(X2))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
       => ( r2_hidden(X3,X1)
         => k1_funct_1(X4,X3) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t65_funct_2])).

fof(c_0_18,plain,(
    ! [X21,X22,X23,X24,X25,X26] :
      ( ( ~ r2_hidden(X23,X22)
        | r1_tarski(X23,X21)
        | X22 != k1_zfmisc_1(X21) )
      & ( ~ r1_tarski(X24,X21)
        | r2_hidden(X24,X22)
        | X22 != k1_zfmisc_1(X21) )
      & ( ~ r2_hidden(esk2_2(X25,X26),X26)
        | ~ r1_tarski(esk2_2(X25,X26),X25)
        | X26 = k1_zfmisc_1(X25) )
      & ( r2_hidden(esk2_2(X25,X26),X26)
        | r1_tarski(esk2_2(X25,X26),X25)
        | X26 = k1_zfmisc_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_19,negated_conjecture,
    ( v1_funct_1(esk10_0)
    & v1_funct_2(esk10_0,esk7_0,k1_tarski(esk8_0))
    & m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,k1_tarski(esk8_0))))
    & r2_hidden(esk9_0,esk7_0)
    & k1_funct_1(esk10_0,esk9_0) != esk8_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_20,plain,(
    ! [X15] : k2_tarski(X15,X15) = k1_tarski(X15) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_21,plain,(
    ! [X16,X17] : k1_enumset1(X16,X16,X17) = k2_tarski(X16,X17) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_22,plain,(
    ! [X18,X19,X20] : k2_enumset1(X18,X18,X19,X20) = k1_enumset1(X18,X19,X20) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X46,X47] :
      ( ( ~ v5_relat_1(X47,X46)
        | r1_tarski(k2_relat_1(X47),X46)
        | ~ v1_relat_1(X47) )
      & ( ~ r1_tarski(k2_relat_1(X47),X46)
        | v5_relat_1(X47,X46)
        | ~ v1_relat_1(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

fof(c_0_25,plain,(
    ! [X63,X64,X65] :
      ( ( v4_relat_1(X65,X63)
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))) )
      & ( v5_relat_1(X65,X64)
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,k1_tarski(esk8_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_30,plain,(
    ! [X60,X61,X62] :
      ( ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))
      | v1_relat_1(X62) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_31,plain,(
    ! [X8,X9,X10,X11,X12,X13] :
      ( ( ~ r2_hidden(X10,X9)
        | X10 = X8
        | X9 != k1_tarski(X8) )
      & ( X11 != X8
        | r2_hidden(X11,X9)
        | X9 != k1_tarski(X8) )
      & ( ~ r2_hidden(esk1_2(X12,X13),X13)
        | esk1_2(X12,X13) != X12
        | X13 = k1_tarski(X12) )
      & ( r2_hidden(esk1_2(X12,X13),X13)
        | esk1_2(X12,X13) = X12
        | X13 = k1_tarski(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_32,plain,(
    ! [X41,X42,X43] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(X41))
      | ~ r2_hidden(X43,X42)
      | r2_hidden(X43,X41) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_33,plain,(
    ! [X44,X45] :
      ( ~ r2_hidden(X44,X45)
      | m1_subset_1(X44,X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_38,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( r2_hidden(k2_relat_1(X1),k1_zfmisc_1(X2))
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( v5_relat_1(esk10_0,k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_37])).

cnf(c_0_45,plain,
    ( X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X3,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(k2_relat_1(esk10_0),k1_zfmisc_1(k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])])).

fof(c_0_48,plain,(
    ! [X48,X49,X50,X52,X53,X54,X56] :
      ( ( r2_hidden(esk4_3(X48,X49,X50),k1_relat_1(X48))
        | ~ r2_hidden(X50,X49)
        | X49 != k2_relat_1(X48)
        | ~ v1_relat_1(X48)
        | ~ v1_funct_1(X48) )
      & ( X50 = k1_funct_1(X48,esk4_3(X48,X49,X50))
        | ~ r2_hidden(X50,X49)
        | X49 != k2_relat_1(X48)
        | ~ v1_relat_1(X48)
        | ~ v1_funct_1(X48) )
      & ( ~ r2_hidden(X53,k1_relat_1(X48))
        | X52 != k1_funct_1(X48,X53)
        | r2_hidden(X52,X49)
        | X49 != k2_relat_1(X48)
        | ~ v1_relat_1(X48)
        | ~ v1_funct_1(X48) )
      & ( ~ r2_hidden(esk5_2(X48,X54),X54)
        | ~ r2_hidden(X56,k1_relat_1(X48))
        | esk5_2(X48,X54) != k1_funct_1(X48,X56)
        | X54 = k2_relat_1(X48)
        | ~ v1_relat_1(X48)
        | ~ v1_funct_1(X48) )
      & ( r2_hidden(esk6_2(X48,X54),k1_relat_1(X48))
        | r2_hidden(esk5_2(X48,X54),X54)
        | X54 = k2_relat_1(X48)
        | ~ v1_relat_1(X48)
        | ~ v1_funct_1(X48) )
      & ( esk5_2(X48,X54) = k1_funct_1(X48,esk6_2(X48,X54))
        | r2_hidden(esk5_2(X48,X54),X54)
        | X54 = k2_relat_1(X48)
        | ~ v1_relat_1(X48)
        | ~ v1_funct_1(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_49,plain,(
    ! [X66,X67,X68] :
      ( ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67)))
      | k1_relset_1(X66,X67,X68) = k1_relat_1(X68) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_50,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(X1,k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))
    | ~ r2_hidden(X1,k2_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_53,plain,(
    ! [X69,X70,X71] :
      ( ( ~ v1_funct_2(X71,X69,X70)
        | X69 = k1_relset_1(X69,X70,X71)
        | X70 = k1_xboole_0
        | ~ m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X69,X70))) )
      & ( X69 != k1_relset_1(X69,X70,X71)
        | v1_funct_2(X71,X69,X70)
        | X70 = k1_xboole_0
        | ~ m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X69,X70))) )
      & ( ~ v1_funct_2(X71,X69,X70)
        | X69 = k1_relset_1(X69,X70,X71)
        | X69 != k1_xboole_0
        | ~ m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X69,X70))) )
      & ( X69 != k1_relset_1(X69,X70,X71)
        | v1_funct_2(X71,X69,X70)
        | X69 != k1_xboole_0
        | ~ m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X69,X70))) )
      & ( ~ v1_funct_2(X71,X69,X70)
        | X71 = k1_xboole_0
        | X69 = k1_xboole_0
        | X70 != k1_xboole_0
        | ~ m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X69,X70))) )
      & ( X71 != k1_xboole_0
        | v1_funct_2(X71,X69,X70)
        | X69 = k1_xboole_0
        | X70 != k1_xboole_0
        | ~ m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X69,X70))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_54,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( v1_funct_2(esk10_0,esk7_0,k1_tarski(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_56,negated_conjecture,
    ( X1 = esk8_0
    | ~ r2_hidden(X1,k2_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_57,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_52])])).

cnf(c_0_58,negated_conjecture,
    ( v1_funct_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_59,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( k1_relset_1(esk7_0,k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0),esk10_0) = k1_relat_1(esk10_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_37])).

cnf(c_0_61,negated_conjecture,
    ( v1_funct_2(esk10_0,esk7_0,k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_27]),c_0_28]),c_0_29])).

fof(c_0_62,plain,(
    ! [X28,X29,X30,X31,X32,X33,X34,X35,X36,X37,X38,X39] :
      ( ( ~ r2_hidden(X33,X32)
        | X33 = X28
        | X33 = X29
        | X33 = X30
        | X33 = X31
        | X32 != k2_enumset1(X28,X29,X30,X31) )
      & ( X34 != X28
        | r2_hidden(X34,X32)
        | X32 != k2_enumset1(X28,X29,X30,X31) )
      & ( X34 != X29
        | r2_hidden(X34,X32)
        | X32 != k2_enumset1(X28,X29,X30,X31) )
      & ( X34 != X30
        | r2_hidden(X34,X32)
        | X32 != k2_enumset1(X28,X29,X30,X31) )
      & ( X34 != X31
        | r2_hidden(X34,X32)
        | X32 != k2_enumset1(X28,X29,X30,X31) )
      & ( esk3_5(X35,X36,X37,X38,X39) != X35
        | ~ r2_hidden(esk3_5(X35,X36,X37,X38,X39),X39)
        | X39 = k2_enumset1(X35,X36,X37,X38) )
      & ( esk3_5(X35,X36,X37,X38,X39) != X36
        | ~ r2_hidden(esk3_5(X35,X36,X37,X38,X39),X39)
        | X39 = k2_enumset1(X35,X36,X37,X38) )
      & ( esk3_5(X35,X36,X37,X38,X39) != X37
        | ~ r2_hidden(esk3_5(X35,X36,X37,X38,X39),X39)
        | X39 = k2_enumset1(X35,X36,X37,X38) )
      & ( esk3_5(X35,X36,X37,X38,X39) != X38
        | ~ r2_hidden(esk3_5(X35,X36,X37,X38,X39),X39)
        | X39 = k2_enumset1(X35,X36,X37,X38) )
      & ( r2_hidden(esk3_5(X35,X36,X37,X38,X39),X39)
        | esk3_5(X35,X36,X37,X38,X39) = X35
        | esk3_5(X35,X36,X37,X38,X39) = X36
        | esk3_5(X35,X36,X37,X38,X39) = X37
        | esk3_5(X35,X36,X37,X38,X39) = X38
        | X39 = k2_enumset1(X35,X36,X37,X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_enumset1])])])])])])).

cnf(c_0_63,negated_conjecture,
    ( k1_funct_1(esk10_0,X1) = esk8_0
    | ~ r2_hidden(X1,k1_relat_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58]),c_0_44])])).

cnf(c_0_64,negated_conjecture,
    ( k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0) = k1_xboole_0
    | k1_relat_1(esk10_0) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_37]),c_0_60]),c_0_61])])).

fof(c_0_65,plain,(
    ! [X58,X59] :
      ( ~ r2_hidden(X58,X59)
      | ~ r1_tarski(X59,X58) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_66,plain,(
    ! [X7] : r1_tarski(k1_xboole_0,X7) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_68,negated_conjecture,
    ( k1_funct_1(esk10_0,esk9_0) != esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_69,negated_conjecture,
    ( k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0) = k1_xboole_0
    | k1_funct_1(esk10_0,X1) = esk8_0
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk9_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_71,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_72,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_73,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X2,X3,X4)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_67])])).

cnf(c_0_74,negated_conjecture,
    ( k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70])])).

cnf(c_0_75,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_76,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:12:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.19/0.41  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.049 s
% 0.19/0.41  
% 0.19/0.41  # Proof found!
% 0.19/0.41  # SZS status Theorem
% 0.19/0.41  # SZS output start CNFRefutation
% 0.19/0.41  fof(t65_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>(r2_hidden(X3,X1)=>k1_funct_1(X4,X3)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 0.19/0.41  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.19/0.41  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.41  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.41  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.41  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.19/0.41  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.41  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.41  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.19/0.41  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.19/0.41  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.19/0.41  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 0.19/0.41  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.19/0.41  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.19/0.41  fof(d2_enumset1, axiom, ![X1, X2, X3, X4, X5]:(X5=k2_enumset1(X1,X2,X3,X4)<=>![X6]:(r2_hidden(X6,X5)<=>~((((X6!=X1&X6!=X2)&X6!=X3)&X6!=X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_enumset1)).
% 0.19/0.41  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.19/0.41  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.41  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>(r2_hidden(X3,X1)=>k1_funct_1(X4,X3)=X2))), inference(assume_negation,[status(cth)],[t65_funct_2])).
% 0.19/0.41  fof(c_0_18, plain, ![X21, X22, X23, X24, X25, X26]:(((~r2_hidden(X23,X22)|r1_tarski(X23,X21)|X22!=k1_zfmisc_1(X21))&(~r1_tarski(X24,X21)|r2_hidden(X24,X22)|X22!=k1_zfmisc_1(X21)))&((~r2_hidden(esk2_2(X25,X26),X26)|~r1_tarski(esk2_2(X25,X26),X25)|X26=k1_zfmisc_1(X25))&(r2_hidden(esk2_2(X25,X26),X26)|r1_tarski(esk2_2(X25,X26),X25)|X26=k1_zfmisc_1(X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.19/0.41  fof(c_0_19, negated_conjecture, (((v1_funct_1(esk10_0)&v1_funct_2(esk10_0,esk7_0,k1_tarski(esk8_0)))&m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,k1_tarski(esk8_0)))))&(r2_hidden(esk9_0,esk7_0)&k1_funct_1(esk10_0,esk9_0)!=esk8_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.19/0.41  fof(c_0_20, plain, ![X15]:k2_tarski(X15,X15)=k1_tarski(X15), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.41  fof(c_0_21, plain, ![X16, X17]:k1_enumset1(X16,X16,X17)=k2_tarski(X16,X17), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.41  fof(c_0_22, plain, ![X18, X19, X20]:k2_enumset1(X18,X18,X19,X20)=k1_enumset1(X18,X19,X20), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.41  cnf(c_0_23, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  fof(c_0_24, plain, ![X46, X47]:((~v5_relat_1(X47,X46)|r1_tarski(k2_relat_1(X47),X46)|~v1_relat_1(X47))&(~r1_tarski(k2_relat_1(X47),X46)|v5_relat_1(X47,X46)|~v1_relat_1(X47))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.19/0.41  fof(c_0_25, plain, ![X63, X64, X65]:((v4_relat_1(X65,X63)|~m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))))&(v5_relat_1(X65,X64)|~m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.41  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,k1_tarski(esk8_0))))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_27, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.41  cnf(c_0_28, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.41  cnf(c_0_29, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.41  fof(c_0_30, plain, ![X60, X61, X62]:(~m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))|v1_relat_1(X62)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.41  fof(c_0_31, plain, ![X8, X9, X10, X11, X12, X13]:(((~r2_hidden(X10,X9)|X10=X8|X9!=k1_tarski(X8))&(X11!=X8|r2_hidden(X11,X9)|X9!=k1_tarski(X8)))&((~r2_hidden(esk1_2(X12,X13),X13)|esk1_2(X12,X13)!=X12|X13=k1_tarski(X12))&(r2_hidden(esk1_2(X12,X13),X13)|esk1_2(X12,X13)=X12|X13=k1_tarski(X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.19/0.41  fof(c_0_32, plain, ![X41, X42, X43]:(~m1_subset_1(X42,k1_zfmisc_1(X41))|(~r2_hidden(X43,X42)|r2_hidden(X43,X41))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.19/0.41  fof(c_0_33, plain, ![X44, X45]:(~r2_hidden(X44,X45)|m1_subset_1(X44,X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.19/0.41  cnf(c_0_34, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_23])).
% 0.19/0.41  cnf(c_0_35, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.41  cnf(c_0_36, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.41  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])).
% 0.19/0.41  cnf(c_0_38, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.41  cnf(c_0_39, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.41  cnf(c_0_40, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.41  cnf(c_0_41, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.41  cnf(c_0_42, plain, (r2_hidden(k2_relat_1(X1),k1_zfmisc_1(X2))|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.41  cnf(c_0_43, negated_conjecture, (v5_relat_1(esk10_0,k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.41  cnf(c_0_44, negated_conjecture, (v1_relat_1(esk10_0)), inference(spm,[status(thm)],[c_0_38, c_0_37])).
% 0.19/0.41  cnf(c_0_45, plain, (X1=X3|X2!=k2_enumset1(X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_27]), c_0_28]), c_0_29])).
% 0.19/0.41  cnf(c_0_46, plain, (r2_hidden(X1,X2)|~r2_hidden(X3,k1_zfmisc_1(X2))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.41  cnf(c_0_47, negated_conjecture, (r2_hidden(k2_relat_1(esk10_0),k1_zfmisc_1(k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])])).
% 0.19/0.41  fof(c_0_48, plain, ![X48, X49, X50, X52, X53, X54, X56]:((((r2_hidden(esk4_3(X48,X49,X50),k1_relat_1(X48))|~r2_hidden(X50,X49)|X49!=k2_relat_1(X48)|(~v1_relat_1(X48)|~v1_funct_1(X48)))&(X50=k1_funct_1(X48,esk4_3(X48,X49,X50))|~r2_hidden(X50,X49)|X49!=k2_relat_1(X48)|(~v1_relat_1(X48)|~v1_funct_1(X48))))&(~r2_hidden(X53,k1_relat_1(X48))|X52!=k1_funct_1(X48,X53)|r2_hidden(X52,X49)|X49!=k2_relat_1(X48)|(~v1_relat_1(X48)|~v1_funct_1(X48))))&((~r2_hidden(esk5_2(X48,X54),X54)|(~r2_hidden(X56,k1_relat_1(X48))|esk5_2(X48,X54)!=k1_funct_1(X48,X56))|X54=k2_relat_1(X48)|(~v1_relat_1(X48)|~v1_funct_1(X48)))&((r2_hidden(esk6_2(X48,X54),k1_relat_1(X48))|r2_hidden(esk5_2(X48,X54),X54)|X54=k2_relat_1(X48)|(~v1_relat_1(X48)|~v1_funct_1(X48)))&(esk5_2(X48,X54)=k1_funct_1(X48,esk6_2(X48,X54))|r2_hidden(esk5_2(X48,X54),X54)|X54=k2_relat_1(X48)|(~v1_relat_1(X48)|~v1_funct_1(X48)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.19/0.41  fof(c_0_49, plain, ![X66, X67, X68]:(~m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67)))|k1_relset_1(X66,X67,X68)=k1_relat_1(X68)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.19/0.41  cnf(c_0_50, plain, (X1=X2|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_45])).
% 0.19/0.41  cnf(c_0_51, negated_conjecture, (r2_hidden(X1,k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))|~r2_hidden(X1,k2_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.19/0.41  cnf(c_0_52, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.41  fof(c_0_53, plain, ![X69, X70, X71]:((((~v1_funct_2(X71,X69,X70)|X69=k1_relset_1(X69,X70,X71)|X70=k1_xboole_0|~m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X69,X70))))&(X69!=k1_relset_1(X69,X70,X71)|v1_funct_2(X71,X69,X70)|X70=k1_xboole_0|~m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X69,X70)))))&((~v1_funct_2(X71,X69,X70)|X69=k1_relset_1(X69,X70,X71)|X69!=k1_xboole_0|~m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X69,X70))))&(X69!=k1_relset_1(X69,X70,X71)|v1_funct_2(X71,X69,X70)|X69!=k1_xboole_0|~m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X69,X70))))))&((~v1_funct_2(X71,X69,X70)|X71=k1_xboole_0|X69=k1_xboole_0|X70!=k1_xboole_0|~m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X69,X70))))&(X71!=k1_xboole_0|v1_funct_2(X71,X69,X70)|X69=k1_xboole_0|X70!=k1_xboole_0|~m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X69,X70)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.19/0.41  cnf(c_0_54, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.41  cnf(c_0_55, negated_conjecture, (v1_funct_2(esk10_0,esk7_0,k1_tarski(esk8_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_56, negated_conjecture, (X1=esk8_0|~r2_hidden(X1,k2_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.19/0.41  cnf(c_0_57, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_52])])).
% 0.19/0.41  cnf(c_0_58, negated_conjecture, (v1_funct_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_59, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.41  cnf(c_0_60, negated_conjecture, (k1_relset_1(esk7_0,k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0),esk10_0)=k1_relat_1(esk10_0)), inference(spm,[status(thm)],[c_0_54, c_0_37])).
% 0.19/0.41  cnf(c_0_61, negated_conjecture, (v1_funct_2(esk10_0,esk7_0,k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_27]), c_0_28]), c_0_29])).
% 0.19/0.41  fof(c_0_62, plain, ![X28, X29, X30, X31, X32, X33, X34, X35, X36, X37, X38, X39]:(((~r2_hidden(X33,X32)|(X33=X28|X33=X29|X33=X30|X33=X31)|X32!=k2_enumset1(X28,X29,X30,X31))&((((X34!=X28|r2_hidden(X34,X32)|X32!=k2_enumset1(X28,X29,X30,X31))&(X34!=X29|r2_hidden(X34,X32)|X32!=k2_enumset1(X28,X29,X30,X31)))&(X34!=X30|r2_hidden(X34,X32)|X32!=k2_enumset1(X28,X29,X30,X31)))&(X34!=X31|r2_hidden(X34,X32)|X32!=k2_enumset1(X28,X29,X30,X31))))&(((((esk3_5(X35,X36,X37,X38,X39)!=X35|~r2_hidden(esk3_5(X35,X36,X37,X38,X39),X39)|X39=k2_enumset1(X35,X36,X37,X38))&(esk3_5(X35,X36,X37,X38,X39)!=X36|~r2_hidden(esk3_5(X35,X36,X37,X38,X39),X39)|X39=k2_enumset1(X35,X36,X37,X38)))&(esk3_5(X35,X36,X37,X38,X39)!=X37|~r2_hidden(esk3_5(X35,X36,X37,X38,X39),X39)|X39=k2_enumset1(X35,X36,X37,X38)))&(esk3_5(X35,X36,X37,X38,X39)!=X38|~r2_hidden(esk3_5(X35,X36,X37,X38,X39),X39)|X39=k2_enumset1(X35,X36,X37,X38)))&(r2_hidden(esk3_5(X35,X36,X37,X38,X39),X39)|(esk3_5(X35,X36,X37,X38,X39)=X35|esk3_5(X35,X36,X37,X38,X39)=X36|esk3_5(X35,X36,X37,X38,X39)=X37|esk3_5(X35,X36,X37,X38,X39)=X38)|X39=k2_enumset1(X35,X36,X37,X38)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_enumset1])])])])])])).
% 0.19/0.41  cnf(c_0_63, negated_conjecture, (k1_funct_1(esk10_0,X1)=esk8_0|~r2_hidden(X1,k1_relat_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58]), c_0_44])])).
% 0.19/0.41  cnf(c_0_64, negated_conjecture, (k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)=k1_xboole_0|k1_relat_1(esk10_0)=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_37]), c_0_60]), c_0_61])])).
% 0.19/0.41  fof(c_0_65, plain, ![X58, X59]:(~r2_hidden(X58,X59)|~r1_tarski(X59,X58)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.19/0.41  fof(c_0_66, plain, ![X7]:r1_tarski(k1_xboole_0,X7), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.41  cnf(c_0_67, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.19/0.41  cnf(c_0_68, negated_conjecture, (k1_funct_1(esk10_0,esk9_0)!=esk8_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_69, negated_conjecture, (k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)=k1_xboole_0|k1_funct_1(esk10_0,X1)=esk8_0|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.19/0.41  cnf(c_0_70, negated_conjecture, (r2_hidden(esk9_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_71, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.19/0.41  cnf(c_0_72, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.19/0.41  cnf(c_0_73, plain, (r2_hidden(X1,k2_enumset1(X1,X2,X3,X4))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_67])])).
% 0.19/0.41  cnf(c_0_74, negated_conjecture, (k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70])])).
% 0.19/0.41  cnf(c_0_75, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.19/0.41  cnf(c_0_76, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 77
% 0.19/0.41  # Proof object clause steps            : 42
% 0.19/0.41  # Proof object formula steps           : 35
% 0.19/0.41  # Proof object conjectures             : 21
% 0.19/0.41  # Proof object clause conjectures      : 18
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 21
% 0.19/0.41  # Proof object initial formulas used   : 17
% 0.19/0.41  # Proof object generating inferences   : 14
% 0.19/0.41  # Proof object simplifying inferences  : 26
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 17
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 48
% 0.19/0.41  # Removed in clause preprocessing      : 3
% 0.19/0.41  # Initial clauses in saturation        : 45
% 0.19/0.41  # Processed clauses                    : 180
% 0.19/0.41  # ...of these trivial                  : 0
% 0.19/0.41  # ...subsumed                          : 23
% 0.19/0.41  # ...remaining for further processing  : 157
% 0.19/0.41  # Other redundant clauses eliminated   : 17
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 0
% 0.19/0.41  # Backward-rewritten                   : 10
% 0.19/0.41  # Generated clauses                    : 307
% 0.19/0.41  # ...of the previous two non-trivial   : 303
% 0.19/0.41  # Contextual simplify-reflections      : 0
% 0.19/0.41  # Paramodulations                      : 294
% 0.19/0.41  # Factorizations                       : 2
% 0.19/0.41  # Equation resolutions                 : 17
% 0.19/0.41  # Propositional unsat checks           : 0
% 0.19/0.41  #    Propositional check models        : 0
% 0.19/0.41  #    Propositional check unsatisfiable : 0
% 0.19/0.41  #    Propositional clauses             : 0
% 0.19/0.41  #    Propositional clauses after purity: 0
% 0.19/0.41  #    Propositional unsat core size     : 0
% 0.19/0.41  #    Propositional preprocessing time  : 0.000
% 0.19/0.41  #    Propositional encoding time       : 0.000
% 0.19/0.41  #    Propositional solver time         : 0.000
% 0.19/0.41  #    Success case prop preproc time    : 0.000
% 0.19/0.41  #    Success case prop encoding time   : 0.000
% 0.19/0.41  #    Success case prop solver time     : 0.000
% 0.19/0.41  # Current number of processed clauses  : 136
% 0.19/0.41  #    Positive orientable unit clauses  : 62
% 0.19/0.41  #    Positive unorientable unit clauses: 0
% 0.19/0.41  #    Negative unit clauses             : 13
% 0.19/0.41  #    Non-unit-clauses                  : 61
% 0.19/0.41  # Current number of unprocessed clauses: 160
% 0.19/0.41  # ...number of literals in the above   : 448
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 13
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 468
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 211
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 7
% 0.19/0.41  # Unit Clause-clause subsumption calls : 269
% 0.19/0.41  # Rewrite failures with RHS unbound    : 0
% 0.19/0.41  # BW rewrite match attempts            : 231
% 0.19/0.41  # BW rewrite match successes           : 1
% 0.19/0.41  # Condensation attempts                : 0
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 7545
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.064 s
% 0.19/0.41  # System time              : 0.007 s
% 0.19/0.41  # Total time               : 0.071 s
% 0.19/0.41  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
