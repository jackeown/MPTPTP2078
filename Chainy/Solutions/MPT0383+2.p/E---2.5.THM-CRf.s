%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0383+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:44 EST 2020

% Result     : Theorem 1.08s
% Output     : CNFRefutation 1.08s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 145 expanded)
%              Number of clauses        :   28 (  66 expanded)
%              Number of leaves         :    9 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :  134 ( 477 expanded)
%              Number of equality atoms :   17 (  73 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d3_tarski)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT004+2.ax',l49_zfmisc_1)).

fof(t65_subset_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ~ ( r2_hidden(X4,X3)
        & r1_tarski(X3,k2_zfmisc_1(X1,X2))
        & ! [X5] :
            ( m1_subset_1(X5,X1)
           => ! [X6] :
                ( m1_subset_1(X6,X2)
               => X4 != k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_subset_1)).

fof(t99_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT004+2.ax',t99_zfmisc_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT004+2.ax',d1_zfmisc_1)).

fof(l139_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
        & ! [X4,X5] : k4_tarski(X4,X5) != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT004+2.ax',l139_zfmisc_1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT004+2.ax',l54_zfmisc_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t7_boole)).

fof(c_0_9,plain,(
    ! [X27,X28,X29,X30,X31] :
      ( ( ~ r1_tarski(X27,X28)
        | ~ r2_hidden(X29,X27)
        | r2_hidden(X29,X28) )
      & ( r2_hidden(esk2_2(X30,X31),X30)
        | r1_tarski(X30,X31) )
      & ( ~ r2_hidden(esk2_2(X30,X31),X31)
        | r1_tarski(X30,X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_10,plain,(
    ! [X1085,X1086] :
      ( ~ r2_hidden(X1085,X1086)
      | r1_tarski(X1085,k3_tarski(X1086)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ~ ( r2_hidden(X4,X3)
          & r1_tarski(X3,k2_zfmisc_1(X1,X2))
          & ! [X5] :
              ( m1_subset_1(X5,X1)
             => ! [X6] :
                  ( m1_subset_1(X6,X2)
                 => X4 != k4_tarski(X5,X6) ) ) ) ),
    inference(assume_negation,[status(cth)],[t65_subset_1])).

cnf(c_0_12,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,negated_conjecture,(
    ! [X1816,X1817] :
      ( r2_hidden(esk81_0,esk80_0)
      & r1_tarski(esk80_0,k2_zfmisc_1(esk78_0,esk79_0))
      & ( ~ m1_subset_1(X1816,esk78_0)
        | ~ m1_subset_1(X1817,esk79_0)
        | esk81_0 != k4_tarski(X1816,X1817) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk81_0,esk80_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_17,plain,(
    ! [X1459] : k3_tarski(k1_zfmisc_1(X1459)) = X1459 ),
    inference(variable_rename,[status(thm)],[t99_zfmisc_1])).

fof(c_0_18,plain,(
    ! [X982,X983,X984,X985,X986,X987] :
      ( ( ~ r2_hidden(X984,X983)
        | r1_tarski(X984,X982)
        | X983 != k1_zfmisc_1(X982) )
      & ( ~ r1_tarski(X985,X982)
        | r2_hidden(X985,X983)
        | X983 != k1_zfmisc_1(X982) )
      & ( ~ r2_hidden(esk21_2(X986,X987),X987)
        | ~ r1_tarski(esk21_2(X986,X987),X986)
        | X987 = k1_zfmisc_1(X986) )
      & ( r2_hidden(esk21_2(X986,X987),X987)
        | r1_tarski(esk21_2(X986,X987),X986)
        | X987 = k1_zfmisc_1(X986) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk81_0,k3_tarski(X1))
    | ~ r2_hidden(esk80_0,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk81_0,X1)
    | ~ r2_hidden(esk80_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_21])).

fof(c_0_24,plain,(
    ! [X1045,X1046,X1047] :
      ( ~ r2_hidden(X1045,k2_zfmisc_1(X1046,X1047))
      | k4_tarski(esk36_1(X1045),esk37_1(X1045)) = X1045 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk81_0,X1)
    | ~ r1_tarski(esk80_0,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(esk80_0,k2_zfmisc_1(esk78_0,esk79_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_27,plain,(
    ! [X1089,X1090,X1091,X1092] :
      ( ( r2_hidden(X1089,X1091)
        | ~ r2_hidden(k4_tarski(X1089,X1090),k2_zfmisc_1(X1091,X1092)) )
      & ( r2_hidden(X1090,X1092)
        | ~ r2_hidden(k4_tarski(X1089,X1090),k2_zfmisc_1(X1091,X1092)) )
      & ( ~ r2_hidden(X1089,X1091)
        | ~ r2_hidden(X1090,X1092)
        | r2_hidden(k4_tarski(X1089,X1090),k2_zfmisc_1(X1091,X1092)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_28,plain,
    ( k4_tarski(esk36_1(X1),esk37_1(X1)) = X1
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk81_0,k2_zfmisc_1(esk78_0,esk79_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_30,plain,(
    ! [X1496,X1497] :
      ( ( ~ m1_subset_1(X1497,X1496)
        | r2_hidden(X1497,X1496)
        | v1_xboole_0(X1496) )
      & ( ~ r2_hidden(X1497,X1496)
        | m1_subset_1(X1497,X1496)
        | v1_xboole_0(X1496) )
      & ( ~ m1_subset_1(X1497,X1496)
        | v1_xboole_0(X1497)
        | ~ v1_xboole_0(X1496) )
      & ( ~ v1_xboole_0(X1497)
        | m1_subset_1(X1497,X1496)
        | ~ v1_xboole_0(X1496) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_31,plain,(
    ! [X381,X382] :
      ( ~ r2_hidden(X381,X382)
      | ~ v1_xboole_0(X382) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk78_0,esk79_0))
    | ~ r2_hidden(X1,esk80_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( ~ m1_subset_1(X1,esk78_0)
    | ~ m1_subset_1(X2,esk79_0)
    | esk81_0 != k4_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_35,negated_conjecture,
    ( k4_tarski(esk36_1(esk81_0),esk37_1(esk81_0)) = esk81_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(X1,esk79_0)
    | ~ r2_hidden(k4_tarski(X2,X1),esk80_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,negated_conjecture,
    ( ~ m1_subset_1(esk37_1(esk81_0),esk79_0)
    | ~ m1_subset_1(esk36_1(esk81_0),esk78_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk37_1(esk81_0),esk79_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_35]),c_0_16])])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(X1,esk78_0)
    | ~ r2_hidden(k4_tarski(X1,X2),esk80_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_33])).

cnf(c_0_44,negated_conjecture,
    ( ~ m1_subset_1(esk36_1(esk81_0),esk78_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk36_1(esk81_0),esk78_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_35]),c_0_16])])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_41]),c_0_45])]),
    [proof]).
%------------------------------------------------------------------------------
