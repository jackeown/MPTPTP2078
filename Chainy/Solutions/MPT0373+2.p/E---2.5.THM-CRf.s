%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0373+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:44 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   67 (  96 expanded)
%              Number of clauses        :   32 (  39 expanded)
%              Number of leaves         :   17 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :  129 ( 204 expanded)
%              Number of equality atoms :   31 (  55 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t55_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,X1)
     => ( X1 != k1_xboole_0
       => m1_subset_1(k1_tarski(X2),k1_zfmisc_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t75_enumset1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t7_boole)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d3_tarski)).

fof(t79_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT004+2.ax',t79_zfmisc_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT004+2.ax',t38_zfmisc_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',l13_xboole_0)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,X1)
       => ( X1 != k1_xboole_0
         => m1_subset_1(k1_tarski(X2),k1_zfmisc_1(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t55_subset_1])).

fof(c_0_18,plain,(
    ! [X1490] : m1_subset_1(k2_subset_1(X1490),k1_zfmisc_1(X1490)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_19,plain,(
    ! [X1486] : k2_subset_1(X1486) = X1486 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_20,negated_conjecture,
    ( m1_subset_1(esk74_0,esk73_0)
    & esk73_0 != k1_xboole_0
    & ~ m1_subset_1(k1_tarski(esk74_0),k1_zfmisc_1(esk73_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_21,plain,(
    ! [X891] : k2_tarski(X891,X891) = k1_tarski(X891) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_22,plain,(
    ! [X892,X893] : k1_enumset1(X892,X892,X893) = k2_tarski(X892,X893) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_23,plain,(
    ! [X894,X895,X896] : k2_enumset1(X894,X894,X895,X896) = k1_enumset1(X894,X895,X896) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_24,plain,(
    ! [X897,X898,X899,X900] : k3_enumset1(X897,X897,X898,X899,X900) = k2_enumset1(X897,X898,X899,X900) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_25,plain,(
    ! [X901,X902,X903,X904,X905] : k4_enumset1(X901,X901,X902,X903,X904,X905) = k3_enumset1(X901,X902,X903,X904,X905) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_26,plain,(
    ! [X906,X907,X908,X909,X910,X911] : k5_enumset1(X906,X906,X907,X908,X909,X910,X911) = k4_enumset1(X906,X907,X908,X909,X910,X911) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_27,plain,(
    ! [X912,X913,X914,X915,X916,X917,X918] : k6_enumset1(X912,X912,X913,X914,X915,X916,X917,X918) = k5_enumset1(X912,X913,X914,X915,X916,X917,X918) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_28,plain,(
    ! [X1483,X1484] :
      ( ( ~ m1_subset_1(X1484,X1483)
        | r2_hidden(X1484,X1483)
        | v1_xboole_0(X1483) )
      & ( ~ r2_hidden(X1484,X1483)
        | m1_subset_1(X1484,X1483)
        | v1_xboole_0(X1483) )
      & ( ~ m1_subset_1(X1484,X1483)
        | v1_xboole_0(X1484)
        | ~ v1_xboole_0(X1483) )
      & ( ~ v1_xboole_0(X1484)
        | m1_subset_1(X1484,X1483)
        | ~ v1_xboole_0(X1483) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_29,plain,(
    ! [X381,X382] :
      ( ~ r2_hidden(X381,X382)
      | ~ v1_xboole_0(X382) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_30,plain,(
    ! [X27,X28,X29,X30,X31] :
      ( ( ~ r1_tarski(X27,X28)
        | ~ r2_hidden(X29,X27)
        | r2_hidden(X29,X28) )
      & ( r2_hidden(esk2_2(X30,X31),X30)
        | r1_tarski(X30,X31) )
      & ( ~ r2_hidden(esk2_2(X30,X31),X31)
        | r1_tarski(X30,X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_31,plain,(
    ! [X1423,X1424] :
      ( ~ r1_tarski(X1423,X1424)
      | r1_tarski(k1_zfmisc_1(X1423),k1_zfmisc_1(X1424)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).

cnf(c_0_32,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_33,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_34,plain,(
    ! [X1513] : ~ v1_xboole_0(k1_zfmisc_1(X1513)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_35,negated_conjecture,
    ( ~ m1_subset_1(k1_tarski(esk74_0),k1_zfmisc_1(esk73_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_36,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_37,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_38,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_39,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_40,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_41,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_42,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_43,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_45,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_46,plain,
    ( r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_48,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_49,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_50,negated_conjecture,
    ( ~ m1_subset_1(k6_enumset1(esk74_0,esk74_0,esk74_0,esk74_0,esk74_0,esk74_0,esk74_0,esk74_0),k1_zfmisc_1(esk73_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_51,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X3,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

fof(c_0_54,plain,(
    ! [X1330,X1331,X1332] :
      ( ( r2_hidden(X1330,X1332)
        | ~ r1_tarski(k2_tarski(X1330,X1331),X1332) )
      & ( r2_hidden(X1331,X1332)
        | ~ r1_tarski(k2_tarski(X1330,X1331),X1332) )
      & ( ~ r2_hidden(X1330,X1332)
        | ~ r2_hidden(X1331,X1332)
        | r1_tarski(k2_tarski(X1330,X1331),X1332) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

fof(c_0_55,plain,(
    ! [X69] :
      ( ~ v1_xboole_0(X69)
      | X69 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk74_0,esk73_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_57,negated_conjecture,
    ( ~ r2_hidden(k6_enumset1(esk74_0,esk74_0,esk74_0,esk74_0,esk74_0,esk74_0,esk74_0,esk74_0),k1_zfmisc_1(esk73_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_59,plain,
    ( r1_tarski(k2_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_60,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( v1_xboole_0(esk73_0)
    | r2_hidden(esk74_0,esk73_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( esk73_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_63,negated_conjecture,
    ( ~ r1_tarski(k6_enumset1(esk74_0,esk74_0,esk74_0,esk74_0,esk74_0,esk74_0,esk74_0,esk74_0),esk73_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_64,plain,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk74_0,esk73_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])]),
    [proof]).
%------------------------------------------------------------------------------
