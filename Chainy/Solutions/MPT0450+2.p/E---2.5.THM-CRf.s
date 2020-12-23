%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0450+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:45 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 172 expanded)
%              Number of clauses        :   38 (  71 expanded)
%              Number of leaves         :   17 (  49 expanded)
%              Depth                    :    8
%              Number of atoms          :  218 ( 351 expanded)
%              Number of equality atoms :   90 ( 183 expanded)
%              Maximal formula depth    :   47 (   5 average)
%              Maximal clause size      :   68 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t34_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k3_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k3_relat_1(X1),k3_relat_1(X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relat_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT006+2.ax',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t70_enumset1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT004+2.ax',d1_zfmisc_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT006+2.ax',t1_subset)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t75_enumset1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t19_xboole_1)).

fof(t31_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t17_xboole_1)).

fof(fc1_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(t4_setfam_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(k1_setfam_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT006+2.ax',t4_setfam_1)).

fof(d6_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( X9 = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)
    <=> ! [X10] :
          ( r2_hidden(X10,X9)
        <=> ~ ( X10 != X1
              & X10 != X2
              & X10 != X3
              & X10 != X4
              & X10 != X5
              & X10 != X6
              & X10 != X7
              & X10 != X8 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT005+2.ax',d6_enumset1)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => r1_tarski(k3_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k3_relat_1(X1),k3_relat_1(X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t34_relat_1])).

fof(c_0_18,plain,(
    ! [X1971,X1972] : k1_setfam_1(k2_tarski(X1971,X1972)) = k3_xboole_0(X1971,X1972) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_19,plain,(
    ! [X892,X893] : k1_enumset1(X892,X892,X893) = k2_tarski(X892,X893) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_20,plain,(
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

fof(c_0_21,plain,(
    ! [X2089,X2090] :
      ( ~ v1_relat_1(X2089)
      | ~ m1_subset_1(X2090,k1_zfmisc_1(X2089))
      | v1_relat_1(X2090) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_22,plain,(
    ! [X1979,X1980] :
      ( ~ r2_hidden(X1979,X1980)
      | m1_subset_1(X1979,X1980) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

fof(c_0_23,negated_conjecture,
    ( v1_relat_1(esk126_0)
    & v1_relat_1(esk127_0)
    & ~ r1_tarski(k3_relat_1(k3_xboole_0(esk126_0,esk127_0)),k3_xboole_0(k3_relat_1(esk126_0),k3_relat_1(esk127_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

cnf(c_0_24,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,plain,(
    ! [X894,X895,X896] : k2_enumset1(X894,X894,X895,X896) = k1_enumset1(X894,X895,X896) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_27,plain,(
    ! [X897,X898,X899,X900] : k3_enumset1(X897,X897,X898,X899,X900) = k2_enumset1(X897,X898,X899,X900) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_28,plain,(
    ! [X901,X902,X903,X904,X905] : k4_enumset1(X901,X901,X902,X903,X904,X905) = k3_enumset1(X901,X902,X903,X904,X905) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_29,plain,(
    ! [X906,X907,X908,X909,X910,X911] : k5_enumset1(X906,X906,X907,X908,X909,X910,X911) = k4_enumset1(X906,X907,X908,X909,X910,X911) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_30,plain,(
    ! [X912,X913,X914,X915,X916,X917,X918] : k6_enumset1(X912,X912,X913,X914,X915,X916,X917,X918) = k5_enumset1(X912,X913,X914,X915,X916,X917,X918) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_31,plain,(
    ! [X202,X203,X204] :
      ( ~ r1_tarski(X202,X203)
      | ~ r1_tarski(X202,X204)
      | r1_tarski(X202,k3_xboole_0(X203,X204)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

fof(c_0_32,plain,(
    ! [X2171,X2172] :
      ( ~ v1_relat_1(X2171)
      | ~ v1_relat_1(X2172)
      | ~ r1_tarski(X2171,X2172)
      | r1_tarski(k3_relat_1(X2171),k3_relat_1(X2172)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_relat_1])])])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_34,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_36,plain,(
    ! [X197,X198] : r1_tarski(k3_xboole_0(X197,X198),X197) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_37,plain,(
    ! [X2121,X2122] :
      ( ~ v1_relat_1(X2121)
      | v1_relat_1(k3_xboole_0(X2121,X2122)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).

cnf(c_0_38,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(esk126_0,esk127_0)),k3_xboole_0(k3_relat_1(esk126_0),k3_relat_1(esk127_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_39,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_40,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_41,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_42,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_43,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_44,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_46,plain,
    ( r1_tarski(k3_relat_1(X1),k3_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_48,plain,
    ( v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_49,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_50,plain,
    ( v1_relat_1(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_51,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k6_enumset1(esk126_0,esk126_0,esk126_0,esk126_0,esk126_0,esk126_0,esk126_0,esk127_0))),k1_setfam_1(k6_enumset1(k3_relat_1(esk126_0),k3_relat_1(esk126_0),k3_relat_1(esk126_0),k3_relat_1(esk126_0),k3_relat_1(esk126_0),k3_relat_1(esk126_0),k3_relat_1(esk126_0),k3_relat_1(esk127_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_44]),c_0_44])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_53,plain,
    ( r1_tarski(k3_relat_1(X1),k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( v1_relat_1(esk127_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_55,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_56,plain,
    ( v1_relat_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_57,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k6_enumset1(esk126_0,esk126_0,esk126_0,esk126_0,esk126_0,esk126_0,esk126_0,esk127_0))),k3_relat_1(esk127_0))
    | ~ r1_tarski(k3_relat_1(k1_setfam_1(k6_enumset1(esk126_0,esk126_0,esk126_0,esk126_0,esk126_0,esk126_0,esk126_0,esk127_0))),k3_relat_1(esk126_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(k3_relat_1(X1),k3_relat_1(esk127_0))
    | ~ r2_hidden(X1,k1_zfmisc_1(esk127_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_59,plain,
    ( r1_tarski(k3_relat_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))),k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_55]),c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( v1_relat_1(esk126_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_62,plain,(
    ! [X2030,X2031] :
      ( ~ r2_hidden(X2030,X2031)
      | r1_tarski(k1_setfam_1(X2031),X2030) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).

fof(c_0_63,plain,(
    ! [X1553,X1554,X1555,X1556,X1557,X1558,X1559,X1560,X1561,X1562,X1563,X1564,X1565,X1566,X1567,X1568,X1569,X1570,X1571,X1572] :
      ( ( ~ r2_hidden(X1562,X1561)
        | X1562 = X1553
        | X1562 = X1554
        | X1562 = X1555
        | X1562 = X1556
        | X1562 = X1557
        | X1562 = X1558
        | X1562 = X1559
        | X1562 = X1560
        | X1561 != k6_enumset1(X1553,X1554,X1555,X1556,X1557,X1558,X1559,X1560) )
      & ( X1563 != X1553
        | r2_hidden(X1563,X1561)
        | X1561 != k6_enumset1(X1553,X1554,X1555,X1556,X1557,X1558,X1559,X1560) )
      & ( X1563 != X1554
        | r2_hidden(X1563,X1561)
        | X1561 != k6_enumset1(X1553,X1554,X1555,X1556,X1557,X1558,X1559,X1560) )
      & ( X1563 != X1555
        | r2_hidden(X1563,X1561)
        | X1561 != k6_enumset1(X1553,X1554,X1555,X1556,X1557,X1558,X1559,X1560) )
      & ( X1563 != X1556
        | r2_hidden(X1563,X1561)
        | X1561 != k6_enumset1(X1553,X1554,X1555,X1556,X1557,X1558,X1559,X1560) )
      & ( X1563 != X1557
        | r2_hidden(X1563,X1561)
        | X1561 != k6_enumset1(X1553,X1554,X1555,X1556,X1557,X1558,X1559,X1560) )
      & ( X1563 != X1558
        | r2_hidden(X1563,X1561)
        | X1561 != k6_enumset1(X1553,X1554,X1555,X1556,X1557,X1558,X1559,X1560) )
      & ( X1563 != X1559
        | r2_hidden(X1563,X1561)
        | X1561 != k6_enumset1(X1553,X1554,X1555,X1556,X1557,X1558,X1559,X1560) )
      & ( X1563 != X1560
        | r2_hidden(X1563,X1561)
        | X1561 != k6_enumset1(X1553,X1554,X1555,X1556,X1557,X1558,X1559,X1560) )
      & ( esk64_9(X1564,X1565,X1566,X1567,X1568,X1569,X1570,X1571,X1572) != X1564
        | ~ r2_hidden(esk64_9(X1564,X1565,X1566,X1567,X1568,X1569,X1570,X1571,X1572),X1572)
        | X1572 = k6_enumset1(X1564,X1565,X1566,X1567,X1568,X1569,X1570,X1571) )
      & ( esk64_9(X1564,X1565,X1566,X1567,X1568,X1569,X1570,X1571,X1572) != X1565
        | ~ r2_hidden(esk64_9(X1564,X1565,X1566,X1567,X1568,X1569,X1570,X1571,X1572),X1572)
        | X1572 = k6_enumset1(X1564,X1565,X1566,X1567,X1568,X1569,X1570,X1571) )
      & ( esk64_9(X1564,X1565,X1566,X1567,X1568,X1569,X1570,X1571,X1572) != X1566
        | ~ r2_hidden(esk64_9(X1564,X1565,X1566,X1567,X1568,X1569,X1570,X1571,X1572),X1572)
        | X1572 = k6_enumset1(X1564,X1565,X1566,X1567,X1568,X1569,X1570,X1571) )
      & ( esk64_9(X1564,X1565,X1566,X1567,X1568,X1569,X1570,X1571,X1572) != X1567
        | ~ r2_hidden(esk64_9(X1564,X1565,X1566,X1567,X1568,X1569,X1570,X1571,X1572),X1572)
        | X1572 = k6_enumset1(X1564,X1565,X1566,X1567,X1568,X1569,X1570,X1571) )
      & ( esk64_9(X1564,X1565,X1566,X1567,X1568,X1569,X1570,X1571,X1572) != X1568
        | ~ r2_hidden(esk64_9(X1564,X1565,X1566,X1567,X1568,X1569,X1570,X1571,X1572),X1572)
        | X1572 = k6_enumset1(X1564,X1565,X1566,X1567,X1568,X1569,X1570,X1571) )
      & ( esk64_9(X1564,X1565,X1566,X1567,X1568,X1569,X1570,X1571,X1572) != X1569
        | ~ r2_hidden(esk64_9(X1564,X1565,X1566,X1567,X1568,X1569,X1570,X1571,X1572),X1572)
        | X1572 = k6_enumset1(X1564,X1565,X1566,X1567,X1568,X1569,X1570,X1571) )
      & ( esk64_9(X1564,X1565,X1566,X1567,X1568,X1569,X1570,X1571,X1572) != X1570
        | ~ r2_hidden(esk64_9(X1564,X1565,X1566,X1567,X1568,X1569,X1570,X1571,X1572),X1572)
        | X1572 = k6_enumset1(X1564,X1565,X1566,X1567,X1568,X1569,X1570,X1571) )
      & ( esk64_9(X1564,X1565,X1566,X1567,X1568,X1569,X1570,X1571,X1572) != X1571
        | ~ r2_hidden(esk64_9(X1564,X1565,X1566,X1567,X1568,X1569,X1570,X1571,X1572),X1572)
        | X1572 = k6_enumset1(X1564,X1565,X1566,X1567,X1568,X1569,X1570,X1571) )
      & ( r2_hidden(esk64_9(X1564,X1565,X1566,X1567,X1568,X1569,X1570,X1571,X1572),X1572)
        | esk64_9(X1564,X1565,X1566,X1567,X1568,X1569,X1570,X1571,X1572) = X1564
        | esk64_9(X1564,X1565,X1566,X1567,X1568,X1569,X1570,X1571,X1572) = X1565
        | esk64_9(X1564,X1565,X1566,X1567,X1568,X1569,X1570,X1571,X1572) = X1566
        | esk64_9(X1564,X1565,X1566,X1567,X1568,X1569,X1570,X1571,X1572) = X1567
        | esk64_9(X1564,X1565,X1566,X1567,X1568,X1569,X1570,X1571,X1572) = X1568
        | esk64_9(X1564,X1565,X1566,X1567,X1568,X1569,X1570,X1571,X1572) = X1569
        | esk64_9(X1564,X1565,X1566,X1567,X1568,X1569,X1570,X1571,X1572) = X1570
        | esk64_9(X1564,X1565,X1566,X1567,X1568,X1569,X1570,X1571,X1572) = X1571
        | X1572 = k6_enumset1(X1564,X1565,X1566,X1567,X1568,X1569,X1570,X1571) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).

cnf(c_0_64,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k6_enumset1(esk126_0,esk126_0,esk126_0,esk126_0,esk126_0,esk126_0,esk126_0,esk127_0))),k3_relat_1(esk126_0))
    | ~ r2_hidden(k1_setfam_1(k6_enumset1(esk126_0,esk126_0,esk126_0,esk126_0,esk126_0,esk126_0,esk126_0,esk127_0)),k1_zfmisc_1(esk127_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(k3_relat_1(k1_setfam_1(k6_enumset1(esk126_0,esk126_0,esk126_0,esk126_0,esk126_0,esk126_0,esk126_0,X1))),k3_relat_1(esk126_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_61])).

cnf(c_0_67,plain,
    ( r1_tarski(k1_setfam_1(X2),X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X5,X6,X7,X8,X9,X10,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( ~ r2_hidden(k1_setfam_1(k6_enumset1(esk126_0,esk126_0,esk126_0,esk126_0,esk126_0,esk126_0,esk126_0,esk127_0)),k1_zfmisc_1(esk127_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_65])])).

cnf(c_0_70,plain,
    ( r2_hidden(k1_setfam_1(X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_71,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_68])])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])]),
    [proof]).
%------------------------------------------------------------------------------
