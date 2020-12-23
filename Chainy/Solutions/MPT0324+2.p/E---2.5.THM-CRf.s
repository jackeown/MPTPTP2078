%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0324+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:43 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 200 expanded)
%              Number of clauses        :   24 (  79 expanded)
%              Number of leaves         :   12 (  59 expanded)
%              Depth                    :    8
%              Number of atoms          :   85 ( 248 expanded)
%              Number of equality atoms :   43 ( 188 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t70_enumset1)).

fof(t137_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4,X5] :
      ( ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
        & r2_hidden(X1,k2_zfmisc_1(X4,X5)) )
     => r2_hidden(X1,k2_zfmisc_1(k3_xboole_0(X2,X4),k3_xboole_0(X3,X5))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_zfmisc_1)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t95_xboole_1)).

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

fof(t123_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t91_xboole_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d4_xboole_0)).

fof(c_0_12,plain,(
    ! [X1078,X1079] : k3_tarski(k2_tarski(X1078,X1079)) = k2_xboole_0(X1078,X1079) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_13,plain,(
    ! [X892,X893] : k1_enumset1(X892,X892,X893) = k2_tarski(X892,X893) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] :
        ( ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
          & r2_hidden(X1,k2_zfmisc_1(X4,X5)) )
       => r2_hidden(X1,k2_zfmisc_1(k3_xboole_0(X2,X4),k3_xboole_0(X3,X5))) ) ),
    inference(assume_negation,[status(cth)],[t137_zfmisc_1])).

fof(c_0_15,plain,(
    ! [X426,X427] : k3_xboole_0(X426,X427) = k5_xboole_0(k5_xboole_0(X426,X427),k2_xboole_0(X426,X427)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

cnf(c_0_16,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X894,X895,X896] : k2_enumset1(X894,X894,X895,X896) = k1_enumset1(X894,X895,X896) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_19,plain,(
    ! [X897,X898,X899,X900] : k3_enumset1(X897,X897,X898,X899,X900) = k2_enumset1(X897,X898,X899,X900) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_20,negated_conjecture,
    ( r2_hidden(esk51_0,k2_zfmisc_1(esk52_0,esk53_0))
    & r2_hidden(esk51_0,k2_zfmisc_1(esk54_0,esk55_0))
    & ~ r2_hidden(esk51_0,k2_zfmisc_1(k3_xboole_0(esk52_0,esk54_0),k3_xboole_0(esk53_0,esk55_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

cnf(c_0_21,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

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
    ! [X1157,X1158,X1159,X1160] : k2_zfmisc_1(k3_xboole_0(X1157,X1158),k3_xboole_0(X1159,X1160)) = k3_xboole_0(k2_zfmisc_1(X1157,X1159),k2_zfmisc_1(X1158,X1160)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

cnf(c_0_29,negated_conjecture,
    ( ~ r2_hidden(esk51_0,k2_zfmisc_1(k3_xboole_0(esk52_0,esk54_0),k3_xboole_0(esk53_0,esk55_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24])).

cnf(c_0_31,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_34,plain,(
    ! [X418,X419,X420] : k5_xboole_0(k5_xboole_0(X418,X419),X420) = k5_xboole_0(X418,k5_xboole_0(X419,X420)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_35,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_36,plain,(
    ! [X42,X43,X44,X45,X46,X47,X48,X49] :
      ( ( r2_hidden(X45,X42)
        | ~ r2_hidden(X45,X44)
        | X44 != k3_xboole_0(X42,X43) )
      & ( r2_hidden(X45,X43)
        | ~ r2_hidden(X45,X44)
        | X44 != k3_xboole_0(X42,X43) )
      & ( ~ r2_hidden(X46,X42)
        | ~ r2_hidden(X46,X43)
        | r2_hidden(X46,X44)
        | X44 != k3_xboole_0(X42,X43) )
      & ( ~ r2_hidden(esk4_3(X47,X48,X49),X49)
        | ~ r2_hidden(esk4_3(X47,X48,X49),X47)
        | ~ r2_hidden(esk4_3(X47,X48,X49),X48)
        | X49 = k3_xboole_0(X47,X48) )
      & ( r2_hidden(esk4_3(X47,X48,X49),X47)
        | r2_hidden(esk4_3(X47,X48,X49),X49)
        | X49 = k3_xboole_0(X47,X48) )
      & ( r2_hidden(esk4_3(X47,X48,X49),X48)
        | r2_hidden(esk4_3(X47,X48,X49),X49)
        | X49 = k3_xboole_0(X47,X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_37,negated_conjecture,
    ( ~ r2_hidden(esk51_0,k2_zfmisc_1(k5_xboole_0(k5_xboole_0(esk52_0,esk54_0),k3_tarski(k6_enumset1(esk52_0,esk52_0,esk52_0,esk52_0,esk52_0,esk52_0,esk52_0,esk54_0))),k5_xboole_0(k5_xboole_0(esk53_0,esk55_0),k3_tarski(k6_enumset1(esk53_0,esk53_0,esk53_0,esk53_0,esk53_0,esk53_0,esk53_0,esk55_0))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_33]),c_0_33])).

cnf(c_0_38,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,plain,
    ( k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))),k5_xboole_0(k5_xboole_0(X3,X4),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)))) = k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)),k3_tarski(k6_enumset1(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_30]),c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_32]),c_0_33]),c_0_33]),c_0_33])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( ~ r2_hidden(esk51_0,k2_zfmisc_1(k5_xboole_0(esk52_0,k5_xboole_0(esk54_0,k3_tarski(k6_enumset1(esk52_0,esk52_0,esk52_0,esk52_0,esk52_0,esk52_0,esk52_0,esk54_0)))),k5_xboole_0(esk53_0,k5_xboole_0(esk55_0,k3_tarski(k6_enumset1(esk53_0,esk53_0,esk53_0,esk53_0,esk53_0,esk53_0,esk53_0,esk55_0)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38]),c_0_38])).

cnf(c_0_42,plain,
    ( k2_zfmisc_1(k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k5_xboole_0(X3,k5_xboole_0(X4,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4))))) = k5_xboole_0(k2_zfmisc_1(X1,X3),k5_xboole_0(k2_zfmisc_1(X2,X4),k3_tarski(k6_enumset1(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_38]),c_0_38]),c_0_38])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X4)
    | X4 != k5_xboole_0(k5_xboole_0(X2,X3),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_30]),c_0_31]),c_0_32]),c_0_33])).

cnf(c_0_44,negated_conjecture,
    ( ~ r2_hidden(esk51_0,k5_xboole_0(k2_zfmisc_1(esk52_0,esk53_0),k5_xboole_0(k2_zfmisc_1(esk54_0,esk55_0),k3_tarski(k6_enumset1(k2_zfmisc_1(esk52_0,esk53_0),k2_zfmisc_1(esk52_0,esk53_0),k2_zfmisc_1(esk52_0,esk53_0),k2_zfmisc_1(esk52_0,esk53_0),k2_zfmisc_1(esk52_0,esk53_0),k2_zfmisc_1(esk52_0,esk53_0),k2_zfmisc_1(esk52_0,esk53_0),k2_zfmisc_1(esk54_0,esk55_0)))))) ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_38])])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk51_0,k2_zfmisc_1(esk54_0,esk55_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk51_0,k2_zfmisc_1(esk52_0,esk53_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47])]),
    [proof]).
%------------------------------------------------------------------------------
