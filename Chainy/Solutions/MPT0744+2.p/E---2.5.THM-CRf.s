%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0744+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:51 EST 2020

% Result     : Theorem 6.83s
% Output     : CNFRefutation 6.83s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 483 expanded)
%              Number of clauses        :   51 ( 188 expanded)
%              Number of leaves         :   23 ( 140 expanded)
%              Depth                    :   13
%              Number of atoms          :  230 ( 855 expanded)
%              Number of equality atoms :   42 ( 349 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t34_ordinal1,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,k1_ordinal1(X2))
          <=> r1_ordinal1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

fof(t25_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => r3_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_ordinal1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT004+2.ax',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t70_enumset1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d3_xboole_0)).

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

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t69_enumset1)).

fof(symmetry_r3_xboole_0,axiom,(
    ! [X1,X2] :
      ( r3_xboole_0(X1,X2)
     => r3_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',symmetry_r3_xboole_0)).

fof(d9_xboole_0,axiom,(
    ! [X1,X2] :
      ( r3_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        | r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',d9_xboole_0)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',idempotence_k2_xboole_0)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT004+2.ax',l49_zfmisc_1)).

fof(t22_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ! [X3] :
              ( v3_ordinal1(X3)
             => ( ( r1_tarski(X1,X2)
                  & r2_hidden(X2,X3) )
               => r2_hidden(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_ordinal1)).

fof(t23_ordinal1,axiom,(
    ! [X1,X2] :
      ( v3_ordinal1(X2)
     => ( r2_hidden(X1,X2)
       => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

fof(cc1_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v1_ordinal1(X1)
        & v2_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(fc2_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( ~ v1_xboole_0(k1_ordinal1(X1))
        & v3_ordinal1(k1_ordinal1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_ordinal1)).

fof(t10_ordinal1,axiom,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ( r2_hidden(X1,k1_ordinal1(X2))
            <=> r1_ordinal1(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t34_ordinal1])).

fof(c_0_24,plain,(
    ! [X3198,X3199] :
      ( ~ v3_ordinal1(X3198)
      | ~ v3_ordinal1(X3199)
      | r3_xboole_0(X3198,X3199) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_ordinal1])])])).

fof(c_0_25,negated_conjecture,
    ( v3_ordinal1(esk228_0)
    & v3_ordinal1(esk229_0)
    & ( ~ r2_hidden(esk228_0,k1_ordinal1(esk229_0))
      | ~ r1_ordinal1(esk228_0,esk229_0) )
    & ( r2_hidden(esk228_0,k1_ordinal1(esk229_0))
      | r1_ordinal1(esk228_0,esk229_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

fof(c_0_26,plain,(
    ! [X1087,X1088] : k3_tarski(k2_tarski(X1087,X1088)) = k2_xboole_0(X1087,X1088) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_27,plain,(
    ! [X892,X893] : k1_enumset1(X892,X892,X893) = k2_tarski(X892,X893) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_28,plain,
    ( r3_xboole_0(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( v3_ordinal1(esk229_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_30,plain,(
    ! [X33,X34,X35,X36,X37,X38,X39,X40] :
      ( ( ~ r2_hidden(X36,X35)
        | r2_hidden(X36,X33)
        | r2_hidden(X36,X34)
        | X35 != k2_xboole_0(X33,X34) )
      & ( ~ r2_hidden(X37,X33)
        | r2_hidden(X37,X35)
        | X35 != k2_xboole_0(X33,X34) )
      & ( ~ r2_hidden(X37,X34)
        | r2_hidden(X37,X35)
        | X35 != k2_xboole_0(X33,X34) )
      & ( ~ r2_hidden(esk3_3(X38,X39,X40),X38)
        | ~ r2_hidden(esk3_3(X38,X39,X40),X40)
        | X40 = k2_xboole_0(X38,X39) )
      & ( ~ r2_hidden(esk3_3(X38,X39,X40),X39)
        | ~ r2_hidden(esk3_3(X38,X39,X40),X40)
        | X40 = k2_xboole_0(X38,X39) )
      & ( r2_hidden(esk3_3(X38,X39,X40),X40)
        | r2_hidden(esk3_3(X38,X39,X40),X38)
        | r2_hidden(esk3_3(X38,X39,X40),X39)
        | X40 = k2_xboole_0(X38,X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_31,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_33,plain,(
    ! [X894,X895,X896] : k2_enumset1(X894,X894,X895,X896) = k1_enumset1(X894,X895,X896) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_34,plain,(
    ! [X897,X898,X899,X900] : k3_enumset1(X897,X897,X898,X899,X900) = k2_enumset1(X897,X898,X899,X900) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_35,plain,(
    ! [X901,X902,X903,X904,X905] : k4_enumset1(X901,X901,X902,X903,X904,X905) = k3_enumset1(X901,X902,X903,X904,X905) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_36,plain,(
    ! [X906,X907,X908,X909,X910,X911] : k5_enumset1(X906,X906,X907,X908,X909,X910,X911) = k4_enumset1(X906,X907,X908,X909,X910,X911) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_37,plain,(
    ! [X912,X913,X914,X915,X916,X917,X918] : k6_enumset1(X912,X912,X913,X914,X915,X916,X917,X918) = k5_enumset1(X912,X913,X914,X915,X916,X917,X918) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_38,plain,(
    ! [X3156] : k1_ordinal1(X3156) = k2_xboole_0(X3156,k1_tarski(X3156)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_39,plain,(
    ! [X891] : k2_tarski(X891,X891) = k1_tarski(X891) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_40,plain,(
    ! [X125,X126] :
      ( ~ r3_xboole_0(X125,X126)
      | r3_xboole_0(X126,X125) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r3_xboole_0])])).

cnf(c_0_41,negated_conjecture,
    ( r3_xboole_0(X1,esk229_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_42,negated_conjecture,
    ( v3_ordinal1(esk228_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_44,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_45,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_49,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_50,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_51,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_52,plain,(
    ! [X106,X107] :
      ( ( ~ r3_xboole_0(X106,X107)
        | r1_tarski(X106,X107)
        | r1_tarski(X107,X106) )
      & ( ~ r1_tarski(X106,X107)
        | r3_xboole_0(X106,X107) )
      & ( ~ r1_tarski(X107,X106)
        | r3_xboole_0(X106,X107) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_xboole_0])])])).

cnf(c_0_53,plain,
    ( r3_xboole_0(X2,X1)
    | ~ r3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_54,negated_conjecture,
    ( r3_xboole_0(esk228_0,esk229_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,X4)
    | r2_hidden(X1,X3)
    | X2 != k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_46]),c_0_47]),c_0_48]),c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk228_0,k1_ordinal1(esk229_0))
    | r1_ordinal1(esk228_0,esk229_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_57,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k2_tarski(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_50,c_0_51])).

fof(c_0_58,plain,(
    ! [X3232,X3233] :
      ( ~ r2_hidden(X3232,X3233)
      | ~ r1_tarski(X3233,X3232) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,X2)
    | r1_tarski(X2,X1)
    | ~ r3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( r3_xboole_0(esk229_0,esk228_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

fof(c_0_61,plain,(
    ! [X3176,X3177] :
      ( ( ~ r1_ordinal1(X3176,X3177)
        | r1_tarski(X3176,X3177)
        | ~ v3_ordinal1(X3176)
        | ~ v3_ordinal1(X3177) )
      & ( ~ r1_tarski(X3176,X3177)
        | r1_ordinal1(X3176,X3177)
        | ~ v3_ordinal1(X3176)
        | ~ v3_ordinal1(X3177) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2))) ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_63,negated_conjecture,
    ( r1_ordinal1(esk228_0,esk229_0)
    | r2_hidden(esk228_0,k3_tarski(k6_enumset1(esk229_0,esk229_0,esk229_0,esk229_0,esk229_0,esk229_0,esk229_0,k6_enumset1(esk229_0,esk229_0,esk229_0,esk229_0,esk229_0,esk229_0,esk229_0,esk229_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57]),c_0_32]),c_0_44]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_49]),c_0_49])).

cnf(c_0_64,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(esk229_0,esk228_0)
    | r1_tarski(esk228_0,esk229_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

fof(c_0_66,plain,(
    ! [X66] : k2_xboole_0(X66,X66) = X66 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_67,plain,(
    ! [X1085,X1086] :
      ( ~ r2_hidden(X1085,X1086)
      | r1_tarski(X1085,k3_tarski(X1086)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( r1_ordinal1(esk228_0,esk229_0)
    | r2_hidden(esk228_0,k6_enumset1(esk229_0,esk229_0,esk229_0,esk229_0,esk229_0,esk229_0,esk229_0,esk229_0))
    | r2_hidden(esk228_0,esk229_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(esk228_0,esk229_0)
    | ~ r2_hidden(esk228_0,esk229_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_71,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

fof(c_0_72,plain,(
    ! [X3191,X3192,X3193] :
      ( ~ v1_ordinal1(X3191)
      | ~ v3_ordinal1(X3192)
      | ~ v3_ordinal1(X3193)
      | ~ r1_tarski(X3191,X3192)
      | ~ r2_hidden(X3192,X3193)
      | r2_hidden(X3191,X3193) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_ordinal1])])])).

fof(c_0_73,plain,(
    ! [X3194,X3195] :
      ( ~ v3_ordinal1(X3195)
      | ~ r2_hidden(X3194,X3195)
      | v3_ordinal1(X3194) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).

fof(c_0_74,plain,(
    ! [X3151] :
      ( ( v1_ordinal1(X3151)
        | ~ v3_ordinal1(X3151) )
      & ( v2_ordinal1(X3151)
        | ~ v3_ordinal1(X3151) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).

fof(c_0_75,plain,(
    ! [X3173] :
      ( ( ~ v1_xboole_0(k1_ordinal1(X3173))
        | ~ v3_ordinal1(X3173) )
      & ( v3_ordinal1(k1_ordinal1(X3173))
        | ~ v3_ordinal1(X3173) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_ordinal1])])])])).

cnf(c_0_76,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(esk228_0,esk229_0)
    | r2_hidden(esk228_0,k6_enumset1(esk229_0,esk229_0,esk229_0,esk229_0,esk229_0,esk229_0,esk229_0,esk229_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_29]),c_0_42])]),c_0_70])).

cnf(c_0_78,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_44]),c_0_45]),c_0_46]),c_0_47]),c_0_48]),c_0_49])).

cnf(c_0_79,plain,
    ( r2_hidden(X1,X3)
    | ~ v1_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X3)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_80,plain,
    ( v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_81,plain,
    ( v1_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

fof(c_0_82,plain,(
    ! [X3180] : r2_hidden(X3180,k1_ordinal1(X3180)) ),
    inference(variable_rename,[status(thm)],[t10_ordinal1])).

cnf(c_0_83,plain,
    ( v3_ordinal1(k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_84,negated_conjecture,
    ( ~ r2_hidden(esk228_0,k1_ordinal1(esk229_0))
    | ~ r1_ordinal1(esk228_0,esk229_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_85,plain,
    ( r1_ordinal1(X1,X2)
    | ~ r1_tarski(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_86,negated_conjecture,
    ( r1_tarski(esk228_0,esk229_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78])])).

cnf(c_0_87,plain,
    ( r2_hidden(X1,X2)
    | ~ v1_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r1_tarski(X1,X3)
    | ~ r2_hidden(X3,X2) ),
    inference(csr,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_88,negated_conjecture,
    ( v1_ordinal1(esk228_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_42])).

cnf(c_0_89,plain,
    ( r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_90,plain,
    ( v3_ordinal1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))
    | ~ v3_ordinal1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_57]),c_0_32]),c_0_44]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_49]),c_0_49])).

cnf(c_0_91,negated_conjecture,
    ( ~ r1_ordinal1(esk228_0,esk229_0)
    | ~ r2_hidden(esk228_0,k3_tarski(k6_enumset1(esk229_0,esk229_0,esk229_0,esk229_0,esk229_0,esk229_0,esk229_0,k6_enumset1(esk229_0,esk229_0,esk229_0,esk229_0,esk229_0,esk229_0,esk229_0,esk229_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_57]),c_0_32]),c_0_44]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_49]),c_0_49])).

cnf(c_0_92,negated_conjecture,
    ( r1_ordinal1(esk228_0,esk229_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_29]),c_0_42])])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(esk228_0,X1)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(esk229_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_86]),c_0_88])])).

cnf(c_0_94,plain,
    ( r2_hidden(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_57]),c_0_32]),c_0_44]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_49]),c_0_49])).

cnf(c_0_95,negated_conjecture,
    ( v3_ordinal1(k3_tarski(k6_enumset1(esk229_0,esk229_0,esk229_0,esk229_0,esk229_0,esk229_0,esk229_0,k6_enumset1(esk229_0,esk229_0,esk229_0,esk229_0,esk229_0,esk229_0,esk229_0,esk229_0)))) ),
    inference(spm,[status(thm)],[c_0_90,c_0_29])).

cnf(c_0_96,negated_conjecture,
    ( ~ r2_hidden(esk228_0,k3_tarski(k6_enumset1(esk229_0,esk229_0,esk229_0,esk229_0,esk229_0,esk229_0,esk229_0,k6_enumset1(esk229_0,esk229_0,esk229_0,esk229_0,esk229_0,esk229_0,esk229_0,esk229_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_92])])).

cnf(c_0_97,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_95])]),c_0_96]),
    [proof]).
%------------------------------------------------------------------------------
