%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0124+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:37 EST 2020

% Result     : Theorem 5.86s
% Output     : CNFRefutation 5.86s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 296 expanded)
%              Number of clauses        :   68 ( 126 expanded)
%              Number of leaves         :   29 (  82 expanded)
%              Depth                    :   12
%              Number of atoms          :  240 ( 522 expanded)
%              Number of equality atoms :   87 ( 252 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t117_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X3,X2)
     => k4_xboole_0(X1,X3) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X3))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_xboole_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',t4_xboole_0)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t20_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3)
        & ! [X4] :
            ( ( r1_tarski(X4,X2)
              & r1_tarski(X4,X3) )
           => r1_tarski(X4,X1) ) )
     => X1 = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t45_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',t3_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d7_xboole_0)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d1_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k5_xboole_0)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(l97_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

fof(t112_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t69_xboole_1,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_tarski(X2,X1)
          & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d3_tarski)).

fof(t85_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_xboole_0(X1,k4_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(c_0_29,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X3,X2)
       => k4_xboole_0(X1,X3) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X3))) ) ),
    inference(assume_negation,[status(cth)],[t117_xboole_1])).

fof(c_0_30,plain,(
    ! [X82,X83,X85,X86,X87] :
      ( ( r1_xboole_0(X82,X83)
        | r2_hidden(esk11_2(X82,X83),k3_xboole_0(X82,X83)) )
      & ( ~ r2_hidden(X87,k3_xboole_0(X85,X86))
        | ~ r1_xboole_0(X85,X86) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_31,plain,(
    ! [X230] : k3_xboole_0(X230,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_32,plain,(
    ! [X331] : r1_xboole_0(X331,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_33,plain,(
    ! [X201,X202,X203] :
      ( ( r1_tarski(esk18_3(X201,X202,X203),X202)
        | ~ r1_tarski(X201,X202)
        | ~ r1_tarski(X201,X203)
        | X201 = k3_xboole_0(X202,X203) )
      & ( r1_tarski(esk18_3(X201,X202,X203),X203)
        | ~ r1_tarski(X201,X202)
        | ~ r1_tarski(X201,X203)
        | X201 = k3_xboole_0(X202,X203) )
      & ( ~ r1_tarski(esk18_3(X201,X202,X203),X201)
        | ~ r1_tarski(X201,X202)
        | ~ r1_tarski(X201,X203)
        | X201 = k3_xboole_0(X202,X203) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_xboole_1])])])])).

fof(c_0_34,negated_conjecture,
    ( r1_tarski(esk16_0,esk15_0)
    & k4_xboole_0(esk14_0,esk16_0) != k2_xboole_0(k4_xboole_0(esk14_0,esk15_0),k3_xboole_0(esk14_0,k4_xboole_0(esk15_0,esk16_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).

fof(c_0_35,plain,(
    ! [X96,X97] :
      ( ( r1_tarski(X96,X97)
        | X96 != X97 )
      & ( r1_tarski(X97,X96)
        | X96 != X97 )
      & ( ~ r1_tarski(X96,X97)
        | ~ r1_tarski(X97,X96)
        | X96 = X97 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_36,plain,(
    ! [X425,X426] : k2_xboole_0(X425,X426) = k5_xboole_0(X425,k4_xboole_0(X426,X425)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_37,plain,(
    ! [X119,X120] : k4_xboole_0(X119,X120) = k5_xboole_0(X119,k3_xboole_0(X119,X120)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_38,plain,(
    ! [X274,X275] :
      ( ~ r1_tarski(X274,X275)
      | X275 = k2_xboole_0(X274,k4_xboole_0(X275,X274)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).

cnf(c_0_39,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_42,plain,(
    ! [X76,X77,X79,X80,X81] :
      ( ( r2_hidden(esk10_2(X76,X77),X76)
        | r1_xboole_0(X76,X77) )
      & ( r2_hidden(esk10_2(X76,X77),X77)
        | r1_xboole_0(X76,X77) )
      & ( ~ r2_hidden(X81,X79)
        | ~ r2_hidden(X81,X80)
        | ~ r1_xboole_0(X79,X80) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_43,plain,
    ( r1_tarski(esk18_3(X1,X2,X3),X2)
    | X1 = k3_xboole_0(X2,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(esk16_0,esk15_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,negated_conjecture,
    ( k4_xboole_0(esk14_0,esk16_0) != k2_xboole_0(k4_xboole_0(esk14_0,esk15_0),k3_xboole_0(esk14_0,k4_xboole_0(esk15_0,esk16_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_49,plain,(
    ! [X11,X12] : k3_xboole_0(X11,X12) = k3_xboole_0(X12,X11) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_50,plain,(
    ! [X410,X411,X412] : k5_xboole_0(k5_xboole_0(X410,X411),X412) = k5_xboole_0(X410,k5_xboole_0(X411,X412)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

fof(c_0_51,plain,(
    ! [X282,X283,X284] : k3_xboole_0(X282,k4_xboole_0(X283,X284)) = k4_xboole_0(k3_xboole_0(X282,X283),X284) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

cnf(c_0_52,plain,
    ( X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_53,plain,(
    ! [X54,X55] :
      ( ( ~ r1_xboole_0(X54,X55)
        | k3_xboole_0(X54,X55) = k1_xboole_0 )
      & ( k3_xboole_0(X54,X55) != k1_xboole_0
        | r1_xboole_0(X54,X55) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_54,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])])).

cnf(c_0_55,plain,
    ( r2_hidden(esk10_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_56,plain,(
    ! [X385,X386] :
      ( ( ~ r1_xboole_0(X385,X386)
        | k4_xboole_0(X385,X386) = X385 )
      & ( k4_xboole_0(X385,X386) != X385
        | r1_xboole_0(X385,X386) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_57,plain,(
    ! [X15,X16,X17] :
      ( ( ~ v1_xboole_0(X15)
        | ~ r2_hidden(X16,X15) )
      & ( r2_hidden(esk1_1(X17),X17)
        | v1_xboole_0(X17) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_58,negated_conjecture,
    ( k3_xboole_0(X1,esk15_0) = esk16_0
    | r1_tarski(esk18_3(esk16_0,X1,esk15_0),X1)
    | ~ r1_tarski(esk16_0,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_60,negated_conjecture,
    ( k5_xboole_0(esk14_0,k3_xboole_0(esk14_0,esk16_0)) != k5_xboole_0(k5_xboole_0(esk14_0,k3_xboole_0(esk14_0,esk15_0)),k5_xboole_0(k3_xboole_0(esk14_0,k5_xboole_0(esk15_0,k3_xboole_0(esk15_0,esk16_0))),k3_xboole_0(k3_xboole_0(esk14_0,k5_xboole_0(esk15_0,k3_xboole_0(esk15_0,esk16_0))),k5_xboole_0(esk14_0,k3_xboole_0(esk14_0,esk15_0))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48])).

cnf(c_0_61,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_62,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_63,plain,(
    ! [X225,X226] :
      ( ~ r1_tarski(X225,X226)
      | k3_xboole_0(X225,X226) = X225 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_64,plain,(
    ! [X13,X14] : k5_xboole_0(X13,X14) = k5_xboole_0(X14,X13) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

fof(c_0_65,plain,(
    ! [X186,X187,X188] : k3_xboole_0(k3_xboole_0(X186,X187),X188) = k3_xboole_0(X186,k3_xboole_0(X187,X188)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

cnf(c_0_66,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_67,plain,
    ( X2 = k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),X1)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_47]),c_0_48]),c_0_48])).

cnf(c_0_68,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_69,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

fof(c_0_70,plain,(
    ! [X316] : k5_xboole_0(X316,k1_xboole_0) = X316 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_71,plain,(
    ! [X231] : r1_tarski(k1_xboole_0,X231) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_72,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

fof(c_0_73,plain,(
    ! [X403,X404] :
      ( ~ v1_xboole_0(X403)
      | X403 = X404
      | ~ v1_xboole_0(X404) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_74,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_75,plain,(
    ! [X112,X113] : r1_xboole_0(k3_xboole_0(X112,X113),k5_xboole_0(X112,X113)) ),
    inference(variable_rename,[status(thm)],[l97_xboole_1])).

cnf(c_0_76,plain,
    ( X1 = k3_xboole_0(X2,X3)
    | ~ r1_tarski(esk18_3(X1,X2,X3),X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_77,negated_conjecture,
    ( k3_xboole_0(esk16_0,esk15_0) = esk16_0
    | r1_tarski(esk18_3(esk16_0,esk16_0,esk15_0),esk16_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_78,negated_conjecture,
    ( k5_xboole_0(esk14_0,k5_xboole_0(k3_xboole_0(esk15_0,esk14_0),k5_xboole_0(k3_xboole_0(esk14_0,k5_xboole_0(esk15_0,k3_xboole_0(esk16_0,esk15_0))),k3_xboole_0(k5_xboole_0(esk14_0,k3_xboole_0(esk15_0,esk14_0)),k3_xboole_0(esk14_0,k5_xboole_0(esk15_0,k3_xboole_0(esk16_0,esk15_0))))))) != k5_xboole_0(esk14_0,k3_xboole_0(esk16_0,esk14_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61]),c_0_61]),c_0_61]),c_0_61]),c_0_61]),c_0_61]),c_0_62])).

cnf(c_0_79,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_80,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_81,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_82,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_48]),c_0_48])).

fof(c_0_83,plain,(
    ! [X153,X154,X155] : k5_xboole_0(k3_xboole_0(X153,X154),k3_xboole_0(X155,X154)) = k3_xboole_0(k5_xboole_0(X153,X155),X154) ),
    inference(variable_rename,[status(thm)],[t112_xboole_1])).

fof(c_0_84,plain,(
    ! [X413] : k5_xboole_0(X413,X413) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_85,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_61]),c_0_62])).

cnf(c_0_86,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_87,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_88,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_89,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_72,c_0_48])).

cnf(c_0_90,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_91,plain,
    ( v1_xboole_0(k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_74])).

cnf(c_0_92,plain,
    ( r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_93,negated_conjecture,
    ( k3_xboole_0(esk16_0,esk15_0) = esk16_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_44]),c_0_59])])).

fof(c_0_94,plain,(
    ! [X339,X340] :
      ( v1_xboole_0(X340)
      | ~ r1_tarski(X340,X339)
      | ~ r1_xboole_0(X340,X339) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

cnf(c_0_95,negated_conjecture,
    ( k5_xboole_0(esk14_0,k5_xboole_0(k3_xboole_0(esk15_0,esk14_0),k5_xboole_0(k3_xboole_0(esk14_0,k5_xboole_0(esk16_0,esk15_0)),k3_xboole_0(k5_xboole_0(esk14_0,k3_xboole_0(esk15_0,esk14_0)),k3_xboole_0(esk14_0,k5_xboole_0(esk16_0,esk15_0)))))) != k5_xboole_0(esk14_0,k3_xboole_0(esk16_0,esk14_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_44])]),c_0_80]),c_0_80])).

cnf(c_0_96,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,k3_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_81])).

cnf(c_0_97,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X3))) = k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_82,c_0_81])).

cnf(c_0_98,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_99,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_100,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_40]),c_0_87]),c_0_87]),c_0_88])])).

cnf(c_0_101,plain,
    ( k5_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X3)
    | ~ v1_xboole_0(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_91])).

cnf(c_0_102,negated_conjecture,
    ( r1_xboole_0(esk16_0,k5_xboole_0(esk16_0,esk15_0)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_103,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

fof(c_0_104,plain,(
    ! [X250,X251] : r1_tarski(k4_xboole_0(X250,X251),X250) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_105,negated_conjecture,
    ( k5_xboole_0(esk14_0,k5_xboole_0(k3_xboole_0(esk15_0,esk14_0),k3_xboole_0(esk14_0,k5_xboole_0(esk16_0,k5_xboole_0(esk15_0,k3_xboole_0(k5_xboole_0(esk16_0,esk15_0),k5_xboole_0(esk14_0,k3_xboole_0(esk15_0,esk14_0)))))))) != k5_xboole_0(esk14_0,k3_xboole_0(esk16_0,esk14_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_96]),c_0_61]),c_0_96]),c_0_61]),c_0_97]),c_0_62])).

cnf(c_0_106,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_98,c_0_61])).

cnf(c_0_107,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X2,k5_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_80]),c_0_62])).

cnf(c_0_108,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_99]),c_0_100])).

cnf(c_0_109,negated_conjecture,
    ( k5_xboole_0(esk16_0,X1) = esk16_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_110,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_41])).

fof(c_0_111,plain,(
    ! [X19,X20,X21,X22,X23] :
      ( ( ~ r1_tarski(X19,X20)
        | ~ r2_hidden(X21,X19)
        | r2_hidden(X21,X20) )
      & ( r2_hidden(esk2_2(X22,X23),X22)
        | r1_tarski(X22,X23) )
      & ( ~ r2_hidden(esk2_2(X22,X23),X23)
        | r1_tarski(X22,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_112,plain,(
    ! [X390,X391,X392] :
      ( ~ r1_tarski(X390,X391)
      | r1_xboole_0(X390,k4_xboole_0(X392,X391)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).

cnf(c_0_113,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_104])).

cnf(c_0_114,negated_conjecture,
    ( k5_xboole_0(esk14_0,k3_xboole_0(esk14_0,k5_xboole_0(esk16_0,k3_xboole_0(k5_xboole_0(esk16_0,esk15_0),k5_xboole_0(esk14_0,k3_xboole_0(esk15_0,esk14_0)))))) != k5_xboole_0(esk14_0,k3_xboole_0(esk16_0,esk14_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_105,c_0_106]),c_0_107]),c_0_108]),c_0_61])).

cnf(c_0_115,negated_conjecture,
    ( k5_xboole_0(esk16_0,X1) = esk16_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_109,c_0_110])).

cnf(c_0_116,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_111])).

cnf(c_0_117,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_112])).

cnf(c_0_118,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_113,c_0_48])).

cnf(c_0_119,negated_conjecture,
    ( ~ r1_tarski(k3_xboole_0(k5_xboole_0(esk16_0,esk15_0),k5_xboole_0(esk14_0,k3_xboole_0(esk15_0,esk14_0))),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_115]),c_0_61])])).

cnf(c_0_120,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_116])).

cnf(c_0_121,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_117,c_0_48])).

cnf(c_0_122,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_118,c_0_61])).

cnf(c_0_123,negated_conjecture,
    ( ~ r1_xboole_0(k5_xboole_0(esk16_0,esk15_0),k5_xboole_0(esk14_0,k3_xboole_0(esk15_0,esk14_0))) ),
    inference(spm,[status(thm)],[c_0_119,c_0_120])).

cnf(c_0_124,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X3,X2)))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_121,c_0_61])).

cnf(c_0_125,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk16_0,esk15_0),esk15_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_93]),c_0_80])).

cnf(c_0_126,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_124]),c_0_125])]),
    [proof]).
%------------------------------------------------------------------------------
