%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:25 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  107 (3878 expanded)
%              Number of clauses        :   60 (1673 expanded)
%              Number of leaves         :   23 (1013 expanded)
%              Depth                    :   17
%              Number of atoms          :  319 (11699 expanded)
%              Number of equality atoms :  106 (3821 expanded)
%              Maximal formula depth    :   37 (   4 average)
%              Maximal clause size      :   52 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t34_ordinal1,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,k1_ordinal1(X2))
          <=> r1_ordinal1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t90_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_enumset1)).

fof(d4_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] :
      ( X7 = k4_enumset1(X1,X2,X3,X4,X5,X6)
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ~ ( X8 != X1
              & X8 != X2
              & X8 != X3
              & X8 != X4
              & X8 != X5
              & X8 != X6 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_enumset1)).

fof(t81_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_enumset1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(t24_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ~ ( ~ r2_hidden(X1,X2)
              & X1 != X2
              & ~ r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(antisymmetry_r2_hidden,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(t26_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r1_ordinal1(X1,X2)
            | r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t10_ordinal1,axiom,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(c_0_23,plain,(
    ! [X33,X34] : r1_tarski(X33,k2_xboole_0(X33,X34)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_24,plain,(
    ! [X35,X36] : k2_xboole_0(X35,X36) = k5_xboole_0(X35,k4_xboole_0(X36,X35)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_27,plain,(
    ! [X26,X27] :
      ( ( k4_xboole_0(X26,X27) != k1_xboole_0
        | r1_tarski(X26,X27) )
      & ( ~ r1_tarski(X26,X27)
        | k4_xboole_0(X26,X27) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_28,plain,(
    ! [X32] : k5_xboole_0(X32,k1_xboole_0) = X32 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_31,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_32,plain,(
    ! [X31] : r1_tarski(k1_xboole_0,X31) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_33,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ( r2_hidden(X1,k1_ordinal1(X2))
            <=> r1_ordinal1(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t34_ordinal1])).

fof(c_0_34,plain,(
    ! [X70] : k1_ordinal1(X70) = k2_xboole_0(X70,k1_tarski(X70)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_35,plain,(
    ! [X37] : k2_tarski(X37,X37) = k1_tarski(X37) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_36,plain,(
    ! [X28,X29,X30] :
      ( ( r1_tarski(X28,X29)
        | ~ r1_tarski(X28,k4_xboole_0(X29,X30)) )
      & ( r1_xboole_0(X28,X30)
        | ~ r1_tarski(X28,k4_xboole_0(X29,X30)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X1)
    | ~ r1_tarski(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_38,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_39,negated_conjecture,
    ( v3_ordinal1(esk4_0)
    & v3_ordinal1(esk5_0)
    & ( ~ r2_hidden(esk4_0,k1_ordinal1(esk5_0))
      | ~ r1_ordinal1(esk4_0,esk5_0) )
    & ( r2_hidden(esk4_0,k1_ordinal1(esk5_0))
      | r1_ordinal1(esk4_0,esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_33])])])).

cnf(c_0_40,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_42,plain,(
    ! [X38,X39] : k1_enumset1(X38,X38,X39) = k2_tarski(X38,X39) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_43,plain,(
    ! [X40,X41,X42] : k2_enumset1(X40,X40,X41,X42) = k1_enumset1(X40,X41,X42) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_44,plain,(
    ! [X49,X50,X51,X52] : k6_enumset1(X49,X49,X49,X49,X49,X50,X51,X52) = k2_enumset1(X49,X50,X51,X52) ),
    inference(variable_rename,[status(thm)],[t90_enumset1])).

fof(c_0_45,plain,(
    ! [X53,X54,X55,X56,X57,X58,X59,X60,X61,X62,X63,X64,X65,X66,X67,X68] :
      ( ( ~ r2_hidden(X60,X59)
        | X60 = X53
        | X60 = X54
        | X60 = X55
        | X60 = X56
        | X60 = X57
        | X60 = X58
        | X59 != k4_enumset1(X53,X54,X55,X56,X57,X58) )
      & ( X61 != X53
        | r2_hidden(X61,X59)
        | X59 != k4_enumset1(X53,X54,X55,X56,X57,X58) )
      & ( X61 != X54
        | r2_hidden(X61,X59)
        | X59 != k4_enumset1(X53,X54,X55,X56,X57,X58) )
      & ( X61 != X55
        | r2_hidden(X61,X59)
        | X59 != k4_enumset1(X53,X54,X55,X56,X57,X58) )
      & ( X61 != X56
        | r2_hidden(X61,X59)
        | X59 != k4_enumset1(X53,X54,X55,X56,X57,X58) )
      & ( X61 != X57
        | r2_hidden(X61,X59)
        | X59 != k4_enumset1(X53,X54,X55,X56,X57,X58) )
      & ( X61 != X58
        | r2_hidden(X61,X59)
        | X59 != k4_enumset1(X53,X54,X55,X56,X57,X58) )
      & ( esk3_7(X62,X63,X64,X65,X66,X67,X68) != X62
        | ~ r2_hidden(esk3_7(X62,X63,X64,X65,X66,X67,X68),X68)
        | X68 = k4_enumset1(X62,X63,X64,X65,X66,X67) )
      & ( esk3_7(X62,X63,X64,X65,X66,X67,X68) != X63
        | ~ r2_hidden(esk3_7(X62,X63,X64,X65,X66,X67,X68),X68)
        | X68 = k4_enumset1(X62,X63,X64,X65,X66,X67) )
      & ( esk3_7(X62,X63,X64,X65,X66,X67,X68) != X64
        | ~ r2_hidden(esk3_7(X62,X63,X64,X65,X66,X67,X68),X68)
        | X68 = k4_enumset1(X62,X63,X64,X65,X66,X67) )
      & ( esk3_7(X62,X63,X64,X65,X66,X67,X68) != X65
        | ~ r2_hidden(esk3_7(X62,X63,X64,X65,X66,X67,X68),X68)
        | X68 = k4_enumset1(X62,X63,X64,X65,X66,X67) )
      & ( esk3_7(X62,X63,X64,X65,X66,X67,X68) != X66
        | ~ r2_hidden(esk3_7(X62,X63,X64,X65,X66,X67,X68),X68)
        | X68 = k4_enumset1(X62,X63,X64,X65,X66,X67) )
      & ( esk3_7(X62,X63,X64,X65,X66,X67,X68) != X67
        | ~ r2_hidden(esk3_7(X62,X63,X64,X65,X66,X67,X68),X68)
        | X68 = k4_enumset1(X62,X63,X64,X65,X66,X67) )
      & ( r2_hidden(esk3_7(X62,X63,X64,X65,X66,X67,X68),X68)
        | esk3_7(X62,X63,X64,X65,X66,X67,X68) = X62
        | esk3_7(X62,X63,X64,X65,X66,X67,X68) = X63
        | esk3_7(X62,X63,X64,X65,X66,X67,X68) = X64
        | esk3_7(X62,X63,X64,X65,X66,X67,X68) = X65
        | esk3_7(X62,X63,X64,X65,X66,X67,X68) = X66
        | esk3_7(X62,X63,X64,X65,X66,X67,X68) = X67
        | X68 = k4_enumset1(X62,X63,X64,X65,X66,X67) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_enumset1])])])])])])).

fof(c_0_46,plain,(
    ! [X43,X44,X45,X46,X47,X48] : k6_enumset1(X43,X43,X43,X44,X45,X46,X47,X48) = k4_enumset1(X43,X44,X45,X46,X47,X48) ),
    inference(variable_rename,[status(thm)],[t81_enumset1])).

fof(c_0_47,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( ~ r1_tarski(X11,X12)
        | ~ r2_hidden(X13,X11)
        | r2_hidden(X13,X12) )
      & ( r2_hidden(esk1_2(X14,X15),X14)
        | r1_tarski(X14,X15) )
      & ( ~ r2_hidden(esk1_2(X14,X15),X15)
        | r1_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_50,plain,(
    ! [X17,X18,X19] :
      ( ( ~ r2_hidden(X17,X18)
        | ~ r2_hidden(X17,X19)
        | ~ r2_hidden(X17,k5_xboole_0(X18,X19)) )
      & ( r2_hidden(X17,X18)
        | r2_hidden(X17,X19)
        | ~ r2_hidden(X17,k5_xboole_0(X18,X19)) )
      & ( ~ r2_hidden(X17,X18)
        | r2_hidden(X17,X19)
        | r2_hidden(X17,k5_xboole_0(X18,X19)) )
      & ( ~ r2_hidden(X17,X19)
        | r2_hidden(X17,X18)
        | r2_hidden(X17,k5_xboole_0(X18,X19)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk4_0,k1_ordinal1(esk5_0))
    | r1_ordinal1(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_52,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k2_tarski(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_53,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_54,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_55,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_56,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | X1 = X6
    | X1 = X7
    | X1 = X8
    | ~ r2_hidden(X1,X2)
    | X2 != k4_enumset1(X3,X4,X5,X6,X7,X8) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_57,plain,
    ( k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_58,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_59,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_61,negated_conjecture,
    ( r1_ordinal1(esk4_0,esk5_0)
    | r2_hidden(esk4_0,k5_xboole_0(esk5_0,k4_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk5_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_26]),c_0_54]),c_0_55])).

cnf(c_0_62,plain,
    ( X1 = X8
    | X1 = X7
    | X1 = X6
    | X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X4,X5,X6,X7,X8)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( r1_ordinal1(esk4_0,esk5_0)
    | r2_hidden(esk4_0,k4_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk5_0))
    | r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

fof(c_0_65,plain,(
    ! [X71,X72] :
      ( ( ~ r1_ordinal1(X71,X72)
        | r1_tarski(X71,X72)
        | ~ v3_ordinal1(X71)
        | ~ v3_ordinal1(X72) )
      & ( ~ r1_tarski(X71,X72)
        | r1_ordinal1(X71,X72)
        | ~ v3_ordinal1(X71)
        | ~ v3_ordinal1(X72) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_66,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | X1 = X5
    | X1 = X6
    | X1 = X7
    | ~ r2_hidden(X1,k6_enumset1(X7,X7,X7,X6,X5,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( r1_ordinal1(esk4_0,esk5_0)
    | r2_hidden(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))
    | r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

fof(c_0_68,plain,(
    ! [X74,X75] :
      ( ~ v3_ordinal1(X74)
      | ~ v3_ordinal1(X75)
      | r2_hidden(X74,X75)
      | X74 = X75
      | r2_hidden(X75,X74) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).

fof(c_0_69,plain,(
    ! [X78,X79] :
      ( ~ r2_hidden(X78,X79)
      | ~ r1_tarski(X79,X78) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_70,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( esk5_0 = esk4_0
    | r1_ordinal1(esk4_0,esk5_0)
    | r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( v3_ordinal1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_73,negated_conjecture,
    ( v3_ordinal1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_74,plain,(
    ! [X9,X10] :
      ( ~ r2_hidden(X9,X10)
      | ~ r2_hidden(X10,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).

cnf(c_0_75,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_76,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_77,negated_conjecture,
    ( esk5_0 = esk4_0
    | r1_tarski(esk4_0,esk5_0)
    | r2_hidden(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72]),c_0_73])])).

cnf(c_0_78,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_79,negated_conjecture,
    ( X1 = esk5_0
    | r2_hidden(X1,esk5_0)
    | r2_hidden(esk5_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_72])).

cnf(c_0_80,negated_conjecture,
    ( esk5_0 = esk4_0
    | ~ r2_hidden(esk5_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78])).

fof(c_0_81,plain,(
    ! [X76,X77] :
      ( ~ v3_ordinal1(X76)
      | ~ v3_ordinal1(X77)
      | r1_ordinal1(X76,X77)
      | r2_hidden(X77,X76) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).

cnf(c_0_82,negated_conjecture,
    ( ~ r2_hidden(esk4_0,k1_ordinal1(esk5_0))
    | ~ r1_ordinal1(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_83,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,k5_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_84,negated_conjecture,
    ( esk5_0 = esk4_0
    | r2_hidden(esk4_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_73]),c_0_80])).

cnf(c_0_85,plain,
    ( r1_ordinal1(X1,X2)
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

fof(c_0_86,plain,(
    ! [X20,X21,X23,X24,X25] :
      ( ( r2_hidden(esk2_2(X20,X21),X20)
        | r1_xboole_0(X20,X21) )
      & ( r2_hidden(esk2_2(X20,X21),X21)
        | r1_xboole_0(X20,X21) )
      & ( ~ r2_hidden(X25,X23)
        | ~ r2_hidden(X25,X24)
        | ~ r1_xboole_0(X23,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_87,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_88,negated_conjecture,
    ( ~ r1_ordinal1(esk4_0,esk5_0)
    | ~ r2_hidden(esk4_0,k5_xboole_0(esk5_0,k4_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk5_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_52]),c_0_53]),c_0_26]),c_0_54]),c_0_55])).

cnf(c_0_89,negated_conjecture,
    ( esk5_0 = esk4_0
    | r2_hidden(esk4_0,k5_xboole_0(esk5_0,X1))
    | r2_hidden(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_90,negated_conjecture,
    ( r1_ordinal1(X1,esk5_0)
    | r2_hidden(esk5_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_85,c_0_72])).

cnf(c_0_91,plain,
    ( ~ r2_hidden(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_29])).

cnf(c_0_92,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_93,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_87,c_0_49])).

cnf(c_0_94,negated_conjecture,
    ( esk5_0 = esk4_0
    | r2_hidden(esk4_0,k4_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk5_0))
    | ~ r1_ordinal1(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_95,negated_conjecture,
    ( r1_ordinal1(esk4_0,esk5_0)
    | r2_hidden(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_73])).

cnf(c_0_96,plain,
    ( ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X2,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_30]),c_0_31])).

fof(c_0_97,plain,(
    ! [X73] : r2_hidden(X73,k1_ordinal1(X73)) ),
    inference(variable_rename,[status(thm)],[t10_ordinal1])).

cnf(c_0_98,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_99,negated_conjecture,
    ( esk5_0 = esk4_0
    | r2_hidden(esk4_0,k4_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_80])).

cnf(c_0_100,negated_conjecture,
    ( r1_ordinal1(X1,esk4_0)
    | r2_hidden(esk4_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_85,c_0_73])).

cnf(c_0_101,plain,
    ( ~ r2_hidden(X1,X1) ),
    inference(spm,[status(thm)],[c_0_96,c_0_38])).

cnf(c_0_102,plain,
    ( r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_103,negated_conjecture,
    ( esk5_0 = esk4_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_84])).

cnf(c_0_104,negated_conjecture,
    ( r1_ordinal1(esk4_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_73]),c_0_101])).

cnf(c_0_105,plain,
    ( r2_hidden(X1,k5_xboole_0(X1,k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_52]),c_0_53]),c_0_26]),c_0_54]),c_0_55])).

cnf(c_0_106,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_103]),c_0_104]),c_0_103]),c_0_103]),c_0_103]),c_0_103]),c_0_103]),c_0_103]),c_0_103]),c_0_103]),c_0_103]),c_0_103]),c_0_105])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:00:10 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.19/0.39  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.021 s
% 0.19/0.39  # Presaturation interreduction done
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.19/0.39  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.19/0.39  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.19/0.39  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 0.19/0.39  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.39  fof(t34_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,k1_ordinal1(X2))<=>r1_ordinal1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 0.19/0.39  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 0.19/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.39  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.19/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.39  fof(t90_enumset1, axiom, ![X1, X2, X3, X4]:k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_enumset1)).
% 0.19/0.39  fof(d4_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:(X7=k4_enumset1(X1,X2,X3,X4,X5,X6)<=>![X8]:(r2_hidden(X8,X7)<=>~((((((X8!=X1&X8!=X2)&X8!=X3)&X8!=X4)&X8!=X5)&X8!=X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_enumset1)).
% 0.19/0.39  fof(t81_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_enumset1)).
% 0.19/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.39  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 0.19/0.39  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 0.19/0.39  fof(t24_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>~(((~(r2_hidden(X1,X2))&X1!=X2)&~(r2_hidden(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 0.19/0.39  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.19/0.39  fof(antisymmetry_r2_hidden, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 0.19/0.39  fof(t26_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r1_ordinal1(X1,X2)|r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 0.19/0.39  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.19/0.39  fof(t10_ordinal1, axiom, ![X1]:r2_hidden(X1,k1_ordinal1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 0.19/0.39  fof(c_0_23, plain, ![X33, X34]:r1_tarski(X33,k2_xboole_0(X33,X34)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.19/0.39  fof(c_0_24, plain, ![X35, X36]:k2_xboole_0(X35,X36)=k5_xboole_0(X35,k4_xboole_0(X36,X35)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.19/0.39  cnf(c_0_25, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.39  cnf(c_0_26, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.39  fof(c_0_27, plain, ![X26, X27]:((k4_xboole_0(X26,X27)!=k1_xboole_0|r1_tarski(X26,X27))&(~r1_tarski(X26,X27)|k4_xboole_0(X26,X27)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.19/0.39  fof(c_0_28, plain, ![X32]:k5_xboole_0(X32,k1_xboole_0)=X32, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.19/0.39  cnf(c_0_29, plain, (r1_tarski(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.39  cnf(c_0_30, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.39  cnf(c_0_31, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.39  fof(c_0_32, plain, ![X31]:r1_tarski(k1_xboole_0,X31), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.39  fof(c_0_33, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,k1_ordinal1(X2))<=>r1_ordinal1(X1,X2))))), inference(assume_negation,[status(cth)],[t34_ordinal1])).
% 0.19/0.39  fof(c_0_34, plain, ![X70]:k1_ordinal1(X70)=k2_xboole_0(X70,k1_tarski(X70)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 0.19/0.39  fof(c_0_35, plain, ![X37]:k2_tarski(X37,X37)=k1_tarski(X37), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.39  fof(c_0_36, plain, ![X28, X29, X30]:((r1_tarski(X28,X29)|~r1_tarski(X28,k4_xboole_0(X29,X30)))&(r1_xboole_0(X28,X30)|~r1_tarski(X28,k4_xboole_0(X29,X30)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 0.19/0.39  cnf(c_0_37, plain, (r1_tarski(X1,X1)|~r1_tarski(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])).
% 0.19/0.39  cnf(c_0_38, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.39  fof(c_0_39, negated_conjecture, (v3_ordinal1(esk4_0)&(v3_ordinal1(esk5_0)&((~r2_hidden(esk4_0,k1_ordinal1(esk5_0))|~r1_ordinal1(esk4_0,esk5_0))&(r2_hidden(esk4_0,k1_ordinal1(esk5_0))|r1_ordinal1(esk4_0,esk5_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_33])])])).
% 0.19/0.39  cnf(c_0_40, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.39  cnf(c_0_41, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.39  fof(c_0_42, plain, ![X38, X39]:k1_enumset1(X38,X38,X39)=k2_tarski(X38,X39), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.39  fof(c_0_43, plain, ![X40, X41, X42]:k2_enumset1(X40,X40,X41,X42)=k1_enumset1(X40,X41,X42), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.39  fof(c_0_44, plain, ![X49, X50, X51, X52]:k6_enumset1(X49,X49,X49,X49,X49,X50,X51,X52)=k2_enumset1(X49,X50,X51,X52), inference(variable_rename,[status(thm)],[t90_enumset1])).
% 0.19/0.39  fof(c_0_45, plain, ![X53, X54, X55, X56, X57, X58, X59, X60, X61, X62, X63, X64, X65, X66, X67, X68]:(((~r2_hidden(X60,X59)|(X60=X53|X60=X54|X60=X55|X60=X56|X60=X57|X60=X58)|X59!=k4_enumset1(X53,X54,X55,X56,X57,X58))&((((((X61!=X53|r2_hidden(X61,X59)|X59!=k4_enumset1(X53,X54,X55,X56,X57,X58))&(X61!=X54|r2_hidden(X61,X59)|X59!=k4_enumset1(X53,X54,X55,X56,X57,X58)))&(X61!=X55|r2_hidden(X61,X59)|X59!=k4_enumset1(X53,X54,X55,X56,X57,X58)))&(X61!=X56|r2_hidden(X61,X59)|X59!=k4_enumset1(X53,X54,X55,X56,X57,X58)))&(X61!=X57|r2_hidden(X61,X59)|X59!=k4_enumset1(X53,X54,X55,X56,X57,X58)))&(X61!=X58|r2_hidden(X61,X59)|X59!=k4_enumset1(X53,X54,X55,X56,X57,X58))))&(((((((esk3_7(X62,X63,X64,X65,X66,X67,X68)!=X62|~r2_hidden(esk3_7(X62,X63,X64,X65,X66,X67,X68),X68)|X68=k4_enumset1(X62,X63,X64,X65,X66,X67))&(esk3_7(X62,X63,X64,X65,X66,X67,X68)!=X63|~r2_hidden(esk3_7(X62,X63,X64,X65,X66,X67,X68),X68)|X68=k4_enumset1(X62,X63,X64,X65,X66,X67)))&(esk3_7(X62,X63,X64,X65,X66,X67,X68)!=X64|~r2_hidden(esk3_7(X62,X63,X64,X65,X66,X67,X68),X68)|X68=k4_enumset1(X62,X63,X64,X65,X66,X67)))&(esk3_7(X62,X63,X64,X65,X66,X67,X68)!=X65|~r2_hidden(esk3_7(X62,X63,X64,X65,X66,X67,X68),X68)|X68=k4_enumset1(X62,X63,X64,X65,X66,X67)))&(esk3_7(X62,X63,X64,X65,X66,X67,X68)!=X66|~r2_hidden(esk3_7(X62,X63,X64,X65,X66,X67,X68),X68)|X68=k4_enumset1(X62,X63,X64,X65,X66,X67)))&(esk3_7(X62,X63,X64,X65,X66,X67,X68)!=X67|~r2_hidden(esk3_7(X62,X63,X64,X65,X66,X67,X68),X68)|X68=k4_enumset1(X62,X63,X64,X65,X66,X67)))&(r2_hidden(esk3_7(X62,X63,X64,X65,X66,X67,X68),X68)|(esk3_7(X62,X63,X64,X65,X66,X67,X68)=X62|esk3_7(X62,X63,X64,X65,X66,X67,X68)=X63|esk3_7(X62,X63,X64,X65,X66,X67,X68)=X64|esk3_7(X62,X63,X64,X65,X66,X67,X68)=X65|esk3_7(X62,X63,X64,X65,X66,X67,X68)=X66|esk3_7(X62,X63,X64,X65,X66,X67,X68)=X67)|X68=k4_enumset1(X62,X63,X64,X65,X66,X67)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_enumset1])])])])])])).
% 0.19/0.39  fof(c_0_46, plain, ![X43, X44, X45, X46, X47, X48]:k6_enumset1(X43,X43,X43,X44,X45,X46,X47,X48)=k4_enumset1(X43,X44,X45,X46,X47,X48), inference(variable_rename,[status(thm)],[t81_enumset1])).
% 0.19/0.39  fof(c_0_47, plain, ![X11, X12, X13, X14, X15]:((~r1_tarski(X11,X12)|(~r2_hidden(X13,X11)|r2_hidden(X13,X12)))&((r2_hidden(esk1_2(X14,X15),X14)|r1_tarski(X14,X15))&(~r2_hidden(esk1_2(X14,X15),X15)|r1_tarski(X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.39  cnf(c_0_48, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.39  cnf(c_0_49, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.39  fof(c_0_50, plain, ![X17, X18, X19]:(((~r2_hidden(X17,X18)|~r2_hidden(X17,X19)|~r2_hidden(X17,k5_xboole_0(X18,X19)))&(r2_hidden(X17,X18)|r2_hidden(X17,X19)|~r2_hidden(X17,k5_xboole_0(X18,X19))))&((~r2_hidden(X17,X18)|r2_hidden(X17,X19)|r2_hidden(X17,k5_xboole_0(X18,X19)))&(~r2_hidden(X17,X19)|r2_hidden(X17,X18)|r2_hidden(X17,k5_xboole_0(X18,X19))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 0.19/0.39  cnf(c_0_51, negated_conjecture, (r2_hidden(esk4_0,k1_ordinal1(esk5_0))|r1_ordinal1(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.39  cnf(c_0_52, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k2_tarski(X1,X1))), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.39  cnf(c_0_53, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.39  cnf(c_0_54, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.39  cnf(c_0_55, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.39  cnf(c_0_56, plain, (X1=X3|X1=X4|X1=X5|X1=X6|X1=X7|X1=X8|~r2_hidden(X1,X2)|X2!=k4_enumset1(X3,X4,X5,X6,X7,X8)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.39  cnf(c_0_57, plain, (k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.39  cnf(c_0_58, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.39  cnf(c_0_59, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.39  cnf(c_0_60, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.39  cnf(c_0_61, negated_conjecture, (r1_ordinal1(esk4_0,esk5_0)|r2_hidden(esk4_0,k5_xboole_0(esk5_0,k4_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk5_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_52]), c_0_53]), c_0_26]), c_0_54]), c_0_55])).
% 0.19/0.39  cnf(c_0_62, plain, (X1=X8|X1=X7|X1=X6|X1=X5|X1=X4|X1=X3|X2!=k6_enumset1(X3,X3,X3,X4,X5,X6,X7,X8)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.39  cnf(c_0_63, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.39  cnf(c_0_64, negated_conjecture, (r1_ordinal1(esk4_0,esk5_0)|r2_hidden(esk4_0,k4_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk5_0))|r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.19/0.39  fof(c_0_65, plain, ![X71, X72]:((~r1_ordinal1(X71,X72)|r1_tarski(X71,X72)|(~v3_ordinal1(X71)|~v3_ordinal1(X72)))&(~r1_tarski(X71,X72)|r1_ordinal1(X71,X72)|(~v3_ordinal1(X71)|~v3_ordinal1(X72)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 0.19/0.39  cnf(c_0_66, plain, (X1=X2|X1=X3|X1=X4|X1=X5|X1=X6|X1=X7|~r2_hidden(X1,k6_enumset1(X7,X7,X7,X6,X5,X4,X3,X2))), inference(er,[status(thm)],[c_0_62])).
% 0.19/0.39  cnf(c_0_67, negated_conjecture, (r1_ordinal1(esk4_0,esk5_0)|r2_hidden(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))|r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.19/0.39  fof(c_0_68, plain, ![X74, X75]:(~v3_ordinal1(X74)|(~v3_ordinal1(X75)|(r2_hidden(X74,X75)|X74=X75|r2_hidden(X75,X74)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).
% 0.19/0.39  fof(c_0_69, plain, ![X78, X79]:(~r2_hidden(X78,X79)|~r1_tarski(X79,X78)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.19/0.39  cnf(c_0_70, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.19/0.39  cnf(c_0_71, negated_conjecture, (esk5_0=esk4_0|r1_ordinal1(esk4_0,esk5_0)|r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.19/0.39  cnf(c_0_72, negated_conjecture, (v3_ordinal1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.39  cnf(c_0_73, negated_conjecture, (v3_ordinal1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.39  fof(c_0_74, plain, ![X9, X10]:(~r2_hidden(X9,X10)|~r2_hidden(X10,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).
% 0.19/0.39  cnf(c_0_75, plain, (r2_hidden(X1,X2)|X1=X2|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.19/0.39  cnf(c_0_76, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.19/0.39  cnf(c_0_77, negated_conjecture, (esk5_0=esk4_0|r1_tarski(esk4_0,esk5_0)|r2_hidden(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72]), c_0_73])])).
% 0.19/0.39  cnf(c_0_78, plain, (~r2_hidden(X1,X2)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.19/0.39  cnf(c_0_79, negated_conjecture, (X1=esk5_0|r2_hidden(X1,esk5_0)|r2_hidden(esk5_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_75, c_0_72])).
% 0.19/0.39  cnf(c_0_80, negated_conjecture, (esk5_0=esk4_0|~r2_hidden(esk5_0,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78])).
% 0.19/0.39  fof(c_0_81, plain, ![X76, X77]:(~v3_ordinal1(X76)|(~v3_ordinal1(X77)|(r1_ordinal1(X76,X77)|r2_hidden(X77,X76)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).
% 0.19/0.39  cnf(c_0_82, negated_conjecture, (~r2_hidden(esk4_0,k1_ordinal1(esk5_0))|~r1_ordinal1(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.39  cnf(c_0_83, plain, (r2_hidden(X1,X3)|r2_hidden(X1,k5_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.39  cnf(c_0_84, negated_conjecture, (esk5_0=esk4_0|r2_hidden(esk4_0,esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_73]), c_0_80])).
% 0.19/0.39  cnf(c_0_85, plain, (r1_ordinal1(X1,X2)|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.19/0.39  fof(c_0_86, plain, ![X20, X21, X23, X24, X25]:(((r2_hidden(esk2_2(X20,X21),X20)|r1_xboole_0(X20,X21))&(r2_hidden(esk2_2(X20,X21),X21)|r1_xboole_0(X20,X21)))&(~r2_hidden(X25,X23)|~r2_hidden(X25,X24)|~r1_xboole_0(X23,X24))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.19/0.39  cnf(c_0_87, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.39  cnf(c_0_88, negated_conjecture, (~r1_ordinal1(esk4_0,esk5_0)|~r2_hidden(esk4_0,k5_xboole_0(esk5_0,k4_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk5_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_52]), c_0_53]), c_0_26]), c_0_54]), c_0_55])).
% 0.19/0.39  cnf(c_0_89, negated_conjecture, (esk5_0=esk4_0|r2_hidden(esk4_0,k5_xboole_0(esk5_0,X1))|r2_hidden(esk4_0,X1)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.19/0.39  cnf(c_0_90, negated_conjecture, (r1_ordinal1(X1,esk5_0)|r2_hidden(esk5_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_85, c_0_72])).
% 0.19/0.39  cnf(c_0_91, plain, (~r2_hidden(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X1)), inference(spm,[status(thm)],[c_0_76, c_0_29])).
% 0.19/0.39  cnf(c_0_92, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.19/0.39  cnf(c_0_93, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_87, c_0_49])).
% 0.19/0.39  cnf(c_0_94, negated_conjecture, (esk5_0=esk4_0|r2_hidden(esk4_0,k4_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk5_0))|~r1_ordinal1(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.19/0.39  cnf(c_0_95, negated_conjecture, (r1_ordinal1(esk4_0,esk5_0)|r2_hidden(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_90, c_0_73])).
% 0.19/0.39  cnf(c_0_96, plain, (~r1_tarski(X1,X2)|~r2_hidden(X2,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_30]), c_0_31])).
% 0.19/0.39  fof(c_0_97, plain, ![X73]:r2_hidden(X73,k1_ordinal1(X73)), inference(variable_rename,[status(thm)],[t10_ordinal1])).
% 0.19/0.39  cnf(c_0_98, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 0.19/0.39  cnf(c_0_99, negated_conjecture, (esk5_0=esk4_0|r2_hidden(esk4_0,k4_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_80])).
% 0.19/0.39  cnf(c_0_100, negated_conjecture, (r1_ordinal1(X1,esk4_0)|r2_hidden(esk4_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_85, c_0_73])).
% 0.19/0.39  cnf(c_0_101, plain, (~r2_hidden(X1,X1)), inference(spm,[status(thm)],[c_0_96, c_0_38])).
% 0.19/0.39  cnf(c_0_102, plain, (r2_hidden(X1,k1_ordinal1(X1))), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.19/0.39  cnf(c_0_103, negated_conjecture, (esk5_0=esk4_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_84])).
% 0.19/0.39  cnf(c_0_104, negated_conjecture, (r1_ordinal1(esk4_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_73]), c_0_101])).
% 0.19/0.39  cnf(c_0_105, plain, (r2_hidden(X1,k5_xboole_0(X1,k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102, c_0_52]), c_0_53]), c_0_26]), c_0_54]), c_0_55])).
% 0.19/0.39  cnf(c_0_106, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_103]), c_0_104]), c_0_103]), c_0_103]), c_0_103]), c_0_103]), c_0_103]), c_0_103]), c_0_103]), c_0_103]), c_0_103]), c_0_103]), c_0_105])]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 107
% 0.19/0.39  # Proof object clause steps            : 60
% 0.19/0.39  # Proof object formula steps           : 47
% 0.19/0.39  # Proof object conjectures             : 25
% 0.19/0.39  # Proof object clause conjectures      : 22
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 28
% 0.19/0.39  # Proof object initial formulas used   : 23
% 0.19/0.39  # Proof object generating inferences   : 24
% 0.19/0.39  # Proof object simplifying inferences  : 43
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 23
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 49
% 0.19/0.39  # Removed in clause preprocessing      : 7
% 0.19/0.39  # Initial clauses in saturation        : 42
% 0.19/0.39  # Processed clauses                    : 313
% 0.19/0.39  # ...of these trivial                  : 3
% 0.19/0.39  # ...subsumed                          : 88
% 0.19/0.39  # ...remaining for further processing  : 222
% 0.19/0.39  # Other redundant clauses eliminated   : 49
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 7
% 0.19/0.39  # Backward-rewritten                   : 70
% 0.19/0.39  # Generated clauses                    : 997
% 0.19/0.39  # ...of the previous two non-trivial   : 819
% 0.19/0.39  # Contextual simplify-reflections      : 5
% 0.19/0.39  # Paramodulations                      : 822
% 0.19/0.39  # Factorizations                       : 132
% 0.19/0.39  # Equation resolutions                 : 49
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 96
% 0.19/0.39  #    Positive orientable unit clauses  : 28
% 0.19/0.39  #    Positive unorientable unit clauses: 0
% 0.19/0.39  #    Negative unit clauses             : 14
% 0.19/0.39  #    Non-unit-clauses                  : 54
% 0.19/0.39  # Current number of unprocessed clauses: 561
% 0.19/0.39  # ...number of literals in the above   : 3493
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 126
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 2356
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 1356
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 50
% 0.19/0.39  # Unit Clause-clause subsumption calls : 381
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 55
% 0.19/0.39  # BW rewrite match successes           : 6
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 17728
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.043 s
% 0.19/0.39  # System time              : 0.008 s
% 0.19/0.39  # Total time               : 0.051 s
% 0.19/0.39  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
