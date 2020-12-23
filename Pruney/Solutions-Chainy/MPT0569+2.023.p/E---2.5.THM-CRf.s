%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:36 EST 2020

% Result     : Theorem 0.38s
% Output     : CNFRefutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 177 expanded)
%              Number of clauses        :   37 (  79 expanded)
%              Number of leaves         :   13 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :  167 ( 440 expanded)
%              Number of equality atoms :   48 ( 136 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t173_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k10_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(t168_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,X1) = k10_relat_1(X2,k3_xboole_0(k2_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

fof(t72_xboole_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X4,X2) )
     => X3 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t166_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(t171_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(c_0_13,plain,(
    ! [X17,X18,X20,X21,X22] :
      ( ( r1_xboole_0(X17,X18)
        | r2_hidden(esk3_2(X17,X18),k3_xboole_0(X17,X18)) )
      & ( ~ r2_hidden(X22,k3_xboole_0(X20,X21))
        | ~ r1_xboole_0(X20,X21) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_14,plain,(
    ! [X25,X26] : k4_xboole_0(X25,k4_xboole_0(X25,X26)) = k3_xboole_0(X25,X26) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_15,plain,(
    ! [X36,X37] :
      ( ( ~ r1_xboole_0(X36,X37)
        | k4_xboole_0(X36,X37) = X36 )
      & ( k4_xboole_0(X36,X37) != X36
        | r1_xboole_0(X36,X37) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_16,plain,(
    ! [X31] : r1_xboole_0(X31,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( k10_relat_1(X2,X1) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t173_relat_1])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X48,X49,X50,X52,X53,X54,X55,X57] :
      ( ( ~ r2_hidden(X50,X49)
        | r2_hidden(k4_tarski(esk4_3(X48,X49,X50),X50),X48)
        | X49 != k2_relat_1(X48) )
      & ( ~ r2_hidden(k4_tarski(X53,X52),X48)
        | r2_hidden(X52,X49)
        | X49 != k2_relat_1(X48) )
      & ( ~ r2_hidden(esk5_2(X54,X55),X55)
        | ~ r2_hidden(k4_tarski(X57,esk5_2(X54,X55)),X54)
        | X55 = k2_relat_1(X54) )
      & ( r2_hidden(esk5_2(X54,X55),X55)
        | r2_hidden(k4_tarski(esk6_2(X54,X55),esk5_2(X54,X55)),X54)
        | X55 = k2_relat_1(X54) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

fof(c_0_23,plain,(
    ! [X64,X65] :
      ( ~ v1_relat_1(X65)
      | k10_relat_1(X65,X64) = k10_relat_1(X65,k3_xboole_0(k2_relat_1(X65),X64)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_relat_1])])).

fof(c_0_24,negated_conjecture,
    ( v1_relat_1(esk9_0)
    & ( k10_relat_1(esk9_0,esk8_0) != k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(esk9_0),esk8_0) )
    & ( k10_relat_1(esk9_0,esk8_0) = k1_xboole_0
      | r1_xboole_0(k2_relat_1(esk9_0),esk8_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_25,plain,(
    ! [X32,X33,X34,X35] :
      ( k2_xboole_0(X32,X33) != k2_xboole_0(X34,X35)
      | ~ r1_xboole_0(X34,X32)
      | ~ r1_xboole_0(X35,X33)
      | X34 = X33 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t72_xboole_1])])).

fof(c_0_26,plain,(
    ! [X23] : k2_xboole_0(X23,k1_xboole_0) = X23 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_27,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_29,plain,(
    ! [X11,X12,X14,X15,X16] :
      ( ( r2_hidden(esk2_2(X11,X12),X11)
        | r1_xboole_0(X11,X12) )
      & ( r2_hidden(esk2_2(X11,X12),X12)
        | r1_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X16,X14)
        | ~ r2_hidden(X16,X15)
        | ~ r1_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_30,plain,(
    ! [X59,X60,X61,X63] :
      ( ( r2_hidden(esk7_3(X59,X60,X61),k2_relat_1(X61))
        | ~ r2_hidden(X59,k10_relat_1(X61,X60))
        | ~ v1_relat_1(X61) )
      & ( r2_hidden(k4_tarski(X59,esk7_3(X59,X60,X61)),X61)
        | ~ r2_hidden(X59,k10_relat_1(X61,X60))
        | ~ v1_relat_1(X61) )
      & ( r2_hidden(esk7_3(X59,X60,X61),X60)
        | ~ r2_hidden(X59,k10_relat_1(X61,X60))
        | ~ v1_relat_1(X61) )
      & ( ~ r2_hidden(X63,k2_relat_1(X61))
        | ~ r2_hidden(k4_tarski(X59,X63),X61)
        | ~ r2_hidden(X63,X60)
        | r2_hidden(X59,k10_relat_1(X61,X60))
        | ~ v1_relat_1(X61) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

cnf(c_0_31,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k10_relat_1(X1,X2) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( k10_relat_1(esk9_0,esk8_0) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(esk9_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( X3 = X2
    | k2_xboole_0(X1,X2) != k2_xboole_0(X3,X4)
    | ~ r1_xboole_0(X3,X1)
    | ~ r1_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_21])])).

cnf(c_0_37,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_38,plain,(
    ! [X66] :
      ( ~ v1_relat_1(X66)
      | k10_relat_1(X66,k1_xboole_0) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t171_relat_1])])).

cnf(c_0_39,plain,
    ( r2_hidden(X3,k10_relat_1(X2,X4))
    | ~ r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( r2_hidden(k4_tarski(esk4_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_42,plain,
    ( k10_relat_1(X1,X2) = k10_relat_1(X1,k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_32,c_0_19])).

cnf(c_0_43,negated_conjecture,
    ( k4_xboole_0(k2_relat_1(esk9_0),esk8_0) = k2_relat_1(esk9_0)
    | k10_relat_1(esk9_0,esk8_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_33])).

cnf(c_0_44,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_45,plain,
    ( k1_xboole_0 = X1
    | ~ r1_xboole_0(X1,k2_xboole_0(X1,X2)) ),
    inference(er,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_21]),c_0_35])])).

cnf(c_0_46,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_47,plain,
    ( k10_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_48,plain,(
    ! [X27] : k4_xboole_0(k1_xboole_0,X27) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(csr,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_50,plain,
    ( r2_hidden(k4_tarski(esk4_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_51,negated_conjecture,
    ( k10_relat_1(esk9_0,k4_xboole_0(k2_relat_1(esk9_0),k2_relat_1(esk9_0))) = k10_relat_1(esk9_0,esk8_0)
    | k10_relat_1(esk9_0,esk8_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])])).

cnf(c_0_52,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( k10_relat_1(esk9_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_44])).

cnf(c_0_54,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_55,plain,
    ( r2_hidden(esk4_3(X1,k2_relat_1(X1),X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( k10_relat_1(esk9_0,esk8_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52]),c_0_53])])).

cnf(c_0_57,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( ~ r2_hidden(X1,k2_relat_1(esk9_0))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_44])]),c_0_57])).

cnf(c_0_59,negated_conjecture,
    ( k10_relat_1(esk9_0,esk8_0) != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(esk9_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_60,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(esk9_0),X1)
    | ~ r2_hidden(esk2_2(k2_relat_1(esk9_0),X1),esk8_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_37])).

cnf(c_0_61,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_62,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(esk9_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_56])])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:14:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.38/0.59  # AutoSched0-Mode selected heuristic G_E___208_B01_00_F1_SE_CS_SP_PS_S04AN
% 0.38/0.59  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.38/0.59  #
% 0.38/0.59  # Preprocessing time       : 0.028 s
% 0.38/0.59  # Presaturation interreduction done
% 0.38/0.59  
% 0.38/0.59  # Proof found!
% 0.38/0.59  # SZS status Theorem
% 0.38/0.59  # SZS output start CNFRefutation
% 0.38/0.59  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.38/0.59  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.38/0.59  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.38/0.59  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.38/0.59  fof(t173_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 0.38/0.59  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 0.38/0.59  fof(t168_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k10_relat_1(X2,X1)=k10_relat_1(X2,k3_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 0.38/0.59  fof(t72_xboole_1, axiom, ![X1, X2, X3, X4]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)&r1_xboole_0(X3,X1))&r1_xboole_0(X4,X2))=>X3=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_xboole_1)).
% 0.38/0.59  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.38/0.59  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.38/0.59  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 0.38/0.59  fof(t171_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_relat_1)).
% 0.38/0.59  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 0.38/0.59  fof(c_0_13, plain, ![X17, X18, X20, X21, X22]:((r1_xboole_0(X17,X18)|r2_hidden(esk3_2(X17,X18),k3_xboole_0(X17,X18)))&(~r2_hidden(X22,k3_xboole_0(X20,X21))|~r1_xboole_0(X20,X21))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.38/0.59  fof(c_0_14, plain, ![X25, X26]:k4_xboole_0(X25,k4_xboole_0(X25,X26))=k3_xboole_0(X25,X26), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.38/0.59  fof(c_0_15, plain, ![X36, X37]:((~r1_xboole_0(X36,X37)|k4_xboole_0(X36,X37)=X36)&(k4_xboole_0(X36,X37)!=X36|r1_xboole_0(X36,X37))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.38/0.59  fof(c_0_16, plain, ![X31]:r1_xboole_0(X31,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.38/0.59  fof(c_0_17, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1)))), inference(assume_negation,[status(cth)],[t173_relat_1])).
% 0.38/0.59  cnf(c_0_18, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.38/0.59  cnf(c_0_19, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.38/0.59  cnf(c_0_20, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.38/0.59  cnf(c_0_21, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.38/0.59  fof(c_0_22, plain, ![X48, X49, X50, X52, X53, X54, X55, X57]:(((~r2_hidden(X50,X49)|r2_hidden(k4_tarski(esk4_3(X48,X49,X50),X50),X48)|X49!=k2_relat_1(X48))&(~r2_hidden(k4_tarski(X53,X52),X48)|r2_hidden(X52,X49)|X49!=k2_relat_1(X48)))&((~r2_hidden(esk5_2(X54,X55),X55)|~r2_hidden(k4_tarski(X57,esk5_2(X54,X55)),X54)|X55=k2_relat_1(X54))&(r2_hidden(esk5_2(X54,X55),X55)|r2_hidden(k4_tarski(esk6_2(X54,X55),esk5_2(X54,X55)),X54)|X55=k2_relat_1(X54)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.38/0.59  fof(c_0_23, plain, ![X64, X65]:(~v1_relat_1(X65)|k10_relat_1(X65,X64)=k10_relat_1(X65,k3_xboole_0(k2_relat_1(X65),X64))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_relat_1])])).
% 0.38/0.59  fof(c_0_24, negated_conjecture, (v1_relat_1(esk9_0)&((k10_relat_1(esk9_0,esk8_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk9_0),esk8_0))&(k10_relat_1(esk9_0,esk8_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk9_0),esk8_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.38/0.59  fof(c_0_25, plain, ![X32, X33, X34, X35]:(k2_xboole_0(X32,X33)!=k2_xboole_0(X34,X35)|~r1_xboole_0(X34,X32)|~r1_xboole_0(X35,X33)|X34=X33), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t72_xboole_1])])).
% 0.38/0.59  fof(c_0_26, plain, ![X23]:k2_xboole_0(X23,k1_xboole_0)=X23, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.38/0.59  cnf(c_0_27, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.38/0.59  cnf(c_0_28, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.38/0.59  fof(c_0_29, plain, ![X11, X12, X14, X15, X16]:(((r2_hidden(esk2_2(X11,X12),X11)|r1_xboole_0(X11,X12))&(r2_hidden(esk2_2(X11,X12),X12)|r1_xboole_0(X11,X12)))&(~r2_hidden(X16,X14)|~r2_hidden(X16,X15)|~r1_xboole_0(X14,X15))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.38/0.59  fof(c_0_30, plain, ![X59, X60, X61, X63]:((((r2_hidden(esk7_3(X59,X60,X61),k2_relat_1(X61))|~r2_hidden(X59,k10_relat_1(X61,X60))|~v1_relat_1(X61))&(r2_hidden(k4_tarski(X59,esk7_3(X59,X60,X61)),X61)|~r2_hidden(X59,k10_relat_1(X61,X60))|~v1_relat_1(X61)))&(r2_hidden(esk7_3(X59,X60,X61),X60)|~r2_hidden(X59,k10_relat_1(X61,X60))|~v1_relat_1(X61)))&(~r2_hidden(X63,k2_relat_1(X61))|~r2_hidden(k4_tarski(X59,X63),X61)|~r2_hidden(X63,X60)|r2_hidden(X59,k10_relat_1(X61,X60))|~v1_relat_1(X61))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.38/0.59  cnf(c_0_31, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.38/0.59  cnf(c_0_32, plain, (k10_relat_1(X1,X2)=k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.38/0.59  cnf(c_0_33, negated_conjecture, (k10_relat_1(esk9_0,esk8_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk9_0),esk8_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.38/0.59  cnf(c_0_34, plain, (X3=X2|k2_xboole_0(X1,X2)!=k2_xboole_0(X3,X4)|~r1_xboole_0(X3,X1)|~r1_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.38/0.59  cnf(c_0_35, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.38/0.59  cnf(c_0_36, plain, (~r2_hidden(X1,k4_xboole_0(X2,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_21])])).
% 0.38/0.59  cnf(c_0_37, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.38/0.59  fof(c_0_38, plain, ![X66]:(~v1_relat_1(X66)|k10_relat_1(X66,k1_xboole_0)=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t171_relat_1])])).
% 0.38/0.59  cnf(c_0_39, plain, (r2_hidden(X3,k10_relat_1(X2,X4))|~r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,X4)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.38/0.59  cnf(c_0_40, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)), inference(er,[status(thm)],[c_0_31])).
% 0.38/0.59  cnf(c_0_41, plain, (r2_hidden(k4_tarski(esk4_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.38/0.59  cnf(c_0_42, plain, (k10_relat_1(X1,X2)=k10_relat_1(X1,k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_32, c_0_19])).
% 0.38/0.59  cnf(c_0_43, negated_conjecture, (k4_xboole_0(k2_relat_1(esk9_0),esk8_0)=k2_relat_1(esk9_0)|k10_relat_1(esk9_0,esk8_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_20, c_0_33])).
% 0.38/0.59  cnf(c_0_44, negated_conjecture, (v1_relat_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.38/0.59  cnf(c_0_45, plain, (k1_xboole_0=X1|~r1_xboole_0(X1,k2_xboole_0(X1,X2))), inference(er,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_21]), c_0_35])])).
% 0.38/0.59  cnf(c_0_46, plain, (r1_xboole_0(k4_xboole_0(X1,X1),X2)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.38/0.59  cnf(c_0_47, plain, (k10_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.38/0.59  fof(c_0_48, plain, ![X27]:k4_xboole_0(k1_xboole_0,X27)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.38/0.59  cnf(c_0_49, plain, (r2_hidden(X1,k10_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X4),X2)|~r2_hidden(X4,X3)), inference(csr,[status(thm)],[c_0_39, c_0_40])).
% 0.38/0.59  cnf(c_0_50, plain, (r2_hidden(k4_tarski(esk4_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_41])).
% 0.38/0.59  cnf(c_0_51, negated_conjecture, (k10_relat_1(esk9_0,k4_xboole_0(k2_relat_1(esk9_0),k2_relat_1(esk9_0)))=k10_relat_1(esk9_0,esk8_0)|k10_relat_1(esk9_0,esk8_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])])).
% 0.38/0.59  cnf(c_0_52, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.38/0.59  cnf(c_0_53, negated_conjecture, (k10_relat_1(esk9_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_47, c_0_44])).
% 0.38/0.59  cnf(c_0_54, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.38/0.59  cnf(c_0_55, plain, (r2_hidden(esk4_3(X1,k2_relat_1(X1),X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.38/0.59  cnf(c_0_56, negated_conjecture, (k10_relat_1(esk9_0,esk8_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_52]), c_0_53])])).
% 0.38/0.59  cnf(c_0_57, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_36, c_0_54])).
% 0.38/0.59  cnf(c_0_58, negated_conjecture, (~r2_hidden(X1,k2_relat_1(esk9_0))|~r2_hidden(X1,esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_44])]), c_0_57])).
% 0.38/0.59  cnf(c_0_59, negated_conjecture, (k10_relat_1(esk9_0,esk8_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk9_0),esk8_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.38/0.59  cnf(c_0_60, negated_conjecture, (r1_xboole_0(k2_relat_1(esk9_0),X1)|~r2_hidden(esk2_2(k2_relat_1(esk9_0),X1),esk8_0)), inference(spm,[status(thm)],[c_0_58, c_0_37])).
% 0.38/0.59  cnf(c_0_61, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.38/0.59  cnf(c_0_62, negated_conjecture, (~r1_xboole_0(k2_relat_1(esk9_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_56])])).
% 0.38/0.59  cnf(c_0_63, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62]), ['proof']).
% 0.38/0.59  # SZS output end CNFRefutation
% 0.38/0.59  # Proof object total steps             : 64
% 0.38/0.59  # Proof object clause steps            : 37
% 0.38/0.59  # Proof object formula steps           : 27
% 0.38/0.59  # Proof object conjectures             : 14
% 0.38/0.59  # Proof object clause conjectures      : 11
% 0.38/0.59  # Proof object formula conjectures     : 3
% 0.38/0.59  # Proof object initial clauses used    : 17
% 0.38/0.59  # Proof object initial formulas used   : 13
% 0.38/0.59  # Proof object generating inferences   : 13
% 0.38/0.59  # Proof object simplifying inferences  : 20
% 0.38/0.59  # Training examples: 0 positive, 0 negative
% 0.38/0.59  # Parsed axioms                        : 22
% 0.38/0.59  # Removed by relevancy pruning/SinE    : 0
% 0.38/0.59  # Initial clauses                      : 36
% 0.38/0.59  # Removed in clause preprocessing      : 2
% 0.38/0.59  # Initial clauses in saturation        : 34
% 0.38/0.59  # Processed clauses                    : 2852
% 0.38/0.59  # ...of these trivial                  : 6
% 0.38/0.59  # ...subsumed                          : 2328
% 0.38/0.59  # ...remaining for further processing  : 518
% 0.38/0.59  # Other redundant clauses eliminated   : 244
% 0.38/0.59  # Clauses deleted for lack of memory   : 0
% 0.38/0.59  # Backward-subsumed                    : 1
% 0.38/0.59  # Backward-rewritten                   : 35
% 0.38/0.59  # Generated clauses                    : 14025
% 0.38/0.59  # ...of the previous two non-trivial   : 10581
% 0.38/0.59  # Contextual simplify-reflections      : 1
% 0.38/0.59  # Paramodulations                      : 13763
% 0.38/0.59  # Factorizations                       : 12
% 0.38/0.59  # Equation resolutions                 : 250
% 0.38/0.59  # Propositional unsat checks           : 0
% 0.38/0.59  #    Propositional check models        : 0
% 0.38/0.59  #    Propositional check unsatisfiable : 0
% 0.38/0.59  #    Propositional clauses             : 0
% 0.38/0.59  #    Propositional clauses after purity: 0
% 0.38/0.59  #    Propositional unsat core size     : 0
% 0.38/0.59  #    Propositional preprocessing time  : 0.000
% 0.38/0.59  #    Propositional encoding time       : 0.000
% 0.38/0.59  #    Propositional solver time         : 0.000
% 0.38/0.59  #    Success case prop preproc time    : 0.000
% 0.38/0.59  #    Success case prop encoding time   : 0.000
% 0.38/0.59  #    Success case prop solver time     : 0.000
% 0.38/0.59  # Current number of processed clauses  : 444
% 0.38/0.59  #    Positive orientable unit clauses  : 18
% 0.38/0.59  #    Positive unorientable unit clauses: 0
% 0.38/0.59  #    Negative unit clauses             : 12
% 0.38/0.59  #    Non-unit-clauses                  : 414
% 0.38/0.59  # Current number of unprocessed clauses: 7700
% 0.38/0.59  # ...number of literals in the above   : 27258
% 0.38/0.59  # Current number of archived formulas  : 0
% 0.38/0.59  # Current number of archived clauses   : 72
% 0.38/0.59  # Clause-clause subsumption calls (NU) : 22261
% 0.38/0.59  # Rec. Clause-clause subsumption calls : 14227
% 0.38/0.59  # Non-unit clause-clause subsumptions  : 1473
% 0.38/0.59  # Unit Clause-clause subsumption calls : 98
% 0.38/0.59  # Rewrite failures with RHS unbound    : 0
% 0.38/0.59  # BW rewrite match attempts            : 32
% 0.38/0.59  # BW rewrite match successes           : 10
% 0.38/0.59  # Condensation attempts                : 0
% 0.38/0.59  # Condensation successes               : 0
% 0.38/0.59  # Termbank termtop insertions          : 194915
% 0.38/0.59  
% 0.38/0.59  # -------------------------------------------------
% 0.38/0.59  # User time                : 0.229 s
% 0.38/0.59  # System time              : 0.015 s
% 0.38/0.59  # Total time               : 0.245 s
% 0.38/0.59  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
