%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relat_1__t173_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:54 EDT 2019

% Result     : Theorem 223.53s
% Output     : CNFRefutation 223.53s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 230 expanded)
%              Number of clauses        :   49 ( 114 expanded)
%              Number of leaves         :   11 (  60 expanded)
%              Depth                    :   15
%              Number of atoms          :  212 ( 804 expanded)
%              Number of equality atoms :   41 ( 143 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t173_relat_1.p',t7_boole)).

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
    file('/export/starexec/sandbox2/benchmark/relat_1__t173_relat_1.p',t3_xboole_0)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t173_relat_1.p',symmetry_r1_xboole_0)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t173_relat_1.p',dt_o_0_0_xboole_0)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t173_relat_1.p',t6_boole)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t173_relat_1.p',d4_xboole_0)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t173_relat_1.p',d7_xboole_0)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t173_relat_1.p',d5_relat_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t173_relat_1.p',t2_boole)).

fof(t166_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t173_relat_1.p',t166_relat_1)).

fof(t173_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k10_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t173_relat_1.p',t173_relat_1)).

fof(c_0_11,plain,(
    ! [X57,X58] :
      ( ~ r2_hidden(X57,X58)
      | ~ v1_xboole_0(X58) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_12,plain,(
    ! [X50,X51,X53,X54,X55] :
      ( ( r2_hidden(esk9_2(X50,X51),X50)
        | r1_xboole_0(X50,X51) )
      & ( r2_hidden(esk9_2(X50,X51),X51)
        | r1_xboole_0(X50,X51) )
      & ( ~ r2_hidden(X55,X53)
        | ~ r2_hidden(X55,X54)
        | ~ r1_xboole_0(X53,X54) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_13,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,plain,
    ( r2_hidden(esk9_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_15,plain,(
    ! [X38,X39] :
      ( ~ r1_xboole_0(X38,X39)
      | r1_xboole_0(X39,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_16,plain,
    ( r1_xboole_0(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

fof(c_0_18,plain,(
    ! [X56] :
      ( ~ v1_xboole_0(X56)
      | X56 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_19,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( r1_xboole_0(X1,o_0_0_xboole_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X14,X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | ~ r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk3_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk3_3(X16,X17,X18),X16)
        | ~ r2_hidden(esk3_3(X16,X17,X18),X17)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk3_3(X16,X17,X18),X16)
        | r2_hidden(esk3_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk3_3(X16,X17,X18),X17)
        | r2_hidden(esk3_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_23,plain,(
    ! [X31,X32] :
      ( ( ~ r1_xboole_0(X31,X32)
        | k3_xboole_0(X31,X32) = k1_xboole_0 )
      & ( k3_xboole_0(X31,X32) != k1_xboole_0
        | r1_xboole_0(X31,X32) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_24,plain,
    ( r1_xboole_0(o_0_0_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_17])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_29,plain,(
    ! [X20,X21,X22,X24,X25,X26,X27,X29] :
      ( ( ~ r2_hidden(X22,X21)
        | r2_hidden(k4_tarski(esk4_3(X20,X21,X22),X22),X20)
        | X21 != k2_relat_1(X20) )
      & ( ~ r2_hidden(k4_tarski(X25,X24),X20)
        | r2_hidden(X24,X21)
        | X21 != k2_relat_1(X20) )
      & ( ~ r2_hidden(esk5_2(X26,X27),X27)
        | ~ r2_hidden(k4_tarski(X29,esk5_2(X26,X27)),X26)
        | X27 = k2_relat_1(X26) )
      & ( r2_hidden(esk5_2(X26,X27),X27)
        | r2_hidden(k4_tarski(esk6_2(X26,X27),esk5_2(X26,X27)),X26)
        | X27 = k2_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_32,plain,(
    ! [X47] : k3_xboole_0(X47,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_33,plain,(
    ! [X40,X41,X42,X44] :
      ( ( r2_hidden(esk8_3(X40,X41,X42),k2_relat_1(X42))
        | ~ r2_hidden(X40,k10_relat_1(X42,X41))
        | ~ v1_relat_1(X42) )
      & ( r2_hidden(k4_tarski(X40,esk8_3(X40,X41,X42)),X42)
        | ~ r2_hidden(X40,k10_relat_1(X42,X41))
        | ~ v1_relat_1(X42) )
      & ( r2_hidden(esk8_3(X40,X41,X42),X41)
        | ~ r2_hidden(X40,k10_relat_1(X42,X41))
        | ~ v1_relat_1(X42) )
      & ( ~ r2_hidden(X44,k2_relat_1(X42))
        | ~ r2_hidden(k4_tarski(X40,X44),X42)
        | ~ r2_hidden(X44,X41)
        | r2_hidden(X40,k10_relat_1(X42,X41))
        | ~ v1_relat_1(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

cnf(c_0_34,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( r2_hidden(k4_tarski(esk4_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
    | r2_hidden(esk3_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_38,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( r2_hidden(esk8_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,plain,
    ( r2_hidden(X3,k10_relat_1(X2,X4))
    | ~ r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( r2_hidden(k4_tarski(esk4_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_3(X2,k1_xboole_0,X1),X1)
    | r2_hidden(esk3_3(X2,k1_xboole_0,X1),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_45,plain,
    ( r2_hidden(esk8_3(esk9_2(X1,k10_relat_1(X2,X3)),X3,X2),X3)
    | r1_xboole_0(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_14])).

cnf(c_0_46,plain,
    ( r2_hidden(esk8_3(X1,X2,X3),k2_relat_1(X3))
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_47,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( k10_relat_1(X2,X1) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t173_relat_1])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,X3)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_49,plain,
    ( r2_hidden(k4_tarski(esk4_3(X1,k2_relat_1(X1),esk9_2(X2,k2_relat_1(X1))),esk9_2(X2,k2_relat_1(X1))),X1)
    | r1_xboole_0(X2,k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_14])).

cnf(c_0_50,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_3(X2,k1_xboole_0,X1),X1) ),
    inference(ef,[status(thm)],[c_0_43])).

cnf(c_0_51,plain,
    ( r1_xboole_0(X1,k10_relat_1(X2,X3))
    | ~ r2_hidden(esk8_3(esk9_2(X1,k10_relat_1(X2,X3)),X3,X2),X4)
    | ~ r1_xboole_0(X4,X3)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_52,plain,
    ( r2_hidden(esk8_3(esk9_2(X1,k10_relat_1(X2,X3)),X3,X2),k2_relat_1(X2))
    | r1_xboole_0(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_14])).

fof(c_0_53,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & ( k10_relat_1(esk2_0,esk1_0) != k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(esk2_0),esk1_0) )
    & ( k10_relat_1(esk2_0,esk1_0) = k1_xboole_0
      | r1_xboole_0(k2_relat_1(esk2_0),esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_47])])])).

cnf(c_0_54,plain,
    ( r2_hidden(esk4_3(X1,k2_relat_1(X1),esk9_2(X2,k2_relat_1(X1))),k10_relat_1(X1,X3))
    | r1_xboole_0(X2,k2_relat_1(X1))
    | ~ r2_hidden(esk9_2(X2,k2_relat_1(X1)),X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_55,plain,
    ( r2_hidden(esk9_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_56,plain,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(esk3_3(X2,k1_xboole_0,X1),X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_50])).

cnf(c_0_57,plain,
    ( X1 = k3_xboole_0(X2,X3)
    | r2_hidden(esk3_3(X2,X3,X1),X1)
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_13,c_0_37])).

cnf(c_0_58,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_17,c_0_25])).

cnf(c_0_59,plain,
    ( r1_xboole_0(X1,k10_relat_1(X2,X3))
    | ~ r1_xboole_0(k2_relat_1(X2),X3)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( k10_relat_1(esk2_0,esk1_0) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(esk2_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_61,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_62,plain,
    ( r2_hidden(esk4_3(X1,k2_relat_1(X1),esk9_2(X2,k2_relat_1(X1))),k10_relat_1(X1,X2))
    | r1_xboole_0(X2,k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_63,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_38]),c_0_58])])).

cnf(c_0_64,negated_conjecture,
    ( k10_relat_1(esk2_0,esk1_0) = k1_xboole_0
    | r1_xboole_0(X1,k10_relat_1(esk2_0,esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])])).

cnf(c_0_65,plain,
    ( r1_xboole_0(X1,k2_relat_1(X2))
    | ~ v1_xboole_0(k10_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( k10_relat_1(esk2_0,esk1_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_67,negated_conjecture,
    ( k10_relat_1(esk2_0,esk1_0) != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(esk2_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_68,negated_conjecture,
    ( r1_xboole_0(esk1_0,k2_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_58]),c_0_61])])).

cnf(c_0_69,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_66])])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_68]),c_0_69]),
    [proof]).
%------------------------------------------------------------------------------
