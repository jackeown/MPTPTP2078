%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:33 EST 2020

% Result     : Theorem 0.88s
% Output     : CNFRefutation 0.88s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 558 expanded)
%              Number of clauses        :   59 ( 263 expanded)
%              Number of leaves         :   14 ( 141 expanded)
%              Depth                    :   12
%              Number of atoms          :  250 (1158 expanded)
%              Number of equality atoms :   76 ( 507 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t173_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k10_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(l24_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_xboole_0(k1_tarski(X1),X2)
        & r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(t166_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(t168_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,X1) = k10_relat_1(X2,k3_xboole_0(k2_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(d14_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k10_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(k4_tarski(X4,X5),X1)
                  & r2_hidden(X5,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(c_0_14,plain,(
    ! [X19,X20,X22,X23,X24] :
      ( ( r1_xboole_0(X19,X20)
        | r2_hidden(esk2_2(X19,X20),k3_xboole_0(X19,X20)) )
      & ( ~ r2_hidden(X24,k3_xboole_0(X22,X23))
        | ~ r1_xboole_0(X22,X23) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_15,plain,(
    ! [X32,X33] : k1_setfam_1(k2_tarski(X32,X33)) = k3_xboole_0(X32,X33) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_16,plain,(
    ! [X17,X18] :
      ( ( ~ r1_xboole_0(X17,X18)
        | k3_xboole_0(X17,X18) = k1_xboole_0 )
      & ( k3_xboole_0(X17,X18) != k1_xboole_0
        | r1_xboole_0(X17,X18) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_17,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X27,X28] : k4_xboole_0(X27,k4_xboole_0(X27,X28)) = k3_xboole_0(X27,X28) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( k10_relat_1(X2,X1) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t173_relat_1])).

fof(c_0_22,plain,(
    ! [X30,X31] :
      ( ~ r1_xboole_0(k1_tarski(X30),X31)
      | ~ r2_hidden(X30,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).

fof(c_0_23,plain,(
    ! [X29] : r1_xboole_0(X29,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_24,plain,(
    ! [X46,X47,X48,X50,X51,X52,X53,X55] :
      ( ( ~ r2_hidden(X48,X47)
        | r2_hidden(k4_tarski(esk7_3(X46,X47,X48),X48),X46)
        | X47 != k2_relat_1(X46) )
      & ( ~ r2_hidden(k4_tarski(X51,X50),X46)
        | r2_hidden(X50,X47)
        | X47 != k2_relat_1(X46) )
      & ( ~ r2_hidden(esk8_2(X52,X53),X53)
        | ~ r2_hidden(k4_tarski(X55,esk8_2(X52,X53)),X52)
        | X53 = k2_relat_1(X52) )
      & ( r2_hidden(esk8_2(X52,X53),X53)
        | r2_hidden(k4_tarski(esk9_2(X52,X53),esk8_2(X52,X53)),X52)
        | X53 = k2_relat_1(X52) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_25,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_26,plain,
    ( r1_xboole_0(X1,X2)
    | k1_setfam_1(k2_tarski(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_19,c_0_18])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_28,plain,(
    ! [X57,X58,X59,X61] :
      ( ( r2_hidden(esk10_3(X57,X58,X59),k2_relat_1(X59))
        | ~ r2_hidden(X57,k10_relat_1(X59,X58))
        | ~ v1_relat_1(X59) )
      & ( r2_hidden(k4_tarski(X57,esk10_3(X57,X58,X59)),X59)
        | ~ r2_hidden(X57,k10_relat_1(X59,X58))
        | ~ v1_relat_1(X59) )
      & ( r2_hidden(esk10_3(X57,X58,X59),X58)
        | ~ r2_hidden(X57,k10_relat_1(X59,X58))
        | ~ v1_relat_1(X59) )
      & ( ~ r2_hidden(X61,k2_relat_1(X59))
        | ~ r2_hidden(k4_tarski(X57,X61),X59)
        | ~ r2_hidden(X61,X58)
        | r2_hidden(X57,k10_relat_1(X59,X58))
        | ~ v1_relat_1(X59) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

fof(c_0_29,negated_conjecture,
    ( v1_relat_1(esk12_0)
    & ( k10_relat_1(esk12_0,esk11_0) != k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(esk12_0),esk11_0) )
    & ( k10_relat_1(esk12_0,esk11_0) = k1_xboole_0
      | r1_xboole_0(k2_relat_1(esk12_0),esk11_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

fof(c_0_30,plain,(
    ! [X62,X63] :
      ( ~ v1_relat_1(X63)
      | k10_relat_1(X63,X62) = k10_relat_1(X63,k3_xboole_0(k2_relat_1(X63),X62)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_relat_1])])).

cnf(c_0_31,plain,
    ( ~ r1_xboole_0(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( r2_hidden(k4_tarski(esk7_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) != k1_xboole_0
    | ~ r2_hidden(X3,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_27,c_0_18])).

cnf(c_0_36,plain,
    ( r2_hidden(esk10_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( v1_relat_1(esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( k10_relat_1(X1,X2) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,plain,
    ( r2_hidden(k4_tarski(esk7_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_33])).

fof(c_0_41,plain,(
    ! [X25] :
      ( X25 = k1_xboole_0
      | r2_hidden(esk3_1(X25),X25) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_42,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k1_xboole_0
    | ~ r2_hidden(X3,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk10_3(X1,X2,esk12_0),X2)
    | ~ r2_hidden(X1,k10_relat_1(esk12_0,X2)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_45,plain,
    ( k10_relat_1(X1,X2) = k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_38,c_0_18])).

cnf(c_0_46,plain,
    ( ~ r2_hidden(X1,k2_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_49,plain,(
    ! [X34,X35,X36,X37,X39,X40,X41,X42,X44] :
      ( ( r2_hidden(k4_tarski(X37,esk4_4(X34,X35,X36,X37)),X34)
        | ~ r2_hidden(X37,X36)
        | X36 != k10_relat_1(X34,X35)
        | ~ v1_relat_1(X34) )
      & ( r2_hidden(esk4_4(X34,X35,X36,X37),X35)
        | ~ r2_hidden(X37,X36)
        | X36 != k10_relat_1(X34,X35)
        | ~ v1_relat_1(X34) )
      & ( ~ r2_hidden(k4_tarski(X39,X40),X34)
        | ~ r2_hidden(X40,X35)
        | r2_hidden(X39,X36)
        | X36 != k10_relat_1(X34,X35)
        | ~ v1_relat_1(X34) )
      & ( ~ r2_hidden(esk5_3(X34,X41,X42),X42)
        | ~ r2_hidden(k4_tarski(esk5_3(X34,X41,X42),X44),X34)
        | ~ r2_hidden(X44,X41)
        | X42 = k10_relat_1(X34,X41)
        | ~ v1_relat_1(X34) )
      & ( r2_hidden(k4_tarski(esk5_3(X34,X41,X42),esk6_3(X34,X41,X42)),X34)
        | r2_hidden(esk5_3(X34,X41,X42),X42)
        | X42 = k10_relat_1(X34,X41)
        | ~ v1_relat_1(X34) )
      & ( r2_hidden(esk6_3(X34,X41,X42),X41)
        | r2_hidden(esk5_3(X34,X41,X42),X42)
        | X42 = k10_relat_1(X34,X41)
        | ~ v1_relat_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

cnf(c_0_50,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k1_xboole_0
    | ~ r2_hidden(X3,k10_relat_1(esk12_0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( k10_relat_1(esk12_0,k4_xboole_0(k2_relat_1(esk12_0),k4_xboole_0(k2_relat_1(esk12_0),X1))) = k10_relat_1(esk12_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_37]),c_0_35])).

cnf(c_0_52,plain,
    ( r2_hidden(esk8_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk9_2(X1,X2),esk8_2(X1,X2)),X1)
    | X2 = k2_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_53,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_54,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k1_setfam_1(k2_tarski(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_18]),c_0_18])).

cnf(c_0_55,negated_conjecture,
    ( k10_relat_1(esk12_0,esk11_0) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(esk12_0),esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_56,plain,(
    ! [X8,X9,X10,X11,X12,X13,X14,X15] :
      ( ( r2_hidden(X11,X8)
        | ~ r2_hidden(X11,X10)
        | X10 != k4_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X11,X9)
        | ~ r2_hidden(X11,X10)
        | X10 != k4_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X12,X8)
        | r2_hidden(X12,X9)
        | r2_hidden(X12,X10)
        | X10 != k4_xboole_0(X8,X9) )
      & ( ~ r2_hidden(esk1_3(X13,X14,X15),X15)
        | ~ r2_hidden(esk1_3(X13,X14,X15),X13)
        | r2_hidden(esk1_3(X13,X14,X15),X14)
        | X15 = k4_xboole_0(X13,X14) )
      & ( r2_hidden(esk1_3(X13,X14,X15),X13)
        | r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k4_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk1_3(X13,X14,X15),X14)
        | r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k4_xboole_0(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_57,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X5 != k10_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,negated_conjecture,
    ( k4_xboole_0(k2_relat_1(esk12_0),k4_xboole_0(k2_relat_1(esk12_0),X1)) != k1_xboole_0
    | ~ r2_hidden(X2,k10_relat_1(esk12_0,X1)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_60,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk8_2(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_52]),c_0_53])).

cnf(c_0_61,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k2_tarski(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_35])).

cnf(c_0_62,negated_conjecture,
    ( k10_relat_1(esk12_0,esk11_0) = k1_xboole_0
    | ~ r2_hidden(X1,k1_setfam_1(k2_tarski(esk11_0,k2_relat_1(esk12_0)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_55]),c_0_54])).

cnf(c_0_63,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_64,negated_conjecture,
    ( k10_relat_1(esk12_0,esk11_0) != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(esk12_0),esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_65,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_57,c_0_18])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(er,[status(thm)],[c_0_58])).

cnf(c_0_68,negated_conjecture,
    ( k10_relat_1(esk12_0,X1) = k1_xboole_0
    | k4_xboole_0(k2_relat_1(esk12_0),k4_xboole_0(k2_relat_1(esk12_0),X1)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_69,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_61])).

cnf(c_0_70,negated_conjecture,
    ( k10_relat_1(esk12_0,esk11_0) = k1_xboole_0
    | ~ r2_hidden(X1,k4_xboole_0(esk11_0,k4_xboole_0(esk11_0,k2_relat_1(esk12_0)))) ),
    inference(rw,[status(thm)],[c_0_62,c_0_35])).

cnf(c_0_71,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_63])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk2_2(k2_relat_1(esk12_0),esk11_0),k4_xboole_0(esk11_0,k4_xboole_0(esk11_0,k2_relat_1(esk12_0))))
    | k10_relat_1(esk12_0,esk11_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_54]),c_0_35])).

cnf(c_0_73,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_66])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(X1,k10_relat_1(esk12_0,X2))
    | ~ r2_hidden(k4_tarski(X1,X3),esk12_0)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_67,c_0_37])).

cnf(c_0_76,negated_conjecture,
    ( k10_relat_1(esk12_0,X1) = k1_xboole_0
    | k4_xboole_0(X1,k4_xboole_0(X1,k2_relat_1(esk12_0))) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_77,negated_conjecture,
    ( k4_xboole_0(esk11_0,k4_xboole_0(esk11_0,k2_relat_1(esk12_0))) = k1_xboole_0
    | k10_relat_1(esk12_0,esk11_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_70,c_0_47])).

cnf(c_0_78,negated_conjecture,
    ( k10_relat_1(esk12_0,esk11_0) != k1_xboole_0
    | ~ r2_hidden(esk2_2(k2_relat_1(esk12_0),esk11_0),k4_xboole_0(esk11_0,k2_relat_1(esk12_0))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_79,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_73])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(esk2_2(k2_relat_1(esk12_0),esk11_0),esk11_0)
    | k10_relat_1(esk12_0,esk11_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_74,c_0_72])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk7_3(esk12_0,k2_relat_1(esk12_0),X1),k10_relat_1(esk12_0,X2))
    | ~ r2_hidden(X1,k2_relat_1(esk12_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_75,c_0_40])).

cnf(c_0_82,negated_conjecture,
    ( k10_relat_1(esk12_0,esk11_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(esk2_2(k2_relat_1(esk12_0),esk11_0),k2_relat_1(esk12_0))
    | k10_relat_1(esk12_0,esk11_0) != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80])).

cnf(c_0_84,negated_conjecture,
    ( ~ r2_hidden(X1,k2_relat_1(esk12_0))
    | ~ r2_hidden(X1,esk11_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_39])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(esk2_2(k2_relat_1(esk12_0),esk11_0),k2_relat_1(esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_82])])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(esk2_2(k2_relat_1(esk12_0),esk11_0),esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_82])])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:38:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.88/1.07  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S032I
% 0.88/1.07  # and selection function SelectUnlessUniqMax.
% 0.88/1.07  #
% 0.88/1.07  # Preprocessing time       : 0.029 s
% 0.88/1.07  # Presaturation interreduction done
% 0.88/1.07  
% 0.88/1.07  # Proof found!
% 0.88/1.07  # SZS status Theorem
% 0.88/1.07  # SZS output start CNFRefutation
% 0.88/1.07  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.88/1.07  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.88/1.07  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.88/1.07  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.88/1.07  fof(t173_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 0.88/1.07  fof(l24_zfmisc_1, axiom, ![X1, X2]:~((r1_xboole_0(k1_tarski(X1),X2)&r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 0.88/1.07  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.88/1.07  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 0.88/1.07  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 0.88/1.07  fof(t168_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k10_relat_1(X2,X1)=k10_relat_1(X2,k3_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 0.88/1.07  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.88/1.07  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.88/1.07  fof(d14_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X4,X5),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 0.88/1.07  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.88/1.07  fof(c_0_14, plain, ![X19, X20, X22, X23, X24]:((r1_xboole_0(X19,X20)|r2_hidden(esk2_2(X19,X20),k3_xboole_0(X19,X20)))&(~r2_hidden(X24,k3_xboole_0(X22,X23))|~r1_xboole_0(X22,X23))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.88/1.07  fof(c_0_15, plain, ![X32, X33]:k1_setfam_1(k2_tarski(X32,X33))=k3_xboole_0(X32,X33), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.88/1.07  fof(c_0_16, plain, ![X17, X18]:((~r1_xboole_0(X17,X18)|k3_xboole_0(X17,X18)=k1_xboole_0)&(k3_xboole_0(X17,X18)!=k1_xboole_0|r1_xboole_0(X17,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.88/1.07  cnf(c_0_17, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.88/1.07  cnf(c_0_18, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.88/1.07  cnf(c_0_19, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.88/1.07  fof(c_0_20, plain, ![X27, X28]:k4_xboole_0(X27,k4_xboole_0(X27,X28))=k3_xboole_0(X27,X28), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.88/1.07  fof(c_0_21, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1)))), inference(assume_negation,[status(cth)],[t173_relat_1])).
% 0.88/1.07  fof(c_0_22, plain, ![X30, X31]:(~r1_xboole_0(k1_tarski(X30),X31)|~r2_hidden(X30,X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).
% 0.88/1.07  fof(c_0_23, plain, ![X29]:r1_xboole_0(X29,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.88/1.07  fof(c_0_24, plain, ![X46, X47, X48, X50, X51, X52, X53, X55]:(((~r2_hidden(X48,X47)|r2_hidden(k4_tarski(esk7_3(X46,X47,X48),X48),X46)|X47!=k2_relat_1(X46))&(~r2_hidden(k4_tarski(X51,X50),X46)|r2_hidden(X50,X47)|X47!=k2_relat_1(X46)))&((~r2_hidden(esk8_2(X52,X53),X53)|~r2_hidden(k4_tarski(X55,esk8_2(X52,X53)),X52)|X53=k2_relat_1(X52))&(r2_hidden(esk8_2(X52,X53),X53)|r2_hidden(k4_tarski(esk9_2(X52,X53),esk8_2(X52,X53)),X52)|X53=k2_relat_1(X52)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.88/1.07  cnf(c_0_25, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X3)))), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.88/1.07  cnf(c_0_26, plain, (r1_xboole_0(X1,X2)|k1_setfam_1(k2_tarski(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_19, c_0_18])).
% 0.88/1.07  cnf(c_0_27, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.88/1.07  fof(c_0_28, plain, ![X57, X58, X59, X61]:((((r2_hidden(esk10_3(X57,X58,X59),k2_relat_1(X59))|~r2_hidden(X57,k10_relat_1(X59,X58))|~v1_relat_1(X59))&(r2_hidden(k4_tarski(X57,esk10_3(X57,X58,X59)),X59)|~r2_hidden(X57,k10_relat_1(X59,X58))|~v1_relat_1(X59)))&(r2_hidden(esk10_3(X57,X58,X59),X58)|~r2_hidden(X57,k10_relat_1(X59,X58))|~v1_relat_1(X59)))&(~r2_hidden(X61,k2_relat_1(X59))|~r2_hidden(k4_tarski(X57,X61),X59)|~r2_hidden(X61,X58)|r2_hidden(X57,k10_relat_1(X59,X58))|~v1_relat_1(X59))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.88/1.07  fof(c_0_29, negated_conjecture, (v1_relat_1(esk12_0)&((k10_relat_1(esk12_0,esk11_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk12_0),esk11_0))&(k10_relat_1(esk12_0,esk11_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk12_0),esk11_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.88/1.07  fof(c_0_30, plain, ![X62, X63]:(~v1_relat_1(X63)|k10_relat_1(X63,X62)=k10_relat_1(X63,k3_xboole_0(k2_relat_1(X63),X62))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_relat_1])])).
% 0.88/1.07  cnf(c_0_31, plain, (~r1_xboole_0(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.88/1.07  cnf(c_0_32, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.88/1.07  cnf(c_0_33, plain, (r2_hidden(k4_tarski(esk7_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.88/1.07  cnf(c_0_34, plain, (k1_setfam_1(k2_tarski(X1,X2))!=k1_xboole_0|~r2_hidden(X3,k1_setfam_1(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.88/1.07  cnf(c_0_35, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k2_tarski(X1,X2))), inference(rw,[status(thm)],[c_0_27, c_0_18])).
% 0.88/1.07  cnf(c_0_36, plain, (r2_hidden(esk10_3(X1,X2,X3),X2)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.88/1.07  cnf(c_0_37, negated_conjecture, (v1_relat_1(esk12_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.88/1.07  cnf(c_0_38, plain, (k10_relat_1(X1,X2)=k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.88/1.07  cnf(c_0_39, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.88/1.07  cnf(c_0_40, plain, (r2_hidden(k4_tarski(esk7_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_33])).
% 0.88/1.07  fof(c_0_41, plain, ![X25]:(X25=k1_xboole_0|r2_hidden(esk3_1(X25),X25)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.88/1.07  fof(c_0_42, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.88/1.07  cnf(c_0_43, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k1_xboole_0|~r2_hidden(X3,k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.88/1.07  cnf(c_0_44, negated_conjecture, (r2_hidden(esk10_3(X1,X2,esk12_0),X2)|~r2_hidden(X1,k10_relat_1(esk12_0,X2))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.88/1.07  cnf(c_0_45, plain, (k10_relat_1(X1,X2)=k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_38, c_0_18])).
% 0.88/1.07  cnf(c_0_46, plain, (~r2_hidden(X1,k2_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.88/1.07  cnf(c_0_47, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.88/1.07  cnf(c_0_48, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.88/1.07  fof(c_0_49, plain, ![X34, X35, X36, X37, X39, X40, X41, X42, X44]:((((r2_hidden(k4_tarski(X37,esk4_4(X34,X35,X36,X37)),X34)|~r2_hidden(X37,X36)|X36!=k10_relat_1(X34,X35)|~v1_relat_1(X34))&(r2_hidden(esk4_4(X34,X35,X36,X37),X35)|~r2_hidden(X37,X36)|X36!=k10_relat_1(X34,X35)|~v1_relat_1(X34)))&(~r2_hidden(k4_tarski(X39,X40),X34)|~r2_hidden(X40,X35)|r2_hidden(X39,X36)|X36!=k10_relat_1(X34,X35)|~v1_relat_1(X34)))&((~r2_hidden(esk5_3(X34,X41,X42),X42)|(~r2_hidden(k4_tarski(esk5_3(X34,X41,X42),X44),X34)|~r2_hidden(X44,X41))|X42=k10_relat_1(X34,X41)|~v1_relat_1(X34))&((r2_hidden(k4_tarski(esk5_3(X34,X41,X42),esk6_3(X34,X41,X42)),X34)|r2_hidden(esk5_3(X34,X41,X42),X42)|X42=k10_relat_1(X34,X41)|~v1_relat_1(X34))&(r2_hidden(esk6_3(X34,X41,X42),X41)|r2_hidden(esk5_3(X34,X41,X42),X42)|X42=k10_relat_1(X34,X41)|~v1_relat_1(X34))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).
% 0.88/1.07  cnf(c_0_50, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k1_xboole_0|~r2_hidden(X3,k10_relat_1(esk12_0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.88/1.07  cnf(c_0_51, negated_conjecture, (k10_relat_1(esk12_0,k4_xboole_0(k2_relat_1(esk12_0),k4_xboole_0(k2_relat_1(esk12_0),X1)))=k10_relat_1(esk12_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_37]), c_0_35])).
% 0.88/1.07  cnf(c_0_52, plain, (r2_hidden(esk8_2(X1,X2),X2)|r2_hidden(k4_tarski(esk9_2(X1,X2),esk8_2(X1,X2)),X1)|X2=k2_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.88/1.07  cnf(c_0_53, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.88/1.07  cnf(c_0_54, plain, (k1_setfam_1(k2_tarski(X1,X2))=k1_setfam_1(k2_tarski(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_18]), c_0_18])).
% 0.88/1.07  cnf(c_0_55, negated_conjecture, (k10_relat_1(esk12_0,esk11_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk12_0),esk11_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.88/1.07  fof(c_0_56, plain, ![X8, X9, X10, X11, X12, X13, X14, X15]:((((r2_hidden(X11,X8)|~r2_hidden(X11,X10)|X10!=k4_xboole_0(X8,X9))&(~r2_hidden(X11,X9)|~r2_hidden(X11,X10)|X10!=k4_xboole_0(X8,X9)))&(~r2_hidden(X12,X8)|r2_hidden(X12,X9)|r2_hidden(X12,X10)|X10!=k4_xboole_0(X8,X9)))&((~r2_hidden(esk1_3(X13,X14,X15),X15)|(~r2_hidden(esk1_3(X13,X14,X15),X13)|r2_hidden(esk1_3(X13,X14,X15),X14))|X15=k4_xboole_0(X13,X14))&((r2_hidden(esk1_3(X13,X14,X15),X13)|r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k4_xboole_0(X13,X14))&(~r2_hidden(esk1_3(X13,X14,X15),X14)|r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k4_xboole_0(X13,X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.88/1.07  cnf(c_0_57, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.88/1.07  cnf(c_0_58, plain, (r2_hidden(X1,X5)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X2,X4)|X5!=k10_relat_1(X3,X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.88/1.07  cnf(c_0_59, negated_conjecture, (k4_xboole_0(k2_relat_1(esk12_0),k4_xboole_0(k2_relat_1(esk12_0),X1))!=k1_xboole_0|~r2_hidden(X2,k10_relat_1(esk12_0,X1))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.88/1.07  cnf(c_0_60, plain, (X1=k1_xboole_0|r2_hidden(esk8_2(k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_52]), c_0_53])).
% 0.88/1.07  cnf(c_0_61, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k2_tarski(X2,X1))), inference(spm,[status(thm)],[c_0_54, c_0_35])).
% 0.88/1.07  cnf(c_0_62, negated_conjecture, (k10_relat_1(esk12_0,esk11_0)=k1_xboole_0|~r2_hidden(X1,k1_setfam_1(k2_tarski(esk11_0,k2_relat_1(esk12_0))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_55]), c_0_54])).
% 0.88/1.07  cnf(c_0_63, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.88/1.07  cnf(c_0_64, negated_conjecture, (k10_relat_1(esk12_0,esk11_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk12_0),esk11_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.88/1.07  cnf(c_0_65, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_57, c_0_18])).
% 0.88/1.07  cnf(c_0_66, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.88/1.07  cnf(c_0_67, plain, (r2_hidden(X1,k10_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X4),X2)|~r2_hidden(X4,X3)), inference(er,[status(thm)],[c_0_58])).
% 0.88/1.07  cnf(c_0_68, negated_conjecture, (k10_relat_1(esk12_0,X1)=k1_xboole_0|k4_xboole_0(k2_relat_1(esk12_0),k4_xboole_0(k2_relat_1(esk12_0),X1))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.88/1.07  cnf(c_0_69, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_35, c_0_61])).
% 0.88/1.07  cnf(c_0_70, negated_conjecture, (k10_relat_1(esk12_0,esk11_0)=k1_xboole_0|~r2_hidden(X1,k4_xboole_0(esk11_0,k4_xboole_0(esk11_0,k2_relat_1(esk12_0))))), inference(rw,[status(thm)],[c_0_62, c_0_35])).
% 0.88/1.07  cnf(c_0_71, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_63])).
% 0.88/1.07  cnf(c_0_72, negated_conjecture, (r2_hidden(esk2_2(k2_relat_1(esk12_0),esk11_0),k4_xboole_0(esk11_0,k4_xboole_0(esk11_0,k2_relat_1(esk12_0))))|k10_relat_1(esk12_0,esk11_0)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_54]), c_0_35])).
% 0.88/1.07  cnf(c_0_73, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.88/1.07  cnf(c_0_74, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_66])).
% 0.88/1.07  cnf(c_0_75, negated_conjecture, (r2_hidden(X1,k10_relat_1(esk12_0,X2))|~r2_hidden(k4_tarski(X1,X3),esk12_0)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_67, c_0_37])).
% 0.88/1.07  cnf(c_0_76, negated_conjecture, (k10_relat_1(esk12_0,X1)=k1_xboole_0|k4_xboole_0(X1,k4_xboole_0(X1,k2_relat_1(esk12_0)))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.88/1.07  cnf(c_0_77, negated_conjecture, (k4_xboole_0(esk11_0,k4_xboole_0(esk11_0,k2_relat_1(esk12_0)))=k1_xboole_0|k10_relat_1(esk12_0,esk11_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_70, c_0_47])).
% 0.88/1.07  cnf(c_0_78, negated_conjecture, (k10_relat_1(esk12_0,esk11_0)!=k1_xboole_0|~r2_hidden(esk2_2(k2_relat_1(esk12_0),esk11_0),k4_xboole_0(esk11_0,k2_relat_1(esk12_0)))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.88/1.07  cnf(c_0_79, plain, (r2_hidden(X1,k4_xboole_0(X2,X3))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_73])).
% 0.88/1.07  cnf(c_0_80, negated_conjecture, (r2_hidden(esk2_2(k2_relat_1(esk12_0),esk11_0),esk11_0)|k10_relat_1(esk12_0,esk11_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_74, c_0_72])).
% 0.88/1.07  cnf(c_0_81, negated_conjecture, (r2_hidden(esk7_3(esk12_0,k2_relat_1(esk12_0),X1),k10_relat_1(esk12_0,X2))|~r2_hidden(X1,k2_relat_1(esk12_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_75, c_0_40])).
% 0.88/1.07  cnf(c_0_82, negated_conjecture, (k10_relat_1(esk12_0,esk11_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.88/1.07  cnf(c_0_83, negated_conjecture, (r2_hidden(esk2_2(k2_relat_1(esk12_0),esk11_0),k2_relat_1(esk12_0))|k10_relat_1(esk12_0,esk11_0)!=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80])).
% 0.88/1.07  cnf(c_0_84, negated_conjecture, (~r2_hidden(X1,k2_relat_1(esk12_0))|~r2_hidden(X1,esk11_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_39])).
% 0.88/1.07  cnf(c_0_85, negated_conjecture, (r2_hidden(esk2_2(k2_relat_1(esk12_0),esk11_0),k2_relat_1(esk12_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_82])])).
% 0.88/1.07  cnf(c_0_86, negated_conjecture, (r2_hidden(esk2_2(k2_relat_1(esk12_0),esk11_0),esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_82])])).
% 0.88/1.07  cnf(c_0_87, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_86])]), ['proof']).
% 0.88/1.07  # SZS output end CNFRefutation
% 0.88/1.07  # Proof object total steps             : 88
% 0.88/1.07  # Proof object clause steps            : 59
% 0.88/1.07  # Proof object formula steps           : 29
% 0.88/1.07  # Proof object conjectures             : 26
% 0.88/1.07  # Proof object clause conjectures      : 23
% 0.88/1.07  # Proof object formula conjectures     : 3
% 0.88/1.07  # Proof object initial clauses used    : 20
% 0.88/1.07  # Proof object initial formulas used   : 14
% 0.88/1.07  # Proof object generating inferences   : 25
% 0.88/1.07  # Proof object simplifying inferences  : 26
% 0.88/1.07  # Training examples: 0 positive, 0 negative
% 0.88/1.07  # Parsed axioms                        : 14
% 0.88/1.07  # Removed by relevancy pruning/SinE    : 0
% 0.88/1.07  # Initial clauses                      : 34
% 0.88/1.07  # Removed in clause preprocessing      : 1
% 0.88/1.07  # Initial clauses in saturation        : 33
% 0.88/1.07  # Processed clauses                    : 9569
% 0.88/1.07  # ...of these trivial                  : 13
% 0.88/1.07  # ...subsumed                          : 8624
% 0.88/1.07  # ...remaining for further processing  : 932
% 0.88/1.07  # Other redundant clauses eliminated   : 8
% 0.88/1.07  # Clauses deleted for lack of memory   : 0
% 0.88/1.07  # Backward-subsumed                    : 33
% 0.88/1.07  # Backward-rewritten                   : 102
% 0.88/1.07  # Generated clauses                    : 98608
% 0.88/1.07  # ...of the previous two non-trivial   : 73043
% 0.88/1.07  # Contextual simplify-reflections      : 5
% 0.88/1.07  # Paramodulations                      : 98584
% 0.88/1.07  # Factorizations                       : 16
% 0.88/1.07  # Equation resolutions                 : 8
% 0.88/1.07  # Propositional unsat checks           : 0
% 0.88/1.07  #    Propositional check models        : 0
% 0.88/1.07  #    Propositional check unsatisfiable : 0
% 0.88/1.07  #    Propositional clauses             : 0
% 0.88/1.07  #    Propositional clauses after purity: 0
% 0.88/1.07  #    Propositional unsat core size     : 0
% 0.88/1.07  #    Propositional preprocessing time  : 0.000
% 0.88/1.07  #    Propositional encoding time       : 0.000
% 0.88/1.07  #    Propositional solver time         : 0.000
% 0.88/1.07  #    Success case prop preproc time    : 0.000
% 0.88/1.07  #    Success case prop encoding time   : 0.000
% 0.88/1.07  #    Success case prop solver time     : 0.000
% 0.88/1.07  # Current number of processed clauses  : 757
% 0.88/1.07  #    Positive orientable unit clauses  : 25
% 0.88/1.07  #    Positive unorientable unit clauses: 4
% 0.88/1.07  #    Negative unit clauses             : 11
% 0.88/1.07  #    Non-unit-clauses                  : 717
% 0.88/1.07  # Current number of unprocessed clauses: 63270
% 0.88/1.07  # ...number of literals in the above   : 186050
% 0.88/1.07  # Current number of archived formulas  : 0
% 0.88/1.07  # Current number of archived clauses   : 168
% 0.88/1.07  # Clause-clause subsumption calls (NU) : 137956
% 0.88/1.07  # Rec. Clause-clause subsumption calls : 110145
% 0.88/1.07  # Non-unit clause-clause subsumptions  : 2591
% 0.88/1.07  # Unit Clause-clause subsumption calls : 893
% 0.88/1.07  # Rewrite failures with RHS unbound    : 0
% 0.88/1.07  # BW rewrite match attempts            : 141
% 0.88/1.07  # BW rewrite match successes           : 71
% 0.88/1.07  # Condensation attempts                : 0
% 0.88/1.07  # Condensation successes               : 0
% 0.88/1.07  # Termbank termtop insertions          : 1639008
% 0.88/1.08  
% 0.88/1.08  # -------------------------------------------------
% 0.88/1.08  # User time                : 0.691 s
% 0.88/1.08  # System time              : 0.041 s
% 0.88/1.08  # Total time               : 0.732 s
% 0.88/1.08  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
