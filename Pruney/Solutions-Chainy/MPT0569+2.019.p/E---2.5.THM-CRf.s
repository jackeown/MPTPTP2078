%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:35 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 187 expanded)
%              Number of clauses        :   32 (  81 expanded)
%              Number of leaves         :   10 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :  177 ( 554 expanded)
%              Number of equality atoms :   36 ( 146 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t173_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k10_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

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

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

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

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

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

fof(c_0_10,plain,(
    ! [X14,X15,X17,X18,X19] :
      ( ( r1_xboole_0(X14,X15)
        | r2_hidden(esk2_2(X14,X15),k3_xboole_0(X14,X15)) )
      & ( ~ r2_hidden(X19,k3_xboole_0(X17,X18))
        | ~ r1_xboole_0(X17,X18) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_11,plain,(
    ! [X20] :
      ( X20 = k1_xboole_0
      | r2_hidden(esk3_1(X20),X20) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( k10_relat_1(X2,X1) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t173_relat_1])).

fof(c_0_13,plain,(
    ! [X46,X47,X48,X50] :
      ( ( r2_hidden(esk10_3(X46,X47,X48),k2_relat_1(X48))
        | ~ r2_hidden(X46,k10_relat_1(X48,X47))
        | ~ v1_relat_1(X48) )
      & ( r2_hidden(k4_tarski(X46,esk10_3(X46,X47,X48)),X48)
        | ~ r2_hidden(X46,k10_relat_1(X48,X47))
        | ~ v1_relat_1(X48) )
      & ( r2_hidden(esk10_3(X46,X47,X48),X47)
        | ~ r2_hidden(X46,k10_relat_1(X48,X47))
        | ~ v1_relat_1(X48) )
      & ( ~ r2_hidden(X50,k2_relat_1(X48))
        | ~ r2_hidden(k4_tarski(X46,X50),X48)
        | ~ r2_hidden(X50,X47)
        | r2_hidden(X46,k10_relat_1(X48,X47))
        | ~ v1_relat_1(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

cnf(c_0_14,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,negated_conjecture,
    ( v1_relat_1(esk12_0)
    & ( k10_relat_1(esk12_0,esk11_0) != k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(esk12_0),esk11_0) )
    & ( k10_relat_1(esk12_0,esk11_0) = k1_xboole_0
      | r1_xboole_0(k2_relat_1(esk12_0),esk11_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_17,plain,
    ( r2_hidden(esk10_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X51,X52] :
      ( ~ v1_relat_1(X52)
      | k10_relat_1(X52,X51) = k10_relat_1(X52,k3_xboole_0(k2_relat_1(X52),X51)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_relat_1])])).

cnf(c_0_19,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( k10_relat_1(esk12_0,esk11_0) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(esk12_0),esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X6,X7] :
      ( ~ r1_xboole_0(X6,X7)
      | r1_xboole_0(X7,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_22,plain,(
    ! [X22] : r1_xboole_0(X22,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_23,plain,(
    ! [X23,X24,X25,X26,X28,X29,X30,X31,X33] :
      ( ( r2_hidden(k4_tarski(X26,esk4_4(X23,X24,X25,X26)),X23)
        | ~ r2_hidden(X26,X25)
        | X25 != k10_relat_1(X23,X24)
        | ~ v1_relat_1(X23) )
      & ( r2_hidden(esk4_4(X23,X24,X25,X26),X24)
        | ~ r2_hidden(X26,X25)
        | X25 != k10_relat_1(X23,X24)
        | ~ v1_relat_1(X23) )
      & ( ~ r2_hidden(k4_tarski(X28,X29),X23)
        | ~ r2_hidden(X29,X24)
        | r2_hidden(X28,X25)
        | X25 != k10_relat_1(X23,X24)
        | ~ v1_relat_1(X23) )
      & ( ~ r2_hidden(esk5_3(X23,X30,X31),X31)
        | ~ r2_hidden(k4_tarski(esk5_3(X23,X30,X31),X33),X23)
        | ~ r2_hidden(X33,X30)
        | X31 = k10_relat_1(X23,X30)
        | ~ v1_relat_1(X23) )
      & ( r2_hidden(k4_tarski(esk5_3(X23,X30,X31),esk6_3(X23,X30,X31)),X23)
        | r2_hidden(esk5_3(X23,X30,X31),X31)
        | X31 = k10_relat_1(X23,X30)
        | ~ v1_relat_1(X23) )
      & ( r2_hidden(esk6_3(X23,X30,X31),X30)
        | r2_hidden(esk5_3(X23,X30,X31),X31)
        | X31 = k10_relat_1(X23,X30)
        | ~ v1_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

fof(c_0_24,plain,(
    ! [X35,X36,X37,X39,X40,X41,X42,X44] :
      ( ( ~ r2_hidden(X37,X36)
        | r2_hidden(k4_tarski(esk7_3(X35,X36,X37),X37),X35)
        | X36 != k2_relat_1(X35) )
      & ( ~ r2_hidden(k4_tarski(X40,X39),X35)
        | r2_hidden(X39,X36)
        | X36 != k2_relat_1(X35) )
      & ( ~ r2_hidden(esk8_2(X41,X42),X42)
        | ~ r2_hidden(k4_tarski(X44,esk8_2(X41,X42)),X41)
        | X42 = k2_relat_1(X41) )
      & ( r2_hidden(esk8_2(X41,X42),X42)
        | r2_hidden(k4_tarski(esk9_2(X41,X42),esk8_2(X41,X42)),X41)
        | X42 = k2_relat_1(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_25,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k10_relat_1(X1,k3_xboole_0(X3,X4)))
    | ~ r1_xboole_0(X3,X4) ),
    inference(spm,[status(thm)],[c_0_14,c_0_17])).

cnf(c_0_26,plain,
    ( k10_relat_1(X1,X2) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( k3_xboole_0(k2_relat_1(esk12_0),esk11_0) = k1_xboole_0
    | k10_relat_1(esk12_0,esk11_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X5 != k10_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( r2_hidden(k4_tarski(esk7_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k10_relat_1(X1,X3))
    | ~ r1_xboole_0(k2_relat_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( k10_relat_1(esk12_0,esk11_0) = k10_relat_1(esk12_0,k1_xboole_0)
    | k10_relat_1(esk12_0,esk11_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

cnf(c_0_35,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( r2_hidden(k4_tarski(esk7_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( k10_relat_1(esk12_0,esk11_0) = k1_xboole_0
    | ~ r2_hidden(X1,k10_relat_1(esk12_0,k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_28])]),c_0_20])).

cnf(c_0_39,negated_conjecture,
    ( k10_relat_1(esk12_0,esk11_0) = k1_xboole_0
    | k10_relat_1(esk12_0,k1_xboole_0) != k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_19,c_0_35])).

cnf(c_0_41,plain,
    ( r2_hidden(esk7_3(X1,k2_relat_1(X1),X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( k10_relat_1(esk12_0,esk11_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_15]),c_0_39])).

cnf(c_0_43,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_40]),c_0_35])])).

fof(c_0_44,plain,(
    ! [X8,X9,X11,X12,X13] :
      ( ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_xboole_0(X8,X9) )
      & ( r2_hidden(esk1_2(X8,X9),X9)
        | r1_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X13,X11)
        | ~ r2_hidden(X13,X12)
        | ~ r1_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_45,negated_conjecture,
    ( ~ r2_hidden(X1,k2_relat_1(esk12_0))
    | ~ r2_hidden(X1,esk11_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_28])]),c_0_43])).

cnf(c_0_46,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( r1_xboole_0(X1,k2_relat_1(esk12_0))
    | ~ r2_hidden(esk1_2(X1,k2_relat_1(esk12_0)),esk11_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_48,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( k10_relat_1(esk12_0,esk11_0) != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(esk12_0),esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_50,negated_conjecture,
    ( r1_xboole_0(esk11_0,k2_relat_1(esk12_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(esk12_0),esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_42])])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_50]),c_0_51]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:48:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.54  # AutoSched0-Mode selected heuristic G_E___208_C02CMA_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.54  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.54  #
% 0.20/0.54  # Preprocessing time       : 0.048 s
% 0.20/0.54  # Presaturation interreduction done
% 0.20/0.54  
% 0.20/0.54  # Proof found!
% 0.20/0.54  # SZS status Theorem
% 0.20/0.54  # SZS output start CNFRefutation
% 0.20/0.54  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.20/0.54  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.20/0.54  fof(t173_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 0.20/0.54  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 0.20/0.54  fof(t168_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k10_relat_1(X2,X1)=k10_relat_1(X2,k3_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 0.20/0.54  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.20/0.54  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.20/0.54  fof(d14_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X4,X5),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 0.20/0.54  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 0.20/0.54  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.20/0.54  fof(c_0_10, plain, ![X14, X15, X17, X18, X19]:((r1_xboole_0(X14,X15)|r2_hidden(esk2_2(X14,X15),k3_xboole_0(X14,X15)))&(~r2_hidden(X19,k3_xboole_0(X17,X18))|~r1_xboole_0(X17,X18))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.20/0.54  fof(c_0_11, plain, ![X20]:(X20=k1_xboole_0|r2_hidden(esk3_1(X20),X20)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.20/0.54  fof(c_0_12, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1)))), inference(assume_negation,[status(cth)],[t173_relat_1])).
% 0.20/0.54  fof(c_0_13, plain, ![X46, X47, X48, X50]:((((r2_hidden(esk10_3(X46,X47,X48),k2_relat_1(X48))|~r2_hidden(X46,k10_relat_1(X48,X47))|~v1_relat_1(X48))&(r2_hidden(k4_tarski(X46,esk10_3(X46,X47,X48)),X48)|~r2_hidden(X46,k10_relat_1(X48,X47))|~v1_relat_1(X48)))&(r2_hidden(esk10_3(X46,X47,X48),X47)|~r2_hidden(X46,k10_relat_1(X48,X47))|~v1_relat_1(X48)))&(~r2_hidden(X50,k2_relat_1(X48))|~r2_hidden(k4_tarski(X46,X50),X48)|~r2_hidden(X50,X47)|r2_hidden(X46,k10_relat_1(X48,X47))|~v1_relat_1(X48))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.20/0.54  cnf(c_0_14, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.54  cnf(c_0_15, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.54  fof(c_0_16, negated_conjecture, (v1_relat_1(esk12_0)&((k10_relat_1(esk12_0,esk11_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk12_0),esk11_0))&(k10_relat_1(esk12_0,esk11_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk12_0),esk11_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.20/0.54  cnf(c_0_17, plain, (r2_hidden(esk10_3(X1,X2,X3),X2)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.54  fof(c_0_18, plain, ![X51, X52]:(~v1_relat_1(X52)|k10_relat_1(X52,X51)=k10_relat_1(X52,k3_xboole_0(k2_relat_1(X52),X51))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_relat_1])])).
% 0.20/0.54  cnf(c_0_19, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.20/0.54  cnf(c_0_20, negated_conjecture, (k10_relat_1(esk12_0,esk11_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk12_0),esk11_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.54  fof(c_0_21, plain, ![X6, X7]:(~r1_xboole_0(X6,X7)|r1_xboole_0(X7,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.20/0.54  fof(c_0_22, plain, ![X22]:r1_xboole_0(X22,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.20/0.54  fof(c_0_23, plain, ![X23, X24, X25, X26, X28, X29, X30, X31, X33]:((((r2_hidden(k4_tarski(X26,esk4_4(X23,X24,X25,X26)),X23)|~r2_hidden(X26,X25)|X25!=k10_relat_1(X23,X24)|~v1_relat_1(X23))&(r2_hidden(esk4_4(X23,X24,X25,X26),X24)|~r2_hidden(X26,X25)|X25!=k10_relat_1(X23,X24)|~v1_relat_1(X23)))&(~r2_hidden(k4_tarski(X28,X29),X23)|~r2_hidden(X29,X24)|r2_hidden(X28,X25)|X25!=k10_relat_1(X23,X24)|~v1_relat_1(X23)))&((~r2_hidden(esk5_3(X23,X30,X31),X31)|(~r2_hidden(k4_tarski(esk5_3(X23,X30,X31),X33),X23)|~r2_hidden(X33,X30))|X31=k10_relat_1(X23,X30)|~v1_relat_1(X23))&((r2_hidden(k4_tarski(esk5_3(X23,X30,X31),esk6_3(X23,X30,X31)),X23)|r2_hidden(esk5_3(X23,X30,X31),X31)|X31=k10_relat_1(X23,X30)|~v1_relat_1(X23))&(r2_hidden(esk6_3(X23,X30,X31),X30)|r2_hidden(esk5_3(X23,X30,X31),X31)|X31=k10_relat_1(X23,X30)|~v1_relat_1(X23))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).
% 0.20/0.54  fof(c_0_24, plain, ![X35, X36, X37, X39, X40, X41, X42, X44]:(((~r2_hidden(X37,X36)|r2_hidden(k4_tarski(esk7_3(X35,X36,X37),X37),X35)|X36!=k2_relat_1(X35))&(~r2_hidden(k4_tarski(X40,X39),X35)|r2_hidden(X39,X36)|X36!=k2_relat_1(X35)))&((~r2_hidden(esk8_2(X41,X42),X42)|~r2_hidden(k4_tarski(X44,esk8_2(X41,X42)),X41)|X42=k2_relat_1(X41))&(r2_hidden(esk8_2(X41,X42),X42)|r2_hidden(k4_tarski(esk9_2(X41,X42),esk8_2(X41,X42)),X41)|X42=k2_relat_1(X41)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.20/0.54  cnf(c_0_25, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k10_relat_1(X1,k3_xboole_0(X3,X4)))|~r1_xboole_0(X3,X4)), inference(spm,[status(thm)],[c_0_14, c_0_17])).
% 0.20/0.54  cnf(c_0_26, plain, (k10_relat_1(X1,X2)=k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.54  cnf(c_0_27, negated_conjecture, (k3_xboole_0(k2_relat_1(esk12_0),esk11_0)=k1_xboole_0|k10_relat_1(esk12_0,esk11_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.54  cnf(c_0_28, negated_conjecture, (v1_relat_1(esk12_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.54  cnf(c_0_29, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.54  cnf(c_0_30, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.54  cnf(c_0_31, plain, (r2_hidden(X1,X5)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X2,X4)|X5!=k10_relat_1(X3,X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.54  cnf(c_0_32, plain, (r2_hidden(k4_tarski(esk7_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.54  cnf(c_0_33, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k10_relat_1(X1,X3))|~r1_xboole_0(k2_relat_1(X1),X3)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.54  cnf(c_0_34, negated_conjecture, (k10_relat_1(esk12_0,esk11_0)=k10_relat_1(esk12_0,k1_xboole_0)|k10_relat_1(esk12_0,esk11_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])])).
% 0.20/0.54  cnf(c_0_35, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.54  cnf(c_0_36, plain, (r2_hidden(X1,k10_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X4),X2)|~r2_hidden(X4,X3)), inference(er,[status(thm)],[c_0_31])).
% 0.20/0.54  cnf(c_0_37, plain, (r2_hidden(k4_tarski(esk7_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_32])).
% 0.20/0.54  cnf(c_0_38, negated_conjecture, (k10_relat_1(esk12_0,esk11_0)=k1_xboole_0|~r2_hidden(X1,k10_relat_1(esk12_0,k1_xboole_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_28])]), c_0_20])).
% 0.20/0.54  cnf(c_0_39, negated_conjecture, (k10_relat_1(esk12_0,esk11_0)=k1_xboole_0|k10_relat_1(esk12_0,k1_xboole_0)!=k1_xboole_0), inference(ef,[status(thm)],[c_0_34])).
% 0.20/0.54  cnf(c_0_40, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_19, c_0_35])).
% 0.20/0.54  cnf(c_0_41, plain, (r2_hidden(esk7_3(X1,k2_relat_1(X1),X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.54  cnf(c_0_42, negated_conjecture, (k10_relat_1(esk12_0,esk11_0)=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_15]), c_0_39])).
% 0.20/0.54  cnf(c_0_43, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_40]), c_0_35])])).
% 0.20/0.54  fof(c_0_44, plain, ![X8, X9, X11, X12, X13]:(((r2_hidden(esk1_2(X8,X9),X8)|r1_xboole_0(X8,X9))&(r2_hidden(esk1_2(X8,X9),X9)|r1_xboole_0(X8,X9)))&(~r2_hidden(X13,X11)|~r2_hidden(X13,X12)|~r1_xboole_0(X11,X12))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.20/0.54  cnf(c_0_45, negated_conjecture, (~r2_hidden(X1,k2_relat_1(esk12_0))|~r2_hidden(X1,esk11_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_28])]), c_0_43])).
% 0.20/0.54  cnf(c_0_46, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.54  cnf(c_0_47, negated_conjecture, (r1_xboole_0(X1,k2_relat_1(esk12_0))|~r2_hidden(esk1_2(X1,k2_relat_1(esk12_0)),esk11_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.54  cnf(c_0_48, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.54  cnf(c_0_49, negated_conjecture, (k10_relat_1(esk12_0,esk11_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk12_0),esk11_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.54  cnf(c_0_50, negated_conjecture, (r1_xboole_0(esk11_0,k2_relat_1(esk12_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.54  cnf(c_0_51, negated_conjecture, (~r1_xboole_0(k2_relat_1(esk12_0),esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_42])])).
% 0.20/0.54  cnf(c_0_52, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_50]), c_0_51]), ['proof']).
% 0.20/0.54  # SZS output end CNFRefutation
% 0.20/0.54  # Proof object total steps             : 53
% 0.20/0.54  # Proof object clause steps            : 32
% 0.20/0.54  # Proof object formula steps           : 21
% 0.20/0.54  # Proof object conjectures             : 16
% 0.20/0.54  # Proof object clause conjectures      : 13
% 0.20/0.54  # Proof object formula conjectures     : 3
% 0.20/0.54  # Proof object initial clauses used    : 13
% 0.20/0.54  # Proof object initial formulas used   : 10
% 0.20/0.54  # Proof object generating inferences   : 16
% 0.20/0.54  # Proof object simplifying inferences  : 16
% 0.20/0.54  # Training examples: 0 positive, 0 negative
% 0.20/0.54  # Parsed axioms                        : 10
% 0.20/0.54  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.54  # Initial clauses                      : 26
% 0.20/0.54  # Removed in clause preprocessing      : 0
% 0.20/0.54  # Initial clauses in saturation        : 26
% 0.20/0.54  # Processed clauses                    : 2945
% 0.20/0.54  # ...of these trivial                  : 0
% 0.20/0.54  # ...subsumed                          : 2611
% 0.20/0.54  # ...remaining for further processing  : 334
% 0.20/0.54  # Other redundant clauses eliminated   : 5
% 0.20/0.54  # Clauses deleted for lack of memory   : 0
% 0.20/0.54  # Backward-subsumed                    : 4
% 0.20/0.54  # Backward-rewritten                   : 9
% 0.20/0.54  # Generated clauses                    : 9375
% 0.20/0.54  # ...of the previous two non-trivial   : 8383
% 0.20/0.54  # Contextual simplify-reflections      : 2
% 0.20/0.54  # Paramodulations                      : 9367
% 0.20/0.54  # Factorizations                       : 3
% 0.20/0.54  # Equation resolutions                 : 5
% 0.20/0.54  # Propositional unsat checks           : 0
% 0.20/0.54  #    Propositional check models        : 0
% 0.20/0.54  #    Propositional check unsatisfiable : 0
% 0.20/0.54  #    Propositional clauses             : 0
% 0.20/0.54  #    Propositional clauses after purity: 0
% 0.20/0.54  #    Propositional unsat core size     : 0
% 0.20/0.54  #    Propositional preprocessing time  : 0.000
% 0.20/0.54  #    Propositional encoding time       : 0.000
% 0.20/0.54  #    Propositional solver time         : 0.000
% 0.20/0.54  #    Success case prop preproc time    : 0.000
% 0.20/0.54  #    Success case prop encoding time   : 0.000
% 0.20/0.54  #    Success case prop solver time     : 0.000
% 0.20/0.54  # Current number of processed clauses  : 291
% 0.20/0.54  #    Positive orientable unit clauses  : 8
% 0.20/0.54  #    Positive unorientable unit clauses: 0
% 0.20/0.54  #    Negative unit clauses             : 2
% 0.20/0.54  #    Non-unit-clauses                  : 281
% 0.20/0.54  # Current number of unprocessed clauses: 5450
% 0.20/0.54  # ...number of literals in the above   : 21296
% 0.20/0.54  # Current number of archived formulas  : 0
% 0.20/0.54  # Current number of archived clauses   : 38
% 0.20/0.54  # Clause-clause subsumption calls (NU) : 43999
% 0.20/0.54  # Rec. Clause-clause subsumption calls : 20201
% 0.20/0.54  # Non-unit clause-clause subsumptions  : 1793
% 0.20/0.54  # Unit Clause-clause subsumption calls : 68
% 0.20/0.54  # Rewrite failures with RHS unbound    : 0
% 0.20/0.54  # BW rewrite match attempts            : 2
% 0.20/0.54  # BW rewrite match successes           : 2
% 0.20/0.54  # Condensation attempts                : 0
% 0.20/0.54  # Condensation successes               : 0
% 0.20/0.54  # Termbank termtop insertions          : 145372
% 0.20/0.54  
% 0.20/0.54  # -------------------------------------------------
% 0.20/0.54  # User time                : 0.187 s
% 0.20/0.54  # System time              : 0.010 s
% 0.20/0.54  # Total time               : 0.197 s
% 0.20/0.54  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
