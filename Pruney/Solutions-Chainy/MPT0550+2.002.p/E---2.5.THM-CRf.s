%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:50:47 EST 2020

% Result     : Theorem 0.10s
% Output     : CNFRefutation 0.10s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 132 expanded)
%              Number of clauses        :   39 (  64 expanded)
%              Number of leaves         :   12 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :  193 ( 400 expanded)
%              Number of equality atoms :   45 ( 108 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(d13_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k9_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(k4_tarski(X5,X4),X1)
                  & r2_hidden(X5,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(cc1_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(t152_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ~ ( X1 != k1_xboole_0
          & r1_tarski(X1,k1_relat_1(X2))
          & k9_relat_1(X2,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_relat_1)).

fof(t81_relat_1,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_12,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( ( ~ r1_tarski(X10,X11)
        | ~ r2_hidden(X12,X10)
        | r2_hidden(X12,X11) )
      & ( r2_hidden(esk2_2(X13,X14),X13)
        | r1_tarski(X13,X14) )
      & ( ~ r2_hidden(esk2_2(X13,X14),X14)
        | r1_tarski(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_13,plain,(
    ! [X50,X51] :
      ( ~ v1_relat_1(X51)
      | ~ r1_tarski(k1_relat_1(X51),X50)
      | k7_relat_1(X51,X50) = X51 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_17,plain,(
    ! [X42,X43,X44,X46] :
      ( ( r2_hidden(esk10_3(X42,X43,X44),k1_relat_1(X44))
        | ~ r2_hidden(X42,k9_relat_1(X44,X43))
        | ~ v1_relat_1(X44) )
      & ( r2_hidden(k4_tarski(esk10_3(X42,X43,X44),X42),X44)
        | ~ r2_hidden(X42,k9_relat_1(X44,X43))
        | ~ v1_relat_1(X44) )
      & ( r2_hidden(esk10_3(X42,X43,X44),X43)
        | ~ r2_hidden(X42,k9_relat_1(X44,X43))
        | ~ v1_relat_1(X44) )
      & ( ~ r2_hidden(X46,k1_relat_1(X44))
        | ~ r2_hidden(k4_tarski(X46,X42),X44)
        | ~ r2_hidden(X46,X43)
        | r2_hidden(X42,k9_relat_1(X44,X43))
        | ~ v1_relat_1(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

fof(c_0_18,plain,(
    ! [X47,X48] :
      ( ~ v1_relat_1(X48)
      | k2_relat_1(k7_relat_1(X48,X47)) = k9_relat_1(X48,X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_19,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_21,plain,(
    ! [X31,X32,X33,X35,X36,X37,X38,X40] :
      ( ( ~ r2_hidden(X33,X32)
        | r2_hidden(k4_tarski(X33,esk7_3(X31,X32,X33)),X31)
        | X32 != k1_relat_1(X31) )
      & ( ~ r2_hidden(k4_tarski(X35,X36),X31)
        | r2_hidden(X35,X32)
        | X32 != k1_relat_1(X31) )
      & ( ~ r2_hidden(esk8_2(X37,X38),X38)
        | ~ r2_hidden(k4_tarski(esk8_2(X37,X38),X40),X37)
        | X38 = k1_relat_1(X37) )
      & ( r2_hidden(esk8_2(X37,X38),X38)
        | r2_hidden(k4_tarski(esk8_2(X37,X38),esk9_2(X37,X38)),X37)
        | X38 = k1_relat_1(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

fof(c_0_22,plain,(
    ! [X19,X20,X21,X22,X24,X25,X26,X27,X29] :
      ( ( r2_hidden(k4_tarski(esk4_4(X19,X20,X21,X22),X22),X19)
        | ~ r2_hidden(X22,X21)
        | X21 != k9_relat_1(X19,X20)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(esk4_4(X19,X20,X21,X22),X20)
        | ~ r2_hidden(X22,X21)
        | X21 != k9_relat_1(X19,X20)
        | ~ v1_relat_1(X19) )
      & ( ~ r2_hidden(k4_tarski(X25,X24),X19)
        | ~ r2_hidden(X25,X20)
        | r2_hidden(X24,X21)
        | X21 != k9_relat_1(X19,X20)
        | ~ v1_relat_1(X19) )
      & ( ~ r2_hidden(esk5_3(X19,X26,X27),X27)
        | ~ r2_hidden(k4_tarski(X29,esk5_3(X19,X26,X27)),X19)
        | ~ r2_hidden(X29,X26)
        | X27 = k9_relat_1(X19,X26)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(k4_tarski(esk6_3(X19,X26,X27),esk5_3(X19,X26,X27)),X19)
        | r2_hidden(esk5_3(X19,X26,X27),X27)
        | X27 = k9_relat_1(X19,X26)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(esk6_3(X19,X26,X27),X26)
        | r2_hidden(esk5_3(X19,X26,X27),X27)
        | X27 = k9_relat_1(X19,X26)
        | ~ v1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_relat_1])])])])])])).

cnf(c_0_23,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( r2_hidden(esk10_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_27,plain,(
    ! [X49] :
      ( k1_relat_1(k6_relat_1(X49)) = X49
      & k2_relat_1(k6_relat_1(X49)) = X49 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_28,plain,(
    ! [X18] :
      ( ~ v1_xboole_0(X18)
      | v1_relat_1(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).

fof(c_0_29,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ~ ( X1 != k1_xboole_0
            & r1_tarski(X1,k1_relat_1(X2))
            & k9_relat_1(X2,X1) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t152_relat_1])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( r2_hidden(X2,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | X5 != k9_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( r2_hidden(k4_tarski(X1,esk7_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(X1,X3))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_34,plain,
    ( k2_relat_1(X1) = k9_relat_1(X1,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_35,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t81_relat_1])).

cnf(c_0_37,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_39,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_40,negated_conjecture,
    ( v1_relat_1(esk12_0)
    & esk11_0 != k1_xboole_0
    & r1_tarski(esk11_0,k1_relat_1(esk12_0))
    & k9_relat_1(esk12_0,esk11_0) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( r2_hidden(esk8_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk8_2(X1,X2),esk9_2(X1,X2)),X1)
    | X2 = k1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,k9_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X4,X1),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_44,plain,
    ( r2_hidden(k4_tarski(X1,esk7_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_45,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_xboole_0(k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_46,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_47,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_48,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_36])).

cnf(c_0_49,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(esk11_0,k1_relat_1(esk12_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_51,plain,
    ( X1 = k1_relat_1(X2)
    | r2_hidden(esk8_2(X2,X1),k1_relat_1(X2))
    | r2_hidden(esk8_2(X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_52,plain,
    ( r2_hidden(esk7_3(X1,k1_relat_1(X1),X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( k9_relat_1(esk12_0,esk11_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_54,negated_conjecture,
    ( v1_relat_1(esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_55,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_48]),c_0_38])])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(esk12_0))
    | ~ r2_hidden(X1,esk11_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,plain,
    ( X1 = X2
    | r2_hidden(esk8_2(k6_relat_1(X2),X1),X1)
    | r2_hidden(esk8_2(k6_relat_1(X2),X1),X2) ),
    inference(spm,[status(thm)],[c_0_51,c_0_39])).

cnf(c_0_58,negated_conjecture,
    ( ~ r2_hidden(X1,esk11_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])]),c_0_55]),c_0_56])).

cnf(c_0_59,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk8_2(k6_relat_1(X1),k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( esk11_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.01/0.07  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.07/0.25  % Computer   : n001.cluster.edu
% 0.07/0.25  % Model      : x86_64 x86_64
% 0.07/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.25  % Memory     : 8042.1875MB
% 0.07/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.25  % CPULimit   : 60
% 0.07/0.25  % WCLimit    : 600
% 0.07/0.25  % DateTime   : Tue Dec  1 18:51:30 EST 2020
% 0.07/0.26  % CPUTime    : 
% 0.07/0.26  # Version: 2.5pre002
% 0.07/0.26  # No SInE strategy applied
% 0.07/0.26  # Trying AutoSched0 for 299 seconds
% 0.10/0.34  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.10/0.34  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.10/0.34  #
% 0.10/0.34  # Preprocessing time       : 0.013 s
% 0.10/0.34  
% 0.10/0.34  # Proof found!
% 0.10/0.34  # SZS status Theorem
% 0.10/0.34  # SZS output start CNFRefutation
% 0.10/0.34  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.10/0.34  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 0.10/0.34  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.10/0.34  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 0.10/0.34  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.10/0.34  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 0.10/0.34  fof(d13_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k9_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X5,X4),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_relat_1)).
% 0.10/0.34  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.10/0.34  fof(cc1_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 0.10/0.34  fof(t152_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>~(((X1!=k1_xboole_0&r1_tarski(X1,k1_relat_1(X2)))&k9_relat_1(X2,X1)=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_relat_1)).
% 0.10/0.34  fof(t81_relat_1, axiom, k6_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 0.10/0.34  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.10/0.34  fof(c_0_12, plain, ![X10, X11, X12, X13, X14]:((~r1_tarski(X10,X11)|(~r2_hidden(X12,X10)|r2_hidden(X12,X11)))&((r2_hidden(esk2_2(X13,X14),X13)|r1_tarski(X13,X14))&(~r2_hidden(esk2_2(X13,X14),X14)|r1_tarski(X13,X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.10/0.34  fof(c_0_13, plain, ![X50, X51]:(~v1_relat_1(X51)|(~r1_tarski(k1_relat_1(X51),X50)|k7_relat_1(X51,X50)=X51)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 0.10/0.34  cnf(c_0_14, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.10/0.34  cnf(c_0_15, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.10/0.34  fof(c_0_16, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.10/0.34  fof(c_0_17, plain, ![X42, X43, X44, X46]:((((r2_hidden(esk10_3(X42,X43,X44),k1_relat_1(X44))|~r2_hidden(X42,k9_relat_1(X44,X43))|~v1_relat_1(X44))&(r2_hidden(k4_tarski(esk10_3(X42,X43,X44),X42),X44)|~r2_hidden(X42,k9_relat_1(X44,X43))|~v1_relat_1(X44)))&(r2_hidden(esk10_3(X42,X43,X44),X43)|~r2_hidden(X42,k9_relat_1(X44,X43))|~v1_relat_1(X44)))&(~r2_hidden(X46,k1_relat_1(X44))|~r2_hidden(k4_tarski(X46,X42),X44)|~r2_hidden(X46,X43)|r2_hidden(X42,k9_relat_1(X44,X43))|~v1_relat_1(X44))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.10/0.34  fof(c_0_18, plain, ![X47, X48]:(~v1_relat_1(X48)|k2_relat_1(k7_relat_1(X48,X47))=k9_relat_1(X48,X47)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.10/0.34  cnf(c_0_19, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.10/0.34  cnf(c_0_20, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.10/0.34  fof(c_0_21, plain, ![X31, X32, X33, X35, X36, X37, X38, X40]:(((~r2_hidden(X33,X32)|r2_hidden(k4_tarski(X33,esk7_3(X31,X32,X33)),X31)|X32!=k1_relat_1(X31))&(~r2_hidden(k4_tarski(X35,X36),X31)|r2_hidden(X35,X32)|X32!=k1_relat_1(X31)))&((~r2_hidden(esk8_2(X37,X38),X38)|~r2_hidden(k4_tarski(esk8_2(X37,X38),X40),X37)|X38=k1_relat_1(X37))&(r2_hidden(esk8_2(X37,X38),X38)|r2_hidden(k4_tarski(esk8_2(X37,X38),esk9_2(X37,X38)),X37)|X38=k1_relat_1(X37)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.10/0.34  fof(c_0_22, plain, ![X19, X20, X21, X22, X24, X25, X26, X27, X29]:((((r2_hidden(k4_tarski(esk4_4(X19,X20,X21,X22),X22),X19)|~r2_hidden(X22,X21)|X21!=k9_relat_1(X19,X20)|~v1_relat_1(X19))&(r2_hidden(esk4_4(X19,X20,X21,X22),X20)|~r2_hidden(X22,X21)|X21!=k9_relat_1(X19,X20)|~v1_relat_1(X19)))&(~r2_hidden(k4_tarski(X25,X24),X19)|~r2_hidden(X25,X20)|r2_hidden(X24,X21)|X21!=k9_relat_1(X19,X20)|~v1_relat_1(X19)))&((~r2_hidden(esk5_3(X19,X26,X27),X27)|(~r2_hidden(k4_tarski(X29,esk5_3(X19,X26,X27)),X19)|~r2_hidden(X29,X26))|X27=k9_relat_1(X19,X26)|~v1_relat_1(X19))&((r2_hidden(k4_tarski(esk6_3(X19,X26,X27),esk5_3(X19,X26,X27)),X19)|r2_hidden(esk5_3(X19,X26,X27),X27)|X27=k9_relat_1(X19,X26)|~v1_relat_1(X19))&(r2_hidden(esk6_3(X19,X26,X27),X26)|r2_hidden(esk5_3(X19,X26,X27),X27)|X27=k9_relat_1(X19,X26)|~v1_relat_1(X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_relat_1])])])])])])).
% 0.10/0.34  cnf(c_0_23, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.10/0.34  cnf(c_0_24, plain, (r2_hidden(esk10_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.10/0.34  cnf(c_0_25, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.10/0.34  cnf(c_0_26, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.10/0.34  fof(c_0_27, plain, ![X49]:(k1_relat_1(k6_relat_1(X49))=X49&k2_relat_1(k6_relat_1(X49))=X49), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.10/0.34  fof(c_0_28, plain, ![X18]:(~v1_xboole_0(X18)|v1_relat_1(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).
% 0.10/0.34  fof(c_0_29, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>~(((X1!=k1_xboole_0&r1_tarski(X1,k1_relat_1(X2)))&k9_relat_1(X2,X1)=k1_xboole_0)))), inference(assume_negation,[status(cth)],[t152_relat_1])).
% 0.10/0.34  cnf(c_0_30, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.10/0.34  cnf(c_0_31, plain, (r2_hidden(X2,X5)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,X4)|X5!=k9_relat_1(X3,X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.10/0.34  cnf(c_0_32, plain, (r2_hidden(k4_tarski(X1,esk7_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.10/0.34  cnf(c_0_33, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k9_relat_1(X1,X3))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.10/0.34  cnf(c_0_34, plain, (k2_relat_1(X1)=k9_relat_1(X1,k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.10/0.34  cnf(c_0_35, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.10/0.34  cnf(c_0_36, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t81_relat_1])).
% 0.10/0.34  cnf(c_0_37, plain, (v1_relat_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.10/0.34  cnf(c_0_38, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.10/0.34  cnf(c_0_39, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.10/0.34  fof(c_0_40, negated_conjecture, (v1_relat_1(esk12_0)&((esk11_0!=k1_xboole_0&r1_tarski(esk11_0,k1_relat_1(esk12_0)))&k9_relat_1(esk12_0,esk11_0)=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).
% 0.10/0.34  cnf(c_0_41, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_30])).
% 0.10/0.34  cnf(c_0_42, plain, (r2_hidden(esk8_2(X1,X2),X2)|r2_hidden(k4_tarski(esk8_2(X1,X2),esk9_2(X1,X2)),X1)|X2=k1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.10/0.34  cnf(c_0_43, plain, (r2_hidden(X1,k9_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X4,X1),X2)|~r2_hidden(X4,X3)), inference(er,[status(thm)],[c_0_31])).
% 0.10/0.34  cnf(c_0_44, plain, (r2_hidden(k4_tarski(X1,esk7_3(X2,k1_relat_1(X2),X1)),X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_32])).
% 0.10/0.34  cnf(c_0_45, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))|~v1_xboole_0(k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.10/0.34  cnf(c_0_46, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.10/0.34  cnf(c_0_47, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.10/0.34  cnf(c_0_48, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_39, c_0_36])).
% 0.10/0.34  cnf(c_0_49, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.10/0.34  cnf(c_0_50, negated_conjecture, (r1_tarski(esk11_0,k1_relat_1(esk12_0))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.10/0.34  cnf(c_0_51, plain, (X1=k1_relat_1(X2)|r2_hidden(esk8_2(X2,X1),k1_relat_1(X2))|r2_hidden(esk8_2(X2,X1),X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.10/0.34  cnf(c_0_52, plain, (r2_hidden(esk7_3(X1,k1_relat_1(X1),X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.10/0.34  cnf(c_0_53, negated_conjecture, (k9_relat_1(esk12_0,esk11_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.10/0.34  cnf(c_0_54, negated_conjecture, (v1_relat_1(esk12_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.10/0.34  cnf(c_0_55, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47]), c_0_48]), c_0_38])])).
% 0.10/0.34  cnf(c_0_56, negated_conjecture, (r2_hidden(X1,k1_relat_1(esk12_0))|~r2_hidden(X1,esk11_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.10/0.34  cnf(c_0_57, plain, (X1=X2|r2_hidden(esk8_2(k6_relat_1(X2),X1),X1)|r2_hidden(esk8_2(k6_relat_1(X2),X1),X2)), inference(spm,[status(thm)],[c_0_51, c_0_39])).
% 0.10/0.34  cnf(c_0_58, negated_conjecture, (~r2_hidden(X1,esk11_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])]), c_0_55]), c_0_56])).
% 0.10/0.34  cnf(c_0_59, plain, (k1_xboole_0=X1|r2_hidden(esk8_2(k6_relat_1(X1),k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_55, c_0_57])).
% 0.10/0.34  cnf(c_0_60, negated_conjecture, (esk11_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.10/0.34  cnf(c_0_61, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60]), ['proof']).
% 0.10/0.34  # SZS output end CNFRefutation
% 0.10/0.34  # Proof object total steps             : 62
% 0.10/0.34  # Proof object clause steps            : 39
% 0.10/0.34  # Proof object formula steps           : 23
% 0.10/0.34  # Proof object conjectures             : 10
% 0.10/0.34  # Proof object clause conjectures      : 7
% 0.10/0.34  # Proof object formula conjectures     : 3
% 0.10/0.34  # Proof object initial clauses used    : 20
% 0.10/0.34  # Proof object initial formulas used   : 12
% 0.10/0.34  # Proof object generating inferences   : 16
% 0.10/0.34  # Proof object simplifying inferences  : 12
% 0.10/0.34  # Training examples: 0 positive, 0 negative
% 0.10/0.34  # Parsed axioms                        : 13
% 0.10/0.34  # Removed by relevancy pruning/SinE    : 0
% 0.10/0.34  # Initial clauses                      : 31
% 0.10/0.34  # Removed in clause preprocessing      : 0
% 0.10/0.34  # Initial clauses in saturation        : 31
% 0.10/0.34  # Processed clauses                    : 1646
% 0.10/0.34  # ...of these trivial                  : 0
% 0.10/0.34  # ...subsumed                          : 1236
% 0.10/0.34  # ...remaining for further processing  : 410
% 0.10/0.34  # Other redundant clauses eliminated   : 5
% 0.10/0.34  # Clauses deleted for lack of memory   : 0
% 0.10/0.34  # Backward-subsumed                    : 28
% 0.10/0.34  # Backward-rewritten                   : 2
% 0.10/0.34  # Generated clauses                    : 10190
% 0.10/0.34  # ...of the previous two non-trivial   : 7409
% 0.10/0.34  # Contextual simplify-reflections      : 15
% 0.10/0.34  # Paramodulations                      : 10179
% 0.10/0.34  # Factorizations                       : 6
% 0.10/0.34  # Equation resolutions                 : 5
% 0.10/0.34  # Propositional unsat checks           : 0
% 0.10/0.34  #    Propositional check models        : 0
% 0.10/0.34  #    Propositional check unsatisfiable : 0
% 0.10/0.34  #    Propositional clauses             : 0
% 0.10/0.34  #    Propositional clauses after purity: 0
% 0.10/0.34  #    Propositional unsat core size     : 0
% 0.10/0.34  #    Propositional preprocessing time  : 0.000
% 0.10/0.34  #    Propositional encoding time       : 0.000
% 0.10/0.34  #    Propositional solver time         : 0.000
% 0.10/0.34  #    Success case prop preproc time    : 0.000
% 0.10/0.34  #    Success case prop encoding time   : 0.000
% 0.10/0.34  #    Success case prop solver time     : 0.000
% 0.10/0.34  # Current number of processed clauses  : 375
% 0.10/0.34  #    Positive orientable unit clauses  : 15
% 0.10/0.34  #    Positive unorientable unit clauses: 0
% 0.10/0.34  #    Negative unit clauses             : 3
% 0.10/0.34  #    Non-unit-clauses                  : 357
% 0.10/0.34  # Current number of unprocessed clauses: 5637
% 0.10/0.34  # ...number of literals in the above   : 22306
% 0.10/0.34  # Current number of archived formulas  : 0
% 0.10/0.34  # Current number of archived clauses   : 30
% 0.10/0.34  # Clause-clause subsumption calls (NU) : 34956
% 0.10/0.34  # Rec. Clause-clause subsumption calls : 28395
% 0.10/0.34  # Non-unit clause-clause subsumptions  : 1023
% 0.10/0.34  # Unit Clause-clause subsumption calls : 201
% 0.10/0.34  # Rewrite failures with RHS unbound    : 0
% 0.10/0.34  # BW rewrite match attempts            : 6
% 0.10/0.34  # BW rewrite match successes           : 2
% 0.10/0.34  # Condensation attempts                : 0
% 0.10/0.34  # Condensation successes               : 0
% 0.10/0.34  # Termbank termtop insertions          : 120970
% 0.10/0.34  
% 0.10/0.34  # -------------------------------------------------
% 0.10/0.34  # User time                : 0.082 s
% 0.10/0.34  # System time              : 0.004 s
% 0.10/0.34  # Total time               : 0.086 s
% 0.10/0.34  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
