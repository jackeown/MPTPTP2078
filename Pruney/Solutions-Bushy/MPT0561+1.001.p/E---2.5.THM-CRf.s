%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0561+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:49 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   41 (  93 expanded)
%              Number of clauses        :   26 (  44 expanded)
%              Number of leaves         :    7 (  21 expanded)
%              Depth                    :   11
%              Number of atoms          :  170 ( 368 expanded)
%              Number of equality atoms :   29 (  58 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t163_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k3_xboole_0(k1_relat_1(X2),X1),k9_relat_1(k4_relat_1(X2),k9_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_relat_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(d7_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( X2 = k4_relat_1(X1)
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> r2_hidden(k4_tarski(X4,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_relat_1)).

fof(dt_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

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

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k3_xboole_0(k1_relat_1(X2),X1),k9_relat_1(k4_relat_1(X2),k9_relat_1(X2,X1))) ) ),
    inference(assume_negation,[status(cth)],[t163_relat_1])).

fof(c_0_8,plain,(
    ! [X35,X36,X37,X38,X39,X40,X41,X42] :
      ( ( r2_hidden(X38,X35)
        | ~ r2_hidden(X38,X37)
        | X37 != k3_xboole_0(X35,X36) )
      & ( r2_hidden(X38,X36)
        | ~ r2_hidden(X38,X37)
        | X37 != k3_xboole_0(X35,X36) )
      & ( ~ r2_hidden(X39,X35)
        | ~ r2_hidden(X39,X36)
        | r2_hidden(X39,X37)
        | X37 != k3_xboole_0(X35,X36) )
      & ( ~ r2_hidden(esk8_3(X40,X41,X42),X42)
        | ~ r2_hidden(esk8_3(X40,X41,X42),X40)
        | ~ r2_hidden(esk8_3(X40,X41,X42),X41)
        | X42 = k3_xboole_0(X40,X41) )
      & ( r2_hidden(esk8_3(X40,X41,X42),X40)
        | r2_hidden(esk8_3(X40,X41,X42),X42)
        | X42 = k3_xboole_0(X40,X41) )
      & ( r2_hidden(esk8_3(X40,X41,X42),X41)
        | r2_hidden(esk8_3(X40,X41,X42),X42)
        | X42 = k3_xboole_0(X40,X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_9,negated_conjecture,
    ( v1_relat_1(esk12_0)
    & ~ r1_tarski(k3_xboole_0(k1_relat_1(esk12_0),esk11_0),k9_relat_1(k4_relat_1(esk12_0),k9_relat_1(esk12_0,esk11_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X18,X19,X20,X21,X22] :
      ( ( ~ r1_tarski(X18,X19)
        | ~ r2_hidden(X20,X18)
        | r2_hidden(X20,X19) )
      & ( r2_hidden(esk4_2(X21,X22),X21)
        | r1_tarski(X21,X22) )
      & ( ~ r2_hidden(esk4_2(X21,X22),X22)
        | r1_tarski(X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_11,plain,(
    ! [X24,X25,X26,X28,X29,X30,X31,X33] :
      ( ( ~ r2_hidden(X26,X25)
        | r2_hidden(k4_tarski(X26,esk5_3(X24,X25,X26)),X24)
        | X25 != k1_relat_1(X24) )
      & ( ~ r2_hidden(k4_tarski(X28,X29),X24)
        | r2_hidden(X28,X25)
        | X25 != k1_relat_1(X24) )
      & ( ~ r2_hidden(esk6_2(X30,X31),X31)
        | ~ r2_hidden(k4_tarski(esk6_2(X30,X31),X33),X30)
        | X31 = k1_relat_1(X30) )
      & ( r2_hidden(esk6_2(X30,X31),X31)
        | r2_hidden(k4_tarski(esk6_2(X30,X31),esk7_2(X30,X31)),X30)
        | X31 = k1_relat_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( ~ r1_tarski(k3_xboole_0(k1_relat_1(esk12_0),esk11_0),k9_relat_1(k4_relat_1(esk12_0),k9_relat_1(esk12_0,esk11_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X44,X45,X46,X47,X48,X49] :
      ( ( ~ r2_hidden(k4_tarski(X46,X47),X45)
        | r2_hidden(k4_tarski(X47,X46),X44)
        | X45 != k4_relat_1(X44)
        | ~ v1_relat_1(X45)
        | ~ v1_relat_1(X44) )
      & ( ~ r2_hidden(k4_tarski(X49,X48),X44)
        | r2_hidden(k4_tarski(X48,X49),X45)
        | X45 != k4_relat_1(X44)
        | ~ v1_relat_1(X45)
        | ~ v1_relat_1(X44) )
      & ( ~ r2_hidden(k4_tarski(esk9_2(X44,X45),esk10_2(X44,X45)),X45)
        | ~ r2_hidden(k4_tarski(esk10_2(X44,X45),esk9_2(X44,X45)),X44)
        | X45 = k4_relat_1(X44)
        | ~ v1_relat_1(X45)
        | ~ v1_relat_1(X44) )
      & ( r2_hidden(k4_tarski(esk9_2(X44,X45),esk10_2(X44,X45)),X45)
        | r2_hidden(k4_tarski(esk10_2(X44,X45),esk9_2(X44,X45)),X44)
        | X45 = k4_relat_1(X44)
        | ~ v1_relat_1(X45)
        | ~ v1_relat_1(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_relat_1])])])])])])).

fof(c_0_16,plain,(
    ! [X52] :
      ( ~ v1_relat_1(X52)
      | v1_relat_1(k4_relat_1(X52)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).

cnf(c_0_17,plain,
    ( r2_hidden(k4_tarski(X1,esk5_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk4_2(k3_xboole_0(k1_relat_1(esk12_0),esk11_0),k9_relat_1(k4_relat_1(esk12_0),k9_relat_1(esk12_0,esk11_0))),k3_xboole_0(k1_relat_1(esk12_0),esk11_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_20,plain,(
    ! [X6,X7,X8,X9,X11,X12,X13,X14,X16] :
      ( ( r2_hidden(k4_tarski(esk1_4(X6,X7,X8,X9),X9),X6)
        | ~ r2_hidden(X9,X8)
        | X8 != k9_relat_1(X6,X7)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(esk1_4(X6,X7,X8,X9),X7)
        | ~ r2_hidden(X9,X8)
        | X8 != k9_relat_1(X6,X7)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(k4_tarski(X12,X11),X6)
        | ~ r2_hidden(X12,X7)
        | r2_hidden(X11,X8)
        | X8 != k9_relat_1(X6,X7)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(esk2_3(X6,X13,X14),X14)
        | ~ r2_hidden(k4_tarski(X16,esk2_3(X6,X13,X14)),X6)
        | ~ r2_hidden(X16,X13)
        | X14 = k9_relat_1(X6,X13)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(k4_tarski(esk3_3(X6,X13,X14),esk2_3(X6,X13,X14)),X6)
        | r2_hidden(esk2_3(X6,X13,X14),X14)
        | X14 = k9_relat_1(X6,X13)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(esk3_3(X6,X13,X14),X13)
        | r2_hidden(esk2_3(X6,X13,X14),X14)
        | X14 = k9_relat_1(X6,X13)
        | ~ v1_relat_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_relat_1])])])])])])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(X2,X1),X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k4_relat_1(X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( v1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( r2_hidden(k4_tarski(X1,esk5_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk4_2(k3_xboole_0(k1_relat_1(esk12_0),esk11_0),k9_relat_1(k4_relat_1(esk12_0),k9_relat_1(esk12_0,esk11_0))),k1_relat_1(esk12_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( r2_hidden(X2,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | X5 != k9_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( r2_hidden(k4_tarski(X1,X2),k4_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X1),X3)
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_21]),c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_2(k3_xboole_0(k1_relat_1(esk12_0),esk11_0),k9_relat_1(k4_relat_1(esk12_0),k9_relat_1(esk12_0,esk11_0))),esk5_3(esk12_0,k1_relat_1(esk12_0),esk4_2(k3_xboole_0(k1_relat_1(esk12_0),esk11_0),k9_relat_1(k4_relat_1(esk12_0),k9_relat_1(esk12_0,esk11_0))))),esk12_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,k9_relat_1(X2,X3))
    | ~ r2_hidden(k4_tarski(X4,X1),X2)
    | ~ r2_hidden(X4,X3)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_3(esk12_0,k1_relat_1(esk12_0),esk4_2(k3_xboole_0(k1_relat_1(esk12_0),esk11_0),k9_relat_1(k4_relat_1(esk12_0),k9_relat_1(esk12_0,esk11_0)))),esk4_2(k3_xboole_0(k1_relat_1(esk12_0),esk11_0),k9_relat_1(k4_relat_1(esk12_0),k9_relat_1(esk12_0,esk11_0)))),k4_relat_1(esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk4_2(k3_xboole_0(k1_relat_1(esk12_0),esk11_0),k9_relat_1(k4_relat_1(esk12_0),k9_relat_1(esk12_0,esk11_0))),k9_relat_1(k4_relat_1(esk12_0),X1))
    | ~ r2_hidden(esk5_3(esk12_0,k1_relat_1(esk12_0),esk4_2(k3_xboole_0(k1_relat_1(esk12_0),esk11_0),k9_relat_1(k4_relat_1(esk12_0),k9_relat_1(esk12_0,esk11_0)))),X1)
    | ~ v1_relat_1(k4_relat_1(esk12_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk5_3(esk12_0,k1_relat_1(esk12_0),esk4_2(k3_xboole_0(k1_relat_1(esk12_0),esk11_0),k9_relat_1(k4_relat_1(esk12_0),k9_relat_1(esk12_0,esk11_0)))),k9_relat_1(esk12_0,X1))
    | ~ r2_hidden(esk4_2(k3_xboole_0(k1_relat_1(esk12_0),esk11_0),k9_relat_1(k4_relat_1(esk12_0),k9_relat_1(esk12_0,esk11_0))),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_27]),c_0_28])])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk4_2(k3_xboole_0(k1_relat_1(esk12_0),esk11_0),k9_relat_1(k4_relat_1(esk12_0),k9_relat_1(esk12_0,esk11_0))),esk11_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_19])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk4_2(k3_xboole_0(k1_relat_1(esk12_0),esk11_0),k9_relat_1(k4_relat_1(esk12_0),k9_relat_1(esk12_0,esk11_0))),k9_relat_1(k4_relat_1(esk12_0),X1))
    | ~ r2_hidden(esk5_3(esk12_0,k1_relat_1(esk12_0),esk4_2(k3_xboole_0(k1_relat_1(esk12_0),esk11_0),k9_relat_1(k4_relat_1(esk12_0),k9_relat_1(esk12_0,esk11_0)))),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_22]),c_0_28])])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk5_3(esk12_0,k1_relat_1(esk12_0),esk4_2(k3_xboole_0(k1_relat_1(esk12_0),esk11_0),k9_relat_1(k4_relat_1(esk12_0),k9_relat_1(esk12_0,esk11_0)))),k9_relat_1(esk12_0,esk11_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk4_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk4_2(k3_xboole_0(k1_relat_1(esk12_0),esk11_0),k9_relat_1(k4_relat_1(esk12_0),k9_relat_1(esk12_0,esk11_0))),k9_relat_1(k4_relat_1(esk12_0),k9_relat_1(esk12_0,esk11_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_13]),
    [proof]).

%------------------------------------------------------------------------------
