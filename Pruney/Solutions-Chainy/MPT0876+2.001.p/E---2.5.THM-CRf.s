%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:38 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  123 (4685 expanded)
%              Number of clauses        :  101 (2092 expanded)
%              Number of leaves         :   11 (1213 expanded)
%              Depth                    :   36
%              Number of atoms          :  436 (17670 expanded)
%              Number of equality atoms :  315 (11460 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t36_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( k3_zfmisc_1(X1,X2,X3) = k3_zfmisc_1(X4,X5,X6)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | X3 = k1_xboole_0
        | ( X1 = X4
          & X2 = X5
          & X3 = X6 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t195_relat_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
            & k2_relat_1(k2_zfmisc_1(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(fc3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X2)
     => v1_xboole_0(k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

fof(t117_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))
          | r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) )
        & ~ r1_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(t135_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X1,X2))
        | r1_tarski(X1,k2_zfmisc_1(X2,X1)) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( k3_zfmisc_1(X1,X2,X3) = k3_zfmisc_1(X4,X5,X6)
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | X3 = k1_xboole_0
          | ( X1 = X4
            & X2 = X5
            & X3 = X6 ) ) ) ),
    inference(assume_negation,[status(cth)],[t36_mcart_1])).

fof(c_0_12,negated_conjecture,
    ( k3_zfmisc_1(esk8_0,esk9_0,esk10_0) = k3_zfmisc_1(esk11_0,esk12_0,esk13_0)
    & esk8_0 != k1_xboole_0
    & esk9_0 != k1_xboole_0
    & esk10_0 != k1_xboole_0
    & ( esk8_0 != esk11_0
      | esk9_0 != esk12_0
      | esk10_0 != esk13_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_13,plain,(
    ! [X47,X48,X49] : k3_zfmisc_1(X47,X48,X49) = k2_zfmisc_1(k2_zfmisc_1(X47,X48),X49) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_14,plain,(
    ! [X45,X46] :
      ( ( k1_relat_1(k2_zfmisc_1(X45,X46)) = X45
        | X45 = k1_xboole_0
        | X46 = k1_xboole_0 )
      & ( k2_relat_1(k2_zfmisc_1(X45,X46)) = X46
        | X45 = k1_xboole_0
        | X46 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t195_relat_1])])])).

cnf(c_0_15,negated_conjecture,
    ( k3_zfmisc_1(esk8_0,esk9_0,esk10_0) = k3_zfmisc_1(esk11_0,esk12_0,esk13_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0),esk13_0) = k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0)) = k2_zfmisc_1(esk11_0,esk12_0)
    | k2_zfmisc_1(esk11_0,esk12_0) = k1_xboole_0
    | esk13_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_20,negated_conjecture,
    ( esk10_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_21,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_22,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( ~ r1_tarski(X11,X12)
        | ~ r2_hidden(X13,X11)
        | r2_hidden(X13,X12) )
      & ( r2_hidden(esk2_2(X14,X15),X14)
        | r1_tarski(X14,X15) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | r1_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_23,negated_conjecture,
    ( k2_zfmisc_1(esk11_0,esk12_0) = k2_zfmisc_1(esk8_0,esk9_0)
    | k2_zfmisc_1(esk11_0,esk12_0) = k1_xboole_0
    | k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0
    | esk13_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_19]),c_0_20])).

cnf(c_0_24,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_26,plain,(
    ! [X36,X37] :
      ( ~ v1_xboole_0(X37)
      | v1_xboole_0(k2_zfmisc_1(X36,X37)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_zfmisc_1])])).

fof(c_0_27,plain,(
    ! [X38,X39,X40] :
      ( ( ~ r1_tarski(k2_zfmisc_1(X39,X38),k2_zfmisc_1(X40,X38))
        | X38 = k1_xboole_0
        | r1_tarski(X39,X40) )
      & ( ~ r1_tarski(k2_zfmisc_1(X38,X39),k2_zfmisc_1(X38,X40))
        | X38 = k1_xboole_0
        | r1_tarski(X39,X40) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_zfmisc_1])])])])).

cnf(c_0_28,negated_conjecture,
    ( k1_relat_1(k2_zfmisc_1(esk8_0,esk9_0)) = esk11_0
    | k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0
    | k2_zfmisc_1(esk11_0,esk12_0) = k1_xboole_0
    | esk13_0 = k1_xboole_0
    | esk11_0 = k1_xboole_0
    | esk12_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_17,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( esk9_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_30,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_33,plain,(
    ! [X19,X20,X21,X22,X25,X26,X27,X28,X29,X30,X32,X33] :
      ( ( r2_hidden(esk3_4(X19,X20,X21,X22),X19)
        | ~ r2_hidden(X22,X21)
        | X21 != k2_zfmisc_1(X19,X20) )
      & ( r2_hidden(esk4_4(X19,X20,X21,X22),X20)
        | ~ r2_hidden(X22,X21)
        | X21 != k2_zfmisc_1(X19,X20) )
      & ( X22 = k4_tarski(esk3_4(X19,X20,X21,X22),esk4_4(X19,X20,X21,X22))
        | ~ r2_hidden(X22,X21)
        | X21 != k2_zfmisc_1(X19,X20) )
      & ( ~ r2_hidden(X26,X19)
        | ~ r2_hidden(X27,X20)
        | X25 != k4_tarski(X26,X27)
        | r2_hidden(X25,X21)
        | X21 != k2_zfmisc_1(X19,X20) )
      & ( ~ r2_hidden(esk5_3(X28,X29,X30),X30)
        | ~ r2_hidden(X32,X28)
        | ~ r2_hidden(X33,X29)
        | esk5_3(X28,X29,X30) != k4_tarski(X32,X33)
        | X30 = k2_zfmisc_1(X28,X29) )
      & ( r2_hidden(esk6_3(X28,X29,X30),X28)
        | r2_hidden(esk5_3(X28,X29,X30),X30)
        | X30 = k2_zfmisc_1(X28,X29) )
      & ( r2_hidden(esk7_3(X28,X29,X30),X29)
        | r2_hidden(esk5_3(X28,X29,X30),X30)
        | X30 = k2_zfmisc_1(X28,X29) )
      & ( esk5_3(X28,X29,X30) = k4_tarski(esk6_3(X28,X29,X30),esk7_3(X28,X29,X30))
        | r2_hidden(esk5_3(X28,X29,X30),X30)
        | X30 = k2_zfmisc_1(X28,X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_34,plain,
    ( v1_xboole_0(k2_zfmisc_1(X2,X1))
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_35,plain,(
    ! [X41,X42] :
      ( ( ~ r1_tarski(X41,k2_zfmisc_1(X41,X42))
        | X41 = k1_xboole_0 )
      & ( ~ r1_tarski(X41,k2_zfmisc_1(X42,X41))
        | X41 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t135_zfmisc_1])])])).

cnf(c_0_36,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(X2,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( k2_zfmisc_1(esk11_0,esk12_0) = k1_xboole_0
    | k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0
    | esk12_0 = k1_xboole_0
    | esk11_0 = k1_xboole_0
    | esk13_0 = k1_xboole_0
    | esk11_0 = esk8_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_38,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,plain,
    ( r2_hidden(esk4_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0))
    | ~ v1_xboole_0(esk13_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_18])).

cnf(c_0_41,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0
    | esk11_0 = esk8_0
    | esk13_0 = k1_xboole_0
    | esk12_0 = k1_xboole_0
    | esk11_0 = k1_xboole_0
    | r1_tarski(esk12_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])])).

cnf(c_0_43,plain,
    ( r2_hidden(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_44,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_45,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),X3)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_34])).

cnf(c_0_46,plain,
    ( X2 = k1_xboole_0
    | r1_tarski(X1,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0),X1)
    | ~ v1_xboole_0(esk13_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0
    | esk11_0 = k1_xboole_0
    | esk13_0 = k1_xboole_0
    | esk11_0 = esk8_0
    | esk12_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X2,X3))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_24,c_0_43])).

cnf(c_0_50,plain,
    ( r2_hidden(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_51,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_45])).

cnf(c_0_52,plain,
    ( k2_relat_1(k2_zfmisc_1(X1,X2)) = X2
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),X1)
    | ~ v1_xboole_0(esk13_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_20])).

cnf(c_0_54,negated_conjecture,
    ( esk12_0 = k1_xboole_0
    | esk11_0 = esk8_0
    | esk13_0 = k1_xboole_0
    | esk11_0 = k1_xboole_0
    | r1_tarski(esk9_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_48]),c_0_38])]),c_0_30])).

cnf(c_0_55,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_56,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_32])).

cnf(c_0_57,negated_conjecture,
    ( k2_relat_1(k2_zfmisc_1(esk8_0,esk9_0)) = esk12_0
    | k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0
    | k2_zfmisc_1(esk11_0,esk12_0) = k1_xboole_0
    | esk13_0 = k1_xboole_0
    | esk11_0 = k1_xboole_0
    | esk12_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_23])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(esk8_0,X1)
    | ~ v1_xboole_0(esk13_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_53]),c_0_29])).

cnf(c_0_59,negated_conjecture,
    ( esk11_0 = k1_xboole_0
    | esk13_0 = k1_xboole_0
    | esk11_0 = esk8_0
    | esk12_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_54]),c_0_29])).

cnf(c_0_60,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(k1_xboole_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_32])])).

cnf(c_0_61,negated_conjecture,
    ( k2_zfmisc_1(esk11_0,esk12_0) = k1_xboole_0
    | k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0
    | esk12_0 = k1_xboole_0
    | esk11_0 = k1_xboole_0
    | esk13_0 = k1_xboole_0
    | esk12_0 = esk9_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_57]),c_0_29]),c_0_30])).

cnf(c_0_62,negated_conjecture,
    ( esk12_0 = k1_xboole_0
    | esk11_0 = esk8_0
    | esk11_0 = k1_xboole_0
    | r1_tarski(esk8_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_32])])).

cnf(c_0_63,plain,
    ( r1_tarski(k2_zfmisc_1(k1_xboole_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_60,c_0_25])).

cnf(c_0_64,negated_conjecture,
    ( k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0)) = esk13_0
    | k2_zfmisc_1(esk11_0,esk12_0) = k1_xboole_0
    | esk13_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_18])).

cnf(c_0_65,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0) = k2_zfmisc_1(k1_xboole_0,esk13_0)
    | k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0
    | esk12_0 = esk9_0
    | esk13_0 = k1_xboole_0
    | esk11_0 = k1_xboole_0
    | esk12_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_18,c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( esk11_0 = k1_xboole_0
    | esk11_0 = esk8_0
    | esk12_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_62]),c_0_30])).

cnf(c_0_67,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( k2_zfmisc_1(esk11_0,esk12_0) = k1_xboole_0
    | k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0
    | esk13_0 = k1_xboole_0
    | esk13_0 = esk10_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_64]),c_0_20])).

cnf(c_0_69,negated_conjecture,
    ( k1_relat_1(k2_zfmisc_1(k1_xboole_0,esk13_0)) = k2_zfmisc_1(esk8_0,esk9_0)
    | k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0
    | esk12_0 = k1_xboole_0
    | esk11_0 = k1_xboole_0
    | esk13_0 = k1_xboole_0
    | esk12_0 = esk9_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_65]),c_0_20])).

cnf(c_0_70,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0) = k1_xboole_0
    | esk11_0 = esk8_0
    | esk11_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_66]),c_0_56]),c_0_67])).

cnf(c_0_71,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0) = k2_zfmisc_1(k1_xboole_0,esk13_0)
    | k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0
    | esk13_0 = esk10_0
    | esk13_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_18,c_0_68])).

cnf(c_0_72,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0
    | k1_relat_1(k1_xboole_0) = esk11_0
    | esk12_0 = esk9_0
    | esk13_0 = k1_xboole_0
    | esk11_0 = k1_xboole_0
    | esk12_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_17,c_0_61])).

cnf(c_0_73,negated_conjecture,
    ( k1_relat_1(k1_xboole_0) = k2_zfmisc_1(esk8_0,esk9_0)
    | k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0
    | esk12_0 = esk9_0
    | esk13_0 = k1_xboole_0
    | esk11_0 = k1_xboole_0
    | esk12_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_69,c_0_67])).

cnf(c_0_74,negated_conjecture,
    ( esk11_0 = k1_xboole_0
    | esk11_0 = esk8_0
    | r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_70]),c_0_38])]),c_0_20])).

fof(c_0_75,plain,(
    ! [X17,X18] :
      ( ( r1_tarski(X17,X18)
        | X17 != X18 )
      & ( r1_tarski(X18,X17)
        | X17 != X18 )
      & ( ~ r1_tarski(X17,X18)
        | ~ r1_tarski(X18,X17)
        | X17 = X18 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_76,negated_conjecture,
    ( k2_relat_1(k2_zfmisc_1(k1_xboole_0,esk13_0)) = esk10_0
    | k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0
    | esk12_0 = k1_xboole_0
    | esk11_0 = k1_xboole_0
    | esk13_0 = k1_xboole_0
    | esk12_0 = esk9_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_65]),c_0_20])).

cnf(c_0_77,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0
    | esk13_0 = k1_xboole_0
    | esk13_0 = esk10_0
    | r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),X1)
    | ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,esk13_0),k2_zfmisc_1(X1,esk10_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_71]),c_0_20])).

cnf(c_0_78,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk9_0) = esk11_0
    | k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0
    | esk12_0 = k1_xboole_0
    | esk11_0 = k1_xboole_0
    | esk13_0 = k1_xboole_0
    | esk12_0 = esk9_0 ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( esk11_0 = esk8_0
    | esk11_0 = k1_xboole_0
    | r1_tarski(esk8_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_74]),c_0_29])).

cnf(c_0_80,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_81,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0
    | k2_relat_1(k1_xboole_0) = esk12_0
    | esk12_0 = esk9_0
    | esk13_0 = k1_xboole_0
    | esk11_0 = k1_xboole_0
    | esk12_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_61])).

cnf(c_0_82,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0
    | k2_relat_1(k1_xboole_0) = esk10_0
    | esk12_0 = esk9_0
    | esk13_0 = k1_xboole_0
    | esk11_0 = k1_xboole_0
    | esk12_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_76,c_0_67])).

cnf(c_0_83,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0
    | esk13_0 = esk10_0
    | esk13_0 = k1_xboole_0
    | r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_63])])).

cnf(c_0_84,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0
    | esk12_0 = esk9_0
    | esk13_0 = k1_xboole_0
    | esk11_0 = k1_xboole_0
    | esk12_0 = k1_xboole_0
    | ~ r1_tarski(esk8_0,esk11_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_78]),c_0_30])).

cnf(c_0_85,negated_conjecture,
    ( esk11_0 = k1_xboole_0
    | esk11_0 = esk8_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_79]),c_0_30])).

cnf(c_0_86,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_80])).

cnf(c_0_87,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0
    | esk12_0 = k1_xboole_0
    | esk11_0 = k1_xboole_0
    | esk13_0 = k1_xboole_0
    | esk12_0 = esk9_0
    | esk12_0 = esk10_0 ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_88,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0
    | esk13_0 = k1_xboole_0
    | esk13_0 = esk10_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_83])).

cnf(c_0_89,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0
    | esk11_0 = k1_xboole_0
    | esk12_0 = k1_xboole_0
    | esk13_0 = k1_xboole_0
    | esk12_0 = esk9_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86])]),c_0_30])).

cnf(c_0_90,negated_conjecture,
    ( esk12_0 = esk10_0
    | esk12_0 = esk9_0
    | esk13_0 = k1_xboole_0
    | esk11_0 = k1_xboole_0
    | esk12_0 = k1_xboole_0
    | r1_tarski(esk9_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_87]),c_0_38])]),c_0_30])).

cnf(c_0_91,negated_conjecture,
    ( esk13_0 = esk10_0
    | esk13_0 = k1_xboole_0
    | r1_tarski(esk9_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_88]),c_0_38])]),c_0_30])).

cnf(c_0_92,negated_conjecture,
    ( k2_relat_1(k1_xboole_0) = esk9_0
    | esk12_0 = esk9_0
    | esk13_0 = k1_xboole_0
    | esk12_0 = k1_xboole_0
    | esk11_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_89]),c_0_29]),c_0_30])).

cnf(c_0_93,negated_conjecture,
    ( k2_zfmisc_1(esk11_0,esk12_0) = k1_xboole_0
    | k2_relat_1(k1_xboole_0) = esk13_0
    | esk12_0 = esk9_0
    | esk12_0 = k1_xboole_0
    | esk11_0 = k1_xboole_0
    | esk13_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_89]),c_0_67])).

cnf(c_0_94,negated_conjecture,
    ( esk12_0 = k1_xboole_0
    | esk11_0 = k1_xboole_0
    | esk13_0 = k1_xboole_0
    | esk12_0 = esk9_0
    | esk12_0 = esk10_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_90]),c_0_29])).

cnf(c_0_95,negated_conjecture,
    ( esk8_0 != esk11_0
    | esk9_0 != esk12_0
    | esk10_0 != esk13_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_96,negated_conjecture,
    ( esk13_0 = k1_xboole_0
    | esk13_0 = esk10_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_91]),c_0_29])).

cnf(c_0_97,negated_conjecture,
    ( k2_zfmisc_1(esk11_0,esk12_0) = k1_xboole_0
    | esk11_0 = k1_xboole_0
    | esk12_0 = k1_xboole_0
    | esk13_0 = k1_xboole_0
    | esk12_0 = esk9_0
    | esk13_0 = esk9_0 ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_98,negated_conjecture,
    ( esk12_0 = esk10_0
    | esk12_0 = esk9_0
    | esk11_0 = k1_xboole_0
    | esk12_0 = k1_xboole_0
    | r1_tarski(esk8_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_94]),c_0_32])])).

cnf(c_0_99,negated_conjecture,
    ( esk13_0 = k1_xboole_0
    | esk11_0 != esk8_0
    | esk12_0 != esk9_0 ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_100,negated_conjecture,
    ( k2_relat_1(k1_xboole_0) = esk12_0
    | esk13_0 = esk9_0
    | esk12_0 = esk9_0
    | esk13_0 = k1_xboole_0
    | esk11_0 = k1_xboole_0
    | esk12_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_97])).

cnf(c_0_101,negated_conjecture,
    ( esk12_0 = k1_xboole_0
    | esk11_0 = k1_xboole_0
    | esk12_0 = esk9_0
    | esk12_0 = esk10_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_98]),c_0_30])).

cnf(c_0_102,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0) = k1_xboole_0
    | esk11_0 != esk8_0
    | esk12_0 != esk9_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_99]),c_0_56])).

cnf(c_0_103,negated_conjecture,
    ( esk13_0 = esk9_0
    | esk11_0 = k1_xboole_0
    | esk12_0 = k1_xboole_0
    | esk13_0 = k1_xboole_0
    | esk12_0 = esk9_0 ),
    inference(spm,[status(thm)],[c_0_92,c_0_100])).

cnf(c_0_104,negated_conjecture,
    ( esk12_0 = esk9_0
    | esk11_0 = k1_xboole_0
    | esk12_0 = k1_xboole_0
    | esk10_0 != esk9_0 ),
    inference(ef,[status(thm)],[c_0_101])).

cnf(c_0_105,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),X1)
    | esk11_0 != esk8_0
    | esk12_0 != esk9_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_102]),c_0_38])]),c_0_20])).

cnf(c_0_106,negated_conjecture,
    ( esk12_0 = esk9_0
    | esk13_0 = k1_xboole_0
    | esk12_0 = k1_xboole_0
    | esk11_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_103]),c_0_29]),c_0_104])).

cnf(c_0_107,negated_conjecture,
    ( r1_tarski(esk8_0,X1)
    | esk11_0 != esk8_0
    | esk12_0 != esk9_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_105]),c_0_29])).

cnf(c_0_108,negated_conjecture,
    ( esk11_0 = k1_xboole_0
    | esk12_0 = k1_xboole_0
    | esk12_0 = esk9_0
    | r1_tarski(esk8_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_106]),c_0_32])])).

cnf(c_0_109,negated_conjecture,
    ( esk11_0 != esk8_0
    | esk12_0 != esk9_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_107]),c_0_30])).

cnf(c_0_110,negated_conjecture,
    ( esk12_0 = esk9_0
    | esk12_0 = k1_xboole_0
    | esk11_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_108]),c_0_30])).

cnf(c_0_111,negated_conjecture,
    ( esk11_0 = k1_xboole_0
    | esk12_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_85])).

cnf(c_0_112,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0) = k1_xboole_0
    | esk11_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_111]),c_0_56]),c_0_67])).

cnf(c_0_113,negated_conjecture,
    ( esk11_0 = k1_xboole_0
    | r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_112]),c_0_38])]),c_0_20])).

cnf(c_0_114,negated_conjecture,
    ( esk11_0 = k1_xboole_0
    | r1_tarski(esk8_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_113]),c_0_29])).

cnf(c_0_115,negated_conjecture,
    ( esk11_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_114]),c_0_30])).

cnf(c_0_116,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_115]),c_0_67]),c_0_67])).

cnf(c_0_117,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_116]),c_0_38])]),c_0_20])).

cnf(c_0_118,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_119,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_117])).

cnf(c_0_120,negated_conjecture,
    ( ~ r1_tarski(esk9_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_119]),c_0_29])).

cnf(c_0_121,negated_conjecture,
    ( r1_tarski(esk9_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_119]),c_0_38])]),c_0_30])).

cnf(c_0_122,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_120,c_0_121])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:05:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.49  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.49  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.49  #
% 0.19/0.49  # Preprocessing time       : 0.028 s
% 0.19/0.49  # Presaturation interreduction done
% 0.19/0.49  
% 0.19/0.49  # Proof found!
% 0.19/0.49  # SZS status Theorem
% 0.19/0.49  # SZS output start CNFRefutation
% 0.19/0.49  fof(t36_mcart_1, conjecture, ![X1, X2, X3, X4, X5, X6]:(k3_zfmisc_1(X1,X2,X3)=k3_zfmisc_1(X4,X5,X6)=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|((X1=X4&X2=X5)&X3=X6))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_mcart_1)).
% 0.19/0.49  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.19/0.49  fof(t195_relat_1, axiom, ![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&~((k1_relat_1(k2_zfmisc_1(X1,X2))=X1&k2_relat_1(k2_zfmisc_1(X1,X2))=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t195_relat_1)).
% 0.19/0.49  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.49  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.49  fof(fc3_zfmisc_1, axiom, ![X1, X2]:(v1_xboole_0(X2)=>v1_xboole_0(k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 0.19/0.49  fof(t117_zfmisc_1, axiom, ![X1, X2, X3]:~(((X1!=k1_xboole_0&(r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))|r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))))&~(r1_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 0.19/0.49  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.49  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.19/0.49  fof(t135_zfmisc_1, axiom, ![X1, X2]:((r1_tarski(X1,k2_zfmisc_1(X1,X2))|r1_tarski(X1,k2_zfmisc_1(X2,X1)))=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 0.19/0.49  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.49  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:(k3_zfmisc_1(X1,X2,X3)=k3_zfmisc_1(X4,X5,X6)=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|((X1=X4&X2=X5)&X3=X6)))), inference(assume_negation,[status(cth)],[t36_mcart_1])).
% 0.19/0.49  fof(c_0_12, negated_conjecture, (k3_zfmisc_1(esk8_0,esk9_0,esk10_0)=k3_zfmisc_1(esk11_0,esk12_0,esk13_0)&(((esk8_0!=k1_xboole_0&esk9_0!=k1_xboole_0)&esk10_0!=k1_xboole_0)&(esk8_0!=esk11_0|esk9_0!=esk12_0|esk10_0!=esk13_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.19/0.49  fof(c_0_13, plain, ![X47, X48, X49]:k3_zfmisc_1(X47,X48,X49)=k2_zfmisc_1(k2_zfmisc_1(X47,X48),X49), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.19/0.49  fof(c_0_14, plain, ![X45, X46]:((k1_relat_1(k2_zfmisc_1(X45,X46))=X45|(X45=k1_xboole_0|X46=k1_xboole_0))&(k2_relat_1(k2_zfmisc_1(X45,X46))=X46|(X45=k1_xboole_0|X46=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t195_relat_1])])])).
% 0.19/0.49  cnf(c_0_15, negated_conjecture, (k3_zfmisc_1(esk8_0,esk9_0,esk10_0)=k3_zfmisc_1(esk11_0,esk12_0,esk13_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.49  cnf(c_0_16, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.49  cnf(c_0_17, plain, (k1_relat_1(k2_zfmisc_1(X1,X2))=X1|X1=k1_xboole_0|X2=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.49  cnf(c_0_18, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0),esk13_0)=k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_16])).
% 0.19/0.49  cnf(c_0_19, negated_conjecture, (k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0))=k2_zfmisc_1(esk11_0,esk12_0)|k2_zfmisc_1(esk11_0,esk12_0)=k1_xboole_0|esk13_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.49  cnf(c_0_20, negated_conjecture, (esk10_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.49  fof(c_0_21, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.49  fof(c_0_22, plain, ![X11, X12, X13, X14, X15]:((~r1_tarski(X11,X12)|(~r2_hidden(X13,X11)|r2_hidden(X13,X12)))&((r2_hidden(esk2_2(X14,X15),X14)|r1_tarski(X14,X15))&(~r2_hidden(esk2_2(X14,X15),X15)|r1_tarski(X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.49  cnf(c_0_23, negated_conjecture, (k2_zfmisc_1(esk11_0,esk12_0)=k2_zfmisc_1(esk8_0,esk9_0)|k2_zfmisc_1(esk11_0,esk12_0)=k1_xboole_0|k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0|esk13_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_19]), c_0_20])).
% 0.19/0.49  cnf(c_0_24, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.49  cnf(c_0_25, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.49  fof(c_0_26, plain, ![X36, X37]:(~v1_xboole_0(X37)|v1_xboole_0(k2_zfmisc_1(X36,X37))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_zfmisc_1])])).
% 0.19/0.49  fof(c_0_27, plain, ![X38, X39, X40]:((~r1_tarski(k2_zfmisc_1(X39,X38),k2_zfmisc_1(X40,X38))|X38=k1_xboole_0|r1_tarski(X39,X40))&(~r1_tarski(k2_zfmisc_1(X38,X39),k2_zfmisc_1(X38,X40))|X38=k1_xboole_0|r1_tarski(X39,X40))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_zfmisc_1])])])])).
% 0.19/0.49  cnf(c_0_28, negated_conjecture, (k1_relat_1(k2_zfmisc_1(esk8_0,esk9_0))=esk11_0|k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0|k2_zfmisc_1(esk11_0,esk12_0)=k1_xboole_0|esk13_0=k1_xboole_0|esk11_0=k1_xboole_0|esk12_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_17, c_0_23])).
% 0.19/0.49  cnf(c_0_29, negated_conjecture, (esk9_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.49  cnf(c_0_30, negated_conjecture, (esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.49  cnf(c_0_31, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.49  cnf(c_0_32, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.49  fof(c_0_33, plain, ![X19, X20, X21, X22, X25, X26, X27, X28, X29, X30, X32, X33]:(((((r2_hidden(esk3_4(X19,X20,X21,X22),X19)|~r2_hidden(X22,X21)|X21!=k2_zfmisc_1(X19,X20))&(r2_hidden(esk4_4(X19,X20,X21,X22),X20)|~r2_hidden(X22,X21)|X21!=k2_zfmisc_1(X19,X20)))&(X22=k4_tarski(esk3_4(X19,X20,X21,X22),esk4_4(X19,X20,X21,X22))|~r2_hidden(X22,X21)|X21!=k2_zfmisc_1(X19,X20)))&(~r2_hidden(X26,X19)|~r2_hidden(X27,X20)|X25!=k4_tarski(X26,X27)|r2_hidden(X25,X21)|X21!=k2_zfmisc_1(X19,X20)))&((~r2_hidden(esk5_3(X28,X29,X30),X30)|(~r2_hidden(X32,X28)|~r2_hidden(X33,X29)|esk5_3(X28,X29,X30)!=k4_tarski(X32,X33))|X30=k2_zfmisc_1(X28,X29))&(((r2_hidden(esk6_3(X28,X29,X30),X28)|r2_hidden(esk5_3(X28,X29,X30),X30)|X30=k2_zfmisc_1(X28,X29))&(r2_hidden(esk7_3(X28,X29,X30),X29)|r2_hidden(esk5_3(X28,X29,X30),X30)|X30=k2_zfmisc_1(X28,X29)))&(esk5_3(X28,X29,X30)=k4_tarski(esk6_3(X28,X29,X30),esk7_3(X28,X29,X30))|r2_hidden(esk5_3(X28,X29,X30),X30)|X30=k2_zfmisc_1(X28,X29))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.19/0.49  cnf(c_0_34, plain, (v1_xboole_0(k2_zfmisc_1(X2,X1))|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.49  fof(c_0_35, plain, ![X41, X42]:((~r1_tarski(X41,k2_zfmisc_1(X41,X42))|X41=k1_xboole_0)&(~r1_tarski(X41,k2_zfmisc_1(X42,X41))|X41=k1_xboole_0)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t135_zfmisc_1])])])).
% 0.19/0.49  cnf(c_0_36, plain, (X1=k1_xboole_0|r1_tarski(X2,X3)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.49  cnf(c_0_37, negated_conjecture, (k2_zfmisc_1(esk11_0,esk12_0)=k1_xboole_0|k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0|esk12_0=k1_xboole_0|esk11_0=k1_xboole_0|esk13_0=k1_xboole_0|esk11_0=esk8_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_28]), c_0_29]), c_0_30])).
% 0.19/0.49  cnf(c_0_38, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.49  cnf(c_0_39, plain, (r2_hidden(esk4_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.49  cnf(c_0_40, negated_conjecture, (v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0))|~v1_xboole_0(esk13_0)), inference(spm,[status(thm)],[c_0_34, c_0_18])).
% 0.19/0.49  cnf(c_0_41, plain, (X1=k1_xboole_0|~r1_tarski(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.49  cnf(c_0_42, negated_conjecture, (k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0|esk11_0=esk8_0|esk13_0=k1_xboole_0|esk12_0=k1_xboole_0|esk11_0=k1_xboole_0|r1_tarski(esk12_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])])).
% 0.19/0.49  cnf(c_0_43, plain, (r2_hidden(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_39])).
% 0.19/0.49  cnf(c_0_44, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X1)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.49  cnf(c_0_45, plain, (r1_tarski(k2_zfmisc_1(X1,X2),X3)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_31, c_0_34])).
% 0.19/0.49  cnf(c_0_46, plain, (X2=k1_xboole_0|r1_tarski(X1,X3)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.49  cnf(c_0_47, negated_conjecture, (r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0),X1)|~v1_xboole_0(esk13_0)), inference(spm,[status(thm)],[c_0_31, c_0_40])).
% 0.19/0.49  cnf(c_0_48, negated_conjecture, (k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0|esk11_0=k1_xboole_0|esk13_0=k1_xboole_0|esk11_0=esk8_0|esk12_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.49  cnf(c_0_49, plain, (~r2_hidden(X1,k2_zfmisc_1(X2,X3))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_24, c_0_43])).
% 0.19/0.49  cnf(c_0_50, plain, (r2_hidden(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_44])).
% 0.19/0.49  cnf(c_0_51, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_41, c_0_45])).
% 0.19/0.49  cnf(c_0_52, plain, (k2_relat_1(k2_zfmisc_1(X1,X2))=X2|X1=k1_xboole_0|X2=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.49  cnf(c_0_53, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),X1)|~v1_xboole_0(esk13_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_20])).
% 0.19/0.49  cnf(c_0_54, negated_conjecture, (esk12_0=k1_xboole_0|esk11_0=esk8_0|esk13_0=k1_xboole_0|esk11_0=k1_xboole_0|r1_tarski(esk9_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_48]), c_0_38])]), c_0_30])).
% 0.19/0.49  cnf(c_0_55, plain, (~r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.49  cnf(c_0_56, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_51, c_0_32])).
% 0.19/0.49  cnf(c_0_57, negated_conjecture, (k2_relat_1(k2_zfmisc_1(esk8_0,esk9_0))=esk12_0|k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0|k2_zfmisc_1(esk11_0,esk12_0)=k1_xboole_0|esk13_0=k1_xboole_0|esk11_0=k1_xboole_0|esk12_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_23])).
% 0.19/0.49  cnf(c_0_58, negated_conjecture, (r1_tarski(esk8_0,X1)|~v1_xboole_0(esk13_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_53]), c_0_29])).
% 0.19/0.49  cnf(c_0_59, negated_conjecture, (esk11_0=k1_xboole_0|esk13_0=k1_xboole_0|esk11_0=esk8_0|esk12_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_54]), c_0_29])).
% 0.19/0.49  cnf(c_0_60, plain, (~r2_hidden(X1,k2_zfmisc_1(k1_xboole_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_32])])).
% 0.19/0.49  cnf(c_0_61, negated_conjecture, (k2_zfmisc_1(esk11_0,esk12_0)=k1_xboole_0|k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0|esk12_0=k1_xboole_0|esk11_0=k1_xboole_0|esk13_0=k1_xboole_0|esk12_0=esk9_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_57]), c_0_29]), c_0_30])).
% 0.19/0.49  cnf(c_0_62, negated_conjecture, (esk12_0=k1_xboole_0|esk11_0=esk8_0|esk11_0=k1_xboole_0|r1_tarski(esk8_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_32])])).
% 0.19/0.49  cnf(c_0_63, plain, (r1_tarski(k2_zfmisc_1(k1_xboole_0,X1),X2)), inference(spm,[status(thm)],[c_0_60, c_0_25])).
% 0.19/0.49  cnf(c_0_64, negated_conjecture, (k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0))=esk13_0|k2_zfmisc_1(esk11_0,esk12_0)=k1_xboole_0|esk13_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_18])).
% 0.19/0.49  cnf(c_0_65, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0)=k2_zfmisc_1(k1_xboole_0,esk13_0)|k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0|esk12_0=esk9_0|esk13_0=k1_xboole_0|esk11_0=k1_xboole_0|esk12_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_18, c_0_61])).
% 0.19/0.49  cnf(c_0_66, negated_conjecture, (esk11_0=k1_xboole_0|esk11_0=esk8_0|esk12_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_62]), c_0_30])).
% 0.19/0.49  cnf(c_0_67, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_41, c_0_63])).
% 0.19/0.49  cnf(c_0_68, negated_conjecture, (k2_zfmisc_1(esk11_0,esk12_0)=k1_xboole_0|k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0|esk13_0=k1_xboole_0|esk13_0=esk10_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_64]), c_0_20])).
% 0.19/0.49  cnf(c_0_69, negated_conjecture, (k1_relat_1(k2_zfmisc_1(k1_xboole_0,esk13_0))=k2_zfmisc_1(esk8_0,esk9_0)|k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0|esk12_0=k1_xboole_0|esk11_0=k1_xboole_0|esk13_0=k1_xboole_0|esk12_0=esk9_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_65]), c_0_20])).
% 0.19/0.49  cnf(c_0_70, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0)=k1_xboole_0|esk11_0=esk8_0|esk11_0=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_66]), c_0_56]), c_0_67])).
% 0.19/0.49  cnf(c_0_71, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0)=k2_zfmisc_1(k1_xboole_0,esk13_0)|k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0|esk13_0=esk10_0|esk13_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_18, c_0_68])).
% 0.19/0.49  cnf(c_0_72, negated_conjecture, (k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0|k1_relat_1(k1_xboole_0)=esk11_0|esk12_0=esk9_0|esk13_0=k1_xboole_0|esk11_0=k1_xboole_0|esk12_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_17, c_0_61])).
% 0.19/0.49  cnf(c_0_73, negated_conjecture, (k1_relat_1(k1_xboole_0)=k2_zfmisc_1(esk8_0,esk9_0)|k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0|esk12_0=esk9_0|esk13_0=k1_xboole_0|esk11_0=k1_xboole_0|esk12_0=k1_xboole_0), inference(rw,[status(thm)],[c_0_69, c_0_67])).
% 0.19/0.49  cnf(c_0_74, negated_conjecture, (esk11_0=k1_xboole_0|esk11_0=esk8_0|r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_70]), c_0_38])]), c_0_20])).
% 0.19/0.49  fof(c_0_75, plain, ![X17, X18]:(((r1_tarski(X17,X18)|X17!=X18)&(r1_tarski(X18,X17)|X17!=X18))&(~r1_tarski(X17,X18)|~r1_tarski(X18,X17)|X17=X18)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.49  cnf(c_0_76, negated_conjecture, (k2_relat_1(k2_zfmisc_1(k1_xboole_0,esk13_0))=esk10_0|k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0|esk12_0=k1_xboole_0|esk11_0=k1_xboole_0|esk13_0=k1_xboole_0|esk12_0=esk9_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_65]), c_0_20])).
% 0.19/0.49  cnf(c_0_77, negated_conjecture, (k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0|esk13_0=k1_xboole_0|esk13_0=esk10_0|r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),X1)|~r1_tarski(k2_zfmisc_1(k1_xboole_0,esk13_0),k2_zfmisc_1(X1,esk10_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_71]), c_0_20])).
% 0.19/0.49  cnf(c_0_78, negated_conjecture, (k2_zfmisc_1(esk8_0,esk9_0)=esk11_0|k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0|esk12_0=k1_xboole_0|esk11_0=k1_xboole_0|esk13_0=k1_xboole_0|esk12_0=esk9_0), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.19/0.49  cnf(c_0_79, negated_conjecture, (esk11_0=esk8_0|esk11_0=k1_xboole_0|r1_tarski(esk8_0,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_74]), c_0_29])).
% 0.19/0.49  cnf(c_0_80, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.19/0.49  cnf(c_0_81, negated_conjecture, (k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0|k2_relat_1(k1_xboole_0)=esk12_0|esk12_0=esk9_0|esk13_0=k1_xboole_0|esk11_0=k1_xboole_0|esk12_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_61])).
% 0.19/0.49  cnf(c_0_82, negated_conjecture, (k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0|k2_relat_1(k1_xboole_0)=esk10_0|esk12_0=esk9_0|esk13_0=k1_xboole_0|esk11_0=k1_xboole_0|esk12_0=k1_xboole_0), inference(rw,[status(thm)],[c_0_76, c_0_67])).
% 0.19/0.49  cnf(c_0_83, negated_conjecture, (k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0|esk13_0=esk10_0|esk13_0=k1_xboole_0|r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_63])])).
% 0.19/0.49  cnf(c_0_84, negated_conjecture, (k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0|esk12_0=esk9_0|esk13_0=k1_xboole_0|esk11_0=k1_xboole_0|esk12_0=k1_xboole_0|~r1_tarski(esk8_0,esk11_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_78]), c_0_30])).
% 0.19/0.49  cnf(c_0_85, negated_conjecture, (esk11_0=k1_xboole_0|esk11_0=esk8_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_79]), c_0_30])).
% 0.19/0.49  cnf(c_0_86, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_80])).
% 0.19/0.49  cnf(c_0_87, negated_conjecture, (k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0|esk12_0=k1_xboole_0|esk11_0=k1_xboole_0|esk13_0=k1_xboole_0|esk12_0=esk9_0|esk12_0=esk10_0), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.19/0.49  cnf(c_0_88, negated_conjecture, (k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0|esk13_0=k1_xboole_0|esk13_0=esk10_0), inference(spm,[status(thm)],[c_0_41, c_0_83])).
% 0.19/0.49  cnf(c_0_89, negated_conjecture, (k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0|esk11_0=k1_xboole_0|esk12_0=k1_xboole_0|esk13_0=k1_xboole_0|esk12_0=esk9_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_86])]), c_0_30])).
% 0.19/0.49  cnf(c_0_90, negated_conjecture, (esk12_0=esk10_0|esk12_0=esk9_0|esk13_0=k1_xboole_0|esk11_0=k1_xboole_0|esk12_0=k1_xboole_0|r1_tarski(esk9_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_87]), c_0_38])]), c_0_30])).
% 0.19/0.49  cnf(c_0_91, negated_conjecture, (esk13_0=esk10_0|esk13_0=k1_xboole_0|r1_tarski(esk9_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_88]), c_0_38])]), c_0_30])).
% 0.19/0.49  cnf(c_0_92, negated_conjecture, (k2_relat_1(k1_xboole_0)=esk9_0|esk12_0=esk9_0|esk13_0=k1_xboole_0|esk12_0=k1_xboole_0|esk11_0=k1_xboole_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_89]), c_0_29]), c_0_30])).
% 0.19/0.49  cnf(c_0_93, negated_conjecture, (k2_zfmisc_1(esk11_0,esk12_0)=k1_xboole_0|k2_relat_1(k1_xboole_0)=esk13_0|esk12_0=esk9_0|esk12_0=k1_xboole_0|esk11_0=k1_xboole_0|esk13_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_89]), c_0_67])).
% 0.19/0.49  cnf(c_0_94, negated_conjecture, (esk12_0=k1_xboole_0|esk11_0=k1_xboole_0|esk13_0=k1_xboole_0|esk12_0=esk9_0|esk12_0=esk10_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_90]), c_0_29])).
% 0.19/0.49  cnf(c_0_95, negated_conjecture, (esk8_0!=esk11_0|esk9_0!=esk12_0|esk10_0!=esk13_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.49  cnf(c_0_96, negated_conjecture, (esk13_0=k1_xboole_0|esk13_0=esk10_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_91]), c_0_29])).
% 0.19/0.49  cnf(c_0_97, negated_conjecture, (k2_zfmisc_1(esk11_0,esk12_0)=k1_xboole_0|esk11_0=k1_xboole_0|esk12_0=k1_xboole_0|esk13_0=k1_xboole_0|esk12_0=esk9_0|esk13_0=esk9_0), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 0.19/0.49  cnf(c_0_98, negated_conjecture, (esk12_0=esk10_0|esk12_0=esk9_0|esk11_0=k1_xboole_0|esk12_0=k1_xboole_0|r1_tarski(esk8_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_94]), c_0_32])])).
% 0.19/0.49  cnf(c_0_99, negated_conjecture, (esk13_0=k1_xboole_0|esk11_0!=esk8_0|esk12_0!=esk9_0), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 0.19/0.49  cnf(c_0_100, negated_conjecture, (k2_relat_1(k1_xboole_0)=esk12_0|esk13_0=esk9_0|esk12_0=esk9_0|esk13_0=k1_xboole_0|esk11_0=k1_xboole_0|esk12_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_97])).
% 0.19/0.49  cnf(c_0_101, negated_conjecture, (esk12_0=k1_xboole_0|esk11_0=k1_xboole_0|esk12_0=esk9_0|esk12_0=esk10_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_98]), c_0_30])).
% 0.19/0.49  cnf(c_0_102, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0)=k1_xboole_0|esk11_0!=esk8_0|esk12_0!=esk9_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_99]), c_0_56])).
% 0.19/0.49  cnf(c_0_103, negated_conjecture, (esk13_0=esk9_0|esk11_0=k1_xboole_0|esk12_0=k1_xboole_0|esk13_0=k1_xboole_0|esk12_0=esk9_0), inference(spm,[status(thm)],[c_0_92, c_0_100])).
% 0.19/0.49  cnf(c_0_104, negated_conjecture, (esk12_0=esk9_0|esk11_0=k1_xboole_0|esk12_0=k1_xboole_0|esk10_0!=esk9_0), inference(ef,[status(thm)],[c_0_101])).
% 0.19/0.49  cnf(c_0_105, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),X1)|esk11_0!=esk8_0|esk12_0!=esk9_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_102]), c_0_38])]), c_0_20])).
% 0.19/0.49  cnf(c_0_106, negated_conjecture, (esk12_0=esk9_0|esk13_0=k1_xboole_0|esk12_0=k1_xboole_0|esk11_0=k1_xboole_0), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_103]), c_0_29]), c_0_104])).
% 0.19/0.49  cnf(c_0_107, negated_conjecture, (r1_tarski(esk8_0,X1)|esk11_0!=esk8_0|esk12_0!=esk9_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_105]), c_0_29])).
% 0.19/0.49  cnf(c_0_108, negated_conjecture, (esk11_0=k1_xboole_0|esk12_0=k1_xboole_0|esk12_0=esk9_0|r1_tarski(esk8_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_106]), c_0_32])])).
% 0.19/0.49  cnf(c_0_109, negated_conjecture, (esk11_0!=esk8_0|esk12_0!=esk9_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_107]), c_0_30])).
% 0.19/0.49  cnf(c_0_110, negated_conjecture, (esk12_0=esk9_0|esk12_0=k1_xboole_0|esk11_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_108]), c_0_30])).
% 0.19/0.49  cnf(c_0_111, negated_conjecture, (esk11_0=k1_xboole_0|esk12_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_110]), c_0_85])).
% 0.19/0.49  cnf(c_0_112, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0)=k1_xboole_0|esk11_0=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_111]), c_0_56]), c_0_67])).
% 0.19/0.49  cnf(c_0_113, negated_conjecture, (esk11_0=k1_xboole_0|r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_112]), c_0_38])]), c_0_20])).
% 0.19/0.49  cnf(c_0_114, negated_conjecture, (esk11_0=k1_xboole_0|r1_tarski(esk8_0,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_113]), c_0_29])).
% 0.19/0.49  cnf(c_0_115, negated_conjecture, (esk11_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_114]), c_0_30])).
% 0.19/0.49  cnf(c_0_116, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_115]), c_0_67]), c_0_67])).
% 0.19/0.49  cnf(c_0_117, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_116]), c_0_38])]), c_0_20])).
% 0.19/0.49  cnf(c_0_118, plain, (X1=k1_xboole_0|~r1_tarski(X1,k2_zfmisc_1(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.49  cnf(c_0_119, negated_conjecture, (k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_41, c_0_117])).
% 0.19/0.49  cnf(c_0_120, negated_conjecture, (~r1_tarski(esk9_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_119]), c_0_29])).
% 0.19/0.49  cnf(c_0_121, negated_conjecture, (r1_tarski(esk9_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_119]), c_0_38])]), c_0_30])).
% 0.19/0.49  cnf(c_0_122, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_120, c_0_121])]), ['proof']).
% 0.19/0.49  # SZS output end CNFRefutation
% 0.19/0.49  # Proof object total steps             : 123
% 0.19/0.49  # Proof object clause steps            : 101
% 0.19/0.49  # Proof object formula steps           : 22
% 0.19/0.49  # Proof object conjectures             : 77
% 0.19/0.49  # Proof object clause conjectures      : 74
% 0.19/0.49  # Proof object formula conjectures     : 3
% 0.19/0.49  # Proof object initial clauses used    : 19
% 0.19/0.49  # Proof object initial formulas used   : 11
% 0.19/0.49  # Proof object generating inferences   : 73
% 0.19/0.49  # Proof object simplifying inferences  : 87
% 0.19/0.49  # Training examples: 0 positive, 0 negative
% 0.19/0.49  # Parsed axioms                        : 12
% 0.19/0.49  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.49  # Initial clauses                      : 31
% 0.19/0.49  # Removed in clause preprocessing      : 1
% 0.19/0.49  # Initial clauses in saturation        : 30
% 0.19/0.49  # Processed clauses                    : 1503
% 0.19/0.49  # ...of these trivial                  : 5
% 0.19/0.49  # ...subsumed                          : 970
% 0.19/0.49  # ...remaining for further processing  : 528
% 0.19/0.49  # Other redundant clauses eliminated   : 7
% 0.19/0.49  # Clauses deleted for lack of memory   : 0
% 0.19/0.49  # Backward-subsumed                    : 244
% 0.19/0.49  # Backward-rewritten                   : 133
% 0.19/0.49  # Generated clauses                    : 7908
% 0.19/0.49  # ...of the previous two non-trivial   : 6787
% 0.19/0.49  # Contextual simplify-reflections      : 8
% 0.19/0.49  # Paramodulations                      : 7887
% 0.19/0.49  # Factorizations                       : 15
% 0.19/0.49  # Equation resolutions                 : 7
% 0.19/0.49  # Propositional unsat checks           : 0
% 0.19/0.49  #    Propositional check models        : 0
% 0.19/0.49  #    Propositional check unsatisfiable : 0
% 0.19/0.49  #    Propositional clauses             : 0
% 0.19/0.49  #    Propositional clauses after purity: 0
% 0.19/0.49  #    Propositional unsat core size     : 0
% 0.19/0.49  #    Propositional preprocessing time  : 0.000
% 0.19/0.49  #    Propositional encoding time       : 0.000
% 0.19/0.49  #    Propositional solver time         : 0.000
% 0.19/0.49  #    Success case prop preproc time    : 0.000
% 0.19/0.49  #    Success case prop encoding time   : 0.000
% 0.19/0.49  #    Success case prop solver time     : 0.000
% 0.19/0.49  # Current number of processed clauses  : 116
% 0.19/0.49  #    Positive orientable unit clauses  : 10
% 0.19/0.49  #    Positive unorientable unit clauses: 0
% 0.19/0.49  #    Negative unit clauses             : 6
% 0.19/0.49  #    Non-unit-clauses                  : 100
% 0.19/0.49  # Current number of unprocessed clauses: 4678
% 0.19/0.49  # ...number of literals in the above   : 25018
% 0.19/0.49  # Current number of archived formulas  : 0
% 0.19/0.49  # Current number of archived clauses   : 407
% 0.19/0.49  # Clause-clause subsumption calls (NU) : 16586
% 0.19/0.49  # Rec. Clause-clause subsumption calls : 4276
% 0.19/0.49  # Non-unit clause-clause subsumptions  : 790
% 0.19/0.49  # Unit Clause-clause subsumption calls : 209
% 0.19/0.49  # Rewrite failures with RHS unbound    : 0
% 0.19/0.49  # BW rewrite match attempts            : 11
% 0.19/0.49  # BW rewrite match successes           : 11
% 0.19/0.49  # Condensation attempts                : 0
% 0.19/0.49  # Condensation successes               : 0
% 0.19/0.49  # Termbank termtop insertions          : 104809
% 0.19/0.49  
% 0.19/0.49  # -------------------------------------------------
% 0.19/0.49  # User time                : 0.152 s
% 0.19/0.49  # System time              : 0.008 s
% 0.19/0.49  # Total time               : 0.160 s
% 0.19/0.49  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
