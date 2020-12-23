%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:06 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 518 expanded)
%              Number of clauses        :   49 ( 193 expanded)
%              Number of leaves         :    8 ( 122 expanded)
%              Depth                    :   16
%              Number of atoms          :  266 (3822 expanded)
%              Number of equality atoms :   62 (1439 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t156_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( v1_relat_1(X4)
                & v1_funct_1(X4) )
             => ( ( X1 = k2_relat_1(X2)
                  & k1_relat_1(X3) = X1
                  & k1_relat_1(X4) = X1
                  & k5_relat_1(X2,X3) = k5_relat_1(X2,X4) )
               => X3 = X4 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_funct_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(t23_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(X2))
           => k1_funct_1(k5_relat_1(X2,X3),X1) = k1_funct_1(X3,k1_funct_1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

fof(d5_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( X2 = k2_relat_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                  & X3 = k1_funct_1(X1,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(d3_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_tarski(X1,X2)
        <=> ! [X3,X4] :
              ( r2_hidden(k4_tarski(X3,X4),X1)
             => r2_hidden(k4_tarski(X3,X4),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( v1_relat_1(X3)
              & v1_funct_1(X3) )
           => ! [X4] :
                ( ( v1_relat_1(X4)
                  & v1_funct_1(X4) )
               => ( ( X1 = k2_relat_1(X2)
                    & k1_relat_1(X3) = X1
                    & k1_relat_1(X4) = X1
                    & k5_relat_1(X2,X3) = k5_relat_1(X2,X4) )
                 => X3 = X4 ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t156_funct_1])).

fof(c_0_9,plain,(
    ! [X44,X45,X46] :
      ( ( r2_hidden(X44,k1_relat_1(X46))
        | ~ r2_hidden(k4_tarski(X44,X45),X46)
        | ~ v1_relat_1(X46)
        | ~ v1_funct_1(X46) )
      & ( X45 = k1_funct_1(X46,X44)
        | ~ r2_hidden(k4_tarski(X44,X45),X46)
        | ~ v1_relat_1(X46)
        | ~ v1_funct_1(X46) )
      & ( ~ r2_hidden(X44,k1_relat_1(X46))
        | X45 != k1_funct_1(X46,X44)
        | r2_hidden(k4_tarski(X44,X45),X46)
        | ~ v1_relat_1(X46)
        | ~ v1_funct_1(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

fof(c_0_10,negated_conjecture,
    ( v1_relat_1(esk11_0)
    & v1_funct_1(esk11_0)
    & v1_relat_1(esk12_0)
    & v1_funct_1(esk12_0)
    & v1_relat_1(esk13_0)
    & v1_funct_1(esk13_0)
    & esk10_0 = k2_relat_1(esk11_0)
    & k1_relat_1(esk12_0) = esk10_0
    & k1_relat_1(esk13_0) = esk10_0
    & k5_relat_1(esk11_0,esk12_0) = k5_relat_1(esk11_0,esk13_0)
    & esk12_0 != esk13_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_11,plain,
    ( r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( k1_relat_1(esk13_0) = esk10_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( esk10_0 = k2_relat_1(esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X41,X42,X43] :
      ( ~ v1_relat_1(X42)
      | ~ v1_funct_1(X42)
      | ~ v1_relat_1(X43)
      | ~ v1_funct_1(X43)
      | ~ r2_hidden(X41,k1_relat_1(X42))
      | k1_funct_1(k5_relat_1(X42,X43),X41) = k1_funct_1(X43,k1_funct_1(X42,X41)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_1])])])).

cnf(c_0_15,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( k1_relat_1(esk13_0) = k2_relat_1(esk11_0) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( v1_funct_1(esk13_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( v1_relat_1(esk13_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( k1_funct_1(k5_relat_1(X1,X2),X3) = k1_funct_1(X2,k1_funct_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( k5_relat_1(esk11_0,esk12_0) = k5_relat_1(esk11_0,esk13_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_1(esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(esk13_0,X1)),esk13_0)
    | ~ r2_hidden(X1,k2_relat_1(esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_24,negated_conjecture,
    ( k1_funct_1(esk13_0,k1_funct_1(esk11_0,X1)) = k1_funct_1(k5_relat_1(esk11_0,esk12_0),X1)
    | ~ r2_hidden(X1,k1_relat_1(esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_17]),c_0_21]),c_0_18]),c_0_22])])).

fof(c_0_25,plain,(
    ! [X31,X32,X33,X35,X36,X37,X39] :
      ( ( r2_hidden(esk7_3(X31,X32,X33),k1_relat_1(X31))
        | ~ r2_hidden(X33,X32)
        | X32 != k2_relat_1(X31)
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) )
      & ( X33 = k1_funct_1(X31,esk7_3(X31,X32,X33))
        | ~ r2_hidden(X33,X32)
        | X32 != k2_relat_1(X31)
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) )
      & ( ~ r2_hidden(X36,k1_relat_1(X31))
        | X35 != k1_funct_1(X31,X36)
        | r2_hidden(X35,X32)
        | X32 != k2_relat_1(X31)
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) )
      & ( ~ r2_hidden(esk8_2(X31,X37),X37)
        | ~ r2_hidden(X39,k1_relat_1(X31))
        | esk8_2(X31,X37) != k1_funct_1(X31,X39)
        | X37 = k2_relat_1(X31)
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) )
      & ( r2_hidden(esk9_2(X31,X37),k1_relat_1(X31))
        | r2_hidden(esk8_2(X31,X37),X37)
        | X37 = k2_relat_1(X31)
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) )
      & ( esk8_2(X31,X37) = k1_funct_1(X31,esk9_2(X31,X37))
        | r2_hidden(esk8_2(X31,X37),X37)
        | X37 = k2_relat_1(X31)
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_26,plain,(
    ! [X20,X21,X22,X24,X25,X26,X27,X29] :
      ( ( ~ r2_hidden(X22,X21)
        | r2_hidden(k4_tarski(X22,esk4_3(X20,X21,X22)),X20)
        | X21 != k1_relat_1(X20) )
      & ( ~ r2_hidden(k4_tarski(X24,X25),X20)
        | r2_hidden(X24,X21)
        | X21 != k1_relat_1(X20) )
      & ( ~ r2_hidden(esk5_2(X26,X27),X27)
        | ~ r2_hidden(k4_tarski(esk5_2(X26,X27),X29),X26)
        | X27 = k1_relat_1(X26) )
      & ( r2_hidden(esk5_2(X26,X27),X27)
        | r2_hidden(k4_tarski(esk5_2(X26,X27),esk6_2(X26,X27)),X26)
        | X27 = k1_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

fof(c_0_27,plain,(
    ! [X13,X14,X15,X16,X17] :
      ( ( ~ r1_tarski(X13,X14)
        | ~ r2_hidden(k4_tarski(X15,X16),X13)
        | r2_hidden(k4_tarski(X15,X16),X14)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(k4_tarski(esk2_2(X13,X17),esk3_2(X13,X17)),X13)
        | r1_tarski(X13,X17)
        | ~ v1_relat_1(X13) )
      & ( ~ r2_hidden(k4_tarski(esk2_2(X13,X17),esk3_2(X13,X17)),X17)
        | r1_tarski(X13,X17)
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(k4_tarski(k1_funct_1(esk11_0,X1),k1_funct_1(k5_relat_1(esk11_0,esk12_0),X1)),esk13_0)
    | ~ r2_hidden(k1_funct_1(esk11_0,X1),k2_relat_1(esk11_0))
    | ~ r2_hidden(X1,k1_relat_1(esk11_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_1(esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_30,negated_conjecture,
    ( v1_relat_1(esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_31,plain,
    ( X1 = k1_funct_1(X2,esk7_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_34,plain,
    ( r2_hidden(k4_tarski(esk2_2(X1,X2),esk3_2(X1,X2)),X1)
    | r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(k4_tarski(k1_funct_1(esk11_0,X1),k1_funct_1(esk12_0,k1_funct_1(esk11_0,X1))),esk13_0)
    | ~ r2_hidden(k1_funct_1(esk11_0,X1),k2_relat_1(esk11_0))
    | ~ r2_hidden(X1,k1_relat_1(esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_19]),c_0_29]),c_0_21]),c_0_30]),c_0_22])])).

cnf(c_0_36,plain,
    ( k1_funct_1(X1,esk7_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( r2_hidden(esk7_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( k1_relat_1(esk12_0) = esk10_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(esk2_2(X1,X2),esk3_2(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_41,plain,
    ( esk3_2(X1,X2) = k1_funct_1(X1,esk2_2(X1,X2))
    | r1_tarski(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(esk12_0,X1)),esk13_0)
    | ~ r2_hidden(esk7_3(esk11_0,k2_relat_1(esk11_0),X1),k1_relat_1(esk11_0))
    | ~ r2_hidden(X1,k2_relat_1(esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_21]),c_0_22])])).

cnf(c_0_43,plain,
    ( r2_hidden(esk7_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( r2_hidden(esk2_2(X1,X2),k1_relat_1(X1))
    | r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_34])).

cnf(c_0_45,negated_conjecture,
    ( k1_relat_1(esk12_0) = k2_relat_1(esk11_0) ),
    inference(rw,[status(thm)],[c_0_39,c_0_13])).

fof(c_0_46,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(esk2_2(X1,X2),k1_funct_1(X1,esk2_2(X1,X2))),X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(esk12_0,X1)),esk13_0)
    | ~ r2_hidden(X1,k2_relat_1(esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_21]),c_0_22])])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk2_2(esk12_0,X1),k2_relat_1(esk11_0))
    | r1_tarski(esk12_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_30])])).

cnf(c_0_50,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk12_0,esk13_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_29]),c_0_30])]),c_0_49])).

cnf(c_0_52,plain,
    ( r2_hidden(k4_tarski(X1,esk4_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(X1,esk13_0)
    | ~ r2_hidden(X1,esk12_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_54,plain,
    ( r2_hidden(k4_tarski(X1,esk4_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_55,negated_conjecture,
    ( X1 = k1_funct_1(esk13_0,X2)
    | ~ r2_hidden(k4_tarski(X2,X1),esk12_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_53]),c_0_17]),c_0_18])])).

fof(c_0_56,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk4_3(esk12_0,k2_relat_1(esk11_0),X1)),esk12_0)
    | ~ r2_hidden(X1,k2_relat_1(esk11_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_45])).

cnf(c_0_58,negated_conjecture,
    ( esk4_3(esk12_0,k2_relat_1(esk11_0),X1) = k1_funct_1(esk13_0,X1)
    | ~ r2_hidden(X1,k2_relat_1(esk11_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_54]),c_0_45]),c_0_45])).

cnf(c_0_59,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( esk12_0 != esk13_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(esk13_0,X1)),esk12_0)
    | ~ r2_hidden(X1,k2_relat_1(esk11_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( ~ r1_tarski(esk13_0,esk12_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_51]),c_0_60])).

cnf(c_0_63,negated_conjecture,
    ( ~ r2_hidden(esk2_2(esk13_0,esk12_0),k2_relat_1(esk11_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_61]),c_0_17]),c_0_18])]),c_0_62])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk2_2(esk13_0,X1),k2_relat_1(esk11_0))
    | r1_tarski(esk13_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_16]),c_0_18])])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_62]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.20/0.34  % DateTime   : Tue Dec  1 11:35:11 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  # Version: 2.5pre002
% 0.20/0.34  # No SInE strategy applied
% 0.20/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S5PRR_S0Y
% 0.20/0.41  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.031 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(t156_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>![X4]:((v1_relat_1(X4)&v1_funct_1(X4))=>((((X1=k2_relat_1(X2)&k1_relat_1(X3)=X1)&k1_relat_1(X4)=X1)&k5_relat_1(X2,X3)=k5_relat_1(X2,X4))=>X3=X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_funct_1)).
% 0.20/0.41  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 0.20/0.41  fof(t23_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(X2))=>k1_funct_1(k5_relat_1(X2,X3),X1)=k1_funct_1(X3,k1_funct_1(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 0.20/0.41  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 0.20/0.41  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 0.20/0.41  fof(d3_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_tarski(X1,X2)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X1)=>r2_hidden(k4_tarski(X3,X4),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relat_1)).
% 0.20/0.41  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.41  fof(c_0_8, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>![X4]:((v1_relat_1(X4)&v1_funct_1(X4))=>((((X1=k2_relat_1(X2)&k1_relat_1(X3)=X1)&k1_relat_1(X4)=X1)&k5_relat_1(X2,X3)=k5_relat_1(X2,X4))=>X3=X4))))), inference(assume_negation,[status(cth)],[t156_funct_1])).
% 0.20/0.41  fof(c_0_9, plain, ![X44, X45, X46]:(((r2_hidden(X44,k1_relat_1(X46))|~r2_hidden(k4_tarski(X44,X45),X46)|(~v1_relat_1(X46)|~v1_funct_1(X46)))&(X45=k1_funct_1(X46,X44)|~r2_hidden(k4_tarski(X44,X45),X46)|(~v1_relat_1(X46)|~v1_funct_1(X46))))&(~r2_hidden(X44,k1_relat_1(X46))|X45!=k1_funct_1(X46,X44)|r2_hidden(k4_tarski(X44,X45),X46)|(~v1_relat_1(X46)|~v1_funct_1(X46)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.20/0.41  fof(c_0_10, negated_conjecture, ((v1_relat_1(esk11_0)&v1_funct_1(esk11_0))&((v1_relat_1(esk12_0)&v1_funct_1(esk12_0))&((v1_relat_1(esk13_0)&v1_funct_1(esk13_0))&((((esk10_0=k2_relat_1(esk11_0)&k1_relat_1(esk12_0)=esk10_0)&k1_relat_1(esk13_0)=esk10_0)&k5_relat_1(esk11_0,esk12_0)=k5_relat_1(esk11_0,esk13_0))&esk12_0!=esk13_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.20/0.41  cnf(c_0_11, plain, (r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_12, negated_conjecture, (k1_relat_1(esk13_0)=esk10_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_13, negated_conjecture, (esk10_0=k2_relat_1(esk11_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  fof(c_0_14, plain, ![X41, X42, X43]:(~v1_relat_1(X42)|~v1_funct_1(X42)|(~v1_relat_1(X43)|~v1_funct_1(X43)|(~r2_hidden(X41,k1_relat_1(X42))|k1_funct_1(k5_relat_1(X42,X43),X41)=k1_funct_1(X43,k1_funct_1(X42,X41))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_1])])])).
% 0.20/0.41  cnf(c_0_15, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_11])).
% 0.20/0.41  cnf(c_0_16, negated_conjecture, (k1_relat_1(esk13_0)=k2_relat_1(esk11_0)), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.20/0.41  cnf(c_0_17, negated_conjecture, (v1_funct_1(esk13_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_18, negated_conjecture, (v1_relat_1(esk13_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_19, plain, (k1_funct_1(k5_relat_1(X1,X2),X3)=k1_funct_1(X2,k1_funct_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_20, negated_conjecture, (k5_relat_1(esk11_0,esk12_0)=k5_relat_1(esk11_0,esk13_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_21, negated_conjecture, (v1_funct_1(esk11_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_22, negated_conjecture, (v1_relat_1(esk11_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_23, negated_conjecture, (r2_hidden(k4_tarski(X1,k1_funct_1(esk13_0,X1)),esk13_0)|~r2_hidden(X1,k2_relat_1(esk11_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18])])).
% 0.20/0.41  cnf(c_0_24, negated_conjecture, (k1_funct_1(esk13_0,k1_funct_1(esk11_0,X1))=k1_funct_1(k5_relat_1(esk11_0,esk12_0),X1)|~r2_hidden(X1,k1_relat_1(esk11_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_17]), c_0_21]), c_0_18]), c_0_22])])).
% 0.20/0.41  fof(c_0_25, plain, ![X31, X32, X33, X35, X36, X37, X39]:((((r2_hidden(esk7_3(X31,X32,X33),k1_relat_1(X31))|~r2_hidden(X33,X32)|X32!=k2_relat_1(X31)|(~v1_relat_1(X31)|~v1_funct_1(X31)))&(X33=k1_funct_1(X31,esk7_3(X31,X32,X33))|~r2_hidden(X33,X32)|X32!=k2_relat_1(X31)|(~v1_relat_1(X31)|~v1_funct_1(X31))))&(~r2_hidden(X36,k1_relat_1(X31))|X35!=k1_funct_1(X31,X36)|r2_hidden(X35,X32)|X32!=k2_relat_1(X31)|(~v1_relat_1(X31)|~v1_funct_1(X31))))&((~r2_hidden(esk8_2(X31,X37),X37)|(~r2_hidden(X39,k1_relat_1(X31))|esk8_2(X31,X37)!=k1_funct_1(X31,X39))|X37=k2_relat_1(X31)|(~v1_relat_1(X31)|~v1_funct_1(X31)))&((r2_hidden(esk9_2(X31,X37),k1_relat_1(X31))|r2_hidden(esk8_2(X31,X37),X37)|X37=k2_relat_1(X31)|(~v1_relat_1(X31)|~v1_funct_1(X31)))&(esk8_2(X31,X37)=k1_funct_1(X31,esk9_2(X31,X37))|r2_hidden(esk8_2(X31,X37),X37)|X37=k2_relat_1(X31)|(~v1_relat_1(X31)|~v1_funct_1(X31)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.20/0.41  fof(c_0_26, plain, ![X20, X21, X22, X24, X25, X26, X27, X29]:(((~r2_hidden(X22,X21)|r2_hidden(k4_tarski(X22,esk4_3(X20,X21,X22)),X20)|X21!=k1_relat_1(X20))&(~r2_hidden(k4_tarski(X24,X25),X20)|r2_hidden(X24,X21)|X21!=k1_relat_1(X20)))&((~r2_hidden(esk5_2(X26,X27),X27)|~r2_hidden(k4_tarski(esk5_2(X26,X27),X29),X26)|X27=k1_relat_1(X26))&(r2_hidden(esk5_2(X26,X27),X27)|r2_hidden(k4_tarski(esk5_2(X26,X27),esk6_2(X26,X27)),X26)|X27=k1_relat_1(X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.20/0.41  fof(c_0_27, plain, ![X13, X14, X15, X16, X17]:((~r1_tarski(X13,X14)|(~r2_hidden(k4_tarski(X15,X16),X13)|r2_hidden(k4_tarski(X15,X16),X14))|~v1_relat_1(X13))&((r2_hidden(k4_tarski(esk2_2(X13,X17),esk3_2(X13,X17)),X13)|r1_tarski(X13,X17)|~v1_relat_1(X13))&(~r2_hidden(k4_tarski(esk2_2(X13,X17),esk3_2(X13,X17)),X17)|r1_tarski(X13,X17)|~v1_relat_1(X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).
% 0.20/0.41  cnf(c_0_28, negated_conjecture, (r2_hidden(k4_tarski(k1_funct_1(esk11_0,X1),k1_funct_1(k5_relat_1(esk11_0,esk12_0),X1)),esk13_0)|~r2_hidden(k1_funct_1(esk11_0,X1),k2_relat_1(esk11_0))|~r2_hidden(X1,k1_relat_1(esk11_0))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.41  cnf(c_0_29, negated_conjecture, (v1_funct_1(esk12_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_30, negated_conjecture, (v1_relat_1(esk12_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_31, plain, (X1=k1_funct_1(X2,esk7_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.41  cnf(c_0_32, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.41  cnf(c_0_33, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_34, plain, (r2_hidden(k4_tarski(esk2_2(X1,X2),esk3_2(X1,X2)),X1)|r1_tarski(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.41  cnf(c_0_35, negated_conjecture, (r2_hidden(k4_tarski(k1_funct_1(esk11_0,X1),k1_funct_1(esk12_0,k1_funct_1(esk11_0,X1))),esk13_0)|~r2_hidden(k1_funct_1(esk11_0,X1),k2_relat_1(esk11_0))|~r2_hidden(X1,k1_relat_1(esk11_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_19]), c_0_29]), c_0_21]), c_0_30]), c_0_22])])).
% 0.20/0.41  cnf(c_0_36, plain, (k1_funct_1(X1,esk7_3(X1,k2_relat_1(X1),X2))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_31])).
% 0.20/0.41  cnf(c_0_37, plain, (r2_hidden(esk7_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.41  cnf(c_0_38, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_32])).
% 0.20/0.41  cnf(c_0_39, negated_conjecture, (k1_relat_1(esk12_0)=esk10_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_40, plain, (r1_tarski(X1,X2)|~r2_hidden(k4_tarski(esk2_2(X1,X2),esk3_2(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.41  cnf(c_0_41, plain, (esk3_2(X1,X2)=k1_funct_1(X1,esk2_2(X1,X2))|r1_tarski(X1,X2)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.41  cnf(c_0_42, negated_conjecture, (r2_hidden(k4_tarski(X1,k1_funct_1(esk12_0,X1)),esk13_0)|~r2_hidden(esk7_3(esk11_0,k2_relat_1(esk11_0),X1),k1_relat_1(esk11_0))|~r2_hidden(X1,k2_relat_1(esk11_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_21]), c_0_22])])).
% 0.20/0.41  cnf(c_0_43, plain, (r2_hidden(esk7_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_37])).
% 0.20/0.41  cnf(c_0_44, plain, (r2_hidden(esk2_2(X1,X2),k1_relat_1(X1))|r1_tarski(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_38, c_0_34])).
% 0.20/0.41  cnf(c_0_45, negated_conjecture, (k1_relat_1(esk12_0)=k2_relat_1(esk11_0)), inference(rw,[status(thm)],[c_0_39, c_0_13])).
% 0.20/0.41  fof(c_0_46, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.41  cnf(c_0_47, plain, (r1_tarski(X1,X2)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(k4_tarski(esk2_2(X1,X2),k1_funct_1(X1,esk2_2(X1,X2))),X2)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.41  cnf(c_0_48, negated_conjecture, (r2_hidden(k4_tarski(X1,k1_funct_1(esk12_0,X1)),esk13_0)|~r2_hidden(X1,k2_relat_1(esk11_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_21]), c_0_22])])).
% 0.20/0.41  cnf(c_0_49, negated_conjecture, (r2_hidden(esk2_2(esk12_0,X1),k2_relat_1(esk11_0))|r1_tarski(esk12_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_30])])).
% 0.20/0.41  cnf(c_0_50, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.41  cnf(c_0_51, negated_conjecture, (r1_tarski(esk12_0,esk13_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_29]), c_0_30])]), c_0_49])).
% 0.20/0.41  cnf(c_0_52, plain, (r2_hidden(k4_tarski(X1,esk4_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.41  cnf(c_0_53, negated_conjecture, (r2_hidden(X1,esk13_0)|~r2_hidden(X1,esk12_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.41  cnf(c_0_54, plain, (r2_hidden(k4_tarski(X1,esk4_3(X2,k1_relat_1(X2),X1)),X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_52])).
% 0.20/0.41  cnf(c_0_55, negated_conjecture, (X1=k1_funct_1(esk13_0,X2)|~r2_hidden(k4_tarski(X2,X1),esk12_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_53]), c_0_17]), c_0_18])])).
% 0.20/0.41  fof(c_0_56, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.41  cnf(c_0_57, negated_conjecture, (r2_hidden(k4_tarski(X1,esk4_3(esk12_0,k2_relat_1(esk11_0),X1)),esk12_0)|~r2_hidden(X1,k2_relat_1(esk11_0))), inference(spm,[status(thm)],[c_0_54, c_0_45])).
% 0.20/0.41  cnf(c_0_58, negated_conjecture, (esk4_3(esk12_0,k2_relat_1(esk11_0),X1)=k1_funct_1(esk13_0,X1)|~r2_hidden(X1,k2_relat_1(esk11_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_54]), c_0_45]), c_0_45])).
% 0.20/0.41  cnf(c_0_59, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.20/0.41  cnf(c_0_60, negated_conjecture, (esk12_0!=esk13_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_61, negated_conjecture, (r2_hidden(k4_tarski(X1,k1_funct_1(esk13_0,X1)),esk12_0)|~r2_hidden(X1,k2_relat_1(esk11_0))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.20/0.41  cnf(c_0_62, negated_conjecture, (~r1_tarski(esk13_0,esk12_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_51]), c_0_60])).
% 0.20/0.41  cnf(c_0_63, negated_conjecture, (~r2_hidden(esk2_2(esk13_0,esk12_0),k2_relat_1(esk11_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_61]), c_0_17]), c_0_18])]), c_0_62])).
% 0.20/0.41  cnf(c_0_64, negated_conjecture, (r2_hidden(esk2_2(esk13_0,X1),k2_relat_1(esk11_0))|r1_tarski(esk13_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_16]), c_0_18])])).
% 0.20/0.41  cnf(c_0_65, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_62]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 66
% 0.20/0.41  # Proof object clause steps            : 49
% 0.20/0.41  # Proof object formula steps           : 17
% 0.20/0.41  # Proof object conjectures             : 33
% 0.20/0.41  # Proof object clause conjectures      : 30
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 22
% 0.20/0.41  # Proof object initial formulas used   : 8
% 0.20/0.41  # Proof object generating inferences   : 20
% 0.20/0.41  # Proof object simplifying inferences  : 45
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 8
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 34
% 0.20/0.41  # Removed in clause preprocessing      : 0
% 0.20/0.41  # Initial clauses in saturation        : 34
% 0.20/0.41  # Processed clauses                    : 289
% 0.20/0.41  # ...of these trivial                  : 1
% 0.20/0.41  # ...subsumed                          : 69
% 0.20/0.41  # ...remaining for further processing  : 219
% 0.20/0.41  # Other redundant clauses eliminated   : 22
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 5
% 0.20/0.41  # Backward-rewritten                   : 0
% 0.20/0.41  # Generated clauses                    : 726
% 0.20/0.41  # ...of the previous two non-trivial   : 657
% 0.20/0.41  # Contextual simplify-reflections      : 9
% 0.20/0.41  # Paramodulations                      : 689
% 0.20/0.41  # Factorizations                       : 16
% 0.20/0.41  # Equation resolutions                 : 22
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 175
% 0.20/0.41  #    Positive orientable unit clauses  : 18
% 0.20/0.41  #    Positive unorientable unit clauses: 0
% 0.20/0.41  #    Negative unit clauses             : 3
% 0.20/0.41  #    Non-unit-clauses                  : 154
% 0.20/0.41  # Current number of unprocessed clauses: 433
% 0.20/0.41  # ...number of literals in the above   : 2248
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 36
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 3430
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 1418
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 83
% 0.20/0.41  # Unit Clause-clause subsumption calls : 106
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 15
% 0.20/0.41  # BW rewrite match successes           : 0
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 22937
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.062 s
% 0.20/0.41  # System time              : 0.006 s
% 0.20/0.41  # Total time               : 0.068 s
% 0.20/0.41  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
