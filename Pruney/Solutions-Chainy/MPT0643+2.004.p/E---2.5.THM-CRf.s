%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:41 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 445 expanded)
%              Number of clauses        :   50 ( 162 expanded)
%              Number of leaves         :    7 ( 102 expanded)
%              Depth                    :   14
%              Number of atoms          :  333 (3267 expanded)
%              Number of equality atoms :   83 (1181 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t50_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( ( k1_relat_1(X2) = X1
              & k1_relat_1(X3) = X1
              & r1_tarski(k2_relat_1(X3),X1)
              & v2_funct_1(X2)
              & k5_relat_1(X3,X2) = X2 )
           => X3 = k6_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

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

fof(d8_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( X3 = k5_relat_1(X1,X2)
              <=> ! [X4,X5] :
                    ( r2_hidden(k4_tarski(X4,X5),X3)
                  <=> ? [X6] :
                        ( r2_hidden(k4_tarski(X4,X6),X1)
                        & r2_hidden(k4_tarski(X6,X5),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

fof(t34_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( X2 = k6_relat_1(X1)
      <=> ( k1_relat_1(X2) = X1
          & ! [X3] :
              ( r2_hidden(X3,X1)
             => k1_funct_1(X2,X3) = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

fof(d8_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( r2_hidden(X2,k1_relat_1(X1))
              & r2_hidden(X3,k1_relat_1(X1))
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( v1_relat_1(X3)
              & v1_funct_1(X3) )
           => ( ( k1_relat_1(X2) = X1
                & k1_relat_1(X3) = X1
                & r1_tarski(k2_relat_1(X3),X1)
                & v2_funct_1(X2)
                & k5_relat_1(X3,X2) = X2 )
             => X3 = k6_relat_1(X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t50_funct_1])).

fof(c_0_8,negated_conjecture,
    ( v1_relat_1(esk13_0)
    & v1_funct_1(esk13_0)
    & v1_relat_1(esk14_0)
    & v1_funct_1(esk14_0)
    & k1_relat_1(esk13_0) = esk12_0
    & k1_relat_1(esk14_0) = esk12_0
    & r1_tarski(k2_relat_1(esk14_0),esk12_0)
    & v2_funct_1(esk13_0)
    & k5_relat_1(esk14_0,esk13_0) = esk13_0
    & esk14_0 != k6_relat_1(esk12_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_9,negated_conjecture,
    ( k1_relat_1(esk14_0) = esk12_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_10,negated_conjecture,
    ( k1_relat_1(esk13_0) = esk12_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_11,plain,(
    ! [X45,X46,X47] :
      ( ( r2_hidden(X45,k1_relat_1(X47))
        | ~ r2_hidden(k4_tarski(X45,X46),X47)
        | ~ v1_relat_1(X47)
        | ~ v1_funct_1(X47) )
      & ( X46 = k1_funct_1(X47,X45)
        | ~ r2_hidden(k4_tarski(X45,X46),X47)
        | ~ v1_relat_1(X47)
        | ~ v1_funct_1(X47) )
      & ( ~ r2_hidden(X45,k1_relat_1(X47))
        | X46 != k1_funct_1(X47,X45)
        | r2_hidden(k4_tarski(X45,X46),X47)
        | ~ v1_relat_1(X47)
        | ~ v1_funct_1(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

fof(c_0_12,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_13,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk14_0),esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( k1_relat_1(esk13_0) = k1_relat_1(esk14_0) ),
    inference(rw,[status(thm)],[c_0_9,c_0_10])).

fof(c_0_15,plain,(
    ! [X26,X27,X28,X30,X31,X32,X34] :
      ( ( r2_hidden(esk6_3(X26,X27,X28),k1_relat_1(X26))
        | ~ r2_hidden(X28,X27)
        | X27 != k2_relat_1(X26)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( X28 = k1_funct_1(X26,esk6_3(X26,X27,X28))
        | ~ r2_hidden(X28,X27)
        | X27 != k2_relat_1(X26)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( ~ r2_hidden(X31,k1_relat_1(X26))
        | X30 != k1_funct_1(X26,X31)
        | r2_hidden(X30,X27)
        | X27 != k2_relat_1(X26)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( ~ r2_hidden(esk7_2(X26,X32),X32)
        | ~ r2_hidden(X34,k1_relat_1(X26))
        | esk7_2(X26,X32) != k1_funct_1(X26,X34)
        | X32 = k2_relat_1(X26)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( r2_hidden(esk8_2(X26,X32),k1_relat_1(X26))
        | r2_hidden(esk7_2(X26,X32),X32)
        | X32 = k2_relat_1(X26)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( esk7_2(X26,X32) = k1_funct_1(X26,esk8_2(X26,X32))
        | r2_hidden(esk7_2(X26,X32),X32)
        | X32 = k2_relat_1(X26)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_16,plain,(
    ! [X13,X14,X15,X16,X17,X19,X20,X21,X24] :
      ( ( r2_hidden(k4_tarski(X16,esk2_5(X13,X14,X15,X16,X17)),X13)
        | ~ r2_hidden(k4_tarski(X16,X17),X15)
        | X15 != k5_relat_1(X13,X14)
        | ~ v1_relat_1(X15)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(k4_tarski(esk2_5(X13,X14,X15,X16,X17),X17),X14)
        | ~ r2_hidden(k4_tarski(X16,X17),X15)
        | X15 != k5_relat_1(X13,X14)
        | ~ v1_relat_1(X15)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13) )
      & ( ~ r2_hidden(k4_tarski(X19,X21),X13)
        | ~ r2_hidden(k4_tarski(X21,X20),X14)
        | r2_hidden(k4_tarski(X19,X20),X15)
        | X15 != k5_relat_1(X13,X14)
        | ~ v1_relat_1(X15)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13) )
      & ( ~ r2_hidden(k4_tarski(esk3_3(X13,X14,X15),esk4_3(X13,X14,X15)),X15)
        | ~ r2_hidden(k4_tarski(esk3_3(X13,X14,X15),X24),X13)
        | ~ r2_hidden(k4_tarski(X24,esk4_3(X13,X14,X15)),X14)
        | X15 = k5_relat_1(X13,X14)
        | ~ v1_relat_1(X15)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(k4_tarski(esk3_3(X13,X14,X15),esk5_3(X13,X14,X15)),X13)
        | r2_hidden(k4_tarski(esk3_3(X13,X14,X15),esk4_3(X13,X14,X15)),X15)
        | X15 = k5_relat_1(X13,X14)
        | ~ v1_relat_1(X15)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(k4_tarski(esk5_3(X13,X14,X15),esk4_3(X13,X14,X15)),X14)
        | r2_hidden(k4_tarski(esk3_3(X13,X14,X15),esk4_3(X13,X14,X15)),X15)
        | X15 = k5_relat_1(X13,X14)
        | ~ v1_relat_1(X15)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).

cnf(c_0_17,plain,
    ( r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk14_0),k1_relat_1(esk14_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_10]),c_0_14])).

cnf(c_0_20,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(X1,esk2_5(X2,X3,X4,X1,X5)),X2)
    | ~ r2_hidden(k4_tarski(X1,X5),X4)
    | X4 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( r2_hidden(k4_tarski(X1,X4),X6)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X2,X4),X5)
    | X6 != k5_relat_1(X3,X5)
    | ~ v1_relat_1(X6)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_1(esk13_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(esk13_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(esk14_0))
    | ~ r2_hidden(X1,k2_relat_1(esk14_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_20])])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_1(esk14_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_29,negated_conjecture,
    ( v1_relat_1(esk14_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_30,plain,(
    ! [X41,X42,X43] :
      ( ( k1_relat_1(X42) = X41
        | X42 != k6_relat_1(X41)
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) )
      & ( ~ r2_hidden(X43,X41)
        | k1_funct_1(X42,X43) = X43
        | X42 != k6_relat_1(X41)
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) )
      & ( r2_hidden(esk11_2(X41,X42),X41)
        | k1_relat_1(X42) != X41
        | X42 = k6_relat_1(X41)
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) )
      & ( k1_funct_1(X42,esk11_2(X41,X42)) != esk11_2(X41,X42)
        | k1_relat_1(X42) != X41
        | X42 = k6_relat_1(X41)
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_funct_1])])])])])).

cnf(c_0_31,plain,
    ( r2_hidden(k4_tarski(X1,esk2_5(X2,X3,k5_relat_1(X2,X3),X1,X4)),X2)
    | ~ v1_relat_1(k5_relat_1(X2,X3))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X4),k5_relat_1(X2,X3)) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( k5_relat_1(esk14_0,esk13_0) = esk13_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_33,plain,
    ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(X3,X4))
    | ~ v1_relat_1(k5_relat_1(X3,X4))
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X5,X2),X4)
    | ~ r2_hidden(k4_tarski(X1,X5),X3) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(esk13_0,X1)),esk13_0)
    | ~ r2_hidden(X1,k1_relat_1(esk14_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_14]),c_0_24]),c_0_25])])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk14_0,X1),k1_relat_1(esk14_0))
    | ~ r2_hidden(X1,k1_relat_1(esk14_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])])).

cnf(c_0_36,plain,
    ( r2_hidden(esk11_2(X1,X2),X1)
    | X2 = k6_relat_1(X1)
    | k1_relat_1(X2) != X1
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( esk14_0 != k6_relat_1(esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_38,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk2_5(esk14_0,esk13_0,esk13_0,X1,X2)),esk14_0)
    | ~ r2_hidden(k4_tarski(X1,X2),esk13_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_25]),c_0_29])])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(esk13_0,X2)),k5_relat_1(X3,esk13_0))
    | ~ v1_relat_1(k5_relat_1(X3,esk13_0))
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,k1_relat_1(esk14_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_25])])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(k4_tarski(k1_funct_1(esk14_0,X1),k1_funct_1(esk14_0,k1_funct_1(esk14_0,X1))),esk14_0)
    | ~ r2_hidden(X1,k1_relat_1(esk14_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_35]),c_0_28]),c_0_29])])).

cnf(c_0_42,plain,
    ( k6_relat_1(k1_relat_1(X1)) = X1
    | r2_hidden(esk11_2(k1_relat_1(X1),X1),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( k6_relat_1(k1_relat_1(esk14_0)) != esk14_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_10]),c_0_14])).

cnf(c_0_44,negated_conjecture,
    ( esk2_5(esk14_0,esk13_0,esk13_0,X1,X2) = k1_funct_1(esk14_0,X1)
    | ~ r2_hidden(k4_tarski(X1,X2),esk13_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_28]),c_0_29])])).

fof(c_0_45,plain,(
    ! [X36,X37,X38] :
      ( ( ~ v2_funct_1(X36)
        | ~ r2_hidden(X37,k1_relat_1(X36))
        | ~ r2_hidden(X38,k1_relat_1(X36))
        | k1_funct_1(X36,X37) != k1_funct_1(X36,X38)
        | X37 = X38
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) )
      & ( r2_hidden(esk9_1(X36),k1_relat_1(X36))
        | v2_funct_1(X36)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) )
      & ( r2_hidden(esk10_1(X36),k1_relat_1(X36))
        | v2_funct_1(X36)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) )
      & ( k1_funct_1(X36,esk9_1(X36)) = k1_funct_1(X36,esk10_1(X36))
        | v2_funct_1(X36)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) )
      & ( esk9_1(X36) != esk10_1(X36)
        | v2_funct_1(X36)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(esk13_0,X2)),esk13_0)
    | ~ r2_hidden(k4_tarski(X1,X2),esk14_0)
    | ~ r2_hidden(X2,k1_relat_1(esk14_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_32]),c_0_25]),c_0_29])])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(k4_tarski(k1_funct_1(esk14_0,esk11_2(k1_relat_1(esk14_0),esk14_0)),k1_funct_1(esk14_0,k1_funct_1(esk14_0,esk11_2(k1_relat_1(esk14_0),esk14_0)))),esk14_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_28]),c_0_29])]),c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(esk14_0,X1)),esk14_0)
    | ~ r2_hidden(k4_tarski(X1,X2),esk13_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_44])).

cnf(c_0_50,plain,
    ( X2 = X3
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( v2_funct_1(esk13_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_52,negated_conjecture,
    ( k1_funct_1(esk13_0,X1) = k1_funct_1(esk13_0,X2)
    | ~ r2_hidden(k4_tarski(X2,X1),esk14_0)
    | ~ r2_hidden(X1,k1_relat_1(esk14_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_46]),c_0_24]),c_0_25])])).

cnf(c_0_53,plain,
    ( k6_relat_1(k1_relat_1(X1)) = X1
    | r2_hidden(k4_tarski(esk11_2(k1_relat_1(X1),X1),k1_funct_1(X1,esk11_2(k1_relat_1(X1),X1))),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_42])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk14_0,esk11_2(k1_relat_1(esk14_0),esk14_0)),k1_relat_1(esk14_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_28]),c_0_29])])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(esk14_0,X1)),esk14_0)
    | ~ r2_hidden(X1,k1_relat_1(esk14_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_34])).

cnf(c_0_56,negated_conjecture,
    ( X1 = X2
    | k1_funct_1(esk13_0,X1) != k1_funct_1(esk13_0,X2)
    | ~ r2_hidden(X2,k1_relat_1(esk14_0))
    | ~ r2_hidden(X1,k1_relat_1(esk14_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_14]),c_0_51]),c_0_24]),c_0_25])])).

cnf(c_0_57,negated_conjecture,
    ( k1_funct_1(esk13_0,k1_funct_1(esk14_0,esk11_2(k1_relat_1(esk14_0),esk14_0))) = k1_funct_1(esk13_0,esk11_2(k1_relat_1(esk14_0),esk14_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_28]),c_0_29])]),c_0_43])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(k4_tarski(esk11_2(k1_relat_1(esk14_0),esk14_0),k1_funct_1(esk14_0,esk11_2(k1_relat_1(esk14_0),esk14_0))),esk14_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_42]),c_0_28]),c_0_29])]),c_0_43])).

cnf(c_0_59,plain,
    ( X1 = k6_relat_1(X2)
    | k1_funct_1(X1,esk11_2(X2,X1)) != esk11_2(X2,X1)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_60,negated_conjecture,
    ( k1_funct_1(esk14_0,esk11_2(k1_relat_1(esk14_0),esk14_0)) = X1
    | k1_funct_1(esk13_0,esk11_2(k1_relat_1(esk14_0),esk14_0)) != k1_funct_1(esk13_0,X1)
    | ~ r2_hidden(X1,k1_relat_1(esk14_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_54])])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk11_2(k1_relat_1(esk14_0),esk14_0),k1_relat_1(esk14_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_58]),c_0_28]),c_0_29])])).

cnf(c_0_62,plain,
    ( k6_relat_1(k1_relat_1(X1)) = X1
    | k1_funct_1(X1,esk11_2(k1_relat_1(X1),X1)) != esk11_2(k1_relat_1(X1),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( k1_funct_1(esk14_0,esk11_2(k1_relat_1(esk14_0),esk14_0)) = esk11_2(k1_relat_1(esk14_0),esk14_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_60]),c_0_61])])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_28]),c_0_29])]),c_0_43]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:39:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.49  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S5PRR_S0Y
% 0.21/0.49  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.21/0.49  #
% 0.21/0.49  # Preprocessing time       : 0.030 s
% 0.21/0.49  # Presaturation interreduction done
% 0.21/0.49  
% 0.21/0.49  # Proof found!
% 0.21/0.49  # SZS status Theorem
% 0.21/0.49  # SZS output start CNFRefutation
% 0.21/0.49  fof(t50_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(((((k1_relat_1(X2)=X1&k1_relat_1(X3)=X1)&r1_tarski(k2_relat_1(X3),X1))&v2_funct_1(X2))&k5_relat_1(X3,X2)=X2)=>X3=k6_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_funct_1)).
% 0.21/0.49  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 0.21/0.49  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.21/0.49  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 0.21/0.49  fof(d8_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(X3=k5_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>?[X6]:(r2_hidden(k4_tarski(X4,X6),X1)&r2_hidden(k4_tarski(X6,X5),X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_relat_1)).
% 0.21/0.49  fof(t34_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(X2=k6_relat_1(X1)<=>(k1_relat_1(X2)=X1&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_funct_1)).
% 0.21/0.49  fof(d8_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)<=>![X2, X3]:(((r2_hidden(X2,k1_relat_1(X1))&r2_hidden(X3,k1_relat_1(X1)))&k1_funct_1(X1,X2)=k1_funct_1(X1,X3))=>X2=X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_funct_1)).
% 0.21/0.49  fof(c_0_7, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(((((k1_relat_1(X2)=X1&k1_relat_1(X3)=X1)&r1_tarski(k2_relat_1(X3),X1))&v2_funct_1(X2))&k5_relat_1(X3,X2)=X2)=>X3=k6_relat_1(X1))))), inference(assume_negation,[status(cth)],[t50_funct_1])).
% 0.21/0.49  fof(c_0_8, negated_conjecture, ((v1_relat_1(esk13_0)&v1_funct_1(esk13_0))&((v1_relat_1(esk14_0)&v1_funct_1(esk14_0))&(((((k1_relat_1(esk13_0)=esk12_0&k1_relat_1(esk14_0)=esk12_0)&r1_tarski(k2_relat_1(esk14_0),esk12_0))&v2_funct_1(esk13_0))&k5_relat_1(esk14_0,esk13_0)=esk13_0)&esk14_0!=k6_relat_1(esk12_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.21/0.49  cnf(c_0_9, negated_conjecture, (k1_relat_1(esk14_0)=esk12_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.49  cnf(c_0_10, negated_conjecture, (k1_relat_1(esk13_0)=esk12_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.49  fof(c_0_11, plain, ![X45, X46, X47]:(((r2_hidden(X45,k1_relat_1(X47))|~r2_hidden(k4_tarski(X45,X46),X47)|(~v1_relat_1(X47)|~v1_funct_1(X47)))&(X46=k1_funct_1(X47,X45)|~r2_hidden(k4_tarski(X45,X46),X47)|(~v1_relat_1(X47)|~v1_funct_1(X47))))&(~r2_hidden(X45,k1_relat_1(X47))|X46!=k1_funct_1(X47,X45)|r2_hidden(k4_tarski(X45,X46),X47)|(~v1_relat_1(X47)|~v1_funct_1(X47)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.21/0.49  fof(c_0_12, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.21/0.49  cnf(c_0_13, negated_conjecture, (r1_tarski(k2_relat_1(esk14_0),esk12_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.49  cnf(c_0_14, negated_conjecture, (k1_relat_1(esk13_0)=k1_relat_1(esk14_0)), inference(rw,[status(thm)],[c_0_9, c_0_10])).
% 0.21/0.49  fof(c_0_15, plain, ![X26, X27, X28, X30, X31, X32, X34]:((((r2_hidden(esk6_3(X26,X27,X28),k1_relat_1(X26))|~r2_hidden(X28,X27)|X27!=k2_relat_1(X26)|(~v1_relat_1(X26)|~v1_funct_1(X26)))&(X28=k1_funct_1(X26,esk6_3(X26,X27,X28))|~r2_hidden(X28,X27)|X27!=k2_relat_1(X26)|(~v1_relat_1(X26)|~v1_funct_1(X26))))&(~r2_hidden(X31,k1_relat_1(X26))|X30!=k1_funct_1(X26,X31)|r2_hidden(X30,X27)|X27!=k2_relat_1(X26)|(~v1_relat_1(X26)|~v1_funct_1(X26))))&((~r2_hidden(esk7_2(X26,X32),X32)|(~r2_hidden(X34,k1_relat_1(X26))|esk7_2(X26,X32)!=k1_funct_1(X26,X34))|X32=k2_relat_1(X26)|(~v1_relat_1(X26)|~v1_funct_1(X26)))&((r2_hidden(esk8_2(X26,X32),k1_relat_1(X26))|r2_hidden(esk7_2(X26,X32),X32)|X32=k2_relat_1(X26)|(~v1_relat_1(X26)|~v1_funct_1(X26)))&(esk7_2(X26,X32)=k1_funct_1(X26,esk8_2(X26,X32))|r2_hidden(esk7_2(X26,X32),X32)|X32=k2_relat_1(X26)|(~v1_relat_1(X26)|~v1_funct_1(X26)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.21/0.49  fof(c_0_16, plain, ![X13, X14, X15, X16, X17, X19, X20, X21, X24]:((((r2_hidden(k4_tarski(X16,esk2_5(X13,X14,X15,X16,X17)),X13)|~r2_hidden(k4_tarski(X16,X17),X15)|X15!=k5_relat_1(X13,X14)|~v1_relat_1(X15)|~v1_relat_1(X14)|~v1_relat_1(X13))&(r2_hidden(k4_tarski(esk2_5(X13,X14,X15,X16,X17),X17),X14)|~r2_hidden(k4_tarski(X16,X17),X15)|X15!=k5_relat_1(X13,X14)|~v1_relat_1(X15)|~v1_relat_1(X14)|~v1_relat_1(X13)))&(~r2_hidden(k4_tarski(X19,X21),X13)|~r2_hidden(k4_tarski(X21,X20),X14)|r2_hidden(k4_tarski(X19,X20),X15)|X15!=k5_relat_1(X13,X14)|~v1_relat_1(X15)|~v1_relat_1(X14)|~v1_relat_1(X13)))&((~r2_hidden(k4_tarski(esk3_3(X13,X14,X15),esk4_3(X13,X14,X15)),X15)|(~r2_hidden(k4_tarski(esk3_3(X13,X14,X15),X24),X13)|~r2_hidden(k4_tarski(X24,esk4_3(X13,X14,X15)),X14))|X15=k5_relat_1(X13,X14)|~v1_relat_1(X15)|~v1_relat_1(X14)|~v1_relat_1(X13))&((r2_hidden(k4_tarski(esk3_3(X13,X14,X15),esk5_3(X13,X14,X15)),X13)|r2_hidden(k4_tarski(esk3_3(X13,X14,X15),esk4_3(X13,X14,X15)),X15)|X15=k5_relat_1(X13,X14)|~v1_relat_1(X15)|~v1_relat_1(X14)|~v1_relat_1(X13))&(r2_hidden(k4_tarski(esk5_3(X13,X14,X15),esk4_3(X13,X14,X15)),X14)|r2_hidden(k4_tarski(esk3_3(X13,X14,X15),esk4_3(X13,X14,X15)),X15)|X15=k5_relat_1(X13,X14)|~v1_relat_1(X15)|~v1_relat_1(X14)|~v1_relat_1(X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).
% 0.21/0.49  cnf(c_0_17, plain, (r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.49  cnf(c_0_18, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.49  cnf(c_0_19, negated_conjecture, (r1_tarski(k2_relat_1(esk14_0),k1_relat_1(esk14_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_10]), c_0_14])).
% 0.21/0.49  cnf(c_0_20, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.49  cnf(c_0_21, plain, (r2_hidden(k4_tarski(X1,esk2_5(X2,X3,X4,X1,X5)),X2)|~r2_hidden(k4_tarski(X1,X5),X4)|X4!=k5_relat_1(X2,X3)|~v1_relat_1(X4)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.49  cnf(c_0_22, plain, (r2_hidden(k4_tarski(X1,X4),X6)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(k4_tarski(X2,X4),X5)|X6!=k5_relat_1(X3,X5)|~v1_relat_1(X6)|~v1_relat_1(X5)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.49  cnf(c_0_23, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_17])).
% 0.21/0.49  cnf(c_0_24, negated_conjecture, (v1_funct_1(esk13_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.49  cnf(c_0_25, negated_conjecture, (v1_relat_1(esk13_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.49  cnf(c_0_26, negated_conjecture, (r2_hidden(X1,k1_relat_1(esk14_0))|~r2_hidden(X1,k2_relat_1(esk14_0))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.21/0.49  cnf(c_0_27, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_20])])).
% 0.21/0.49  cnf(c_0_28, negated_conjecture, (v1_funct_1(esk14_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.49  cnf(c_0_29, negated_conjecture, (v1_relat_1(esk14_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.49  fof(c_0_30, plain, ![X41, X42, X43]:(((k1_relat_1(X42)=X41|X42!=k6_relat_1(X41)|(~v1_relat_1(X42)|~v1_funct_1(X42)))&(~r2_hidden(X43,X41)|k1_funct_1(X42,X43)=X43|X42!=k6_relat_1(X41)|(~v1_relat_1(X42)|~v1_funct_1(X42))))&((r2_hidden(esk11_2(X41,X42),X41)|k1_relat_1(X42)!=X41|X42=k6_relat_1(X41)|(~v1_relat_1(X42)|~v1_funct_1(X42)))&(k1_funct_1(X42,esk11_2(X41,X42))!=esk11_2(X41,X42)|k1_relat_1(X42)!=X41|X42=k6_relat_1(X41)|(~v1_relat_1(X42)|~v1_funct_1(X42))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_funct_1])])])])])).
% 0.21/0.49  cnf(c_0_31, plain, (r2_hidden(k4_tarski(X1,esk2_5(X2,X3,k5_relat_1(X2,X3),X1,X4)),X2)|~v1_relat_1(k5_relat_1(X2,X3))|~v1_relat_1(X3)|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X4),k5_relat_1(X2,X3))), inference(er,[status(thm)],[c_0_21])).
% 0.21/0.49  cnf(c_0_32, negated_conjecture, (k5_relat_1(esk14_0,esk13_0)=esk13_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.49  cnf(c_0_33, plain, (r2_hidden(k4_tarski(X1,X2),k5_relat_1(X3,X4))|~v1_relat_1(k5_relat_1(X3,X4))|~v1_relat_1(X4)|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X5,X2),X4)|~r2_hidden(k4_tarski(X1,X5),X3)), inference(er,[status(thm)],[c_0_22])).
% 0.21/0.49  cnf(c_0_34, negated_conjecture, (r2_hidden(k4_tarski(X1,k1_funct_1(esk13_0,X1)),esk13_0)|~r2_hidden(X1,k1_relat_1(esk14_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_14]), c_0_24]), c_0_25])])).
% 0.21/0.49  cnf(c_0_35, negated_conjecture, (r2_hidden(k1_funct_1(esk14_0,X1),k1_relat_1(esk14_0))|~r2_hidden(X1,k1_relat_1(esk14_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])])).
% 0.21/0.49  cnf(c_0_36, plain, (r2_hidden(esk11_2(X1,X2),X1)|X2=k6_relat_1(X1)|k1_relat_1(X2)!=X1|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.49  cnf(c_0_37, negated_conjecture, (esk14_0!=k6_relat_1(esk12_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.49  cnf(c_0_38, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.49  cnf(c_0_39, negated_conjecture, (r2_hidden(k4_tarski(X1,esk2_5(esk14_0,esk13_0,esk13_0,X1,X2)),esk14_0)|~r2_hidden(k4_tarski(X1,X2),esk13_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_25]), c_0_29])])).
% 0.21/0.49  cnf(c_0_40, negated_conjecture, (r2_hidden(k4_tarski(X1,k1_funct_1(esk13_0,X2)),k5_relat_1(X3,esk13_0))|~v1_relat_1(k5_relat_1(X3,esk13_0))|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X2,k1_relat_1(esk14_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_25])])).
% 0.21/0.49  cnf(c_0_41, negated_conjecture, (r2_hidden(k4_tarski(k1_funct_1(esk14_0,X1),k1_funct_1(esk14_0,k1_funct_1(esk14_0,X1))),esk14_0)|~r2_hidden(X1,k1_relat_1(esk14_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_35]), c_0_28]), c_0_29])])).
% 0.21/0.49  cnf(c_0_42, plain, (k6_relat_1(k1_relat_1(X1))=X1|r2_hidden(esk11_2(k1_relat_1(X1),X1),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_36])).
% 0.21/0.49  cnf(c_0_43, negated_conjecture, (k6_relat_1(k1_relat_1(esk14_0))!=esk14_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_10]), c_0_14])).
% 0.21/0.49  cnf(c_0_44, negated_conjecture, (esk2_5(esk14_0,esk13_0,esk13_0,X1,X2)=k1_funct_1(esk14_0,X1)|~r2_hidden(k4_tarski(X1,X2),esk13_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_28]), c_0_29])])).
% 0.21/0.49  fof(c_0_45, plain, ![X36, X37, X38]:((~v2_funct_1(X36)|(~r2_hidden(X37,k1_relat_1(X36))|~r2_hidden(X38,k1_relat_1(X36))|k1_funct_1(X36,X37)!=k1_funct_1(X36,X38)|X37=X38)|(~v1_relat_1(X36)|~v1_funct_1(X36)))&((((r2_hidden(esk9_1(X36),k1_relat_1(X36))|v2_funct_1(X36)|(~v1_relat_1(X36)|~v1_funct_1(X36)))&(r2_hidden(esk10_1(X36),k1_relat_1(X36))|v2_funct_1(X36)|(~v1_relat_1(X36)|~v1_funct_1(X36))))&(k1_funct_1(X36,esk9_1(X36))=k1_funct_1(X36,esk10_1(X36))|v2_funct_1(X36)|(~v1_relat_1(X36)|~v1_funct_1(X36))))&(esk9_1(X36)!=esk10_1(X36)|v2_funct_1(X36)|(~v1_relat_1(X36)|~v1_funct_1(X36))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).
% 0.21/0.49  cnf(c_0_46, negated_conjecture, (r2_hidden(k4_tarski(X1,k1_funct_1(esk13_0,X2)),esk13_0)|~r2_hidden(k4_tarski(X1,X2),esk14_0)|~r2_hidden(X2,k1_relat_1(esk14_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_32]), c_0_25]), c_0_29])])).
% 0.21/0.49  cnf(c_0_47, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.49  cnf(c_0_48, negated_conjecture, (r2_hidden(k4_tarski(k1_funct_1(esk14_0,esk11_2(k1_relat_1(esk14_0),esk14_0)),k1_funct_1(esk14_0,k1_funct_1(esk14_0,esk11_2(k1_relat_1(esk14_0),esk14_0)))),esk14_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_28]), c_0_29])]), c_0_43])).
% 0.21/0.49  cnf(c_0_49, negated_conjecture, (r2_hidden(k4_tarski(X1,k1_funct_1(esk14_0,X1)),esk14_0)|~r2_hidden(k4_tarski(X1,X2),esk13_0)), inference(spm,[status(thm)],[c_0_39, c_0_44])).
% 0.21/0.49  cnf(c_0_50, plain, (X2=X3|~v2_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~r2_hidden(X3,k1_relat_1(X1))|k1_funct_1(X1,X2)!=k1_funct_1(X1,X3)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.21/0.49  cnf(c_0_51, negated_conjecture, (v2_funct_1(esk13_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.49  cnf(c_0_52, negated_conjecture, (k1_funct_1(esk13_0,X1)=k1_funct_1(esk13_0,X2)|~r2_hidden(k4_tarski(X2,X1),esk14_0)|~r2_hidden(X1,k1_relat_1(esk14_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_46]), c_0_24]), c_0_25])])).
% 0.21/0.49  cnf(c_0_53, plain, (k6_relat_1(k1_relat_1(X1))=X1|r2_hidden(k4_tarski(esk11_2(k1_relat_1(X1),X1),k1_funct_1(X1,esk11_2(k1_relat_1(X1),X1))),X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_23, c_0_42])).
% 0.21/0.49  cnf(c_0_54, negated_conjecture, (r2_hidden(k1_funct_1(esk14_0,esk11_2(k1_relat_1(esk14_0),esk14_0)),k1_relat_1(esk14_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_28]), c_0_29])])).
% 0.21/0.49  cnf(c_0_55, negated_conjecture, (r2_hidden(k4_tarski(X1,k1_funct_1(esk14_0,X1)),esk14_0)|~r2_hidden(X1,k1_relat_1(esk14_0))), inference(spm,[status(thm)],[c_0_49, c_0_34])).
% 0.21/0.49  cnf(c_0_56, negated_conjecture, (X1=X2|k1_funct_1(esk13_0,X1)!=k1_funct_1(esk13_0,X2)|~r2_hidden(X2,k1_relat_1(esk14_0))|~r2_hidden(X1,k1_relat_1(esk14_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_14]), c_0_51]), c_0_24]), c_0_25])])).
% 0.21/0.49  cnf(c_0_57, negated_conjecture, (k1_funct_1(esk13_0,k1_funct_1(esk14_0,esk11_2(k1_relat_1(esk14_0),esk14_0)))=k1_funct_1(esk13_0,esk11_2(k1_relat_1(esk14_0),esk14_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), c_0_28]), c_0_29])]), c_0_43])).
% 0.21/0.49  cnf(c_0_58, negated_conjecture, (r2_hidden(k4_tarski(esk11_2(k1_relat_1(esk14_0),esk14_0),k1_funct_1(esk14_0,esk11_2(k1_relat_1(esk14_0),esk14_0))),esk14_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_42]), c_0_28]), c_0_29])]), c_0_43])).
% 0.21/0.49  cnf(c_0_59, plain, (X1=k6_relat_1(X2)|k1_funct_1(X1,esk11_2(X2,X1))!=esk11_2(X2,X1)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.49  cnf(c_0_60, negated_conjecture, (k1_funct_1(esk14_0,esk11_2(k1_relat_1(esk14_0),esk14_0))=X1|k1_funct_1(esk13_0,esk11_2(k1_relat_1(esk14_0),esk14_0))!=k1_funct_1(esk13_0,X1)|~r2_hidden(X1,k1_relat_1(esk14_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_54])])).
% 0.21/0.49  cnf(c_0_61, negated_conjecture, (r2_hidden(esk11_2(k1_relat_1(esk14_0),esk14_0),k1_relat_1(esk14_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_58]), c_0_28]), c_0_29])])).
% 0.21/0.49  cnf(c_0_62, plain, (k6_relat_1(k1_relat_1(X1))=X1|k1_funct_1(X1,esk11_2(k1_relat_1(X1),X1))!=esk11_2(k1_relat_1(X1),X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_59])).
% 0.21/0.49  cnf(c_0_63, negated_conjecture, (k1_funct_1(esk14_0,esk11_2(k1_relat_1(esk14_0),esk14_0))=esk11_2(k1_relat_1(esk14_0),esk14_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_60]), c_0_61])])).
% 0.21/0.49  cnf(c_0_64, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_28]), c_0_29])]), c_0_43]), ['proof']).
% 0.21/0.49  # SZS output end CNFRefutation
% 0.21/0.49  # Proof object total steps             : 65
% 0.21/0.49  # Proof object clause steps            : 50
% 0.21/0.49  # Proof object formula steps           : 15
% 0.21/0.49  # Proof object conjectures             : 36
% 0.21/0.49  # Proof object clause conjectures      : 33
% 0.21/0.49  # Proof object formula conjectures     : 3
% 0.21/0.49  # Proof object initial clauses used    : 20
% 0.21/0.49  # Proof object initial formulas used   : 7
% 0.21/0.49  # Proof object generating inferences   : 21
% 0.21/0.49  # Proof object simplifying inferences  : 66
% 0.21/0.49  # Training examples: 0 positive, 0 negative
% 0.21/0.49  # Parsed axioms                        : 7
% 0.21/0.49  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.49  # Initial clauses                      : 37
% 0.21/0.49  # Removed in clause preprocessing      : 0
% 0.21/0.49  # Initial clauses in saturation        : 37
% 0.21/0.49  # Processed clauses                    : 616
% 0.21/0.49  # ...of these trivial                  : 3
% 0.21/0.49  # ...subsumed                          : 164
% 0.21/0.49  # ...remaining for further processing  : 449
% 0.21/0.49  # Other redundant clauses eliminated   : 99
% 0.21/0.49  # Clauses deleted for lack of memory   : 0
% 0.21/0.49  # Backward-subsumed                    : 13
% 0.21/0.49  # Backward-rewritten                   : 167
% 0.21/0.49  # Generated clauses                    : 2565
% 0.21/0.49  # ...of the previous two non-trivial   : 2382
% 0.21/0.49  # Contextual simplify-reflections      : 11
% 0.21/0.49  # Paramodulations                      : 2438
% 0.21/0.49  # Factorizations                       : 6
% 0.21/0.49  # Equation resolutions                 : 122
% 0.21/0.49  # Propositional unsat checks           : 0
% 0.21/0.49  #    Propositional check models        : 0
% 0.21/0.49  #    Propositional check unsatisfiable : 0
% 0.21/0.49  #    Propositional clauses             : 0
% 0.21/0.49  #    Propositional clauses after purity: 0
% 0.21/0.49  #    Propositional unsat core size     : 0
% 0.21/0.49  #    Propositional preprocessing time  : 0.000
% 0.21/0.49  #    Propositional encoding time       : 0.000
% 0.21/0.49  #    Propositional solver time         : 0.000
% 0.21/0.49  #    Success case prop preproc time    : 0.000
% 0.21/0.49  #    Success case prop encoding time   : 0.000
% 0.21/0.49  #    Success case prop solver time     : 0.000
% 0.21/0.49  # Current number of processed clauses  : 221
% 0.21/0.49  #    Positive orientable unit clauses  : 13
% 0.21/0.49  #    Positive unorientable unit clauses: 0
% 0.21/0.49  #    Negative unit clauses             : 1
% 0.21/0.49  #    Non-unit-clauses                  : 207
% 0.21/0.49  # Current number of unprocessed clauses: 1694
% 0.21/0.49  # ...number of literals in the above   : 10503
% 0.21/0.49  # Current number of archived formulas  : 0
% 0.21/0.49  # Current number of archived clauses   : 217
% 0.21/0.49  # Clause-clause subsumption calls (NU) : 20724
% 0.21/0.49  # Rec. Clause-clause subsumption calls : 2064
% 0.21/0.49  # Non-unit clause-clause subsumptions  : 188
% 0.21/0.49  # Unit Clause-clause subsumption calls : 41
% 0.21/0.49  # Rewrite failures with RHS unbound    : 0
% 0.21/0.49  # BW rewrite match attempts            : 71
% 0.21/0.49  # BW rewrite match successes           : 2
% 0.21/0.49  # Condensation attempts                : 0
% 0.21/0.49  # Condensation successes               : 0
% 0.21/0.49  # Termbank termtop insertions          : 96002
% 0.21/0.49  
% 0.21/0.49  # -------------------------------------------------
% 0.21/0.49  # User time                : 0.143 s
% 0.21/0.49  # System time              : 0.007 s
% 0.21/0.49  # Total time               : 0.150 s
% 0.21/0.49  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
