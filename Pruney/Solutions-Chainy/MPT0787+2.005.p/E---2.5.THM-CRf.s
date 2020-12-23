%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:55 EST 2020

% Result     : Theorem 0.53s
% Output     : CNFRefutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  118 (2098 expanded)
%              Number of clauses        :   91 ( 843 expanded)
%              Number of leaves         :   13 ( 493 expanded)
%              Depth                    :   23
%              Number of atoms          :  512 (12863 expanded)
%              Number of equality atoms :   88 (1442 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t37_wellord1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( v2_wellord1(X3)
          & r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X2,k3_relat_1(X3)) )
       => ( r2_hidden(k4_tarski(X1,X2),X3)
        <=> r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_wellord1)).

fof(l4_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v6_relat_2(X1)
      <=> ! [X2,X3] :
            ~ ( r2_hidden(X2,k3_relat_1(X1))
              & r2_hidden(X3,k3_relat_1(X1))
              & X2 != X3
              & ~ r2_hidden(k4_tarski(X2,X3),X1)
              & ~ r2_hidden(k4_tarski(X3,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l4_wellord1)).

fof(d4_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
      <=> ( v1_relat_2(X1)
          & v8_relat_2(X1)
          & v4_relat_2(X1)
          & v6_relat_2(X1)
          & v1_wellord1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord1)).

fof(d1_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k1_wellord1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ( X4 != X2
                & r2_hidden(k4_tarski(X4,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

fof(l2_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v8_relat_2(X1)
      <=> ! [X2,X3,X4] :
            ( ( r2_hidden(k4_tarski(X2,X3),X1)
              & r2_hidden(k4_tarski(X3,X4),X1) )
           => r2_hidden(k4_tarski(X2,X4),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l2_wellord1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(s1_xboole_0__e7_18__wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => ? [X3] :
        ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,k3_relat_1(X1))
            & ~ r2_hidden(k4_tarski(X4,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s1_xboole_0__e7_18__wellord1)).

fof(l3_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_2(X1)
      <=> ! [X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X1)
              & r2_hidden(k4_tarski(X3,X2),X1) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_wellord1)).

fof(t30_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X2,k3_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t9_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_wellord1(X2,X1)
       => ! [X3] :
            ~ ( r1_tarski(X3,X1)
              & X3 != k1_xboole_0
              & ! [X4] :
                  ~ ( r2_hidden(X4,X3)
                    & ! [X5] :
                        ( r2_hidden(X5,X3)
                       => r2_hidden(k4_tarski(X4,X5),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_wellord1)).

fof(t8_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( r2_wellord1(X1,k3_relat_1(X1))
      <=> v2_wellord1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( ( v2_wellord1(X3)
            & r2_hidden(X1,k3_relat_1(X3))
            & r2_hidden(X2,k3_relat_1(X3)) )
         => ( r2_hidden(k4_tarski(X1,X2),X3)
          <=> r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t37_wellord1])).

fof(c_0_14,plain,(
    ! [X40,X41,X42] :
      ( ( ~ v6_relat_2(X40)
        | ~ r2_hidden(X41,k3_relat_1(X40))
        | ~ r2_hidden(X42,k3_relat_1(X40))
        | X41 = X42
        | r2_hidden(k4_tarski(X41,X42),X40)
        | r2_hidden(k4_tarski(X42,X41),X40)
        | ~ v1_relat_1(X40) )
      & ( r2_hidden(esk8_1(X40),k3_relat_1(X40))
        | v6_relat_2(X40)
        | ~ v1_relat_1(X40) )
      & ( r2_hidden(esk9_1(X40),k3_relat_1(X40))
        | v6_relat_2(X40)
        | ~ v1_relat_1(X40) )
      & ( esk8_1(X40) != esk9_1(X40)
        | v6_relat_2(X40)
        | ~ v1_relat_1(X40) )
      & ( ~ r2_hidden(k4_tarski(esk8_1(X40),esk9_1(X40)),X40)
        | v6_relat_2(X40)
        | ~ v1_relat_1(X40) )
      & ( ~ r2_hidden(k4_tarski(esk9_1(X40),esk8_1(X40)),X40)
        | v6_relat_2(X40)
        | ~ v1_relat_1(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l4_wellord1])])])])])])).

fof(c_0_15,negated_conjecture,
    ( v1_relat_1(esk14_0)
    & v2_wellord1(esk14_0)
    & r2_hidden(esk12_0,k3_relat_1(esk14_0))
    & r2_hidden(esk13_0,k3_relat_1(esk14_0))
    & ( ~ r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)
      | ~ r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0)) )
    & ( r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)
      | r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_16,plain,
    ( X2 = X3
    | r2_hidden(k4_tarski(X2,X3),X1)
    | r2_hidden(k4_tarski(X3,X2),X1)
    | ~ v6_relat_2(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ r2_hidden(X3,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk13_0,k3_relat_1(esk14_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( v1_relat_1(esk14_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X27] :
      ( ( v1_relat_2(X27)
        | ~ v2_wellord1(X27)
        | ~ v1_relat_1(X27) )
      & ( v8_relat_2(X27)
        | ~ v2_wellord1(X27)
        | ~ v1_relat_1(X27) )
      & ( v4_relat_2(X27)
        | ~ v2_wellord1(X27)
        | ~ v1_relat_1(X27) )
      & ( v6_relat_2(X27)
        | ~ v2_wellord1(X27)
        | ~ v1_relat_1(X27) )
      & ( v1_wellord1(X27)
        | ~ v2_wellord1(X27)
        | ~ v1_relat_1(X27) )
      & ( ~ v1_relat_2(X27)
        | ~ v8_relat_2(X27)
        | ~ v4_relat_2(X27)
        | ~ v6_relat_2(X27)
        | ~ v1_wellord1(X27)
        | v2_wellord1(X27)
        | ~ v1_relat_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).

fof(c_0_20,plain,(
    ! [X19,X20,X21,X22,X23,X24,X25] :
      ( ( X22 != X20
        | ~ r2_hidden(X22,X21)
        | X21 != k1_wellord1(X19,X20)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(k4_tarski(X22,X20),X19)
        | ~ r2_hidden(X22,X21)
        | X21 != k1_wellord1(X19,X20)
        | ~ v1_relat_1(X19) )
      & ( X23 = X20
        | ~ r2_hidden(k4_tarski(X23,X20),X19)
        | r2_hidden(X23,X21)
        | X21 != k1_wellord1(X19,X20)
        | ~ v1_relat_1(X19) )
      & ( ~ r2_hidden(esk2_3(X19,X24,X25),X25)
        | esk2_3(X19,X24,X25) = X24
        | ~ r2_hidden(k4_tarski(esk2_3(X19,X24,X25),X24),X19)
        | X25 = k1_wellord1(X19,X24)
        | ~ v1_relat_1(X19) )
      & ( esk2_3(X19,X24,X25) != X24
        | r2_hidden(esk2_3(X19,X24,X25),X25)
        | X25 = k1_wellord1(X19,X24)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(k4_tarski(esk2_3(X19,X24,X25),X24),X19)
        | r2_hidden(esk2_3(X19,X24,X25),X25)
        | X25 = k1_wellord1(X19,X24)
        | ~ v1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).

cnf(c_0_21,negated_conjecture,
    ( X1 = esk13_0
    | r2_hidden(k4_tarski(esk13_0,X1),esk14_0)
    | r2_hidden(k4_tarski(X1,esk13_0),esk14_0)
    | ~ v6_relat_2(esk14_0)
    | ~ r2_hidden(X1,k3_relat_1(esk14_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])])).

cnf(c_0_22,plain,
    ( v6_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( v2_wellord1(esk14_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( X1 = X2
    | r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_wellord1(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( X1 = esk13_0
    | r2_hidden(k4_tarski(X1,esk13_0),esk14_0)
    | r2_hidden(k4_tarski(esk13_0,X1),esk14_0)
    | ~ r2_hidden(X1,k3_relat_1(esk14_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_18])])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk12_0,k3_relat_1(esk14_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_27,plain,(
    ! [X28,X29,X30,X31] :
      ( ( ~ v8_relat_2(X28)
        | ~ r2_hidden(k4_tarski(X29,X30),X28)
        | ~ r2_hidden(k4_tarski(X30,X31),X28)
        | r2_hidden(k4_tarski(X29,X31),X28)
        | ~ v1_relat_1(X28) )
      & ( r2_hidden(k4_tarski(esk3_1(X28),esk4_1(X28)),X28)
        | v8_relat_2(X28)
        | ~ v1_relat_1(X28) )
      & ( r2_hidden(k4_tarski(esk4_1(X28),esk5_1(X28)),X28)
        | v8_relat_2(X28)
        | ~ v1_relat_1(X28) )
      & ( ~ r2_hidden(k4_tarski(esk3_1(X28),esk5_1(X28)),X28)
        | v8_relat_2(X28)
        | ~ v1_relat_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l2_wellord1])])])])])).

cnf(c_0_28,plain,
    ( X1 = X2
    | r2_hidden(X1,k1_wellord1(X3,X2))
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X1,X2),X3) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(k4_tarski(esk13_0,esk12_0),esk14_0)
    | r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | X4 != k1_wellord1(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_31,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_32,plain,(
    ! [X45,X46,X48,X49] :
      ( ( r2_hidden(X48,k3_relat_1(X45))
        | ~ r2_hidden(X48,esk10_2(X45,X46))
        | ~ v1_relat_1(X45) )
      & ( ~ r2_hidden(k4_tarski(X48,X46),X45)
        | ~ r2_hidden(X48,esk10_2(X45,X46))
        | ~ v1_relat_1(X45) )
      & ( ~ r2_hidden(X49,k3_relat_1(X45))
        | r2_hidden(k4_tarski(X49,X46),X45)
        | r2_hidden(X49,esk10_2(X45,X46))
        | ~ v1_relat_1(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[s1_xboole_0__e7_18__wellord1])])])])])])])).

cnf(c_0_33,plain,
    ( r2_hidden(k4_tarski(X2,X4),X1)
    | ~ v8_relat_2(X1)
    | ~ r2_hidden(k4_tarski(X2,X3),X1)
    | ~ r2_hidden(k4_tarski(X3,X4),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)
    | r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_18])])).

cnf(c_0_35,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k1_wellord1(X3,X2)) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)
    | r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,esk10_2(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))
    | r2_hidden(k4_tarski(X1,esk13_0),esk14_0)
    | ~ v8_relat_2(esk14_0)
    | ~ r2_hidden(k4_tarski(X1,esk12_0),esk14_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_18])])).

cnf(c_0_40,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v8_relat_2(X3)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X1,X4),X3)
    | ~ r2_hidden(X4,k1_wellord1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)
    | r2_hidden(X1,k1_wellord1(esk14_0,esk13_0))
    | ~ r2_hidden(X1,k1_wellord1(esk14_0,esk12_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))
    | ~ r2_hidden(esk12_0,esk10_2(esk14_0,esk13_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_34]),c_0_18])])).

cnf(c_0_43,negated_conjecture,
    ( esk13_0 = esk12_0
    | X1 = esk13_0
    | r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))
    | r2_hidden(X1,k1_wellord1(esk14_0,esk13_0))
    | ~ v8_relat_2(esk14_0)
    | ~ r2_hidden(k4_tarski(X1,esk12_0),esk14_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_39]),c_0_18])])).

cnf(c_0_44,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)
    | r2_hidden(k4_tarski(esk13_0,X1),esk14_0)
    | ~ v8_relat_2(esk14_0)
    | ~ r2_hidden(esk12_0,k1_wellord1(esk14_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_29]),c_0_18])])).

cnf(c_0_45,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))
    | r2_hidden(esk12_0,k1_wellord1(esk14_0,esk13_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_34]),c_0_18])])).

fof(c_0_46,plain,(
    ! [X35,X36,X37] :
      ( ( ~ v4_relat_2(X35)
        | ~ r2_hidden(k4_tarski(X36,X37),X35)
        | ~ r2_hidden(k4_tarski(X37,X36),X35)
        | X36 = X37
        | ~ v1_relat_1(X35) )
      & ( r2_hidden(k4_tarski(esk6_1(X35),esk7_1(X35)),X35)
        | v4_relat_2(X35)
        | ~ v1_relat_1(X35) )
      & ( r2_hidden(k4_tarski(esk7_1(X35),esk6_1(X35)),X35)
        | v4_relat_2(X35)
        | ~ v1_relat_1(X35) )
      & ( esk6_1(X35) != esk7_1(X35)
        | v4_relat_2(X35)
        | ~ v1_relat_1(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_wellord1])])])])])).

fof(c_0_47,plain,(
    ! [X14,X15,X16] :
      ( ( r2_hidden(X14,k3_relat_1(X16))
        | ~ r2_hidden(k4_tarski(X14,X15),X16)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(X15,k3_relat_1(X16))
        | ~ r2_hidden(k4_tarski(X14,X15),X16)
        | ~ v1_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_relat_1])])])).

cnf(c_0_48,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,X3)
    | X3 != k1_wellord1(X4,X2)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_49,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(esk13_0,k1_wellord1(esk14_0,esk13_0))
    | r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)
    | ~ r2_hidden(esk12_0,esk10_2(esk14_0,esk13_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( esk13_0 = esk12_0
    | X1 = esk13_0
    | r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))
    | r2_hidden(X1,k1_wellord1(esk14_0,esk13_0))
    | ~ v8_relat_2(esk14_0)
    | ~ r2_hidden(X1,k1_wellord1(esk14_0,esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_35]),c_0_18])])).

cnf(c_0_51,plain,
    ( v8_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_52,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)
    | r2_hidden(k4_tarski(X1,X2),esk14_0)
    | ~ v8_relat_2(esk14_0)
    | ~ r2_hidden(k4_tarski(X1,esk13_0),esk14_0)
    | ~ r2_hidden(esk12_0,k1_wellord1(esk14_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_44]),c_0_18])])).

cnf(c_0_53,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(esk12_0,k1_wellord1(esk14_0,esk13_0))
    | r2_hidden(esk13_0,k1_wellord1(esk14_0,esk13_0))
    | r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_45])).

cnf(c_0_54,plain,
    ( X2 = X3
    | ~ v4_relat_2(X1)
    | ~ r2_hidden(k4_tarski(X2,X3),X1)
    | ~ r2_hidden(k4_tarski(X3,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_55,plain,
    ( r2_hidden(k4_tarski(X1,X3),X2)
    | r2_hidden(X1,esk10_2(X2,X3))
    | ~ r2_hidden(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_57,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_wellord1(X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_48])])).

cnf(c_0_58,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(esk13_0,k1_wellord1(esk14_0,esk13_0))
    | ~ r2_hidden(esk12_0,esk10_2(esk14_0,esk13_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_49]),c_0_18])])).

cnf(c_0_59,negated_conjecture,
    ( esk13_0 = esk12_0
    | X1 = esk13_0
    | r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))
    | r2_hidden(X1,k1_wellord1(esk14_0,esk13_0))
    | ~ r2_hidden(X1,k1_wellord1(esk14_0,esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_23]),c_0_18])])).

cnf(c_0_60,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_61,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)
    | r2_hidden(k4_tarski(X1,X2),esk14_0)
    | ~ v8_relat_2(esk14_0)
    | ~ r2_hidden(esk12_0,k1_wellord1(esk14_0,X2))
    | ~ r2_hidden(X1,k1_wellord1(esk14_0,esk13_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_35]),c_0_18])])).

cnf(c_0_62,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(esk13_0,k1_wellord1(esk14_0,esk13_0))
    | r2_hidden(esk12_0,k1_wellord1(esk14_0,esk13_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_53]),c_0_18])])).

cnf(c_0_63,plain,
    ( r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X2),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k1_wellord1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_64,plain,
    ( X1 = X2
    | r2_hidden(X2,esk10_2(X3,X1))
    | ~ v4_relat_2(X3)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X1,X2),X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])).

cnf(c_0_65,negated_conjecture,
    ( esk13_0 = esk12_0
    | ~ r2_hidden(esk12_0,esk10_2(esk14_0,esk13_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_18])])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_67,negated_conjecture,
    ( esk1_2(k1_wellord1(esk14_0,esk12_0),X1) = esk13_0
    | esk13_0 = esk12_0
    | r2_hidden(esk1_2(k1_wellord1(esk14_0,esk12_0),X1),k1_wellord1(esk14_0,esk13_0))
    | r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))
    | r1_tarski(k1_wellord1(esk14_0,esk12_0),X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)
    | r2_hidden(k4_tarski(X1,X2),esk14_0)
    | ~ r2_hidden(esk12_0,k1_wellord1(esk14_0,X2))
    | ~ r2_hidden(X1,k1_wellord1(esk14_0,esk13_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_51]),c_0_23]),c_0_18])])).

cnf(c_0_69,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(esk12_0,k1_wellord1(esk14_0,esk13_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_62]),c_0_18])])).

fof(c_0_70,plain,(
    ! [X12,X13] :
      ( ( r1_tarski(X12,X13)
        | X12 != X13 )
      & ( r1_tarski(X13,X12)
        | X12 != X13 )
      & ( ~ r1_tarski(X12,X13)
        | ~ r1_tarski(X13,X12)
        | X12 = X13 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_71,negated_conjecture,
    ( X1 = k1_wellord1(esk14_0,X2)
    | r2_hidden(k4_tarski(esk2_3(esk14_0,X2,X1),X2),esk14_0)
    | r2_hidden(esk2_3(esk14_0,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_18])).

cnf(c_0_72,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)
    | ~ v4_relat_2(esk14_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_29]),c_0_18])]),c_0_65])).

cnf(c_0_73,negated_conjecture,
    ( esk1_2(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0)) = esk13_0
    | esk13_0 = esk12_0
    | r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))
    | r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_74,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)
    | r2_hidden(k4_tarski(X1,esk13_0),esk14_0)
    | ~ r2_hidden(X1,k1_wellord1(esk14_0,esk13_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

fof(c_0_75,plain,(
    ! [X17,X18] :
      ( ~ r2_hidden(X17,X18)
      | ~ r1_tarski(X18,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_76,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_77,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X3,k1_wellord1(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_35])).

cnf(c_0_78,negated_conjecture,
    ( X1 = k1_wellord1(esk14_0,X2)
    | r2_hidden(esk2_3(esk14_0,X2,X1),X1)
    | r2_hidden(X2,k3_relat_1(esk14_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_71]),c_0_18])])).

cnf(c_0_79,negated_conjecture,
    ( esk13_0 = esk12_0
    | ~ v4_relat_2(esk14_0)
    | ~ r2_hidden(k4_tarski(esk13_0,esk12_0),esk14_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_72]),c_0_18])])).

cnf(c_0_80,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)
    | ~ r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_81,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))
    | r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_73])).

cnf(c_0_82,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_69])).

cnf(c_0_83,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_84,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_76])).

cnf(c_0_85,negated_conjecture,
    ( k1_wellord1(X1,X2) = k1_wellord1(esk14_0,X3)
    | r2_hidden(X3,k3_relat_1(esk14_0))
    | r2_hidden(X2,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_86,negated_conjecture,
    ( esk13_0 = esk12_0
    | ~ v4_relat_2(esk14_0)
    | ~ r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_35]),c_0_18])])).

cnf(c_0_87,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82])).

cnf(c_0_88,plain,
    ( ~ r2_hidden(X1,X1) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_89,negated_conjecture,
    ( k1_wellord1(esk14_0,X1) = k1_wellord1(esk14_0,X2)
    | r2_hidden(X1,k3_relat_1(esk14_0))
    | r2_hidden(X2,k3_relat_1(esk14_0)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_18])).

fof(c_0_90,plain,(
    ! [X51,X52,X53,X55] :
      ( ( r2_hidden(esk11_3(X51,X52,X53),X53)
        | ~ r1_tarski(X53,X51)
        | X53 = k1_xboole_0
        | ~ r2_wellord1(X52,X51)
        | ~ v1_relat_1(X52) )
      & ( ~ r2_hidden(X55,X53)
        | r2_hidden(k4_tarski(esk11_3(X51,X52,X53),X55),X52)
        | ~ r1_tarski(X53,X51)
        | X53 = k1_xboole_0
        | ~ r2_wellord1(X52,X51)
        | ~ v1_relat_1(X52) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_wellord1])])])])])).

cnf(c_0_91,negated_conjecture,
    ( esk13_0 = esk12_0
    | ~ v4_relat_2(esk14_0) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_92,plain,
    ( v4_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_93,negated_conjecture,
    ( k1_wellord1(esk14_0,X1) = k1_wellord1(esk14_0,k3_relat_1(esk14_0))
    | r2_hidden(X1,k3_relat_1(esk14_0)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_94,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | r1_tarski(k1_wellord1(X2,X1),X3)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_77,c_0_60])).

cnf(c_0_95,plain,
    ( r2_hidden(k4_tarski(esk11_3(X3,X4,X2),X1),X4)
    | X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X3)
    | ~ r2_wellord1(X4,X3)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_96,negated_conjecture,
    ( esk13_0 = esk12_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_23]),c_0_18])])).

cnf(c_0_97,negated_conjecture,
    ( r2_hidden(X1,k3_relat_1(esk14_0))
    | ~ r2_hidden(X2,k1_wellord1(esk14_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_93]),c_0_18])]),c_0_88])).

cnf(c_0_98,plain,
    ( r2_hidden(esk11_3(X1,X2,X3),X3)
    | X3 = k1_xboole_0
    | ~ r1_tarski(X3,X1)
    | ~ r2_wellord1(X2,X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_99,negated_conjecture,
    ( r2_hidden(X1,k3_relat_1(esk14_0))
    | r1_tarski(k1_wellord1(esk14_0,X1),X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_93]),c_0_18])]),c_0_88])).

fof(c_0_100,plain,(
    ! [X50] :
      ( ( ~ r2_wellord1(X50,k3_relat_1(X50))
        | v2_wellord1(X50)
        | ~ v1_relat_1(X50) )
      & ( ~ v2_wellord1(X50)
        | r2_wellord1(X50,k3_relat_1(X50))
        | ~ v1_relat_1(X50) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_wellord1])])])).

cnf(c_0_101,plain,
    ( X1 = k1_xboole_0
    | ~ r2_wellord1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(esk11_3(X3,X2,X1),esk10_2(X2,X4))
    | ~ r2_hidden(X4,X1)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_38,c_0_95])).

cnf(c_0_102,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_96]),c_0_96]),c_0_84])])).

cnf(c_0_103,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(X1,esk10_2(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_104,negated_conjecture,
    ( k1_wellord1(esk14_0,X1) = k1_xboole_0
    | r2_hidden(X1,k3_relat_1(esk14_0))
    | ~ r2_wellord1(X2,X3)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_99])).

cnf(c_0_105,plain,
    ( r2_wellord1(X1,k3_relat_1(X1))
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

cnf(c_0_106,plain,
    ( esk10_2(X1,X2) = k1_xboole_0
    | ~ r2_wellord1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,esk10_2(X1,X2))
    | ~ r1_tarski(esk10_2(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_101,c_0_98])).

cnf(c_0_107,negated_conjecture,
    ( r2_hidden(esk12_0,esk10_2(esk14_0,esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_55]),c_0_18]),c_0_26])])).

cnf(c_0_108,plain,
    ( r2_hidden(esk1_2(esk10_2(X1,X2),X3),k3_relat_1(X1))
    | r1_tarski(esk10_2(X1,X2),X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_103,c_0_60])).

cnf(c_0_109,negated_conjecture,
    ( k1_wellord1(esk14_0,X1) = k1_xboole_0
    | r2_hidden(X1,k3_relat_1(esk14_0))
    | ~ v2_wellord1(X2)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_110,negated_conjecture,
    ( esk10_2(esk14_0,esk12_0) = k1_xboole_0
    | ~ r2_wellord1(esk14_0,X1)
    | ~ r1_tarski(esk10_2(esk14_0,esk12_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_18])])).

cnf(c_0_111,plain,
    ( r1_tarski(esk10_2(X1,X2),k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_108])).

cnf(c_0_112,negated_conjecture,
    ( k1_wellord1(esk14_0,X1) = k1_xboole_0
    | r2_hidden(X1,k3_relat_1(esk14_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_23]),c_0_18])])).

cnf(c_0_113,negated_conjecture,
    ( esk10_2(esk14_0,esk12_0) = k1_xboole_0
    | ~ r2_wellord1(esk14_0,k3_relat_1(esk14_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_18])])).

cnf(c_0_114,negated_conjecture,
    ( k1_wellord1(esk14_0,k3_relat_1(esk14_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_88,c_0_112])).

cnf(c_0_115,negated_conjecture,
    ( esk10_2(esk14_0,esk12_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_105]),c_0_23]),c_0_18])])).

cnf(c_0_116,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_114]),c_0_18])]),c_0_88])).

cnf(c_0_117,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_107,c_0_115]),c_0_116]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:32:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.53/0.73  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.53/0.73  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.53/0.73  #
% 0.53/0.73  # Preprocessing time       : 0.029 s
% 0.53/0.73  
% 0.53/0.73  # Proof found!
% 0.53/0.73  # SZS status Theorem
% 0.53/0.73  # SZS output start CNFRefutation
% 0.53/0.73  fof(t37_wellord1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(((v2_wellord1(X3)&r2_hidden(X1,k3_relat_1(X3)))&r2_hidden(X2,k3_relat_1(X3)))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_wellord1)).
% 0.53/0.73  fof(l4_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v6_relat_2(X1)<=>![X2, X3]:~(((((r2_hidden(X2,k3_relat_1(X1))&r2_hidden(X3,k3_relat_1(X1)))&X2!=X3)&~(r2_hidden(k4_tarski(X2,X3),X1)))&~(r2_hidden(k4_tarski(X3,X2),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l4_wellord1)).
% 0.53/0.73  fof(d4_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v2_wellord1(X1)<=>((((v1_relat_2(X1)&v8_relat_2(X1))&v4_relat_2(X1))&v6_relat_2(X1))&v1_wellord1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_wellord1)).
% 0.53/0.73  fof(d1_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k1_wellord1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4!=X2&r2_hidden(k4_tarski(X4,X2),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord1)).
% 0.53/0.73  fof(l2_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v8_relat_2(X1)<=>![X2, X3, X4]:((r2_hidden(k4_tarski(X2,X3),X1)&r2_hidden(k4_tarski(X3,X4),X1))=>r2_hidden(k4_tarski(X2,X4),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l2_wellord1)).
% 0.53/0.73  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.53/0.73  fof(s1_xboole_0__e7_18__wellord1, axiom, ![X1, X2]:(v1_relat_1(X1)=>?[X3]:![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,k3_relat_1(X1))&~(r2_hidden(k4_tarski(X4,X2),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s1_xboole_0__e7_18__wellord1)).
% 0.53/0.73  fof(l3_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v4_relat_2(X1)<=>![X2, X3]:((r2_hidden(k4_tarski(X2,X3),X1)&r2_hidden(k4_tarski(X3,X2),X1))=>X2=X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_wellord1)).
% 0.53/0.73  fof(t30_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k3_relat_1(X3))&r2_hidden(X2,k3_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relat_1)).
% 0.53/0.73  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.53/0.73  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.53/0.73  fof(t9_wellord1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r2_wellord1(X2,X1)=>![X3]:~(((r1_tarski(X3,X1)&X3!=k1_xboole_0)&![X4]:~((r2_hidden(X4,X3)&![X5]:(r2_hidden(X5,X3)=>r2_hidden(k4_tarski(X4,X5),X2)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_wellord1)).
% 0.53/0.73  fof(t8_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(r2_wellord1(X1,k3_relat_1(X1))<=>v2_wellord1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_wellord1)).
% 0.53/0.73  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(((v2_wellord1(X3)&r2_hidden(X1,k3_relat_1(X3)))&r2_hidden(X2,k3_relat_1(X3)))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2)))))), inference(assume_negation,[status(cth)],[t37_wellord1])).
% 0.53/0.73  fof(c_0_14, plain, ![X40, X41, X42]:((~v6_relat_2(X40)|(~r2_hidden(X41,k3_relat_1(X40))|~r2_hidden(X42,k3_relat_1(X40))|X41=X42|r2_hidden(k4_tarski(X41,X42),X40)|r2_hidden(k4_tarski(X42,X41),X40))|~v1_relat_1(X40))&(((((r2_hidden(esk8_1(X40),k3_relat_1(X40))|v6_relat_2(X40)|~v1_relat_1(X40))&(r2_hidden(esk9_1(X40),k3_relat_1(X40))|v6_relat_2(X40)|~v1_relat_1(X40)))&(esk8_1(X40)!=esk9_1(X40)|v6_relat_2(X40)|~v1_relat_1(X40)))&(~r2_hidden(k4_tarski(esk8_1(X40),esk9_1(X40)),X40)|v6_relat_2(X40)|~v1_relat_1(X40)))&(~r2_hidden(k4_tarski(esk9_1(X40),esk8_1(X40)),X40)|v6_relat_2(X40)|~v1_relat_1(X40)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l4_wellord1])])])])])])).
% 0.53/0.73  fof(c_0_15, negated_conjecture, (v1_relat_1(esk14_0)&(((v2_wellord1(esk14_0)&r2_hidden(esk12_0,k3_relat_1(esk14_0)))&r2_hidden(esk13_0,k3_relat_1(esk14_0)))&((~r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)|~r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0)))&(r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)|r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.53/0.73  cnf(c_0_16, plain, (X2=X3|r2_hidden(k4_tarski(X2,X3),X1)|r2_hidden(k4_tarski(X3,X2),X1)|~v6_relat_2(X1)|~r2_hidden(X2,k3_relat_1(X1))|~r2_hidden(X3,k3_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.53/0.73  cnf(c_0_17, negated_conjecture, (r2_hidden(esk13_0,k3_relat_1(esk14_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.53/0.73  cnf(c_0_18, negated_conjecture, (v1_relat_1(esk14_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.53/0.73  fof(c_0_19, plain, ![X27]:((((((v1_relat_2(X27)|~v2_wellord1(X27)|~v1_relat_1(X27))&(v8_relat_2(X27)|~v2_wellord1(X27)|~v1_relat_1(X27)))&(v4_relat_2(X27)|~v2_wellord1(X27)|~v1_relat_1(X27)))&(v6_relat_2(X27)|~v2_wellord1(X27)|~v1_relat_1(X27)))&(v1_wellord1(X27)|~v2_wellord1(X27)|~v1_relat_1(X27)))&(~v1_relat_2(X27)|~v8_relat_2(X27)|~v4_relat_2(X27)|~v6_relat_2(X27)|~v1_wellord1(X27)|v2_wellord1(X27)|~v1_relat_1(X27))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).
% 0.53/0.73  fof(c_0_20, plain, ![X19, X20, X21, X22, X23, X24, X25]:((((X22!=X20|~r2_hidden(X22,X21)|X21!=k1_wellord1(X19,X20)|~v1_relat_1(X19))&(r2_hidden(k4_tarski(X22,X20),X19)|~r2_hidden(X22,X21)|X21!=k1_wellord1(X19,X20)|~v1_relat_1(X19)))&(X23=X20|~r2_hidden(k4_tarski(X23,X20),X19)|r2_hidden(X23,X21)|X21!=k1_wellord1(X19,X20)|~v1_relat_1(X19)))&((~r2_hidden(esk2_3(X19,X24,X25),X25)|(esk2_3(X19,X24,X25)=X24|~r2_hidden(k4_tarski(esk2_3(X19,X24,X25),X24),X19))|X25=k1_wellord1(X19,X24)|~v1_relat_1(X19))&((esk2_3(X19,X24,X25)!=X24|r2_hidden(esk2_3(X19,X24,X25),X25)|X25=k1_wellord1(X19,X24)|~v1_relat_1(X19))&(r2_hidden(k4_tarski(esk2_3(X19,X24,X25),X24),X19)|r2_hidden(esk2_3(X19,X24,X25),X25)|X25=k1_wellord1(X19,X24)|~v1_relat_1(X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).
% 0.53/0.73  cnf(c_0_21, negated_conjecture, (X1=esk13_0|r2_hidden(k4_tarski(esk13_0,X1),esk14_0)|r2_hidden(k4_tarski(X1,esk13_0),esk14_0)|~v6_relat_2(esk14_0)|~r2_hidden(X1,k3_relat_1(esk14_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])])).
% 0.53/0.73  cnf(c_0_22, plain, (v6_relat_2(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.53/0.73  cnf(c_0_23, negated_conjecture, (v2_wellord1(esk14_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.53/0.73  cnf(c_0_24, plain, (X1=X2|r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_wellord1(X3,X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.53/0.73  cnf(c_0_25, negated_conjecture, (X1=esk13_0|r2_hidden(k4_tarski(X1,esk13_0),esk14_0)|r2_hidden(k4_tarski(esk13_0,X1),esk14_0)|~r2_hidden(X1,k3_relat_1(esk14_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_18])])).
% 0.53/0.73  cnf(c_0_26, negated_conjecture, (r2_hidden(esk12_0,k3_relat_1(esk14_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.53/0.73  fof(c_0_27, plain, ![X28, X29, X30, X31]:((~v8_relat_2(X28)|(~r2_hidden(k4_tarski(X29,X30),X28)|~r2_hidden(k4_tarski(X30,X31),X28)|r2_hidden(k4_tarski(X29,X31),X28))|~v1_relat_1(X28))&(((r2_hidden(k4_tarski(esk3_1(X28),esk4_1(X28)),X28)|v8_relat_2(X28)|~v1_relat_1(X28))&(r2_hidden(k4_tarski(esk4_1(X28),esk5_1(X28)),X28)|v8_relat_2(X28)|~v1_relat_1(X28)))&(~r2_hidden(k4_tarski(esk3_1(X28),esk5_1(X28)),X28)|v8_relat_2(X28)|~v1_relat_1(X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l2_wellord1])])])])])).
% 0.53/0.73  cnf(c_0_28, plain, (X1=X2|r2_hidden(X1,k1_wellord1(X3,X2))|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X1,X2),X3)), inference(er,[status(thm)],[c_0_24])).
% 0.53/0.73  cnf(c_0_29, negated_conjecture, (esk13_0=esk12_0|r2_hidden(k4_tarski(esk13_0,esk12_0),esk14_0)|r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.53/0.73  cnf(c_0_30, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,X4)|X4!=k1_wellord1(X3,X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.53/0.73  fof(c_0_31, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.53/0.73  fof(c_0_32, plain, ![X45, X46, X48, X49]:(((r2_hidden(X48,k3_relat_1(X45))|~r2_hidden(X48,esk10_2(X45,X46))|~v1_relat_1(X45))&(~r2_hidden(k4_tarski(X48,X46),X45)|~r2_hidden(X48,esk10_2(X45,X46))|~v1_relat_1(X45)))&(~r2_hidden(X49,k3_relat_1(X45))|r2_hidden(k4_tarski(X49,X46),X45)|r2_hidden(X49,esk10_2(X45,X46))|~v1_relat_1(X45))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[s1_xboole_0__e7_18__wellord1])])])])])])])).
% 0.53/0.73  cnf(c_0_33, plain, (r2_hidden(k4_tarski(X2,X4),X1)|~v8_relat_2(X1)|~r2_hidden(k4_tarski(X2,X3),X1)|~r2_hidden(k4_tarski(X3,X4),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.53/0.73  cnf(c_0_34, negated_conjecture, (esk13_0=esk12_0|r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)|r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_18])])).
% 0.53/0.73  cnf(c_0_35, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)|~r2_hidden(X1,k1_wellord1(X3,X2))), inference(er,[status(thm)],[c_0_30])).
% 0.53/0.73  cnf(c_0_36, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.53/0.73  cnf(c_0_37, negated_conjecture, (r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)|r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.53/0.73  cnf(c_0_38, plain, (~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,esk10_2(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.53/0.73  cnf(c_0_39, negated_conjecture, (esk13_0=esk12_0|r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))|r2_hidden(k4_tarski(X1,esk13_0),esk14_0)|~v8_relat_2(esk14_0)|~r2_hidden(k4_tarski(X1,esk12_0),esk14_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_18])])).
% 0.53/0.73  cnf(c_0_40, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~v8_relat_2(X3)|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X1,X4),X3)|~r2_hidden(X4,k1_wellord1(X3,X2))), inference(spm,[status(thm)],[c_0_33, c_0_35])).
% 0.53/0.73  cnf(c_0_41, negated_conjecture, (r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)|r2_hidden(X1,k1_wellord1(esk14_0,esk13_0))|~r2_hidden(X1,k1_wellord1(esk14_0,esk12_0))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.53/0.73  cnf(c_0_42, negated_conjecture, (esk13_0=esk12_0|r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))|~r2_hidden(esk12_0,esk10_2(esk14_0,esk13_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_34]), c_0_18])])).
% 0.53/0.73  cnf(c_0_43, negated_conjecture, (esk13_0=esk12_0|X1=esk13_0|r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))|r2_hidden(X1,k1_wellord1(esk14_0,esk13_0))|~v8_relat_2(esk14_0)|~r2_hidden(k4_tarski(X1,esk12_0),esk14_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_39]), c_0_18])])).
% 0.53/0.73  cnf(c_0_44, negated_conjecture, (esk13_0=esk12_0|r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)|r2_hidden(k4_tarski(esk13_0,X1),esk14_0)|~v8_relat_2(esk14_0)|~r2_hidden(esk12_0,k1_wellord1(esk14_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_29]), c_0_18])])).
% 0.53/0.73  cnf(c_0_45, negated_conjecture, (esk13_0=esk12_0|r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))|r2_hidden(esk12_0,k1_wellord1(esk14_0,esk13_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_34]), c_0_18])])).
% 0.53/0.73  fof(c_0_46, plain, ![X35, X36, X37]:((~v4_relat_2(X35)|(~r2_hidden(k4_tarski(X36,X37),X35)|~r2_hidden(k4_tarski(X37,X36),X35)|X36=X37)|~v1_relat_1(X35))&(((r2_hidden(k4_tarski(esk6_1(X35),esk7_1(X35)),X35)|v4_relat_2(X35)|~v1_relat_1(X35))&(r2_hidden(k4_tarski(esk7_1(X35),esk6_1(X35)),X35)|v4_relat_2(X35)|~v1_relat_1(X35)))&(esk6_1(X35)!=esk7_1(X35)|v4_relat_2(X35)|~v1_relat_1(X35)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_wellord1])])])])])).
% 0.53/0.73  fof(c_0_47, plain, ![X14, X15, X16]:((r2_hidden(X14,k3_relat_1(X16))|~r2_hidden(k4_tarski(X14,X15),X16)|~v1_relat_1(X16))&(r2_hidden(X15,k3_relat_1(X16))|~r2_hidden(k4_tarski(X14,X15),X16)|~v1_relat_1(X16))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_relat_1])])])).
% 0.53/0.73  cnf(c_0_48, plain, (X1!=X2|~r2_hidden(X1,X3)|X3!=k1_wellord1(X4,X2)|~v1_relat_1(X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.53/0.73  cnf(c_0_49, negated_conjecture, (esk13_0=esk12_0|r2_hidden(esk13_0,k1_wellord1(esk14_0,esk13_0))|r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)|~r2_hidden(esk12_0,esk10_2(esk14_0,esk13_0))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.53/0.73  cnf(c_0_50, negated_conjecture, (esk13_0=esk12_0|X1=esk13_0|r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))|r2_hidden(X1,k1_wellord1(esk14_0,esk13_0))|~v8_relat_2(esk14_0)|~r2_hidden(X1,k1_wellord1(esk14_0,esk12_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_35]), c_0_18])])).
% 0.53/0.73  cnf(c_0_51, plain, (v8_relat_2(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.53/0.73  cnf(c_0_52, negated_conjecture, (esk13_0=esk12_0|r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)|r2_hidden(k4_tarski(X1,X2),esk14_0)|~v8_relat_2(esk14_0)|~r2_hidden(k4_tarski(X1,esk13_0),esk14_0)|~r2_hidden(esk12_0,k1_wellord1(esk14_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_44]), c_0_18])])).
% 0.53/0.73  cnf(c_0_53, negated_conjecture, (esk13_0=esk12_0|r2_hidden(esk12_0,k1_wellord1(esk14_0,esk13_0))|r2_hidden(esk13_0,k1_wellord1(esk14_0,esk13_0))|r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)), inference(spm,[status(thm)],[c_0_41, c_0_45])).
% 0.53/0.73  cnf(c_0_54, plain, (X2=X3|~v4_relat_2(X1)|~r2_hidden(k4_tarski(X2,X3),X1)|~r2_hidden(k4_tarski(X3,X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.53/0.73  cnf(c_0_55, plain, (r2_hidden(k4_tarski(X1,X3),X2)|r2_hidden(X1,esk10_2(X2,X3))|~r2_hidden(X1,k3_relat_1(X2))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.53/0.73  cnf(c_0_56, plain, (r2_hidden(X1,k3_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.53/0.73  cnf(c_0_57, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k1_wellord1(X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_48])])).
% 0.53/0.73  cnf(c_0_58, negated_conjecture, (esk13_0=esk12_0|r2_hidden(esk13_0,k1_wellord1(esk14_0,esk13_0))|~r2_hidden(esk12_0,esk10_2(esk14_0,esk13_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_49]), c_0_18])])).
% 0.53/0.73  cnf(c_0_59, negated_conjecture, (esk13_0=esk12_0|X1=esk13_0|r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))|r2_hidden(X1,k1_wellord1(esk14_0,esk13_0))|~r2_hidden(X1,k1_wellord1(esk14_0,esk12_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_23]), c_0_18])])).
% 0.53/0.73  cnf(c_0_60, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.53/0.73  cnf(c_0_61, negated_conjecture, (esk13_0=esk12_0|r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)|r2_hidden(k4_tarski(X1,X2),esk14_0)|~v8_relat_2(esk14_0)|~r2_hidden(esk12_0,k1_wellord1(esk14_0,X2))|~r2_hidden(X1,k1_wellord1(esk14_0,esk13_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_35]), c_0_18])])).
% 0.53/0.73  cnf(c_0_62, negated_conjecture, (esk13_0=esk12_0|r2_hidden(esk13_0,k1_wellord1(esk14_0,esk13_0))|r2_hidden(esk12_0,k1_wellord1(esk14_0,esk13_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_53]), c_0_18])])).
% 0.53/0.73  cnf(c_0_63, plain, (r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X2),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k1_wellord1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.53/0.73  cnf(c_0_64, plain, (X1=X2|r2_hidden(X2,esk10_2(X3,X1))|~v4_relat_2(X3)|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X1,X2),X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])).
% 0.53/0.73  cnf(c_0_65, negated_conjecture, (esk13_0=esk12_0|~r2_hidden(esk12_0,esk10_2(esk14_0,esk13_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_18])])).
% 0.53/0.73  cnf(c_0_66, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.53/0.73  cnf(c_0_67, negated_conjecture, (esk1_2(k1_wellord1(esk14_0,esk12_0),X1)=esk13_0|esk13_0=esk12_0|r2_hidden(esk1_2(k1_wellord1(esk14_0,esk12_0),X1),k1_wellord1(esk14_0,esk13_0))|r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))|r1_tarski(k1_wellord1(esk14_0,esk12_0),X1)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.53/0.73  cnf(c_0_68, negated_conjecture, (esk13_0=esk12_0|r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)|r2_hidden(k4_tarski(X1,X2),esk14_0)|~r2_hidden(esk12_0,k1_wellord1(esk14_0,X2))|~r2_hidden(X1,k1_wellord1(esk14_0,esk13_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_51]), c_0_23]), c_0_18])])).
% 0.53/0.73  cnf(c_0_69, negated_conjecture, (esk13_0=esk12_0|r2_hidden(esk12_0,k1_wellord1(esk14_0,esk13_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_62]), c_0_18])])).
% 0.53/0.73  fof(c_0_70, plain, ![X12, X13]:(((r1_tarski(X12,X13)|X12!=X13)&(r1_tarski(X13,X12)|X12!=X13))&(~r1_tarski(X12,X13)|~r1_tarski(X13,X12)|X12=X13)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.53/0.73  cnf(c_0_71, negated_conjecture, (X1=k1_wellord1(esk14_0,X2)|r2_hidden(k4_tarski(esk2_3(esk14_0,X2,X1),X2),esk14_0)|r2_hidden(esk2_3(esk14_0,X2,X1),X1)), inference(spm,[status(thm)],[c_0_63, c_0_18])).
% 0.53/0.73  cnf(c_0_72, negated_conjecture, (esk13_0=esk12_0|r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)|~v4_relat_2(esk14_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_29]), c_0_18])]), c_0_65])).
% 0.53/0.73  cnf(c_0_73, negated_conjecture, (esk1_2(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0))=esk13_0|esk13_0=esk12_0|r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))|r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.53/0.73  cnf(c_0_74, negated_conjecture, (esk13_0=esk12_0|r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)|r2_hidden(k4_tarski(X1,esk13_0),esk14_0)|~r2_hidden(X1,k1_wellord1(esk14_0,esk13_0))), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.53/0.73  fof(c_0_75, plain, ![X17, X18]:(~r2_hidden(X17,X18)|~r1_tarski(X18,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.53/0.73  cnf(c_0_76, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.53/0.73  cnf(c_0_77, plain, (r2_hidden(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r2_hidden(X3,k1_wellord1(X2,X1))), inference(spm,[status(thm)],[c_0_56, c_0_35])).
% 0.53/0.73  cnf(c_0_78, negated_conjecture, (X1=k1_wellord1(esk14_0,X2)|r2_hidden(esk2_3(esk14_0,X2,X1),X1)|r2_hidden(X2,k3_relat_1(esk14_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_71]), c_0_18])])).
% 0.53/0.73  cnf(c_0_79, negated_conjecture, (esk13_0=esk12_0|~v4_relat_2(esk14_0)|~r2_hidden(k4_tarski(esk13_0,esk12_0),esk14_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_72]), c_0_18])])).
% 0.53/0.73  cnf(c_0_80, negated_conjecture, (~r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)|~r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.53/0.73  cnf(c_0_81, negated_conjecture, (esk13_0=esk12_0|r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))|r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0))), inference(spm,[status(thm)],[c_0_60, c_0_73])).
% 0.53/0.73  cnf(c_0_82, negated_conjecture, (esk13_0=esk12_0|r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)), inference(spm,[status(thm)],[c_0_74, c_0_69])).
% 0.53/0.73  cnf(c_0_83, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.53/0.73  cnf(c_0_84, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_76])).
% 0.53/0.73  cnf(c_0_85, negated_conjecture, (k1_wellord1(X1,X2)=k1_wellord1(esk14_0,X3)|r2_hidden(X3,k3_relat_1(esk14_0))|r2_hidden(X2,k3_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.53/0.73  cnf(c_0_86, negated_conjecture, (esk13_0=esk12_0|~v4_relat_2(esk14_0)|~r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_35]), c_0_18])])).
% 0.53/0.73  cnf(c_0_87, negated_conjecture, (esk13_0=esk12_0|r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_82])).
% 0.53/0.73  cnf(c_0_88, plain, (~r2_hidden(X1,X1)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.53/0.73  cnf(c_0_89, negated_conjecture, (k1_wellord1(esk14_0,X1)=k1_wellord1(esk14_0,X2)|r2_hidden(X1,k3_relat_1(esk14_0))|r2_hidden(X2,k3_relat_1(esk14_0))), inference(spm,[status(thm)],[c_0_85, c_0_18])).
% 0.53/0.73  fof(c_0_90, plain, ![X51, X52, X53, X55]:((r2_hidden(esk11_3(X51,X52,X53),X53)|(~r1_tarski(X53,X51)|X53=k1_xboole_0)|~r2_wellord1(X52,X51)|~v1_relat_1(X52))&(~r2_hidden(X55,X53)|r2_hidden(k4_tarski(esk11_3(X51,X52,X53),X55),X52)|(~r1_tarski(X53,X51)|X53=k1_xboole_0)|~r2_wellord1(X52,X51)|~v1_relat_1(X52))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_wellord1])])])])])).
% 0.53/0.73  cnf(c_0_91, negated_conjecture, (esk13_0=esk12_0|~v4_relat_2(esk14_0)), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.53/0.73  cnf(c_0_92, plain, (v4_relat_2(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.53/0.73  cnf(c_0_93, negated_conjecture, (k1_wellord1(esk14_0,X1)=k1_wellord1(esk14_0,k3_relat_1(esk14_0))|r2_hidden(X1,k3_relat_1(esk14_0))), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.53/0.73  cnf(c_0_94, plain, (r2_hidden(X1,k3_relat_1(X2))|r1_tarski(k1_wellord1(X2,X1),X3)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_77, c_0_60])).
% 0.53/0.73  cnf(c_0_95, plain, (r2_hidden(k4_tarski(esk11_3(X3,X4,X2),X1),X4)|X2=k1_xboole_0|~r2_hidden(X1,X2)|~r1_tarski(X2,X3)|~r2_wellord1(X4,X3)|~v1_relat_1(X4)), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.53/0.73  cnf(c_0_96, negated_conjecture, (esk13_0=esk12_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_23]), c_0_18])])).
% 0.53/0.73  cnf(c_0_97, negated_conjecture, (r2_hidden(X1,k3_relat_1(esk14_0))|~r2_hidden(X2,k1_wellord1(esk14_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_93]), c_0_18])]), c_0_88])).
% 0.53/0.73  cnf(c_0_98, plain, (r2_hidden(esk11_3(X1,X2,X3),X3)|X3=k1_xboole_0|~r1_tarski(X3,X1)|~r2_wellord1(X2,X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.53/0.73  cnf(c_0_99, negated_conjecture, (r2_hidden(X1,k3_relat_1(esk14_0))|r1_tarski(k1_wellord1(esk14_0,X1),X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_93]), c_0_18])]), c_0_88])).
% 0.53/0.73  fof(c_0_100, plain, ![X50]:((~r2_wellord1(X50,k3_relat_1(X50))|v2_wellord1(X50)|~v1_relat_1(X50))&(~v2_wellord1(X50)|r2_wellord1(X50,k3_relat_1(X50))|~v1_relat_1(X50))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_wellord1])])])).
% 0.53/0.73  cnf(c_0_101, plain, (X1=k1_xboole_0|~r2_wellord1(X2,X3)|~v1_relat_1(X2)|~r2_hidden(esk11_3(X3,X2,X1),esk10_2(X2,X4))|~r2_hidden(X4,X1)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_38, c_0_95])).
% 0.53/0.73  cnf(c_0_102, negated_conjecture, (~r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_96]), c_0_96]), c_0_84])])).
% 0.53/0.73  cnf(c_0_103, plain, (r2_hidden(X1,k3_relat_1(X2))|~r2_hidden(X1,esk10_2(X2,X3))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.53/0.73  cnf(c_0_104, negated_conjecture, (k1_wellord1(esk14_0,X1)=k1_xboole_0|r2_hidden(X1,k3_relat_1(esk14_0))|~r2_wellord1(X2,X3)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_99])).
% 0.53/0.73  cnf(c_0_105, plain, (r2_wellord1(X1,k3_relat_1(X1))|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_100])).
% 0.53/0.73  cnf(c_0_106, plain, (esk10_2(X1,X2)=k1_xboole_0|~r2_wellord1(X1,X3)|~v1_relat_1(X1)|~r2_hidden(X2,esk10_2(X1,X2))|~r1_tarski(esk10_2(X1,X2),X3)), inference(spm,[status(thm)],[c_0_101, c_0_98])).
% 0.53/0.73  cnf(c_0_107, negated_conjecture, (r2_hidden(esk12_0,esk10_2(esk14_0,esk12_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_55]), c_0_18]), c_0_26])])).
% 0.53/0.73  cnf(c_0_108, plain, (r2_hidden(esk1_2(esk10_2(X1,X2),X3),k3_relat_1(X1))|r1_tarski(esk10_2(X1,X2),X3)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_103, c_0_60])).
% 0.53/0.73  cnf(c_0_109, negated_conjecture, (k1_wellord1(esk14_0,X1)=k1_xboole_0|r2_hidden(X1,k3_relat_1(esk14_0))|~v2_wellord1(X2)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_104, c_0_105])).
% 0.53/0.73  cnf(c_0_110, negated_conjecture, (esk10_2(esk14_0,esk12_0)=k1_xboole_0|~r2_wellord1(esk14_0,X1)|~r1_tarski(esk10_2(esk14_0,esk12_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_18])])).
% 0.53/0.73  cnf(c_0_111, plain, (r1_tarski(esk10_2(X1,X2),k3_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_66, c_0_108])).
% 0.53/0.73  cnf(c_0_112, negated_conjecture, (k1_wellord1(esk14_0,X1)=k1_xboole_0|r2_hidden(X1,k3_relat_1(esk14_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_23]), c_0_18])])).
% 0.53/0.73  cnf(c_0_113, negated_conjecture, (esk10_2(esk14_0,esk12_0)=k1_xboole_0|~r2_wellord1(esk14_0,k3_relat_1(esk14_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_18])])).
% 0.53/0.73  cnf(c_0_114, negated_conjecture, (k1_wellord1(esk14_0,k3_relat_1(esk14_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_88, c_0_112])).
% 0.53/0.73  cnf(c_0_115, negated_conjecture, (esk10_2(esk14_0,esk12_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_105]), c_0_23]), c_0_18])])).
% 0.53/0.73  cnf(c_0_116, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_114]), c_0_18])]), c_0_88])).
% 0.53/0.73  cnf(c_0_117, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_107, c_0_115]), c_0_116]), ['proof']).
% 0.53/0.73  # SZS output end CNFRefutation
% 0.53/0.73  # Proof object total steps             : 118
% 0.53/0.73  # Proof object clause steps            : 91
% 0.53/0.73  # Proof object formula steps           : 27
% 0.53/0.73  # Proof object conjectures             : 59
% 0.53/0.73  # Proof object clause conjectures      : 56
% 0.53/0.73  # Proof object formula conjectures     : 3
% 0.53/0.73  # Proof object initial clauses used    : 28
% 0.53/0.73  # Proof object initial formulas used   : 13
% 0.53/0.73  # Proof object generating inferences   : 57
% 0.53/0.73  # Proof object simplifying inferences  : 84
% 0.53/0.73  # Training examples: 0 positive, 0 negative
% 0.53/0.73  # Parsed axioms                        : 13
% 0.53/0.73  # Removed by relevancy pruning/SinE    : 0
% 0.53/0.73  # Initial clauses                      : 48
% 0.53/0.73  # Removed in clause preprocessing      : 0
% 0.53/0.73  # Initial clauses in saturation        : 48
% 0.53/0.73  # Processed clauses                    : 3081
% 0.53/0.73  # ...of these trivial                  : 14
% 0.53/0.73  # ...subsumed                          : 1965
% 0.53/0.73  # ...remaining for further processing  : 1102
% 0.53/0.73  # Other redundant clauses eliminated   : 6
% 0.53/0.73  # Clauses deleted for lack of memory   : 0
% 0.53/0.73  # Backward-subsumed                    : 398
% 0.53/0.73  # Backward-rewritten                   : 308
% 0.53/0.73  # Generated clauses                    : 15476
% 0.53/0.73  # ...of the previous two non-trivial   : 13321
% 0.53/0.73  # Contextual simplify-reflections      : 34
% 0.53/0.73  # Paramodulations                      : 15465
% 0.53/0.73  # Factorizations                       : 6
% 0.53/0.73  # Equation resolutions                 : 6
% 0.53/0.73  # Propositional unsat checks           : 0
% 0.53/0.73  #    Propositional check models        : 0
% 0.53/0.73  #    Propositional check unsatisfiable : 0
% 0.53/0.73  #    Propositional clauses             : 0
% 0.53/0.73  #    Propositional clauses after purity: 0
% 0.53/0.73  #    Propositional unsat core size     : 0
% 0.53/0.73  #    Propositional preprocessing time  : 0.000
% 0.53/0.73  #    Propositional encoding time       : 0.000
% 0.53/0.73  #    Propositional solver time         : 0.000
% 0.53/0.73  #    Success case prop preproc time    : 0.000
% 0.53/0.73  #    Success case prop encoding time   : 0.000
% 0.53/0.73  #    Success case prop solver time     : 0.000
% 0.53/0.73  # Current number of processed clauses  : 391
% 0.53/0.73  #    Positive orientable unit clauses  : 9
% 0.53/0.73  #    Positive unorientable unit clauses: 0
% 0.53/0.73  #    Negative unit clauses             : 6
% 0.53/0.73  #    Non-unit-clauses                  : 376
% 0.53/0.73  # Current number of unprocessed clauses: 9899
% 0.53/0.73  # ...number of literals in the above   : 69603
% 0.53/0.73  # Current number of archived formulas  : 0
% 0.53/0.73  # Current number of archived clauses   : 706
% 0.53/0.73  # Clause-clause subsumption calls (NU) : 96049
% 0.53/0.73  # Rec. Clause-clause subsumption calls : 12153
% 0.53/0.73  # Non-unit clause-clause subsumptions  : 2207
% 0.53/0.73  # Unit Clause-clause subsumption calls : 1522
% 0.53/0.73  # Rewrite failures with RHS unbound    : 0
% 0.53/0.73  # BW rewrite match attempts            : 8
% 0.53/0.73  # BW rewrite match successes           : 4
% 0.53/0.73  # Condensation attempts                : 0
% 0.53/0.73  # Condensation successes               : 0
% 0.53/0.73  # Termbank termtop insertions          : 391012
% 0.53/0.74  
% 0.53/0.74  # -------------------------------------------------
% 0.53/0.74  # User time                : 0.388 s
% 0.53/0.74  # System time              : 0.013 s
% 0.53/0.74  # Total time               : 0.401 s
% 0.53/0.74  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
