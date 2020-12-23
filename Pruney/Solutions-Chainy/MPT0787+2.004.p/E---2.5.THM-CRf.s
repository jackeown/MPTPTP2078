%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:55 EST 2020

% Result     : Theorem 0.47s
% Output     : CNFRefutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  101 (1349 expanded)
%              Number of clauses        :   76 ( 536 expanded)
%              Number of leaves         :   12 ( 321 expanded)
%              Depth                    :   21
%              Number of atoms          :  445 (8035 expanded)
%              Number of equality atoms :   75 ( 807 expanded)
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

fof(t10_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => ! [X2] :
            ~ ( r1_tarski(X2,k3_relat_1(X1))
              & X2 != k1_xboole_0
              & ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & ! [X4] :
                        ( r2_hidden(X4,X2)
                       => r2_hidden(k4_tarski(X3,X4),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( ( v2_wellord1(X3)
            & r2_hidden(X1,k3_relat_1(X3))
            & r2_hidden(X2,k3_relat_1(X3)) )
         => ( r2_hidden(k4_tarski(X1,X2),X3)
          <=> r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t37_wellord1])).

fof(c_0_13,plain,(
    ! [X39,X40,X41] :
      ( ( ~ v6_relat_2(X39)
        | ~ r2_hidden(X40,k3_relat_1(X39))
        | ~ r2_hidden(X41,k3_relat_1(X39))
        | X40 = X41
        | r2_hidden(k4_tarski(X40,X41),X39)
        | r2_hidden(k4_tarski(X41,X40),X39)
        | ~ v1_relat_1(X39) )
      & ( r2_hidden(esk8_1(X39),k3_relat_1(X39))
        | v6_relat_2(X39)
        | ~ v1_relat_1(X39) )
      & ( r2_hidden(esk9_1(X39),k3_relat_1(X39))
        | v6_relat_2(X39)
        | ~ v1_relat_1(X39) )
      & ( esk8_1(X39) != esk9_1(X39)
        | v6_relat_2(X39)
        | ~ v1_relat_1(X39) )
      & ( ~ r2_hidden(k4_tarski(esk8_1(X39),esk9_1(X39)),X39)
        | v6_relat_2(X39)
        | ~ v1_relat_1(X39) )
      & ( ~ r2_hidden(k4_tarski(esk9_1(X39),esk8_1(X39)),X39)
        | v6_relat_2(X39)
        | ~ v1_relat_1(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l4_wellord1])])])])])])).

fof(c_0_14,negated_conjecture,
    ( v1_relat_1(esk14_0)
    & v2_wellord1(esk14_0)
    & r2_hidden(esk12_0,k3_relat_1(esk14_0))
    & r2_hidden(esk13_0,k3_relat_1(esk14_0))
    & ( ~ r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)
      | ~ r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0)) )
    & ( r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)
      | r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_15,plain,
    ( X2 = X3
    | r2_hidden(k4_tarski(X2,X3),X1)
    | r2_hidden(k4_tarski(X3,X2),X1)
    | ~ v6_relat_2(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ r2_hidden(X3,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk13_0,k3_relat_1(esk14_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( v1_relat_1(esk14_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X26] :
      ( ( v1_relat_2(X26)
        | ~ v2_wellord1(X26)
        | ~ v1_relat_1(X26) )
      & ( v8_relat_2(X26)
        | ~ v2_wellord1(X26)
        | ~ v1_relat_1(X26) )
      & ( v4_relat_2(X26)
        | ~ v2_wellord1(X26)
        | ~ v1_relat_1(X26) )
      & ( v6_relat_2(X26)
        | ~ v2_wellord1(X26)
        | ~ v1_relat_1(X26) )
      & ( v1_wellord1(X26)
        | ~ v2_wellord1(X26)
        | ~ v1_relat_1(X26) )
      & ( ~ v1_relat_2(X26)
        | ~ v8_relat_2(X26)
        | ~ v4_relat_2(X26)
        | ~ v6_relat_2(X26)
        | ~ v1_wellord1(X26)
        | v2_wellord1(X26)
        | ~ v1_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).

fof(c_0_19,plain,(
    ! [X18,X19,X20,X21,X22,X23,X24] :
      ( ( X21 != X19
        | ~ r2_hidden(X21,X20)
        | X20 != k1_wellord1(X18,X19)
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(k4_tarski(X21,X19),X18)
        | ~ r2_hidden(X21,X20)
        | X20 != k1_wellord1(X18,X19)
        | ~ v1_relat_1(X18) )
      & ( X22 = X19
        | ~ r2_hidden(k4_tarski(X22,X19),X18)
        | r2_hidden(X22,X20)
        | X20 != k1_wellord1(X18,X19)
        | ~ v1_relat_1(X18) )
      & ( ~ r2_hidden(esk2_3(X18,X23,X24),X24)
        | esk2_3(X18,X23,X24) = X23
        | ~ r2_hidden(k4_tarski(esk2_3(X18,X23,X24),X23),X18)
        | X24 = k1_wellord1(X18,X23)
        | ~ v1_relat_1(X18) )
      & ( esk2_3(X18,X23,X24) != X23
        | r2_hidden(esk2_3(X18,X23,X24),X24)
        | X24 = k1_wellord1(X18,X23)
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(k4_tarski(esk2_3(X18,X23,X24),X23),X18)
        | r2_hidden(esk2_3(X18,X23,X24),X24)
        | X24 = k1_wellord1(X18,X23)
        | ~ v1_relat_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).

cnf(c_0_20,negated_conjecture,
    ( X1 = esk13_0
    | r2_hidden(k4_tarski(esk13_0,X1),esk14_0)
    | r2_hidden(k4_tarski(X1,esk13_0),esk14_0)
    | ~ v6_relat_2(esk14_0)
    | ~ r2_hidden(X1,k3_relat_1(esk14_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

cnf(c_0_21,plain,
    ( v6_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( v2_wellord1(esk14_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( X1 = X2
    | r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_wellord1(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( X1 = esk13_0
    | r2_hidden(k4_tarski(X1,esk13_0),esk14_0)
    | r2_hidden(k4_tarski(esk13_0,X1),esk14_0)
    | ~ r2_hidden(X1,k3_relat_1(esk14_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_17])])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk12_0,k3_relat_1(esk14_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_26,plain,(
    ! [X27,X28,X29,X30] :
      ( ( ~ v8_relat_2(X27)
        | ~ r2_hidden(k4_tarski(X28,X29),X27)
        | ~ r2_hidden(k4_tarski(X29,X30),X27)
        | r2_hidden(k4_tarski(X28,X30),X27)
        | ~ v1_relat_1(X27) )
      & ( r2_hidden(k4_tarski(esk3_1(X27),esk4_1(X27)),X27)
        | v8_relat_2(X27)
        | ~ v1_relat_1(X27) )
      & ( r2_hidden(k4_tarski(esk4_1(X27),esk5_1(X27)),X27)
        | v8_relat_2(X27)
        | ~ v1_relat_1(X27) )
      & ( ~ r2_hidden(k4_tarski(esk3_1(X27),esk5_1(X27)),X27)
        | v8_relat_2(X27)
        | ~ v1_relat_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l2_wellord1])])])])])).

cnf(c_0_27,plain,
    ( X1 = X2
    | r2_hidden(X1,k1_wellord1(X3,X2))
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X1,X2),X3) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(k4_tarski(esk13_0,esk12_0),esk14_0)
    | r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_29,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_30,plain,(
    ! [X44,X45,X47,X48] :
      ( ( r2_hidden(X47,k3_relat_1(X44))
        | ~ r2_hidden(X47,esk10_2(X44,X45))
        | ~ v1_relat_1(X44) )
      & ( ~ r2_hidden(k4_tarski(X47,X45),X44)
        | ~ r2_hidden(X47,esk10_2(X44,X45))
        | ~ v1_relat_1(X44) )
      & ( ~ r2_hidden(X48,k3_relat_1(X44))
        | r2_hidden(k4_tarski(X48,X45),X44)
        | r2_hidden(X48,esk10_2(X44,X45))
        | ~ v1_relat_1(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[s1_xboole_0__e7_18__wellord1])])])])])])])).

cnf(c_0_31,plain,
    ( r2_hidden(k4_tarski(X2,X4),X1)
    | ~ v8_relat_2(X1)
    | ~ r2_hidden(k4_tarski(X2,X3),X1)
    | ~ r2_hidden(k4_tarski(X3,X4),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)
    | r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_17])])).

cnf(c_0_33,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)
    | r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_35,plain,
    ( ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,esk10_2(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))
    | r2_hidden(k4_tarski(X1,esk13_0),esk14_0)
    | ~ v8_relat_2(esk14_0)
    | ~ r2_hidden(k4_tarski(X1,esk12_0),esk14_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_17])])).

cnf(c_0_37,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | X4 != k1_wellord1(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)
    | r2_hidden(X1,k1_wellord1(esk14_0,esk13_0))
    | ~ r2_hidden(X1,k1_wellord1(esk14_0,esk12_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))
    | ~ r2_hidden(esk12_0,esk10_2(esk14_0,esk13_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_32]),c_0_17])])).

cnf(c_0_40,negated_conjecture,
    ( esk13_0 = esk12_0
    | X1 = esk13_0
    | r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))
    | r2_hidden(X1,k1_wellord1(esk14_0,esk13_0))
    | ~ v8_relat_2(esk14_0)
    | ~ r2_hidden(k4_tarski(X1,esk12_0),esk14_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_36]),c_0_17])])).

cnf(c_0_41,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k1_wellord1(X3,X2)) ),
    inference(er,[status(thm)],[c_0_37])).

fof(c_0_42,plain,(
    ! [X34,X35,X36] :
      ( ( ~ v4_relat_2(X34)
        | ~ r2_hidden(k4_tarski(X35,X36),X34)
        | ~ r2_hidden(k4_tarski(X36,X35),X34)
        | X35 = X36
        | ~ v1_relat_1(X34) )
      & ( r2_hidden(k4_tarski(esk6_1(X34),esk7_1(X34)),X34)
        | v4_relat_2(X34)
        | ~ v1_relat_1(X34) )
      & ( r2_hidden(k4_tarski(esk7_1(X34),esk6_1(X34)),X34)
        | v4_relat_2(X34)
        | ~ v1_relat_1(X34) )
      & ( esk6_1(X34) != esk7_1(X34)
        | v4_relat_2(X34)
        | ~ v1_relat_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_wellord1])])])])])).

fof(c_0_43,plain,(
    ! [X13,X14,X15] :
      ( ( r2_hidden(X13,k3_relat_1(X15))
        | ~ r2_hidden(k4_tarski(X13,X14),X15)
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(X14,k3_relat_1(X15))
        | ~ r2_hidden(k4_tarski(X13,X14),X15)
        | ~ v1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_relat_1])])])).

cnf(c_0_44,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,X3)
    | X3 != k1_wellord1(X4,X2)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_45,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(esk13_0,k1_wellord1(esk14_0,esk13_0))
    | r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)
    | ~ r2_hidden(esk12_0,esk10_2(esk14_0,esk13_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( esk13_0 = esk12_0
    | X1 = esk13_0
    | r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))
    | r2_hidden(X1,k1_wellord1(esk14_0,esk13_0))
    | ~ v8_relat_2(esk14_0)
    | ~ r2_hidden(X1,k1_wellord1(esk14_0,esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_17])])).

cnf(c_0_47,plain,
    ( v8_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_48,plain,
    ( r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X2),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k1_wellord1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_49,plain,
    ( X2 = X3
    | ~ v4_relat_2(X1)
    | ~ r2_hidden(k4_tarski(X2,X3),X1)
    | ~ r2_hidden(k4_tarski(X3,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,plain,
    ( r2_hidden(k4_tarski(X1,X3),X2)
    | r2_hidden(X1,esk10_2(X2,X3))
    | ~ r2_hidden(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_wellord1(X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_44])])).

cnf(c_0_53,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(esk13_0,k1_wellord1(esk14_0,esk13_0))
    | ~ r2_hidden(esk12_0,esk10_2(esk14_0,esk13_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_45]),c_0_17])])).

cnf(c_0_54,negated_conjecture,
    ( esk13_0 = esk12_0
    | X1 = esk13_0
    | r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))
    | r2_hidden(X1,k1_wellord1(esk14_0,esk13_0))
    | ~ r2_hidden(X1,k1_wellord1(esk14_0,esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_22]),c_0_17])])).

cnf(c_0_55,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

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
    ( X1 = k1_wellord1(esk14_0,X2)
    | r2_hidden(k4_tarski(esk2_3(esk14_0,X2,X1),X2),esk14_0)
    | r2_hidden(esk2_3(esk14_0,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_17])).

cnf(c_0_58,plain,
    ( X1 = X2
    | r2_hidden(X2,esk10_2(X3,X1))
    | ~ v4_relat_2(X3)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X1,X2),X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( esk13_0 = esk12_0
    | ~ r2_hidden(esk12_0,esk10_2(esk14_0,esk13_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_17])])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_61,negated_conjecture,
    ( esk1_2(k1_wellord1(esk14_0,esk12_0),X1) = esk13_0
    | esk13_0 = esk12_0
    | r2_hidden(esk1_2(k1_wellord1(esk14_0,esk12_0),X1),k1_wellord1(esk14_0,esk13_0))
    | r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))
    | r1_tarski(k1_wellord1(esk14_0,esk12_0),X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

fof(c_0_62,plain,(
    ! [X16,X17] :
      ( ~ r2_hidden(X16,X17)
      | ~ r1_tarski(X17,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X3,k1_wellord1(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_41])).

cnf(c_0_65,negated_conjecture,
    ( X1 = k1_wellord1(esk14_0,X2)
    | r2_hidden(esk2_3(esk14_0,X2,X1),X1)
    | r2_hidden(X2,k3_relat_1(esk14_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_57]),c_0_17])])).

cnf(c_0_66,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)
    | ~ v4_relat_2(esk14_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_28]),c_0_17])]),c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( esk1_2(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0)) = esk13_0
    | esk13_0 = esk12_0
    | r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))
    | r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_68,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_63])).

cnf(c_0_70,negated_conjecture,
    ( k1_wellord1(X1,X2) = k1_wellord1(esk14_0,X3)
    | r2_hidden(X3,k3_relat_1(esk14_0))
    | r2_hidden(X2,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( esk13_0 = esk12_0
    | ~ v4_relat_2(esk14_0)
    | ~ r2_hidden(k4_tarski(esk13_0,esk12_0),esk14_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_66]),c_0_17])])).

cnf(c_0_72,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)
    | ~ r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_73,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))
    | r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_67])).

cnf(c_0_74,plain,
    ( ~ r2_hidden(X1,X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_75,negated_conjecture,
    ( k1_wellord1(esk14_0,X1) = k1_wellord1(esk14_0,X2)
    | r2_hidden(X1,k3_relat_1(esk14_0))
    | r2_hidden(X2,k3_relat_1(esk14_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_17])).

cnf(c_0_76,negated_conjecture,
    ( esk13_0 = esk12_0
    | ~ v4_relat_2(esk14_0)
    | ~ r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_41]),c_0_17])])).

cnf(c_0_77,negated_conjecture,
    ( esk13_0 = esk12_0
    | r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_32])).

cnf(c_0_78,negated_conjecture,
    ( k1_wellord1(esk14_0,X1) = k1_wellord1(esk14_0,k3_relat_1(esk14_0))
    | r2_hidden(X1,k3_relat_1(esk14_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

fof(c_0_79,plain,(
    ! [X49,X50,X52] :
      ( ( r2_hidden(esk11_2(X49,X50),X50)
        | ~ r1_tarski(X50,k3_relat_1(X49))
        | X50 = k1_xboole_0
        | ~ v2_wellord1(X49)
        | ~ v1_relat_1(X49) )
      & ( ~ r2_hidden(X52,X50)
        | r2_hidden(k4_tarski(esk11_2(X49,X50),X52),X49)
        | ~ r1_tarski(X50,k3_relat_1(X49))
        | X50 = k1_xboole_0
        | ~ v2_wellord1(X49)
        | ~ v1_relat_1(X49) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_wellord1])])])])])).

cnf(c_0_80,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | r1_tarski(k1_wellord1(X2,X1),X3)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_64,c_0_55])).

cnf(c_0_81,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(X1,esk10_2(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_82,negated_conjecture,
    ( esk13_0 = esk12_0
    | ~ v4_relat_2(esk14_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_83,plain,
    ( v4_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(X1,k3_relat_1(esk14_0))
    | ~ r2_hidden(X2,k1_wellord1(esk14_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_78]),c_0_17])]),c_0_74])).

cnf(c_0_85,plain,
    ( r2_hidden(esk11_2(X1,X2),X2)
    | X2 = k1_xboole_0
    | ~ r1_tarski(X2,k3_relat_1(X1))
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(X1,k3_relat_1(esk14_0))
    | r1_tarski(k1_wellord1(esk14_0,X1),X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_78]),c_0_17])]),c_0_74])).

cnf(c_0_87,plain,
    ( r2_hidden(k4_tarski(esk11_2(X3,X2),X1),X3)
    | X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,k3_relat_1(X3))
    | ~ v2_wellord1(X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_88,plain,
    ( r2_hidden(esk1_2(esk10_2(X1,X2),X3),k3_relat_1(X1))
    | r1_tarski(esk10_2(X1,X2),X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_81,c_0_55])).

cnf(c_0_89,negated_conjecture,
    ( esk13_0 = esk12_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_22]),c_0_17])])).

cnf(c_0_90,negated_conjecture,
    ( k1_wellord1(esk14_0,X1) = k1_xboole_0
    | r2_hidden(X1,k3_relat_1(esk14_0))
    | ~ v2_wellord1(X2)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86])).

cnf(c_0_91,plain,
    ( X1 = k1_xboole_0
    | ~ v2_wellord1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(esk11_2(X2,X1),esk10_2(X2,X3))
    | ~ r2_hidden(X3,X1)
    | ~ r1_tarski(X1,k3_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_87])).

cnf(c_0_92,plain,
    ( r1_tarski(esk10_2(X1,X2),k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_88])).

cnf(c_0_93,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_89]),c_0_89]),c_0_69])])).

cnf(c_0_94,negated_conjecture,
    ( k1_wellord1(esk14_0,X1) = k1_xboole_0
    | r2_hidden(X1,k3_relat_1(esk14_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_22]),c_0_17])])).

cnf(c_0_95,plain,
    ( esk10_2(X1,X2) = k1_xboole_0
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,esk10_2(X1,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_85]),c_0_92])).

cnf(c_0_96,negated_conjecture,
    ( r2_hidden(esk12_0,esk10_2(esk14_0,esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_50]),c_0_17]),c_0_25])])).

cnf(c_0_97,negated_conjecture,
    ( k1_wellord1(esk14_0,k3_relat_1(esk14_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_74,c_0_94])).

cnf(c_0_98,negated_conjecture,
    ( esk10_2(esk14_0,esk12_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_22]),c_0_17])])).

cnf(c_0_99,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_97]),c_0_17])]),c_0_74])).

cnf(c_0_100,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_98]),c_0_99]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:42:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.47/0.69  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.47/0.69  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.47/0.69  #
% 0.47/0.69  # Preprocessing time       : 0.029 s
% 0.47/0.69  
% 0.47/0.69  # Proof found!
% 0.47/0.69  # SZS status Theorem
% 0.47/0.69  # SZS output start CNFRefutation
% 0.47/0.69  fof(t37_wellord1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(((v2_wellord1(X3)&r2_hidden(X1,k3_relat_1(X3)))&r2_hidden(X2,k3_relat_1(X3)))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_wellord1)).
% 0.47/0.69  fof(l4_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v6_relat_2(X1)<=>![X2, X3]:~(((((r2_hidden(X2,k3_relat_1(X1))&r2_hidden(X3,k3_relat_1(X1)))&X2!=X3)&~(r2_hidden(k4_tarski(X2,X3),X1)))&~(r2_hidden(k4_tarski(X3,X2),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l4_wellord1)).
% 0.47/0.69  fof(d4_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v2_wellord1(X1)<=>((((v1_relat_2(X1)&v8_relat_2(X1))&v4_relat_2(X1))&v6_relat_2(X1))&v1_wellord1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_wellord1)).
% 0.47/0.69  fof(d1_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k1_wellord1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4!=X2&r2_hidden(k4_tarski(X4,X2),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord1)).
% 0.47/0.69  fof(l2_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v8_relat_2(X1)<=>![X2, X3, X4]:((r2_hidden(k4_tarski(X2,X3),X1)&r2_hidden(k4_tarski(X3,X4),X1))=>r2_hidden(k4_tarski(X2,X4),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l2_wellord1)).
% 0.47/0.69  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.47/0.69  fof(s1_xboole_0__e7_18__wellord1, axiom, ![X1, X2]:(v1_relat_1(X1)=>?[X3]:![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,k3_relat_1(X1))&~(r2_hidden(k4_tarski(X4,X2),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s1_xboole_0__e7_18__wellord1)).
% 0.47/0.69  fof(l3_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v4_relat_2(X1)<=>![X2, X3]:((r2_hidden(k4_tarski(X2,X3),X1)&r2_hidden(k4_tarski(X3,X2),X1))=>X2=X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_wellord1)).
% 0.47/0.69  fof(t30_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k3_relat_1(X3))&r2_hidden(X2,k3_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relat_1)).
% 0.47/0.69  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.47/0.69  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.47/0.69  fof(t10_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v2_wellord1(X1)=>![X2]:~(((r1_tarski(X2,k3_relat_1(X1))&X2!=k1_xboole_0)&![X3]:~((r2_hidden(X3,X2)&![X4]:(r2_hidden(X4,X2)=>r2_hidden(k4_tarski(X3,X4),X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_wellord1)).
% 0.47/0.69  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(((v2_wellord1(X3)&r2_hidden(X1,k3_relat_1(X3)))&r2_hidden(X2,k3_relat_1(X3)))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2)))))), inference(assume_negation,[status(cth)],[t37_wellord1])).
% 0.47/0.69  fof(c_0_13, plain, ![X39, X40, X41]:((~v6_relat_2(X39)|(~r2_hidden(X40,k3_relat_1(X39))|~r2_hidden(X41,k3_relat_1(X39))|X40=X41|r2_hidden(k4_tarski(X40,X41),X39)|r2_hidden(k4_tarski(X41,X40),X39))|~v1_relat_1(X39))&(((((r2_hidden(esk8_1(X39),k3_relat_1(X39))|v6_relat_2(X39)|~v1_relat_1(X39))&(r2_hidden(esk9_1(X39),k3_relat_1(X39))|v6_relat_2(X39)|~v1_relat_1(X39)))&(esk8_1(X39)!=esk9_1(X39)|v6_relat_2(X39)|~v1_relat_1(X39)))&(~r2_hidden(k4_tarski(esk8_1(X39),esk9_1(X39)),X39)|v6_relat_2(X39)|~v1_relat_1(X39)))&(~r2_hidden(k4_tarski(esk9_1(X39),esk8_1(X39)),X39)|v6_relat_2(X39)|~v1_relat_1(X39)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l4_wellord1])])])])])])).
% 0.47/0.69  fof(c_0_14, negated_conjecture, (v1_relat_1(esk14_0)&(((v2_wellord1(esk14_0)&r2_hidden(esk12_0,k3_relat_1(esk14_0)))&r2_hidden(esk13_0,k3_relat_1(esk14_0)))&((~r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)|~r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0)))&(r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)|r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.47/0.69  cnf(c_0_15, plain, (X2=X3|r2_hidden(k4_tarski(X2,X3),X1)|r2_hidden(k4_tarski(X3,X2),X1)|~v6_relat_2(X1)|~r2_hidden(X2,k3_relat_1(X1))|~r2_hidden(X3,k3_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.47/0.69  cnf(c_0_16, negated_conjecture, (r2_hidden(esk13_0,k3_relat_1(esk14_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.47/0.69  cnf(c_0_17, negated_conjecture, (v1_relat_1(esk14_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.47/0.69  fof(c_0_18, plain, ![X26]:((((((v1_relat_2(X26)|~v2_wellord1(X26)|~v1_relat_1(X26))&(v8_relat_2(X26)|~v2_wellord1(X26)|~v1_relat_1(X26)))&(v4_relat_2(X26)|~v2_wellord1(X26)|~v1_relat_1(X26)))&(v6_relat_2(X26)|~v2_wellord1(X26)|~v1_relat_1(X26)))&(v1_wellord1(X26)|~v2_wellord1(X26)|~v1_relat_1(X26)))&(~v1_relat_2(X26)|~v8_relat_2(X26)|~v4_relat_2(X26)|~v6_relat_2(X26)|~v1_wellord1(X26)|v2_wellord1(X26)|~v1_relat_1(X26))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).
% 0.47/0.69  fof(c_0_19, plain, ![X18, X19, X20, X21, X22, X23, X24]:((((X21!=X19|~r2_hidden(X21,X20)|X20!=k1_wellord1(X18,X19)|~v1_relat_1(X18))&(r2_hidden(k4_tarski(X21,X19),X18)|~r2_hidden(X21,X20)|X20!=k1_wellord1(X18,X19)|~v1_relat_1(X18)))&(X22=X19|~r2_hidden(k4_tarski(X22,X19),X18)|r2_hidden(X22,X20)|X20!=k1_wellord1(X18,X19)|~v1_relat_1(X18)))&((~r2_hidden(esk2_3(X18,X23,X24),X24)|(esk2_3(X18,X23,X24)=X23|~r2_hidden(k4_tarski(esk2_3(X18,X23,X24),X23),X18))|X24=k1_wellord1(X18,X23)|~v1_relat_1(X18))&((esk2_3(X18,X23,X24)!=X23|r2_hidden(esk2_3(X18,X23,X24),X24)|X24=k1_wellord1(X18,X23)|~v1_relat_1(X18))&(r2_hidden(k4_tarski(esk2_3(X18,X23,X24),X23),X18)|r2_hidden(esk2_3(X18,X23,X24),X24)|X24=k1_wellord1(X18,X23)|~v1_relat_1(X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).
% 0.47/0.69  cnf(c_0_20, negated_conjecture, (X1=esk13_0|r2_hidden(k4_tarski(esk13_0,X1),esk14_0)|r2_hidden(k4_tarski(X1,esk13_0),esk14_0)|~v6_relat_2(esk14_0)|~r2_hidden(X1,k3_relat_1(esk14_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])])).
% 0.47/0.69  cnf(c_0_21, plain, (v6_relat_2(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.47/0.69  cnf(c_0_22, negated_conjecture, (v2_wellord1(esk14_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.47/0.69  cnf(c_0_23, plain, (X1=X2|r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_wellord1(X3,X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.47/0.69  cnf(c_0_24, negated_conjecture, (X1=esk13_0|r2_hidden(k4_tarski(X1,esk13_0),esk14_0)|r2_hidden(k4_tarski(esk13_0,X1),esk14_0)|~r2_hidden(X1,k3_relat_1(esk14_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_17])])).
% 0.47/0.69  cnf(c_0_25, negated_conjecture, (r2_hidden(esk12_0,k3_relat_1(esk14_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.47/0.69  fof(c_0_26, plain, ![X27, X28, X29, X30]:((~v8_relat_2(X27)|(~r2_hidden(k4_tarski(X28,X29),X27)|~r2_hidden(k4_tarski(X29,X30),X27)|r2_hidden(k4_tarski(X28,X30),X27))|~v1_relat_1(X27))&(((r2_hidden(k4_tarski(esk3_1(X27),esk4_1(X27)),X27)|v8_relat_2(X27)|~v1_relat_1(X27))&(r2_hidden(k4_tarski(esk4_1(X27),esk5_1(X27)),X27)|v8_relat_2(X27)|~v1_relat_1(X27)))&(~r2_hidden(k4_tarski(esk3_1(X27),esk5_1(X27)),X27)|v8_relat_2(X27)|~v1_relat_1(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l2_wellord1])])])])])).
% 0.47/0.69  cnf(c_0_27, plain, (X1=X2|r2_hidden(X1,k1_wellord1(X3,X2))|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X1,X2),X3)), inference(er,[status(thm)],[c_0_23])).
% 0.47/0.69  cnf(c_0_28, negated_conjecture, (esk13_0=esk12_0|r2_hidden(k4_tarski(esk13_0,esk12_0),esk14_0)|r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.47/0.69  fof(c_0_29, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.47/0.69  fof(c_0_30, plain, ![X44, X45, X47, X48]:(((r2_hidden(X47,k3_relat_1(X44))|~r2_hidden(X47,esk10_2(X44,X45))|~v1_relat_1(X44))&(~r2_hidden(k4_tarski(X47,X45),X44)|~r2_hidden(X47,esk10_2(X44,X45))|~v1_relat_1(X44)))&(~r2_hidden(X48,k3_relat_1(X44))|r2_hidden(k4_tarski(X48,X45),X44)|r2_hidden(X48,esk10_2(X44,X45))|~v1_relat_1(X44))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[s1_xboole_0__e7_18__wellord1])])])])])])])).
% 0.47/0.69  cnf(c_0_31, plain, (r2_hidden(k4_tarski(X2,X4),X1)|~v8_relat_2(X1)|~r2_hidden(k4_tarski(X2,X3),X1)|~r2_hidden(k4_tarski(X3,X4),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.47/0.69  cnf(c_0_32, negated_conjecture, (esk13_0=esk12_0|r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)|r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_17])])).
% 0.47/0.69  cnf(c_0_33, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.47/0.69  cnf(c_0_34, negated_conjecture, (r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)|r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.47/0.69  cnf(c_0_35, plain, (~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,esk10_2(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.47/0.69  cnf(c_0_36, negated_conjecture, (esk13_0=esk12_0|r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))|r2_hidden(k4_tarski(X1,esk13_0),esk14_0)|~v8_relat_2(esk14_0)|~r2_hidden(k4_tarski(X1,esk12_0),esk14_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_17])])).
% 0.47/0.69  cnf(c_0_37, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,X4)|X4!=k1_wellord1(X3,X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.47/0.69  cnf(c_0_38, negated_conjecture, (r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)|r2_hidden(X1,k1_wellord1(esk14_0,esk13_0))|~r2_hidden(X1,k1_wellord1(esk14_0,esk12_0))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.47/0.69  cnf(c_0_39, negated_conjecture, (esk13_0=esk12_0|r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))|~r2_hidden(esk12_0,esk10_2(esk14_0,esk13_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_32]), c_0_17])])).
% 0.47/0.69  cnf(c_0_40, negated_conjecture, (esk13_0=esk12_0|X1=esk13_0|r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))|r2_hidden(X1,k1_wellord1(esk14_0,esk13_0))|~v8_relat_2(esk14_0)|~r2_hidden(k4_tarski(X1,esk12_0),esk14_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_36]), c_0_17])])).
% 0.47/0.69  cnf(c_0_41, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)|~r2_hidden(X1,k1_wellord1(X3,X2))), inference(er,[status(thm)],[c_0_37])).
% 0.47/0.69  fof(c_0_42, plain, ![X34, X35, X36]:((~v4_relat_2(X34)|(~r2_hidden(k4_tarski(X35,X36),X34)|~r2_hidden(k4_tarski(X36,X35),X34)|X35=X36)|~v1_relat_1(X34))&(((r2_hidden(k4_tarski(esk6_1(X34),esk7_1(X34)),X34)|v4_relat_2(X34)|~v1_relat_1(X34))&(r2_hidden(k4_tarski(esk7_1(X34),esk6_1(X34)),X34)|v4_relat_2(X34)|~v1_relat_1(X34)))&(esk6_1(X34)!=esk7_1(X34)|v4_relat_2(X34)|~v1_relat_1(X34)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_wellord1])])])])])).
% 0.47/0.69  fof(c_0_43, plain, ![X13, X14, X15]:((r2_hidden(X13,k3_relat_1(X15))|~r2_hidden(k4_tarski(X13,X14),X15)|~v1_relat_1(X15))&(r2_hidden(X14,k3_relat_1(X15))|~r2_hidden(k4_tarski(X13,X14),X15)|~v1_relat_1(X15))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_relat_1])])])).
% 0.47/0.69  cnf(c_0_44, plain, (X1!=X2|~r2_hidden(X1,X3)|X3!=k1_wellord1(X4,X2)|~v1_relat_1(X4)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.47/0.69  cnf(c_0_45, negated_conjecture, (esk13_0=esk12_0|r2_hidden(esk13_0,k1_wellord1(esk14_0,esk13_0))|r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)|~r2_hidden(esk12_0,esk10_2(esk14_0,esk13_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.47/0.69  cnf(c_0_46, negated_conjecture, (esk13_0=esk12_0|X1=esk13_0|r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))|r2_hidden(X1,k1_wellord1(esk14_0,esk13_0))|~v8_relat_2(esk14_0)|~r2_hidden(X1,k1_wellord1(esk14_0,esk12_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_17])])).
% 0.47/0.69  cnf(c_0_47, plain, (v8_relat_2(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.47/0.69  cnf(c_0_48, plain, (r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X2),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k1_wellord1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.47/0.69  cnf(c_0_49, plain, (X2=X3|~v4_relat_2(X1)|~r2_hidden(k4_tarski(X2,X3),X1)|~r2_hidden(k4_tarski(X3,X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.47/0.69  cnf(c_0_50, plain, (r2_hidden(k4_tarski(X1,X3),X2)|r2_hidden(X1,esk10_2(X2,X3))|~r2_hidden(X1,k3_relat_1(X2))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.47/0.69  cnf(c_0_51, plain, (r2_hidden(X1,k3_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.47/0.69  cnf(c_0_52, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k1_wellord1(X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_44])])).
% 0.47/0.69  cnf(c_0_53, negated_conjecture, (esk13_0=esk12_0|r2_hidden(esk13_0,k1_wellord1(esk14_0,esk13_0))|~r2_hidden(esk12_0,esk10_2(esk14_0,esk13_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_45]), c_0_17])])).
% 0.47/0.69  cnf(c_0_54, negated_conjecture, (esk13_0=esk12_0|X1=esk13_0|r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))|r2_hidden(X1,k1_wellord1(esk14_0,esk13_0))|~r2_hidden(X1,k1_wellord1(esk14_0,esk12_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_22]), c_0_17])])).
% 0.47/0.69  cnf(c_0_55, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.47/0.69  fof(c_0_56, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.47/0.69  cnf(c_0_57, negated_conjecture, (X1=k1_wellord1(esk14_0,X2)|r2_hidden(k4_tarski(esk2_3(esk14_0,X2,X1),X2),esk14_0)|r2_hidden(esk2_3(esk14_0,X2,X1),X1)), inference(spm,[status(thm)],[c_0_48, c_0_17])).
% 0.47/0.69  cnf(c_0_58, plain, (X1=X2|r2_hidden(X2,esk10_2(X3,X1))|~v4_relat_2(X3)|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X1,X2),X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])).
% 0.47/0.69  cnf(c_0_59, negated_conjecture, (esk13_0=esk12_0|~r2_hidden(esk12_0,esk10_2(esk14_0,esk13_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_17])])).
% 0.47/0.69  cnf(c_0_60, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.47/0.69  cnf(c_0_61, negated_conjecture, (esk1_2(k1_wellord1(esk14_0,esk12_0),X1)=esk13_0|esk13_0=esk12_0|r2_hidden(esk1_2(k1_wellord1(esk14_0,esk12_0),X1),k1_wellord1(esk14_0,esk13_0))|r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))|r1_tarski(k1_wellord1(esk14_0,esk12_0),X1)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.47/0.69  fof(c_0_62, plain, ![X16, X17]:(~r2_hidden(X16,X17)|~r1_tarski(X17,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.47/0.69  cnf(c_0_63, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.47/0.69  cnf(c_0_64, plain, (r2_hidden(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r2_hidden(X3,k1_wellord1(X2,X1))), inference(spm,[status(thm)],[c_0_51, c_0_41])).
% 0.47/0.69  cnf(c_0_65, negated_conjecture, (X1=k1_wellord1(esk14_0,X2)|r2_hidden(esk2_3(esk14_0,X2,X1),X1)|r2_hidden(X2,k3_relat_1(esk14_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_57]), c_0_17])])).
% 0.47/0.69  cnf(c_0_66, negated_conjecture, (esk13_0=esk12_0|r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)|~v4_relat_2(esk14_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_28]), c_0_17])]), c_0_59])).
% 0.47/0.69  cnf(c_0_67, negated_conjecture, (esk1_2(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0))=esk13_0|esk13_0=esk12_0|r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))|r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.47/0.69  cnf(c_0_68, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.47/0.69  cnf(c_0_69, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_63])).
% 0.47/0.69  cnf(c_0_70, negated_conjecture, (k1_wellord1(X1,X2)=k1_wellord1(esk14_0,X3)|r2_hidden(X3,k3_relat_1(esk14_0))|r2_hidden(X2,k3_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.47/0.69  cnf(c_0_71, negated_conjecture, (esk13_0=esk12_0|~v4_relat_2(esk14_0)|~r2_hidden(k4_tarski(esk13_0,esk12_0),esk14_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_66]), c_0_17])])).
% 0.47/0.69  cnf(c_0_72, negated_conjecture, (~r2_hidden(k4_tarski(esk12_0,esk13_0),esk14_0)|~r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.47/0.69  cnf(c_0_73, negated_conjecture, (esk13_0=esk12_0|r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))|r1_tarski(k1_wellord1(esk14_0,esk12_0),k1_wellord1(esk14_0,esk13_0))), inference(spm,[status(thm)],[c_0_55, c_0_67])).
% 0.47/0.69  cnf(c_0_74, plain, (~r2_hidden(X1,X1)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.47/0.69  cnf(c_0_75, negated_conjecture, (k1_wellord1(esk14_0,X1)=k1_wellord1(esk14_0,X2)|r2_hidden(X1,k3_relat_1(esk14_0))|r2_hidden(X2,k3_relat_1(esk14_0))), inference(spm,[status(thm)],[c_0_70, c_0_17])).
% 0.47/0.69  cnf(c_0_76, negated_conjecture, (esk13_0=esk12_0|~v4_relat_2(esk14_0)|~r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_41]), c_0_17])])).
% 0.47/0.69  cnf(c_0_77, negated_conjecture, (esk13_0=esk12_0|r2_hidden(esk13_0,k1_wellord1(esk14_0,esk12_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_32])).
% 0.47/0.69  cnf(c_0_78, negated_conjecture, (k1_wellord1(esk14_0,X1)=k1_wellord1(esk14_0,k3_relat_1(esk14_0))|r2_hidden(X1,k3_relat_1(esk14_0))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.47/0.69  fof(c_0_79, plain, ![X49, X50, X52]:((r2_hidden(esk11_2(X49,X50),X50)|(~r1_tarski(X50,k3_relat_1(X49))|X50=k1_xboole_0)|~v2_wellord1(X49)|~v1_relat_1(X49))&(~r2_hidden(X52,X50)|r2_hidden(k4_tarski(esk11_2(X49,X50),X52),X49)|(~r1_tarski(X50,k3_relat_1(X49))|X50=k1_xboole_0)|~v2_wellord1(X49)|~v1_relat_1(X49))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_wellord1])])])])])).
% 0.47/0.69  cnf(c_0_80, plain, (r2_hidden(X1,k3_relat_1(X2))|r1_tarski(k1_wellord1(X2,X1),X3)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_64, c_0_55])).
% 0.47/0.69  cnf(c_0_81, plain, (r2_hidden(X1,k3_relat_1(X2))|~r2_hidden(X1,esk10_2(X2,X3))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.47/0.69  cnf(c_0_82, negated_conjecture, (esk13_0=esk12_0|~v4_relat_2(esk14_0)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.47/0.69  cnf(c_0_83, plain, (v4_relat_2(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.47/0.69  cnf(c_0_84, negated_conjecture, (r2_hidden(X1,k3_relat_1(esk14_0))|~r2_hidden(X2,k1_wellord1(esk14_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_78]), c_0_17])]), c_0_74])).
% 0.47/0.69  cnf(c_0_85, plain, (r2_hidden(esk11_2(X1,X2),X2)|X2=k1_xboole_0|~r1_tarski(X2,k3_relat_1(X1))|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.47/0.69  cnf(c_0_86, negated_conjecture, (r2_hidden(X1,k3_relat_1(esk14_0))|r1_tarski(k1_wellord1(esk14_0,X1),X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_78]), c_0_17])]), c_0_74])).
% 0.47/0.69  cnf(c_0_87, plain, (r2_hidden(k4_tarski(esk11_2(X3,X2),X1),X3)|X2=k1_xboole_0|~r2_hidden(X1,X2)|~r1_tarski(X2,k3_relat_1(X3))|~v2_wellord1(X3)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.47/0.69  cnf(c_0_88, plain, (r2_hidden(esk1_2(esk10_2(X1,X2),X3),k3_relat_1(X1))|r1_tarski(esk10_2(X1,X2),X3)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_81, c_0_55])).
% 0.47/0.69  cnf(c_0_89, negated_conjecture, (esk13_0=esk12_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_22]), c_0_17])])).
% 0.47/0.69  cnf(c_0_90, negated_conjecture, (k1_wellord1(esk14_0,X1)=k1_xboole_0|r2_hidden(X1,k3_relat_1(esk14_0))|~v2_wellord1(X2)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_86])).
% 0.47/0.69  cnf(c_0_91, plain, (X1=k1_xboole_0|~v2_wellord1(X2)|~v1_relat_1(X2)|~r2_hidden(esk11_2(X2,X1),esk10_2(X2,X3))|~r2_hidden(X3,X1)|~r1_tarski(X1,k3_relat_1(X2))), inference(spm,[status(thm)],[c_0_35, c_0_87])).
% 0.47/0.69  cnf(c_0_92, plain, (r1_tarski(esk10_2(X1,X2),k3_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_60, c_0_88])).
% 0.47/0.69  cnf(c_0_93, negated_conjecture, (~r2_hidden(k4_tarski(esk12_0,esk12_0),esk14_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_89]), c_0_89]), c_0_69])])).
% 0.47/0.69  cnf(c_0_94, negated_conjecture, (k1_wellord1(esk14_0,X1)=k1_xboole_0|r2_hidden(X1,k3_relat_1(esk14_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_22]), c_0_17])])).
% 0.47/0.69  cnf(c_0_95, plain, (esk10_2(X1,X2)=k1_xboole_0|~v2_wellord1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,esk10_2(X1,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_85]), c_0_92])).
% 0.47/0.69  cnf(c_0_96, negated_conjecture, (r2_hidden(esk12_0,esk10_2(esk14_0,esk12_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_50]), c_0_17]), c_0_25])])).
% 0.47/0.69  cnf(c_0_97, negated_conjecture, (k1_wellord1(esk14_0,k3_relat_1(esk14_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_74, c_0_94])).
% 0.47/0.69  cnf(c_0_98, negated_conjecture, (esk10_2(esk14_0,esk12_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_22]), c_0_17])])).
% 0.47/0.69  cnf(c_0_99, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_97]), c_0_17])]), c_0_74])).
% 0.47/0.69  cnf(c_0_100, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_98]), c_0_99]), ['proof']).
% 0.47/0.69  # SZS output end CNFRefutation
% 0.47/0.69  # Proof object total steps             : 101
% 0.47/0.69  # Proof object clause steps            : 76
% 0.47/0.69  # Proof object formula steps           : 25
% 0.47/0.69  # Proof object conjectures             : 46
% 0.47/0.69  # Proof object clause conjectures      : 43
% 0.47/0.69  # Proof object formula conjectures     : 3
% 0.47/0.69  # Proof object initial clauses used    : 27
% 0.47/0.69  # Proof object initial formulas used   : 12
% 0.47/0.69  # Proof object generating inferences   : 43
% 0.47/0.69  # Proof object simplifying inferences  : 66
% 0.47/0.69  # Training examples: 0 positive, 0 negative
% 0.47/0.69  # Parsed axioms                        : 12
% 0.47/0.69  # Removed by relevancy pruning/SinE    : 0
% 0.47/0.69  # Initial clauses                      : 46
% 0.47/0.69  # Removed in clause preprocessing      : 0
% 0.47/0.69  # Initial clauses in saturation        : 46
% 0.47/0.69  # Processed clauses                    : 2520
% 0.47/0.69  # ...of these trivial                  : 13
% 0.47/0.69  # ...subsumed                          : 1503
% 0.47/0.69  # ...remaining for further processing  : 1004
% 0.47/0.69  # Other redundant clauses eliminated   : 6
% 0.47/0.69  # Clauses deleted for lack of memory   : 0
% 0.47/0.69  # Backward-subsumed                    : 310
% 0.47/0.69  # Backward-rewritten                   : 369
% 0.47/0.69  # Generated clauses                    : 12708
% 0.47/0.69  # ...of the previous two non-trivial   : 10774
% 0.47/0.69  # Contextual simplify-reflections      : 32
% 0.47/0.69  # Paramodulations                      : 12697
% 0.47/0.69  # Factorizations                       : 6
% 0.47/0.69  # Equation resolutions                 : 6
% 0.47/0.69  # Propositional unsat checks           : 0
% 0.47/0.69  #    Propositional check models        : 0
% 0.47/0.69  #    Propositional check unsatisfiable : 0
% 0.47/0.69  #    Propositional clauses             : 0
% 0.47/0.69  #    Propositional clauses after purity: 0
% 0.47/0.69  #    Propositional unsat core size     : 0
% 0.47/0.69  #    Propositional preprocessing time  : 0.000
% 0.47/0.69  #    Propositional encoding time       : 0.000
% 0.47/0.69  #    Propositional solver time         : 0.000
% 0.47/0.69  #    Success case prop preproc time    : 0.000
% 0.47/0.69  #    Success case prop encoding time   : 0.000
% 0.47/0.69  #    Success case prop solver time     : 0.000
% 0.47/0.69  # Current number of processed clauses  : 320
% 0.47/0.69  #    Positive orientable unit clauses  : 8
% 0.47/0.69  #    Positive unorientable unit clauses: 0
% 0.47/0.69  #    Negative unit clauses             : 5
% 0.47/0.69  #    Non-unit-clauses                  : 307
% 0.47/0.69  # Current number of unprocessed clauses: 8024
% 0.47/0.69  # ...number of literals in the above   : 55531
% 0.47/0.69  # Current number of archived formulas  : 0
% 0.47/0.69  # Current number of archived clauses   : 679
% 0.47/0.69  # Clause-clause subsumption calls (NU) : 74350
% 0.47/0.69  # Rec. Clause-clause subsumption calls : 8311
% 0.47/0.69  # Non-unit clause-clause subsumptions  : 1714
% 0.47/0.69  # Unit Clause-clause subsumption calls : 1578
% 0.47/0.69  # Rewrite failures with RHS unbound    : 0
% 0.47/0.69  # BW rewrite match attempts            : 10
% 0.47/0.69  # BW rewrite match successes           : 4
% 0.47/0.69  # Condensation attempts                : 0
% 0.47/0.69  # Condensation successes               : 0
% 0.47/0.69  # Termbank termtop insertions          : 320511
% 0.47/0.69  
% 0.47/0.69  # -------------------------------------------------
% 0.47/0.69  # User time                : 0.346 s
% 0.47/0.69  # System time              : 0.012 s
% 0.47/0.69  # Total time               : 0.358 s
% 0.47/0.69  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
