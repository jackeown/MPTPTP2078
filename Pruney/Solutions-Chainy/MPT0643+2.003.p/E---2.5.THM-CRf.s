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
% DateTime   : Thu Dec  3 10:53:41 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 192 expanded)
%              Number of clauses        :   34 (  66 expanded)
%              Number of leaves         :    7 (  45 expanded)
%              Depth                    :    9
%              Number of atoms          :  223 (1394 expanded)
%              Number of equality atoms :   65 ( 541 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   23 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

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

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_7,plain,(
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

fof(c_0_8,negated_conjecture,(
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

fof(c_0_9,plain,(
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
      & ( r2_hidden(esk10_2(X41,X42),X41)
        | k1_relat_1(X42) != X41
        | X42 = k6_relat_1(X41)
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) )
      & ( k1_funct_1(X42,esk10_2(X41,X42)) != esk10_2(X41,X42)
        | k1_relat_1(X42) != X41
        | X42 = k6_relat_1(X41)
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_funct_1])])])])])).

cnf(c_0_10,plain,
    ( r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,negated_conjecture,
    ( v1_relat_1(esk12_0)
    & v1_funct_1(esk12_0)
    & v1_relat_1(esk13_0)
    & v1_funct_1(esk13_0)
    & k1_relat_1(esk12_0) = esk11_0
    & k1_relat_1(esk13_0) = esk11_0
    & r1_tarski(k2_relat_1(esk13_0),esk11_0)
    & v2_funct_1(esk12_0)
    & k5_relat_1(esk13_0,esk12_0) = esk12_0
    & esk13_0 != k6_relat_1(esk11_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_12,plain,
    ( r2_hidden(esk10_2(X1,X2),X1)
    | X2 = k6_relat_1(X1)
    | k1_relat_1(X2) != X1
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X22,X23,X24,X26,X27,X28,X29,X31] :
      ( ( ~ r2_hidden(X24,X23)
        | r2_hidden(k4_tarski(esk5_3(X22,X23,X24),X24),X22)
        | X23 != k2_relat_1(X22) )
      & ( ~ r2_hidden(k4_tarski(X27,X26),X22)
        | r2_hidden(X26,X23)
        | X23 != k2_relat_1(X22) )
      & ( ~ r2_hidden(esk6_2(X28,X29),X29)
        | ~ r2_hidden(k4_tarski(X31,esk6_2(X28,X29)),X28)
        | X29 = k2_relat_1(X28) )
      & ( r2_hidden(esk6_2(X28,X29),X29)
        | r2_hidden(k4_tarski(esk7_2(X28,X29),esk6_2(X28,X29)),X28)
        | X29 = k2_relat_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( k1_relat_1(esk13_0) = esk11_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( v1_funct_1(esk13_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( v1_relat_1(esk13_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k6_relat_1(k1_relat_1(X1)) = X1
    | r2_hidden(esk10_2(k1_relat_1(X1),X1),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( esk13_0 != k6_relat_1(esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_20,plain,(
    ! [X38,X39,X40] :
      ( ~ v1_relat_1(X39)
      | ~ v1_funct_1(X39)
      | ~ v1_relat_1(X40)
      | ~ v1_funct_1(X40)
      | ~ r2_hidden(X38,k1_relat_1(X39))
      | k1_funct_1(k5_relat_1(X39,X40),X38) = k1_funct_1(X40,k1_funct_1(X39,X38)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_1])])])).

cnf(c_0_21,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(esk13_0,X1)),esk13_0)
    | ~ r2_hidden(X1,esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17])])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk10_2(esk11_0,esk13_0),esk11_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_16]),c_0_15]),c_0_15]),c_0_15]),c_0_17])]),c_0_19])).

fof(c_0_24,plain,(
    ! [X33,X34,X35] :
      ( ( ~ v2_funct_1(X33)
        | ~ r2_hidden(X34,k1_relat_1(X33))
        | ~ r2_hidden(X35,k1_relat_1(X33))
        | k1_funct_1(X33,X34) != k1_funct_1(X33,X35)
        | X34 = X35
        | ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33) )
      & ( r2_hidden(esk8_1(X33),k1_relat_1(X33))
        | v2_funct_1(X33)
        | ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33) )
      & ( r2_hidden(esk9_1(X33),k1_relat_1(X33))
        | v2_funct_1(X33)
        | ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33) )
      & ( k1_funct_1(X33,esk8_1(X33)) = k1_funct_1(X33,esk9_1(X33))
        | v2_funct_1(X33)
        | ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33) )
      & ( esk8_1(X33) != esk9_1(X33)
        | v2_funct_1(X33)
        | ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).

cnf(c_0_25,plain,
    ( k1_funct_1(k5_relat_1(X1,X2),X3) = k1_funct_1(X2,k1_funct_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(k4_tarski(esk10_2(esk11_0,esk13_0),k1_funct_1(esk13_0,esk10_2(esk11_0,esk13_0))),esk13_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( X2 = X3
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( k1_relat_1(esk12_0) = esk11_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_31,negated_conjecture,
    ( v2_funct_1(esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_1(esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_33,negated_conjecture,
    ( v1_relat_1(esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_34,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk13_0,X1),X2) = k1_funct_1(X1,k1_funct_1(esk13_0,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_15]),c_0_16]),c_0_17])])).

cnf(c_0_35,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk13_0,esk10_2(esk11_0,esk13_0)),k2_relat_1(esk13_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_37,plain,
    ( X1 = k6_relat_1(X2)
    | k1_funct_1(X1,esk10_2(X2,X1)) != esk10_2(X2,X1)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_38,negated_conjecture,
    ( X1 = X2
    | k1_funct_1(esk12_0,X1) != k1_funct_1(esk12_0,X2)
    | ~ r2_hidden(X2,esk11_0)
    | ~ r2_hidden(X1,esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32]),c_0_33])])).

cnf(c_0_39,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk13_0,X1),esk10_2(esk11_0,esk13_0)) = k1_funct_1(X1,k1_funct_1(esk13_0,esk10_2(esk11_0,esk13_0)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_23])).

cnf(c_0_40,negated_conjecture,
    ( k5_relat_1(esk13_0,esk12_0) = esk12_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk13_0,esk10_2(esk11_0,esk13_0)),X1)
    | ~ r1_tarski(k2_relat_1(esk13_0),X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk13_0),esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_43,plain,
    ( k6_relat_1(k1_relat_1(X1)) = X1
    | k1_funct_1(X1,esk10_2(k1_relat_1(X1),X1)) != esk10_2(k1_relat_1(X1),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( X1 = esk10_2(esk11_0,esk13_0)
    | k1_funct_1(esk12_0,X1) != k1_funct_1(esk12_0,esk10_2(esk11_0,esk13_0))
    | ~ r2_hidden(X1,esk11_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_23])).

cnf(c_0_45,negated_conjecture,
    ( k1_funct_1(esk12_0,k1_funct_1(esk13_0,esk10_2(esk11_0,esk13_0))) = k1_funct_1(esk12_0,esk10_2(esk11_0,esk13_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_32]),c_0_40]),c_0_33])])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk13_0,esk10_2(esk11_0,esk13_0)),esk11_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( k1_funct_1(esk13_0,esk10_2(esk11_0,esk13_0)) != esk10_2(esk11_0,esk13_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_15]),c_0_16]),c_0_17])]),c_0_19])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])]),c_0_47]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:12:26 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S064I
% 0.18/0.37  # and selection function SelectComplexG.
% 0.18/0.37  #
% 0.18/0.37  # Preprocessing time       : 0.029 s
% 0.18/0.37  # Presaturation interreduction done
% 0.18/0.37  
% 0.18/0.37  # Proof found!
% 0.18/0.37  # SZS status Theorem
% 0.18/0.37  # SZS output start CNFRefutation
% 0.18/0.37  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 0.18/0.37  fof(t50_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(((((k1_relat_1(X2)=X1&k1_relat_1(X3)=X1)&r1_tarski(k2_relat_1(X3),X1))&v2_funct_1(X2))&k5_relat_1(X3,X2)=X2)=>X3=k6_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_funct_1)).
% 0.18/0.37  fof(t34_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(X2=k6_relat_1(X1)<=>(k1_relat_1(X2)=X1&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_funct_1)).
% 0.18/0.37  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 0.18/0.37  fof(t23_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(X2))=>k1_funct_1(k5_relat_1(X2,X3),X1)=k1_funct_1(X3,k1_funct_1(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 0.18/0.37  fof(d8_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)<=>![X2, X3]:(((r2_hidden(X2,k1_relat_1(X1))&r2_hidden(X3,k1_relat_1(X1)))&k1_funct_1(X1,X2)=k1_funct_1(X1,X3))=>X2=X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_funct_1)).
% 0.18/0.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.18/0.37  fof(c_0_7, plain, ![X45, X46, X47]:(((r2_hidden(X45,k1_relat_1(X47))|~r2_hidden(k4_tarski(X45,X46),X47)|(~v1_relat_1(X47)|~v1_funct_1(X47)))&(X46=k1_funct_1(X47,X45)|~r2_hidden(k4_tarski(X45,X46),X47)|(~v1_relat_1(X47)|~v1_funct_1(X47))))&(~r2_hidden(X45,k1_relat_1(X47))|X46!=k1_funct_1(X47,X45)|r2_hidden(k4_tarski(X45,X46),X47)|(~v1_relat_1(X47)|~v1_funct_1(X47)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.18/0.37  fof(c_0_8, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(((((k1_relat_1(X2)=X1&k1_relat_1(X3)=X1)&r1_tarski(k2_relat_1(X3),X1))&v2_funct_1(X2))&k5_relat_1(X3,X2)=X2)=>X3=k6_relat_1(X1))))), inference(assume_negation,[status(cth)],[t50_funct_1])).
% 0.18/0.37  fof(c_0_9, plain, ![X41, X42, X43]:(((k1_relat_1(X42)=X41|X42!=k6_relat_1(X41)|(~v1_relat_1(X42)|~v1_funct_1(X42)))&(~r2_hidden(X43,X41)|k1_funct_1(X42,X43)=X43|X42!=k6_relat_1(X41)|(~v1_relat_1(X42)|~v1_funct_1(X42))))&((r2_hidden(esk10_2(X41,X42),X41)|k1_relat_1(X42)!=X41|X42=k6_relat_1(X41)|(~v1_relat_1(X42)|~v1_funct_1(X42)))&(k1_funct_1(X42,esk10_2(X41,X42))!=esk10_2(X41,X42)|k1_relat_1(X42)!=X41|X42=k6_relat_1(X41)|(~v1_relat_1(X42)|~v1_funct_1(X42))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_funct_1])])])])])).
% 0.18/0.37  cnf(c_0_10, plain, (r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.37  fof(c_0_11, negated_conjecture, ((v1_relat_1(esk12_0)&v1_funct_1(esk12_0))&((v1_relat_1(esk13_0)&v1_funct_1(esk13_0))&(((((k1_relat_1(esk12_0)=esk11_0&k1_relat_1(esk13_0)=esk11_0)&r1_tarski(k2_relat_1(esk13_0),esk11_0))&v2_funct_1(esk12_0))&k5_relat_1(esk13_0,esk12_0)=esk12_0)&esk13_0!=k6_relat_1(esk11_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.18/0.37  cnf(c_0_12, plain, (r2_hidden(esk10_2(X1,X2),X1)|X2=k6_relat_1(X1)|k1_relat_1(X2)!=X1|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.37  fof(c_0_13, plain, ![X22, X23, X24, X26, X27, X28, X29, X31]:(((~r2_hidden(X24,X23)|r2_hidden(k4_tarski(esk5_3(X22,X23,X24),X24),X22)|X23!=k2_relat_1(X22))&(~r2_hidden(k4_tarski(X27,X26),X22)|r2_hidden(X26,X23)|X23!=k2_relat_1(X22)))&((~r2_hidden(esk6_2(X28,X29),X29)|~r2_hidden(k4_tarski(X31,esk6_2(X28,X29)),X28)|X29=k2_relat_1(X28))&(r2_hidden(esk6_2(X28,X29),X29)|r2_hidden(k4_tarski(esk7_2(X28,X29),esk6_2(X28,X29)),X28)|X29=k2_relat_1(X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.18/0.37  cnf(c_0_14, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_10])).
% 0.18/0.37  cnf(c_0_15, negated_conjecture, (k1_relat_1(esk13_0)=esk11_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.37  cnf(c_0_16, negated_conjecture, (v1_funct_1(esk13_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.37  cnf(c_0_17, negated_conjecture, (v1_relat_1(esk13_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.37  cnf(c_0_18, plain, (k6_relat_1(k1_relat_1(X1))=X1|r2_hidden(esk10_2(k1_relat_1(X1),X1),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_12])).
% 0.18/0.37  cnf(c_0_19, negated_conjecture, (esk13_0!=k6_relat_1(esk11_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.37  fof(c_0_20, plain, ![X38, X39, X40]:(~v1_relat_1(X39)|~v1_funct_1(X39)|(~v1_relat_1(X40)|~v1_funct_1(X40)|(~r2_hidden(X38,k1_relat_1(X39))|k1_funct_1(k5_relat_1(X39,X40),X38)=k1_funct_1(X40,k1_funct_1(X39,X38))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_1])])])).
% 0.18/0.37  cnf(c_0_21, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.37  cnf(c_0_22, negated_conjecture, (r2_hidden(k4_tarski(X1,k1_funct_1(esk13_0,X1)),esk13_0)|~r2_hidden(X1,esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_17])])).
% 0.18/0.37  cnf(c_0_23, negated_conjecture, (r2_hidden(esk10_2(esk11_0,esk13_0),esk11_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_16]), c_0_15]), c_0_15]), c_0_15]), c_0_17])]), c_0_19])).
% 0.18/0.37  fof(c_0_24, plain, ![X33, X34, X35]:((~v2_funct_1(X33)|(~r2_hidden(X34,k1_relat_1(X33))|~r2_hidden(X35,k1_relat_1(X33))|k1_funct_1(X33,X34)!=k1_funct_1(X33,X35)|X34=X35)|(~v1_relat_1(X33)|~v1_funct_1(X33)))&((((r2_hidden(esk8_1(X33),k1_relat_1(X33))|v2_funct_1(X33)|(~v1_relat_1(X33)|~v1_funct_1(X33)))&(r2_hidden(esk9_1(X33),k1_relat_1(X33))|v2_funct_1(X33)|(~v1_relat_1(X33)|~v1_funct_1(X33))))&(k1_funct_1(X33,esk8_1(X33))=k1_funct_1(X33,esk9_1(X33))|v2_funct_1(X33)|(~v1_relat_1(X33)|~v1_funct_1(X33))))&(esk8_1(X33)!=esk9_1(X33)|v2_funct_1(X33)|(~v1_relat_1(X33)|~v1_funct_1(X33))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).
% 0.18/0.37  cnf(c_0_25, plain, (k1_funct_1(k5_relat_1(X1,X2),X3)=k1_funct_1(X2,k1_funct_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.37  fof(c_0_26, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.18/0.37  cnf(c_0_27, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)), inference(er,[status(thm)],[c_0_21])).
% 0.18/0.37  cnf(c_0_28, negated_conjecture, (r2_hidden(k4_tarski(esk10_2(esk11_0,esk13_0),k1_funct_1(esk13_0,esk10_2(esk11_0,esk13_0))),esk13_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.18/0.37  cnf(c_0_29, plain, (X2=X3|~v2_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~r2_hidden(X3,k1_relat_1(X1))|k1_funct_1(X1,X2)!=k1_funct_1(X1,X3)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.37  cnf(c_0_30, negated_conjecture, (k1_relat_1(esk12_0)=esk11_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.37  cnf(c_0_31, negated_conjecture, (v2_funct_1(esk12_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.37  cnf(c_0_32, negated_conjecture, (v1_funct_1(esk12_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.37  cnf(c_0_33, negated_conjecture, (v1_relat_1(esk12_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.37  cnf(c_0_34, negated_conjecture, (k1_funct_1(k5_relat_1(esk13_0,X1),X2)=k1_funct_1(X1,k1_funct_1(esk13_0,X2))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_15]), c_0_16]), c_0_17])])).
% 0.18/0.37  cnf(c_0_35, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.18/0.37  cnf(c_0_36, negated_conjecture, (r2_hidden(k1_funct_1(esk13_0,esk10_2(esk11_0,esk13_0)),k2_relat_1(esk13_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.18/0.37  cnf(c_0_37, plain, (X1=k6_relat_1(X2)|k1_funct_1(X1,esk10_2(X2,X1))!=esk10_2(X2,X1)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.37  cnf(c_0_38, negated_conjecture, (X1=X2|k1_funct_1(esk12_0,X1)!=k1_funct_1(esk12_0,X2)|~r2_hidden(X2,esk11_0)|~r2_hidden(X1,esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32]), c_0_33])])).
% 0.18/0.37  cnf(c_0_39, negated_conjecture, (k1_funct_1(k5_relat_1(esk13_0,X1),esk10_2(esk11_0,esk13_0))=k1_funct_1(X1,k1_funct_1(esk13_0,esk10_2(esk11_0,esk13_0)))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_34, c_0_23])).
% 0.18/0.37  cnf(c_0_40, negated_conjecture, (k5_relat_1(esk13_0,esk12_0)=esk12_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.37  cnf(c_0_41, negated_conjecture, (r2_hidden(k1_funct_1(esk13_0,esk10_2(esk11_0,esk13_0)),X1)|~r1_tarski(k2_relat_1(esk13_0),X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.18/0.37  cnf(c_0_42, negated_conjecture, (r1_tarski(k2_relat_1(esk13_0),esk11_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.37  cnf(c_0_43, plain, (k6_relat_1(k1_relat_1(X1))=X1|k1_funct_1(X1,esk10_2(k1_relat_1(X1),X1))!=esk10_2(k1_relat_1(X1),X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_37])).
% 0.18/0.37  cnf(c_0_44, negated_conjecture, (X1=esk10_2(esk11_0,esk13_0)|k1_funct_1(esk12_0,X1)!=k1_funct_1(esk12_0,esk10_2(esk11_0,esk13_0))|~r2_hidden(X1,esk11_0)), inference(spm,[status(thm)],[c_0_38, c_0_23])).
% 0.18/0.37  cnf(c_0_45, negated_conjecture, (k1_funct_1(esk12_0,k1_funct_1(esk13_0,esk10_2(esk11_0,esk13_0)))=k1_funct_1(esk12_0,esk10_2(esk11_0,esk13_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_32]), c_0_40]), c_0_33])])).
% 0.18/0.37  cnf(c_0_46, negated_conjecture, (r2_hidden(k1_funct_1(esk13_0,esk10_2(esk11_0,esk13_0)),esk11_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.18/0.37  cnf(c_0_47, negated_conjecture, (k1_funct_1(esk13_0,esk10_2(esk11_0,esk13_0))!=esk10_2(esk11_0,esk13_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_15]), c_0_16]), c_0_17])]), c_0_19])).
% 0.18/0.37  cnf(c_0_48, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])]), c_0_47]), ['proof']).
% 0.18/0.37  # SZS output end CNFRefutation
% 0.18/0.37  # Proof object total steps             : 49
% 0.18/0.37  # Proof object clause steps            : 34
% 0.18/0.37  # Proof object formula steps           : 15
% 0.18/0.37  # Proof object conjectures             : 26
% 0.18/0.37  # Proof object clause conjectures      : 23
% 0.18/0.37  # Proof object formula conjectures     : 3
% 0.18/0.37  # Proof object initial clauses used    : 17
% 0.18/0.37  # Proof object initial formulas used   : 7
% 0.18/0.37  # Proof object generating inferences   : 13
% 0.18/0.37  # Proof object simplifying inferences  : 30
% 0.18/0.37  # Training examples: 0 positive, 0 negative
% 0.18/0.37  # Parsed axioms                        : 8
% 0.18/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.37  # Initial clauses                      : 34
% 0.18/0.37  # Removed in clause preprocessing      : 0
% 0.18/0.37  # Initial clauses in saturation        : 34
% 0.18/0.37  # Processed clauses                    : 164
% 0.18/0.37  # ...of these trivial                  : 0
% 0.18/0.37  # ...subsumed                          : 11
% 0.18/0.37  # ...remaining for further processing  : 153
% 0.18/0.37  # Other redundant clauses eliminated   : 9
% 0.18/0.37  # Clauses deleted for lack of memory   : 0
% 0.18/0.37  # Backward-subsumed                    : 1
% 0.18/0.37  # Backward-rewritten                   : 9
% 0.18/0.37  # Generated clauses                    : 257
% 0.18/0.37  # ...of the previous two non-trivial   : 237
% 0.18/0.37  # Contextual simplify-reflections      : 0
% 0.18/0.37  # Paramodulations                      : 242
% 0.18/0.37  # Factorizations                       : 2
% 0.18/0.37  # Equation resolutions                 : 13
% 0.18/0.37  # Propositional unsat checks           : 0
% 0.18/0.37  #    Propositional check models        : 0
% 0.18/0.37  #    Propositional check unsatisfiable : 0
% 0.18/0.37  #    Propositional clauses             : 0
% 0.18/0.37  #    Propositional clauses after purity: 0
% 0.18/0.37  #    Propositional unsat core size     : 0
% 0.18/0.37  #    Propositional preprocessing time  : 0.000
% 0.18/0.37  #    Propositional encoding time       : 0.000
% 0.18/0.37  #    Propositional solver time         : 0.000
% 0.18/0.37  #    Success case prop preproc time    : 0.000
% 0.18/0.37  #    Success case prop encoding time   : 0.000
% 0.18/0.37  #    Success case prop solver time     : 0.000
% 0.18/0.37  # Current number of processed clauses  : 101
% 0.18/0.37  #    Positive orientable unit clauses  : 18
% 0.18/0.37  #    Positive unorientable unit clauses: 0
% 0.18/0.37  #    Negative unit clauses             : 2
% 0.18/0.37  #    Non-unit-clauses                  : 81
% 0.18/0.37  # Current number of unprocessed clauses: 136
% 0.18/0.37  # ...number of literals in the above   : 436
% 0.18/0.37  # Current number of archived formulas  : 0
% 0.18/0.37  # Current number of archived clauses   : 43
% 0.18/0.37  # Clause-clause subsumption calls (NU) : 843
% 0.18/0.37  # Rec. Clause-clause subsumption calls : 590
% 0.18/0.37  # Non-unit clause-clause subsumptions  : 12
% 0.18/0.37  # Unit Clause-clause subsumption calls : 12
% 0.18/0.37  # Rewrite failures with RHS unbound    : 0
% 0.18/0.37  # BW rewrite match attempts            : 5
% 0.18/0.37  # BW rewrite match successes           : 3
% 0.18/0.37  # Condensation attempts                : 0
% 0.18/0.37  # Condensation successes               : 0
% 0.18/0.37  # Termbank termtop insertions          : 7821
% 0.18/0.38  
% 0.18/0.38  # -------------------------------------------------
% 0.18/0.38  # User time                : 0.038 s
% 0.18/0.38  # System time              : 0.006 s
% 0.18/0.38  # Total time               : 0.044 s
% 0.18/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
