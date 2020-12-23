%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:56 EST 2020

% Result     : Theorem 0.39s
% Output     : CNFRefutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   73 (1314 expanded)
%              Number of clauses        :   56 ( 529 expanded)
%              Number of leaves         :    8 ( 305 expanded)
%              Depth                    :   26
%              Number of atoms          :  355 (8438 expanded)
%              Number of equality atoms :   57 (1040 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_wellord1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l4_wellord1)).

fof(d4_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
      <=> ( v1_relat_2(X1)
          & v8_relat_2(X1)
          & v4_relat_2(X1)
          & v6_relat_2(X1)
          & v1_wellord1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

fof(d1_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k1_wellord1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ( X4 != X2
                & r2_hidden(k4_tarski(X4,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

fof(l2_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v8_relat_2(X1)
      <=> ! [X2,X3,X4] :
            ( ( r2_hidden(k4_tarski(X2,X3),X1)
              & r2_hidden(k4_tarski(X3,X4),X1) )
           => r2_hidden(k4_tarski(X2,X4),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l2_wellord1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(l3_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_2(X1)
      <=> ! [X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X1)
              & r2_hidden(k4_tarski(X3,X2),X1) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_wellord1)).

fof(l1_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v1_relat_2(X1)
      <=> ! [X2] :
            ( r2_hidden(X2,k3_relat_1(X1))
           => r2_hidden(k4_tarski(X2,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_wellord1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( ( v2_wellord1(X3)
            & r2_hidden(X1,k3_relat_1(X3))
            & r2_hidden(X2,k3_relat_1(X3)) )
         => ( r2_hidden(k4_tarski(X1,X2),X3)
          <=> r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t37_wellord1])).

fof(c_0_9,plain,(
    ! [X35,X36,X37] :
      ( ( ~ v6_relat_2(X35)
        | ~ r2_hidden(X36,k3_relat_1(X35))
        | ~ r2_hidden(X37,k3_relat_1(X35))
        | X36 = X37
        | r2_hidden(k4_tarski(X36,X37),X35)
        | r2_hidden(k4_tarski(X37,X36),X35)
        | ~ v1_relat_1(X35) )
      & ( r2_hidden(esk9_1(X35),k3_relat_1(X35))
        | v6_relat_2(X35)
        | ~ v1_relat_1(X35) )
      & ( r2_hidden(esk10_1(X35),k3_relat_1(X35))
        | v6_relat_2(X35)
        | ~ v1_relat_1(X35) )
      & ( esk9_1(X35) != esk10_1(X35)
        | v6_relat_2(X35)
        | ~ v1_relat_1(X35) )
      & ( ~ r2_hidden(k4_tarski(esk9_1(X35),esk10_1(X35)),X35)
        | v6_relat_2(X35)
        | ~ v1_relat_1(X35) )
      & ( ~ r2_hidden(k4_tarski(esk10_1(X35),esk9_1(X35)),X35)
        | v6_relat_2(X35)
        | ~ v1_relat_1(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l4_wellord1])])])])])])).

fof(c_0_10,negated_conjecture,
    ( v1_relat_1(esk13_0)
    & v2_wellord1(esk13_0)
    & r2_hidden(esk11_0,k3_relat_1(esk13_0))
    & r2_hidden(esk12_0,k3_relat_1(esk13_0))
    & ( ~ r2_hidden(k4_tarski(esk11_0,esk12_0),esk13_0)
      | ~ r1_tarski(k1_wellord1(esk13_0,esk11_0),k1_wellord1(esk13_0,esk12_0)) )
    & ( r2_hidden(k4_tarski(esk11_0,esk12_0),esk13_0)
      | r1_tarski(k1_wellord1(esk13_0,esk11_0),k1_wellord1(esk13_0,esk12_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_11,plain,
    ( X2 = X3
    | r2_hidden(k4_tarski(X2,X3),X1)
    | r2_hidden(k4_tarski(X3,X2),X1)
    | ~ v6_relat_2(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ r2_hidden(X3,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( r2_hidden(esk12_0,k3_relat_1(esk13_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( v1_relat_1(esk13_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X19] :
      ( ( v1_relat_2(X19)
        | ~ v2_wellord1(X19)
        | ~ v1_relat_1(X19) )
      & ( v8_relat_2(X19)
        | ~ v2_wellord1(X19)
        | ~ v1_relat_1(X19) )
      & ( v4_relat_2(X19)
        | ~ v2_wellord1(X19)
        | ~ v1_relat_1(X19) )
      & ( v6_relat_2(X19)
        | ~ v2_wellord1(X19)
        | ~ v1_relat_1(X19) )
      & ( v1_wellord1(X19)
        | ~ v2_wellord1(X19)
        | ~ v1_relat_1(X19) )
      & ( ~ v1_relat_2(X19)
        | ~ v8_relat_2(X19)
        | ~ v4_relat_2(X19)
        | ~ v6_relat_2(X19)
        | ~ v1_wellord1(X19)
        | v2_wellord1(X19)
        | ~ v1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).

fof(c_0_15,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17] :
      ( ( X14 != X12
        | ~ r2_hidden(X14,X13)
        | X13 != k1_wellord1(X11,X12)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(k4_tarski(X14,X12),X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k1_wellord1(X11,X12)
        | ~ v1_relat_1(X11) )
      & ( X15 = X12
        | ~ r2_hidden(k4_tarski(X15,X12),X11)
        | r2_hidden(X15,X13)
        | X13 != k1_wellord1(X11,X12)
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(esk2_3(X11,X16,X17),X17)
        | esk2_3(X11,X16,X17) = X16
        | ~ r2_hidden(k4_tarski(esk2_3(X11,X16,X17),X16),X11)
        | X17 = k1_wellord1(X11,X16)
        | ~ v1_relat_1(X11) )
      & ( esk2_3(X11,X16,X17) != X16
        | r2_hidden(esk2_3(X11,X16,X17),X17)
        | X17 = k1_wellord1(X11,X16)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(k4_tarski(esk2_3(X11,X16,X17),X16),X11)
        | r2_hidden(esk2_3(X11,X16,X17),X17)
        | X17 = k1_wellord1(X11,X16)
        | ~ v1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).

cnf(c_0_16,negated_conjecture,
    ( X1 = esk12_0
    | r2_hidden(k4_tarski(esk12_0,X1),esk13_0)
    | r2_hidden(k4_tarski(X1,esk12_0),esk13_0)
    | ~ v6_relat_2(esk13_0)
    | ~ r2_hidden(X1,k3_relat_1(esk13_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])])).

cnf(c_0_17,plain,
    ( v6_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( v2_wellord1(esk13_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_19,plain,(
    ! [X23,X24,X25,X26] :
      ( ( ~ v8_relat_2(X23)
        | ~ r2_hidden(k4_tarski(X24,X25),X23)
        | ~ r2_hidden(k4_tarski(X25,X26),X23)
        | r2_hidden(k4_tarski(X24,X26),X23)
        | ~ v1_relat_1(X23) )
      & ( r2_hidden(k4_tarski(esk4_1(X23),esk5_1(X23)),X23)
        | v8_relat_2(X23)
        | ~ v1_relat_1(X23) )
      & ( r2_hidden(k4_tarski(esk5_1(X23),esk6_1(X23)),X23)
        | v8_relat_2(X23)
        | ~ v1_relat_1(X23) )
      & ( ~ r2_hidden(k4_tarski(esk4_1(X23),esk6_1(X23)),X23)
        | v8_relat_2(X23)
        | ~ v1_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l2_wellord1])])])])])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | X4 != k1_wellord1(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( X1 = X2
    | r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_wellord1(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( X1 = esk12_0
    | r2_hidden(k4_tarski(X1,esk12_0),esk13_0)
    | r2_hidden(k4_tarski(esk12_0,X1),esk13_0)
    | ~ r2_hidden(X1,k3_relat_1(esk13_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_13])])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk11_0,k3_relat_1(esk13_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_24,plain,
    ( r2_hidden(k4_tarski(X2,X4),X1)
    | ~ v8_relat_2(X1)
    | ~ r2_hidden(k4_tarski(X2,X3),X1)
    | ~ r2_hidden(k4_tarski(X3,X4),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k1_wellord1(X3,X2)) ),
    inference(er,[status(thm)],[c_0_20])).

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
    ( X1 = X2
    | r2_hidden(X1,k1_wellord1(X3,X2))
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X1,X2),X3) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( esk12_0 = esk11_0
    | r2_hidden(k4_tarski(esk12_0,esk11_0),esk13_0)
    | r2_hidden(k4_tarski(esk11_0,esk12_0),esk13_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v8_relat_2(X3)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X1,X4),X3)
    | ~ r2_hidden(X4,k1_wellord1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(k4_tarski(esk11_0,esk12_0),esk13_0)
    | r1_tarski(k1_wellord1(esk13_0,esk11_0),k1_wellord1(esk13_0,esk12_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_32,negated_conjecture,
    ( esk12_0 = esk11_0
    | r2_hidden(k4_tarski(esk11_0,esk12_0),esk13_0)
    | r2_hidden(esk12_0,k1_wellord1(esk13_0,esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_13])])).

cnf(c_0_33,negated_conjecture,
    ( esk12_0 = esk11_0
    | r2_hidden(k4_tarski(esk11_0,esk12_0),esk13_0)
    | r2_hidden(k4_tarski(esk12_0,X1),esk13_0)
    | ~ v8_relat_2(esk13_0)
    | ~ r2_hidden(esk11_0,k1_wellord1(esk13_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_28]),c_0_13])])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(k4_tarski(esk11_0,esk12_0),esk13_0)
    | r2_hidden(X1,k1_wellord1(esk13_0,esk12_0))
    | ~ r2_hidden(X1,k1_wellord1(esk13_0,esk11_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( esk12_0 = esk11_0
    | r2_hidden(esk12_0,k1_wellord1(esk13_0,esk11_0))
    | r2_hidden(esk11_0,k1_wellord1(esk13_0,esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_32]),c_0_13])])).

cnf(c_0_36,negated_conjecture,
    ( esk12_0 = esk11_0
    | r2_hidden(k4_tarski(esk11_0,esk12_0),esk13_0)
    | r2_hidden(k4_tarski(X1,X2),esk13_0)
    | ~ v8_relat_2(esk13_0)
    | ~ r2_hidden(k4_tarski(X1,esk12_0),esk13_0)
    | ~ r2_hidden(esk11_0,k1_wellord1(esk13_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_33]),c_0_13])])).

cnf(c_0_37,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,X3)
    | X3 != k1_wellord1(X4,X2)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_38,negated_conjecture,
    ( esk12_0 = esk11_0
    | r2_hidden(esk11_0,k1_wellord1(esk13_0,esk12_0))
    | r2_hidden(esk12_0,k1_wellord1(esk13_0,esk12_0))
    | r2_hidden(k4_tarski(esk11_0,esk12_0),esk13_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( esk12_0 = esk11_0
    | r2_hidden(k4_tarski(esk11_0,esk12_0),esk13_0)
    | r2_hidden(k4_tarski(X1,X2),esk13_0)
    | ~ v8_relat_2(esk13_0)
    | ~ r2_hidden(esk11_0,k1_wellord1(esk13_0,X2))
    | ~ r2_hidden(X1,k1_wellord1(esk13_0,esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_25]),c_0_13])])).

cnf(c_0_40,plain,
    ( v8_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_41,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_wellord1(X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_37])])).

cnf(c_0_42,negated_conjecture,
    ( esk12_0 = esk11_0
    | r2_hidden(esk12_0,k1_wellord1(esk13_0,esk12_0))
    | r2_hidden(esk11_0,k1_wellord1(esk13_0,esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_38]),c_0_13])])).

cnf(c_0_43,negated_conjecture,
    ( esk12_0 = esk11_0
    | r2_hidden(k4_tarski(esk11_0,esk12_0),esk13_0)
    | r2_hidden(k4_tarski(X1,X2),esk13_0)
    | ~ r2_hidden(esk11_0,k1_wellord1(esk13_0,X2))
    | ~ r2_hidden(X1,k1_wellord1(esk13_0,esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_18]),c_0_13])])).

cnf(c_0_44,negated_conjecture,
    ( esk12_0 = esk11_0
    | r2_hidden(esk11_0,k1_wellord1(esk13_0,esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_13])])).

cnf(c_0_45,negated_conjecture,
    ( esk12_0 = esk11_0
    | r2_hidden(k4_tarski(esk11_0,esk12_0),esk13_0)
    | r2_hidden(k4_tarski(X1,esk12_0),esk13_0)
    | ~ r2_hidden(X1,k1_wellord1(esk13_0,esk12_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_46,negated_conjecture,
    ( esk12_0 = esk11_0
    | r2_hidden(k4_tarski(esk11_0,esk12_0),esk13_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( esk12_0 = esk11_0
    | r2_hidden(k4_tarski(X1,esk12_0),esk13_0)
    | ~ v8_relat_2(esk13_0)
    | ~ r2_hidden(k4_tarski(X1,esk11_0),esk13_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_46]),c_0_13])])).

cnf(c_0_48,negated_conjecture,
    ( esk12_0 = esk11_0
    | X1 = esk12_0
    | r2_hidden(X1,k1_wellord1(esk13_0,esk12_0))
    | ~ v8_relat_2(esk13_0)
    | ~ r2_hidden(k4_tarski(X1,esk11_0),esk13_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_47]),c_0_13])])).

fof(c_0_49,plain,(
    ! [X30,X31,X32] :
      ( ( ~ v4_relat_2(X30)
        | ~ r2_hidden(k4_tarski(X31,X32),X30)
        | ~ r2_hidden(k4_tarski(X32,X31),X30)
        | X31 = X32
        | ~ v1_relat_1(X30) )
      & ( r2_hidden(k4_tarski(esk7_1(X30),esk8_1(X30)),X30)
        | v4_relat_2(X30)
        | ~ v1_relat_1(X30) )
      & ( r2_hidden(k4_tarski(esk8_1(X30),esk7_1(X30)),X30)
        | v4_relat_2(X30)
        | ~ v1_relat_1(X30) )
      & ( esk7_1(X30) != esk8_1(X30)
        | v4_relat_2(X30)
        | ~ v1_relat_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_wellord1])])])])])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_51,negated_conjecture,
    ( esk12_0 = esk11_0
    | X1 = esk12_0
    | r2_hidden(X1,k1_wellord1(esk13_0,esk12_0))
    | ~ v8_relat_2(esk13_0)
    | ~ r2_hidden(X1,k1_wellord1(esk13_0,esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_25]),c_0_13])])).

cnf(c_0_52,plain,
    ( X2 = X3
    | ~ v4_relat_2(X1)
    | ~ r2_hidden(k4_tarski(X2,X3),X1)
    | ~ r2_hidden(k4_tarski(X3,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( esk1_2(X1,k1_wellord1(esk13_0,esk12_0)) = esk12_0
    | esk12_0 = esk11_0
    | r1_tarski(X1,k1_wellord1(esk13_0,esk12_0))
    | ~ v8_relat_2(esk13_0)
    | ~ r2_hidden(esk1_2(X1,k1_wellord1(esk13_0,esk12_0)),k1_wellord1(esk13_0,esk11_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_54,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_55,plain,
    ( X1 = X2
    | ~ v4_relat_2(X3)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,k1_wellord1(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_25])).

cnf(c_0_56,negated_conjecture,
    ( esk1_2(k1_wellord1(esk13_0,esk11_0),k1_wellord1(esk13_0,esk12_0)) = esk12_0
    | esk12_0 = esk11_0
    | r1_tarski(k1_wellord1(esk13_0,esk11_0),k1_wellord1(esk13_0,esk12_0))
    | ~ v8_relat_2(esk13_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( esk12_0 = esk11_0
    | r2_hidden(k4_tarski(esk11_0,esk12_0),esk13_0)
    | ~ v4_relat_2(esk13_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_28]),c_0_13])]),c_0_44])).

cnf(c_0_58,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk11_0,esk12_0),esk13_0)
    | ~ r1_tarski(k1_wellord1(esk13_0,esk11_0),k1_wellord1(esk13_0,esk12_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_59,negated_conjecture,
    ( esk12_0 = esk11_0
    | r2_hidden(esk12_0,k1_wellord1(esk13_0,esk11_0))
    | r1_tarski(k1_wellord1(esk13_0,esk11_0),k1_wellord1(esk13_0,esk12_0))
    | ~ v8_relat_2(esk13_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( esk12_0 = esk11_0
    | ~ v4_relat_2(esk13_0)
    | ~ r2_hidden(esk12_0,k1_wellord1(esk13_0,esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_57]),c_0_13])])).

cnf(c_0_61,negated_conjecture,
    ( esk12_0 = esk11_0
    | r2_hidden(esk12_0,k1_wellord1(esk13_0,esk11_0))
    | ~ v8_relat_2(esk13_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_46])).

cnf(c_0_62,negated_conjecture,
    ( esk12_0 = esk11_0
    | ~ v4_relat_2(esk13_0)
    | ~ v8_relat_2(esk13_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_63,plain,
    ( v4_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_64,negated_conjecture,
    ( esk12_0 = esk11_0
    | ~ v8_relat_2(esk13_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_18]),c_0_13])])).

cnf(c_0_65,negated_conjecture,
    ( esk12_0 = esk11_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_40]),c_0_18]),c_0_13])])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_54])).

fof(c_0_67,plain,(
    ! [X20,X21] :
      ( ( ~ v1_relat_2(X20)
        | ~ r2_hidden(X21,k3_relat_1(X20))
        | r2_hidden(k4_tarski(X21,X21),X20)
        | ~ v1_relat_1(X20) )
      & ( r2_hidden(esk3_1(X20),k3_relat_1(X20))
        | v1_relat_2(X20)
        | ~ v1_relat_1(X20) )
      & ( ~ r2_hidden(k4_tarski(esk3_1(X20),esk3_1(X20)),X20)
        | v1_relat_2(X20)
        | ~ v1_relat_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_wellord1])])])])])).

cnf(c_0_68,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk11_0,esk11_0),esk13_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_65]),c_0_65]),c_0_66])])).

cnf(c_0_69,plain,
    ( r2_hidden(k4_tarski(X2,X2),X1)
    | ~ v1_relat_2(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_70,negated_conjecture,
    ( ~ v1_relat_2(esk13_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_13]),c_0_23])])).

cnf(c_0_71,plain,
    ( v1_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_18]),c_0_13])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:45:40 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.39/0.55  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.39/0.55  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.39/0.55  #
% 0.39/0.55  # Preprocessing time       : 0.028 s
% 0.39/0.55  
% 0.39/0.55  # Proof found!
% 0.39/0.55  # SZS status Theorem
% 0.39/0.55  # SZS output start CNFRefutation
% 0.39/0.55  fof(t37_wellord1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(((v2_wellord1(X3)&r2_hidden(X1,k3_relat_1(X3)))&r2_hidden(X2,k3_relat_1(X3)))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_wellord1)).
% 0.39/0.55  fof(l4_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v6_relat_2(X1)<=>![X2, X3]:~(((((r2_hidden(X2,k3_relat_1(X1))&r2_hidden(X3,k3_relat_1(X1)))&X2!=X3)&~(r2_hidden(k4_tarski(X2,X3),X1)))&~(r2_hidden(k4_tarski(X3,X2),X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l4_wellord1)).
% 0.39/0.55  fof(d4_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v2_wellord1(X1)<=>((((v1_relat_2(X1)&v8_relat_2(X1))&v4_relat_2(X1))&v6_relat_2(X1))&v1_wellord1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_wellord1)).
% 0.39/0.55  fof(d1_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k1_wellord1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4!=X2&r2_hidden(k4_tarski(X4,X2),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord1)).
% 0.39/0.55  fof(l2_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v8_relat_2(X1)<=>![X2, X3, X4]:((r2_hidden(k4_tarski(X2,X3),X1)&r2_hidden(k4_tarski(X3,X4),X1))=>r2_hidden(k4_tarski(X2,X4),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l2_wellord1)).
% 0.39/0.55  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.39/0.55  fof(l3_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v4_relat_2(X1)<=>![X2, X3]:((r2_hidden(k4_tarski(X2,X3),X1)&r2_hidden(k4_tarski(X3,X2),X1))=>X2=X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_wellord1)).
% 0.39/0.55  fof(l1_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v1_relat_2(X1)<=>![X2]:(r2_hidden(X2,k3_relat_1(X1))=>r2_hidden(k4_tarski(X2,X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_wellord1)).
% 0.39/0.55  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(((v2_wellord1(X3)&r2_hidden(X1,k3_relat_1(X3)))&r2_hidden(X2,k3_relat_1(X3)))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2)))))), inference(assume_negation,[status(cth)],[t37_wellord1])).
% 0.39/0.55  fof(c_0_9, plain, ![X35, X36, X37]:((~v6_relat_2(X35)|(~r2_hidden(X36,k3_relat_1(X35))|~r2_hidden(X37,k3_relat_1(X35))|X36=X37|r2_hidden(k4_tarski(X36,X37),X35)|r2_hidden(k4_tarski(X37,X36),X35))|~v1_relat_1(X35))&(((((r2_hidden(esk9_1(X35),k3_relat_1(X35))|v6_relat_2(X35)|~v1_relat_1(X35))&(r2_hidden(esk10_1(X35),k3_relat_1(X35))|v6_relat_2(X35)|~v1_relat_1(X35)))&(esk9_1(X35)!=esk10_1(X35)|v6_relat_2(X35)|~v1_relat_1(X35)))&(~r2_hidden(k4_tarski(esk9_1(X35),esk10_1(X35)),X35)|v6_relat_2(X35)|~v1_relat_1(X35)))&(~r2_hidden(k4_tarski(esk10_1(X35),esk9_1(X35)),X35)|v6_relat_2(X35)|~v1_relat_1(X35)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l4_wellord1])])])])])])).
% 0.39/0.55  fof(c_0_10, negated_conjecture, (v1_relat_1(esk13_0)&(((v2_wellord1(esk13_0)&r2_hidden(esk11_0,k3_relat_1(esk13_0)))&r2_hidden(esk12_0,k3_relat_1(esk13_0)))&((~r2_hidden(k4_tarski(esk11_0,esk12_0),esk13_0)|~r1_tarski(k1_wellord1(esk13_0,esk11_0),k1_wellord1(esk13_0,esk12_0)))&(r2_hidden(k4_tarski(esk11_0,esk12_0),esk13_0)|r1_tarski(k1_wellord1(esk13_0,esk11_0),k1_wellord1(esk13_0,esk12_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.39/0.55  cnf(c_0_11, plain, (X2=X3|r2_hidden(k4_tarski(X2,X3),X1)|r2_hidden(k4_tarski(X3,X2),X1)|~v6_relat_2(X1)|~r2_hidden(X2,k3_relat_1(X1))|~r2_hidden(X3,k3_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.39/0.55  cnf(c_0_12, negated_conjecture, (r2_hidden(esk12_0,k3_relat_1(esk13_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.39/0.55  cnf(c_0_13, negated_conjecture, (v1_relat_1(esk13_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.39/0.55  fof(c_0_14, plain, ![X19]:((((((v1_relat_2(X19)|~v2_wellord1(X19)|~v1_relat_1(X19))&(v8_relat_2(X19)|~v2_wellord1(X19)|~v1_relat_1(X19)))&(v4_relat_2(X19)|~v2_wellord1(X19)|~v1_relat_1(X19)))&(v6_relat_2(X19)|~v2_wellord1(X19)|~v1_relat_1(X19)))&(v1_wellord1(X19)|~v2_wellord1(X19)|~v1_relat_1(X19)))&(~v1_relat_2(X19)|~v8_relat_2(X19)|~v4_relat_2(X19)|~v6_relat_2(X19)|~v1_wellord1(X19)|v2_wellord1(X19)|~v1_relat_1(X19))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).
% 0.39/0.55  fof(c_0_15, plain, ![X11, X12, X13, X14, X15, X16, X17]:((((X14!=X12|~r2_hidden(X14,X13)|X13!=k1_wellord1(X11,X12)|~v1_relat_1(X11))&(r2_hidden(k4_tarski(X14,X12),X11)|~r2_hidden(X14,X13)|X13!=k1_wellord1(X11,X12)|~v1_relat_1(X11)))&(X15=X12|~r2_hidden(k4_tarski(X15,X12),X11)|r2_hidden(X15,X13)|X13!=k1_wellord1(X11,X12)|~v1_relat_1(X11)))&((~r2_hidden(esk2_3(X11,X16,X17),X17)|(esk2_3(X11,X16,X17)=X16|~r2_hidden(k4_tarski(esk2_3(X11,X16,X17),X16),X11))|X17=k1_wellord1(X11,X16)|~v1_relat_1(X11))&((esk2_3(X11,X16,X17)!=X16|r2_hidden(esk2_3(X11,X16,X17),X17)|X17=k1_wellord1(X11,X16)|~v1_relat_1(X11))&(r2_hidden(k4_tarski(esk2_3(X11,X16,X17),X16),X11)|r2_hidden(esk2_3(X11,X16,X17),X17)|X17=k1_wellord1(X11,X16)|~v1_relat_1(X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).
% 0.39/0.55  cnf(c_0_16, negated_conjecture, (X1=esk12_0|r2_hidden(k4_tarski(esk12_0,X1),esk13_0)|r2_hidden(k4_tarski(X1,esk12_0),esk13_0)|~v6_relat_2(esk13_0)|~r2_hidden(X1,k3_relat_1(esk13_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13])])).
% 0.39/0.55  cnf(c_0_17, plain, (v6_relat_2(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.39/0.55  cnf(c_0_18, negated_conjecture, (v2_wellord1(esk13_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.39/0.55  fof(c_0_19, plain, ![X23, X24, X25, X26]:((~v8_relat_2(X23)|(~r2_hidden(k4_tarski(X24,X25),X23)|~r2_hidden(k4_tarski(X25,X26),X23)|r2_hidden(k4_tarski(X24,X26),X23))|~v1_relat_1(X23))&(((r2_hidden(k4_tarski(esk4_1(X23),esk5_1(X23)),X23)|v8_relat_2(X23)|~v1_relat_1(X23))&(r2_hidden(k4_tarski(esk5_1(X23),esk6_1(X23)),X23)|v8_relat_2(X23)|~v1_relat_1(X23)))&(~r2_hidden(k4_tarski(esk4_1(X23),esk6_1(X23)),X23)|v8_relat_2(X23)|~v1_relat_1(X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l2_wellord1])])])])])).
% 0.39/0.55  cnf(c_0_20, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,X4)|X4!=k1_wellord1(X3,X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.39/0.55  cnf(c_0_21, plain, (X1=X2|r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_wellord1(X3,X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.39/0.55  cnf(c_0_22, negated_conjecture, (X1=esk12_0|r2_hidden(k4_tarski(X1,esk12_0),esk13_0)|r2_hidden(k4_tarski(esk12_0,X1),esk13_0)|~r2_hidden(X1,k3_relat_1(esk13_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_13])])).
% 0.39/0.55  cnf(c_0_23, negated_conjecture, (r2_hidden(esk11_0,k3_relat_1(esk13_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.39/0.55  cnf(c_0_24, plain, (r2_hidden(k4_tarski(X2,X4),X1)|~v8_relat_2(X1)|~r2_hidden(k4_tarski(X2,X3),X1)|~r2_hidden(k4_tarski(X3,X4),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.39/0.55  cnf(c_0_25, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)|~r2_hidden(X1,k1_wellord1(X3,X2))), inference(er,[status(thm)],[c_0_20])).
% 0.39/0.55  fof(c_0_26, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.39/0.55  cnf(c_0_27, plain, (X1=X2|r2_hidden(X1,k1_wellord1(X3,X2))|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X1,X2),X3)), inference(er,[status(thm)],[c_0_21])).
% 0.39/0.55  cnf(c_0_28, negated_conjecture, (esk12_0=esk11_0|r2_hidden(k4_tarski(esk12_0,esk11_0),esk13_0)|r2_hidden(k4_tarski(esk11_0,esk12_0),esk13_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.39/0.55  cnf(c_0_29, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~v8_relat_2(X3)|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X1,X4),X3)|~r2_hidden(X4,k1_wellord1(X3,X2))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.39/0.55  cnf(c_0_30, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.39/0.55  cnf(c_0_31, negated_conjecture, (r2_hidden(k4_tarski(esk11_0,esk12_0),esk13_0)|r1_tarski(k1_wellord1(esk13_0,esk11_0),k1_wellord1(esk13_0,esk12_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.39/0.55  cnf(c_0_32, negated_conjecture, (esk12_0=esk11_0|r2_hidden(k4_tarski(esk11_0,esk12_0),esk13_0)|r2_hidden(esk12_0,k1_wellord1(esk13_0,esk11_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_13])])).
% 0.39/0.55  cnf(c_0_33, negated_conjecture, (esk12_0=esk11_0|r2_hidden(k4_tarski(esk11_0,esk12_0),esk13_0)|r2_hidden(k4_tarski(esk12_0,X1),esk13_0)|~v8_relat_2(esk13_0)|~r2_hidden(esk11_0,k1_wellord1(esk13_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_28]), c_0_13])])).
% 0.39/0.55  cnf(c_0_34, negated_conjecture, (r2_hidden(k4_tarski(esk11_0,esk12_0),esk13_0)|r2_hidden(X1,k1_wellord1(esk13_0,esk12_0))|~r2_hidden(X1,k1_wellord1(esk13_0,esk11_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.39/0.55  cnf(c_0_35, negated_conjecture, (esk12_0=esk11_0|r2_hidden(esk12_0,k1_wellord1(esk13_0,esk11_0))|r2_hidden(esk11_0,k1_wellord1(esk13_0,esk12_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_32]), c_0_13])])).
% 0.39/0.55  cnf(c_0_36, negated_conjecture, (esk12_0=esk11_0|r2_hidden(k4_tarski(esk11_0,esk12_0),esk13_0)|r2_hidden(k4_tarski(X1,X2),esk13_0)|~v8_relat_2(esk13_0)|~r2_hidden(k4_tarski(X1,esk12_0),esk13_0)|~r2_hidden(esk11_0,k1_wellord1(esk13_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_33]), c_0_13])])).
% 0.39/0.55  cnf(c_0_37, plain, (X1!=X2|~r2_hidden(X1,X3)|X3!=k1_wellord1(X4,X2)|~v1_relat_1(X4)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.39/0.55  cnf(c_0_38, negated_conjecture, (esk12_0=esk11_0|r2_hidden(esk11_0,k1_wellord1(esk13_0,esk12_0))|r2_hidden(esk12_0,k1_wellord1(esk13_0,esk12_0))|r2_hidden(k4_tarski(esk11_0,esk12_0),esk13_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.39/0.55  cnf(c_0_39, negated_conjecture, (esk12_0=esk11_0|r2_hidden(k4_tarski(esk11_0,esk12_0),esk13_0)|r2_hidden(k4_tarski(X1,X2),esk13_0)|~v8_relat_2(esk13_0)|~r2_hidden(esk11_0,k1_wellord1(esk13_0,X2))|~r2_hidden(X1,k1_wellord1(esk13_0,esk12_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_25]), c_0_13])])).
% 0.39/0.55  cnf(c_0_40, plain, (v8_relat_2(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.39/0.55  cnf(c_0_41, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k1_wellord1(X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_37])])).
% 0.39/0.55  cnf(c_0_42, negated_conjecture, (esk12_0=esk11_0|r2_hidden(esk12_0,k1_wellord1(esk13_0,esk12_0))|r2_hidden(esk11_0,k1_wellord1(esk13_0,esk12_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_38]), c_0_13])])).
% 0.39/0.55  cnf(c_0_43, negated_conjecture, (esk12_0=esk11_0|r2_hidden(k4_tarski(esk11_0,esk12_0),esk13_0)|r2_hidden(k4_tarski(X1,X2),esk13_0)|~r2_hidden(esk11_0,k1_wellord1(esk13_0,X2))|~r2_hidden(X1,k1_wellord1(esk13_0,esk12_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_18]), c_0_13])])).
% 0.39/0.55  cnf(c_0_44, negated_conjecture, (esk12_0=esk11_0|r2_hidden(esk11_0,k1_wellord1(esk13_0,esk12_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_13])])).
% 0.39/0.55  cnf(c_0_45, negated_conjecture, (esk12_0=esk11_0|r2_hidden(k4_tarski(esk11_0,esk12_0),esk13_0)|r2_hidden(k4_tarski(X1,esk12_0),esk13_0)|~r2_hidden(X1,k1_wellord1(esk13_0,esk12_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.39/0.55  cnf(c_0_46, negated_conjecture, (esk12_0=esk11_0|r2_hidden(k4_tarski(esk11_0,esk12_0),esk13_0)), inference(spm,[status(thm)],[c_0_45, c_0_44])).
% 0.39/0.55  cnf(c_0_47, negated_conjecture, (esk12_0=esk11_0|r2_hidden(k4_tarski(X1,esk12_0),esk13_0)|~v8_relat_2(esk13_0)|~r2_hidden(k4_tarski(X1,esk11_0),esk13_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_46]), c_0_13])])).
% 0.39/0.55  cnf(c_0_48, negated_conjecture, (esk12_0=esk11_0|X1=esk12_0|r2_hidden(X1,k1_wellord1(esk13_0,esk12_0))|~v8_relat_2(esk13_0)|~r2_hidden(k4_tarski(X1,esk11_0),esk13_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_47]), c_0_13])])).
% 0.39/0.55  fof(c_0_49, plain, ![X30, X31, X32]:((~v4_relat_2(X30)|(~r2_hidden(k4_tarski(X31,X32),X30)|~r2_hidden(k4_tarski(X32,X31),X30)|X31=X32)|~v1_relat_1(X30))&(((r2_hidden(k4_tarski(esk7_1(X30),esk8_1(X30)),X30)|v4_relat_2(X30)|~v1_relat_1(X30))&(r2_hidden(k4_tarski(esk8_1(X30),esk7_1(X30)),X30)|v4_relat_2(X30)|~v1_relat_1(X30)))&(esk7_1(X30)!=esk8_1(X30)|v4_relat_2(X30)|~v1_relat_1(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_wellord1])])])])])).
% 0.39/0.55  cnf(c_0_50, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.39/0.55  cnf(c_0_51, negated_conjecture, (esk12_0=esk11_0|X1=esk12_0|r2_hidden(X1,k1_wellord1(esk13_0,esk12_0))|~v8_relat_2(esk13_0)|~r2_hidden(X1,k1_wellord1(esk13_0,esk11_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_25]), c_0_13])])).
% 0.39/0.55  cnf(c_0_52, plain, (X2=X3|~v4_relat_2(X1)|~r2_hidden(k4_tarski(X2,X3),X1)|~r2_hidden(k4_tarski(X3,X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.39/0.55  cnf(c_0_53, negated_conjecture, (esk1_2(X1,k1_wellord1(esk13_0,esk12_0))=esk12_0|esk12_0=esk11_0|r1_tarski(X1,k1_wellord1(esk13_0,esk12_0))|~v8_relat_2(esk13_0)|~r2_hidden(esk1_2(X1,k1_wellord1(esk13_0,esk12_0)),k1_wellord1(esk13_0,esk11_0))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.39/0.55  cnf(c_0_54, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.39/0.55  cnf(c_0_55, plain, (X1=X2|~v4_relat_2(X3)|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X2,k1_wellord1(X3,X1))), inference(spm,[status(thm)],[c_0_52, c_0_25])).
% 0.39/0.55  cnf(c_0_56, negated_conjecture, (esk1_2(k1_wellord1(esk13_0,esk11_0),k1_wellord1(esk13_0,esk12_0))=esk12_0|esk12_0=esk11_0|r1_tarski(k1_wellord1(esk13_0,esk11_0),k1_wellord1(esk13_0,esk12_0))|~v8_relat_2(esk13_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.39/0.55  cnf(c_0_57, negated_conjecture, (esk12_0=esk11_0|r2_hidden(k4_tarski(esk11_0,esk12_0),esk13_0)|~v4_relat_2(esk13_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_28]), c_0_13])]), c_0_44])).
% 0.39/0.55  cnf(c_0_58, negated_conjecture, (~r2_hidden(k4_tarski(esk11_0,esk12_0),esk13_0)|~r1_tarski(k1_wellord1(esk13_0,esk11_0),k1_wellord1(esk13_0,esk12_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.39/0.55  cnf(c_0_59, negated_conjecture, (esk12_0=esk11_0|r2_hidden(esk12_0,k1_wellord1(esk13_0,esk11_0))|r1_tarski(k1_wellord1(esk13_0,esk11_0),k1_wellord1(esk13_0,esk12_0))|~v8_relat_2(esk13_0)), inference(spm,[status(thm)],[c_0_54, c_0_56])).
% 0.39/0.55  cnf(c_0_60, negated_conjecture, (esk12_0=esk11_0|~v4_relat_2(esk13_0)|~r2_hidden(esk12_0,k1_wellord1(esk13_0,esk11_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_57]), c_0_13])])).
% 0.39/0.55  cnf(c_0_61, negated_conjecture, (esk12_0=esk11_0|r2_hidden(esk12_0,k1_wellord1(esk13_0,esk11_0))|~v8_relat_2(esk13_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_46])).
% 0.39/0.55  cnf(c_0_62, negated_conjecture, (esk12_0=esk11_0|~v4_relat_2(esk13_0)|~v8_relat_2(esk13_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.39/0.55  cnf(c_0_63, plain, (v4_relat_2(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.39/0.55  cnf(c_0_64, negated_conjecture, (esk12_0=esk11_0|~v8_relat_2(esk13_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_18]), c_0_13])])).
% 0.39/0.55  cnf(c_0_65, negated_conjecture, (esk12_0=esk11_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_40]), c_0_18]), c_0_13])])).
% 0.39/0.55  cnf(c_0_66, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_50, c_0_54])).
% 0.39/0.55  fof(c_0_67, plain, ![X20, X21]:((~v1_relat_2(X20)|(~r2_hidden(X21,k3_relat_1(X20))|r2_hidden(k4_tarski(X21,X21),X20))|~v1_relat_1(X20))&((r2_hidden(esk3_1(X20),k3_relat_1(X20))|v1_relat_2(X20)|~v1_relat_1(X20))&(~r2_hidden(k4_tarski(esk3_1(X20),esk3_1(X20)),X20)|v1_relat_2(X20)|~v1_relat_1(X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_wellord1])])])])])).
% 0.39/0.55  cnf(c_0_68, negated_conjecture, (~r2_hidden(k4_tarski(esk11_0,esk11_0),esk13_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_65]), c_0_65]), c_0_66])])).
% 0.39/0.55  cnf(c_0_69, plain, (r2_hidden(k4_tarski(X2,X2),X1)|~v1_relat_2(X1)|~r2_hidden(X2,k3_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.39/0.55  cnf(c_0_70, negated_conjecture, (~v1_relat_2(esk13_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_13]), c_0_23])])).
% 0.39/0.55  cnf(c_0_71, plain, (v1_relat_2(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.39/0.55  cnf(c_0_72, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_18]), c_0_13])]), ['proof']).
% 0.39/0.55  # SZS output end CNFRefutation
% 0.39/0.55  # Proof object total steps             : 73
% 0.39/0.55  # Proof object clause steps            : 56
% 0.39/0.55  # Proof object formula steps           : 17
% 0.39/0.55  # Proof object conjectures             : 39
% 0.39/0.55  # Proof object clause conjectures      : 36
% 0.39/0.55  # Proof object formula conjectures     : 3
% 0.39/0.55  # Proof object initial clauses used    : 20
% 0.39/0.55  # Proof object initial formulas used   : 8
% 0.39/0.55  # Proof object generating inferences   : 32
% 0.39/0.55  # Proof object simplifying inferences  : 54
% 0.39/0.55  # Training examples: 0 positive, 0 negative
% 0.39/0.55  # Parsed axioms                        : 8
% 0.39/0.55  # Removed by relevancy pruning/SinE    : 0
% 0.39/0.55  # Initial clauses                      : 38
% 0.39/0.55  # Removed in clause preprocessing      : 0
% 0.39/0.55  # Initial clauses in saturation        : 38
% 0.39/0.55  # Processed clauses                    : 1155
% 0.39/0.55  # ...of these trivial                  : 0
% 0.39/0.55  # ...subsumed                          : 649
% 0.39/0.55  # ...remaining for further processing  : 506
% 0.39/0.55  # Other redundant clauses eliminated   : 4
% 0.39/0.55  # Clauses deleted for lack of memory   : 0
% 0.39/0.55  # Backward-subsumed                    : 232
% 0.39/0.55  # Backward-rewritten                   : 125
% 0.39/0.55  # Generated clauses                    : 4399
% 0.39/0.55  # ...of the previous two non-trivial   : 3954
% 0.39/0.55  # Contextual simplify-reflections      : 14
% 0.39/0.55  # Paramodulations                      : 4393
% 0.39/0.55  # Factorizations                       : 0
% 0.39/0.55  # Equation resolutions                 : 4
% 0.39/0.55  # Propositional unsat checks           : 0
% 0.39/0.55  #    Propositional check models        : 0
% 0.39/0.55  #    Propositional check unsatisfiable : 0
% 0.39/0.55  #    Propositional clauses             : 0
% 0.39/0.55  #    Propositional clauses after purity: 0
% 0.39/0.55  #    Propositional unsat core size     : 0
% 0.39/0.55  #    Propositional preprocessing time  : 0.000
% 0.39/0.55  #    Propositional encoding time       : 0.000
% 0.39/0.55  #    Propositional solver time         : 0.000
% 0.39/0.55  #    Success case prop preproc time    : 0.000
% 0.39/0.55  #    Success case prop encoding time   : 0.000
% 0.39/0.55  #    Success case prop solver time     : 0.000
% 0.39/0.55  # Current number of processed clauses  : 143
% 0.39/0.55  #    Positive orientable unit clauses  : 5
% 0.39/0.55  #    Positive unorientable unit clauses: 0
% 0.39/0.55  #    Negative unit clauses             : 2
% 0.39/0.55  #    Non-unit-clauses                  : 136
% 0.39/0.55  # Current number of unprocessed clauses: 2739
% 0.39/0.55  # ...number of literals in the above   : 23063
% 0.39/0.55  # Current number of archived formulas  : 0
% 0.39/0.55  # Current number of archived clauses   : 360
% 0.39/0.55  # Clause-clause subsumption calls (NU) : 37418
% 0.39/0.55  # Rec. Clause-clause subsumption calls : 2694
% 0.39/0.55  # Non-unit clause-clause subsumptions  : 895
% 0.39/0.55  # Unit Clause-clause subsumption calls : 41
% 0.39/0.55  # Rewrite failures with RHS unbound    : 0
% 0.39/0.55  # BW rewrite match attempts            : 4
% 0.39/0.55  # BW rewrite match successes           : 1
% 0.39/0.55  # Condensation attempts                : 0
% 0.39/0.55  # Condensation successes               : 0
% 0.39/0.55  # Termbank termtop insertions          : 147361
% 0.39/0.55  
% 0.39/0.55  # -------------------------------------------------
% 0.39/0.55  # User time                : 0.192 s
% 0.39/0.55  # System time              : 0.008 s
% 0.39/0.55  # Total time               : 0.200 s
% 0.39/0.55  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
