%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0787+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:11 EST 2020

% Result     : Theorem 0.10s
% Output     : CNFRefutation 0.10s
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

fof(l3_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_2(X1)
      <=> ! [X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X1)
              & r2_hidden(k4_tarski(X3,X2),X1) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_wellord1)).

fof(l1_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v1_relat_2(X1)
      <=> ! [X2] :
            ( r2_hidden(X2,k3_relat_1(X1))
           => r2_hidden(k4_tarski(X2,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_wellord1)).

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
    ! [X5,X6,X7,X8,X9,X10,X11] :
      ( ( X8 != X6
        | ~ r2_hidden(X8,X7)
        | X7 != k1_wellord1(X5,X6)
        | ~ v1_relat_1(X5) )
      & ( r2_hidden(k4_tarski(X8,X6),X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k1_wellord1(X5,X6)
        | ~ v1_relat_1(X5) )
      & ( X9 = X6
        | ~ r2_hidden(k4_tarski(X9,X6),X5)
        | r2_hidden(X9,X7)
        | X7 != k1_wellord1(X5,X6)
        | ~ v1_relat_1(X5) )
      & ( ~ r2_hidden(esk1_3(X5,X10,X11),X11)
        | esk1_3(X5,X10,X11) = X10
        | ~ r2_hidden(k4_tarski(esk1_3(X5,X10,X11),X10),X5)
        | X11 = k1_wellord1(X5,X10)
        | ~ v1_relat_1(X5) )
      & ( esk1_3(X5,X10,X11) != X10
        | r2_hidden(esk1_3(X5,X10,X11),X11)
        | X11 = k1_wellord1(X5,X10)
        | ~ v1_relat_1(X5) )
      & ( r2_hidden(k4_tarski(esk1_3(X5,X10,X11),X10),X5)
        | r2_hidden(esk1_3(X5,X10,X11),X11)
        | X11 = k1_wellord1(X5,X10)
        | ~ v1_relat_1(X5) ) ) ),
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
    | ~ r2_hidden(X1,k1_wellord1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(er,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X13,X14,X15,X16,X17] :
      ( ( ~ r1_tarski(X13,X14)
        | ~ r2_hidden(X15,X13)
        | r2_hidden(X15,X14) )
      & ( r2_hidden(esk2_2(X16,X17),X16)
        | r1_tarski(X16,X17) )
      & ( ~ r2_hidden(esk2_2(X16,X17),X17)
        | r1_tarski(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_27,plain,
    ( X1 = X2
    | r2_hidden(X1,k1_wellord1(X3,X2))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( esk12_0 = esk11_0
    | r2_hidden(k4_tarski(esk12_0,esk11_0),esk13_0)
    | r2_hidden(k4_tarski(esk11_0,esk12_0),esk13_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v8_relat_2(X3)
    | ~ r2_hidden(k4_tarski(X1,X4),X3)
    | ~ r2_hidden(X4,k1_wellord1(X3,X2))
    | ~ v1_relat_1(X3) ),
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
    ( ~ r2_hidden(X1,k1_wellord1(X2,X1))
    | ~ v1_relat_1(X2) ),
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
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
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
    ( esk2_2(X1,k1_wellord1(esk13_0,esk12_0)) = esk12_0
    | esk12_0 = esk11_0
    | r1_tarski(X1,k1_wellord1(esk13_0,esk12_0))
    | ~ v8_relat_2(esk13_0)
    | ~ r2_hidden(esk2_2(X1,k1_wellord1(esk13_0,esk12_0)),k1_wellord1(esk13_0,esk11_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_54,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_55,plain,
    ( X1 = X2
    | ~ v4_relat_2(X3)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,k1_wellord1(X3,X1))
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_52,c_0_25])).

cnf(c_0_56,negated_conjecture,
    ( esk2_2(k1_wellord1(esk13_0,esk11_0),k1_wellord1(esk13_0,esk12_0)) = esk12_0
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
    | r1_tarski(k1_wellord1(esk13_0,esk11_0),k1_wellord1(esk13_0,esk12_0))
    | r2_hidden(esk12_0,k1_wellord1(esk13_0,esk11_0))
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
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_65]),c_0_66]),c_0_65])])).

cnf(c_0_69,plain,
    ( r2_hidden(k4_tarski(X2,X2),X1)
    | ~ v1_relat_2(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_70,negated_conjecture,
    ( ~ v1_relat_2(esk13_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_23]),c_0_13])])).

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
