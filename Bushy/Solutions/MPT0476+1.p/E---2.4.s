%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relat_1__t71_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:04 EDT 2019

% Result     : Theorem 267.30s
% Output     : CNFRefutation 267.30s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 220 expanded)
%              Number of clauses        :   29 ( 113 expanded)
%              Number of leaves         :    5 (  53 expanded)
%              Depth                    :   11
%              Number of atoms          :  141 (1124 expanded)
%              Number of equality atoms :   59 ( 401 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( X2 = k6_relat_1(X1)
      <=> ! [X3,X4] :
            ( r2_hidden(k4_tarski(X3,X4),X2)
          <=> ( r2_hidden(X3,X1)
              & X3 = X4 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t71_relat_1.p',d10_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t71_relat_1.p',dt_k6_relat_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t71_relat_1.p',d5_relat_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t71_relat_1.p',d4_relat_1)).

fof(t71_relat_1,conjecture,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t71_relat_1.p',t71_relat_1)).

fof(c_0_5,plain,(
    ! [X8,X9,X10,X11,X12,X13] :
      ( ( r2_hidden(X10,X8)
        | ~ r2_hidden(k4_tarski(X10,X11),X9)
        | X9 != k6_relat_1(X8)
        | ~ v1_relat_1(X9) )
      & ( X10 = X11
        | ~ r2_hidden(k4_tarski(X10,X11),X9)
        | X9 != k6_relat_1(X8)
        | ~ v1_relat_1(X9) )
      & ( ~ r2_hidden(X12,X8)
        | X12 != X13
        | r2_hidden(k4_tarski(X12,X13),X9)
        | X9 != k6_relat_1(X8)
        | ~ v1_relat_1(X9) )
      & ( ~ r2_hidden(k4_tarski(esk2_2(X8,X9),esk3_2(X8,X9)),X9)
        | ~ r2_hidden(esk2_2(X8,X9),X8)
        | esk2_2(X8,X9) != esk3_2(X8,X9)
        | X9 = k6_relat_1(X8)
        | ~ v1_relat_1(X9) )
      & ( r2_hidden(esk2_2(X8,X9),X8)
        | r2_hidden(k4_tarski(esk2_2(X8,X9),esk3_2(X8,X9)),X9)
        | X9 = k6_relat_1(X8)
        | ~ v1_relat_1(X9) )
      & ( esk2_2(X8,X9) = esk3_2(X8,X9)
        | r2_hidden(k4_tarski(esk2_2(X8,X9),esk3_2(X8,X9)),X9)
        | X9 = k6_relat_1(X8)
        | ~ v1_relat_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_relat_1])])])])])])).

fof(c_0_6,plain,(
    ! [X46] : v1_relat_1(k6_relat_1(X46)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

cnf(c_0_7,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X3 != k6_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,plain,(
    ! [X35,X36,X37,X39,X40,X41,X42,X44] :
      ( ( ~ r2_hidden(X37,X36)
        | r2_hidden(k4_tarski(esk8_3(X35,X36,X37),X37),X35)
        | X36 != k2_relat_1(X35) )
      & ( ~ r2_hidden(k4_tarski(X40,X39),X35)
        | r2_hidden(X39,X36)
        | X36 != k2_relat_1(X35) )
      & ( ~ r2_hidden(esk9_2(X41,X42),X42)
        | ~ r2_hidden(k4_tarski(X44,esk9_2(X41,X42)),X41)
        | X42 = k2_relat_1(X41) )
      & ( r2_hidden(esk9_2(X41,X42),X42)
        | r2_hidden(k4_tarski(esk10_2(X41,X42),esk9_2(X41,X42)),X41)
        | X42 = k2_relat_1(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X4)
    | X4 != k6_relat_1(X2)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

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
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X2),k6_relat_1(X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_7]),c_0_8])])).

cnf(c_0_13,plain,
    ( r2_hidden(esk9_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk10_2(X1,X2),esk9_2(X1,X2)),X1)
    | X2 = k2_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(X1,X3),X4)
    | ~ r2_hidden(X1,X2)
    | X1 != X3
    | X4 != k6_relat_1(X2)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_10]),c_0_8])])).

cnf(c_0_16,plain,
    ( r2_hidden(esk6_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk6_2(X1,X2),esk7_2(X1,X2)),X1)
    | X2 = k1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( X2 = k2_relat_1(X1)
    | ~ r2_hidden(esk9_2(X1,X2),X2)
    | ~ r2_hidden(k4_tarski(X3,esk9_2(X1,X2)),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( esk10_2(k6_relat_1(X1),X2) = esk9_2(k6_relat_1(X1),X2)
    | X2 = k2_relat_1(k6_relat_1(X1))
    | r2_hidden(esk9_2(k6_relat_1(X1),X2),X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,plain,
    ( r2_hidden(k4_tarski(X1,X1),X2)
    | X2 != k6_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( X1 = k1_relat_1(k6_relat_1(X2))
    | r2_hidden(esk6_2(k6_relat_1(X2),X1),X1)
    | r2_hidden(esk6_2(k6_relat_1(X2),X1),X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,plain,
    ( esk10_2(k6_relat_1(X1),X2) = esk9_2(k6_relat_1(X1),X2)
    | X2 = k2_relat_1(k6_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X3,esk9_2(k6_relat_1(X1),X2)),k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( r2_hidden(k4_tarski(X1,X1),k6_relat_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_19]),c_0_8])])).

cnf(c_0_24,plain,
    ( X2 = k1_relat_1(X1)
    | ~ r2_hidden(esk6_2(X1,X2),X2)
    | ~ r2_hidden(k4_tarski(esk6_2(X1,X2),X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_25,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1
    | r2_hidden(esk6_2(k6_relat_1(X1),X1),X1) ),
    inference(ef,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( esk10_2(k6_relat_1(X1),X2) = esk9_2(k6_relat_1(X1),X2)
    | X2 = k2_relat_1(k6_relat_1(X1))
    | ~ r2_hidden(esk9_2(k6_relat_1(X1),X2),X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1
    | ~ r2_hidden(k4_tarski(esk6_2(k6_relat_1(X1),X1),X2),k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_29,negated_conjecture,(
    ~ ! [X1] :
        ( k1_relat_1(k6_relat_1(X1)) = X1
        & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    inference(assume_negation,[status(cth)],[t71_relat_1])).

cnf(c_0_30,plain,
    ( X1 = k2_relat_1(X2)
    | r2_hidden(esk10_2(X2,X1),k1_relat_1(X2))
    | r2_hidden(esk9_2(X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_13])).

cnf(c_0_31,plain,
    ( esk10_2(k6_relat_1(X1),X1) = esk9_2(k6_relat_1(X1),X1)
    | k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_27,c_0_18])).

cnf(c_0_32,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_23]),c_0_25])).

fof(c_0_33,negated_conjecture,
    ( k1_relat_1(k6_relat_1(esk1_0)) != esk1_0
    | k2_relat_1(k6_relat_1(esk1_0)) != esk1_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).

cnf(c_0_34,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1
    | r2_hidden(esk9_2(k6_relat_1(X1),X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])])).

cnf(c_0_35,negated_conjecture,
    ( k1_relat_1(k6_relat_1(esk1_0)) != esk1_0
    | k2_relat_1(k6_relat_1(esk1_0)) != esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_36,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1
    | ~ r2_hidden(k4_tarski(X2,esk9_2(k6_relat_1(X1),X1)),k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( k2_relat_1(k6_relat_1(esk1_0)) != esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_32])])).

cnf(c_0_38,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_23]),c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38])]),
    [proof]).
%------------------------------------------------------------------------------
