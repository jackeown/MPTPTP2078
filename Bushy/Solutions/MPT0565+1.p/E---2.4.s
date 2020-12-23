%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relat_1__t169_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:53 EDT 2019

% Result     : Theorem 153.43s
% Output     : CNFRefutation 153.43s
% Verified   : 
% Statistics : Number of formulae       :   37 (  87 expanded)
%              Number of clauses        :   22 (  40 expanded)
%              Number of leaves         :    7 (  20 expanded)
%              Depth                    :   12
%              Number of atoms          :  134 ( 263 expanded)
%              Number of equality atoms :   31 (  69 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t169_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t169_relat_1.p',t169_relat_1)).

fof(t167_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t169_relat_1.p',t167_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t169_relat_1.p',d10_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t169_relat_1.p',d3_tarski)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t169_relat_1.p',d4_relat_1)).

fof(d14_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k10_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(k4_tarski(X4,X5),X1)
                  & r2_hidden(X5,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t169_relat_1.p',d14_relat_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t169_relat_1.p',d5_relat_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    inference(assume_negation,[status(cth)],[t169_relat_1])).

fof(c_0_8,plain,(
    ! [X53,X54] :
      ( ~ v1_relat_1(X54)
      | r1_tarski(k10_relat_1(X54,X53),k1_relat_1(X54)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).

fof(c_0_9,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & k10_relat_1(esk1_0,k2_relat_1(esk1_0)) != k1_relat_1(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X9,X10] :
      ( ( r1_tarski(X9,X10)
        | X9 != X10 )
      & ( r1_tarski(X10,X9)
        | X9 != X10 )
      & ( ~ r1_tarski(X9,X10)
        | ~ r1_tarski(X10,X9)
        | X9 = X10 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_11,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk1_0,X1),k1_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

fof(c_0_15,plain,(
    ! [X23,X24,X25,X26,X27] :
      ( ( ~ r1_tarski(X23,X24)
        | ~ r2_hidden(X25,X23)
        | r2_hidden(X25,X24) )
      & ( r2_hidden(esk5_2(X26,X27),X26)
        | r1_tarski(X26,X27) )
      & ( ~ r2_hidden(esk5_2(X26,X27),X27)
        | r1_tarski(X26,X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_16,plain,(
    ! [X29,X30,X31,X33,X34,X35,X36,X38] :
      ( ( ~ r2_hidden(X31,X30)
        | r2_hidden(k4_tarski(X31,esk6_3(X29,X30,X31)),X29)
        | X30 != k1_relat_1(X29) )
      & ( ~ r2_hidden(k4_tarski(X33,X34),X29)
        | r2_hidden(X33,X30)
        | X30 != k1_relat_1(X29) )
      & ( ~ r2_hidden(esk7_2(X35,X36),X36)
        | ~ r2_hidden(k4_tarski(esk7_2(X35,X36),X38),X35)
        | X36 = k1_relat_1(X35) )
      & ( r2_hidden(esk7_2(X35,X36),X36)
        | r2_hidden(k4_tarski(esk7_2(X35,X36),esk8_2(X35,X36)),X35)
        | X36 = k1_relat_1(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_17,negated_conjecture,
    ( k1_relat_1(esk1_0) = k10_relat_1(esk1_0,X1)
    | ~ r1_tarski(k1_relat_1(esk1_0),k10_relat_1(esk1_0,X1)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,plain,
    ( r2_hidden(esk5_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X11,X12,X13,X14,X16,X17,X18,X19,X21] :
      ( ( r2_hidden(k4_tarski(X14,esk2_4(X11,X12,X13,X14)),X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k10_relat_1(X11,X12)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(esk2_4(X11,X12,X13,X14),X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k10_relat_1(X11,X12)
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(k4_tarski(X16,X17),X11)
        | ~ r2_hidden(X17,X12)
        | r2_hidden(X16,X13)
        | X13 != k10_relat_1(X11,X12)
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(esk3_3(X11,X18,X19),X19)
        | ~ r2_hidden(k4_tarski(esk3_3(X11,X18,X19),X21),X11)
        | ~ r2_hidden(X21,X18)
        | X19 = k10_relat_1(X11,X18)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(k4_tarski(esk3_3(X11,X18,X19),esk4_3(X11,X18,X19)),X11)
        | r2_hidden(esk3_3(X11,X18,X19),X19)
        | X19 = k10_relat_1(X11,X18)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(esk4_3(X11,X18,X19),X18)
        | r2_hidden(esk3_3(X11,X18,X19),X19)
        | X19 = k10_relat_1(X11,X18)
        | ~ v1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(X1,esk6_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( k10_relat_1(esk1_0,k2_relat_1(esk1_0)) != k1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,negated_conjecture,
    ( k1_relat_1(esk1_0) = k10_relat_1(esk1_0,X1)
    | r2_hidden(esk5_2(k1_relat_1(esk1_0),k10_relat_1(esk1_0,X1)),k1_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_23,plain,(
    ! [X40,X41,X42,X44,X45,X46,X47,X49] :
      ( ( ~ r2_hidden(X42,X41)
        | r2_hidden(k4_tarski(esk9_3(X40,X41,X42),X42),X40)
        | X41 != k2_relat_1(X40) )
      & ( ~ r2_hidden(k4_tarski(X45,X44),X40)
        | r2_hidden(X44,X41)
        | X41 != k2_relat_1(X40) )
      & ( ~ r2_hidden(esk10_2(X46,X47),X47)
        | ~ r2_hidden(k4_tarski(X49,esk10_2(X46,X47)),X46)
        | X47 = k2_relat_1(X46) )
      & ( r2_hidden(esk10_2(X46,X47),X47)
        | r2_hidden(k4_tarski(esk11_2(X46,X47),esk10_2(X46,X47)),X46)
        | X47 = k2_relat_1(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X5 != k10_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( r2_hidden(k4_tarski(X1,esk6_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk5_2(k1_relat_1(esk1_0),k10_relat_1(esk1_0,k2_relat_1(esk1_0))),k1_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,X3)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_2(k1_relat_1(esk1_0),k10_relat_1(esk1_0,k2_relat_1(esk1_0))),esk6_3(esk1_0,k1_relat_1(esk1_0),esk5_2(k1_relat_1(esk1_0),k10_relat_1(esk1_0,k2_relat_1(esk1_0))))),esk1_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk5_2(k1_relat_1(esk1_0),k10_relat_1(esk1_0,k2_relat_1(esk1_0))),k10_relat_1(esk1_0,X1))
    | ~ r2_hidden(esk6_3(esk1_0,k1_relat_1(esk1_0),esk5_2(k1_relat_1(esk1_0),k10_relat_1(esk1_0,k2_relat_1(esk1_0)))),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_12])])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk6_3(esk1_0,k1_relat_1(esk1_0),esk5_2(k1_relat_1(esk1_0),k10_relat_1(esk1_0,k2_relat_1(esk1_0)))),k2_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_29])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk5_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk5_2(k1_relat_1(esk1_0),k10_relat_1(esk1_0,k2_relat_1(esk1_0))),k10_relat_1(esk1_0,k2_relat_1(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk1_0),k10_relat_1(esk1_0,k2_relat_1(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_35]),c_0_14])]),c_0_21]),
    [proof]).
%------------------------------------------------------------------------------
