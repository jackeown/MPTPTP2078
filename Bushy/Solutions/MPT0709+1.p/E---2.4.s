%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_1__t164_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:18 EDT 2019

% Result     : Theorem 151.41s
% Output     : CNFRefutation 151.41s
% Verified   : 
% Statistics : Number of formulae       :   36 (  83 expanded)
%              Number of clauses        :   23 (  33 expanded)
%              Number of leaves         :    6 (  20 expanded)
%              Depth                    :   10
%              Number of atoms          :  195 ( 396 expanded)
%              Number of equality atoms :   34 (  61 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   44 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t164_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ( r1_tarski(X1,k1_relat_1(X2))
          & v2_funct_1(X2) )
       => k10_relat_1(X2,k9_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t164_funct_1.p',t164_funct_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t164_funct_1.p',d3_tarski)).

fof(d12_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( X3 = k9_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(X5,k1_relat_1(X1))
                  & r2_hidden(X5,X2)
                  & X4 = k1_funct_1(X1,X5) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t164_funct_1.p',d12_funct_1)).

fof(d13_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( X3 = k10_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ( r2_hidden(X4,k1_relat_1(X1))
                & r2_hidden(k1_funct_1(X1,X4),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t164_funct_1.p',d13_funct_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t164_funct_1.p',d10_xboole_0)).

fof(t152_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v2_funct_1(X2)
       => r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t164_funct_1.p',t152_funct_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( ( r1_tarski(X1,k1_relat_1(X2))
            & v2_funct_1(X2) )
         => k10_relat_1(X2,k9_relat_1(X2,X1)) = X1 ) ) ),
    inference(assume_negation,[status(cth)],[t164_funct_1])).

fof(c_0_7,plain,(
    ! [X32,X33,X34,X35,X36] :
      ( ( ~ r1_tarski(X32,X33)
        | ~ r2_hidden(X34,X32)
        | r2_hidden(X34,X33) )
      & ( r2_hidden(esk7_2(X35,X36),X35)
        | r1_tarski(X35,X36) )
      & ( ~ r2_hidden(esk7_2(X35,X36),X36)
        | r1_tarski(X35,X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_8,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & r1_tarski(esk1_0,k1_relat_1(esk2_0))
    & v2_funct_1(esk2_0)
    & k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)) != esk1_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_9,plain,(
    ! [X12,X13,X14,X15,X17,X18,X19,X20,X22] :
      ( ( r2_hidden(esk3_4(X12,X13,X14,X15),k1_relat_1(X12))
        | ~ r2_hidden(X15,X14)
        | X14 != k9_relat_1(X12,X13)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( r2_hidden(esk3_4(X12,X13,X14,X15),X13)
        | ~ r2_hidden(X15,X14)
        | X14 != k9_relat_1(X12,X13)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( X15 = k1_funct_1(X12,esk3_4(X12,X13,X14,X15))
        | ~ r2_hidden(X15,X14)
        | X14 != k9_relat_1(X12,X13)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( ~ r2_hidden(X18,k1_relat_1(X12))
        | ~ r2_hidden(X18,X13)
        | X17 != k1_funct_1(X12,X18)
        | r2_hidden(X17,X14)
        | X14 != k9_relat_1(X12,X13)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( ~ r2_hidden(esk4_3(X12,X19,X20),X20)
        | ~ r2_hidden(X22,k1_relat_1(X12))
        | ~ r2_hidden(X22,X19)
        | esk4_3(X12,X19,X20) != k1_funct_1(X12,X22)
        | X20 = k9_relat_1(X12,X19)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( r2_hidden(esk5_3(X12,X19,X20),k1_relat_1(X12))
        | r2_hidden(esk4_3(X12,X19,X20),X20)
        | X20 = k9_relat_1(X12,X19)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( r2_hidden(esk5_3(X12,X19,X20),X19)
        | r2_hidden(esk4_3(X12,X19,X20),X20)
        | X20 = k9_relat_1(X12,X19)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( esk4_3(X12,X19,X20) = k1_funct_1(X12,esk5_3(X12,X19,X20))
        | r2_hidden(esk4_3(X12,X19,X20),X20)
        | X20 = k9_relat_1(X12,X19)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).

cnf(c_0_10,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( r1_tarski(esk1_0,k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X24,X25,X26,X27,X28,X29,X30] :
      ( ( r2_hidden(X27,k1_relat_1(X24))
        | ~ r2_hidden(X27,X26)
        | X26 != k10_relat_1(X24,X25)
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) )
      & ( r2_hidden(k1_funct_1(X24,X27),X25)
        | ~ r2_hidden(X27,X26)
        | X26 != k10_relat_1(X24,X25)
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) )
      & ( ~ r2_hidden(X28,k1_relat_1(X24))
        | ~ r2_hidden(k1_funct_1(X24,X28),X25)
        | r2_hidden(X28,X26)
        | X26 != k10_relat_1(X24,X25)
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) )
      & ( ~ r2_hidden(esk6_3(X24,X29,X30),X30)
        | ~ r2_hidden(esk6_3(X24,X29,X30),k1_relat_1(X24))
        | ~ r2_hidden(k1_funct_1(X24,esk6_3(X24,X29,X30)),X29)
        | X30 = k10_relat_1(X24,X29)
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) )
      & ( r2_hidden(esk6_3(X24,X29,X30),k1_relat_1(X24))
        | r2_hidden(esk6_3(X24,X29,X30),X30)
        | X30 = k10_relat_1(X24,X29)
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) )
      & ( r2_hidden(k1_funct_1(X24,esk6_3(X24,X29,X30)),X29)
        | r2_hidden(esk6_3(X24,X29,X30),X30)
        | X30 = k10_relat_1(X24,X29)
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_funct_1])])])])])])).

cnf(c_0_13,plain,
    ( r2_hidden(X4,X5)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,X3)
    | X4 != k1_funct_1(X2,X1)
    | X5 != k9_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(esk2_0))
    | ~ r2_hidden(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,plain,
    ( r2_hidden(esk7_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k1_funct_1(X2,X1),X3)
    | X4 != k10_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k9_relat_1(X1,X3))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_13])])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk7_2(esk1_0,X1),k1_relat_1(esk2_0))
    | r1_tarski(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ r2_hidden(k1_funct_1(X2,X1),X3)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk2_0,esk7_2(esk1_0,X1)),k9_relat_1(esk2_0,X2))
    | r1_tarski(esk1_0,X1)
    | ~ r2_hidden(esk7_2(esk1_0,X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20])])).

fof(c_0_23,plain,(
    ! [X10,X11] :
      ( ( r1_tarski(X10,X11)
        | X10 != X11 )
      & ( r1_tarski(X11,X10)
        | X10 != X11 )
      & ( ~ r1_tarski(X10,X11)
        | ~ r1_tarski(X11,X10)
        | X10 = X11 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_24,plain,(
    ! [X40,X41] :
      ( ~ v1_relat_1(X41)
      | ~ v1_funct_1(X41)
      | ~ v2_funct_1(X41)
      | r1_tarski(k10_relat_1(X41,k9_relat_1(X41,X40)),X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t152_funct_1])])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk7_2(esk1_0,X1),k10_relat_1(esk2_0,X2))
    | r1_tarski(esk1_0,X1)
    | ~ r2_hidden(k1_funct_1(esk2_0,esk7_2(esk1_0,X1)),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk2_0,esk7_2(esk1_0,X1)),k9_relat_1(esk2_0,esk1_0))
    | r1_tarski(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_15])).

cnf(c_0_27,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk7_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk7_2(esk1_0,X1),k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)))
    | r1_tarski(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,plain,
    ( k10_relat_1(X1,k9_relat_1(X1,X2)) = X2
    | ~ v2_funct_1(X1)
    | ~ r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( v2_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_34,negated_conjecture,
    ( k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)) != esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_35,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_19]),c_0_20])]),c_0_34]),
    [proof]).
%------------------------------------------------------------------------------
