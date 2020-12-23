%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0950+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:27 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   80 (1614 expanded)
%              Number of clauses        :   49 ( 652 expanded)
%              Number of leaves         :   15 ( 401 expanded)
%              Depth                    :   20
%              Number of atoms          :  273 (5098 expanded)
%              Number of equality atoms :   30 ( 458 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   33 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t17_wellord2,conjecture,(
    ! [X1,X2] :
      ( v3_ordinal1(X2)
     => ( r1_tarski(X1,X2)
       => r1_ordinal1(k2_wellord2(k1_wellord2(X1)),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_wellord2)).

fof(connectedness_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
        | r1_ordinal1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(d1_wellord2,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( X2 = k1_wellord2(X1)
      <=> ( k3_relat_1(X2) = X1
          & ! [X3,X4] :
              ( ( r2_hidden(X3,X1)
                & r2_hidden(X4,X1) )
             => ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> r1_tarski(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

fof(dt_k1_wellord2,axiom,(
    ! [X1] : v1_relat_1(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(t64_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ~ ( r1_tarski(X1,k3_relat_1(X2))
          & v2_wellord1(X2)
          & ~ r4_wellord1(X2,k2_wellord1(X2,X1))
          & ! [X3] :
              ~ ( r2_hidden(X3,k3_relat_1(X2))
                & r4_wellord1(k2_wellord1(X2,k1_wellord1(X2,X3)),k2_wellord1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_wellord1)).

fof(t9_wellord2,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( r1_tarski(X2,X1)
         => v2_wellord1(k1_wellord2(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_wellord2)).

fof(cc5_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,X1)
         => v3_ordinal1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_ordinal1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(t8_wellord2,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_wellord1(k1_wellord2(X2),X1) = k1_wellord2(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).

fof(t10_wellord2,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,X2)
           => X1 = k1_wellord1(k1_wellord2(X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord2)).

fof(d2_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
         => r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

fof(cc1_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v1_ordinal1(X1)
        & v2_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(t50_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r4_wellord1(X1,X2)
           => r4_wellord1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).

fof(d2_wellord2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ( X2 = k2_wellord2(X1)
            <=> r4_wellord1(X1,k1_wellord2(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_wellord2)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v3_ordinal1(X2)
       => ( r1_tarski(X1,X2)
         => r1_ordinal1(k2_wellord2(k1_wellord2(X1)),X2) ) ) ),
    inference(assume_negation,[status(cth)],[t17_wellord2])).

fof(c_0_16,plain,(
    ! [X8,X9] :
      ( ~ v3_ordinal1(X8)
      | ~ v3_ordinal1(X9)
      | r1_ordinal1(X8,X9)
      | r1_ordinal1(X9,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[connectedness_r1_ordinal1])])).

fof(c_0_17,negated_conjecture,
    ( v3_ordinal1(esk6_0)
    & r1_tarski(esk5_0,esk6_0)
    & ~ r1_ordinal1(k2_wellord2(k1_wellord2(esk5_0)),esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

cnf(c_0_18,plain,
    ( r1_ordinal1(X1,X2)
    | r1_ordinal1(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( v3_ordinal1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_20,plain,(
    ! [X10,X11,X12,X13] :
      ( ( k3_relat_1(X11) = X10
        | X11 != k1_wellord2(X10)
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(k4_tarski(X12,X13),X11)
        | r1_tarski(X12,X13)
        | ~ r2_hidden(X12,X10)
        | ~ r2_hidden(X13,X10)
        | X11 != k1_wellord2(X10)
        | ~ v1_relat_1(X11) )
      & ( ~ r1_tarski(X12,X13)
        | r2_hidden(k4_tarski(X12,X13),X11)
        | ~ r2_hidden(X12,X10)
        | ~ r2_hidden(X13,X10)
        | X11 != k1_wellord2(X10)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | k3_relat_1(X11) != X10
        | X11 = k1_wellord2(X10)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(esk2_2(X10,X11),X10)
        | k3_relat_1(X11) != X10
        | X11 = k1_wellord2(X10)
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X10,X11),esk2_2(X10,X11)),X11)
        | ~ r1_tarski(esk1_2(X10,X11),esk2_2(X10,X11))
        | k3_relat_1(X11) != X10
        | X11 = k1_wellord2(X10)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(k4_tarski(esk1_2(X10,X11),esk2_2(X10,X11)),X11)
        | r1_tarski(esk1_2(X10,X11),esk2_2(X10,X11))
        | k3_relat_1(X11) != X10
        | X11 = k1_wellord2(X10)
        | ~ v1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).

fof(c_0_21,plain,(
    ! [X22] : v1_relat_1(k1_wellord2(X22)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_22,plain,(
    ! [X24,X25] :
      ( ( ~ r1_ordinal1(X24,X25)
        | r1_tarski(X24,X25)
        | ~ v3_ordinal1(X24)
        | ~ v3_ordinal1(X25) )
      & ( ~ r1_tarski(X24,X25)
        | r1_ordinal1(X24,X25)
        | ~ v3_ordinal1(X24)
        | ~ v3_ordinal1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_23,negated_conjecture,
    ( r1_ordinal1(X1,esk6_0)
    | r1_ordinal1(esk6_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_24,plain,(
    ! [X36,X37] :
      ( ( r2_hidden(esk4_2(X36,X37),k3_relat_1(X37))
        | ~ r1_tarski(X36,k3_relat_1(X37))
        | ~ v2_wellord1(X37)
        | r4_wellord1(X37,k2_wellord1(X37,X36))
        | ~ v1_relat_1(X37) )
      & ( r4_wellord1(k2_wellord1(X37,k1_wellord1(X37,esk4_2(X36,X37))),k2_wellord1(X37,X36))
        | ~ r1_tarski(X36,k3_relat_1(X37))
        | ~ v2_wellord1(X37)
        | r4_wellord1(X37,k2_wellord1(X37,X36))
        | ~ v1_relat_1(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t64_wellord1])])])])])).

cnf(c_0_25,plain,
    ( k3_relat_1(X1) = X2
    | X1 != k1_wellord2(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_27,plain,(
    ! [X45,X46] :
      ( ~ v3_ordinal1(X45)
      | ~ r1_tarski(X46,X45)
      | v2_wellord1(k1_wellord2(X46)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_wellord2])])])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( r1_ordinal1(esk6_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_19])).

cnf(c_0_30,plain,
    ( r2_hidden(esk4_2(X1,X2),k3_relat_1(X2))
    | r4_wellord1(X2,k2_wellord1(X2,X1))
    | ~ r1_tarski(X1,k3_relat_1(X2))
    | ~ v2_wellord1(X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( k3_relat_1(k1_wellord2(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_25]),c_0_26])])).

cnf(c_0_32,plain,
    ( v2_wellord1(k1_wellord2(X2))
    | ~ v3_ordinal1(X1)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk6_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_19])])).

cnf(c_0_34,plain,
    ( r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,esk4_2(X2,X1))),k2_wellord1(X1,X2))
    | r4_wellord1(X1,k2_wellord1(X1,X2))
    | ~ r1_tarski(X2,k3_relat_1(X1))
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),X2))
    | r2_hidden(esk4_2(X2,k1_wellord2(X1)),X1)
    | ~ v2_wellord1(k1_wellord2(X1))
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_26])])).

cnf(c_0_36,negated_conjecture,
    ( v2_wellord1(k1_wellord2(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_19])])).

cnf(c_0_37,plain,
    ( r4_wellord1(k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),esk4_2(X2,k1_wellord2(X1)))),k2_wellord1(k1_wellord2(X1),X2))
    | r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),X2))
    | ~ v2_wellord1(k1_wellord2(X1))
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_31]),c_0_26])])).

fof(c_0_38,plain,(
    ! [X6,X7] :
      ( ~ v3_ordinal1(X6)
      | ~ m1_subset_1(X7,X6)
      | v3_ordinal1(X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc5_ordinal1])])])).

fof(c_0_39,plain,(
    ! [X28,X29] :
      ( ~ r2_hidden(X28,X29)
      | m1_subset_1(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_40,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk6_0),k2_wellord1(k1_wellord2(esk6_0),X1))
    | r2_hidden(esk4_2(X1,k1_wellord2(esk6_0)),esk6_0)
    | ~ r1_tarski(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_42,plain,(
    ! [X43,X44] :
      ( ~ r1_tarski(X43,X44)
      | k2_wellord1(k1_wellord2(X44),X43) = k1_wellord2(X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_wellord2])])).

cnf(c_0_43,negated_conjecture,
    ( r4_wellord1(k2_wellord1(k1_wellord2(esk6_0),k1_wellord1(k1_wellord2(esk6_0),esk4_2(X1,k1_wellord2(esk6_0)))),k2_wellord1(k1_wellord2(esk6_0),X1))
    | r4_wellord1(k1_wellord2(esk6_0),k2_wellord1(k1_wellord2(esk6_0),X1))
    | ~ r1_tarski(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_36])).

fof(c_0_44,plain,(
    ! [X26,X27] :
      ( ~ v3_ordinal1(X26)
      | ~ v3_ordinal1(X27)
      | ~ r2_hidden(X26,X27)
      | X26 = k1_wellord1(k1_wellord2(X27),X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_wellord2])])])).

cnf(c_0_45,plain,
    ( v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_47,plain,(
    ! [X16,X17,X18] :
      ( ( ~ v1_ordinal1(X16)
        | ~ r2_hidden(X17,X16)
        | r1_tarski(X17,X16) )
      & ( r2_hidden(esk3_1(X18),X18)
        | v1_ordinal1(X18) )
      & ( ~ r1_tarski(esk3_1(X18),X18)
        | v1_ordinal1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).

cnf(c_0_48,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk6_0),k2_wellord1(k1_wellord2(esk6_0),esk5_0))
    | r2_hidden(esk4_2(esk5_0,k1_wellord2(esk6_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_49,plain,
    ( k2_wellord1(k1_wellord2(X2),X1) = k1_wellord2(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( r4_wellord1(k2_wellord1(k1_wellord2(esk6_0),k1_wellord1(k1_wellord2(esk6_0),esk4_2(esk5_0,k1_wellord2(esk6_0)))),k2_wellord1(k1_wellord2(esk6_0),esk5_0))
    | r4_wellord1(k1_wellord2(esk6_0),k2_wellord1(k1_wellord2(esk6_0),esk5_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_41])).

cnf(c_0_51,plain,
    ( X1 = k1_wellord1(k1_wellord2(X2),X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,plain,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,X2)
    | ~ v3_ordinal1(X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,plain,
    ( r1_tarski(X2,X1)
    | ~ v1_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk6_0),k1_wellord2(esk5_0))
    | r2_hidden(esk4_2(esk5_0,k1_wellord2(esk6_0)),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_41])])).

fof(c_0_55,plain,(
    ! [X5] :
      ( ( v1_ordinal1(X5)
        | ~ v3_ordinal1(X5) )
      & ( v2_ordinal1(X5)
        | ~ v3_ordinal1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).

cnf(c_0_56,negated_conjecture,
    ( r4_wellord1(k2_wellord1(k1_wellord2(esk6_0),k1_wellord1(k1_wellord2(esk6_0),esk4_2(esk5_0,k1_wellord2(esk6_0)))),k1_wellord2(esk5_0))
    | r4_wellord1(k1_wellord2(esk6_0),k1_wellord2(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_49]),c_0_41])])).

cnf(c_0_57,plain,
    ( k1_wellord1(k1_wellord2(X1),X2) = X2
    | ~ r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1) ),
    inference(csr,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk6_0),k1_wellord2(esk5_0))
    | r1_tarski(esk4_2(esk5_0,k1_wellord2(esk6_0)),esk6_0)
    | ~ v1_ordinal1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_59,plain,
    ( v1_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

fof(c_0_60,plain,(
    ! [X34,X35] :
      ( ~ v1_relat_1(X34)
      | ~ v1_relat_1(X35)
      | ~ r4_wellord1(X34,X35)
      | r4_wellord1(X35,X34) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_wellord1])])])).

cnf(c_0_61,negated_conjecture,
    ( r4_wellord1(k2_wellord1(k1_wellord2(esk6_0),esk4_2(esk5_0,k1_wellord2(esk6_0))),k1_wellord2(esk5_0))
    | r4_wellord1(k1_wellord2(esk6_0),k1_wellord2(esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_19])]),c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk6_0),k1_wellord2(esk5_0))
    | r1_tarski(esk4_2(esk5_0,k1_wellord2(esk6_0)),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_19])])).

fof(c_0_63,plain,(
    ! [X20,X21] :
      ( ( X21 != k2_wellord2(X20)
        | r4_wellord1(X20,k1_wellord2(X21))
        | ~ v3_ordinal1(X21)
        | ~ v2_wellord1(X20)
        | ~ v1_relat_1(X20) )
      & ( ~ r4_wellord1(X20,k1_wellord2(X21))
        | X21 = k2_wellord2(X20)
        | ~ v3_ordinal1(X21)
        | ~ v2_wellord1(X20)
        | ~ v1_relat_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_wellord2])])])])).

cnf(c_0_64,plain,
    ( r4_wellord1(X2,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r4_wellord1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk4_2(esk5_0,k1_wellord2(esk6_0))),k1_wellord2(esk5_0))
    | r4_wellord1(k1_wellord2(esk6_0),k1_wellord2(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_49]),c_0_62])).

cnf(c_0_66,plain,
    ( X2 = k2_wellord2(X1)
    | ~ r4_wellord1(X1,k1_wellord2(X2))
    | ~ v3_ordinal1(X2)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk5_0),k1_wellord2(esk4_2(esk5_0,k1_wellord2(esk6_0))))
    | r4_wellord1(k1_wellord2(esk6_0),k1_wellord2(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_26]),c_0_26])])).

cnf(c_0_68,negated_conjecture,
    ( v2_wellord1(k1_wellord2(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_41]),c_0_19])])).

cnf(c_0_69,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk6_0),k1_wellord2(esk5_0))
    | v3_ordinal1(esk4_2(esk5_0,k1_wellord2(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_54]),c_0_19])])).

cnf(c_0_70,negated_conjecture,
    ( ~ r1_ordinal1(k2_wellord2(k1_wellord2(esk5_0)),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_71,plain,
    ( r1_ordinal1(X1,X2)
    | ~ r1_tarski(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_72,negated_conjecture,
    ( esk4_2(esk5_0,k1_wellord2(esk6_0)) = k2_wellord2(k1_wellord2(esk5_0))
    | r4_wellord1(k1_wellord2(esk6_0),k1_wellord2(esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68]),c_0_26])]),c_0_69])).

cnf(c_0_73,negated_conjecture,
    ( ~ r1_tarski(k2_wellord2(k1_wellord2(esk5_0)),esk6_0)
    | ~ v3_ordinal1(k2_wellord2(k1_wellord2(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_19])])).

cnf(c_0_74,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk6_0),k1_wellord2(esk5_0))
    | r1_tarski(k2_wellord2(k1_wellord2(esk5_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_72])).

cnf(c_0_75,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk6_0),k1_wellord2(esk5_0))
    | v3_ordinal1(k2_wellord2(k1_wellord2(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_72])).

cnf(c_0_76,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk6_0),k1_wellord2(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75])).

cnf(c_0_77,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk5_0),k1_wellord2(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_76]),c_0_26]),c_0_26])])).

cnf(c_0_78,negated_conjecture,
    ( k2_wellord2(k1_wellord2(esk5_0)) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_77]),c_0_68]),c_0_26]),c_0_19])])).

cnf(c_0_79,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_78]),c_0_33]),c_0_78]),c_0_19])]),
    [proof]).

%------------------------------------------------------------------------------
