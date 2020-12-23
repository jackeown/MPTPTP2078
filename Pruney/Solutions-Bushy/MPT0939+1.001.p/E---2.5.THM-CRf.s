%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0939+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:26 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 196 expanded)
%              Number of clauses        :   33 (  89 expanded)
%              Number of leaves         :    9 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :  209 ( 796 expanded)
%              Number of equality atoms :   21 (  77 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   33 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(d6_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r6_relat_2(X1,X2)
        <=> ! [X3,X4] :
              ~ ( r2_hidden(X3,X2)
                & r2_hidden(X4,X2)
                & X3 != X4
                & ~ r2_hidden(k4_tarski(X3,X4),X1)
                & ~ r2_hidden(k4_tarski(X4,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_2)).

fof(dt_k1_wellord2,axiom,(
    ! [X1] : v1_relat_1(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(t4_wellord2,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v6_relat_2(k1_wellord2(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_wellord2)).

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

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(d14_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v6_relat_2(X1)
      <=> r6_relat_2(X1,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_2)).

fof(c_0_9,plain,(
    ! [X5,X6] :
      ( ~ v3_ordinal1(X5)
      | ~ m1_subset_1(X6,X5)
      | v3_ordinal1(X6) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc5_ordinal1])])])).

fof(c_0_10,plain,(
    ! [X26,X27] :
      ( ~ r2_hidden(X26,X27)
      | m1_subset_1(X26,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

fof(c_0_11,plain,(
    ! [X16,X17,X18,X19,X20] :
      ( ( ~ r6_relat_2(X16,X17)
        | ~ r2_hidden(X18,X17)
        | ~ r2_hidden(X19,X17)
        | X18 = X19
        | r2_hidden(k4_tarski(X18,X19),X16)
        | r2_hidden(k4_tarski(X19,X18),X16)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(esk3_2(X16,X20),X20)
        | r6_relat_2(X16,X20)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(esk4_2(X16,X20),X20)
        | r6_relat_2(X16,X20)
        | ~ v1_relat_1(X16) )
      & ( esk3_2(X16,X20) != esk4_2(X16,X20)
        | r6_relat_2(X16,X20)
        | ~ v1_relat_1(X16) )
      & ( ~ r2_hidden(k4_tarski(esk3_2(X16,X20),esk4_2(X16,X20)),X16)
        | r6_relat_2(X16,X20)
        | ~ v1_relat_1(X16) )
      & ( ~ r2_hidden(k4_tarski(esk4_2(X16,X20),esk3_2(X16,X20)),X16)
        | r6_relat_2(X16,X20)
        | ~ v1_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_relat_2])])])])])])])).

fof(c_0_12,plain,(
    ! [X23] : v1_relat_1(k1_wellord2(X23)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

cnf(c_0_13,plain,
    ( v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | r6_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => v6_relat_2(k1_wellord2(X1)) ) ),
    inference(assume_negation,[status(cth)],[t4_wellord2])).

cnf(c_0_18,plain,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,X2)
    | ~ v3_ordinal1(X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( r2_hidden(esk3_2(k1_wellord2(X1),X2),X2)
    | r6_relat_2(k1_wellord2(X1),X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_20,negated_conjecture,
    ( v3_ordinal1(esk5_0)
    & ~ v6_relat_2(k1_wellord2(esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

cnf(c_0_21,plain,
    ( r2_hidden(esk4_2(X1,X2),X2)
    | r6_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_22,plain,(
    ! [X7,X8] :
      ( ~ v3_ordinal1(X7)
      | ~ v3_ordinal1(X8)
      | r1_ordinal1(X7,X8)
      | r1_ordinal1(X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[connectedness_r1_ordinal1])])).

cnf(c_0_23,plain,
    ( r6_relat_2(k1_wellord2(X1),X2)
    | v3_ordinal1(esk3_2(k1_wellord2(X1),X2))
    | ~ v3_ordinal1(X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( v3_ordinal1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( r2_hidden(esk4_2(k1_wellord2(X1),X2),X2)
    | r6_relat_2(k1_wellord2(X1),X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_16])).

cnf(c_0_26,plain,
    ( r1_ordinal1(X1,X2)
    | r1_ordinal1(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( r6_relat_2(k1_wellord2(X1),esk5_0)
    | v3_ordinal1(esk3_2(k1_wellord2(X1),esk5_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,plain,
    ( r6_relat_2(k1_wellord2(X1),X2)
    | v3_ordinal1(esk4_2(k1_wellord2(X1),X2))
    | ~ v3_ordinal1(X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_25])).

fof(c_0_29,plain,(
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

fof(c_0_30,plain,(
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

cnf(c_0_31,negated_conjecture,
    ( r6_relat_2(k1_wellord2(X1),esk5_0)
    | r1_ordinal1(X2,esk3_2(k1_wellord2(X1),esk5_0))
    | r1_ordinal1(esk3_2(k1_wellord2(X1),esk5_0),X2)
    | ~ v3_ordinal1(X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( r6_relat_2(k1_wellord2(X1),esk5_0)
    | v3_ordinal1(esk4_2(k1_wellord2(X1),esk5_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_24])).

cnf(c_0_33,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X1,X4)
    | ~ r2_hidden(X2,X4)
    | X3 != k1_wellord2(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( r6_relat_2(k1_wellord2(X1),esk5_0)
    | r6_relat_2(k1_wellord2(X2),esk5_0)
    | r1_ordinal1(esk3_2(k1_wellord2(X2),esk5_0),esk4_2(k1_wellord2(X1),esk5_0))
    | r1_ordinal1(esk4_2(k1_wellord2(X1),esk5_0),esk3_2(k1_wellord2(X2),esk5_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,plain,
    ( r6_relat_2(X1,X2)
    | ~ r2_hidden(k4_tarski(esk4_2(X1,X2),esk3_2(X1,X2)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_37,plain,
    ( r2_hidden(k4_tarski(X1,X2),k1_wellord2(X3))
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_33]),c_0_16])])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(esk4_2(k1_wellord2(X1),esk5_0),esk3_2(k1_wellord2(X2),esk5_0))
    | r6_relat_2(k1_wellord2(X2),esk5_0)
    | r6_relat_2(k1_wellord2(X1),esk5_0)
    | r1_ordinal1(esk3_2(k1_wellord2(X2),esk5_0),esk4_2(k1_wellord2(X1),esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_32]),c_0_27])).

cnf(c_0_39,plain,
    ( r6_relat_2(X1,X2)
    | ~ r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_40,plain,(
    ! [X9] :
      ( ( ~ v6_relat_2(X9)
        | r6_relat_2(X9,k3_relat_1(X9))
        | ~ v1_relat_1(X9) )
      & ( ~ r6_relat_2(X9,k3_relat_1(X9))
        | v6_relat_2(X9)
        | ~ v1_relat_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_2])])])).

cnf(c_0_41,plain,
    ( k3_relat_1(X1) = X2
    | X1 != k1_wellord2(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,plain,
    ( r6_relat_2(k1_wellord2(X1),X2)
    | ~ r1_tarski(esk4_2(k1_wellord2(X1),X2),esk3_2(k1_wellord2(X1),X2))
    | ~ r2_hidden(esk3_2(k1_wellord2(X1),X2),X1)
    | ~ r2_hidden(esk4_2(k1_wellord2(X1),X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_16])])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(esk4_2(k1_wellord2(X1),esk5_0),esk3_2(k1_wellord2(X2),esk5_0))
    | r1_tarski(esk3_2(k1_wellord2(X2),esk5_0),esk4_2(k1_wellord2(X1),esk5_0))
    | r6_relat_2(k1_wellord2(X1),esk5_0)
    | r6_relat_2(k1_wellord2(X2),esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_38]),c_0_27]),c_0_32])).

cnf(c_0_44,plain,
    ( r6_relat_2(k1_wellord2(X1),X2)
    | ~ r1_tarski(esk3_2(k1_wellord2(X1),X2),esk4_2(k1_wellord2(X1),X2))
    | ~ r2_hidden(esk4_2(k1_wellord2(X1),X2),X1)
    | ~ r2_hidden(esk3_2(k1_wellord2(X1),X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_37]),c_0_16])])).

cnf(c_0_45,plain,
    ( v6_relat_2(X1)
    | ~ r6_relat_2(X1,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,plain,
    ( k3_relat_1(k1_wellord2(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_41]),c_0_16])])).

cnf(c_0_47,negated_conjecture,
    ( r6_relat_2(k1_wellord2(X1),esk5_0)
    | ~ r2_hidden(esk3_2(k1_wellord2(X1),esk5_0),X1)
    | ~ r2_hidden(esk4_2(k1_wellord2(X1),esk5_0),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_48,plain,
    ( v6_relat_2(k1_wellord2(X1))
    | ~ r6_relat_2(k1_wellord2(X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_16])])).

cnf(c_0_49,negated_conjecture,
    ( r6_relat_2(k1_wellord2(esk5_0),esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_25]),c_0_19])).

cnf(c_0_50,negated_conjecture,
    ( ~ v6_relat_2(k1_wellord2(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),
    [proof]).

%------------------------------------------------------------------------------
