%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:43 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 281 expanded)
%              Number of clauses        :   40 ( 112 expanded)
%              Number of leaves         :   12 (  70 expanded)
%              Depth                    :   11
%              Number of atoms          :  202 ( 958 expanded)
%              Number of equality atoms :   36 ( 212 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   33 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t11_wellord2,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).

fof(t26_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r1_ordinal1(X1,X2)
            | r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(t10_wellord2,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,X2)
           => X1 = k1_wellord1(k1_wellord2(X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(t7_wellord2,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v2_wellord1(k1_wellord2(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

fof(dt_k1_wellord2,axiom,(
    ! [X1] : v1_relat_1(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t57_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => ! [X2] :
            ~ ( r2_hidden(X2,k3_relat_1(X1))
              & r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).

fof(t13_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_wellord1(X2,X1),k3_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_wellord1)).

fof(t8_wellord2,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_wellord1(k1_wellord2(X2),X1) = k1_wellord2(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).

fof(t50_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r4_wellord1(X1,X2)
           => r4_wellord1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ( r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))
             => X1 = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t11_wellord2])).

fof(c_0_13,plain,(
    ! [X9,X10] :
      ( ~ v3_ordinal1(X9)
      | ~ v3_ordinal1(X10)
      | r1_ordinal1(X9,X10)
      | r2_hidden(X10,X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).

fof(c_0_14,negated_conjecture,
    ( v3_ordinal1(esk3_0)
    & v3_ordinal1(esk4_0)
    & r4_wellord1(k1_wellord2(esk3_0),k1_wellord2(esk4_0))
    & esk3_0 != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_15,plain,
    ( r1_ordinal1(X1,X2)
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( v3_ordinal1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_17,plain,(
    ! [X24,X25] :
      ( ~ v3_ordinal1(X24)
      | ~ v3_ordinal1(X25)
      | ~ r2_hidden(X24,X25)
      | X24 = k1_wellord1(k1_wellord2(X25),X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_wellord2])])])).

fof(c_0_18,plain,(
    ! [X7,X8] :
      ( ( ~ r1_ordinal1(X7,X8)
        | r1_tarski(X7,X8)
        | ~ v3_ordinal1(X7)
        | ~ v3_ordinal1(X8) )
      & ( ~ r1_tarski(X7,X8)
        | r1_ordinal1(X7,X8)
        | ~ v3_ordinal1(X7)
        | ~ v3_ordinal1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk4_0,X1)
    | r1_ordinal1(X1,esk4_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( v3_ordinal1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( X1 = k1_wellord1(k1_wellord2(X2),X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X26] :
      ( ~ v3_ordinal1(X26)
      | v2_wellord1(k1_wellord2(X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_wellord2])])).

fof(c_0_23,plain,(
    ! [X17,X18,X19,X20] :
      ( ( k3_relat_1(X18) = X17
        | X18 != k1_wellord2(X17)
        | ~ v1_relat_1(X18) )
      & ( ~ r2_hidden(k4_tarski(X19,X20),X18)
        | r1_tarski(X19,X20)
        | ~ r2_hidden(X19,X17)
        | ~ r2_hidden(X20,X17)
        | X18 != k1_wellord2(X17)
        | ~ v1_relat_1(X18) )
      & ( ~ r1_tarski(X19,X20)
        | r2_hidden(k4_tarski(X19,X20),X18)
        | ~ r2_hidden(X19,X17)
        | ~ r2_hidden(X20,X17)
        | X18 != k1_wellord2(X17)
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(esk1_2(X17,X18),X17)
        | k3_relat_1(X18) != X17
        | X18 = k1_wellord2(X17)
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(esk2_2(X17,X18),X17)
        | k3_relat_1(X18) != X17
        | X18 = k1_wellord2(X17)
        | ~ v1_relat_1(X18) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X17,X18),esk2_2(X17,X18)),X18)
        | ~ r1_tarski(esk1_2(X17,X18),esk2_2(X17,X18))
        | k3_relat_1(X18) != X17
        | X18 = k1_wellord2(X17)
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(k4_tarski(esk1_2(X17,X18),esk2_2(X17,X18)),X18)
        | r1_tarski(esk1_2(X17,X18),esk2_2(X17,X18))
        | k3_relat_1(X18) != X17
        | X18 = k1_wellord2(X17)
        | ~ v1_relat_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).

fof(c_0_24,plain,(
    ! [X23] : v1_relat_1(k1_wellord2(X23)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_25,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0)
    | r1_ordinal1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk3_0,X1)
    | r1_ordinal1(X1,esk3_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_20])).

fof(c_0_29,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X15)
      | ~ v2_wellord1(X15)
      | ~ r2_hidden(X16,k3_relat_1(X15))
      | ~ r4_wellord1(X15,k2_wellord1(X15,k1_wellord1(X15,X16))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t57_wellord1])])])).

cnf(c_0_30,negated_conjecture,
    ( k1_wellord1(k1_wellord2(esk3_0),X1) = X1
    | ~ r2_hidden(X1,esk3_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_20])).

cnf(c_0_31,plain,
    ( v2_wellord1(k1_wellord2(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k3_relat_1(X1) = X2
    | X1 != k1_wellord2(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_34,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X12)
      | r1_tarski(k1_wellord1(X12,X11),k3_relat_1(X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_wellord1])])).

cnf(c_0_35,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0)
    | r1_tarski(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_16]),c_0_20])])).

cnf(c_0_37,negated_conjecture,
    ( esk3_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | r1_ordinal1(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_16])).

cnf(c_0_39,plain,
    ( ~ v1_relat_1(X1)
    | ~ v2_wellord1(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,negated_conjecture,
    ( k1_wellord1(k1_wellord2(esk3_0),esk4_0) = esk4_0
    | ~ r2_hidden(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_16])).

cnf(c_0_41,negated_conjecture,
    ( v2_wellord1(k1_wellord2(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_20])).

cnf(c_0_42,plain,
    ( k3_relat_1(k1_wellord2(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_32]),c_0_33])])).

fof(c_0_43,plain,(
    ! [X27,X28] :
      ( ~ r1_tarski(X27,X28)
      | k2_wellord1(k1_wellord2(X28),X27) = k1_wellord2(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_wellord2])])).

cnf(c_0_44,plain,
    ( r1_tarski(k1_wellord1(X1,X2),k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,negated_conjecture,
    ( k1_wellord1(k1_wellord2(esk4_0),X1) = X1
    | ~ r2_hidden(X1,esk4_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_16])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0)
    | ~ r1_tarski(esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | r1_tarski(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_38]),c_0_20]),c_0_16])])).

cnf(c_0_48,negated_conjecture,
    ( ~ r4_wellord1(k1_wellord2(esk3_0),k2_wellord1(k1_wellord2(esk3_0),esk4_0))
    | ~ r2_hidden(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_33]),c_0_42])])).

cnf(c_0_49,plain,
    ( k2_wellord1(k1_wellord2(X2),X1) = k1_wellord2(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk3_0),k1_wellord2(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0)
    | ~ r2_hidden(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_40]),c_0_42]),c_0_33])])).

fof(c_0_52,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X13)
      | ~ v1_relat_1(X14)
      | ~ r4_wellord1(X13,X14)
      | r4_wellord1(X14,X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_wellord1])])])).

cnf(c_0_53,negated_conjecture,
    ( k1_wellord1(k1_wellord2(esk4_0),esk3_0) = esk3_0
    | ~ r2_hidden(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_20])).

cnf(c_0_54,negated_conjecture,
    ( v2_wellord1(k1_wellord2(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_16])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | r2_hidden(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_56,negated_conjecture,
    ( ~ r2_hidden(esk4_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])]),c_0_51])).

cnf(c_0_57,plain,
    ( r4_wellord1(X2,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r4_wellord1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( ~ r4_wellord1(k1_wellord2(esk4_0),k2_wellord1(k1_wellord2(esk4_0),esk3_0))
    | ~ r2_hidden(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_53]),c_0_54]),c_0_33]),c_0_42])])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk4_0),k1_wellord2(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_50]),c_0_33]),c_0_33])])).

cnf(c_0_61,negated_conjecture,
    ( ~ r4_wellord1(k1_wellord2(esk4_0),k2_wellord1(k1_wellord2(esk4_0),esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59])])).

cnf(c_0_62,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk4_0),k2_wellord1(k1_wellord2(X1),esk3_0))
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_49])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[c_0_36,c_0_56])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:46:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.36  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0Y
% 0.12/0.36  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.36  #
% 0.12/0.36  # Preprocessing time       : 0.021 s
% 0.12/0.36  # Presaturation interreduction done
% 0.12/0.36  
% 0.12/0.36  # Proof found!
% 0.12/0.36  # SZS status Theorem
% 0.12/0.36  # SZS output start CNFRefutation
% 0.12/0.36  fof(t11_wellord2, conjecture, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))=>X1=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_wellord2)).
% 0.12/0.36  fof(t26_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r1_ordinal1(X1,X2)|r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 0.12/0.36  fof(t10_wellord2, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)=>X1=k1_wellord1(k1_wellord2(X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_wellord2)).
% 0.12/0.36  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 0.12/0.36  fof(t7_wellord2, axiom, ![X1]:(v3_ordinal1(X1)=>v2_wellord1(k1_wellord2(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_wellord2)).
% 0.12/0.36  fof(d1_wellord2, axiom, ![X1, X2]:(v1_relat_1(X2)=>(X2=k1_wellord2(X1)<=>(k3_relat_1(X2)=X1&![X3, X4]:((r2_hidden(X3,X1)&r2_hidden(X4,X1))=>(r2_hidden(k4_tarski(X3,X4),X2)<=>r1_tarski(X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 0.12/0.36  fof(dt_k1_wellord2, axiom, ![X1]:v1_relat_1(k1_wellord2(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 0.12/0.36  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.12/0.36  fof(t57_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v2_wellord1(X1)=>![X2]:~((r2_hidden(X2,k3_relat_1(X1))&r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_wellord1)).
% 0.12/0.36  fof(t13_wellord1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_wellord1(X2,X1),k3_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_wellord1)).
% 0.12/0.36  fof(t8_wellord2, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_wellord1(k1_wellord2(X2),X1)=k1_wellord2(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_wellord2)).
% 0.12/0.36  fof(t50_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r4_wellord1(X1,X2)=>r4_wellord1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_wellord1)).
% 0.12/0.36  fof(c_0_12, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))=>X1=X2)))), inference(assume_negation,[status(cth)],[t11_wellord2])).
% 0.12/0.36  fof(c_0_13, plain, ![X9, X10]:(~v3_ordinal1(X9)|(~v3_ordinal1(X10)|(r1_ordinal1(X9,X10)|r2_hidden(X10,X9)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).
% 0.12/0.36  fof(c_0_14, negated_conjecture, (v3_ordinal1(esk3_0)&(v3_ordinal1(esk4_0)&(r4_wellord1(k1_wellord2(esk3_0),k1_wellord2(esk4_0))&esk3_0!=esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.12/0.36  cnf(c_0_15, plain, (r1_ordinal1(X1,X2)|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.36  cnf(c_0_16, negated_conjecture, (v3_ordinal1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.36  fof(c_0_17, plain, ![X24, X25]:(~v3_ordinal1(X24)|(~v3_ordinal1(X25)|(~r2_hidden(X24,X25)|X24=k1_wellord1(k1_wellord2(X25),X24)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_wellord2])])])).
% 0.12/0.36  fof(c_0_18, plain, ![X7, X8]:((~r1_ordinal1(X7,X8)|r1_tarski(X7,X8)|(~v3_ordinal1(X7)|~v3_ordinal1(X8)))&(~r1_tarski(X7,X8)|r1_ordinal1(X7,X8)|(~v3_ordinal1(X7)|~v3_ordinal1(X8)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 0.12/0.36  cnf(c_0_19, negated_conjecture, (r2_hidden(esk4_0,X1)|r1_ordinal1(X1,esk4_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.12/0.36  cnf(c_0_20, negated_conjecture, (v3_ordinal1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.36  cnf(c_0_21, plain, (X1=k1_wellord1(k1_wellord2(X2),X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.36  fof(c_0_22, plain, ![X26]:(~v3_ordinal1(X26)|v2_wellord1(k1_wellord2(X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_wellord2])])).
% 0.12/0.36  fof(c_0_23, plain, ![X17, X18, X19, X20]:(((k3_relat_1(X18)=X17|X18!=k1_wellord2(X17)|~v1_relat_1(X18))&((~r2_hidden(k4_tarski(X19,X20),X18)|r1_tarski(X19,X20)|(~r2_hidden(X19,X17)|~r2_hidden(X20,X17))|X18!=k1_wellord2(X17)|~v1_relat_1(X18))&(~r1_tarski(X19,X20)|r2_hidden(k4_tarski(X19,X20),X18)|(~r2_hidden(X19,X17)|~r2_hidden(X20,X17))|X18!=k1_wellord2(X17)|~v1_relat_1(X18))))&(((r2_hidden(esk1_2(X17,X18),X17)|k3_relat_1(X18)!=X17|X18=k1_wellord2(X17)|~v1_relat_1(X18))&(r2_hidden(esk2_2(X17,X18),X17)|k3_relat_1(X18)!=X17|X18=k1_wellord2(X17)|~v1_relat_1(X18)))&((~r2_hidden(k4_tarski(esk1_2(X17,X18),esk2_2(X17,X18)),X18)|~r1_tarski(esk1_2(X17,X18),esk2_2(X17,X18))|k3_relat_1(X18)!=X17|X18=k1_wellord2(X17)|~v1_relat_1(X18))&(r2_hidden(k4_tarski(esk1_2(X17,X18),esk2_2(X17,X18)),X18)|r1_tarski(esk1_2(X17,X18),esk2_2(X17,X18))|k3_relat_1(X18)!=X17|X18=k1_wellord2(X17)|~v1_relat_1(X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).
% 0.12/0.36  fof(c_0_24, plain, ![X23]:v1_relat_1(k1_wellord2(X23)), inference(variable_rename,[status(thm)],[dt_k1_wellord2])).
% 0.12/0.36  fof(c_0_25, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.12/0.36  cnf(c_0_26, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.36  cnf(c_0_27, negated_conjecture, (r2_hidden(esk4_0,esk3_0)|r1_ordinal1(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.12/0.36  cnf(c_0_28, negated_conjecture, (r2_hidden(esk3_0,X1)|r1_ordinal1(X1,esk3_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_15, c_0_20])).
% 0.12/0.36  fof(c_0_29, plain, ![X15, X16]:(~v1_relat_1(X15)|(~v2_wellord1(X15)|(~r2_hidden(X16,k3_relat_1(X15))|~r4_wellord1(X15,k2_wellord1(X15,k1_wellord1(X15,X16)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t57_wellord1])])])).
% 0.12/0.36  cnf(c_0_30, negated_conjecture, (k1_wellord1(k1_wellord2(esk3_0),X1)=X1|~r2_hidden(X1,esk3_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_21, c_0_20])).
% 0.12/0.36  cnf(c_0_31, plain, (v2_wellord1(k1_wellord2(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.36  cnf(c_0_32, plain, (k3_relat_1(X1)=X2|X1!=k1_wellord2(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.36  cnf(c_0_33, plain, (v1_relat_1(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.36  fof(c_0_34, plain, ![X11, X12]:(~v1_relat_1(X12)|r1_tarski(k1_wellord1(X12,X11),k3_relat_1(X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_wellord1])])).
% 0.12/0.36  cnf(c_0_35, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.36  cnf(c_0_36, negated_conjecture, (r2_hidden(esk4_0,esk3_0)|r1_tarski(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_16]), c_0_20])])).
% 0.12/0.36  cnf(c_0_37, negated_conjecture, (esk3_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.36  cnf(c_0_38, negated_conjecture, (r2_hidden(esk3_0,esk4_0)|r1_ordinal1(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_28, c_0_16])).
% 0.12/0.36  cnf(c_0_39, plain, (~v1_relat_1(X1)|~v2_wellord1(X1)|~r2_hidden(X2,k3_relat_1(X1))|~r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.36  cnf(c_0_40, negated_conjecture, (k1_wellord1(k1_wellord2(esk3_0),esk4_0)=esk4_0|~r2_hidden(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_30, c_0_16])).
% 0.12/0.36  cnf(c_0_41, negated_conjecture, (v2_wellord1(k1_wellord2(esk3_0))), inference(spm,[status(thm)],[c_0_31, c_0_20])).
% 0.12/0.36  cnf(c_0_42, plain, (k3_relat_1(k1_wellord2(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_32]), c_0_33])])).
% 0.12/0.36  fof(c_0_43, plain, ![X27, X28]:(~r1_tarski(X27,X28)|k2_wellord1(k1_wellord2(X28),X27)=k1_wellord2(X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_wellord2])])).
% 0.12/0.36  cnf(c_0_44, plain, (r1_tarski(k1_wellord1(X1,X2),k3_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.12/0.36  cnf(c_0_45, negated_conjecture, (k1_wellord1(k1_wellord2(esk4_0),X1)=X1|~r2_hidden(X1,esk4_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_21, c_0_16])).
% 0.12/0.36  cnf(c_0_46, negated_conjecture, (r2_hidden(esk4_0,esk3_0)|~r1_tarski(esk4_0,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])).
% 0.12/0.36  cnf(c_0_47, negated_conjecture, (r2_hidden(esk3_0,esk4_0)|r1_tarski(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_38]), c_0_20]), c_0_16])])).
% 0.12/0.36  cnf(c_0_48, negated_conjecture, (~r4_wellord1(k1_wellord2(esk3_0),k2_wellord1(k1_wellord2(esk3_0),esk4_0))|~r2_hidden(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_33]), c_0_42])])).
% 0.12/0.36  cnf(c_0_49, plain, (k2_wellord1(k1_wellord2(X2),X1)=k1_wellord2(X1)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.12/0.36  cnf(c_0_50, negated_conjecture, (r4_wellord1(k1_wellord2(esk3_0),k1_wellord2(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.36  cnf(c_0_51, negated_conjecture, (r1_tarski(esk4_0,esk3_0)|~r2_hidden(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_40]), c_0_42]), c_0_33])])).
% 0.12/0.36  fof(c_0_52, plain, ![X13, X14]:(~v1_relat_1(X13)|(~v1_relat_1(X14)|(~r4_wellord1(X13,X14)|r4_wellord1(X14,X13)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_wellord1])])])).
% 0.12/0.36  cnf(c_0_53, negated_conjecture, (k1_wellord1(k1_wellord2(esk4_0),esk3_0)=esk3_0|~r2_hidden(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_45, c_0_20])).
% 0.12/0.36  cnf(c_0_54, negated_conjecture, (v2_wellord1(k1_wellord2(esk4_0))), inference(spm,[status(thm)],[c_0_31, c_0_16])).
% 0.12/0.36  cnf(c_0_55, negated_conjecture, (r2_hidden(esk3_0,esk4_0)|r2_hidden(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.12/0.36  cnf(c_0_56, negated_conjecture, (~r2_hidden(esk4_0,esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])]), c_0_51])).
% 0.12/0.36  cnf(c_0_57, plain, (r4_wellord1(X2,X1)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r4_wellord1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.12/0.36  cnf(c_0_58, negated_conjecture, (~r4_wellord1(k1_wellord2(esk4_0),k2_wellord1(k1_wellord2(esk4_0),esk3_0))|~r2_hidden(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_53]), c_0_54]), c_0_33]), c_0_42])])).
% 0.12/0.36  cnf(c_0_59, negated_conjecture, (r2_hidden(esk3_0,esk4_0)), inference(sr,[status(thm)],[c_0_55, c_0_56])).
% 0.12/0.36  cnf(c_0_60, negated_conjecture, (r4_wellord1(k1_wellord2(esk4_0),k1_wellord2(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_50]), c_0_33]), c_0_33])])).
% 0.12/0.36  cnf(c_0_61, negated_conjecture, (~r4_wellord1(k1_wellord2(esk4_0),k2_wellord1(k1_wellord2(esk4_0),esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59])])).
% 0.12/0.36  cnf(c_0_62, negated_conjecture, (r4_wellord1(k1_wellord2(esk4_0),k2_wellord1(k1_wellord2(X1),esk3_0))|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_60, c_0_49])).
% 0.12/0.36  cnf(c_0_63, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(sr,[status(thm)],[c_0_36, c_0_56])).
% 0.12/0.36  cnf(c_0_64, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63])]), ['proof']).
% 0.12/0.36  # SZS output end CNFRefutation
% 0.12/0.36  # Proof object total steps             : 65
% 0.12/0.36  # Proof object clause steps            : 40
% 0.12/0.36  # Proof object formula steps           : 25
% 0.12/0.36  # Proof object conjectures             : 31
% 0.12/0.36  # Proof object clause conjectures      : 28
% 0.12/0.36  # Proof object formula conjectures     : 3
% 0.12/0.36  # Proof object initial clauses used    : 15
% 0.12/0.36  # Proof object initial formulas used   : 12
% 0.12/0.36  # Proof object generating inferences   : 21
% 0.12/0.36  # Proof object simplifying inferences  : 33
% 0.12/0.36  # Training examples: 0 positive, 0 negative
% 0.12/0.36  # Parsed axioms                        : 12
% 0.12/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.36  # Initial clauses                      : 24
% 0.12/0.36  # Removed in clause preprocessing      : 0
% 0.12/0.36  # Initial clauses in saturation        : 24
% 0.12/0.36  # Processed clauses                    : 121
% 0.12/0.36  # ...of these trivial                  : 3
% 0.12/0.36  # ...subsumed                          : 11
% 0.12/0.36  # ...remaining for further processing  : 107
% 0.12/0.36  # Other redundant clauses eliminated   : 9
% 0.12/0.36  # Clauses deleted for lack of memory   : 0
% 0.12/0.36  # Backward-subsumed                    : 4
% 0.12/0.36  # Backward-rewritten                   : 8
% 0.12/0.36  # Generated clauses                    : 185
% 0.12/0.36  # ...of the previous two non-trivial   : 161
% 0.12/0.36  # Contextual simplify-reflections      : 1
% 0.12/0.36  # Paramodulations                      : 173
% 0.12/0.36  # Factorizations                       : 0
% 0.12/0.36  # Equation resolutions                 : 9
% 0.12/0.36  # Propositional unsat checks           : 0
% 0.12/0.36  #    Propositional check models        : 0
% 0.12/0.36  #    Propositional check unsatisfiable : 0
% 0.12/0.36  #    Propositional clauses             : 0
% 0.12/0.36  #    Propositional clauses after purity: 0
% 0.12/0.36  #    Propositional unsat core size     : 0
% 0.12/0.36  #    Propositional preprocessing time  : 0.000
% 0.12/0.36  #    Propositional encoding time       : 0.000
% 0.12/0.36  #    Propositional solver time         : 0.000
% 0.12/0.36  #    Success case prop preproc time    : 0.000
% 0.12/0.36  #    Success case prop encoding time   : 0.000
% 0.12/0.36  #    Success case prop solver time     : 0.000
% 0.12/0.36  # Current number of processed clauses  : 60
% 0.12/0.36  #    Positive orientable unit clauses  : 16
% 0.12/0.36  #    Positive unorientable unit clauses: 0
% 0.12/0.36  #    Negative unit clauses             : 4
% 0.12/0.36  #    Non-unit-clauses                  : 40
% 0.12/0.36  # Current number of unprocessed clauses: 82
% 0.12/0.36  # ...number of literals in the above   : 286
% 0.12/0.36  # Current number of archived formulas  : 0
% 0.12/0.36  # Current number of archived clauses   : 38
% 0.12/0.36  # Clause-clause subsumption calls (NU) : 292
% 0.12/0.36  # Rec. Clause-clause subsumption calls : 210
% 0.12/0.36  # Non-unit clause-clause subsumptions  : 7
% 0.12/0.36  # Unit Clause-clause subsumption calls : 123
% 0.12/0.36  # Rewrite failures with RHS unbound    : 0
% 0.12/0.36  # BW rewrite match attempts            : 8
% 0.12/0.36  # BW rewrite match successes           : 5
% 0.12/0.36  # Condensation attempts                : 0
% 0.12/0.36  # Condensation successes               : 0
% 0.12/0.36  # Termbank termtop insertions          : 4379
% 0.12/0.36  
% 0.12/0.36  # -------------------------------------------------
% 0.12/0.36  # User time                : 0.024 s
% 0.12/0.36  # System time              : 0.005 s
% 0.12/0.36  # Total time               : 0.029 s
% 0.12/0.36  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
