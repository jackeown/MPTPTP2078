%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:04 EST 2020

% Result     : Theorem 1.37s
% Output     : CNFRefutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :   90 (3451 expanded)
%              Number of clauses        :   67 (1437 expanded)
%              Number of leaves         :   11 ( 837 expanded)
%              Depth                    :   18
%              Number of atoms          :  255 (14707 expanded)
%              Number of equality atoms :   64 (3579 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t160_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k2_relat_1(k5_relat_1(X1,X2)) = k9_relat_1(X2,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(d11_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( v1_relat_1(X3)
         => ( X3 = k7_relat_1(X1,X2)
          <=> ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X3)
              <=> ( r2_hidden(X4,X2)
                  & r2_hidden(k4_tarski(X4,X5),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t80_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t55_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(t47_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(k1_relat_1(X1),k2_relat_1(X2))
           => k2_relat_1(k5_relat_1(X2,X1)) = k2_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => k2_relat_1(k5_relat_1(X1,X2)) = k9_relat_1(X2,k2_relat_1(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t160_relat_1])).

fof(c_0_12,plain,(
    ! [X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X15,X13)
        | ~ r2_hidden(k4_tarski(X15,X16),X14)
        | X14 != k7_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X12) )
      & ( r2_hidden(k4_tarski(X15,X16),X12)
        | ~ r2_hidden(k4_tarski(X15,X16),X14)
        | X14 != k7_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X12) )
      & ( ~ r2_hidden(X17,X13)
        | ~ r2_hidden(k4_tarski(X17,X18),X12)
        | r2_hidden(k4_tarski(X17,X18),X14)
        | X14 != k7_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X12) )
      & ( ~ r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X14)
        | ~ r2_hidden(esk2_3(X12,X13,X14),X13)
        | ~ r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X12)
        | X14 = k7_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X12) )
      & ( r2_hidden(esk2_3(X12,X13,X14),X13)
        | r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X14)
        | X14 = k7_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X12) )
      & ( r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X12)
        | r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X14)
        | X14 = k7_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_relat_1])])])])])])).

fof(c_0_13,plain,(
    ! [X33,X34] :
      ( ~ v1_relat_1(X33)
      | v1_relat_1(k7_relat_1(X33,X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_14,plain,(
    ! [X42] :
      ( ~ v1_relat_1(X42)
      | k5_relat_1(X42,k6_relat_1(k2_relat_1(X42))) = X42 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).

fof(c_0_15,plain,(
    ! [X43,X44] :
      ( ~ v1_relat_1(X44)
      | k7_relat_1(X44,X43) = k5_relat_1(k6_relat_1(X43),X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

fof(c_0_16,plain,(
    ! [X32] : v1_relat_1(k6_relat_1(X32)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_17,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & v1_relat_1(esk8_0)
    & k2_relat_1(k5_relat_1(esk7_0,esk8_0)) != k9_relat_1(esk8_0,k2_relat_1(esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_18,plain,(
    ! [X39,X40,X41] :
      ( ~ v1_relat_1(X39)
      | ~ v1_relat_1(X40)
      | ~ v1_relat_1(X41)
      | k5_relat_1(k5_relat_1(X39,X40),X41) = k5_relat_1(X39,k5_relat_1(X40,X41)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X4)
    | X4 != k7_relat_1(X5,X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X5) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_24,plain,(
    ! [X21,X22,X23,X25,X26,X27,X28,X30] :
      ( ( ~ r2_hidden(X23,X22)
        | r2_hidden(k4_tarski(X23,esk4_3(X21,X22,X23)),X21)
        | X22 != k1_relat_1(X21) )
      & ( ~ r2_hidden(k4_tarski(X25,X26),X21)
        | r2_hidden(X25,X22)
        | X22 != k1_relat_1(X21) )
      & ( ~ r2_hidden(esk5_2(X27,X28),X28)
        | ~ r2_hidden(k4_tarski(esk5_2(X27,X28),X30),X27)
        | X28 = k1_relat_1(X27) )
      & ( r2_hidden(esk5_2(X27,X28),X28)
        | r2_hidden(k4_tarski(esk5_2(X27,X28),esk6_2(X27,X28)),X27)
        | X28 = k1_relat_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_25,plain,
    ( r2_hidden(k4_tarski(esk2_3(X1,X2,X3),esk3_3(X1,X2,X3)),X1)
    | r2_hidden(k4_tarski(esk2_3(X1,X2,X3),esk3_3(X1,X2,X3)),X3)
    | X3 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X1,X4),k7_relat_1(X3,X2)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_19]),c_0_20])).

cnf(c_0_29,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X1))),X1) = k6_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_23])])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(X1,esk4_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_31,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_32,negated_conjecture,
    ( k7_relat_1(X1,X2) = esk8_0
    | r2_hidden(k4_tarski(esk2_3(X1,X2,esk8_0),esk3_3(X1,X2,esk8_0)),esk8_0)
    | r2_hidden(k4_tarski(esk2_3(X1,X2,esk8_0),esk3_3(X1,X2,esk8_0)),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( k5_relat_1(X1,k5_relat_1(k6_relat_1(k2_relat_1(X1)),X2)) = k5_relat_1(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_21]),c_0_23])])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_23])])).

cnf(c_0_36,plain,
    ( r2_hidden(k4_tarski(X1,esk4_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( X3 = k7_relat_1(X1,X2)
    | ~ r2_hidden(k4_tarski(esk2_3(X1,X2,X3),esk3_3(X1,X2,X3)),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(k4_tarski(esk2_3(X1,X2,X3),esk3_3(X1,X2,X3)),X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_40,negated_conjecture,
    ( k7_relat_1(esk8_0,X1) = esk8_0
    | r2_hidden(k4_tarski(esk2_3(esk8_0,X1,esk8_0),esk3_3(esk8_0,X1,esk8_0)),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_32]),c_0_26])])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( k7_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X1))),X2),X1) = k5_relat_1(k6_relat_1(X1),X2)
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X1))),X2))
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_34]),c_0_23])])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(k6_relat_1(X2))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_44,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_45,plain,(
    ! [X35,X36] :
      ( ~ v1_relat_1(X36)
      | k2_relat_1(k7_relat_1(X36,X35)) = k9_relat_1(X36,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_46,negated_conjecture,
    ( k7_relat_1(esk8_0,X1) = esk8_0
    | ~ r2_hidden(esk2_3(esk8_0,X1,esk8_0),X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_26])]),c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( k7_relat_1(esk8_0,X1) = esk8_0
    | r2_hidden(esk2_3(esk8_0,X1,esk8_0),k1_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_40])).

cnf(c_0_48,plain,
    ( v1_relat_1(k5_relat_1(k6_relat_1(X1),X2))
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X1))),X2))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_42])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_50,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_relat_1(k6_relat_1(X3))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_51,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( k7_relat_1(esk8_0,k1_relat_1(esk8_0)) = esk8_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_53,plain,
    ( v1_relat_1(k5_relat_1(k6_relat_1(X1),X2))
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_22]),c_0_20])).

cnf(c_0_54,plain,
    ( k5_relat_1(k6_relat_1(X1),k5_relat_1(X2,X3)) = k5_relat_1(k7_relat_1(X2,X1),X3)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_22]),c_0_23])])).

fof(c_0_55,plain,(
    ! [X37,X38] :
      ( ~ v1_relat_1(X37)
      | ~ v1_relat_1(X38)
      | ~ r1_tarski(k1_relat_1(X37),k2_relat_1(X38))
      | k2_relat_1(k5_relat_1(X38,X37)) = k2_relat_1(X37) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_relat_1])])])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_relat_1(k6_relat_1(X2))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_38])).

cnf(c_0_58,plain,
    ( k5_relat_1(k7_relat_1(X1,X2),k6_relat_1(k9_relat_1(X1,X2))) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_51]),c_0_20])).

cnf(c_0_59,negated_conjecture,
    ( k9_relat_1(esk8_0,k1_relat_1(esk8_0)) = k2_relat_1(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_26])])).

cnf(c_0_60,plain,
    ( v1_relat_1(k5_relat_1(k7_relat_1(X1,X2),X3))
    | ~ v1_relat_1(k5_relat_1(X1,X3))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_61,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3) = k5_relat_1(k6_relat_1(X2),k7_relat_1(X3,X1))
    | ~ v1_relat_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_22]),c_0_23])])).

cnf(c_0_62,plain,
    ( k2_relat_1(k5_relat_1(X2,X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k1_relat_1(X1),k2_relat_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_63,plain,
    ( r1_tarski(k1_relat_1(k6_relat_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( k5_relat_1(esk8_0,k6_relat_1(k2_relat_1(esk8_0))) = esk8_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_52]),c_0_52]),c_0_26])])).

cnf(c_0_65,plain,
    ( v1_relat_1(k5_relat_1(k6_relat_1(X1),k7_relat_1(X2,X3)))
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_23])]),c_0_53])).

cnf(c_0_66,plain,
    ( k2_relat_1(k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))) = k2_relat_1(k6_relat_1(k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_23])])).

cnf(c_0_67,plain,
    ( k2_relat_1(k5_relat_1(k7_relat_1(X1,X2),X3)) = k2_relat_1(X3)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X3),k9_relat_1(X1,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_51]),c_0_20])).

cnf(c_0_68,negated_conjecture,
    ( k5_relat_1(k7_relat_1(esk8_0,X1),k6_relat_1(k2_relat_1(esk8_0))) = k5_relat_1(k6_relat_1(X1),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_64]),c_0_23]),c_0_26])])).

cnf(c_0_69,plain,
    ( k5_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(k5_relat_1(X1,X3),X2)
    | ~ v1_relat_1(k5_relat_1(X1,X3))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_54])).

cnf(c_0_70,negated_conjecture,
    ( v1_relat_1(k5_relat_1(k6_relat_1(X1),esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_52]),c_0_26])])).

cnf(c_0_71,plain,
    ( k2_relat_1(k6_relat_1(k2_relat_1(X1))) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_21])).

cnf(c_0_72,plain,
    ( k2_relat_1(k6_relat_1(k9_relat_1(X1,X2))) = k2_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_58]),c_0_23]),c_0_63])])).

cnf(c_0_73,negated_conjecture,
    ( k5_relat_1(k6_relat_1(X1),esk8_0) = k7_relat_1(esk8_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_64]),c_0_64]),c_0_26]),c_0_23]),c_0_26])])).

cnf(c_0_74,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk8_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_22]),c_0_26])])).

cnf(c_0_75,plain,
    ( r2_hidden(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_36])).

cnf(c_0_76,plain,
    ( k2_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(X1,X2)))) = k2_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_23])])).

cnf(c_0_77,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk8_0,k2_relat_1(k6_relat_1(X1))),X1) = k7_relat_1(esk8_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_73]),c_0_73]),c_0_74]),c_0_26])])).

cnf(c_0_78,plain,
    ( r2_hidden(esk1_2(k1_relat_1(k7_relat_1(X1,X2)),X3),X2)
    | r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_38])).

cnf(c_0_79,negated_conjecture,
    ( k2_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(esk8_0,X1)))) = k2_relat_1(k7_relat_1(esk8_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_74])])).

cnf(c_0_80,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_78])).

cnf(c_0_81,negated_conjecture,
    ( k2_relat_1(k6_relat_1(k9_relat_1(esk8_0,X1))) = k9_relat_1(esk8_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_51]),c_0_26])])).

cnf(c_0_82,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk8_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_77]),c_0_74])])).

cnf(c_0_83,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk8_0,X1)) = k9_relat_1(esk8_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_81]),c_0_26])])).

cnf(c_0_84,negated_conjecture,
    ( k2_relat_1(k5_relat_1(X1,k7_relat_1(esk8_0,k2_relat_1(X1)))) = k9_relat_1(esk8_0,k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_82]),c_0_74])]),c_0_83])).

cnf(c_0_85,plain,
    ( k5_relat_1(X1,k7_relat_1(X2,k2_relat_1(X1))) = k5_relat_1(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_22])).

cnf(c_0_86,negated_conjecture,
    ( k2_relat_1(k5_relat_1(esk7_0,esk8_0)) != k9_relat_1(esk8_0,k2_relat_1(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_87,negated_conjecture,
    ( k2_relat_1(k5_relat_1(X1,esk8_0)) = k9_relat_1(esk8_0,k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_26])])).

cnf(c_0_88,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_89,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n016.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 18:10:49 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 1.37/1.56  # AutoSched0-Mode selected heuristic G_E___208_C00_02_nc_F1_SE_CS_SP_PS_S033N
% 1.37/1.56  # and selection function PSelectUnlessUniqMax.
% 1.37/1.56  #
% 1.37/1.56  # Preprocessing time       : 0.028 s
% 1.37/1.56  # Presaturation interreduction done
% 1.37/1.56  
% 1.37/1.56  # Proof found!
% 1.37/1.56  # SZS status Theorem
% 1.37/1.56  # SZS output start CNFRefutation
% 1.37/1.56  fof(t160_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k2_relat_1(k5_relat_1(X1,X2))=k9_relat_1(X2,k2_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 1.37/1.56  fof(d11_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(v1_relat_1(X3)=>(X3=k7_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>(r2_hidden(X4,X2)&r2_hidden(k4_tarski(X4,X5),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_relat_1)).
% 1.37/1.56  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 1.37/1.56  fof(t80_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 1.37/1.56  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 1.37/1.56  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.37/1.56  fof(t55_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 1.37/1.56  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 1.37/1.56  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.37/1.56  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.37/1.56  fof(t47_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X1),k2_relat_1(X2))=>k2_relat_1(k5_relat_1(X2,X1))=k2_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relat_1)).
% 1.37/1.56  fof(c_0_11, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k2_relat_1(k5_relat_1(X1,X2))=k9_relat_1(X2,k2_relat_1(X1))))), inference(assume_negation,[status(cth)],[t160_relat_1])).
% 1.37/1.56  fof(c_0_12, plain, ![X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X15,X13)|~r2_hidden(k4_tarski(X15,X16),X14)|X14!=k7_relat_1(X12,X13)|~v1_relat_1(X14)|~v1_relat_1(X12))&(r2_hidden(k4_tarski(X15,X16),X12)|~r2_hidden(k4_tarski(X15,X16),X14)|X14!=k7_relat_1(X12,X13)|~v1_relat_1(X14)|~v1_relat_1(X12)))&(~r2_hidden(X17,X13)|~r2_hidden(k4_tarski(X17,X18),X12)|r2_hidden(k4_tarski(X17,X18),X14)|X14!=k7_relat_1(X12,X13)|~v1_relat_1(X14)|~v1_relat_1(X12)))&((~r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X14)|(~r2_hidden(esk2_3(X12,X13,X14),X13)|~r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X12))|X14=k7_relat_1(X12,X13)|~v1_relat_1(X14)|~v1_relat_1(X12))&((r2_hidden(esk2_3(X12,X13,X14),X13)|r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X14)|X14=k7_relat_1(X12,X13)|~v1_relat_1(X14)|~v1_relat_1(X12))&(r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X12)|r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X14)|X14=k7_relat_1(X12,X13)|~v1_relat_1(X14)|~v1_relat_1(X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_relat_1])])])])])])).
% 1.37/1.56  fof(c_0_13, plain, ![X33, X34]:(~v1_relat_1(X33)|v1_relat_1(k7_relat_1(X33,X34))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 1.37/1.56  fof(c_0_14, plain, ![X42]:(~v1_relat_1(X42)|k5_relat_1(X42,k6_relat_1(k2_relat_1(X42)))=X42), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).
% 1.37/1.56  fof(c_0_15, plain, ![X43, X44]:(~v1_relat_1(X44)|k7_relat_1(X44,X43)=k5_relat_1(k6_relat_1(X43),X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 1.37/1.56  fof(c_0_16, plain, ![X32]:v1_relat_1(k6_relat_1(X32)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 1.37/1.56  fof(c_0_17, negated_conjecture, (v1_relat_1(esk7_0)&(v1_relat_1(esk8_0)&k2_relat_1(k5_relat_1(esk7_0,esk8_0))!=k9_relat_1(esk8_0,k2_relat_1(esk7_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 1.37/1.56  fof(c_0_18, plain, ![X39, X40, X41]:(~v1_relat_1(X39)|(~v1_relat_1(X40)|(~v1_relat_1(X41)|k5_relat_1(k5_relat_1(X39,X40),X41)=k5_relat_1(X39,k5_relat_1(X40,X41))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).
% 1.37/1.56  cnf(c_0_19, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),X4)|X4!=k7_relat_1(X5,X2)|~v1_relat_1(X4)|~v1_relat_1(X5)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.37/1.56  cnf(c_0_20, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.37/1.56  cnf(c_0_21, plain, (k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.37/1.56  cnf(c_0_22, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.37/1.56  cnf(c_0_23, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.37/1.56  fof(c_0_24, plain, ![X21, X22, X23, X25, X26, X27, X28, X30]:(((~r2_hidden(X23,X22)|r2_hidden(k4_tarski(X23,esk4_3(X21,X22,X23)),X21)|X22!=k1_relat_1(X21))&(~r2_hidden(k4_tarski(X25,X26),X21)|r2_hidden(X25,X22)|X22!=k1_relat_1(X21)))&((~r2_hidden(esk5_2(X27,X28),X28)|~r2_hidden(k4_tarski(esk5_2(X27,X28),X30),X27)|X28=k1_relat_1(X27))&(r2_hidden(esk5_2(X27,X28),X28)|r2_hidden(k4_tarski(esk5_2(X27,X28),esk6_2(X27,X28)),X27)|X28=k1_relat_1(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 1.37/1.56  cnf(c_0_25, plain, (r2_hidden(k4_tarski(esk2_3(X1,X2,X3),esk3_3(X1,X2,X3)),X1)|r2_hidden(k4_tarski(esk2_3(X1,X2,X3),esk3_3(X1,X2,X3)),X3)|X3=k7_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.37/1.56  cnf(c_0_26, negated_conjecture, (v1_relat_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.37/1.56  cnf(c_0_27, plain, (k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.37/1.56  cnf(c_0_28, plain, (r2_hidden(X1,X2)|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X1,X4),k7_relat_1(X3,X2))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_19]), c_0_20])).
% 1.37/1.56  cnf(c_0_29, plain, (k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X1))),X1)=k6_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_23])])).
% 1.37/1.56  cnf(c_0_30, plain, (r2_hidden(k4_tarski(X1,esk4_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.37/1.56  fof(c_0_31, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 1.37/1.56  cnf(c_0_32, negated_conjecture, (k7_relat_1(X1,X2)=esk8_0|r2_hidden(k4_tarski(esk2_3(X1,X2,esk8_0),esk3_3(X1,X2,esk8_0)),esk8_0)|r2_hidden(k4_tarski(esk2_3(X1,X2,esk8_0),esk3_3(X1,X2,esk8_0)),X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 1.37/1.56  cnf(c_0_33, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.37/1.56  cnf(c_0_34, plain, (k5_relat_1(X1,k5_relat_1(k6_relat_1(k2_relat_1(X1)),X2))=k5_relat_1(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_21]), c_0_23])])).
% 1.37/1.56  cnf(c_0_35, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k6_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_23])])).
% 1.37/1.56  cnf(c_0_36, plain, (r2_hidden(k4_tarski(X1,esk4_3(X2,k1_relat_1(X2),X1)),X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_30])).
% 1.37/1.56  cnf(c_0_37, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.37/1.56  cnf(c_0_38, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.37/1.56  cnf(c_0_39, plain, (X3=k7_relat_1(X1,X2)|~r2_hidden(k4_tarski(esk2_3(X1,X2,X3),esk3_3(X1,X2,X3)),X3)|~r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(k4_tarski(esk2_3(X1,X2,X3),esk3_3(X1,X2,X3)),X1)|~v1_relat_1(X3)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.37/1.56  cnf(c_0_40, negated_conjecture, (k7_relat_1(esk8_0,X1)=esk8_0|r2_hidden(k4_tarski(esk2_3(esk8_0,X1,esk8_0),esk3_3(esk8_0,X1,esk8_0)),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_32]), c_0_26])])).
% 1.37/1.56  cnf(c_0_41, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_33])).
% 1.37/1.56  cnf(c_0_42, plain, (k7_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X1))),X2),X1)=k5_relat_1(k6_relat_1(X1),X2)|~v1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X1))),X2))|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_34]), c_0_23])])).
% 1.37/1.56  cnf(c_0_43, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(k6_relat_1(X2)))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 1.37/1.56  cnf(c_0_44, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 1.37/1.56  fof(c_0_45, plain, ![X35, X36]:(~v1_relat_1(X36)|k2_relat_1(k7_relat_1(X36,X35))=k9_relat_1(X36,X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 1.37/1.56  cnf(c_0_46, negated_conjecture, (k7_relat_1(esk8_0,X1)=esk8_0|~r2_hidden(esk2_3(esk8_0,X1,esk8_0),X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_26])]), c_0_40])).
% 1.37/1.56  cnf(c_0_47, negated_conjecture, (k7_relat_1(esk8_0,X1)=esk8_0|r2_hidden(esk2_3(esk8_0,X1,esk8_0),k1_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_41, c_0_40])).
% 1.37/1.56  cnf(c_0_48, plain, (v1_relat_1(k5_relat_1(k6_relat_1(X1),X2))|~v1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X1))),X2))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_20, c_0_42])).
% 1.37/1.56  cnf(c_0_49, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.37/1.56  cnf(c_0_50, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,k1_relat_1(k6_relat_1(X3)))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 1.37/1.56  cnf(c_0_51, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 1.37/1.56  cnf(c_0_52, negated_conjecture, (k7_relat_1(esk8_0,k1_relat_1(esk8_0))=esk8_0), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 1.37/1.56  cnf(c_0_53, plain, (v1_relat_1(k5_relat_1(k6_relat_1(X1),X2))|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_22]), c_0_20])).
% 1.37/1.56  cnf(c_0_54, plain, (k5_relat_1(k6_relat_1(X1),k5_relat_1(X2,X3))=k5_relat_1(k7_relat_1(X2,X1),X3)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_22]), c_0_23])])).
% 1.37/1.56  fof(c_0_55, plain, ![X37, X38]:(~v1_relat_1(X37)|(~v1_relat_1(X38)|(~r1_tarski(k1_relat_1(X37),k2_relat_1(X38))|k2_relat_1(k5_relat_1(X38,X37))=k2_relat_1(X37)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_relat_1])])])).
% 1.37/1.56  cnf(c_0_56, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_relat_1(k6_relat_1(X2)))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 1.37/1.56  cnf(c_0_57, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_49, c_0_38])).
% 1.37/1.56  cnf(c_0_58, plain, (k5_relat_1(k7_relat_1(X1,X2),k6_relat_1(k9_relat_1(X1,X2)))=k7_relat_1(X1,X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_51]), c_0_20])).
% 1.37/1.56  cnf(c_0_59, negated_conjecture, (k9_relat_1(esk8_0,k1_relat_1(esk8_0))=k2_relat_1(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_26])])).
% 1.37/1.56  cnf(c_0_60, plain, (v1_relat_1(k5_relat_1(k7_relat_1(X1,X2),X3))|~v1_relat_1(k5_relat_1(X1,X3))|~v1_relat_1(X3)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 1.37/1.56  cnf(c_0_61, plain, (k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3)=k5_relat_1(k6_relat_1(X2),k7_relat_1(X3,X1))|~v1_relat_1(X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_22]), c_0_23])])).
% 1.37/1.56  cnf(c_0_62, plain, (k2_relat_1(k5_relat_1(X2,X1))=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(k1_relat_1(X1),k2_relat_1(X2))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 1.37/1.56  cnf(c_0_63, plain, (r1_tarski(k1_relat_1(k6_relat_1(X1)),X1)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 1.37/1.56  cnf(c_0_64, negated_conjecture, (k5_relat_1(esk8_0,k6_relat_1(k2_relat_1(esk8_0)))=esk8_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_52]), c_0_52]), c_0_26])])).
% 1.37/1.56  cnf(c_0_65, plain, (v1_relat_1(k5_relat_1(k6_relat_1(X1),k7_relat_1(X2,X3)))|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_23])]), c_0_53])).
% 1.37/1.56  cnf(c_0_66, plain, (k2_relat_1(k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))))=k2_relat_1(k6_relat_1(k2_relat_1(X1)))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_23])])).
% 1.37/1.56  cnf(c_0_67, plain, (k2_relat_1(k5_relat_1(k7_relat_1(X1,X2),X3))=k2_relat_1(X3)|~v1_relat_1(X3)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X3),k9_relat_1(X1,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_51]), c_0_20])).
% 1.37/1.56  cnf(c_0_68, negated_conjecture, (k5_relat_1(k7_relat_1(esk8_0,X1),k6_relat_1(k2_relat_1(esk8_0)))=k5_relat_1(k6_relat_1(X1),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_64]), c_0_23]), c_0_26])])).
% 1.37/1.56  cnf(c_0_69, plain, (k5_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(k5_relat_1(X1,X3),X2)|~v1_relat_1(k5_relat_1(X1,X3))|~v1_relat_1(X3)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_22, c_0_54])).
% 1.37/1.56  cnf(c_0_70, negated_conjecture, (v1_relat_1(k5_relat_1(k6_relat_1(X1),esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_52]), c_0_26])])).
% 1.37/1.56  cnf(c_0_71, plain, (k2_relat_1(k6_relat_1(k2_relat_1(X1)))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_66, c_0_21])).
% 1.37/1.56  cnf(c_0_72, plain, (k2_relat_1(k6_relat_1(k9_relat_1(X1,X2)))=k2_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_58]), c_0_23]), c_0_63])])).
% 1.37/1.56  cnf(c_0_73, negated_conjecture, (k5_relat_1(k6_relat_1(X1),esk8_0)=k7_relat_1(esk8_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_64]), c_0_64]), c_0_26]), c_0_23]), c_0_26])])).
% 1.37/1.56  cnf(c_0_74, negated_conjecture, (v1_relat_1(k7_relat_1(esk8_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_22]), c_0_26])])).
% 1.37/1.56  cnf(c_0_75, plain, (r2_hidden(X1,X2)|~v1_relat_1(X3)|~r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))), inference(spm,[status(thm)],[c_0_28, c_0_36])).
% 1.37/1.56  cnf(c_0_76, plain, (k2_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(X1,X2))))=k2_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_23])])).
% 1.37/1.56  cnf(c_0_77, negated_conjecture, (k7_relat_1(k7_relat_1(esk8_0,k2_relat_1(k6_relat_1(X1))),X1)=k7_relat_1(esk8_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_73]), c_0_73]), c_0_74]), c_0_26])])).
% 1.37/1.56  cnf(c_0_78, plain, (r2_hidden(esk1_2(k1_relat_1(k7_relat_1(X1,X2)),X3),X2)|r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X3)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_75, c_0_38])).
% 1.37/1.56  cnf(c_0_79, negated_conjecture, (k2_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(esk8_0,X1))))=k2_relat_1(k7_relat_1(esk8_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_74])])).
% 1.37/1.56  cnf(c_0_80, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_49, c_0_78])).
% 1.37/1.56  cnf(c_0_81, negated_conjecture, (k2_relat_1(k6_relat_1(k9_relat_1(esk8_0,X1)))=k9_relat_1(esk8_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_51]), c_0_26])])).
% 1.37/1.56  cnf(c_0_82, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(esk8_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_77]), c_0_74])])).
% 1.37/1.56  cnf(c_0_83, negated_conjecture, (k2_relat_1(k7_relat_1(esk8_0,X1))=k9_relat_1(esk8_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_81]), c_0_26])])).
% 1.37/1.56  cnf(c_0_84, negated_conjecture, (k2_relat_1(k5_relat_1(X1,k7_relat_1(esk8_0,k2_relat_1(X1))))=k9_relat_1(esk8_0,k2_relat_1(X1))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_82]), c_0_74])]), c_0_83])).
% 1.37/1.56  cnf(c_0_85, plain, (k5_relat_1(X1,k7_relat_1(X2,k2_relat_1(X1)))=k5_relat_1(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_34, c_0_22])).
% 1.37/1.56  cnf(c_0_86, negated_conjecture, (k2_relat_1(k5_relat_1(esk7_0,esk8_0))!=k9_relat_1(esk8_0,k2_relat_1(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.37/1.56  cnf(c_0_87, negated_conjecture, (k2_relat_1(k5_relat_1(X1,esk8_0))=k9_relat_1(esk8_0,k2_relat_1(X1))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_26])])).
% 1.37/1.56  cnf(c_0_88, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.37/1.56  cnf(c_0_89, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_88])]), ['proof']).
% 1.37/1.56  # SZS output end CNFRefutation
% 1.37/1.56  # Proof object total steps             : 90
% 1.37/1.56  # Proof object clause steps            : 67
% 1.37/1.56  # Proof object formula steps           : 23
% 1.37/1.56  # Proof object conjectures             : 25
% 1.37/1.56  # Proof object clause conjectures      : 22
% 1.37/1.56  # Proof object formula conjectures     : 3
% 1.37/1.56  # Proof object initial clauses used    : 18
% 1.37/1.56  # Proof object initial formulas used   : 11
% 1.37/1.56  # Proof object generating inferences   : 46
% 1.37/1.56  # Proof object simplifying inferences  : 73
% 1.37/1.56  # Training examples: 0 positive, 0 negative
% 1.37/1.56  # Parsed axioms                        : 11
% 1.37/1.56  # Removed by relevancy pruning/SinE    : 0
% 1.37/1.56  # Initial clauses                      : 23
% 1.37/1.56  # Removed in clause preprocessing      : 0
% 1.37/1.56  # Initial clauses in saturation        : 23
% 1.37/1.56  # Processed clauses                    : 3769
% 1.37/1.56  # ...of these trivial                  : 180
% 1.37/1.56  # ...subsumed                          : 2598
% 1.37/1.56  # ...remaining for further processing  : 991
% 1.37/1.56  # Other redundant clauses eliminated   : 5
% 1.37/1.56  # Clauses deleted for lack of memory   : 0
% 1.37/1.56  # Backward-subsumed                    : 56
% 1.37/1.56  # Backward-rewritten                   : 169
% 1.37/1.56  # Generated clauses                    : 81206
% 1.37/1.56  # ...of the previous two non-trivial   : 75237
% 1.37/1.56  # Contextual simplify-reflections      : 102
% 1.37/1.56  # Paramodulations                      : 81171
% 1.37/1.56  # Factorizations                       : 30
% 1.37/1.56  # Equation resolutions                 : 5
% 1.37/1.56  # Propositional unsat checks           : 0
% 1.37/1.56  #    Propositional check models        : 0
% 1.37/1.56  #    Propositional check unsatisfiable : 0
% 1.37/1.56  #    Propositional clauses             : 0
% 1.37/1.56  #    Propositional clauses after purity: 0
% 1.37/1.56  #    Propositional unsat core size     : 0
% 1.37/1.56  #    Propositional preprocessing time  : 0.000
% 1.37/1.56  #    Propositional encoding time       : 0.000
% 1.37/1.56  #    Propositional solver time         : 0.000
% 1.37/1.56  #    Success case prop preproc time    : 0.000
% 1.37/1.56  #    Success case prop encoding time   : 0.000
% 1.37/1.56  #    Success case prop solver time     : 0.000
% 1.37/1.56  # Current number of processed clauses  : 738
% 1.37/1.56  #    Positive orientable unit clauses  : 77
% 1.37/1.56  #    Positive unorientable unit clauses: 0
% 1.37/1.56  #    Negative unit clauses             : 1
% 1.37/1.56  #    Non-unit-clauses                  : 660
% 1.37/1.56  # Current number of unprocessed clauses: 71068
% 1.37/1.56  # ...number of literals in the above   : 431708
% 1.37/1.56  # Current number of archived formulas  : 0
% 1.37/1.56  # Current number of archived clauses   : 248
% 1.37/1.56  # Clause-clause subsumption calls (NU) : 168012
% 1.37/1.56  # Rec. Clause-clause subsumption calls : 84553
% 1.37/1.56  # Non-unit clause-clause subsumptions  : 2749
% 1.37/1.56  # Unit Clause-clause subsumption calls : 10850
% 1.37/1.56  # Rewrite failures with RHS unbound    : 0
% 1.37/1.56  # BW rewrite match attempts            : 295
% 1.37/1.56  # BW rewrite match successes           : 115
% 1.37/1.56  # Condensation attempts                : 0
% 1.37/1.56  # Condensation successes               : 0
% 1.37/1.56  # Termbank termtop insertions          : 3167742
% 1.40/1.56  
% 1.40/1.56  # -------------------------------------------------
% 1.40/1.56  # User time                : 1.184 s
% 1.40/1.56  # System time              : 0.052 s
% 1.40/1.56  # Total time               : 1.236 s
% 1.40/1.56  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
