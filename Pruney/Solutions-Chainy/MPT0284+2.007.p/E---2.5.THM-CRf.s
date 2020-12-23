%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:13 EST 2020

% Result     : Theorem 4.62s
% Output     : CNFRefutation 4.62s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 836 expanded)
%              Number of clauses        :   60 ( 388 expanded)
%              Number of leaves         :   11 ( 223 expanded)
%              Depth                    :   22
%              Number of atoms          :  151 (1288 expanded)
%              Number of equality atoms :   38 ( 672 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(t86_zfmisc_1,conjecture,(
    ! [X1,X2] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X1,X2)),k1_zfmisc_1(k4_xboole_0(X2,X1))),k1_zfmisc_1(k5_xboole_0(X1,X2))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_zfmisc_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(c_0_11,plain,(
    ! [X16,X17,X18] :
      ( ~ r1_tarski(X16,X17)
      | r1_tarski(X16,k2_xboole_0(X18,X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

fof(c_0_12,plain,(
    ! [X33,X34] : k3_tarski(k2_tarski(X33,X34)) = k2_xboole_0(X33,X34) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_13,plain,(
    ! [X21,X22] : r1_tarski(X21,k2_xboole_0(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_18,plain,(
    ! [X26,X27,X28,X29,X30,X31] :
      ( ( ~ r2_hidden(X28,X27)
        | r1_tarski(X28,X26)
        | X27 != k1_zfmisc_1(X26) )
      & ( ~ r1_tarski(X29,X26)
        | r2_hidden(X29,X27)
        | X27 != k1_zfmisc_1(X26) )
      & ( ~ r2_hidden(esk2_2(X30,X31),X31)
        | ~ r1_tarski(esk2_2(X30,X31),X30)
        | X31 = k1_zfmisc_1(X30) )
      & ( r2_hidden(esk2_2(X30,X31),X31)
        | r1_tarski(esk2_2(X30,X31),X30)
        | X31 = k1_zfmisc_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_16,c_0_15])).

fof(c_0_21,plain,(
    ! [X19,X20] :
      ( ~ r1_tarski(X19,X20)
      | k2_xboole_0(X19,X20) = X20 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_22,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,k3_tarski(k2_tarski(X1,X3))))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k3_tarski(k2_tarski(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_15]),c_0_15])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X1,X4))))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_15])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_27])).

cnf(c_0_33,plain,
    ( r1_tarski(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | X1 != k1_zfmisc_1(X3) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,k1_zfmisc_1(k3_tarski(k2_tarski(X2,k3_tarski(k2_tarski(X1,X3)))))) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_35,plain,
    ( k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X2,X1)))) = k3_tarski(k2_tarski(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,plain,
    ( r1_tarski(esk1_2(k1_zfmisc_1(X1),X2),X1)
    | r1_tarski(k1_zfmisc_1(X1),X2) ),
    inference(er,[status(thm)],[c_0_33])).

fof(c_0_37,plain,(
    ! [X23,X24,X25] :
      ( ~ r1_tarski(X23,X24)
      | ~ r1_tarski(X25,X24)
      | r1_tarski(k2_xboole_0(X23,X25),X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,k1_zfmisc_1(k3_tarski(k2_tarski(X2,k3_tarski(k2_tarski(X3,X1)))))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,plain,
    ( k3_tarski(k2_tarski(X1,esk1_2(k1_zfmisc_1(X1),X2))) = X1
    | r1_tarski(k1_zfmisc_1(X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_36]),c_0_27])).

fof(c_0_40,negated_conjecture,(
    ~ ! [X1,X2] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X1,X2)),k1_zfmisc_1(k4_xboole_0(X2,X1))),k1_zfmisc_1(k5_xboole_0(X1,X2))) ),
    inference(assume_negation,[status(cth)],[t86_zfmisc_1])).

cnf(c_0_41,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_43,plain,
    ( r2_hidden(esk1_2(k1_zfmisc_1(X1),X2),k1_zfmisc_1(k3_tarski(k2_tarski(X3,X1))))
    | r1_tarski(k1_zfmisc_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

fof(c_0_44,negated_conjecture,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(esk3_0,esk4_0)),k1_zfmisc_1(k4_xboole_0(esk4_0,esk3_0))),k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_40])])])).

fof(c_0_45,plain,(
    ! [X14,X15] : k4_xboole_0(X14,X15) = k5_xboole_0(X14,k3_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_46,plain,
    ( r1_tarski(k3_tarski(k2_tarski(X1,X3)),X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_41,c_0_15])).

cnf(c_0_47,plain,
    ( r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(k3_tarski(k2_tarski(X2,X1)))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

fof(c_0_48,plain,(
    ! [X12,X13] : k5_xboole_0(X12,X13) = k2_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X13,X12)) ),
    inference(variable_rename,[status(thm)],[d6_xboole_0])).

cnf(c_0_49,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(esk3_0,esk4_0)),k1_zfmisc_1(k4_xboole_0(esk4_0,esk3_0))),k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_tarski(esk2_2(X1,X2),X1)
    | X2 = k1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_52,plain,
    ( r1_tarski(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_tarski(X1,k3_tarski(k2_tarski(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_20])).

cnf(c_0_53,plain,
    ( r1_tarski(k1_zfmisc_1(X1),k3_tarski(k2_tarski(X2,k1_zfmisc_1(k3_tarski(k2_tarski(X3,X1)))))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_47])).

cnf(c_0_54,plain,
    ( r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(k3_tarski(k2_tarski(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_27])).

cnf(c_0_55,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k2_tarski(k1_zfmisc_1(k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk4_0))),k1_zfmisc_1(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk3_0))))),k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_15]),c_0_50]),c_0_50])).

cnf(c_0_57,plain,
    ( X1 = X2
    | r2_hidden(esk2_2(X3,X2),X2)
    | r2_hidden(esk2_2(X3,X1),X1)
    | r1_tarski(esk2_2(X3,X2),X3)
    | r1_tarski(esk2_2(X3,X1),X3) ),
    inference(spm,[status(thm)],[c_0_51,c_0_51])).

cnf(c_0_58,plain,
    ( r1_tarski(k3_tarski(k2_tarski(k1_zfmisc_1(X1),X2)),k3_tarski(k2_tarski(X2,k1_zfmisc_1(k3_tarski(k2_tarski(X3,X1)))))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_59,plain,
    ( k3_tarski(k2_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(k3_tarski(k2_tarski(X1,X2))))) = k1_zfmisc_1(k3_tarski(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_54])).

cnf(c_0_60,plain,
    ( k5_xboole_0(X1,X2) = k3_tarski(k2_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_15]),c_0_50]),c_0_50])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk2_2(X1,k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0))),k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0)))
    | r2_hidden(esk2_2(X1,X2),X2)
    | r1_tarski(esk2_2(X1,k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0))),X1)
    | r1_tarski(esk2_2(X1,X2),X1)
    | ~ r1_tarski(k3_tarski(k2_tarski(k1_zfmisc_1(k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk4_0))),k1_zfmisc_1(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk3_0))))),X2) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,plain,
    ( r1_tarski(k3_tarski(k2_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))),k1_zfmisc_1(k3_tarski(k2_tarski(X2,X1)))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_63,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_27]),c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk2_2(X1,k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0))),k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0)))
    | r1_tarski(esk2_2(X1,k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0))),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_60]),c_0_63]),c_0_60]),c_0_63]),c_0_60]),c_0_63])])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(esk2_2(X1,k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0))),X1)
    | r1_tarski(esk2_2(X1,k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0))),X2)
    | k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0)) != k1_zfmisc_1(X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_64])).

cnf(c_0_66,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(esk2_2(X1,k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0))),k5_xboole_0(esk3_0,esk4_0))
    | r1_tarski(esk2_2(X1,k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0))),X1) ),
    inference(er,[status(thm)],[c_0_65])).

cnf(c_0_68,plain,
    ( k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X2,k3_tarski(k2_tarski(X1,X3)))))) = k3_tarski(k2_tarski(X2,k3_tarski(k2_tarski(X1,X3)))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_25])).

cnf(c_0_69,plain,
    ( r1_tarski(k3_tarski(k2_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))),k5_xboole_0(X2,X3))
    | ~ r1_tarski(X1,k5_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_66])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(esk2_2(k5_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0))),k5_xboole_0(esk3_0,esk4_0)) ),
    inference(ef,[status(thm)],[c_0_67])).

cnf(c_0_71,plain,
    ( r1_tarski(k3_tarski(k2_tarski(X1,k1_zfmisc_1(X2))),k1_zfmisc_1(k3_tarski(k2_tarski(X2,X3))))
    | ~ r1_tarski(X1,k1_zfmisc_1(k3_tarski(k2_tarski(X2,X3)))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_54])).

cnf(c_0_72,plain,
    ( r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(k3_tarski(k2_tarski(X2,k3_tarski(k2_tarski(X1,X3)))))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_68])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_tarski(k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk4_0)),esk2_2(k5_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0))))),k5_xboole_0(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_27])).

cnf(c_0_74,plain,
    ( r1_tarski(k3_tarski(k2_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))),k1_zfmisc_1(k3_tarski(k2_tarski(X2,k3_tarski(k2_tarski(X1,X3)))))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_75,negated_conjecture,
    ( k3_tarski(k2_tarski(k5_xboole_0(esk3_0,esk4_0),k3_tarski(k2_tarski(k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk4_0)),esk2_2(k5_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0))))))) = k5_xboole_0(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_73]),c_0_27])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_tarski(k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0)),k1_zfmisc_1(k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk4_0))))),k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_27])).

cnf(c_0_77,plain,
    ( k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X1,X2)))) = k3_tarski(k2_tarski(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_20])).

cnf(c_0_78,plain,
    ( r1_tarski(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X3,X2)))
    | ~ r1_tarski(X1,k3_tarski(k2_tarski(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_32])).

cnf(c_0_79,negated_conjecture,
    ( k3_tarski(k2_tarski(k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0)),k1_zfmisc_1(k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk4_0))))) = k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_76]),c_0_27]),c_0_77])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_tarski(X1,k1_zfmisc_1(k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk4_0))))),k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0)))
    | ~ r1_tarski(X1,k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_81,plain,
    ( r1_tarski(k1_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X2))),k1_zfmisc_1(k5_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_60])).

cnf(c_0_82,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_27]),c_0_56]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:03:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 4.62/4.78  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S065A
% 4.62/4.78  # and selection function SelectComplexAHP.
% 4.62/4.78  #
% 4.62/4.78  # Preprocessing time       : 0.027 s
% 4.62/4.78  # Presaturation interreduction done
% 4.62/4.78  
% 4.62/4.78  # Proof found!
% 4.62/4.78  # SZS status Theorem
% 4.62/4.78  # SZS output start CNFRefutation
% 4.62/4.78  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 4.62/4.78  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.62/4.78  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.62/4.78  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.62/4.78  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.62/4.78  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.62/4.78  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.62/4.78  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 4.62/4.78  fof(t86_zfmisc_1, conjecture, ![X1, X2]:r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X1,X2)),k1_zfmisc_1(k4_xboole_0(X2,X1))),k1_zfmisc_1(k5_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_zfmisc_1)).
% 4.62/4.78  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.62/4.78  fof(d6_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 4.62/4.78  fof(c_0_11, plain, ![X16, X17, X18]:(~r1_tarski(X16,X17)|r1_tarski(X16,k2_xboole_0(X18,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 4.62/4.78  fof(c_0_12, plain, ![X33, X34]:k3_tarski(k2_tarski(X33,X34))=k2_xboole_0(X33,X34), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 4.62/4.78  fof(c_0_13, plain, ![X21, X22]:r1_tarski(X21,k2_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 4.62/4.78  cnf(c_0_14, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 4.62/4.78  cnf(c_0_15, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 4.62/4.78  cnf(c_0_16, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 4.62/4.78  fof(c_0_17, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 4.62/4.78  fof(c_0_18, plain, ![X26, X27, X28, X29, X30, X31]:(((~r2_hidden(X28,X27)|r1_tarski(X28,X26)|X27!=k1_zfmisc_1(X26))&(~r1_tarski(X29,X26)|r2_hidden(X29,X27)|X27!=k1_zfmisc_1(X26)))&((~r2_hidden(esk2_2(X30,X31),X31)|~r1_tarski(esk2_2(X30,X31),X30)|X31=k1_zfmisc_1(X30))&(r2_hidden(esk2_2(X30,X31),X31)|r1_tarski(esk2_2(X30,X31),X30)|X31=k1_zfmisc_1(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 4.62/4.78  cnf(c_0_19, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 4.62/4.78  cnf(c_0_20, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_16, c_0_15])).
% 4.62/4.78  fof(c_0_21, plain, ![X19, X20]:(~r1_tarski(X19,X20)|k2_xboole_0(X19,X20)=X20), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 4.62/4.78  cnf(c_0_22, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 4.62/4.78  fof(c_0_23, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 4.62/4.78  cnf(c_0_24, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 4.62/4.78  cnf(c_0_25, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,k3_tarski(k2_tarski(X1,X3)))))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 4.62/4.78  cnf(c_0_26, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.62/4.78  cnf(c_0_27, plain, (k3_tarski(k2_tarski(X1,X2))=k3_tarski(k2_tarski(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_15]), c_0_15])).
% 4.62/4.78  cnf(c_0_28, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 4.62/4.78  cnf(c_0_29, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 4.62/4.78  cnf(c_0_30, plain, (r2_hidden(X1,X2)|X2!=k1_zfmisc_1(k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X1,X4)))))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 4.62/4.78  cnf(c_0_31, plain, (k3_tarski(k2_tarski(X1,X2))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_26, c_0_15])).
% 4.62/4.78  cnf(c_0_32, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X1)))), inference(spm,[status(thm)],[c_0_20, c_0_27])).
% 4.62/4.78  cnf(c_0_33, plain, (r1_tarski(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|X1!=k1_zfmisc_1(X3)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 4.62/4.78  cnf(c_0_34, plain, (r2_hidden(X1,k1_zfmisc_1(k3_tarski(k2_tarski(X2,k3_tarski(k2_tarski(X1,X3))))))), inference(er,[status(thm)],[c_0_30])).
% 4.62/4.78  cnf(c_0_35, plain, (k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X2,X1))))=k3_tarski(k2_tarski(X2,X1))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 4.62/4.78  cnf(c_0_36, plain, (r1_tarski(esk1_2(k1_zfmisc_1(X1),X2),X1)|r1_tarski(k1_zfmisc_1(X1),X2)), inference(er,[status(thm)],[c_0_33])).
% 4.62/4.78  fof(c_0_37, plain, ![X23, X24, X25]:(~r1_tarski(X23,X24)|~r1_tarski(X25,X24)|r1_tarski(k2_xboole_0(X23,X25),X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 4.62/4.78  cnf(c_0_38, plain, (r2_hidden(X1,k1_zfmisc_1(k3_tarski(k2_tarski(X2,k3_tarski(k2_tarski(X3,X1))))))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 4.62/4.78  cnf(c_0_39, plain, (k3_tarski(k2_tarski(X1,esk1_2(k1_zfmisc_1(X1),X2)))=X1|r1_tarski(k1_zfmisc_1(X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_36]), c_0_27])).
% 4.62/4.78  fof(c_0_40, negated_conjecture, ~(![X1, X2]:r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X1,X2)),k1_zfmisc_1(k4_xboole_0(X2,X1))),k1_zfmisc_1(k5_xboole_0(X1,X2)))), inference(assume_negation,[status(cth)],[t86_zfmisc_1])).
% 4.62/4.78  cnf(c_0_41, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 4.62/4.78  cnf(c_0_42, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 4.62/4.78  cnf(c_0_43, plain, (r2_hidden(esk1_2(k1_zfmisc_1(X1),X2),k1_zfmisc_1(k3_tarski(k2_tarski(X3,X1))))|r1_tarski(k1_zfmisc_1(X1),X2)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 4.62/4.78  fof(c_0_44, negated_conjecture, ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(esk3_0,esk4_0)),k1_zfmisc_1(k4_xboole_0(esk4_0,esk3_0))),k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_40])])])).
% 4.62/4.78  fof(c_0_45, plain, ![X14, X15]:k4_xboole_0(X14,X15)=k5_xboole_0(X14,k3_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 4.62/4.78  cnf(c_0_46, plain, (r1_tarski(k3_tarski(k2_tarski(X1,X3)),X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_41, c_0_15])).
% 4.62/4.78  cnf(c_0_47, plain, (r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(k3_tarski(k2_tarski(X2,X1))))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 4.62/4.78  fof(c_0_48, plain, ![X12, X13]:k5_xboole_0(X12,X13)=k2_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X13,X12)), inference(variable_rename,[status(thm)],[d6_xboole_0])).
% 4.62/4.78  cnf(c_0_49, negated_conjecture, (~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(esk3_0,esk4_0)),k1_zfmisc_1(k4_xboole_0(esk4_0,esk3_0))),k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 4.62/4.78  cnf(c_0_50, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 4.62/4.78  cnf(c_0_51, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_tarski(esk2_2(X1,X2),X1)|X2=k1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 4.62/4.78  cnf(c_0_52, plain, (r1_tarski(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X2,X3)))|~r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))), inference(spm,[status(thm)],[c_0_46, c_0_20])).
% 4.62/4.78  cnf(c_0_53, plain, (r1_tarski(k1_zfmisc_1(X1),k3_tarski(k2_tarski(X2,k1_zfmisc_1(k3_tarski(k2_tarski(X3,X1))))))), inference(spm,[status(thm)],[c_0_19, c_0_47])).
% 4.62/4.78  cnf(c_0_54, plain, (r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(k3_tarski(k2_tarski(X1,X2))))), inference(spm,[status(thm)],[c_0_47, c_0_27])).
% 4.62/4.78  cnf(c_0_55, plain, (k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 4.62/4.78  cnf(c_0_56, negated_conjecture, (~r1_tarski(k3_tarski(k2_tarski(k1_zfmisc_1(k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk4_0))),k1_zfmisc_1(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk3_0))))),k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_15]), c_0_50]), c_0_50])).
% 4.62/4.78  cnf(c_0_57, plain, (X1=X2|r2_hidden(esk2_2(X3,X2),X2)|r2_hidden(esk2_2(X3,X1),X1)|r1_tarski(esk2_2(X3,X2),X3)|r1_tarski(esk2_2(X3,X1),X3)), inference(spm,[status(thm)],[c_0_51, c_0_51])).
% 4.62/4.78  cnf(c_0_58, plain, (r1_tarski(k3_tarski(k2_tarski(k1_zfmisc_1(X1),X2)),k3_tarski(k2_tarski(X2,k1_zfmisc_1(k3_tarski(k2_tarski(X3,X1))))))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 4.62/4.78  cnf(c_0_59, plain, (k3_tarski(k2_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(k3_tarski(k2_tarski(X1,X2)))))=k1_zfmisc_1(k3_tarski(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_31, c_0_54])).
% 4.62/4.78  cnf(c_0_60, plain, (k5_xboole_0(X1,X2)=k3_tarski(k2_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X2,k3_xboole_0(X2,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_15]), c_0_50]), c_0_50])).
% 4.62/4.78  cnf(c_0_61, negated_conjecture, (r2_hidden(esk2_2(X1,k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0))),k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0)))|r2_hidden(esk2_2(X1,X2),X2)|r1_tarski(esk2_2(X1,k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0))),X1)|r1_tarski(esk2_2(X1,X2),X1)|~r1_tarski(k3_tarski(k2_tarski(k1_zfmisc_1(k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk4_0))),k1_zfmisc_1(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk3_0))))),X2)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 4.62/4.78  cnf(c_0_62, plain, (r1_tarski(k3_tarski(k2_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))),k1_zfmisc_1(k3_tarski(k2_tarski(X2,X1))))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 4.62/4.78  cnf(c_0_63, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_27]), c_0_60])).
% 4.62/4.78  cnf(c_0_64, negated_conjecture, (r2_hidden(esk2_2(X1,k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0))),k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0)))|r1_tarski(esk2_2(X1,k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0))),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_60]), c_0_63]), c_0_60]), c_0_63]), c_0_60]), c_0_63])])).
% 4.62/4.78  cnf(c_0_65, negated_conjecture, (r1_tarski(esk2_2(X1,k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0))),X1)|r1_tarski(esk2_2(X1,k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0))),X2)|k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0))!=k1_zfmisc_1(X2)), inference(spm,[status(thm)],[c_0_28, c_0_64])).
% 4.62/4.78  cnf(c_0_66, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_20, c_0_60])).
% 4.62/4.78  cnf(c_0_67, negated_conjecture, (r1_tarski(esk2_2(X1,k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0))),k5_xboole_0(esk3_0,esk4_0))|r1_tarski(esk2_2(X1,k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0))),X1)), inference(er,[status(thm)],[c_0_65])).
% 4.62/4.78  cnf(c_0_68, plain, (k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X2,k3_tarski(k2_tarski(X1,X3))))))=k3_tarski(k2_tarski(X2,k3_tarski(k2_tarski(X1,X3))))), inference(spm,[status(thm)],[c_0_31, c_0_25])).
% 4.62/4.78  cnf(c_0_69, plain, (r1_tarski(k3_tarski(k2_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))),k5_xboole_0(X2,X3))|~r1_tarski(X1,k5_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_46, c_0_66])).
% 4.62/4.78  cnf(c_0_70, negated_conjecture, (r1_tarski(esk2_2(k5_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0))),k5_xboole_0(esk3_0,esk4_0))), inference(ef,[status(thm)],[c_0_67])).
% 4.62/4.78  cnf(c_0_71, plain, (r1_tarski(k3_tarski(k2_tarski(X1,k1_zfmisc_1(X2))),k1_zfmisc_1(k3_tarski(k2_tarski(X2,X3))))|~r1_tarski(X1,k1_zfmisc_1(k3_tarski(k2_tarski(X2,X3))))), inference(spm,[status(thm)],[c_0_46, c_0_54])).
% 4.62/4.78  cnf(c_0_72, plain, (r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(k3_tarski(k2_tarski(X2,k3_tarski(k2_tarski(X1,X3))))))), inference(spm,[status(thm)],[c_0_54, c_0_68])).
% 4.62/4.78  cnf(c_0_73, negated_conjecture, (r1_tarski(k3_tarski(k2_tarski(k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk4_0)),esk2_2(k5_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0))))),k5_xboole_0(esk3_0,esk4_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_27])).
% 4.62/4.78  cnf(c_0_74, plain, (r1_tarski(k3_tarski(k2_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))),k1_zfmisc_1(k3_tarski(k2_tarski(X2,k3_tarski(k2_tarski(X1,X3))))))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 4.62/4.78  cnf(c_0_75, negated_conjecture, (k3_tarski(k2_tarski(k5_xboole_0(esk3_0,esk4_0),k3_tarski(k2_tarski(k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk4_0)),esk2_2(k5_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0)))))))=k5_xboole_0(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_73]), c_0_27])).
% 4.62/4.78  cnf(c_0_76, negated_conjecture, (r1_tarski(k3_tarski(k2_tarski(k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0)),k1_zfmisc_1(k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk4_0))))),k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_27])).
% 4.62/4.78  cnf(c_0_77, plain, (k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X1,X2))))=k3_tarski(k2_tarski(X1,X2))), inference(spm,[status(thm)],[c_0_31, c_0_20])).
% 4.62/4.78  cnf(c_0_78, plain, (r1_tarski(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X3,X2)))|~r1_tarski(X1,k3_tarski(k2_tarski(X3,X2)))), inference(spm,[status(thm)],[c_0_46, c_0_32])).
% 4.62/4.78  cnf(c_0_79, negated_conjecture, (k3_tarski(k2_tarski(k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0)),k1_zfmisc_1(k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk4_0)))))=k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_76]), c_0_27]), c_0_77])).
% 4.62/4.78  cnf(c_0_80, negated_conjecture, (r1_tarski(k3_tarski(k2_tarski(X1,k1_zfmisc_1(k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk4_0))))),k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0)))|~r1_tarski(X1,k1_zfmisc_1(k5_xboole_0(esk3_0,esk4_0)))), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 4.62/4.78  cnf(c_0_81, plain, (r1_tarski(k1_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X2))),k1_zfmisc_1(k5_xboole_0(X2,X1)))), inference(spm,[status(thm)],[c_0_47, c_0_60])).
% 4.62/4.78  cnf(c_0_82, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_27]), c_0_56]), ['proof']).
% 4.62/4.78  # SZS output end CNFRefutation
% 4.62/4.78  # Proof object total steps             : 83
% 4.62/4.78  # Proof object clause steps            : 60
% 4.62/4.78  # Proof object formula steps           : 23
% 4.62/4.78  # Proof object conjectures             : 16
% 4.62/4.78  # Proof object clause conjectures      : 13
% 4.62/4.78  # Proof object formula conjectures     : 3
% 4.62/4.78  # Proof object initial clauses used    : 14
% 4.62/4.78  # Proof object initial formulas used   : 11
% 4.62/4.78  # Proof object generating inferences   : 39
% 4.62/4.78  # Proof object simplifying inferences  : 28
% 4.62/4.78  # Training examples: 0 positive, 0 negative
% 4.62/4.78  # Parsed axioms                        : 11
% 4.62/4.78  # Removed by relevancy pruning/SinE    : 0
% 4.62/4.78  # Initial clauses                      : 16
% 4.62/4.78  # Removed in clause preprocessing      : 2
% 4.62/4.78  # Initial clauses in saturation        : 14
% 4.62/4.78  # Processed clauses                    : 12247
% 4.62/4.78  # ...of these trivial                  : 2321
% 4.62/4.78  # ...subsumed                          : 7701
% 4.62/4.78  # ...remaining for further processing  : 2225
% 4.62/4.78  # Other redundant clauses eliminated   : 934
% 4.62/4.78  # Clauses deleted for lack of memory   : 0
% 4.62/4.78  # Backward-subsumed                    : 103
% 4.62/4.78  # Backward-rewritten                   : 23
% 4.62/4.78  # Generated clauses                    : 414991
% 4.62/4.78  # ...of the previous two non-trivial   : 383781
% 4.62/4.78  # Contextual simplify-reflections      : 0
% 4.62/4.78  # Paramodulations                      : 413607
% 4.62/4.78  # Factorizations                       : 116
% 4.62/4.78  # Equation resolutions                 : 1268
% 4.62/4.78  # Propositional unsat checks           : 0
% 4.62/4.78  #    Propositional check models        : 0
% 4.62/4.78  #    Propositional check unsatisfiable : 0
% 4.62/4.78  #    Propositional clauses             : 0
% 4.62/4.78  #    Propositional clauses after purity: 0
% 4.62/4.78  #    Propositional unsat core size     : 0
% 4.62/4.78  #    Propositional preprocessing time  : 0.000
% 4.62/4.78  #    Propositional encoding time       : 0.000
% 4.62/4.78  #    Propositional solver time         : 0.000
% 4.62/4.78  #    Success case prop preproc time    : 0.000
% 4.62/4.78  #    Success case prop encoding time   : 0.000
% 4.62/4.78  #    Success case prop solver time     : 0.000
% 4.62/4.78  # Current number of processed clauses  : 2085
% 4.62/4.78  #    Positive orientable unit clauses  : 751
% 4.62/4.78  #    Positive unorientable unit clauses: 2
% 4.62/4.78  #    Negative unit clauses             : 1
% 4.62/4.78  #    Non-unit-clauses                  : 1331
% 4.62/4.78  # Current number of unprocessed clauses: 371397
% 4.62/4.78  # ...number of literals in the above   : 2258676
% 4.62/4.78  # Current number of archived formulas  : 0
% 4.62/4.78  # Current number of archived clauses   : 142
% 4.62/4.78  # Clause-clause subsumption calls (NU) : 901322
% 4.62/4.78  # Rec. Clause-clause subsumption calls : 206380
% 4.62/4.78  # Non-unit clause-clause subsumptions  : 7795
% 4.62/4.78  # Unit Clause-clause subsumption calls : 73325
% 4.62/4.78  # Rewrite failures with RHS unbound    : 0
% 4.62/4.78  # BW rewrite match attempts            : 21240
% 4.62/4.78  # BW rewrite match successes           : 40
% 4.62/4.78  # Condensation attempts                : 0
% 4.62/4.78  # Condensation successes               : 0
% 4.62/4.78  # Termbank termtop insertions          : 15657669
% 4.62/4.80  
% 4.62/4.80  # -------------------------------------------------
% 4.62/4.80  # User time                : 4.299 s
% 4.62/4.80  # System time              : 0.170 s
% 4.62/4.80  # Total time               : 4.469 s
% 4.62/4.80  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
