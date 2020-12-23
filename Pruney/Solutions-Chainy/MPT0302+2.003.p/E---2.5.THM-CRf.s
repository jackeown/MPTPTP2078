%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:31 EST 2020

% Result     : Theorem 1.12s
% Output     : CNFRefutation 1.12s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 858 expanded)
%              Number of clauses        :   47 ( 377 expanded)
%              Number of leaves         :   12 ( 236 expanded)
%              Depth                    :   13
%              Number of atoms          :  125 (1175 expanded)
%              Number of equality atoms :   62 ( 873 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t112_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t114_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X2,X1)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | X1 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(c_0_12,plain,(
    ! [X36,X37] : k4_xboole_0(X36,k4_xboole_0(X36,X37)) = k3_xboole_0(X36,X37) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_13,plain,(
    ! [X29,X30] : k4_xboole_0(X29,X30) = k5_xboole_0(X29,k3_xboole_0(X29,X30)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_14,plain,(
    ! [X31,X32,X33] : k5_xboole_0(k3_xboole_0(X31,X32),k3_xboole_0(X33,X32)) = k3_xboole_0(k5_xboole_0(X31,X33),X32) ),
    inference(variable_rename,[status(thm)],[t112_xboole_1])).

fof(c_0_15,plain,(
    ! [X15] : k3_xboole_0(X15,X15) = X15 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_16,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X27,X28] :
      ( ( k4_xboole_0(X27,X28) != k1_xboole_0
        | r1_tarski(X27,X28) )
      & ( ~ r1_tarski(X27,X28)
        | k4_xboole_0(X27,X28) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X2,X1)
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | X1 = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t114_zfmisc_1])).

fof(c_0_21,plain,(
    ! [X41,X42,X43,X44] :
      ( ( r2_hidden(X41,X43)
        | ~ r2_hidden(k4_tarski(X41,X42),k2_zfmisc_1(X43,X44)) )
      & ( r2_hidden(X42,X44)
        | ~ r2_hidden(k4_tarski(X41,X42),k2_zfmisc_1(X43,X44)) )
      & ( ~ r2_hidden(X41,X43)
        | ~ r2_hidden(X42,X44)
        | r2_hidden(k4_tarski(X41,X42),k2_zfmisc_1(X43,X44)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

fof(c_0_22,plain,(
    ! [X25] :
      ( X25 = k1_xboole_0
      | r2_hidden(esk3_1(X25),X25) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_23,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_18])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_28,plain,(
    ! [X34,X35] : r1_tarski(k3_xboole_0(X34,X35),X34) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_29,negated_conjecture,
    ( k2_zfmisc_1(esk4_0,esk5_0) = k2_zfmisc_1(esk5_0,esk4_0)
    & esk4_0 != k1_xboole_0
    & esk5_0 != k1_xboole_0
    & esk4_0 != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_32,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_33,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X1,k5_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_34,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2))) = k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_26])).

cnf(c_0_35,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_27,c_0_18])).

cnf(c_0_36,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_37,plain,(
    ! [X38] : k5_xboole_0(X38,k1_xboole_0) = X38 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_39,negated_conjecture,
    ( k2_zfmisc_1(esk4_0,esk5_0) = k2_zfmisc_1(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(k4_tarski(X2,esk3_1(X1)),k2_zfmisc_1(X3,X1))
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_41,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,X2)))) = k3_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_25]),c_0_33]),c_0_34])).

cnf(c_0_43,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(k3_xboole_0(X1,X2),X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_25]),c_0_33])).

cnf(c_0_44,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_25])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk5_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_47,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(k4_tarski(esk1_2(X2,X3),esk3_1(X1)),k2_zfmisc_1(X2,X1))
    | r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_49,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_24])).

cnf(c_0_50,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k5_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_24]),c_0_25])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,X1),esk4_0)
    | r1_tarski(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])).

cnf(c_0_53,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_34,c_0_49])).

cnf(c_0_54,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_35,c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_56,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_53])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_58,plain,
    ( r2_hidden(k4_tarski(X1,esk1_2(X2,X3)),k2_zfmisc_1(X4,X2))
    | r1_tarski(X2,X3)
    | ~ r2_hidden(X1,X4) ),
    inference(spm,[status(thm)],[c_0_30,c_0_41])).

cnf(c_0_59,negated_conjecture,
    ( k3_xboole_0(esk5_0,k5_xboole_0(esk5_0,esk4_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_60,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X1,X2))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_50]),c_0_50])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(esk5_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_39])).

cnf(c_0_62,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(k4_tarski(esk3_1(X1),esk1_2(X2,X3)),k2_zfmisc_1(X1,X2))
    | r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_58,c_0_31])).

cnf(c_0_63,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_64,negated_conjecture,
    ( k3_xboole_0(esk5_0,esk4_0) = esk5_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_59]),c_0_44]),c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,X1),esk5_0)
    | r1_tarski(esk4_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( k3_xboole_0(esk4_0,k5_xboole_0(esk4_0,esk5_0)) = k5_xboole_0(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_64])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( k5_xboole_0(esk4_0,k5_xboole_0(esk4_0,esk5_0)) = esk5_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_66]),c_0_60]),c_0_25]),c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( k5_xboole_0(esk4_0,esk5_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_67]),c_0_66])).

cnf(c_0_70,negated_conjecture,
    ( esk4_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_69]),c_0_44]),c_0_70]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:14:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 1.12/1.28  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S4b
% 1.12/1.28  # and selection function SelectCQIPrecW.
% 1.12/1.28  #
% 1.12/1.28  # Preprocessing time       : 0.013 s
% 1.12/1.28  # Presaturation interreduction done
% 1.12/1.28  
% 1.12/1.28  # Proof found!
% 1.12/1.28  # SZS status Theorem
% 1.12/1.28  # SZS output start CNFRefutation
% 1.12/1.28  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.12/1.28  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.12/1.28  fof(t112_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_xboole_1)).
% 1.12/1.28  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 1.12/1.28  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.12/1.28  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.12/1.28  fof(t114_zfmisc_1, conjecture, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X2,X1)=>(X1=k1_xboole_0|X2=k1_xboole_0|X1=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t114_zfmisc_1)).
% 1.12/1.28  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 1.12/1.28  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.12/1.28  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.12/1.28  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.12/1.28  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 1.12/1.28  fof(c_0_12, plain, ![X36, X37]:k4_xboole_0(X36,k4_xboole_0(X36,X37))=k3_xboole_0(X36,X37), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 1.12/1.28  fof(c_0_13, plain, ![X29, X30]:k4_xboole_0(X29,X30)=k5_xboole_0(X29,k3_xboole_0(X29,X30)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 1.12/1.28  fof(c_0_14, plain, ![X31, X32, X33]:k5_xboole_0(k3_xboole_0(X31,X32),k3_xboole_0(X33,X32))=k3_xboole_0(k5_xboole_0(X31,X33),X32), inference(variable_rename,[status(thm)],[t112_xboole_1])).
% 1.12/1.28  fof(c_0_15, plain, ![X15]:k3_xboole_0(X15,X15)=X15, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 1.12/1.28  fof(c_0_16, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 1.12/1.28  cnf(c_0_17, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.12/1.28  cnf(c_0_18, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.12/1.28  fof(c_0_19, plain, ![X27, X28]:((k4_xboole_0(X27,X28)!=k1_xboole_0|r1_tarski(X27,X28))&(~r1_tarski(X27,X28)|k4_xboole_0(X27,X28)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 1.12/1.28  fof(c_0_20, negated_conjecture, ~(![X1, X2]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X2,X1)=>(X1=k1_xboole_0|X2=k1_xboole_0|X1=X2))), inference(assume_negation,[status(cth)],[t114_zfmisc_1])).
% 1.12/1.28  fof(c_0_21, plain, ![X41, X42, X43, X44]:(((r2_hidden(X41,X43)|~r2_hidden(k4_tarski(X41,X42),k2_zfmisc_1(X43,X44)))&(r2_hidden(X42,X44)|~r2_hidden(k4_tarski(X41,X42),k2_zfmisc_1(X43,X44))))&(~r2_hidden(X41,X43)|~r2_hidden(X42,X44)|r2_hidden(k4_tarski(X41,X42),k2_zfmisc_1(X43,X44)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 1.12/1.28  fof(c_0_22, plain, ![X25]:(X25=k1_xboole_0|r2_hidden(esk3_1(X25),X25)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 1.12/1.28  cnf(c_0_23, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.12/1.28  cnf(c_0_24, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.12/1.28  cnf(c_0_25, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.12/1.28  cnf(c_0_26, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18]), c_0_18])).
% 1.12/1.28  cnf(c_0_27, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.12/1.28  fof(c_0_28, plain, ![X34, X35]:r1_tarski(k3_xboole_0(X34,X35),X34), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 1.12/1.28  fof(c_0_29, negated_conjecture, (k2_zfmisc_1(esk4_0,esk5_0)=k2_zfmisc_1(esk5_0,esk4_0)&((esk4_0!=k1_xboole_0&esk5_0!=k1_xboole_0)&esk4_0!=esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 1.12/1.28  cnf(c_0_30, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.12/1.28  cnf(c_0_31, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.12/1.28  fof(c_0_32, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 1.12/1.28  cnf(c_0_33, plain, (k5_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X1,k5_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])).
% 1.12/1.28  cnf(c_0_34, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2)))=k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_26, c_0_26])).
% 1.12/1.28  cnf(c_0_35, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_27, c_0_18])).
% 1.12/1.28  cnf(c_0_36, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.12/1.28  fof(c_0_37, plain, ![X38]:k5_xboole_0(X38,k1_xboole_0)=X38, inference(variable_rename,[status(thm)],[t5_boole])).
% 1.12/1.28  cnf(c_0_38, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.12/1.28  cnf(c_0_39, negated_conjecture, (k2_zfmisc_1(esk4_0,esk5_0)=k2_zfmisc_1(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.12/1.28  cnf(c_0_40, plain, (X1=k1_xboole_0|r2_hidden(k4_tarski(X2,esk3_1(X1)),k2_zfmisc_1(X3,X1))|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 1.12/1.28  cnf(c_0_41, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.12/1.28  cnf(c_0_42, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,X2))))=k3_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_25]), c_0_33]), c_0_34])).
% 1.12/1.28  cnf(c_0_43, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(k3_xboole_0(X1,X2),X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_25]), c_0_33])).
% 1.12/1.28  cnf(c_0_44, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_37])).
% 1.12/1.28  cnf(c_0_45, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3))=k3_xboole_0(k5_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_23, c_0_25])).
% 1.12/1.28  cnf(c_0_46, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk5_0,esk4_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 1.12/1.28  cnf(c_0_47, plain, (X1=k1_xboole_0|r2_hidden(k4_tarski(esk1_2(X2,X3),esk3_1(X1)),k2_zfmisc_1(X2,X1))|r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 1.12/1.28  cnf(c_0_48, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.12/1.28  cnf(c_0_49, plain, (k3_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_24])).
% 1.12/1.28  cnf(c_0_50, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,k5_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_24]), c_0_25])).
% 1.12/1.28  cnf(c_0_51, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.12/1.28  cnf(c_0_52, negated_conjecture, (r2_hidden(esk1_2(esk5_0,X1),esk4_0)|r1_tarski(esk5_0,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])).
% 1.12/1.28  cnf(c_0_53, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_34, c_0_49])).
% 1.12/1.28  cnf(c_0_54, plain, (k3_xboole_0(X1,k5_xboole_0(X1,X2))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_35, c_0_50])).
% 1.12/1.28  cnf(c_0_55, negated_conjecture, (r1_tarski(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 1.12/1.28  cnf(c_0_56, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_26, c_0_53])).
% 1.12/1.28  cnf(c_0_57, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.12/1.28  cnf(c_0_58, plain, (r2_hidden(k4_tarski(X1,esk1_2(X2,X3)),k2_zfmisc_1(X4,X2))|r1_tarski(X2,X3)|~r2_hidden(X1,X4)), inference(spm,[status(thm)],[c_0_30, c_0_41])).
% 1.12/1.28  cnf(c_0_59, negated_conjecture, (k3_xboole_0(esk5_0,k5_xboole_0(esk5_0,esk4_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 1.12/1.28  cnf(c_0_60, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X1,X2)))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_50]), c_0_50])).
% 1.12/1.28  cnf(c_0_61, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(esk5_0,esk4_0))), inference(spm,[status(thm)],[c_0_57, c_0_39])).
% 1.12/1.28  cnf(c_0_62, plain, (X1=k1_xboole_0|r2_hidden(k4_tarski(esk3_1(X1),esk1_2(X2,X3)),k2_zfmisc_1(X1,X2))|r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_58, c_0_31])).
% 1.12/1.28  cnf(c_0_63, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.12/1.28  cnf(c_0_64, negated_conjecture, (k3_xboole_0(esk5_0,esk4_0)=esk5_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_59]), c_0_44]), c_0_60])).
% 1.12/1.28  cnf(c_0_65, negated_conjecture, (r2_hidden(esk1_2(esk4_0,X1),esk5_0)|r1_tarski(esk4_0,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63])).
% 1.12/1.28  cnf(c_0_66, negated_conjecture, (k3_xboole_0(esk4_0,k5_xboole_0(esk4_0,esk5_0))=k5_xboole_0(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_33, c_0_64])).
% 1.12/1.28  cnf(c_0_67, negated_conjecture, (r1_tarski(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_51, c_0_65])).
% 1.12/1.28  cnf(c_0_68, negated_conjecture, (k5_xboole_0(esk4_0,k5_xboole_0(esk4_0,esk5_0))=esk5_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_66]), c_0_60]), c_0_25]), c_0_64])).
% 1.12/1.28  cnf(c_0_69, negated_conjecture, (k5_xboole_0(esk4_0,esk5_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_67]), c_0_66])).
% 1.12/1.28  cnf(c_0_70, negated_conjecture, (esk4_0!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.12/1.28  cnf(c_0_71, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_69]), c_0_44]), c_0_70]), ['proof']).
% 1.12/1.28  # SZS output end CNFRefutation
% 1.12/1.28  # Proof object total steps             : 72
% 1.12/1.28  # Proof object clause steps            : 47
% 1.12/1.28  # Proof object formula steps           : 25
% 1.12/1.28  # Proof object conjectures             : 19
% 1.12/1.28  # Proof object clause conjectures      : 16
% 1.12/1.28  # Proof object formula conjectures     : 3
% 1.12/1.28  # Proof object initial clauses used    : 18
% 1.12/1.28  # Proof object initial formulas used   : 12
% 1.12/1.28  # Proof object generating inferences   : 22
% 1.12/1.28  # Proof object simplifying inferences  : 27
% 1.12/1.28  # Training examples: 0 positive, 0 negative
% 1.12/1.28  # Parsed axioms                        : 16
% 1.12/1.28  # Removed by relevancy pruning/SinE    : 0
% 1.12/1.28  # Initial clauses                      : 30
% 1.12/1.28  # Removed in clause preprocessing      : 1
% 1.12/1.28  # Initial clauses in saturation        : 29
% 1.12/1.28  # Processed clauses                    : 7032
% 1.12/1.28  # ...of these trivial                  : 500
% 1.12/1.28  # ...subsumed                          : 5385
% 1.12/1.28  # ...remaining for further processing  : 1147
% 1.12/1.28  # Other redundant clauses eliminated   : 223
% 1.12/1.28  # Clauses deleted for lack of memory   : 0
% 1.12/1.28  # Backward-subsumed                    : 6
% 1.12/1.28  # Backward-rewritten                   : 259
% 1.12/1.28  # Generated clauses                    : 127249
% 1.12/1.28  # ...of the previous two non-trivial   : 103947
% 1.12/1.28  # Contextual simplify-reflections      : 0
% 1.12/1.28  # Paramodulations                      : 126876
% 1.12/1.28  # Factorizations                       : 150
% 1.12/1.28  # Equation resolutions                 : 223
% 1.12/1.28  # Propositional unsat checks           : 0
% 1.12/1.28  #    Propositional check models        : 0
% 1.12/1.28  #    Propositional check unsatisfiable : 0
% 1.12/1.28  #    Propositional clauses             : 0
% 1.12/1.28  #    Propositional clauses after purity: 0
% 1.12/1.28  #    Propositional unsat core size     : 0
% 1.12/1.28  #    Propositional preprocessing time  : 0.000
% 1.12/1.28  #    Propositional encoding time       : 0.000
% 1.12/1.28  #    Propositional solver time         : 0.000
% 1.12/1.28  #    Success case prop preproc time    : 0.000
% 1.12/1.28  #    Success case prop encoding time   : 0.000
% 1.12/1.28  #    Success case prop solver time     : 0.000
% 1.12/1.28  # Current number of processed clauses  : 848
% 1.12/1.28  #    Positive orientable unit clauses  : 234
% 1.12/1.28  #    Positive unorientable unit clauses: 3
% 1.12/1.28  #    Negative unit clauses             : 54
% 1.12/1.28  #    Non-unit-clauses                  : 557
% 1.12/1.28  # Current number of unprocessed clauses: 94780
% 1.12/1.28  # ...number of literals in the above   : 230434
% 1.12/1.28  # Current number of archived formulas  : 0
% 1.12/1.28  # Current number of archived clauses   : 295
% 1.12/1.28  # Clause-clause subsumption calls (NU) : 25891
% 1.12/1.28  # Rec. Clause-clause subsumption calls : 18437
% 1.12/1.28  # Non-unit clause-clause subsumptions  : 1450
% 1.12/1.28  # Unit Clause-clause subsumption calls : 4444
% 1.12/1.28  # Rewrite failures with RHS unbound    : 0
% 1.12/1.28  # BW rewrite match attempts            : 783
% 1.12/1.28  # BW rewrite match successes           : 100
% 1.12/1.28  # Condensation attempts                : 0
% 1.12/1.28  # Condensation successes               : 0
% 1.12/1.28  # Termbank termtop insertions          : 2310317
% 1.12/1.29  
% 1.12/1.29  # -------------------------------------------------
% 1.12/1.29  # User time                : 0.894 s
% 1.12/1.29  # System time              : 0.056 s
% 1.12/1.29  # Total time               : 0.950 s
% 1.12/1.29  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
