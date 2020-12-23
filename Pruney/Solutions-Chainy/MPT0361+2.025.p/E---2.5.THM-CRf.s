%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:46:22 EST 2020

% Result     : Theorem 4.94s
% Output     : CNFRefutation 4.94s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 103 expanded)
%              Number of clauses        :   31 (  43 expanded)
%              Number of leaves         :   14 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :  138 ( 230 expanded)
%              Number of equality atoms :   58 (  70 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t41_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(dt_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(t35_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(X2,k3_subset_1(X1,X3))
           => r1_tarski(X3,k3_subset_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t41_subset_1])).

fof(c_0_15,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14,X15,X16] :
      ( ( ~ r2_hidden(X11,X10)
        | X11 = X7
        | X11 = X8
        | X11 = X9
        | X10 != k1_enumset1(X7,X8,X9) )
      & ( X12 != X7
        | r2_hidden(X12,X10)
        | X10 != k1_enumset1(X7,X8,X9) )
      & ( X12 != X8
        | r2_hidden(X12,X10)
        | X10 != k1_enumset1(X7,X8,X9) )
      & ( X12 != X9
        | r2_hidden(X12,X10)
        | X10 != k1_enumset1(X7,X8,X9) )
      & ( esk1_4(X13,X14,X15,X16) != X13
        | ~ r2_hidden(esk1_4(X13,X14,X15,X16),X16)
        | X16 = k1_enumset1(X13,X14,X15) )
      & ( esk1_4(X13,X14,X15,X16) != X14
        | ~ r2_hidden(esk1_4(X13,X14,X15,X16),X16)
        | X16 = k1_enumset1(X13,X14,X15) )
      & ( esk1_4(X13,X14,X15,X16) != X15
        | ~ r2_hidden(esk1_4(X13,X14,X15,X16),X16)
        | X16 = k1_enumset1(X13,X14,X15) )
      & ( r2_hidden(esk1_4(X13,X14,X15,X16),X16)
        | esk1_4(X13,X14,X15,X16) = X13
        | esk1_4(X13,X14,X15,X16) = X14
        | esk1_4(X13,X14,X15,X16) = X15
        | X16 = k1_enumset1(X13,X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_16,plain,(
    ! [X20,X21,X22] : k2_enumset1(X20,X20,X21,X22) = k1_enumset1(X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_17,plain,(
    ! [X23,X24,X25,X26] : k3_enumset1(X23,X23,X24,X25,X26) = k2_enumset1(X23,X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_18,plain,(
    ! [X27,X28,X29,X30,X31] : k4_enumset1(X27,X27,X28,X29,X30,X31) = k3_enumset1(X27,X28,X29,X30,X31) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_19,plain,(
    ! [X32,X33,X34,X35,X36,X37] : k5_enumset1(X32,X32,X33,X34,X35,X36,X37) = k4_enumset1(X32,X33,X34,X35,X36,X37) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_20,plain,(
    ! [X40,X41] : k3_tarski(k2_tarski(X40,X41)) = k2_xboole_0(X40,X41) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_21,plain,(
    ! [X18,X19] : k1_enumset1(X18,X18,X19) = k2_tarski(X18,X19) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_22,plain,(
    ! [X44,X45,X46] :
      ( ~ m1_subset_1(X45,k1_zfmisc_1(X44))
      | ~ m1_subset_1(X46,k1_zfmisc_1(X44))
      | m1_subset_1(k4_subset_1(X44,X45,X46),k1_zfmisc_1(X44)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).

fof(c_0_23,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))
    & ~ r1_tarski(k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k3_subset_1(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X2,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_29,plain,(
    ! [X49,X50,X51] :
      ( ~ m1_subset_1(X50,k1_zfmisc_1(X49))
      | ~ m1_subset_1(X51,k1_zfmisc_1(X49))
      | k4_subset_1(X49,X50,X51) = k2_xboole_0(X50,X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_30,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k5_enumset1(X4,X4,X4,X4,X4,X2,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_35,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_37,plain,(
    ! [X47,X48] :
      ( ~ m1_subset_1(X48,k1_zfmisc_1(X47))
      | k3_subset_1(X47,k3_subset_1(X47,X48)) = X48 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(k4_subset_1(esk2_0,esk3_0,X1),k1_zfmisc_1(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_40,plain,(
    ! [X42,X43] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(X42))
      | m1_subset_1(k3_subset_1(X42,X43),k1_zfmisc_1(X42)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_41,plain,(
    ! [X38,X39] :
      ( ~ r2_hidden(X38,X39)
      | r1_tarski(X38,k3_tarski(X39)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X2)
    | X2 != k5_enumset1(X3,X3,X3,X3,X3,X1,X4) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_43,plain,
    ( k4_subset_1(X2,X1,X3) = k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_25]),c_0_26]),c_0_27]),c_0_28])).

fof(c_0_44,plain,(
    ! [X52,X53,X54] :
      ( ~ m1_subset_1(X53,k1_zfmisc_1(X52))
      | ~ m1_subset_1(X54,k1_zfmisc_1(X52))
      | ~ r1_tarski(X53,k3_subset_1(X52,X54))
      | r1_tarski(X54,k3_subset_1(X52,X53)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_subset_1])])])).

cnf(c_0_45,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(k4_subset_1(esk2_0,esk3_0,esk4_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_47,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,k5_enumset1(X2,X2,X2,X2,X2,X1,X3)) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( k3_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1)) = k4_subset_1(esk2_0,esk3_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_33])).

cnf(c_0_51,plain,
    ( r1_tarski(X3,k3_subset_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,k3_subset_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( k3_subset_1(esk2_0,k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0))) = k4_subset_1(esk2_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_46])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X1,X3))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( k3_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) = k4_subset_1(esk2_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_39])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k3_subset_1(esk2_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0))
    | ~ r1_tarski(X1,k4_subset_1(esk2_0,esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(esk3_0,k4_subset_1(esk2_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k3_subset_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_33])]),c_0_58]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:14:05 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 4.94/5.11  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 4.94/5.11  # and selection function SelectNegativeLiterals.
% 4.94/5.11  #
% 4.94/5.11  # Preprocessing time       : 0.027 s
% 4.94/5.11  
% 4.94/5.11  # Proof found!
% 4.94/5.11  # SZS status Theorem
% 4.94/5.11  # SZS output start CNFRefutation
% 4.94/5.11  fof(t41_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_subset_1)).
% 4.94/5.11  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 4.94/5.11  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 4.94/5.11  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 4.94/5.11  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 4.94/5.12  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 4.94/5.12  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.94/5.12  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 4.94/5.12  fof(dt_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 4.94/5.12  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 4.94/5.12  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.94/5.12  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.94/5.12  fof(l49_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 4.94/5.12  fof(t35_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X3))=>r1_tarski(X3,k3_subset_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_subset_1)).
% 4.94/5.12  fof(c_0_14, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2))))), inference(assume_negation,[status(cth)],[t41_subset_1])).
% 4.94/5.12  fof(c_0_15, plain, ![X7, X8, X9, X10, X11, X12, X13, X14, X15, X16]:(((~r2_hidden(X11,X10)|(X11=X7|X11=X8|X11=X9)|X10!=k1_enumset1(X7,X8,X9))&(((X12!=X7|r2_hidden(X12,X10)|X10!=k1_enumset1(X7,X8,X9))&(X12!=X8|r2_hidden(X12,X10)|X10!=k1_enumset1(X7,X8,X9)))&(X12!=X9|r2_hidden(X12,X10)|X10!=k1_enumset1(X7,X8,X9))))&((((esk1_4(X13,X14,X15,X16)!=X13|~r2_hidden(esk1_4(X13,X14,X15,X16),X16)|X16=k1_enumset1(X13,X14,X15))&(esk1_4(X13,X14,X15,X16)!=X14|~r2_hidden(esk1_4(X13,X14,X15,X16),X16)|X16=k1_enumset1(X13,X14,X15)))&(esk1_4(X13,X14,X15,X16)!=X15|~r2_hidden(esk1_4(X13,X14,X15,X16),X16)|X16=k1_enumset1(X13,X14,X15)))&(r2_hidden(esk1_4(X13,X14,X15,X16),X16)|(esk1_4(X13,X14,X15,X16)=X13|esk1_4(X13,X14,X15,X16)=X14|esk1_4(X13,X14,X15,X16)=X15)|X16=k1_enumset1(X13,X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 4.94/5.12  fof(c_0_16, plain, ![X20, X21, X22]:k2_enumset1(X20,X20,X21,X22)=k1_enumset1(X20,X21,X22), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 4.94/5.12  fof(c_0_17, plain, ![X23, X24, X25, X26]:k3_enumset1(X23,X23,X24,X25,X26)=k2_enumset1(X23,X24,X25,X26), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 4.94/5.12  fof(c_0_18, plain, ![X27, X28, X29, X30, X31]:k4_enumset1(X27,X27,X28,X29,X30,X31)=k3_enumset1(X27,X28,X29,X30,X31), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 4.94/5.12  fof(c_0_19, plain, ![X32, X33, X34, X35, X36, X37]:k5_enumset1(X32,X32,X33,X34,X35,X36,X37)=k4_enumset1(X32,X33,X34,X35,X36,X37), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 4.94/5.12  fof(c_0_20, plain, ![X40, X41]:k3_tarski(k2_tarski(X40,X41))=k2_xboole_0(X40,X41), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 4.94/5.12  fof(c_0_21, plain, ![X18, X19]:k1_enumset1(X18,X18,X19)=k2_tarski(X18,X19), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 4.94/5.12  fof(c_0_22, plain, ![X44, X45, X46]:(~m1_subset_1(X45,k1_zfmisc_1(X44))|~m1_subset_1(X46,k1_zfmisc_1(X44))|m1_subset_1(k4_subset_1(X44,X45,X46),k1_zfmisc_1(X44))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).
% 4.94/5.12  fof(c_0_23, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))&~r1_tarski(k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k3_subset_1(esk2_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 4.94/5.12  cnf(c_0_24, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X2,X5)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 4.94/5.12  cnf(c_0_25, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 4.94/5.12  cnf(c_0_26, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 4.94/5.12  cnf(c_0_27, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 4.94/5.12  cnf(c_0_28, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 4.94/5.12  fof(c_0_29, plain, ![X49, X50, X51]:(~m1_subset_1(X50,k1_zfmisc_1(X49))|~m1_subset_1(X51,k1_zfmisc_1(X49))|k4_subset_1(X49,X50,X51)=k2_xboole_0(X50,X51)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 4.94/5.12  cnf(c_0_30, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 4.94/5.12  cnf(c_0_31, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.94/5.12  cnf(c_0_32, plain, (m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 4.94/5.12  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 4.94/5.12  cnf(c_0_34, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k5_enumset1(X4,X4,X4,X4,X4,X2,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27]), c_0_28])).
% 4.94/5.12  cnf(c_0_35, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 4.94/5.12  cnf(c_0_36, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 4.94/5.12  fof(c_0_37, plain, ![X47, X48]:(~m1_subset_1(X48,k1_zfmisc_1(X47))|k3_subset_1(X47,k3_subset_1(X47,X48))=X48), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 4.94/5.12  cnf(c_0_38, negated_conjecture, (m1_subset_1(k4_subset_1(esk2_0,esk3_0,X1),k1_zfmisc_1(esk2_0))|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 4.94/5.12  cnf(c_0_39, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 4.94/5.12  fof(c_0_40, plain, ![X42, X43]:(~m1_subset_1(X43,k1_zfmisc_1(X42))|m1_subset_1(k3_subset_1(X42,X43),k1_zfmisc_1(X42))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 4.94/5.12  fof(c_0_41, plain, ![X38, X39]:(~r2_hidden(X38,X39)|r1_tarski(X38,k3_tarski(X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).
% 4.94/5.12  cnf(c_0_42, plain, (r2_hidden(X1,X2)|X2!=k5_enumset1(X3,X3,X3,X3,X3,X1,X4)), inference(er,[status(thm)],[c_0_34])).
% 4.94/5.12  cnf(c_0_43, plain, (k4_subset_1(X2,X1,X3)=k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_25]), c_0_26]), c_0_27]), c_0_28])).
% 4.94/5.12  fof(c_0_44, plain, ![X52, X53, X54]:(~m1_subset_1(X53,k1_zfmisc_1(X52))|(~m1_subset_1(X54,k1_zfmisc_1(X52))|(~r1_tarski(X53,k3_subset_1(X52,X54))|r1_tarski(X54,k3_subset_1(X52,X53))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_subset_1])])])).
% 4.94/5.12  cnf(c_0_45, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 4.94/5.12  cnf(c_0_46, negated_conjecture, (m1_subset_1(k4_subset_1(esk2_0,esk3_0,esk4_0),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 4.94/5.12  cnf(c_0_47, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 4.94/5.12  cnf(c_0_48, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 4.94/5.12  cnf(c_0_49, plain, (r2_hidden(X1,k5_enumset1(X2,X2,X2,X2,X2,X1,X3))), inference(er,[status(thm)],[c_0_42])).
% 4.94/5.12  cnf(c_0_50, negated_conjecture, (k3_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1))=k4_subset_1(esk2_0,esk3_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_43, c_0_33])).
% 4.94/5.12  cnf(c_0_51, plain, (r1_tarski(X3,k3_subset_1(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,k3_subset_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 4.94/5.12  cnf(c_0_52, negated_conjecture, (k3_subset_1(esk2_0,k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)))=k4_subset_1(esk2_0,esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 4.94/5.12  cnf(c_0_53, negated_conjecture, (m1_subset_1(k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_47, c_0_46])).
% 4.94/5.12  cnf(c_0_54, plain, (r1_tarski(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X1,X3)))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 4.94/5.12  cnf(c_0_55, negated_conjecture, (k3_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))=k4_subset_1(esk2_0,esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_50, c_0_39])).
% 4.94/5.12  cnf(c_0_56, negated_conjecture, (r1_tarski(k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k3_subset_1(esk2_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))|~r1_tarski(X1,k4_subset_1(esk2_0,esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])])).
% 4.94/5.12  cnf(c_0_57, negated_conjecture, (r1_tarski(esk3_0,k4_subset_1(esk2_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 4.94/5.12  cnf(c_0_58, negated_conjecture, (~r1_tarski(k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k3_subset_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 4.94/5.12  cnf(c_0_59, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_33])]), c_0_58]), ['proof']).
% 4.94/5.12  # SZS output end CNFRefutation
% 4.94/5.12  # Proof object total steps             : 60
% 4.94/5.12  # Proof object clause steps            : 31
% 4.94/5.12  # Proof object formula steps           : 29
% 4.94/5.12  # Proof object conjectures             : 15
% 4.94/5.12  # Proof object clause conjectures      : 12
% 4.94/5.12  # Proof object formula conjectures     : 3
% 4.94/5.12  # Proof object initial clauses used    : 16
% 4.94/5.12  # Proof object initial formulas used   : 14
% 4.94/5.12  # Proof object generating inferences   : 11
% 4.94/5.12  # Proof object simplifying inferences  : 16
% 4.94/5.12  # Training examples: 0 positive, 0 negative
% 4.94/5.12  # Parsed axioms                        : 14
% 4.94/5.12  # Removed by relevancy pruning/SinE    : 0
% 4.94/5.12  # Initial clauses                      : 23
% 4.94/5.12  # Removed in clause preprocessing      : 6
% 4.94/5.12  # Initial clauses in saturation        : 17
% 4.94/5.12  # Processed clauses                    : 2708
% 4.94/5.12  # ...of these trivial                  : 194
% 4.94/5.12  # ...subsumed                          : 230
% 4.94/5.12  # ...remaining for further processing  : 2284
% 4.94/5.12  # Other redundant clauses eliminated   : 180
% 4.94/5.12  # Clauses deleted for lack of memory   : 0
% 4.94/5.12  # Backward-subsumed                    : 0
% 4.94/5.12  # Backward-rewritten                   : 22
% 4.94/5.12  # Generated clauses                    : 155841
% 4.94/5.12  # ...of the previous two non-trivial   : 155438
% 4.94/5.12  # Contextual simplify-reflections      : 0
% 4.94/5.12  # Paramodulations                      : 155590
% 4.94/5.12  # Factorizations                       : 58
% 4.94/5.12  # Equation resolutions                 : 193
% 4.94/5.12  # Propositional unsat checks           : 0
% 4.94/5.12  #    Propositional check models        : 0
% 4.94/5.12  #    Propositional check unsatisfiable : 0
% 4.94/5.12  #    Propositional clauses             : 0
% 4.94/5.12  #    Propositional clauses after purity: 0
% 4.94/5.12  #    Propositional unsat core size     : 0
% 4.94/5.12  #    Propositional preprocessing time  : 0.000
% 4.94/5.12  #    Propositional encoding time       : 0.000
% 4.94/5.12  #    Propositional solver time         : 0.000
% 4.94/5.12  #    Success case prop preproc time    : 0.000
% 4.94/5.12  #    Success case prop encoding time   : 0.000
% 4.94/5.12  #    Success case prop solver time     : 0.000
% 4.94/5.12  # Current number of processed clauses  : 2259
% 4.94/5.12  #    Positive orientable unit clauses  : 1129
% 4.94/5.12  #    Positive unorientable unit clauses: 0
% 4.94/5.12  #    Negative unit clauses             : 1
% 4.94/5.12  #    Non-unit-clauses                  : 1129
% 4.94/5.12  # Current number of unprocessed clauses: 152741
% 4.94/5.12  # ...number of literals in the above   : 406731
% 4.94/5.12  # Current number of archived formulas  : 0
% 4.94/5.12  # Current number of archived clauses   : 28
% 4.94/5.12  # Clause-clause subsumption calls (NU) : 1138300
% 4.94/5.12  # Rec. Clause-clause subsumption calls : 191515
% 4.94/5.12  # Non-unit clause-clause subsumptions  : 230
% 4.94/5.12  # Unit Clause-clause subsumption calls : 77441
% 4.94/5.12  # Rewrite failures with RHS unbound    : 0
% 4.94/5.12  # BW rewrite match attempts            : 127770
% 4.94/5.12  # BW rewrite match successes           : 22
% 4.94/5.12  # Condensation attempts                : 0
% 4.94/5.12  # Condensation successes               : 0
% 4.94/5.12  # Termbank termtop insertions          : 7051859
% 4.98/5.13  
% 4.98/5.13  # -------------------------------------------------
% 4.98/5.13  # User time                : 4.701 s
% 4.98/5.13  # System time              : 0.080 s
% 4.98/5.13  # Total time               : 4.782 s
% 4.98/5.13  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
